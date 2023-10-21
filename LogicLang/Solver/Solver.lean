import LogicLang.Solver.Backtracker 
import LogicLang.Syntax.Expressions 
import LogicLang.Syntax.Parser 

partial def extractConstraintsFromExpression (expr : Expression) : List LogicalPredicate := 
  match expr with 
    | .expressions es => List.bind es extractConstraintsFromExpression
    | .functionDefinition _ _ _ _ => [] 
    | .enumDefinition _ _ => []
    | .assertion pred => [pred]

partial def createDomainByNameTable (expr : Expression) : List (String × List String) := 
  match expr with 
    | .expressions es => List.bind es createDomainByNameTable
    | .functionDefinition _ _ _ _ => [] 
    | .assertion _ => []
    | .enumDefinition name values => [(name, values)]

partial def extractFunctionDefinitions (getDomainByName : String -> List String) (expr : Expression) : List (String × String × String) := 
  match expr with 
    | .expressions es => List.bind es (extractFunctionDefinitions getDomainByName)
    | .assertion _ => []
    | .enumDefinition _ _ => []
    | .functionDefinition _ f x domain => (getDomainByName x).map (λe => (f, e, domain))

def testQuestion := parseMultiLineString 
        "
        enum Person = Matt | Dean | Liz | Kate;
        enum Horse = Morse | Dorse | Lorse | Korse;
        fn getHorse :: Person -> Horse;
        
        getHorse(Dean) != Morse;
        getHorse(Dean) != Dorse;
        getHorse(Dean) != Korse;
        
        getHorse(Dean) = getHorse(Matt);
        getHorse(Matt) = getHorse(Liz);
        getHorse(Liz) = getHorse(Kate);
        "

#eval testQuestion 

#eval createDomainByNameTable <$> testQuestion  
#eval extractConstraintsFromExpression <$> testQuestion   

def getDomain (domains : List (String × List String)) (name : String) : List String := 
  match domains with
  
    | (domainName, values) :: tail => 
      if name == domainName 
        then values 
        else getDomain tail name

    | [] => []

#eval (λe => getDomain e "Horse") <$> createDomainByNameTable <$> testQuestion
#eval (λe => getDomain e "Person") <$> createDomainByNameTable <$> testQuestion

def testBacktracker := 
  match testQuestion with 

    | .ok question =>

      let domainsByName := createDomainByNameTable question 
      let functionDefinitions := extractFunctionDefinitions (getDomain domainsByName) question 
      let constraints := extractConstraintsFromExpression question 

      StateT.run (backtrack functionDefinitions constraints (getDomain domainsByName)) []

    | .error _ => ((), [])

#eval testBacktracker

