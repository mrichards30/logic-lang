import LogicLang.Solver.Backtracker 
import LogicLang.Syntax.Expressions 

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

def getDomain (domains : List (String × List String)) (name : String) : List String := 
  match domains with
  
    | (domainName, values) :: tail => 
      if name == domainName 
        then values 
        else getDomain tail name

    | [] => []

def runSolver (expression : Expression) := 
    let domainsByName := createDomainByNameTable expression 
    let functionDefinitions := extractFunctionDefinitions (getDomain domainsByName) expression 
    let constraints := extractConstraintsFromExpression expression 

    StateT.run (backtrack functionDefinitions constraints (getDomain domainsByName)) []
