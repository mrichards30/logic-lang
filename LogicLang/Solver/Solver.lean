import LogicLang.Solver.Backtracker
import LogicLang.Syntax.Expressions

partial def extractConstraintsFromExpression (expr : Expression) : List LogicalPredicate :=
  match expr with
    | .expressions es => List.bind es extractConstraintsFromExpression
    | .assertion pred => [pred]
    | _ => []

partial def createDomainByNameTable (expr : Expression) : List (String × List String) :=
  match expr with
    | .expressions es => List.bind es createDomainByNameTable
    | .enumDefinition name values => [(name, values)]
    | _ => []

partial def extractFunctionDefinitions (getDomainByName : String -> List String) (expr : Expression) : List (String × String × String) :=
  match expr with
    | .expressions es => List.bind es (extractFunctionDefinitions getDomainByName)
    | .functionDefinition _ f x domain => (getDomainByName x).map (λe => (f, e, domain))
    | _ => []

partial def extractInjectiveFunctionNames (expr : Expression) : List String :=
  match expr with
    | .functionDefinition (some _) f _ _ => [f]
    | .expressions es => es.bind extractInjectiveFunctionNames
    | _ => []

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

    let context := { injectiveFunctions := extractInjectiveFunctionNames expression }

    StateT.run (backtrack context functionDefinitions constraints (getDomain domainsByName)) []
