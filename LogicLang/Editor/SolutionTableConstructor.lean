import LogicLang.Syntax.Expressions

def getFunctionName (p : LogicalPredicate) : Option String := 
  match p with 
    | .predicate (.functionCall f _) _ _ => some f 
    | .predicate _ _ (.functionCall f _) => some f 
    | _ => none

def getFunctionParameter (p : LogicalPredicate) : Option String := 
  match p with 
    | .predicate (.functionCall _ (.literal x)) _ _ => some x 
    | .predicate _ _ (.functionCall _ (.literal x)) => some x
    | _ => none

def getFunctionAssignment (p : LogicalPredicate) : Option String := 
  match p with 
    | .predicate (.functionCall _ (.literal _)) _ (.literal x) => some x 
    | .predicate (.literal x) _ (.functionCall _ (.literal _)) => some x
    | _ => none

def doFunctionNamesMatch (a b : LogicalPredicate) : Bool :=
  getFunctionName a == getFunctionName b

def List.sort (comparator : α -> α -> Bool) (lst : List α) : List α := 
  Array.insertionSort (lst.toArray) comparator |> Array.toList

def createAsciiTable (ps : List LogicalPredicate) : Option String := do 

  let compareFunctionNames (a b : LogicalPredicate) : Bool := 
    match (getFunctionName a, getFunctionName b) with
      | (some x, some y) => x > y 
      | _ => False

  -- groupBy only compares adjacent elements; we can sort then group to exhaustively group.
  let predsByFunction := ps.sort compareFunctionNames 
                        |> List.groupBy doFunctionNamesMatch 

  let mut asciiTable := ""

  for functionGroup in predsByFunction do
    let fnName <- getFunctionName (<- functionGroup.head?)
    asciiTable := asciiTable ++ 
                    "\n+----------------------+\n" ++ 
                    s!"| {fnName} \n" ++           
                    "+----------------------+\n" 
    let predicateDetails <- functionGroup.mapM convertToFnInfoTuple
    for (name, param, assignment) in predicateDetails do 
      asciiTable := s!"| {asciiTable} \n {name}({param}) = {assignment} "
    asciiTable := asciiTable ++ "\n\n+----------------------+ \n "

  return asciiTable

  where convertToFnInfoTuple (p : LogicalPredicate) : Option (String × String × String) := do
    let name <- getFunctionName p
    let param <- getFunctionParameter p
    let assignment <- getFunctionAssignment p
    return (name, param, assignment)
  
def examplePreds : List LogicalPredicate := [
    LogicalPredicate.predicate
      (Value.functionCall "getHorse" (Value.literal "Topalov"))
      (ComparisonOperation.equals)
      (Value.literal "Chestnut"),
    LogicalPredicate.predicate
      (Value.functionCall "getHorse" (Value.literal "Hacking"))
      (ComparisonOperation.equals)
      (Value.literal "Bay"),
    LogicalPredicate.predicate
      (Value.functionCall "getActivity" (Value.literal "Gray"))
      (ComparisonOperation.equals)
      (Value.literal "StandingStill"),
    LogicalPredicate.predicate
      (Value.functionCall "getActivity" (Value.literal "Black"))
      (ComparisonOperation.equals)
      (Value.literal "StandingStill"),
    LogicalPredicate.predicate
      (Value.functionCall "getActivity" (Value.literal "Bay"))
      (ComparisonOperation.notEquals)
      (Value.literal "Jumping"),
    LogicalPredicate.predicate
      (Value.functionCall "getActivity" (Value.literal "Bay"))
      (ComparisonOperation.equals)
      (Value.literal "StandingStill"),
    LogicalPredicate.predicate
      (Value.functionCall "getActivity" (Value.literal "Chestnut"))
      (ComparisonOperation.equals)
      (Value.literal "StandingStill"),
    LogicalPredicate.predicate
      (Value.functionCall "getHorse" (Value.literal "Mountback"))
      (ComparisonOperation.equals)
      (Value.literal "Bay"),
    LogicalPredicate.predicate
      (Value.functionCall "getHorse" (Value.literal "Klamberon"))
      (ComparisonOperation.equals)
      (Value.literal "Bay")
    ]

def compareFunctionNames (a b : LogicalPredicate) : Bool := 
    match (getFunctionName a, getFunctionName b) with
      | (some x, some y) => x > y 
      | _ => False

#eval createAsciiTable examplePreds