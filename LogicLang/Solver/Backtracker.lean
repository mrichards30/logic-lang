import LogicLang.Syntax.Expressions 

structure PartialAssignment where 
  functionName : String
  functionParameter : String
  assignedValue : String
deriving Repr 

partial def testConstraint (expr : PartialAssignment) (constraint : LogicalPredicate) : Bool :=
  match constraint with 

    | .connect left op right => False 
    
    | .predicate left op right => 

      match (left, op, right) with  

        | (l, .notEquals, r) => 
          let predWithEqInsteadOfNotEq := testConstraint expr (.predicate l .equals r)
          !predWithEqInsteadOfNotEq

        | (.literal a, .equals, .literal b) => a == b -- just comparing two strings... 

        | (.functionCall functionName (.literal x), .equals, .literal b) | (.literal b, .equals, .functionCall functionName (.literal x)) => 
          -- comparing f(x)=C where C is a literal/constant; return false if `expr` is represented
          -- by the constraint, but has a different assignment value
            if expr.functionName == functionName && expr.functionParameter == x
              then expr.assignedValue == b
              else True 

        | _ => False 

    | .invertedPredicate pred => !(testConstraint expr pred) 

def testConstraints (constraints : List LogicalPredicate) (expr : PartialAssignment) : Bool := 
  constraints.all (testConstraint expr) 

-- TODO: FIX HARDCODING FROM ENUM DEFINITIONS
def getDomainByName (s : String) : List String := 
  if s == "Horse" then ["Matt's horse", "Joe's horse", "Kate's horse"]
  else if s == "Degree" then ["Eco", "Maths", "Comp"]
  else ["Matt", "Joe"]

def backtrack (remainingFnDomainAndRanges : List (String × String × String)) (constraints : List LogicalPredicate) : StateT (List LogicalPredicate) Id Unit := do
  unless (<-get).isEmpty do return  -- only execute any code if a solution hasn't been found yet
    
  match remainingFnDomainAndRanges with 
    | [] => 
      -- erasing duplicates because the solution can overlap with the initial constraints
      let solution := constraints.eraseDups 
      set solution

    | (fn, x, domain) :: xs => 
      let domainValues := getDomainByName domain
      let nextAssignments := domainValues.map (λe => {
          functionName := fn,
          functionParameter := x
          assignedValue := e
        }) |> List.filter (testConstraints constraints)

      for p in nextAssignments do
        backtrack xs ((toPred p) :: constraints)

    return ()

  where toPred (p : PartialAssignment) := 
          LogicalPredicate.predicate 
            (.functionCall (p.functionName) (.literal p.functionParameter)) 
            .equals 
            (.literal p.assignedValue)

#eval (StateT.run (backtrack 
  [("getHorse", "Matt", "Horse"), ("getHorse", "Joe", "Horse"), ("getHorse", "Kate", "Horse")] 
  [
    (.predicate (.functionCall "getHorse" (.literal "Matt")) .equals (.literal "Matt's horse")),
    (.predicate (.functionCall "getHorse" (.literal "Joe")) .equals (.literal "Joe's horse")),
    (.predicate (.functionCall "getHorse" (.literal "Kate")) .equals (.literal "Kate's horse"))
  ]) []).snd

-- Examples/testing:

-- two literals can be compared regardless of the input state:

#eval testConstraint { -- should be false
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Matt's horse"
  } (.predicate (.literal "One string") .equals (.literal "Another string"))
  
#eval testConstraint { -- should be true
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Matt's horse"
  } (.predicate (.literal "Same string") .equals (.literal "Same string"))

#eval testConstraint { -- should be false
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Matt's horse"
  } (.predicate (.literal "Same string") .notEquals (.literal "Same string"))

#eval testConstraint { -- should be false
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Matt's horse"
  } (.invertedPredicate (.predicate (.literal "Same string") .equals (.literal "Same string")))

-- a simple function can be tested against a unary constraint:

#eval testConstraint { -- should be false
  functionName := "getHorse",
  functionParameter := "Matt",
  assignedValue := "Matt's horse"
} (.predicate (.functionCall "getHorse" (.literal "Matt")) .equals (.literal "Joe's horse"))

#eval testConstraint { -- should be true
  functionName := "getHorse",
  functionParameter := "Matt",
  assignedValue := "Matt's horse"
} (.predicate (.functionCall "getHorse" (.literal "Matt")) .equals (.literal "Matt's horse"))

#eval testConstraint { -- should be true
  functionName := "getHorse",
  functionParameter := "Matt",
  assignedValue := "Matt's horse"
} (.predicate (.literal "Matt's horse") .equals (.functionCall "getHorse" (.literal "Matt"))) -- swapped args order

