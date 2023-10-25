import LogicLang.Syntax.Expressions 

structure PartialAssignment where 
  functionName : String
  functionParameter : String
  assignedValue : String
deriving Repr 

def LogicalPredicate.substitute (original substitution : Value) (pred : LogicalPredicate) := 
  
  let rec substituteInValue (target : Value) : Value := 
    if target == original 
      then substitution 
      else 
        match target with 
          | .literal _ => target
          | .functionCall f x => .functionCall f (substituteInValue x) 
  
  match pred with 
    | .predicate l x r => LogicalPredicate.predicate (substituteInValue l) x (substituteInValue r)
    | .invertedPredicate p => .invertedPredicate (LogicalPredicate.substitute original substitution p)
    | .connect l x r => .connect (LogicalPredicate.substitute original substitution l) x (LogicalPredicate.substitute original substitution r)

def examplePred := (LogicalPredicate.predicate 
  (.functionCall "getHorse" (.literal "Matt")) .equals (.functionCall "getHorse" (.literal "Kate")))

#eval examplePred.substitute (.functionCall "getHorse" (.literal "Matt")) (.literal "Morse")

partial def testConstraint (expr : PartialAssignment) (constraint : LogicalPredicate) : Bool :=
  match constraint with 

    | .connect left op right => 
       match op with -- precedence: implies then and then or 
        | .implies => testConstraint expr (.invertedPredicate left) || testConstraint expr right 
        | .and => testConstraint expr left && testConstraint expr right 
        | .or => testConstraint expr left || testConstraint expr right 
    
    | .predicate left op right => 

      match (left, op, right) with 

        | (.literal a, .equals, .literal b) => a == b

        | (.literal a, .notEquals, .literal b) => a != b  

        | (.functionCall functionName (.literal x), .equals, .literal b) | (.literal b, .equals, .functionCall functionName (.literal x)) => 
          -- comparing f(x)=C where C is a literal/constant; return false if `expr` is represented
          -- by the constraint, but has a different assignment value
            if expr.functionName == functionName && expr.functionParameter == x
              then expr.assignedValue == b
              else True -- don't reject if it's not relevant

        | (.functionCall functionName (.literal x), .notEquals, .literal b) | (.literal b, .notEquals, .functionCall functionName (.literal x)) => 
          -- comparing f(x)=C where C is a literal/constant; return false if `expr` is represented
          -- by the constraint, but has a different assignment value
            if expr.functionName == functionName && expr.functionParameter == x
              then expr.assignedValue != b
              else True -- don't reject if it's not relevant

        | _ => True -- don't reject anything more nested; it will be substituted/simplified when it's time to check it

    | .invertedPredicate (.invertedPredicate pred) => testConstraint expr pred

    | .invertedPredicate (.predicate left op right) => 

      match (left, op, right) with  

        | (.literal a, .equals, .literal b) => a != b

        | (.literal a, .notEquals, .literal b) => a == b  

        | (.functionCall functionName (.literal x), .equals, .literal b) | (.literal b, .equals, .functionCall functionName (.literal x)) => 
          -- comparing f(x)=C where C is a literal/constant; return false if `expr` is represented
          -- by the constraint, but has a different assignment value
            if expr.functionName == functionName && expr.functionParameter == x
              then expr.assignedValue != b
              else True -- don't reject if it's not relevant

        | (.functionCall functionName (.literal x), .notEquals, .literal b) | (.literal b, .notEquals, .functionCall functionName (.literal x)) => 
          -- comparing f(x)=C where C is a literal/constant; return false if `expr` is represented
          -- by the constraint, but has a different assignment value
            if expr.functionName == functionName && expr.functionParameter == x
              then expr.assignedValue == b
              else True -- don't reject if it's not relevant

        | _ => True -- don't reject anything more nested; it will be substituted/simplified when it's time to check it

    | .invertedPredicate (.connect left op right) => 

      let invertedOp := if op == .and then .or else .and 
      testConstraint expr (.connect (.invertedPredicate left) invertedOp (.invertedPredicate right))

def testConstraints (constraints : List LogicalPredicate) (expr : PartialAssignment) : Bool := 
  constraints.all (testConstraint expr) 

-- only for #eval testing
def mockFindDomainByName (s : String) : List String := 
  if s == "Horse" then ["Morse", "Jorse", "Lorse", "Korse"]
  else if s == "Degree" then ["Eco", "Maths", "Comp"]
  else ["Matt", "Joe", "Kate", "Liz"]

def substituteNewAssignmentIntoConstraints (assignment : PartialAssignment) (constraints : List LogicalPredicate) : List LogicalPredicate := 
  
  let substitute (next : LogicalPredicate) : LogicalPredicate := 
    next.substitute 
      (.functionCall assignment.functionName (.literal assignment.functionParameter)) 
      (.literal assignment.assignedValue)

  constraints.foldl (λ acc next => substitute next :: acc) []

/--
- We don't want to include trivial observations in our 
- solutions, e.g., "Joe" == "Joe". This function can be 
- used in a filter over solutions to remove anything
- uninteresting before returning them to the user.
-/
def LogicalPredicate.isSimpleAssignment (pred : LogicalPredicate) : Bool := 
  match pred with 
    | .connect _ _ _ => False 
    | .invertedPredicate _ => False 
    | .predicate l _ r => 
      match (l, r) with 
        | (.functionCall _ (.literal _), .literal _) => True 
        | (.literal _, .functionCall _ (.literal _)) => True 
        | _ => False 

def backtrack (remainingFnDomainAndRanges : List (String × String × String)) (constraints : List LogicalPredicate) (getDomainByName : String -> List String) : StateT (List LogicalPredicate) Id Unit := do
  unless (<-get).isEmpty do return  -- only execute any code if a solution hasn't been found yet
    
  match remainingFnDomainAndRanges with 
    | [] => 
      -- erasing duplicates because the solution can overlap with the initial constraints
      let solution := constraints
                        |> List.eraseDups
                        |> List.filter LogicalPredicate.isSimpleAssignment
      set solution

    | (fn, x, domain) :: xs => 
      let domainValues := getDomainByName domain
      let nextAssignments := domainValues.map (λe => {
          functionName := fn,
          functionParameter := x
          assignedValue := e
        }) |> List.filter (testConstraints constraints)

      for p in nextAssignments do
        let updatedConstraints := substituteNewAssignmentIntoConstraints p constraints
        backtrack xs ((toPred p) :: updatedConstraints) getDomainByName

    return ()

  where toPred (p : PartialAssignment) := 
          LogicalPredicate.predicate 
            (.functionCall (p.functionName) (.literal p.functionParameter)) 
            .equals 
            (.literal p.assignedValue)

#eval (StateT.run (backtrack 
  [("getHorse", "Matt", "Horse"), ("getHorse", "Joe", "Horse"), ("getHorse", "Kate", "Horse")] 
  [
    (.predicate (.functionCall "getHorse" (.literal "Kate")) .equals (.literal "Korse")),
    (.predicate (.functionCall "getHorse" (.literal "Matt")) .equals (.functionCall "getHorse" (.literal "Kate"))),
    (.predicate (.functionCall "getHorse" (.literal "Joe")) .equals (.literal "Jorse"))
  ] mockFindDomainByName) []).snd

-- Examples/testing:

-- two literals can be compared regardless of the input state:

#eval testConstraint { -- should be false
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.literal "One string") .equals (.literal "Another string"))
  
#eval testConstraint { -- should be true
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.literal "Same string") .equals (.literal "Same string"))

#eval testConstraint { -- should be false
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.literal "Same string") .notEquals (.literal "Same string"))

#eval testConstraint { -- should be false
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.invertedPredicate (.predicate (.literal "Same string") .equals (.literal "Same string")))

-- a simple function can be tested against a unary constraint:

#eval testConstraint { -- should be false
  functionName := "getHorse",
  functionParameter := "Matt",
  assignedValue := "Morse"
} (.predicate (.functionCall "getHorse" (.literal "Matt")) .equals (.literal "Jorse"))

#eval testConstraint { -- should be true
  functionName := "getHorse",
  functionParameter := "Matt",
  assignedValue := "Morse"
} (.predicate (.functionCall "getHorse" (.literal "Matt")) .equals (.literal "Morse"))

#eval testConstraint { -- should be true
  functionName := "getHorse",
  functionParameter := "Matt",
  assignedValue := "Morse"
} (.predicate (.literal "Morse") .equals (.functionCall "getHorse" (.literal "Matt"))) -- swapped args order

-- negative predicates when we are missing info should be accepted 

#eval testConstraint { -- should be true - not enough info to reject
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.functionCall "getHorse" (.literal "Kate")) .notEquals (.literal "Korse"))

#eval testConstraint { -- should be true - not enough info to reject
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.functionCall "getHorse" (.literal "Kate")) .notEquals (.literal "Korse"))

#eval testConstraint { -- should be true
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.functionCall "getHorse" (.literal "Matt")) .notEquals (.literal "Korse"))

#eval testConstraint { -- should be true - not enough info to reject
    functionName := "getHorse",
    functionParameter := "Matt",
    assignedValue := "Morse"
  } (.predicate (.functionCall "getHorse" (.literal "Matt")) .notEquals (.functionCall "getHorse" (.literal "Kate")))
