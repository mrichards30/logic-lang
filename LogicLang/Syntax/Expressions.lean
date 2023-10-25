inductive FnModifier where
    | injective : FnModifier
deriving Repr

inductive ComparisonOperation where
    | equals : ComparisonOperation
    | notEquals : ComparisonOperation
deriving Repr, BEq 

inductive LogicalConnective where
    | or : LogicalConnective 
    | and : LogicalConnective
    | implies : LogicalConnective
deriving Repr, BEq

instance : ToString LogicalConnective where
    toString op := match op with 
        | LogicalConnective.or => "∨"
        | LogicalConnective.and => "∧"
        | LogicalConnective.implies => "->"

inductive Value where
    | literal : String -> Value
    | functionCall : String -> Value -> Value
deriving Repr, BEq 

inductive LogicalPredicate where 
    | connect : LogicalPredicate -> LogicalConnective -> LogicalPredicate -> LogicalPredicate
    | predicate : Value -> ComparisonOperation -> Value -> LogicalPredicate
    | invertedPredicate : LogicalPredicate -> LogicalPredicate
deriving Repr, BEq

inductive Expression where
    | expressions : List Expression -> Expression
    | functionDefinition : (Option FnModifier) -> String -> String -> String -> Expression
    | enumDefinition : String -> List String -> Expression
    | assertion : LogicalPredicate -> Expression
deriving Repr

instance : Append Expression where 
    append a b := match (a, b) with 
        | (.expressions es1, .expressions es2) => .expressions (es1 ++ es2)
        | (.expressions es, e) | (e, .expressions es) => .expressions (e :: es)
        | (e1, e2) => .expressions [e1, e2]
