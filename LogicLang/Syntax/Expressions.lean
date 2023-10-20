inductive FnModifier where
    | injective : FnModifier
deriving Repr

inductive ComparisonOperation where
    | equals : ComparisonOperation
    | notEquals : ComparisonOperation
deriving Repr

inductive LogicalConnective where
    | or : LogicalConnective 
    | and : LogicalConnective
deriving Repr

instance : ToString LogicalConnective where
    toString op := match op with 
        | LogicalConnective.or => "∨"
        | LogicalConnective.and => "∧"

inductive Value where
    | literal : String -> Value
    | functionCall : String -> Value -> Value
deriving Repr

inductive LogicalPredicate where 
    | connect : LogicalPredicate -> LogicalConnective -> LogicalPredicate -> LogicalPredicate
    | predicate : Value -> ComparisonOperation -> Value -> LogicalPredicate
    | invertedPredicate : LogicalPredicate -> LogicalPredicate
deriving Repr

inductive Expression where
    | expressions : List Expression -> Expression
    | functionDefinition : (Option FnModifier) -> String -> String -> String -> Expression
    | enumDefinition : String -> List String -> Expression
    | assertion : LogicalPredicate -> Expression
deriving Repr

instance : Append Expression where 
    append a b := match (a, b) with 
        | (.expressions es1, .expressions es2) => .expressions (es1 ++ es2)
        | (.expressions es, e) => .expressions (e :: es)
        | (e, .expressions es) => .expressions (e :: es)
        | (e1, e2) => .expressions [e1, e2]
