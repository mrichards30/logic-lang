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
    | functionDefinition : (Option FnModifier) -> String -> String -> String -> Expression
    | enumDefinition : String -> List String -> Expression
    | assertion : LogicalPredicate -> Expression
deriving Repr