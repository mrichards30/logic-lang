import LogicLang.Syntax.Scanner

structure ParserContext (ε i α : Type) where 
  input : i 
  result : Option α := none  
  errors : List ε := []
deriving Repr

class WithErrors (X : Type -> Type -> Type -> Type) where 
  error (val : ε) (current : X ε i α) : X ε i α

instance : WithErrors ParserContext  where
  error x current := { current with errors := x :: current.errors }

class HandlerChain (X : Type -> Type -> Type) where 
  yield (val : α) (current : X i α) : X i α
  delegate (current : X i α) (next : i -> X i α) : X i α

instance : HandlerChain (ParserContext ε)  where 
  yield x current := { current with result := x }
  delegate current next := match current.result with
    | some _ => current 
    | none => {
      current with 
        result := current.input >>= (λi => (next i).result)
    }

instance : Monad (ParserContext ε (List Token)) where 
  bind x next := { x with 
      result := x.result >>= (λr => (next r).result) 
    }
  pure x := { result := x, input := [] }
  

infix:72 " ~> " => HandlerChain.delegate

abbrev TokenParserContext (α : Type) := ParserContext (Token × String) (List Token) α 

-- Example

def exampleParserContext : TokenParserContext Expression := {
  input := [],
  result := none,
  errors := []
}

#eval exampleParserContext 
      ~> λ_ => { input := [], result := none }
      ~> λ_ => { input := [], result := some (Expression.enumDefinition "First" ["1"]) }
      ~> λ_ => { input := [], result := some (Expression.enumDefinition "Second" ["2"]) }

#eval exampleParserContext 
      ~> λ_ => { input := [], result := none }
      ~> λ_ => { input := [], result := some (Expression.enumDefinition "First" ["1"]) }
      ~> λ_ => { input := [], result := some (Expression.enumDefinition "Second" ["2"]) }

def ParserContext.error (error : ε) (ctx : ParserContext ε α i) : ParserContext ε α i := 
  { ctx with errors := error :: ctx.errors }
