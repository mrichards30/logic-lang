/-

The type described in this file implements the chain of responsibility pattern.

That is, we can create a pipeline of handlers that take some input to a HandledResult,
where exactly one will end up handling the input and either succeed or fail; the others 
that deem the input to not be their responsibility will delegate the input to the next 
function in the pipeline.

An implementation of the pipeline will end by failing if we finish still trying to
delegate the input.

Example:

fn handler : (input : α) -> HandledResult {
  if !shouldHandle then return .delegate input

  do some computation

  return .failed x or .handled x
}

-/

inductive HandledResult (ε α i : Type u) where
  -- it is not my responsibility to compute this value 
  | delegate (input : i) : HandledResult ε α i
  -- it is my responsibility to compute this value; computation successful
  | handled (value : α) : HandledResult ε α i
  -- it is my responsibility to compute this value; however, an error occurred
  | failed (error : ε) : HandledResult ε α i
deriving Repr

instance : Monad (HandledResult ε α) where 
    pure x := HandledResult.delegate x
    bind attempt next := match attempt with 
        | HandledResult.failed e => HandledResult.failed e
        | HandledResult.handled x => HandledResult.handled x
        | HandledResult.delegate input => next input