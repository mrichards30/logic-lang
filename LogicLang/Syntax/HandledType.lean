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