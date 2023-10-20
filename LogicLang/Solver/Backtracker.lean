import LogicLang.Syntax.Expressions 

structure SolverComponents where 
  constraints : Expression 
deriving Repr 

def testConstraint (expr : Expression) (world : List Expression) : Bool := True 
