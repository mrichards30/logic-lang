import LogicLang.Syntax.Parser
import LogicLang.Solver.Solver

/--
-       This file exists for easy testing purposes; the below string
-       can be used as a REPL environment instead of having to worry
-       about IO.
-/

def testQuestion := parseMultiLineString 
        "
        enum Horse = Morse | Lorse;
        enum Person = Matt | Liz | Kate | Joe;

        fn getHorse :: Person -> Horse;

        getHorse(Matt) = Morse;
        getHorse(Liz) = getHorse(Matt) ∨ getHorse(Liz) = getHorse(Kate);
        getHorse(Kate) = getHorse(Joe);
        getHorse(Joe) = Lorse; 
        "
#eval testQuestion

#eval runSolver <$> testQuestion
