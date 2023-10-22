import LogicLang.Syntax.Parser
import LogicLang.Solver.Solver

/--
-       This file exists for easy testing purposes; the below string
-       can be used as a REPL environment instead of having to worry
-       about IO.
-/

def testQuestion := parseMultiLineString 
        "
        enum Person = Matt | Liz | Joe | Kate;
        enum Horse = Morse | Lorse | Jorse | Korse;

        fn getHorse :: Person -> Horse;

        getHorse(Matt) = Morse ∨ getHorse(Matt) = Lorse;
        getHorse(Liz) = Morse ∨ getHorse(Liz) = Lorse;
        Korse = getHorse(Kate);
        getHorse(Matt) != Lorse; 
        getHorse(Joe) = getHorse(Liz); 
        "
#eval testQuestion

#eval runSolver <$> testQuestion
