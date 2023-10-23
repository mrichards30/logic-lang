import LogicLang.Editor.SolutionTableConstructor
import LogicLang.Syntax.Parser
import LogicLang.Solver.Solver

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
    let fileExists <- filename.pathExists
    if not fileExists then
        let stderr <- IO.getStderr
        stderr.putStrLn s!"File {filename} not found"
        pure none
    else
        let handle <- IO.FS.Handle.mk filename IO.FS.Mode.read
        pure (some (IO.FS.Stream.ofHandle handle))

def bufsize : USize := 20 * 1024

def convertStreamToString (stream : IO.FS.Stream) : IO String := do 
    let mut accumulator := ""
    let mut buffer <- stream.read bufsize 
    
    while !buffer.isEmpty do
        let bufferAsString := String.fromUTF8Unchecked buffer
        accumulator := s!"{accumulator}{bufferAsString}"
        buffer <- stream.read bufsize 

    return accumulator
    

def getReadableResultFromContents (streamContents : String) : Option String := 

    let expression := parseMultiLineString streamContents
    let parserResponse := runSolver <$> expression
    
    match parserResponse with
        | .error e => some e 
        | .ok (_, e) => createAsciiTable e


-- exit codes from https://man.freebsd.org/cgi/man.cgi?query=sysexits&apropos=0&sektion=0&manpath=FreeBSD+4.3-RELEASE&format=html 

def main (args : List String) : IO UInt32 := do
    match args with
    | [] => 
        IO.println "please enter a file name"
        pure 64 -- incorrect usage
    | fileName :: _ =>
        let fileContents <- fileStream (System.FilePath.mk fileName) 
        match fileContents with 
            | some stream => 

                let streamContents <- convertStreamToString stream

                let result := getReadableResultFromContents streamContents

                match result with 
                    | some e => IO.eprintln e
                    | none => pure ()

                pure 64 
            | none => pure 66 -- unreadable input
        pure 0

#eval main ["./Examples/valid_example1.logic"]
#eval main ["./Examples/syntax_error1.logic"]
#eval main ["./Examples/syntax_error2.logic"]
