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

def printStream (stream : IO.FS.Stream) : IO Unit := do 
    repeat 
        let buffer <- stream.read bufsize 
        if !buffer.isEmpty then 
            let stdout <- IO.getStdout
            stdout.write buffer 

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
                printStream stream
                pure 64
            | none => pure 66 -- unreadable input
        pure 0
        