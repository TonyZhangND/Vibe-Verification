
def bufsize : USize := 20 * 1024 -- 20KB

partial def dump (stream: IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle <- IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨ filename ⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

def help : String :=
  "feline - concatenate files and print to standard output

USAGE:
  feline [OPTIONS] [FILE...]

OPTIONS:
  --help    Show this help message

ARGUMENTS:
  FILE      Files to concatenate (use '-' for stdin)
            If no files specified, reads from stdin

EXAMPLES:
  feline file.txt          Print contents of file.txt
  feline file1 file2       Print contents of file1 then file2
  feline -                 Read from stdin
  feline file.txt -        Print file.txt, then read from stdin"

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--help"] => do
      IO.println help
      pure 0
  | [] => process 0 ["-"]
  | _ =>
      if args.contains "--help" then do
        IO.println help
        pure 0
      else
        process 0 args
