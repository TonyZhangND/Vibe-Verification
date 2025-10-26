/-
  Functional Programming In Lean
  https://lean-lang.org/functional_programming_in_lean/
-/

-- def main : IO Unit := do
--   let stdin ← IO.getStdin
--   let stdout ← IO.getStdout
--   stdout.putStrLn "How would you like to be addressed?"
--   let input ← stdin.getLine
--   let name := input.dropRightWhile Char.isWhitespace
--   stdout.putStrLn s!"Hello, {name}!"


-- def nTimes (action : IO Unit) : Nat → IO Unit
--   | 0 => pure ()
--   | n + 1 => do
--     action
--     nTimes action n


-- #evalnTimes (IO.println "Hello, Tony san!") 3


def main : IO Unit := do
  -- using `:=`to assign the result of IO.println "Hello!" to englishGreeting. Compared to using `←`, it does not execute the IO action.
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
