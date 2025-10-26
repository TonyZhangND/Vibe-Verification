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

def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

def OnePlusOneIsTwo : Prop := 1 + 1 = 2

#check OnePlusOneIsTwo

theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
#eval third woodlandCritters (by decide)


/- Proof Exercises -/

theorem t1 : 2 + 3 = 5 := by
  rfl

theorem t2 : 15 - 8 = 7 := by
  rfl

theorem t3 : "Hello".append "World" = "HelloWorld" := by
  rfl

theorem t4 : 5 < 18 := by
  omega


def fifth (xs : List α) (ok : xs.length > 4) : α :=
  xs[4]

def woodlandCrittersPlus : List String :=
  ["hedgehog", "deer", "snail", "fox", "rabbit"]

#eval fifth woodlandCrittersPlus (by decide)
