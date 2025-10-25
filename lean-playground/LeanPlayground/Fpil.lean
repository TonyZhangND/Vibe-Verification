/-
  Functional Programming In Lean
  https://lean-lang.org/functional_programming_in_lean/
-/

def hello := "world"

#eval hello

#eval 3 + 2

#eval String.append "Hello, " "Lean!"

#evalString.append "it is " (if 1 > 2 then "yes" else "no")

#check( hello )

def add1 (n: Nat) : Nat := n + 1

#eval add1 1



/- Exercise 1.4.3 -/

structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0, y := 0.0 }

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume (rectangularPrism : RectangularPrism) : Float :=
  rectangularPrism.height * rectangularPrism.width * rectangularPrism.depth

#eval volume { height := 1.0, width := 2.0, depth := 3.0 }

structure Segment where
  p1: Point
  p2: Point

def length (segment : Segment) : Float :=
  let dx := segment.p2.x - segment.p1.x
  let dy := segment.p2.y - segment.p1.y
  Float.sqrt (dx * dx + dy * dy)

#eval length { p1 := { x := 0.0, y := 0.0 }, p2 := { x := 3.0, y := 4.0 } }

/- Chapter 1.6 -/

structure PPoint (α : Type) where
  x : α
  y : α

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

/- Exercise 1.6.5 -/

def last? (s : List α) : Option α :=
  match s with
  | [] => none
  | [x] => some x
  | _ :: xs => last? xs

#eval last? [1, 2, 3, 4, 5, 6]

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs => if predicate x then some x else findFirst? xs predicate

#eval List.findFirst? [1, 2, 3, 4, 5, 6] (fun x => x % 2 == 0)

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

#eval zip [1, 2, 3] [4, 5, 6]
#eval zip [1, 2, 3] [4]

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, _ => []
  | _, [] => []
  | n, x :: xs => x :: take (n - 1) xs

#eval take 3 [1, 2, 3, 4, 5, 6]
