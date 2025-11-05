/-
  Functional Programming In Lean
  https://lean-lang.org/functional_programming_in_lean/
-/

inductive Pos : Type where
  | one : Pos
  | succ : Pos -> Pos

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)


-- Define a type class Plus, that overloads operations with respect to a type α.
-- It has one overloaded operation called `plus`
class Plus (α : Type) where
  plus : α → α → α

/- Type classes are first class, just as types are first class. In particular, a type class is another kind of type. The type of Plus is Type → Type, because it takes a type as an argument (α) and results in a new type that describes the overloading of Plus's operation for α. -/

-- Overload plus for a particular type, using an instance:
instance : Plus Nat where
  plus := Nat.add

open Plus (plus)

#eval plus 5 3

instance : Plus Pos where
  plus := Pos.plus

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))

def fourteen : Pos := plus seven seven


/- Add is a Lean built-in type class for homogeneous addition
    (i.e., both args have the same type).
  Defining an instance of Add Pos allows Pos values to use ordinary addition syntax:
-/
instance : Add Pos where
  add := Pos.plus

#eval seven + seven
#eval Add.add seven seven

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

def three : Pos := Pos.succ (Pos.succ (Pos.succ Pos.one))

#eval posToString true three


def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1


instance : ToString Pos where
  toString x := toString (x.toNat)

#eval s!"There are {seven}"

/- Let's implement multiplication for Pos -/

def Pos.mul : Pos → Pos → Pos
   | Pos.one, k => k
   | Pos.succ n, k => (n.mul k).plus n

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]

/- Zero, One and OfNat are built-in type classes that allow us to represent
arbitrary types with numeric literals -/

instance : One Pos where
  one := Pos.one

#eval (1: Pos) + (1 : Pos)

inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)

#eval (0 : LT4)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n


/- Ch 3.1.6 Exercises -/

-- Structure-based positive number representation
structure Pos2 where
  succ ::
  pred : Nat

-- Examples of creating Pos2 values
def eight : Pos2 := Pos2.succ 7  -- represents 8 (successor of 7)
def twelve : Pos2 := Pos2.succ 11 -- represents 12 (successor of 11)

-- Convert Pos2 to Nat (just add 1 to the predecessor)
def Pos2.toNat (p : Pos2) : Nat := p.pred + 1

-- Addition for Pos2
def Pos2.plus : Pos2 → Pos2 → Pos2
  | succ x, succ y => Pos2.succ (x + y + 1)

instance : Add Pos2 where
  add := Pos2.plus

-- Multiplication for Pos2
def Pos2.mul : Pos2 → Pos2 → Pos2
  | succ x, succ y => Pos2.succ (x * y + x + y)

instance : Mul Pos2 where
  mul := Pos2.mul

-- ToString for Pos2
instance : ToString Pos2 where
  toString p := toString p.toNat


-- Test it out
#eval eight + twelve  -- should be 20
#eval eight * twelve  -- should be 96
#eval s!"Eight is {eight}"


-- Even numbers: 0, 2, 4, 6, ...
-- succ adds 2 (not 1)
inductive Evens : Type where
  | zero : Evens
  | succ : Evens -> Evens

-- Convert to Nat (each succ adds 2)
def Evens.toNat : Evens → Nat
  | Evens.zero => 0
  | Evens.succ n => n.toNat + 2

-- Addition for even numbers
def Evens.plus : Evens → Evens → Evens
  | Evens.zero, k => k
  | Evens.succ n, k => Evens.succ (n.plus k)

-- Multiplication for even numbers
def Evens.mul : Evens → Evens → Evens
  | Evens.zero, _ => Evens.zero
  | Evens.succ n, k => k.plus (k.plus (n.mul k))

-- Type class instances
instance : ToString Evens where
  toString e := toString e.toNat

instance : Add Evens where
  add := Evens.plus

instance : Mul Evens where
  mul := Evens.mul

-- Examples
def two : Evens := Evens.succ Evens.zero
def four : Evens := Evens.succ two
def six : Evens := Evens.succ four

#eval two + four  -- should be 6
#eval two * four  -- should be 8
#eval s!"Two times four is {two * four}"
