/- Ch 8.1. Tail Recursion -/

def NonTail.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => (sum xs) + x


def Tail.sumHelper (acc: Nat) (xs : List Nat) : Nat :=
  match xs with
  | [] => acc
  | x :: xs => sumHelper (acc + x) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

def NonTail.reverse (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs => (reverse xs) ++ [x]


def Tail.reverseHelper (acc : List α) (xs : List α) : List α :=
  match xs with
  | [] => acc
  | x :: xs => reverseHelper ([x] ++ acc) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs


def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def Tail.lengthHelper (acc: Nat) (xs : List α) : Nat :=
  match xs with
  | [] => acc
  | _ :: xs => lengthHelper (acc + 1) xs

def Tail.length (xs : List α) : Nat :=
  Tail.lengthHelper 0 xs

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def Tail.factorialHelper (acc: Nat) (x : Nat) : Nat :=
  match x with
  | 0 => acc
  | n + 1 => factorialHelper (acc * (n + 1)) n

def Tail.factorial (n : Nat) : Nat :=
  Tail.factorialHelper 1 n

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filterHelper (acc : List α) (p : α → Bool) (xs : List α)
: List α :=
  match xs with
  | [] => acc
  | x :: xs =>
    if p x then
      filterHelper (x :: acc) p xs
    else
      filterHelper acc p xs

def Tail.filter (p : α → Bool) (xs : List α) :=
  Tail.reverse (Tail.filterHelper [] p xs)
