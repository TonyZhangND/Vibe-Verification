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
