/- Ch 8.1 Tail Recursion -/

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

/- Ch 8.2 Proving Equivalence -/

theorem helper_add_sum_accum (xs : List Nat) :
  (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
   induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    -- Goal: n + (NonTail.sum ys + y) = Tail.sumHelper (n + y) ys
    rw [Nat.add_comm (NonTail.sum ys) y]  -- Swap to: n + (y + NonTail.sum ys)
    rw [←Nat.add_assoc]                    -- Reassociate to: (n + y) + NonTail.sum ys
    exact ih (n + y)                       -- Apply IH with (n + y)


theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs  -- extensional equality
  simp [Tail.sum]
  rw [←helper_add_sum_accum xs 0]
  simp

theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper
  <;> grind [NonTail.sum]

/- Ch 8.2.3 Exercise -/

theorem additive_identity : (n: Nat) → 0 + n = n := by
  intro n
  simp

theorem add_assoc (n m k : Nat) : n + m + k = n + (m + k) := by
  induction k with
  | zero => simp
  | succ x =>
    rw [Nat.add_assoc]

theorem add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => simp
  | succ x ih =>
    -- Goal: n + (x + 1) = (x + 1) + n
    -- IH: n + x = x + n
    rw [Nat.add_succ]        -- n + (x + 1) → (n + x) + 1
    rw [ih]                  -- (n + x) + 1 → (x + n) + 1
    rw [Nat.succ_add]        -- (x + n) + 1 → (x + 1) + n


theorem helper_reverse_accum (xs: List α) : (acc : List α) ->
  Tail.reverseHelper acc xs = (NonTail.reverse xs) ++ acc := by
  induction xs with
  | nil =>
    simp [Tail.reverseHelper, NonTail.reverse]
  | cons y ys ih =>
    intro acc
    simp [Tail.reverseHelper, NonTail.reverse]
    rw [List.append_cons]
    rw [List.append_assoc]
    rw [←List.singleton_append]
    rw [ih]

theorem helper_reverse_accum_2 (acc : List α) (xs: List α) :
  Tail.reverseHelper acc xs = (NonTail.reverse xs) ++ acc := by
  fun_induction Tail.reverseHelper with
  | case1 List.nil =>
    simp [NonTail.reverse]
  | case2 acc y ys ih =>
    simp [NonTail.reverse]
    rw [List.append_cons]
    rw [List.append_assoc]
    rw [←List.singleton_append]
    rw [ih]

theorem helper_reverse_accum_3 (acc : List α) (xs: List α) :
  Tail.reverseHelper acc xs = (NonTail.reverse xs) ++ acc := by
  fun_induction Tail.reverseHelper
  <;> grind [NonTail.reverse]


theorem non_tail_reverse_eq_tail_reverse :
  @NonTail.reverse = @Tail.reverse := by
  funext α xs
  simp [Tail.reverse]
  rw [helper_reverse_accum]
  simp

-- Cursor wrote helper_factorial_accum and non_tail_factorial_eq_tail_factorial
-- in a heartbeat
theorem helper_factorial_accum (n : Nat) (acc : Nat) :
  acc * NonTail.factorial n = Tail.factorialHelper acc n := by
  fun_induction Tail.factorialHelper
  <;> grind [NonTail.factorial]

theorem non_tail_factorial_eq_tail_factorial :
  NonTail.factorial = Tail.factorial := by
  funext n
  simp [Tail.factorial]
  rw [← helper_factorial_accum]
  simp


/- Ch 8.3 Arrays and Termination -/

inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem three_is_three : IsThree 3 := by
  constructor

theorem four_is_not_three : ¬ IsThree 4 := by
  intro h        -- Assume we have h : IsThree 4
  cases h        -- Case analysis - but IsThree only has constructor for 3!

inductive IsFive : Nat → Prop where
  | isFive : IsFive 5

theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree =>
    constructor

theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))



def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
  termination_by arr.size - i


/- Ch 8.4 MergeSort -/

-- Version with explicit termination proof (using ys instead of y'::ys')
def merge_with_proof [Ord α] (xs ys : List α) : List α :=
  match hxs : xs, hys: ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge_with_proof xs' ys
    | .gt => y' :: merge_with_proof xs ys'
  termination_by xs.length + ys.length

-- Simpler version where Lean figures it out automatically
def merge [Ord α] (xs ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y'::ys')
    | .gt => y' :: merge (x'::xs') ys'


def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)

theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
    case right => omega


theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith[splitList]
    apply splitList_shorter_le

theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right


def mergeSort [Ord α] (lst : List α) : List α :=
  match h : lst with
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    -- lst = x :: y :: xs, so lst.length ≥ 2 immediately
    have : lst.length ≥ 2 := by
      rw [h]; simp [List.length]
    let split := splitList lst
    have h1 : split.fst.length < lst.length := splitList_shorter_fst lst ‹lst.length ≥ 2›
    have h2 : split.snd.length < lst.length := splitList_shorter_snd lst ‹lst.length ≥ 2›
    merge (mergeSort split.fst) (mergeSort split.snd)
  termination_by lst.length

#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
#eval mergeSort [5, 3, 22, 15]

/- Ch 8.4 Exercises -/

-- ∀ n : 0 < n + 1
theorem zero_lt_n_plus_one : (n : Nat) → 0 < n + 1 := by
  intro n
  simp

-- ∀ n : 0 ≤ n
theorem zero_le_n : (n : Nat) → 0 ≤ n := by
  intro n
  simp

-- For all natural numbers n, k : (n + 1) - (k + 1) = n - k
theorem cancellation : (n k: Nat) → (n + 1) - (k + 1) = n - k := by
  intro n
  simp

-- For all natural numbers n, k: if k < n, then n ≠ 0
theorem k_not_zero : (n k: Nat) → k < n → n ≠ 0 := by
  intro n k h_lt h_eq
  rw [h_eq] at h_lt   -- Substitute n = 0, get k < 0
  simp at h_lt        -- k < 0 is impossible (contradiction)
