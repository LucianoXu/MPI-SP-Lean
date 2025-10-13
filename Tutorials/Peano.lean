import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

/-
This file introduces how to operate the Lean language, without touching too much of the dependent type theory under the hood.
-/

/- Let's start with commands first ... -/

/- check -/

#check 0

#check 1

#check true

#check false

#check ℕ

#check Type

#check Type 1

#check 0 + 1

#check not true

#check (1 : ℕ)

#check_failure (1 : Bool)

#check ((1 : ℕ) : ℕ)

#check (1 : (ℕ : Type))

#check (0 = 1)

#check ∀ (p q: Prop), p → q → p


/- eval -/

#eval 1 + 2

#eval not true

/- print -/

#print not


/- Then let's start with some functional programming basics -/

/- datatype grammar -/

inductive my_bool : Type
  | my_true : my_bool
  | my_false : my_bool

/- Now you can consider the signature as a form of function name, parameter and result type, but
it's actually much deeper. -/

def my_not (b : my_bool) : my_bool :=
  match b with
  | .my_true => .my_false
  | .my_false => .my_true

#eval my_not my_bool.my_true


def nat_smaller_than_3 (n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => true
  | 2 => true
  | _ => false

/-
def nat_factorial (n : Nat) : Nat :=
  match n with
  | ? ? ?
-/


/-
Now let's start our journey on natural numbers

How to define natural numbers?

One possibility: by enumeration of 0, 1, 2, 3, ....
But we want finite axiomization.

Peano: 5 axioms to describe natural numbers
1. `0` is a natural number
2. is `a` is natural number, then the successor of `a` (`S a`) is a natural number as well.
3. for natural numbers `b` and `c`, `b = c` if and only if `S a = S b` (injectivity of constructors)
4. `0` is not the succesor of any natural number
5. principle of induction
-/

section MyNatSection

inductive MyNat : Type
| O : MyNat
| S : MyNat → MyNat



def add (x y : MyNat) : MyNat :=
  match x with
  | .O => y
  | .S z => .S (add z y)


theorem add_zero_left (x : MyNat) : add MyNat.O x = x := by
  rfl

example (x : MyNat) : add MyNat.O x = x := by
  simp [add]

-- add `add` to simp
attribute [simp] add

example (x : MyNat) : add MyNat.O x = x := by
  simp


/- this is the funciontal construction -/
example (x : MyNat) : add MyNat.O x = x := rfl
example (x : MyNat) : add MyNat.O x = x := Eq.refl x


@[simp]
theorem add_zero_right (x : MyNat) : add x MyNat.O = x := by
  induction x with
  | O => rfl
  | S z ih =>
    simp [add]
    exact ih

example x : add x MyNat.O = x := by
  induction x with
  | O => simp
  | S z ih => simp


local infix: 55 "+" => add


@[simp]
theorem S_add_right (x : MyNat) (y : MyNat) : x + y.S = (x + y).S := by
  induction x with
  | O => simp
  | S z ih =>
    simp
    exact ih

example (x y : MyNat) : x + y.S = (x + y).S := by
  induction x; simp; simp[*]

example (x y : MyNat) : x + y.S = (x + y).S := by
  induction x <;> simp[*]

/- let's customize our own handy tactic -/

open Lean Parser.Tactic Elab Tactic
syntax (name := indsimp) "indsimp" elimTarget : tactic
macro_rules
  | `(tactic| indsimp $t:elimTarget) => `(tactic| induction $t <;> simp [*])
-----------------------------------------------------------------------------

example (x y : MyNat) : x + y.S = (x + y).S := by
  indsimp x


theorem my_add_comm (x y : MyNat) : x + y = y + x := by
  induction x with
  | O => simp
  | S z ih => simp; exact ih

theorem my_add_assoc (x y z: MyNat) : (x + y) + z = x + (y + z) := by
  indsimp x


/- example of using the theorems -/

example (x y : MyNat) : (x + y) + x = x + (x + y) := by
  rw [my_add_comm]


example (x y : MyNat) : (x + y) + x = (y + x) + x := by
  rw [my_add_comm x y]

example (x y z : MyNat) : (x + y) + z = x + (z + y) := by
  rw [my_add_assoc]
  rw [my_add_comm z y]

example (x y z : MyNat) : (x + y) + z = x + (z + y) := by
  rw [my_add_assoc, my_add_comm z y]

/- proof by calc -/
example (x y z : MyNat) : (x + y) + z = x + (z + y) := by
  calc
    (x + y) + z = x + (y + z) := by rw [my_add_assoc]
    _ = x + (z + y)           := by rw [my_add_comm z y]

/- proof by navigation and rewriting -/
example (x y z : MyNat) : (x + y) + z = x + (z + y) := by
  rw [my_add_assoc]
  conv =>
    lhs -- navigates to the left-hand side of a relation (equality, in this case)
    congr -- congrence, i.e. x = x' /\ y = y' /\ z = z' /\ => f(x, y, z) = f(x', y', z')
    · rfl
    · rw [my_add_comm]



/- Now we come to multiplication -/

/--
x * y defined as
- 0 * y = 0
- (1 + x) * y = x * y + y
-/
@[simp]
def mul (x y : MyNat) : MyNat :=
  match x with
  | .O => .O
  | .S z => add y (mul z y)

local infixl: 60 "*" => mul


@[simp]
theorem mul_zero_right (x : MyNat) : x * MyNat.O = MyNat.O := by
  indsimp x

@[simp]
theorem S_mul_right (x y : MyNat) : x * y.S = x + x * y := by
  induction x with
  | O => simp
  | S z ih =>
    simp [ih]
    calc
      _ = (y + z) + z * y := by rw [my_add_assoc]
      _ = (z + y) + z * y := by rw [my_add_comm y z]
      _ = _               := by rw [my_add_assoc]


theorem my_mul_comm (x y : MyNat) : x * y = y * x := by
  indsimp x



theorem mul_add_distr (x y z : MyNat) : x * (y + z) = (x * y) + (x * z) := by
  induction x with
  | O => simp
  | S w ih =>
    simp [ih]
    calc
      (y + z) + ((w * y) + (w * z)) = y + (z + ((w * y) + (w * z))) := by rw [my_add_assoc]
      y + (z + ((w * y) + (w * z))) = y + ((z + (w * y)) + (w * z)) := by rw [my_add_assoc]
      y + ((z + (w * y)) + (w * z)) = y + (((w * y) + z) + (w * z)) := by rw [my_add_comm z (w * y)]
      y + (((w * y) + z) + (w * z)) = y + ((w * y) + (z + (w * z))) := by rw [my_add_assoc]
      _ = (y + (w*y)) + (z + (w*z))                                 := by rw [my_add_assoc]


theorem add_mul_distr (x y z : MyNat) : (x + y) * z = (x * z) + (y * z) := by
  calc
    (x+y)*z = z*(x+y) := by rw [my_mul_comm]
          _ = (z*x) + (z*y) := by rw [mul_add_distr]
          _ = _ := by rw [my_mul_comm z x, my_mul_comm z y]


theorem my_mul_assoc (x y z : MyNat) : (x * y) * z = x * (y * z) := by
  induction x with
  | O => simp
  | S w ih =>
    simp
    rw [add_mul_distr, ih]

end MyNatSection

/- How should we improve the level of automation -/

/-
Having proved the arithmetic lemmas, we now hook `MyNat` into Lean's type class hierarchy so
the standard notation and automation (e.g., `simp`, `abel`) understand our definitions.
-/

/-
`Zero` ties `MyNat.O` to the literal `0`.
-/
instance : Zero MyNat where
  zero := MyNat.O

/-
`One` declares the successor of zero as the canonical `1`.
-/
instance : One MyNat where
  one := MyNat.O.S

/-
`HAdd` exposes our custom `add` function through the `x + y` syntax.
-/
instance : HAdd MyNat MyNat MyNat where
  hAdd := add

/-
`HMul` lets us keep using the familiar `x * y` notation for multiplication.
-/
instance : HMul MyNat MyNat MyNat where
  hMul := mul


/-
`AddSemigroup` packages associativity, confirming `(MyNat, +)` is an additive semigroup.
-/
instance : AddSemigroup MyNat where
  add := HAdd.hAdd
  add_assoc := my_add_assoc

/-
`AddZeroClass` provides the left and right identity laws so Lean treats `0` as the neutral element.
-/
instance : AddZeroClass MyNat where
  add := HAdd.hAdd
  zero := 0
  zero_add := add_zero_left
  add_zero := add_zero_right


-- more structure needed ...

-- print the definition bound to '+' infix
#print HAdd.hAdd

@[simp]
theorem hadd_def (x y : MyNat) : x + y = add x y := rfl

/-
Lean's additive monoid API expects a natural-number scalar multiplication `nsmul`, so we supply
it by recursion on the scalar.
-/
def nsmul (n : Nat) (x : MyNat) : MyNat :=
  match n, x with
  | .zero, _ => .O
  | .succ n, x => add x (nsmul n x)



@[simp]
theorem my_zero_nsmul (x : MyNat) : nsmul 0 x = MyNat.O := rfl

@[simp]
theorem my_succ_nsmul (n : Nat) (x : MyNat) : nsmul n.succ x = nsmul n x + x := by
  simp [nsmul]
  induction x with
  | O => simp
  | S z ih => rw [my_add_comm]


/-
`AddMonoid` bundles scalar multiplication via `nsmul`, matching the usual additive monoid on naturals.
-/
instance : AddMonoid MyNat where
  nsmul := nsmul
  nsmul_zero := my_zero_nsmul
  nsmul_succ := my_succ_nsmul


/-
`AddCommMagma` adds the commutativity law we proved with `my_add_comm`.
-/
instance : AddCommMagma MyNat where
  add := HAdd.hAdd
  add_comm := my_add_comm


/-
`AddCommMonoid` combines all the previous structure, so Lean now treats `MyNat` like the usual natural numbers under addition.
-/
instance : AddCommMonoid MyNat where

/- Now we can use the `abel` tactic provided by Mathlib -/
example (x y z : MyNat) : x + z + y + x + y = y + x + (y + x + z):= by abel


/- The framework of type classes allows us to reason about an abstract `AddCommMonoid` -/
example [AddCommMonoid α] (x y z : α) : x + z + y + x + y = y + x + (y + x + z):= by abel

example {α : Type u} [AddCommMonoid α] (x y z : α) : x + z + y + x + y = y + x + (y + x + z):= by abel

/-
Exercise:
1. Define factorial on `MyNat` and the factorial of a number `a` is always larger than `a`.

2. Extend `MyNat` with an order relation `≤` defined by repeated successor, then prove it is reflexive and transitive.

3. Define `MyList` as a new inductive data type, which holds lists of `MyNat` instances. Try to define functions that append to the head and end of the list, the concatenation function, the reverse function. Declare and prove some properties of these functions.
-/
