import Mathlib.Data.Matrix.Basic

/-
This file introduces higher-order functions, dependent types and Curry-Howard correspondence.
-/

/- Curry-Howard correspondence -- why proof are programs -/

section STLC
/- simply typed lambda calculus -/

variable (P Q R : Type)

#check P

-- [Proposition ~ Type]

section p_of_P

variable (p : P)
#check (p : P)

end p_of_P

-- [Proof ~ Term]

#check P → Q
#check P → P

-- [Implication ~ Function Type]

#check (fun (p : P) => p : P → P)

-- Again, proof of the implication proposition is a function term, Proof ~ Term (Program)

#check (?_ : P → (Q → P)) -- Exercise: what is the term here?
#check (fun (p : P) => fun (q : Q) => p : P → (Q → P)) -- Answer

-- Another perspective is that the function will provide a proof term of the conclusion type when given a proof term of the premise type. Therefore it is a "witness" of the implication.

-- What about other logical connectives?

-- [Conjunction ~ Product Type] : A ∧ B ≃ A × B

section prod_type
#check P × Q

variable (p : P) (q : Q)

#check ((p, q) : P × Q)

#check (⟨p, q⟩ : P × Q)

variable (pq : P × Q)

#check (pq.1 : P)
#check (pq.2 : Q)

end prod_type

-- how to encode P ∧ Q → Q ∧ P ?
#check (?_ : P × Q → Q × P)
#check (fun (pq : P × Q) => (pq.2, pq.1) : P × Q → Q × P)

-- [Disjunction ~ Sum Type]

section sum_type
#check P ⊕ Q

variable (p : P) (q : Q)

#check (Sum.inl p : P ⊕ Q)

#check (Sum.inr q : P ⊕ Q)

variable (pq : P ⊕ Q)

#check (?_ : P)
#check (?_ : Q)

-- its not possible because we don't know which one it is, this even relates to the difference between constructive and classical logic.

-- what we can do is pattern match on it:

#check
  match pq with
  | Sum.inl p_val => "p_val"
  | Sum.inr q_val => "q_val"

end sum_type

-- how to encode P ∨ Q → Q ∨ P ?
#check (?_ : P ⊕ Q → Q ⊕ P)
#check (
  fun (pq : P ⊕ Q) =>
  match pq with
  | Sum.inl p_val => Sum.inr p_val
  | Sum.inr q_val => Sum.inl q_val
  : P ⊕ Q → Q ⊕ P
)

-- Negation : ~ A == A → False
-- [False ~ Empty Type]
#check Empty

def my_neg (P : Type) : Type := P → Empty
prefix:70 " ~ " => my_neg

#check P → ~ ~ P

#check P → ((P → Empty) → Empty)

#check (_ : P → ~ ~ P)

#check (fun (p : P) =>  _ : P → ~ ~ P)
#check (fun (p : P) => (fun (p_to_empty : P → Empty) => _ ): P → ~ ~ P)
#check (fun (p : P) => (fun (p_to_empty : P → Empty) => p_to_empty p ): P → ~ ~ P)

#check (
  by
    intro p
    intro p_to_empty
    apply p_to_empty
    exact p
  : (P → ~ ~ P))

-- So far we showed the premitive stage of Curry-Howard correspondence in STLC.

/-

[Proposition ~ Type]
[Proof ~ Term]
[Implication ~ Function Type]
[Conjunction ~ Product Type]
[Disjunction ~ Sum Type]
[False ~ Empty Type]

[Propositional Logic ~ Simply Typed Lambda Calculus]
- Computer science perspective: Propositional logic corresponds to the simply typed λ-calculus, which is strongly normalizing and therefore decidable — every proof term reduces to a unique normal form.

-/


end STLC


section PropInsteadofType
-- Now we switch to Lean's Prop universe instead of Type universe for logic.
-- The problem: do we need to distinguish different proofs for the same proposition?

variable (P : Type)
variable (p1 p2 : P)

-- example : p1 = p2 := by rfl

variable (P' Q' R': Prop)
variable (p1' p2' : P')
example : p1' = p2' := by rfl
-- Different proofs of the same proposition are definitionally equal in Prop universe.

-- Existing connectives in Prop universe

#check P' ∧ Q'
#check And P' Q'

#check P' ∨ Q'
#check Or P' Q'

#check ¬ P'
#check Not P'

-- an exercise for tatic proof:
-- A complicated propositional logic tautology: Pierce's Law
-- ((P' → Q') → P') → P'
example : ((P' → Q') → P') → P' := by
  intro h
  by_contra hnp
  apply hnp
  apply h
  intro hp
  exfalso
  exact hnp hp

-- Another complex tautology: Double negation elimination implies excluded middle
-- (¬¬P' → P') → (P' ∨ ¬P')
example : (¬¬P' → P') → (P' ∨ ¬P') := by
  intro dne
  by_contra h
  apply h
  right
  intro hp
  apply h
  left
  exact hp

-- De Morgan's law with triple negation
-- ¬(P' ∧ Q') → (¬P' ∨ ¬Q')
example : ¬(P' ∧ Q') → (¬P' ∨ ¬Q') := by
  intro h
  by_contra h2
  apply h
  constructor
  · by_contra hnp
    apply h2
    left
    exact hnp
  · by_contra hnq
    apply h2
    right
    exact hnq

/- Critical Question: what is the difference between Bool and Prop? -/

end PropInsteadofType


section DependentTypes

-- First order logic with predicates:

variable (A : Type)
variable (f : A → Prop)

-- a simple FOL tautology: ∀ x ∈ A, P(x) → P(x)
-- How to encode it?
#check (?_ : forall (x : A), f x → f x)

-- Types as first class citizens, types are terms too!
-- C++: type of type does not exist
-- OCaml: type of type is Type, but types cannot be passed to functions

#check (Type : Type 1)
#check (ℕ : Type)

-- and actually in Lean, arrow types are special cases of dependent function types (Π types)
#check (A → A)  -- non-dependent function type
#check (forall (_ : A), A)  -- dependent function type

-- and you can even check the Lean code definition for arrow types

example : (A → A) = (forall (_ : A), A) := by rfl


-- other examples of dependent types

-- Dependent pairs where the second component's type depends on the first
#check (Σ (n : Nat), Vector Nat n)
#check (Sigma (fun (n : Nat) => Vector Nat n))

-- Equality types that depend on terms
#check (fun (x y : Nat) => x = y)


-- existential quantifier: it is a dependent sum type
#check Exists f
#check Exists (fun (x : A) => f x)
#check exists (x : A), f x

example : Exists f = Exists (fun (x : A) => f x) := by rfl
example : Exists f = exists (x : A), f x := by rfl

-- suggestion: take a look at Core.lean


/- exerciese -/

-- some complicated FOL tautologies with quantifiers
-- Universal instantiation: ∀x, P(x) → P(a) for any specific a
example (a : A) : (∀ x, f x) → f a := by
  intro h
  exact h a

-- Existential generalization: P(a) → ∃x, P(x) for any specific a
example (a : A) : f a → (∃ x, f x) := by
  intro h
  use a

-- Distribution of universal quantifier over implication
variable (g : A → Prop)
example : (∀ x, f x → g x) → ((∀ x, f x) → (∀ x, g x)) := by
  intro h hf x
  apply h
  exact hf x

-- Relationship between universal and existential quantifiers
example : (∀ x, f x) → ¬(∃ x, ¬f x) := by
  intro h hex
  obtain ⟨a, hna⟩ := hex
  exact hna (h a)

-- Another direction of De Morgan for quantifiers
example : ¬(∀ x, f x) → (∃ x, ¬f x) := by
  intro h
  by_contra hne
  apply h
  intro x
  by_contra hnfx
  apply hne
  use x

-- Swapping quantifiers (when they're the same type)
variable (B : Type)
variable (R : A → B → Prop)
example : (∀ x, ∃ y, R x y) → (∃ y, ∀ x, R x y) ∨ True := by
  intro h
  right
  trivial
-- Note: The reverse direction is not always true, so we added ∨ True

-- A more complex tautology with mixed quantifiers
example : (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) := by
  intro h y
  obtain ⟨x, hx⟩ := h
  use x
  exact hx y



end DependentTypes


-- TODO: Constructive (Intuitionistic) Logic v.s. Classical logic

-- TODO: consistent axioms in CIC type theory





inductive MyList (α : Type) : Type
  | nil : MyList α
  | cons : α → MyList α → MyList α

#check MyList.cons

#check MyList

#check Type → Type

#check Nat → (Nat → Nat)

#check Nat → (Nat → Type)

#check Matrix


-- About empty and proof by refutation
