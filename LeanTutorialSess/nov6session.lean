import Mathlib.Data.Real.Basic

/-
# Part 4. Working With Proof Terms

Recall that:
1. A _proposition_ `A` has type `A : Prop`.
2. A _proof term_ `hA` of `A` has type `hA : A`, and acts as a proof of `A`.
-/

#check 1 = 1
#check 1 ≠ 1
#check (rfl : 1 = 1)

/-
Proof term of implication `A → B` acts like
a function that takes proof term `hA : A` of A
and returns a new proof term `hB : B` of B
-/

-- Recall our notation of functions
-- The function below is f(x) = 2x
#check (λ x : ℕ ↦ 2 * x) -- Type ℕ → ℕ

-- 'let A, B, C be arbitrary propositions'
variables (A B C : Prop)

theorem aba : A → (B → A) :=
  λ ha : A ↦ (λ hb : B ↦ ha)

def return_fst : ℕ → ℕ → ℕ :=
  λ x : ℕ ↦ (λ y : ℕ ↦ x)

#eval return_fst 777 99

/-
Underlines from Lean Server
- blue: informs user
- orange: warning / style issue / sorry
- red: error / type checking fails
-/

/-
## Tactic mode

- Activated by starting with `by` after `:= `
- Then apply tactics (functions on proof terms) to generate proof
-/

example : A → B → A := by
  intros ha hb -- corresponds to λ in proof term
  exact ha

variables (A1 A2 A3 : Prop)

example : A1 → (A2 → (A3 → B)) := by
  intros ha1 ha2 ha3
  sorry

example : ((A1 → A2) → A3) → B := by
  intros h
  sorry

/-
A1 → A2 → A3 → B

A1, A2, A3 assume -> Prove B

A1 → (A2 → (A3 → B))

((A1 → A2) → A3) → B

f(3) -> f 3
-/

theorem triangle : (A → B) → (B → C) → (A → C) :=
  λ (hab : A → B) (hbc : B → C) ↦
    (λ ha : A ↦ (hbc (hab ha : B) : C)) -- A → C

example : (A → B) → (B → C) → (A → C) := by
  intro hab hbc ha
  -- #1. exact hbc (hab ha)
  -- #2.
  apply hbc
  apply hab
  -- #2-1. exact ha
  assumption

example : (A → B) → (B → C) → (A → C) := by
  intro hab hbc
  intros
  apply hbc
  apply hab
  assumption
  -- intros; assumption

/-
(Dependent version)
Proof term of `∀ a : A, P a` acts like
a function that takes term `a : A`
and returns a new proof term `ha : P a`
-/

-- Proposition about natural number
variables (Q : ℕ → Prop)

def P (n : ℕ) : Prop := ∃ m, n = 2 * m

#check Q 5


theorem put3 (h : ∀ x : ℕ, P x) : P 3 := (h 3 : P 3)

example (h : ∀ x : ℕ, P x) : P 3 := by
  exact h 3

/-
Proof term of conjunction `A ∧ B` acts like
a tuple ⟨hA, hB⟩  of `hA : A` and `hB : B`
-/

-- use ⟨, ⟩ to make pair
example (ha : A) (hb : B) : A ∧ B := ⟨ha, hb⟩

-- use .left or .right to access each
example (h : A ∧ B) : A := h.left
example (h : A ∧ B) : B := h.right

-- Fun Exercises!!
theorem logic1 (hab : A → B) (habc : A ∧ B → C) : A → C :=
  λ ha : A ↦ (
    habc (⟨ha, hab ha⟩ : A ∧ B)
  )

-- `And` Constructor term
#check And.intro

example (hab : A → B) (habc : A ∧ B → C) : A → C := by
  intro ha
  apply habc
  -- `cases` or `rcases` works for assumptions (not goal)
  constructor -- breaks down A ∧ B
  exact ha
  apply hab
  exact ha

example (h : A ∧ (B ∧ C)) : A ∧ B ∧ C := by
  rcases h with ⟨ha, ⟨hb, hc⟩⟩
  -- does not work with cases
  exact ⟨ha, hb, hc⟩

/-
example (hab : A ∧ B) (hc : C) : A ∧ B ∧ C := by
  cases hab with
-/

theorem logic2 (h : A → B ∧ C) : (A → B) ∧ (A ∧ C) := sorry

/-
(Dependent version)
Proof term of existence `∃ a : A, P a` acts like
a tuple ⟨a, hPa⟩  of `a : A` and `hPa : P a`
-/

example (h : P 3) : ∃ x : ℕ, P x := ⟨3, h⟩

example (h : ∃ x : ℕ, P x ∧ Q x) :
    (∃ x : ℕ, P x) ∧ (∃ x : ℕ, Q x) := by
  constructor
  · rcases h with ⟨x, ⟨hPx, hQx⟩⟩
    -- one: exact ⟨x, hPx⟩
    -- two:
    exists x
  · rcases h with ⟨x, ⟨hPx, hQx⟩⟩
    use x

/-
Proof term of disjunction `A ∨ B` is a data containing
one of `hA : A` and `hB : B`
-/

variable (hA : A) (hB : B)
-- Use Or.inl / Or.inr to make disjunction
#check (Or.inl hA : A ∨ B)
#check (Or.inr hB : A ∨ B)

-- Use Or.elim / .elim to use disjunction
#check Or.elim
example (h : A ∨ B) (hA : A → C) (hB : B → C) : C :=
  h.elim hA hB

-- Fun Exercises!!
example (h : (A ∧ B) ∨ C) : (A ∨ C) ∧ (B ∨ C) := sorry
