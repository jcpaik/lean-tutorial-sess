import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-
# Part 1. Terms and Types.

Lean is based on _type theory_.
Each object in Lean is a term with a unique type attached to it.
-/

-- Numbers
-- Use `\N` to type ℕ, use `\Z` to type ℤ.
#check (2 : ℕ)
-- Computer science, Peano arithmetic
#check (0 : ℕ)
#check (-3 : ℤ)
-- #check (-3 : ℕ)
#check (2 + 2)
#eval 2 + 2
#check (2 + 2 : ℝ)
#check 2 ^ 100
#eval 2 ^ 100
#eval 3 / 0

-- Tuples
#check (2, 3)
#check ((2 : ℕ), (-3 : ℝ))
#check ((2, 3), (4, 5))

-- Functions
-- Type `\r` to write `→`
#check (Nat.succ : ℕ → ℕ) -- Function that adds one
#eval Nat.succ 3
#check Nat.succ 3
#check Nat.add -- Not of type (ℕ × ℕ) → ℕ
#check Nat.add 2
#eval Nat.add 2 3
-- In Lean, a multi-variable function is written as `f a b c`
-- which is `((f a) b) c`.
-- Here, `f` would have type `f : A → B → C → D`.

-- Types are terms with higher-level types
#check (3 : ℕ)
#check (ℕ : Type 0)
#check (Type 0 : Type 1)
#check (Type 1 : Type 2)
-- ...

-- Propositions
-- ... have type `Prop`
#check 2 + 2 = 4
#check 2 + 2 = 5
-- `\and` → `∧`, `\or` → `∨`, `\not` → `¬`, `\r` → `→`.
#check 1 = 1 ∧ 2 = 2
#check 2 + 2 = 4 ∨ 2 + 2 = 5
#check ¬ (2 + 2 = 5)
-- `\forall` → `∀`, `\exists` → `∃`
#check ∀ x : ℕ, x = 2 → x + 2 = 4
#check ∃ y : ℕ, y + 2 = 4
-- `\iff` → `↔`
#check ∀ x : ℕ, x + 2 = 4 ↔ x = 2
-- `\geq` → `≥`
#check ∀ n ≥ 3, ∀ (a b c : ℕ), a^n + b^n = c^n → a = 0 ∧ b = 0 ∧ c = 0

-- Proofs

-- Declare using `theorem ⟨name⟩ : ⟨statement⟩ := by`
-- use _tactics_ to prove the theorem
theorem two_two_four : 2 + 2 = 4 := by
  rfl -- checks definitional equality

-- `two_two_four` is a _proof term_
#check two_two_four -- with type `2 + 2 = 4`

-- Exercise: state and show `2 + 2 = 4 ∨ 2 + 2 = 5`.
theorem two_two_four_or_five : 2 + 2 = 4 ∨ 2 + 2 = 5 := by
  left -- choose left as goal
  rfl

-- The type of `two_two_four_or_five` is:
#check two_two_four_or_five

-- Exercise: state and show `2 + 2 = 4 ∨ 2 + 2 = 5`.
-- type `\.` to write `·` (middle dot)
theorem equals_and : 1 = 1 ∧ 2 = 2 := by
  constructor -- breaks down `∧` into two goals
  · rfl -- focus on first goal and prove by `rfl`
  · rfl

theorem plus_two_is_four : ∀ x : ℕ, x = 2 → x + 2 = 4 := by
  intro x -- assume arbitrary x
  intro hx -- assume hypothesis
  rw [hx] -- rewrite `hx` equation to goal

-- same as above
-- `theorem ⟨name⟩ (term1 : type1) (term2 : type2) : ⟨statement⟩ := by`
theorem plus_two_is_four' (x : ℕ) (hx : x = 2) : x + 2 = 4 := by
  rw [hx]

theorem equals_two (x : ℕ) (hx : x + 2 = 4) : x = 2 := by
  -- `have ⟨name⟩ : ⟨statement⟩ := by`
  have hx' : (x + 2) - 2 = 2 := by
    rw [hx]
  simp at hx' -- or, `ring_nf` at hx'
  exact hx' -- exactly assumption X

theorem nat_add_comm (a b : ℕ) : a + b = b + a := by
  ring_nf -- computes normal form of ring

-- `∀ x : A, P x` acts like a _function_ from `x : A` to `h : P x`
#check nat_add_comm
#check nat_add_comm 2 3
#check plus_two_is_four
#check plus_two_is_four 2
#check plus_two_is_four 7

theorem plus_two_is_four_iff (x : ℕ) : x + 2 = 4 ↔ x = 2 := by
  constructor -- break down `↔` into two goals
  · exact equals_two x
  · exact plus_two_is_four x

theorem eq_five (x : ℕ) (hx : x + 2 = 4) : x + 3 = 5 := by
  apply equals_two x at hx
  rw [hx]

theorem two_two_not_five : ¬ 2 + 2 = 5 := by
  by_contra h
  simp at h
