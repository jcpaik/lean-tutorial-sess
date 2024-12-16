import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-
Lean is based on _type theory_.
Each object in Lean is a term with a unique type attached to it.
-/

-- Numbers
-- Use `\N` to type ℕ, use `\Z` to type ℤ.

-- Tuples

-- Functions
-- Type `\r` to write `→`
-- In Lean, a multi-variable function is written as `f a b c`
-- which is `((f a) b) c`.
-- Here, `f` would have type `f : A → B → C → D`.

-- Types are terms with higher-level types

-- Propositions
-- ... have type `Prop`
-- `\and` → `∧`, `\or` → `∨`, `\not` → `¬`, `\r` → `→`.
-- `\forall` → `∀`, `\exists` → `∃`
-- `\iff` → `↔`
-- `\geq` → `≥`

-- Proofs
-- Declare using `theorem ⟨name⟩ : ⟨statement⟩ := by`
-- use _tactics_ to prove the theorem

-- The type of a theorem is its statement.

-- Exercise: state and show `2 + 2 = 4 ∨ 2 + 2 = 5`.

-- The type of a theorem is its statement.

-- type `\.` to write `·` (middle dot)

-- `theorem ⟨name⟩ (term1 : type1) (term2 : type2) : ⟨statement⟩ := by`

-- Exercise: State Fermat's Last Theorem

-- `∀ x : A, P x` acts like a _function_ from `x : A` to `h : P x`
