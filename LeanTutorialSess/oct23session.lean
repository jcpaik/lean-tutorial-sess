import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-
# Part 1. Terms and Types.

**Every object in _Lean_ is a _term_ with a _type_.**

Type/uncomment each line in and see what happens.
You may play with new '#check's to see how it works.
-/

/-
Numbers are terms with their type (ℕ, ℤ, ℝ).

We write (term : type) syntax to denote its type.
Type '\N ' (backslash, letter 'N', then space) to type ℕ.
-/

-- 2 ∈ ℕ
#check (2 : ℕ)
-- Computer science, Peano arithmetic
#check (0 : ℕ)
#check (-3 : ℤ)
-- #check (-3 : ℕ)
#check (2 + 2)
#check (2 + 2 : ℝ)

-- prepare this
-- int × int -> int
-- α x α -> α
#check (30 / 7)
#eval 30 / 7

/-
_Tuples_ of terms (e.g. numbers) are terms too.

If (a : A) and (b : B), then ((a, b) : A × B).
Have a guess before clicking #check!
-/
#check (2, 3)
#check ((2 : ℕ), (-3 : ℝ))
#check ((2, 3), (4, 5))

/-
_Propositions_ are terms too!

As terms, they have type `Prop`.
-/
#check 2 + 2 = 4
#check 2 + 2 = 5
-- \forall → ∀
-- \exists -> ∃
#check ∀ n : ℕ, ∃ m > n, Prime m

/-
Important:
1. `2 + 2 = 4`, as a _term_, has type `Prop`.
2. `2 + 2 = 4`, as a _type_, has the **proof** of `2 + 2 = 4` as terms.

term : type
(proof of 2+2=4) : 2+2=4
2+2=4 : Prop

type with no term
(proof???) : 2+2=5
2+2=5 : Prop
-/

-- := is for definition
def val := 3

-- 2+2=4의 증명 two_two_four를 정의하겠다
theorem two_two_four : 2 + 2 = 4 := rfl

#check two_two_four

def integer : ℤ := ↑(3 : ℕ)
-- def natural : ℕ := ↑(3 : ℤ)
-- def natural : ℕ := (-3 : ℤ)
-- there is a 'coercion' map ℕ -> ℤ
#check (↑(3 : ℕ) : ℤ)

/-
_Functions_ are terms too, with their _function type_ A → B.

Syntax: fun (input : type) ↦ output
Have a guess before clicking #check!
-/

#check fun (x : ℝ) ↦ x + 2 -- Write \map or \mapsto for arrow
-- #check fun (x : ℕ) ↦ (x, -x)

/-
# Part 2 : Definitions and Theorems
-/
def a := 3

def f := fun (x : ℝ) ↦ x + 2

def g := fun (a : ℕ) ↦ (fun (b : ℕ) ↦ a + b)
-- `syntatic sugar`
def g_easy (a : ℕ) (b : ℕ) : ℕ := a + b
#check g_easy 3
def g_easy' (a b : ℕ) : ℕ := a + b
#check g_easy' 3

-- g : ℕ -> (ℕ -> ℕ)
-- h : ℕ × ℕ -> ℕ
-- 결과값은 같지만, type이 달라 다른 함수
def h (pair : ℕ × ℕ) := pair.fst + pair.snd
#check g
#check h

-- rfl: 'by definition' equality
theorem g_eq_h (a : ℕ) (b : ℕ) : g a b = h (a, b) := rfl 

def lots (a : ℕ) (b : ℕ) (c : ℕ) : ℤ := sorry

#check (lots : ℕ -> ℕ -> ℕ -> ℤ)
#check (lots : ℕ -> (ℕ -> (ℕ -> ℤ)))

#eval (1, 2, 3, 4).snd

#check (g : ℕ -> (ℕ -> ℕ))
#check (g 3 : ℕ -> ℕ) -- a := 3
-- (fun (b : ℕ) ↦ 3 + b)
#check (g 3 4 : ℕ)
#eval g 3 4

/-
We usually write f(3)
In lean, we write `f 3` (`function argument`)
So `g 3 4` means (g(3))(4)
-/
#check f 3
-- #check f 3 4

def f' (x : ℝ) := x + 2

theorem something : (3 = 3) := by
  sorry

theorem coerce_back (n : ℤ) (hn : n ≥ 0) : ∃! m : ℕ, n = ↑m :=
  sorry

def add9 (n : ℕ) := n + 9
def add9' : ℕ → ℕ
  | 0 => 9
  | n+1 => add9' n + 9