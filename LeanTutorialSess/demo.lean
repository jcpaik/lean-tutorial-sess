import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Zsqrtd.GaussianInt


#check Nat
#check ℕ
#check Int
#check Real
#check ℝ
#check ℕ → ℕ
#check ℕ × ℕ
#check List ℕ

#check 2 + 2
#check (2 + 2 : ℝ)
#check (2, 3, 4)
#check fun x : ℝ => x + 2
#check fun x : ℝ ↦ x + 2

#check 2 + 2 = 4
#check 2 + 2 = 5
#check ∀ n : ℕ, ∃ m > n, Prime m

#check (rfl : 2 + 2 = 4)

def foo := 2

theorem bar : foo = 2 := rfl

#check bar

#check Type

def baz (x : ℕ) := x + 3

theorem baz_baz (x : ℕ) : baz (baz x) = x + 6 := by
  simp [baz]

#eval 2 ^ 287

noncomputable section

#check Float

def foo' := (2 : ℝ) / 5

def f : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*n + 1 + f n

#eval f 0
#eval f 1
#eval f 2

#eval List.range 20 |>.map f

theorem f_eq : ∀ n, f n = n^2 := by
  intro n
  induction' n with n ih
  · rfl
  rw [f, ih]
  ring

#check f_eq

#print f_eq


/-
Groups where every element has order 2.
-/

section

variable {G : Type*} [Group G]

#check @inv_mul_cancel
#check @mul_one
#check @one_mul
#check @mul_assoc

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z = y * (y * z) * (y * z) * z
  · rw [mul_assoc y, h, mul_one]
  have h2 : z * y = y * (y * z) * (y * z) * z
  · rw [mul_assoc, mul_assoc y z, h, mul_one, ←mul_assoc, h, one_mul]
  rw [h1, h2]

#check @mul_left_cancel

example (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  have h1 : y * z * (y * z) = y * z * (z * y)
  · sorry
  sorry

end

/-
Integer ModEq
-/

#check Int.ModEq
#check Int.ModEq.refl
#check Int.ModEq.symm
#check Int.ModEq.trans
#check Int.ModEq.add
#check Int.ModEq.add_left

section

variable (a1 a2 b1 b2 c1 c2 n : ℤ)
variable (m : ℕ)

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] := by
-- show_term {
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply ha
  apply hb
  apply hc
-- }

#check ZMod m

example (ha : a1 ≡ a2 [ZMOD m])
    (hb : b1 ≡ b2 [ZMOD m])
    (hc : c1 ≡ c2 [ZMOD m]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD m] := by
    simp [← ZMod.intCast_eq_intCast_iff] at *
    rw [ha, hb, hc]

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] := by
    refine Int.ModEq.add ?h₁ hc
    exact Int.ModEq.mul ha hb

example (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    abs a1 ≡ abs a2 [ZMOD n] := by
    sorry

example (ha : a1 ≡ a2 [ZMOD m]) (k : ℕ) :
    a1^k ≡ a2^k[ZMOD m] := by
  induction' k with k ih
  . rfl
  rw [pow_succ, pow_succ]
  have := Int.ModEq.mul ih ha
  -- exact Int.ModEq.mul ih ha
  apply Int.ModEq.mul
  apply ih
  apply ha

theorem foo'' (ha : a1 ≡ a2 [ZMOD n])
    (hb : b1 ≡ b2 [ZMOD n])
    (hc : c1 ≡ c2 [ZMOD n]) :
    a1 * b1 + c1 ≡ a2 * b2 + c2 [ZMOD n] := by
  apply Int.ModEq.add
  . apply Int.ModEq.mul
    exact ha
    exact hb
  . exact hc

end

def FnUb (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

#check FnUb

section

variable {f g : ℝ → ℝ} {a b : ℝ}

theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (f + g) (a + b) := by
  -- rw [FnUb]
  intro y
  dsimp
  -- apply?
  -- apply add_le_add (hfa y) (hgb y)
  show_term {
  apply add_le_add
  apply hfa
  apply hgb }

end

/-
The existential quantifier
-/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5/2
  norm_num

section

def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) :
    FnHasUb (f + g) := by
  rcases ubf with ⟨u, hu⟩
  rcases ubg with ⟨v, hv⟩
  use u + v
  apply fnUb_add hu hv

/-
Disjunction
-/

section

variable (x y : ℝ)

#check le_or_gt 0 y
#check abs_of_nonneg
#check abs_of_neg

example : x < abs y → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  . rw [abs_of_nonneg h]
    intro h1
    left
    exact h1
  . rw [abs_of_neg h]
    intro h1
    right
    exact h1

end

/-
More stuff.
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  sorry

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (s + t) (a + b) := by
  sorry

/-
Structures.
-/

section

variable {R : Type*} [CommSemiring R]
variable (x y : R)

example : (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

#check mul_comm
#check mul_assoc

set_option pp.all true in
#check mul_comm x y

end

section

variable {V F : Type*} [Field F] [AddCommGroup V] [Module F V]

variable (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ)

variable (u v : Type*) [Fintype u] [Fintype v]

variable (M : Matrix u v ℝ)

end

/-
Number theory.
-/

#check Zsqrtd (-5)

#check Polynomial

open Polynomial

#check C 5
#check X

theorem irred_x_squared_plus_five : Irreducible (X^2 + 5 : Polynomial ℚ) := by
  sorry

instance : Fact (Irreducible (X^2 + 5 : Polynomial ℚ)) := ⟨irred_x_squared_plus_five⟩

#check NumberField
#check AdjoinRoot (X^2 + 5 : Polynomial ℚ)

#synth Field (AdjoinRoot (X^2 + 5 : Polynomial ℚ))
#synth IsDomain (AdjoinRoot (X^2 + 5 : Polynomial ℚ))

#check NumberField.classNumber (AdjoinRoot (X^2 + 5 : Polynomial ℚ))

#check NumberField.exists_ideal_in_class_of_norm_le

theorem classNumber_adjoinRoot_x_squared_plus_five_le :
    NumberField.classNumber (AdjoinRoot (X^2 + 5 : Polynomial ℚ)) ≤ 2 := by
  -- trans
  -- apply NumberField.hermiteTheorem.minkowskiBound_lt_boundOfDiscBdd
  sorry

--#check ClassGroup (Zsqrtd (-5))

end
