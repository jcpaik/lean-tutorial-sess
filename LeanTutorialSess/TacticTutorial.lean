import Mathlib.Tactic

variable (A B C D : Prop)

-- type `\r` to enter `→`
theorem id_a (ha : A) : A := by
  exact ha

theorem id_a' : A → A := by
  intro ha
  exact ha

-- type `\r` to enter `→`
theorem modus_ponens' : (A → B) → A → B := by
  intro hAB hA
  apply hAB
  exact hA

-- type `\and` to enter `∧`
theorem split_and_goal (hA : A) (hB : B) : A ∧ B := by
  constructor
  exact hA
  exact hB

-- type `\<` to enter `⟨`, type `\>` to enter `⟩`
theorem split_and_assumption (h : A ∧ B) : B ∧ A := by
  rcases h with ⟨ha, hb⟩
  constructor
  exact hb
  exact ha

theorem split_and_assumption' (h : A ∧ B) : B ∧ A := by
  obtain ⟨ha, hb⟩ := h
  constructor
  exact hb
  exact ha

theorem syllogism (hAB : A → B) (hBC : B → C) (hA : A) : C := by
  have hB : B := hAB hA
  have hC : C := hBC hB
  exact hC

-- type `\not` to enter `¬`
theorem contrapositive (h : A → B) : ¬B → ¬A := by
  intro hnB
  -- ¬A is equivalent to A → False
  intro hA
  apply hnB
  apply h
  exact hA

-- type `\or` to enter `∨`
theorem left_or_right (h : A ∨ B) : B ∨ A := by
  -- split or in assumption
  rcases h with hA | hB
  right
  exact hA
  left
  exact hB

-- by cases on A or ¬A
theorem em_example : A ∨ ¬A := by
  by_cases hA : A
  left
  exact hA
  right
  exact hA

theorem false_elim (h : False) : A := by
  exfalso
  exact h

variable (P : ℕ → Prop)

-- type `\ex` to enter `∃`
theorem exists_elim (h : ∃ x : ℕ, P x ∧ A) : A := by
  rcases h with ⟨x, hx, ha⟩
  exact ha

theorem exists_elim' (h : ∃ x : ℕ, P x ∧ A) : A := by
  obtain ⟨x, hx, ha⟩ := h
  exact ha

-- type `\all` to enter `∀`
theorem forall_example : ∀ n : ℕ, P n → P n := by
  intro n hPn
  exact hPn

-- `∀ x, P x` is a _function_ that sends `x` to a proof of `P x`
theorem apply_example (h : ∀ n, P n) : P 3 := by
  exact h 3

theorem apply_example' (h : ∀ n, P n) : P 3 := by
  apply h

-- type `\ex` to enter `∃`
-- `∃ x, P x` is a _pair_ of `x` and the proof of `P x`
theorem exists_P3 (hP3 : P 3) : ∃ n, P n := by
  exact ⟨3, hP3⟩

theorem exists_P3' (hP3 : P 3) : ∃ n, P n := by
  exists 3

theorem exists_P3'' (hP3 : P 3) : ∃ n, P n := by
  exists 3

-- type `\ex` to enter `∃`, type `\and` to enter `∧`
theorem rcases_example (h : ∃ n, P n ∧ n > 0) : ∃ m, P m := by
  rcases h with ⟨n, hPn, hn_gt_0⟩
  use n

-- type `\ex` to enter `∃`
theorem obtain_example (h : ∃ n, P n) (nhP5 : ¬ P 5) : ∃ k, P k ∧ k ≠ 5 := by
  obtain ⟨n, hPn⟩ := h
  by_cases hn5 : n = 5
  -- type `exfalso` to enter `exfalso`
  exfalso
  rw [hn5] at hPn
  exact nhP5 hPn
  -- n ≠ 5
  use n

-- type `\eq` to enter `=`
theorem refl_example (n : ℕ) : n = n := by
  rfl

theorem rw_example (a : ℕ) (eq : a = 5) (hP5 : P 5) : P a := by
  rw [eq]
  exact hP5

theorem rw_example' (a : ℕ) (eq : a = 5) (hPa : P a) : P 5 := by
  rw [← eq]
  exact hPa

theorem eq_trans_example (a b c : ℕ) (hab : a = b) (hbc : b = c) : a = c := by
  rw [hab]
  exact hbc
