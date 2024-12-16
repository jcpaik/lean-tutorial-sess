import Mathlib.Tactic.Ring.RingNF

-- helper lemma to use
lemma nonzero_is_succ {n : ℕ} (hn : n ≠ 0) : ∃ n', n = n' + 1 := by
  cases' n with n0 n'
  · contradiction
  · use n0

def divides (a b : ℕ) : Prop := ∃ c : ℕ, b = a * c

lemma divides_2_6 : divides 2 6 := by
  sorry

-- `omega` derives contradiction from any assumptions and goals
-- of linear equalities and inequalities on natural numbers
lemma not_divides_2_5 : ¬ divides 2 5 := by
  sorry

lemma divides_and : divides 2 4 ∧ divides 2 8 := by
  -- Exercise
  sorry

lemma zero_divides_iff {n : ℕ} : divides 0 n ↔ n = 0 := by
  sorry

lemma one_divides {n : ℕ} : divides 1 n := by
  sorry

-- Showcase
lemma le_of_divides {n m : ℕ} (hm : m ≠ 0) : divides n m → n ≤ m := by
  sorry

lemma divides_antisymm {n m : ℕ} (dnm : divides n m) (dmn : divides m n) : m = n := by
  by_cases hn : n = 0
  · -- Exercise
    -- `rw [⟨equation⟩] at ⟨target⟩`
    sorry
  · by_cases hm : m = 0
    · -- Exercise
      -- use `rw` only
      sorry
    · have n_le_m : n ≤ m := by
        -- `apply` and `exact`
        apply le_of_divides hm
        exact dnm
      have m_le_n : m ≤ n := by
        -- Exercise
        -- `apply` and `exact`
        sorry
      omega

lemma divides_one_iff {n : ℕ} : divides n 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exfalso
      -- Exercise
      -- `rw`, `obtain`, and `simp`
      sorry
    · sorry
  · intro hn
    rw [hn]
    use 1

lemma divides_trans {j k l : ℕ} (hjk : divides j k) (hkl : divides k l) : divides j l := by
  obtain ⟨c, eq_k⟩ := hjk
  -- Exercise
  -- use `ring_nf` to show a * b * c = a * (b * c)
  sorry

def is_prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ n : ℕ, divides n p → n = 1 ∨ n = p

theorem exists_prime_factor {n : ℕ} (hn : 2 ≤ n) : ∃ p, is_prime p ∧ divides p n := by
  -- strong induction!
  induction' n using Nat.strongRecOn with n ih
  · by_cases hprime : is_prime n -- case analysis on whether n is prime or not
    · -- n is prime
      -- Exercise
      sorry
    · -- n is not prime
      rw [is_prime] at hprime
      push_neg at hprime
      obtain ⟨d, hd_dvd_n, hd⟩ := hprime hn
      -- So d divides n, d ≠ 1, and d ≠ n
      have hd_ne_zero : d ≠ 0 := by
        by_contra hd0
        rw [hd0] at hd_dvd_n
        rw [zero_divides_iff] at hd_dvd_n
        omega
      have hd_gt_one : d > 1 := by
        omega
      have hd_lt_n : d < n := by
        have n_ne_zero : n ≠ 0 := by omega
        have d_le_n := le_of_divides n_ne_zero hd_dvd_n
        omega
      -- Since d < n and d ≥ 2, we can apply the induction hypothesis to d
      have hd_ge_two : d ≥ 2 := by
        omega
      have ih_p : ∃ p, is_prime p ∧ divides p d := by
        apply ih
        · exact hd_lt_n
        · omega
      -- Showcase
      obtain ⟨p, hp, dp⟩ := ih_p
      -- Exercise
      sorry

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

lemma one_le_factorial {n : ℕ} : 1 ≤ factorial n := by
  induction' n with n ih
  · rfl
  · rw [factorial]
    by_contra x
    simp at x
    omega

lemma factorial_divides_factorial_succ {n : ℕ} : divides (factorial n) (factorial (n + 1)) := by
  use (n + 1)
  rfl

-- Showcase
lemma le_divides_factorial {n m : ℕ} (hm : m ≠ 0) (hle : m ≤ n) : divides m (factorial n) := by
  induction' n with n ih
  · exfalso
    omega
  · by_cases hm : m = n + 1
    · -- Exercise
      sorry
    · -- Exercise
      sorry

lemma le_is_add_eq (h : m ≤ n) : ∃ k : Nat, n = m + k :=
  Nat.exists_eq_add_of_le h

lemma not_divides_of_divides_succ {n m : ℕ} (hn : 2 ≤ n) (h : divides n m) : ¬ divides n (m + 1) := by
  by_contra hnm
  have hn0 : n ≠ 0 := by
    omega
  have hn1 : divides n 1 := by
    obtain ⟨c, eq_c⟩ := hnm
    obtain ⟨d, eq_d⟩ := h
    rw [eq_d] at eq_c
    have ineq_n : n * d ≤ n * c := by
      omega
    have ineq_cd : d ≤ c := by
      exact Nat.le_of_mul_le_mul_left ineq_n (Nat.zero_lt_of_ne_zero hn0)
    obtain ⟨e, eq_e⟩ := Nat.exists_eq_add_of_le ineq_cd
    use e
    rw [eq_e] at eq_c
    ring_nf at eq_c
    omega
  -- Exercise
  sorry

theorem infinitude_of_primes (N : ℕ) : ∃ p, N < p ∧ is_prime p := by
  set M := factorial N + 1 with def_M
  have hM : 2 ≤ M := by
    have h' : 1 ≤ factorial N := by
      exact one_le_factorial
    omega
  have factor_M := exists_prime_factor hM
  -- Exercise
  -- Hint 1: use `obtain` to break down `factor_M`
  -- Hint 2: use `contradiction` to finish proof from `p` and `¬ p` in assumption
  sorry
