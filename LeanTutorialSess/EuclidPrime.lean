import Mathlib.Tactic.Ring.RingNF

-- helper lemma to use
lemma nonzero_is_succ {n : ℕ} (hn : n ≠ 0) : ∃ n', n = n' + 1 := by
  cases' n with n0 n'
  · contradiction
  · use n0

def divides (a b : ℕ) : Prop := ∃ c : ℕ, b = a * c

lemma divides_2_6 : divides 2 6 := by
  rw [divides]
  use 3

lemma not_divides_2_5 : ¬ divides 2 5 := by
  rw [divides]
  push_neg
  intro c
  omega

lemma zero_divides_iff {n : ℕ} : divides 0 n ↔ n = 0 := by
  constructor
  · intro hn
    obtain ⟨m, hm⟩ := hn
    ring_nf at hm
    exact hm
  · intro hn
    rw [hn]
    use 0

lemma one_divides {n : ℕ} : divides 1 n := by
  use n
  omega

lemma le_of_divides {n m : ℕ} (hm : m ≠ 0) : divides n m → n ≤ m := by
  intro hdiv
  obtain ⟨c, heq⟩ := hdiv
  by_cases hc : c = 0
  · rw [hc] at heq
    ring_nf at heq
    contradiction
  · obtain ⟨c', hc'⟩ := nonzero_is_succ hc
    rw [heq, hc']
    ring_nf
    omega

lemma divides_antisymm {n m : ℕ} (dnm : divides n m) (dmn : divides m n) : m = n := by
  by_cases hn : n = 0
  · rw [hn] at dnm
    rw [zero_divides_iff] at dnm
    rw [hn, dnm]
  · by_cases hm : m = 0
    · rw [hm] at dmn
      rw [zero_divides_iff] at dmn
      omega
    · have n_le_m : n ≤ m := by
        apply le_of_divides
        exact hm
        exact dnm
      have m_le_n : m ≤ n := by
        apply le_of_divides
        exact hn
        exact dmn
      omega

lemma divides_one_iff {n : ℕ} : divides n 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · rw [hn] at h
      rw [zero_divides_iff] at h
      omega
    · have h' : divides 1 n := one_divides
      apply divides_antisymm
      exact h'
      exact h
  · intro h
    rw [h]
    rw [divides]
    use 1

lemma divides_trans {j k l : ℕ} (hjk : divides j k) (hkl : divides k l) : divides j l := by
  obtain ⟨c, eq_jk⟩ := hjk
  obtain ⟨d, eq_kl⟩ := hkl
  use c * d
  rw [eq_kl, eq_jk]
  ring_nf

def is_prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ n : ℕ, divides n p → n = 1 ∨ n = p

theorem exists_prime_factor {n : ℕ} (hn : 2 ≤ n) : ∃ p, is_prime p ∧ divides p n := by
  induction' n using Nat.strongRecOn with n ih
  · by_cases hprime : is_prime n
    · exact ⟨n, hprime, ⟨1, by ring_nf⟩⟩
    · rw [is_prime] at hprime
      push_neg at hprime
      obtain ⟨d, hd_dvd_n, hd⟩ := hprime hn
      -- So d divides n, d ≠ 1, and d ≠ n
      have hd_ne_zero : d ≠ 0 := by
        by_contra hd0
        rw [hd0] at hd_dvd_n
        rw [zero_divides_iff] at hd_dvd_n
        omega
      have hd_gt_one : d > 1 := by omega
      have hd_lt_n : d < n := by
        have n_ne_zero : n ≠ 0 := by omega
        have d_le_n := le_of_divides n_ne_zero hd_dvd_n
        omega
      -- Since d < n and d ≥ 2, we can apply the induction hypothesis to d
      have hd_ge_two : d ≥ 2 := by omega
      have ih_p := ih d hd_lt_n hd_ge_two
      obtain ⟨p, hp, hpd⟩ := ih_p
      refine ⟨p, hp, ?_⟩
      exact divides_trans hpd hd_dvd_n

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

lemma le_divides_factorial {n m : ℕ} (hm : m ≠ 0) (hle : m ≤ n) : divides m (factorial n) := by
  induction' n with n ih
  · exfalso
    omega
  · by_cases hm : m = n + 1
    · rw [hm]
      rw [divides]
      use factorial n
      rw [factorial]
      exact Nat.mul_comm _ _
    · have m_le_n : m ≤ n := by
        omega
      apply ih at m_le_n
      apply divides_trans m_le_n
      exact factorial_divides_factorial_succ

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
    ring_nf at eq_c ⊢
    omega
  rw [divides_one_iff] at hn1
  omega

theorem infinitude_of_primes (N : ℕ) : ∃ p, N < p ∧ is_prime p := by
  set M := factorial N + 1 with def_M
  have hM : 2 ≤ M := by
    have h' : 1 ≤ factorial N := by
      exact one_le_factorial
    omega
  obtain ⟨p, hp, p_dvd_M⟩ := exists_prime_factor hM
  refine ⟨p, ?_, hp⟩
  by_contra hN'
  have hN : p ≤ N := by omega
  have hp2 : 2 ≤ p := hp.1
  have hp0 : p ≠ 0 := by omega
  have no_p_dvd_M : ¬ divides p M := by
    apply not_divides_of_divides_succ
    · exact hp.1
    · exact le_divides_factorial hp0 hN
  contradiction
