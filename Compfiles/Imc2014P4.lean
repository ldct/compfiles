/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2014, Problem 4

Let `n > 6` be a perfect number, and let `n = p_1^{e_1} * ... * p_k^{e_k}` be its
prime factorization with `1 < p_1 < ... < p_k`. Prove that `e_1` is an even
number.

We formalize the conclusion as: the exponent of the smallest prime factor of
`n` (i.e., `n.factorization n.minFac`) is even.

The proof strategy: Suppose `e_1 = n.factorization p_1` is odd, where `p_1` is
the smallest prime factor. Then `(p_1 + 1) ∣ (1 + p_1 + ⋯ + p_1^{e_1})`, and the
latter divides `σ(n) = 2n`. We split on whether `p_1 = 2`:

* If `p_1 ≥ 3`, then `n` is odd, so `(p_1 + 1) / 2 ∣ n`. But
  `(p_1 + 1) / 2 < p_1` and `(p_1 + 1) / 2 ≥ 2`, contradicting minimality of
  `p_1`.
* If `p_1 = 2`, then `3 ∣ 2n`, so `3 ∣ n`, hence `6 ∣ n`. Together with `n > 6`,
  the five distinct divisors `1, n/6, n/3, n/2, n` have sum `2n + 1 > 2n`,
  contradicting `σ(n) = 2n`.
-/

namespace Imc2014P4

open Nat Finset

/-- The geometric sum `1 + p + p^2 + … + p^e` is divisible by `p + 1` when
`e` is odd. -/
private lemma succ_dvd_geom_sum_of_odd (p e : ℕ) (he : Odd e) :
    p + 1 ∣ ∑ i ∈ range (e + 1), p ^ i := by
  -- The sum equals `(p+1) * (1 + p^2 + p^4 + … + p^{e-1})` when `e` is odd.
  obtain ⟨k, rfl⟩ := he
  -- Pair up consecutive terms: ∑_{j<k+1} (p^(2j) + p^(2j+1)) = (p+1) * ∑ p^(2j).
  have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  rw [h1]
  -- Use that range (2 * (k+1)) splits as image of {0, 1} × range (k+1).
  have key : ∀ N : ℕ,
      ∑ i ∈ range (2 * N), p ^ i = (p + 1) * ∑ j ∈ range N, p ^ (2 * j) := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 from by ring]
      rw [Finset.sum_range_succ, Finset.sum_range_succ _ (2 * M)]
      rw [Finset.sum_range_succ _ M, ih]
      have hpow : p ^ (2 * M + 1) = p * p ^ (2 * M) := by rw [pow_succ]; ring
      rw [hpow]
      ring
  rw [key (k + 1)]
  exact ⟨_, rfl⟩

/-- The `p`-factor `∑ i ∈ range (n.factorization p + 1), p^i` divides
`∑ d ∈ n.divisors, d`, when `p` is a prime factor of `n`. -/
private lemma geom_sum_dvd_sum_divisors {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hpn : p ∣ n) :
    ∑ i ∈ range (n.factorization p + 1), p ^ i ∣ ∑ d ∈ n.divisors, d := by
  rw [Nat.sum_divisors hn]
  refine Finset.dvd_prod_of_mem _ ?_
  rw [Nat.mem_primeFactors]
  exact ⟨hp, hpn, hn⟩

/-- For a perfect number `n > 6`, the exponent of the smallest prime factor in
`n` is even. -/
problem imc2014_p4 (n : ℕ) (h6 : 6 < n) (hperf : n.Perfect) :
    Even (n.factorization n.minFac) := by
  have hn_pos : 0 < n := hperf.2
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hn1 : 1 < n := by omega
  set p := n.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hn1.ne'
  have hp2 : 2 ≤ p := hp.two_le
  have hpn : p ∣ n := Nat.minFac_dvd n
  set e := n.factorization p with he_def
  have he_pos : 0 < e := hp.factorization_pos_of_dvd hn_ne hpn
  -- We argue by contradiction: assume e is odd.
  by_contra hodd_ne
  rw [Nat.not_even_iff_odd] at hodd_ne
  -- σ(n) = 2n
  have hsigma : ∑ d ∈ n.divisors, d = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hn_pos).mp hperf
  -- (p+1) | (1 + p + ... + p^e)
  have h1 : p + 1 ∣ ∑ i ∈ range (e + 1), p ^ i :=
    succ_dvd_geom_sum_of_odd p e hodd_ne
  -- (1 + p + ... + p^e) | σ(n) = 2n
  have h2 : ∑ i ∈ range (e + 1), p ^ i ∣ 2 * n := by
    rw [← hsigma]
    exact geom_sum_dvd_sum_divisors hn_ne hp hpn
  have hp1_dvd : p + 1 ∣ 2 * n := h1.trans h2
  -- Case split on whether p = 2.
  rcases eq_or_ne p 2 with hp_eq | hp_ne
  · -- p = 2: 3 ∣ 2n so 3 ∣ n; then 6 ∣ n, contradiction with n > 6.
    have h3_dvd_2n : (3 : ℕ) ∣ 2 * n := by rw [hp_eq] at hp1_dvd; exact hp1_dvd
    have h3p : Nat.Prime 3 := by decide
    have h3_dvd_n : (3 : ℕ) ∣ n := by
      rcases (h3p.dvd_mul.mp h3_dvd_2n) with h | h
      · exact absurd h (by decide)
      · exact h
    have h2_dvd_n : (2 : ℕ) ∣ n := by rw [hp_eq] at hpn; exact hpn
    have h6_dvd_n : (6 : ℕ) ∣ n := by
      rw [show (6 : ℕ) = 2 * 3 from rfl]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2_dvd_n h3_dvd_n
    -- Now divisors 1, n/6, n/3, n/2, n are distinct and sum to 2n + 1.
    have h6_dvd_n_copy := h6_dvd_n
    obtain ⟨k, hk⟩ := h6_dvd_n_copy
    have hk_pos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, Nat.mul_zero] at hk; omega
      · exact h
    -- k ≥ 2 since n > 6 = 6 * 1.
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k
        all_goals (rw [hk] at h6; omega)
      · exact hge
    -- n/6 = k, n/3 = 2k, n/2 = 3k, n = 6k
    have h_n6 : n / 6 = k := by
      rw [hk]; exact Nat.mul_div_cancel_left k (by norm_num)
    have h_n3 : n / 3 = 2 * k := by
      have : n = 3 * (2 * k) := by rw [hk]; ring
      rw [this]; exact Nat.mul_div_cancel_left (2*k) (by norm_num)
    have h_n2 : n / 2 = 3 * k := by
      have : n = 2 * (3 * k) := by rw [hk]; ring
      rw [this]; exact Nat.mul_div_cancel_left (3*k) (by norm_num)
    -- These five values are all divisors.
    have hd1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn_ne
    have hdn : n ∈ n.divisors := Nat.mem_divisors_self n hn_ne
    have hd6 : n / 6 ∈ n.divisors := Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd h6_dvd_n, hn_ne⟩
    have hd3 : n / 3 ∈ n.divisors := Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd h3_dvd_n, hn_ne⟩
    have hd2 : n / 2 ∈ n.divisors := Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd h2_dvd_n, hn_ne⟩
    -- Distinctness of {1, k, 2k, 3k, 6k}
    have h1nek : 1 ≠ k := by omega
    have h1ne2k : 1 ≠ 2 * k := by omega
    have h1ne3k : 1 ≠ 3 * k := by omega
    have h1ne6k : 1 ≠ 6 * k := by omega
    have hkne2k : k ≠ 2 * k := by omega
    have hkne3k : k ≠ 3 * k := by omega
    have hkne6k : k ≠ 6 * k := by omega
    have h2kne3k : 2 * k ≠ 3 * k := by omega
    have h2kne6k : 2 * k ≠ 6 * k := by omega
    have h3kne6k : 3 * k ≠ 6 * k := by omega
    -- Build the finset
    let S : Finset ℕ := {1, k, 2*k, 3*k, 6*k}
    have hS_sub : S ⊆ n.divisors := by
      intro x hx
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hd1
      · rw [← h_n6]; exact hd6
      · rw [← h_n3]; exact hd3
      · rw [← h_n2]; exact hd2
      · rw [show 6 * k = n from by rw [hk]]; exact hdn
    have hsum_S_le : ∑ x ∈ S, x ≤ ∑ d ∈ n.divisors, d :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ => Nat.zero_le _)
    -- Compute ∑ x ∈ S, x = 1 + k + 2k + 3k + 6k = 1 + 12k = 1 + 2n.
    have hsum_S : ∑ x ∈ S, x = 1 + 12 * k := by
      simp only [S]
      rw [Finset.sum_insert (by simp [h1nek, h1ne2k, h1ne3k, h1ne6k])]
      rw [Finset.sum_insert (by simp [hkne2k, hkne3k, hkne6k])]
      rw [Finset.sum_insert (by simp [h2kne3k, h2kne6k])]
      rw [Finset.sum_insert (by simp [h3kne6k])]
      rw [Finset.sum_singleton]
      ring
    have h12k : 12 * k = 2 * n := by rw [hk]; ring
    rw [h12k] at hsum_S
    rw [hsigma] at hsum_S_le
    rw [hsum_S] at hsum_S_le
    omega
  · -- p ≥ 3 (odd prime): n is odd, so (p+1)/2 ∣ n; but (p+1)/2 < p, contradicting minimality.
    have hp3 : 3 ≤ p := by
      have hp_odd : Odd p := hp.odd_of_ne_two hp_ne
      omega
    -- (p+1) | 2n, p+1 even, so (p+1)/2 | n.
    have hp1_even : Even (p + 1) := by
      have : Odd p := hp.odd_of_ne_two hp_ne
      rcases this with ⟨t, ht⟩
      exact ⟨t + 1, by omega⟩
    obtain ⟨q, hq⟩ := hp1_even
    have hq_eq : p + 1 = 2 * q := by linarith
    have hq_dvd : q ∣ n := by
      -- 2q | 2n, so q | n.
      have : 2 * q ∣ 2 * n := by rw [← hq_eq]; exact hp1_dvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 2)).mp this
    -- q ≥ 2 and q < p.
    have hq_ge : 2 ≤ q := by omega
    have hq_lt : q < p := by omega
    -- minFac n ≤ q, but minFac n = p > q. Contradiction.
    have : p ≤ q := by
      rw [hp_def]
      exact Nat.minFac_le_of_dvd hq_ge hq_dvd
    omega

end Imc2014P4
