/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 3
(IMC 2002, Day 1, Problem 3)

Let `n ≥ 1`. Define `a_k = 1 / C(n, k)` and `b_k = 2^(k-n)` for `k = 1, …, n`.
Show that
  `∑_{k=1}^n (a_k - b_k) / k = 0`.

The proof proceeds by induction on `n`, using the identity
`k · C(n, k) = n · C(n-1, k-1)` to relate the `a_k` sum to a sum over
`C(n-1, j)^(-1)`, and the identity
`1 / C(n,k) + 1 / C(n, k+1) = (n+1) / (n · C(n-1, k))`
to obtain the recurrence `x_{n+1} = x_n + 2^{n+1}/(n+1)` for
`x_n = (2^n / n) · ∑_{j=0}^{n-1} 1 / C(n-1, j)`.
-/

namespace Imc2002P3

open Finset

snip begin

/-- `1/C(n,k) + 1/C(n,k+1) = (n+1) / (n · C(n-1, k))`, valid for `1 ≤ n` and `k ≤ n-1`. -/
lemma inv_choose_add_inv_choose_succ (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    (1 / (n.choose k : ℝ)) + (1 / (n.choose (k + 1) : ℝ)) =
      (n + 1 : ℝ) / (n * ((n - 1).choose k : ℝ)) := by
  -- We use C(n,k) = n/(n-k) · C(n-1,k) and C(n,k+1) = n/(k+1) · C(n-1,k).
  -- Equivalently: (n-k) · C(n,k) = n · C(n-1,k), (k+1) · C(n,k+1) = n · C(n-1,k).
  have hkn : k ≤ n := hk.trans (Nat.sub_le _ _)
  have hk1n : k + 1 ≤ n := by omega
  -- Key identities in ℕ:
  have hk_lt_n : k < n := by omega
  have hid1 : (n - k) * n.choose k = n * (n - 1).choose k := by
    -- From Nat.choose_mul_factorial_mul_factorial at (n, k) and (n-1, k):
    -- C(n,k)*k!*(n-k)! = n!; C(n-1,k)*k!*(n-1-k)! = (n-1)!
    have h1 : n.choose k * k.factorial * (n - k).factorial = n.factorial :=
      Nat.choose_mul_factorial_mul_factorial hkn
    have h2 : (n-1).choose k * k.factorial * (n - 1 - k).factorial = (n-1).factorial := by
      apply Nat.choose_mul_factorial_mul_factorial
      omega
    have hfact_n : n.factorial = n * (n-1).factorial := by
      conv_lhs => rw [show n = (n-1) + 1 from by omega]
      rw [Nat.factorial_succ]
      congr 1
      omega
    have hfact_nk : (n - k).factorial = (n - k) * (n - 1 - k).factorial := by
      conv_lhs => rw [show n - k = (n - 1 - k) + 1 from by omega]
      rw [Nat.factorial_succ]
      congr 1
      omega
    have h3 : (n - k) * (n.choose k * k.factorial * (n - 1 - k).factorial) =
              n * (n - 1).factorial := by
      calc (n - k) * (n.choose k * k.factorial * (n - 1 - k).factorial)
          = n.choose k * k.factorial * ((n - k) * (n - 1 - k).factorial) := by ring
        _ = n.choose k * k.factorial * (n - k).factorial := by rw [← hfact_nk]
        _ = n.factorial := h1
        _ = n * (n - 1).factorial := hfact_n
    have h4 : n * ((n - 1).choose k * k.factorial * (n - 1 - k).factorial) =
              n * (n - 1).factorial := by rw [h2]
    have h5 : (n - k) * (n.choose k * k.factorial * (n - 1 - k).factorial) =
              n * ((n - 1).choose k * k.factorial * (n - 1 - k).factorial) := by
      rw [h3, h4]
    have hne : k.factorial * (n - 1 - k).factorial > 0 :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    have heq : (n - k) * n.choose k * (k.factorial * (n - 1 - k).factorial) =
               n * (n - 1).choose k * (k.factorial * (n - 1 - k).factorial) := by
      calc (n - k) * n.choose k * (k.factorial * (n - 1 - k).factorial)
          = (n - k) * (n.choose k * k.factorial * (n - 1 - k).factorial) := by ring
        _ = n * ((n - 1).choose k * k.factorial * (n - 1 - k).factorial) := h5
        _ = n * (n - 1).choose k * (k.factorial * (n - 1 - k).factorial) := by ring
    exact Nat.eq_of_mul_eq_mul_right hne heq
  have hid2 : (k + 1) * n.choose (k + 1) = n * (n - 1).choose k := by
    -- (k+1) * C(n, k+1) = n * C(n-1, k)
    have h := Nat.add_one_mul_choose_eq (n - 1) k
    -- (n-1+1) * C(n-1, k) = C(n-1+1, k+1) * (k+1)
    have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [hn_eq] at h
    linarith
  -- Now cast to ℝ.
  have hCk_ne : (n.choose k : ℝ) ≠ 0 := by
    have : n.choose k > 0 := Nat.choose_pos hkn
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hCk1_ne : (n.choose (k + 1) : ℝ) ≠ 0 := by
    have : n.choose (k + 1) > 0 := Nat.choose_pos hk1n
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hCnk_ne : ((n - 1).choose k : ℝ) ≠ 0 := by
    have hk_le' : k ≤ n - 1 := hk
    have : (n - 1).choose k > 0 := Nat.choose_pos hk_le'
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  -- (n-k)·C(n,k) = n·C(n-1,k) in ℕ, so in ℝ: (n-k : ℕ) * C(n,k) = n * C(n-1,k)
  have hid1R : ((n - k : ℕ) : ℝ) * (n.choose k : ℝ) = (n : ℝ) * ((n - 1).choose k : ℝ) := by
    exact_mod_cast hid1
  have hid2R : ((k + 1 : ℕ) : ℝ) * (n.choose (k + 1) : ℝ) =
               (n : ℝ) * ((n - 1).choose k : ℝ) := by
    exact_mod_cast hid2
  have hnk_cast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) :=
    Nat.cast_sub hkn
  rw [hnk_cast] at hid1R
  push_cast at hid2R
  -- Now compute 1/C(n,k) + 1/C(n,k+1).
  -- 1/C(n,k) = (n-k) / (n * C(n-1,k))
  -- 1/C(n,k+1) = (k+1) / (n * C(n-1,k))
  have hnCnk_ne : (n : ℝ) * ((n - 1).choose k : ℝ) ≠ 0 := mul_ne_zero hn_ne hCnk_ne
  have h1 : 1 / (n.choose k : ℝ) = ((n : ℝ) - k) / ((n : ℝ) * ((n - 1).choose k : ℝ)) := by
    rw [div_eq_div_iff hCk_ne hnCnk_ne]
    linarith [hid1R]
  have h2 : 1 / (n.choose (k + 1) : ℝ) = ((k : ℝ) + 1) / ((n : ℝ) * ((n - 1).choose k : ℝ)) := by
    rw [div_eq_div_iff hCk1_ne hnCnk_ne]
    linarith [hid2R]
  rw [h1, h2]
  rw [← add_div]
  rw [div_eq_div_iff hnCnk_ne hnCnk_ne]
  ring

/-- Sum rewriting using `k·C(n,k) = n·C(n-1,k-1)`:
    `∑_{k=1}^n 1/(k · C(n,k)) = (1/n) · ∑_{j=0}^{n-1} 1/C(n-1, j)`. -/
lemma sum_inv_k_choose_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / ((k : ℝ) * (n.choose k : ℝ)) =
      (1 / (n : ℝ)) * ∑ j ∈ range n, (1 : ℝ) / ((n - 1).choose j : ℝ) := by
  -- Reindex k = j+1, j ∈ range n.
  -- k · C(n,k) = n · C(n-1, k-1). So 1/(k · C(n,k)) = 1/(n · C(n-1, k-1)).
  rw [show (Icc 1 n) = (range n).image (· + 1) from ?_]
  · rw [sum_image (fun _ _ _ _ h => by omega)]
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    -- Need: 1 / ((j+1) * C(n, j+1)) = (1/n) * (1 / C(n-1, j))
    have hid : ((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ) =
               (n : ℝ) * ((n - 1).choose j : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (n - 1) j
      have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [hn_eq] at h
      have hN : (j + 1) * n.choose (j + 1) = n * (n - 1).choose j := by linarith
      exact_mod_cast hN
    have hj1 : j + 1 ≤ n := hj
    have hCk_ne : (n.choose (j+1) : ℝ) ≠ 0 := by
      have : n.choose (j+1) > 0 := Nat.choose_pos hj1
      exact_mod_cast Nat.pos_iff_ne_zero.mp this
    have hCnk_ne : ((n - 1).choose j : ℝ) ≠ 0 := by
      have hj_le : j ≤ n - 1 := by omega
      have : (n - 1).choose j > 0 := Nat.choose_pos hj_le
      exact_mod_cast Nat.pos_iff_ne_zero.mp this
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
    have hj1_ne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by
      push_cast; positivity
    field_simp
    linarith [hid]
  · ext k
    simp [mem_Icc, mem_image, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega

/-- `∑_{k=0}^n 1/C(n, k) = 1 + (n+1)/(2n) · ∑_{j=0}^{n-1} 1/C(n-1, j)` for `n ≥ 1`.
In the form used below, `2n · ∑_{k=0}^n 1/C(n,k) = 2n + (n+1) · ∑_{j=0}^{n-1} 1/C(n-1,j)`. -/
lemma two_n_sum_inv_choose_eq (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) * (n : ℝ) * ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) =
      2 * (n : ℝ) + (n + 1 : ℝ) * ∑ j ∈ range n, (1 : ℝ) / ((n - 1).choose j : ℝ) := by
  -- ∑_{k=0}^n 1/C(n,k): split into first + middle + last.
  -- Actually we use: 2·∑_{k=0}^n 1/C(n,k) = 2 + ∑_{k=0}^{n-1}(1/C(n,k) + 1/C(n,k+1)).
  -- Proof: 2·∑_{k=0}^n = ∑_{k=0}^n + ∑_{k=0}^n = (1/C(n,0)) + ∑_{k=1}^n 1/C(n,k) + ∑_{k=0}^{n-1} 1/C(n,k) + 1/C(n,n)
  --   = 1 + 1 + ∑_{k=1}^n + ∑_{k=0}^{n-1} = 2 + ∑_{k=0}^{n-1} (1/C(n,k+1) + 1/C(n,k)).
  -- Then use the identity 1/C(n,k) + 1/C(n,k+1) = (n+1)/(n · C(n-1,k)).
  have h_sum_split :
      2 * ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) =
      2 + ∑ k ∈ range n, ((1 : ℝ) / (n.choose k : ℝ) + 1 / (n.choose (k + 1) : ℝ)) := by
    -- LHS = ∑ + ∑
    have hS : ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) =
              1 + ∑ k ∈ range n, (1 : ℝ) / (n.choose (k + 1) : ℝ) := by
      rw [sum_range_succ']
      simp [add_comm]
    have hS' : ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) =
               (∑ k ∈ range n, (1 : ℝ) / (n.choose k : ℝ)) + 1 := by
      rw [sum_range_succ]
      congr 1
      rw [Nat.choose_self]; simp
    calc 2 * ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ)
        = (∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ)) +
          (∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ)) := by ring
      _ = (1 + ∑ k ∈ range n, (1 : ℝ) / (n.choose (k + 1) : ℝ)) +
          ((∑ k ∈ range n, (1 : ℝ) / (n.choose k : ℝ)) + 1) := by rw [← hS, ← hS']
      _ = 2 + ∑ k ∈ range n, ((1 : ℝ) / (n.choose k : ℝ) + 1 / (n.choose (k + 1) : ℝ)) := by
          rw [sum_add_distrib]; ring
  have h_pair_sum : ∑ k ∈ range n,
        ((1 : ℝ) / (n.choose k : ℝ) + 1 / (n.choose (k + 1) : ℝ)) =
      ((n + 1 : ℝ) / n) * ∑ k ∈ range n, (1 : ℝ) / ((n - 1).choose k : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    have hk_le : k ≤ n - 1 := by omega
    rw [inv_choose_add_inv_choose_succ n k hn hk_le]
    have hCnk_ne : ((n - 1).choose k : ℝ) ≠ 0 := by
      have : (n - 1).choose k > 0 := Nat.choose_pos hk_le
      exact_mod_cast Nat.pos_iff_ne_zero.mp this
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
    field_simp
  -- Put it together.
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  calc 2 * (n : ℝ) * ∑ k ∈ range (n + 1), 1 / (n.choose k : ℝ)
      = (n : ℝ) * (2 * ∑ k ∈ range (n + 1), 1 / (n.choose k : ℝ)) := by ring
    _ = (n : ℝ) * (2 + ∑ k ∈ range n,
            ((1 : ℝ) / (n.choose k : ℝ) + 1 / (n.choose (k + 1) : ℝ))) := by rw [h_sum_split]
    _ = (n : ℝ) * (2 + ((n + 1 : ℝ) / n) * ∑ k ∈ range n, 1 / ((n - 1).choose k : ℝ)) := by
          rw [h_pair_sum]
    _ = 2 * (n : ℝ) + (n + 1 : ℝ) * ∑ j ∈ range n, 1 / ((n - 1).choose j : ℝ) := by
          have : (n : ℝ) * (((n + 1 : ℝ) / n) * ∑ k ∈ range n, 1 / ((n - 1).choose k : ℝ)) =
                 (n + 1 : ℝ) * ∑ k ∈ range n, 1 / ((n - 1).choose k : ℝ) := by
            rw [← mul_assoc]; field_simp
          linarith [this]

/-- The quantity `x n = (2^n / n) · ∑_{j=0}^{n-1} 1/C(n-1, j)` for `n ≥ 1`. -/
noncomputable def x (n : ℕ) : ℝ :=
  ((2 : ℝ)^n / n) * ∑ j ∈ range n, 1 / ((n - 1).choose j : ℝ)

/-- The recurrence `x (n+1) = x n + 2^(n+1) / (n+1)` for `n ≥ 1`. -/
lemma x_succ (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = x n + (2 : ℝ)^(n + 1) / (n + 1) := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have hn1_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; positivity
  have hnn1 : ((n + 1 - 1 : ℕ) : ℝ) = (n : ℝ) := by push_cast; ring
  have hkey := two_n_sum_inv_choose_eq n hn
  -- x(n+1) = (2^(n+1) / (n+1)) * ∑_{k ∈ range (n+1)} 1/C(n, k)
  -- Goal: x(n+1) = x n + 2^(n+1)/(n+1)
  unfold x
  have h_n1_minus_1 : (n + 1 - 1 : ℕ) = n := by omega
  rw [h_n1_minus_1]
  push_cast
  -- Now: (2^(n+1) / (n+1)) * ∑_{k ∈ range (n+1)} 1/C(n, k) = x n + 2^(n+1)/(n+1)
  -- From hkey: 2n · ∑ ... = 2n + (n+1) · ∑_{j ∈ range n} 1/C(n-1, j)
  -- So ∑ k ∈ range (n+1), 1/C(n,k) = 1 + ((n+1)/(2n)) · ∑_{j ∈ range n} 1/C(n-1, j)
  have hsum : ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) =
              1 + ((n + 1 : ℝ) / (2 * n)) * ∑ j ∈ range n, 1 / ((n - 1).choose j : ℝ) := by
    have h2n_ne : (2 * (n : ℝ)) ≠ 0 := by positivity
    have := hkey
    field_simp at this ⊢
    linarith
  rw [hsum]
  field_simp
  ring

/-- Base case: `x 1 = 2`. -/
lemma x_one : x 1 = 2 := by
  unfold x
  simp

/-- `x n = ∑_{k=1}^n 2^k / k` for `n ≥ 1`. -/
lemma x_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    x n = ∑ k ∈ Icc 1 n, (2 : ℝ)^k / k := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [x_one]
    simp [Icc_self, Finset.sum_singleton]
  | succ n hn ih =>
    rw [x_succ n hn, ih]
    -- Goal: ∑ k ∈ Icc 1 n, 2^k/k + 2^(n+1)/(n+1) = ∑ k ∈ Icc 1 (n+1), 2^k/k
    have hIcc : Icc 1 (n + 1) = Icc 1 n ∪ {n + 1} := by
      ext k
      simp only [mem_Icc, mem_union, mem_singleton]
      omega
    rw [hIcc]
    have hdisj : Disjoint (Icc 1 n) ({n + 1} : Finset ℕ) := by
      rw [disjoint_singleton_right]
      simp [mem_Icc]
    rw [sum_union hdisj, sum_singleton]
    push_cast
    ring

snip end

problem imc2002_p3 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, ((1 / (n.choose k : ℝ)) - (2 : ℝ)^((k : ℤ) - n)) / k = 0 := by
  -- The sum ∑ (a_k - b_k)/k = ∑ a_k/k - ∑ b_k/k
  -- = ∑_{k=1}^n 1/(k C(n,k)) - ∑_{k=1}^n 2^(k-n)/k
  -- The first equals (1/n) · ∑_{j=0}^{n-1} 1/C(n-1,j) = x n / 2^n
  -- The second equals (1/2^n) · ∑_{k=1}^n 2^k/k = x n / 2^n (by x_eq_sum)
  -- Hence they are equal, so the difference is 0.
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have h2n_ne : (2 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  -- Split the sum.
  have hsplit : ∑ k ∈ Icc 1 n, ((1 / (n.choose k : ℝ)) - (2 : ℝ)^((k : ℤ) - n)) / k =
      (∑ k ∈ Icc 1 n, (1 : ℝ) / ((k : ℝ) * (n.choose k : ℝ))) -
      ∑ k ∈ Icc 1 n, (2 : ℝ)^((k : ℤ) - n) / k := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    rw [mem_Icc] at hk
    have hk_ne : (k : ℝ) ≠ 0 := by
      have hk1 : 1 ≤ k := hk.1
      exact_mod_cast Nat.pos_iff_ne_zero.mp hk1
    rw [sub_div]
    congr 1
    rw [div_div, mul_comm]
  rw [hsplit]
  -- First sum.
  rw [sum_inv_k_choose_eq n hn]
  -- = (1/n) · ∑_{j=0}^{n-1} 1/C(n-1,j) = (2^n / n · ∑...) / 2^n = x n / 2^n
  have hfirst : (1 / (n : ℝ)) * ∑ j ∈ range n, 1 / ((n - 1).choose j : ℝ) = x n / (2 : ℝ)^n := by
    unfold x
    field_simp
  rw [hfirst]
  -- Second sum: ∑ 2^(k-n)/k = (1/2^n) ∑ 2^k/k = x n / 2^n by x_eq_sum
  have hsecond : ∑ k ∈ Icc 1 n, (2 : ℝ)^((k : ℤ) - n) / k = x n / (2 : ℝ)^n := by
    rw [x_eq_sum n hn]
    rw [eq_div_iff h2n_ne]
    rw [sum_mul]
    apply sum_congr rfl
    intro k hk
    rw [mem_Icc] at hk
    have hk_ne : (k : ℝ) ≠ 0 := by
      have : k ≥ 1 := hk.1
      exact_mod_cast Nat.pos_iff_ne_zero.mp this
    rw [show ((k : ℤ) - n) = ((k : ℤ) + (-n : ℤ)) from by ring]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have h1 : (2 : ℝ)^((k : ℤ)) = (2 : ℝ)^k := by
      rw [show ((k : ℤ)) = ((k : ℕ) : ℤ) from rfl, zpow_natCast]
    have h2 : (2 : ℝ)^(-(n : ℤ)) = 1 / (2 : ℝ)^n := by
      rw [zpow_neg, zpow_natCast, one_div]
    rw [h1, h2]
    field_simp
  rw [hsecond]
  ring

end Imc2002P3
