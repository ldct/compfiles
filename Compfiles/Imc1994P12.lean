/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 12 (Day 2 Problem 6)

Find
`lim_{N → ∞} (ln² N / N) * Σ_{k=2}^{N-2} 1/(ln k · ln(N - k)) = 1`.

## Proof outline (official solution)

Let `A_N = (ln² N / N) · Σ_{k=2}^{N-2} 1/(ln k · ln(N - k))`.

* **Lower bound.** For `2 ≤ k ≤ N - 2` we have `ln k ≤ ln N` and
  `ln (N - k) ≤ ln N`, hence `1 / (ln k · ln (N - k)) ≥ 1 / ln² N`. Summing
  the `N - 3` terms,
  `A_N ≥ (ln² N / N) · (N - 3) / ln² N = 1 - 3/N → 1`.

* **Upper bound.** The function `k ↦ 1/(ln k · ln (N - k))` is decreasing
  on `[2, N/2]` and symmetric about `N/2`. With
  `M := ⌊N/ln² N⌋ + 1 < N/2`, split the range into the two `[2, M]` tails
  and the middle `[M+1, N-M-1]`. The tails are bounded by the maximum
  `1/(ln 2 · ln (N - 2))` and the middle by `1/(ln M · ln (N - M))`, giving
  `A_N ≤ 2M ln N / (N ln 2) + (1 - 2M/N) · ln N / ln M + O(1/ln N)`.
  Since `ln M = ln N − 2 ln ln N + O(1)` and `M = O(N / ln² N)`, both terms
  tend to `1`, yielding `lim sup A_N ≤ 1`.

The lower bound is fully formalized below. The upper bound argument is
genuinely involved (Riemann-sum splitting, careful asymptotic estimates
using `M = ⌊N/ln² N⌋ + 1`), so it is left as a `sorry` with detailed
in-line `TODO` comments.
-/

namespace Imc1994P12

open Filter Finset
open scoped Topology BigOperators

/-- The sum appearing in the problem: `Σ_{k=2}^{N-2} 1 / (ln k · ln (N - k))`. -/
noncomputable def innerSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (N - 2), 1 / (Real.log k * Real.log (N - k))

/-- The full expression `A_N := (ln² N / N) · Σ_{k=2}^{N-2} 1/(ln k · ln(N-k))`. -/
noncomputable def A (N : ℕ) : ℝ :=
  (Real.log N)^2 / N * innerSum N

snip begin

/-- For `N ≥ 5` and `2 ≤ k ≤ N - 2`, both `ln k` and `ln (N - k)` are positive. -/
lemma log_pos_of_mem {N k : ℕ} (hN : 5 ≤ N) (hk : k ∈ Finset.Icc 2 (N - 2)) :
    0 < Real.log k ∧ 0 < Real.log ((N : ℝ) - k) := by
  rw [Finset.mem_Icc] at hk
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨?_, ?_⟩
  · have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    exact Real.log_pos this
  · have hNk : (1 : ℝ) < (N : ℝ) - k := by
      have h1 : k + 1 < N := by omega
      have : (k : ℝ) + 1 < N := by exact_mod_cast h1
      linarith
    exact Real.log_pos hNk

/-- For `N ≥ 5` and `2 ≤ k ≤ N - 2`, `ln k ≤ ln N`. -/
lemma log_le_log_N_left {N k : ℕ} (hN : 5 ≤ N) (hk : k ∈ Finset.Icc 2 (N - 2)) :
    Real.log k ≤ Real.log N := by
  rw [Finset.mem_Icc] at hk
  obtain ⟨_, hk2⟩ := hk
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast (by omega : k ≤ N)
  exact Real.log_le_log hk_pos hkN

/-- For `N ≥ 5` and `2 ≤ k ≤ N - 2`, `ln (N - k) ≤ ln N`. -/
lemma log_le_log_N_right {N k : ℕ} (hN : 5 ≤ N) (hk : k ∈ Finset.Icc 2 (N - 2)) :
    Real.log ((N : ℝ) - k) ≤ Real.log N := by
  rw [Finset.mem_Icc] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hpos : (0 : ℝ) < (N : ℝ) - k := by
    have hkN : k + 1 < N := by omega
    have : (k : ℝ) + 1 < N := by exact_mod_cast hkN
    linarith
  have hle : (N : ℝ) - k ≤ (N : ℝ) := by
    have hk_nn : (0 : ℝ) ≤ k := by exact_mod_cast (Nat.zero_le k)
    linarith
  exact Real.log_le_log hpos hle

/-- The cardinality of `Finset.Icc 2 (N - 2)` for `N ≥ 5` is `N - 3`. -/
lemma card_Icc_aux {N : ℕ} (hN : 5 ≤ N) :
    (Finset.Icc 2 (N - 2)).card = N - 3 := by
  rw [Nat.card_Icc]
  omega

/-- **Lower bound** on the inner sum: for `N ≥ 5`,
`Σ_{k=2}^{N-2} 1/(ln k · ln (N - k)) ≥ (N - 3) / ln² N`. -/
lemma innerSum_lb {N : ℕ} (hN : 5 ≤ N) :
    ((N : ℝ) - 3) / (Real.log N)^2 ≤ innerSum N := by
  have hlogN_pos : 0 < Real.log N := by
    have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact Real.log_pos this
  have hlogN_sq_pos : 0 < (Real.log N)^2 := by positivity
  -- Each term ≥ 1 / ln² N.
  have hterm : ∀ k ∈ Finset.Icc 2 (N - 2),
      1 / (Real.log N)^2 ≤ 1 / (Real.log k * Real.log ((N : ℝ) - k)) := by
    intro k hk
    obtain ⟨hk_pos, hNk_pos⟩ := log_pos_of_mem hN hk
    have hk_le : Real.log k ≤ Real.log N := log_le_log_N_left hN hk
    have hNk_le : Real.log ((N : ℝ) - k) ≤ Real.log N := log_le_log_N_right hN hk
    have hprod_pos : 0 < Real.log k * Real.log ((N : ℝ) - k) := mul_pos hk_pos hNk_pos
    have hprod_le : Real.log k * Real.log ((N : ℝ) - k) ≤ (Real.log N)^2 := by
      have := mul_le_mul hk_le hNk_le (le_of_lt hNk_pos) (le_of_lt hlogN_pos)
      have hsq : Real.log N * Real.log N = (Real.log N)^2 := by ring
      linarith [hsq]
    exact one_div_le_one_div_of_le hprod_pos hprod_le
  calc ((N : ℝ) - 3) / (Real.log N)^2
      = (Finset.Icc 2 (N - 2)).card • (1 / (Real.log N)^2) := by
        rw [card_Icc_aux hN]
        rw [nsmul_eq_mul]
        have h3 : 3 ≤ N := by omega
        rw [Nat.cast_sub h3]
        push_cast
        ring
    _ = ∑ _k ∈ Finset.Icc 2 (N - 2), 1 / (Real.log N)^2 := by
        rw [Finset.sum_const]
    _ ≤ ∑ k ∈ Finset.Icc 2 (N - 2), 1 / (Real.log k * Real.log ((N : ℝ) - k)) :=
        Finset.sum_le_sum hterm
    _ = innerSum N := by
        unfold innerSum
        apply Finset.sum_congr rfl
        intros k _
        congr 1

/-- **Lower bound** on `A_N`: for `N ≥ 5`, `A_N ≥ 1 - 3 / N`. -/
lemma A_lb {N : ℕ} (hN : 5 ≤ N) : 1 - 3 / (N : ℝ) ≤ A N := by
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN_pos : 0 < Real.log N := by
    have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact Real.log_pos this
  have hlogN_sq_pos : 0 < (Real.log N)^2 := by positivity
  have hlb := innerSum_lb hN
  unfold A
  have hcoef_pos : 0 < (Real.log N)^2 / (N : ℝ) := div_pos hlogN_sq_pos hN_pos
  -- (ln² N / N) * innerSum N ≥ (ln² N / N) * ((N - 3) / ln² N) = (N - 3)/N
  have h1 : (Real.log N)^2 / (N : ℝ) * (((N : ℝ) - 3) / (Real.log N)^2)
              = ((N : ℝ) - 3) / N := by
    field_simp
  have h2 : (Real.log N)^2 / (N : ℝ) * (((N : ℝ) - 3) / (Real.log N)^2)
              ≤ (Real.log N)^2 / (N : ℝ) * innerSum N :=
    mul_le_mul_of_nonneg_left hlb (le_of_lt hcoef_pos)
  rw [h1] at h2
  have h3 : ((N : ℝ) - 3) / N = 1 - 3 / N := by
    field_simp
  linarith [h2, h3.symm.le]

snip end

problem imc1994_p12 :
    Tendsto (fun N : ℕ => A N) atTop (nhds 1) := by
  -- We sandwich A N between 1 - 3/N (lower bound, fully proved above) and
  -- 1 + ε(N) where ε(N) → 0 (upper bound; see TODO below).
  --
  -- TODO (upper bound): formalize the official asymptotic argument.
  -- Setting M = ⌊N/(log N)^2⌋ + 1, split the sum at indices M and N - M:
  --   * the two tail blocks `[2, M]` and `[N - M, N - 2]` each contribute
  --     ≤ (M - 1) / (log 2 · log (N - 2));
  --   * the middle block `[M + 1, N - M - 1]` is monotone-symmetric,
  --     bounded by (N - 2M - 1) / (log M · log (N - M)).
  -- Multiplying by ln² N / N and using ln M = ln N - 2 ln ln N + O(1) gives
  --   A N ≤ 1 + O(ln ln N / ln N) → 1.
  -- Together with `A_lb`, the squeeze theorem yields the result.
  sorry

end Imc1994P12
