/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1999, Problem 2 (Day 1)

Does there exist a bijection `π : ℕ → ℕ` with
`∑_{n=1}^∞ π(n) / n² < ∞`?

The answer is **no**.

## Solution sketch (official)

Suppose such a bijection existed. For any `N ≥ 1`, the values
`π(N+1), …, π(3N)` are `2N` distinct natural numbers. Hence their sum is
at least `0 + 1 + … + (2N-1) = N(2N-1) ≥ N²` (for `N ≥ 1`). Therefore

  `∑_{n=N+1}^{3N} π(n) / n² ≥ (1 / (3N)²) · N² = 1 / 9`.

In particular, the partial sums are not Cauchy, contradicting summability.
-/

namespace Imc1999P2

open scoped BigOperators
open Finset

snip begin

/-- For a finset `s ⊆ ℕ`, the `i`-th element (in sorted order) is at least `i`. -/
lemma orderEmbOfFin_ge (s : Finset ℕ) {k : ℕ} (h : s.card = k) (i : Fin k) :
    (i : ℕ) ≤ s.orderEmbOfFin h i := by
  rcases i with ⟨i, hi⟩
  induction i with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hj : j < k := lt_of_le_of_lt (Nat.le_succ j) hi
    have ih' := ih hj
    have hlt : s.orderEmbOfFin h ⟨j, hj⟩ < s.orderEmbOfFin h ⟨j+1, hi⟩ :=
      (s.orderEmbOfFin h).strictMono (by simp [Fin.lt_def])
    show j + 1 ≤ s.orderEmbOfFin h ⟨j + 1, hi⟩
    -- Note: ih' here is `↑(⟨j, hj⟩ : Fin k) ≤ ...` which simplifies to `j ≤ ...`
    have hih : j ≤ (s.orderEmbOfFin h ⟨j, hj⟩ : ℕ) := ih'
    have hlt' : (s.orderEmbOfFin h ⟨j, hj⟩ : ℕ) < s.orderEmbOfFin h ⟨j+1, hi⟩ := hlt
    omega

/-- For any finset `s ⊆ ℕ`, the sum of its elements is at least
`s.card * (s.card - 1) / 2` (the sum of the smallest `|s|` distinct
naturals `0, 1, …, |s|-1`). -/
lemma finset_nat_sum_ge_triangular (s : Finset ℕ) :
    s.card * (s.card - 1) / 2 ≤ ∑ n ∈ s, n := by
  classical
  -- Use the order embedding `Fin s.card ↪o ℕ` to write the sum.
  have hk : s.card = s.card := rfl
  have himg : (Finset.univ : Finset (Fin s.card)).image (s.orderEmbOfFin hk) = s :=
    Finset.image_orderEmbOfFin_univ s hk
  have hsum_eq : ∑ n ∈ s, n = ∑ i : Fin s.card, (s.orderEmbOfFin hk i : ℕ) := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image]
    intros _ _ _ _ heq
    exact (s.orderEmbOfFin hk).injective heq
  rw [hsum_eq]
  -- ∑ i : Fin k, orderEmbOfFin h i ≥ ∑ i : Fin k, (i : ℕ).
  have hbd : ∑ i : Fin s.card, ((i : ℕ) : ℕ) ≤ ∑ i : Fin s.card, (s.orderEmbOfFin hk i : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    exact orderEmbOfFin_ge s hk i
  refine le_trans ?_ hbd
  -- ∑ i : Fin k, (i : ℕ) = ∑ i ∈ range k, i = k*(k-1)/2.
  have heq : ∑ i : Fin s.card, ((i : ℕ) : ℕ) = ∑ i ∈ range s.card, i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => i)]
  rw [heq, Finset.sum_range_id]

/-- Easier formulation: for an injective `f : ℕ → ℕ` and finset `s`,
the sum `∑_{n ∈ s} f n` is at least `s.card * (s.card - 1) / 2`. -/
lemma sum_inj_ge_triangular (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : Finset ℕ) :
    s.card * (s.card - 1) / 2 ≤ ∑ n ∈ s, f n := by
  have h1 : ∑ n ∈ s, f n = ∑ m ∈ s.image f, m := by
    rw [Finset.sum_image]
    intros _ _ _ _ h; exact hf h
  rw [h1]
  have hcard : (s.image f).card = s.card := Finset.card_image_of_injective s hf
  have := finset_nat_sum_ge_triangular (s.image f)
  rw [hcard] at this
  exact this

/-- For `N ≥ 1`, the cardinality of `Ico (N+1) (3N+1)` is `2N`. -/
lemma card_Ico_window (N : ℕ) :
    (Finset.Ico (N + 1) (3 * N + 1)).card = 2 * N := by
  rw [Nat.card_Ico]; omega

/-- Key bound: for a bijection `π : ℕ → ℕ` and `N ≥ 1`,
`∑_{n=N+1}^{3N} π n ≥ N²`. -/
lemma sum_window_ge (π : ℕ → ℕ) (hπ : Function.Bijective π) (N : ℕ) (hN : 1 ≤ N) :
    N * N ≤ ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), π n := by
  have h1 := sum_inj_ge_triangular π hπ.injective (Finset.Ico (N + 1) (3 * N + 1))
  rw [card_Ico_window] at h1
  -- We have 2N * (2N - 1) / 2 ≤ sum. Now 2N*(2N-1)/2 = N*(2N-1) ≥ N*N for N ≥ 1.
  refine le_trans ?_ h1
  -- Goal: N*N ≤ 2N*(2N-1)/2.
  rcases N with _ | N
  · omega
  · -- N ≥ 1, so 2N - 1 ≥ N. Then 2N*(2N-1)/2 = N*(2N-1) ≥ N*N.
    have hkey : 2 * (N + 1) * (2 * (N + 1) - 1) / 2 = (N + 1) * (2 * (N + 1) - 1) := by
      have : 2 * (N + 1) * (2 * (N + 1) - 1) = (N + 1) * (2 * (N + 1) - 1) * 2 := by ring
      rw [this, Nat.mul_div_cancel _ Nat.zero_lt_two]
    rw [hkey]
    have h2 : N + 1 ≤ 2 * (N + 1) - 1 := by omega
    exact Nat.mul_le_mul_left _ h2

/-- Real cast version: for a bijection `π : ℕ → ℕ` and `N ≥ 1`,
`∑_{n=N+1}^{3N} (π n : ℝ) ≥ N²`. -/
lemma sum_window_ge_real (π : ℕ → ℕ) (hπ : Function.Bijective π) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * N ≤ ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ) := by
  have h := sum_window_ge π hπ N hN
  have hcast : ((N * N : ℕ) : ℝ) ≤ ((∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), π n : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  exact hcast

snip end

/-- **IMC 1999 Problem 2.**
There is no bijection `π : ℕ → ℕ` such that the series
`∑ n, π(n) / n²` converges. (Equivalently, no such bijection has a
summable scaling `n ↦ π(n)/n²`. The `n = 0` term is `0` by convention,
so this matches the original statement of the series starting at `n = 1`.) -/
problem imc1999_p2 :
    ¬ ∃ π : ℕ → ℕ, Function.Bijective π ∧
      Summable (fun n : ℕ => (π n : ℝ) / (n : ℝ) ^ 2) := by
  rintro ⟨π, hπ, hsum⟩
  -- The general strategy: show partial sums are not Cauchy.
  -- 1. Series is summable, so its tail goes to 0:
  --    `∀ ε > 0, ∃ K, ∀ A B, K ≤ A ≤ B → |∑_{n ∈ Ico A B} π n / n²| < ε`.
  -- 2. Take ε = 1/9, get K. Pick N ≥ max K 1.
  -- 3. Compute ∑ over Ico (N+1) (3N+1) is ≥ 1/9 by `sum_window_ge_real`
  --    and bounding 1/n² ≥ 1/(3N)² on the window.
  -- 4. Contradiction with the Cauchy bound.

  -- Show the limit of ∑_{n ∈ Ico (N+1) (3N+1)} π n / n² is 0.
  have htail : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    -- ∑_{Ico (N+1) (3N+1)} = ∑_{Ico 0 (3N+1)} - ∑_{Ico 0 (N+1)}
    have hL : Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, (π n : ℝ) / (n : ℝ) ^ 2)
        Filter.atTop (nhds (∑' n, (π n : ℝ) / (n : ℝ) ^ 2)) :=
      hsum.hasSum.tendsto_sum_nat
    -- partial sums tend to S. Then the difference tends to S - S = 0.
    set S := ∑' n, (π n : ℝ) / (n : ℝ) ^ 2
    have hL3 : Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2)
        Filter.atTop (nhds S) := by
      have h := hL.comp (Filter.tendsto_atTop_atTop.mpr
        (fun M => ⟨M, fun N hN => by omega⟩) :
          Filter.Tendsto (fun N : ℕ => 3 * N + 1) Filter.atTop Filter.atTop)
      exact h
    have hL1 : Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (π n : ℝ) / (n : ℝ) ^ 2)
        Filter.atTop (nhds S) := by
      have h := hL.comp (Filter.tendsto_atTop_atTop.mpr
        (fun M => ⟨M, fun N hN => by omega⟩) :
          Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop)
      exact h
    have hdiff := hL3.sub hL1
    rw [sub_self] at hdiff
    -- ∑ Ico (N+1) (3N+1) = ∑ range (3N+1) - ∑ range (N+1)
    have heq : ∀ N : ℕ,
        (∑ n ∈ Finset.range (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2)
        - (∑ n ∈ Finset.range (N + 1), (π n : ℝ) / (n : ℝ) ^ 2)
        = ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2 := by
      intro N
      have hsplit : ∑ n ∈ Finset.range (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2
          = (∑ n ∈ Finset.range (N + 1), (π n : ℝ) / (n : ℝ) ^ 2)
            + ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2 := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
        exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _)
          (by omega : N + 1 ≤ 3 * N + 1)).symm
      linarith
    convert hdiff using 1
    funext N; rw [heq]
  -- Now exhibit a contradiction: for each N ≥ 1, the tail at N is ≥ 1/9.
  -- So it cannot tend to 0.
  have hge : ∀ N : ℕ, 1 ≤ N →
      (1 : ℝ) / 9 ≤ ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ) / (n : ℝ) ^ 2 := by
    intro N hN
    -- For n in Ico (N+1) (3N+1), n ≤ 3N, so n² ≤ (3N)² = 9N², so 1/n² ≥ 1/(9N²) > 0.
    -- Hence ∑ π n / n² ≥ ∑ π n / (3N)² = (1/9N²) * ∑ π n ≥ (1/9N²) * N² = 1/9.
    have h3N_pos : (0 : ℝ) < 3 * N := by exact_mod_cast (by omega : 0 < 3 * N)
    have h3N_sq_pos : (0 : ℝ) < (3 * N : ℝ) ^ 2 := by positivity
    have hwin : ∀ n ∈ Finset.Ico (N + 1) (3 * N + 1),
        (π n : ℝ) / (3 * N : ℝ) ^ 2 ≤ (π n : ℝ) / (n : ℝ) ^ 2 := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hn_pos : 0 < n := by omega
      have hn_le : n ≤ 3 * N := by omega
      have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have hnR_le : (n : ℝ) ≤ 3 * N := by exact_mod_cast hn_le
      have hn_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have hsq_le : (n : ℝ) ^ 2 ≤ (3 * N : ℝ) ^ 2 := by
        apply pow_le_pow_left₀ hnR_pos.le hnR_le
      apply div_le_div_of_nonneg_left (by positivity) hn_sq_pos hsq_le
    have hsum_le := Finset.sum_le_sum hwin
    -- ∑ π n / (3N)² = (1 / (3N)²) * ∑ π n.
    have hfac : ∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ) / (3 * N : ℝ) ^ 2
        = (∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ)) / (3 * N : ℝ) ^ 2 := by
      rw [Finset.sum_div]
    rw [hfac] at hsum_le
    have hsumN := sum_window_ge_real π hπ N hN
    have hN_pos_R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN_sq_pos_R : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    -- ∑ π n ≥ N², so ∑ π n / (3N)² ≥ N²/(9N²) = 1/9.
    have h19 : (N : ℝ) * N / (3 * N : ℝ) ^ 2 = 1 / 9 := by
      have : (N : ℝ) ≠ 0 := hN_pos_R.ne'
      field_simp
      ring
    have hbd : (1 : ℝ) / 9 ≤
        (∑ n ∈ Finset.Ico (N + 1) (3 * N + 1), (π n : ℝ)) / (3 * N : ℝ) ^ 2 := by
      rw [← h19]
      exact div_le_div_of_nonneg_right hsumN h3N_sq_pos.le
    linarith
  -- htail tends to 0, but tail at every N ≥ 1 is ≥ 1/9. Contradiction.
  -- Eventually htail < 1/9 (with ε = 1/18 say).
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨K, hK⟩ := htail (1/18) (by norm_num)
  let N := max K 1
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNK : K ≤ N := le_max_left _ _
  have h1 := hge N hN1
  have h2 := hK N hNK
  rw [Real.dist_eq] at h2
  have h3 := abs_lt.mp h2
  linarith [h3.1, h3.2]

end Imc1999P2
