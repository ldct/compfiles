/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2011, Problem 8 (= Day 2 P3)

Determine the value of
  `∑_{n=1}^∞ ln(1 + 1/n) · ln(1 + 1/(2n)) · ln(1 + 1/(2n+1))`.

The answer is `(ln 2)^3 / 3`.
-/

namespace Imc2011P8

open Filter Topology

/-- The function `f(n) = ln(1 + 1/n) = ln((n+1)/n)`, with `f(0) = 0` by convention. -/
noncomputable def f (n : ℕ) : ℝ := Real.log (1 + 1 / (n : ℝ))

/-- The general term of the series, indexed from `n = 0`. We will state `HasSum` as
`∑' n, a n` where `a n` corresponds to the `(n+1)`-th term in the original sum. -/
noncomputable def a (n : ℕ) : ℝ := f (n + 1) * f (2 * (n + 1)) * f (2 * (n + 1) + 1)

snip begin

/-- `f(n) ≥ 0` for `n ≥ 1` (and also `f(0) = 0`). -/
lemma f_nonneg : ∀ n : ℕ, 0 ≤ f n := by
  intro n
  unfold f
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · apply Real.log_nonneg
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith

/-- `f(n) ≤ 1/n` for `n ≥ 1`. -/
lemma f_le_inv (n : ℕ) (hn : 1 ≤ n) : f n ≤ 1 / (n : ℝ) := by
  unfold f
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 1 + 1 / (n : ℝ) := by
    have h1 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- The key telescoping identity: `f(n) = f(2n) + f(2n+1)` for `n ≥ 1`. -/
lemma f_split (n : ℕ) (hn : 1 ≤ n) : f n = f (2 * n) + f (2 * n + 1) := by
  -- f(n) = log((n+1)/n)
  -- f(2n) = log((2n+1)/(2n))
  -- f(2n+1) = log((2n+2)/(2n+1))
  -- f(2n) + f(2n+1) = log((2n+2)/(2n)) = log((n+1)/n) = f(n).
  unfold f
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h2n_pos : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast (by omega : 0 < 2 * n)
  have h2n_ne : ((2 * n : ℕ) : ℝ) ≠ 0 := h2n_pos.ne'
  have h2n1_pos : (0 : ℝ) < (2 * n + 1 : ℕ) := by exact_mod_cast (by omega : 0 < 2 * n + 1)
  have h2n1_ne : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := h2n1_pos.ne'
  -- Express each as a single log of a ratio.
  have hA : (1 : ℝ) + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by field_simp
  have hB : (1 : ℝ) + 1 / ((2 * n : ℕ) : ℝ) =
      (((2 * n : ℕ) : ℝ) + 1) / ((2 * n : ℕ) : ℝ) := by field_simp
  have hC : (1 : ℝ) + 1 / ((2 * n + 1 : ℕ) : ℝ) =
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) := by field_simp
  rw [hA, hB, hC]
  -- Now the identity is: log((n+1)/n) = log((2n+1)/(2n)) + log((2n+2)/(2n+1))
  -- RHS = log( ((2n+1)/(2n)) * ((2n+2)/(2n+1)) ) = log((2n+2)/(2n)) = log((n+1)/n).
  have hpos1 : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < (((2 * n : ℕ) : ℝ) + 1) / ((2 * n : ℕ) : ℝ) := by positivity
  have hpos3 : (0 : ℝ) < (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) := by positivity
  rw [← Real.log_mul hpos2.ne' hpos3.ne']
  congr 1
  -- Want: (n+1)/n = ((2n+1)/(2n)) * ((2n+2)/(2n+1))
  have h2nn : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h2n1n : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
  rw [h2nn, h2n1n]
  field_simp
  ring

/-- `g(n) = ∑_{k=n}^{2n-1} f(k)^3 = ∑_{j<n} f(n+j)^3`. -/
noncomputable def g (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (f (n + j))^3

/-- Reindex `g(n+1) = ∑_{j<n+1} f((n+1)+j)^3`, isolating the `n`-th term. -/
lemma g_succ_split (n : ℕ) :
    g (n + 1) =
      (∑ j ∈ Finset.range n, (f ((n + 1) + j))^3) + f (2 * n + 1)^3 := by
  unfold g
  rw [Finset.sum_range_succ]
  have heq : (n + 1) + n = 2 * n + 1 := by ring
  rw [heq]

/-- The telescoping identity for `g`: `g(n) - g(n+1) = 3 * f(n) * f(2n) * f(2n+1)` for `n ≥ 1`. -/
lemma g_diff (n : ℕ) (hn : 1 ≤ n) :
    g n - g (n + 1) = 3 * f n * f (2 * n) * f (2 * n + 1) := by
  -- We show: g n - g(n+1) = f(n)^3 - f(2n)^3 - f(2n+1)^3.
  -- Then use f(n) = f(2n) + f(2n+1) and (a+b)^3 - a^3 - b^3 = 3ab(a+b).
  obtain ⟨m, hnm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Decompose g(n) by extracting the first index j = 0 (which gives f(n)^3).
  have h_g_n : g n = f n ^ 3 + ∑ j ∈ Finset.range m, (f (n + (j + 1)))^3 := by
    unfold g
    conv_lhs => rw [hnm]
    rw [Finset.sum_range_succ']
    simp [hnm]
    ring
  -- Decompose g(n+1) by extracting the last index j = n (gives f(2n+1)^3).
  have h_g_n1 : g (n + 1) =
      (∑ j ∈ Finset.range n, (f ((n + 1) + j))^3) + f (2 * n + 1)^3 :=
    g_succ_split n
  -- Further extract j = m from g(n+1)'s sum (gives f(2n)^3).
  have h_inner_n1 :
      (∑ j ∈ Finset.range n, (f ((n + 1) + j))^3) =
      (∑ j ∈ Finset.range m, (f ((n + 1) + j))^3) + f (2 * n)^3 := by
    have hn_eq : Finset.range n = Finset.range (m + 1) := by rw [hnm]
    rw [hn_eq, Finset.sum_range_succ]
    have heq1 : (n + 1) + m = 2 * n := by omega
    rw [heq1]
  rw [h_g_n, h_g_n1, h_inner_n1]
  -- Now both inner sums match (after re-indexing).
  have h_inner_eq : (∑ j ∈ Finset.range m, (f (n + (j + 1)))^3) =
      (∑ j ∈ Finset.range m, (f ((n + 1) + j))^3) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [h_inner_eq]
  -- Use f n = f(2n) + f(2n+1).
  have hsplit := f_split n hn
  set A := f (2 * n)
  set B := f (2 * n + 1)
  have hfn : f n = A + B := hsplit
  rw [hfn]
  ring

/-- `g(n) ≤ 1/n^2` for `n ≥ 1`. -/
lemma g_le (n : ℕ) (hn : 1 ≤ n) : g n ≤ 1 / (n : ℝ) ^ 2 := by
  unfold g
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound : ∀ j ∈ Finset.range n, (f (n + j))^3 ≤ (1 / (n : ℝ))^3 := by
    intro j _
    have hpos : 1 ≤ n + j := by omega
    have hf_nn : 0 ≤ f (n + j) := f_nonneg (n + j)
    have hf_le : f (n + j) ≤ 1 / ((n + j : ℕ) : ℝ) := f_le_inv (n + j) hpos
    have hnj_le : 1 / ((n + j : ℕ) : ℝ) ≤ 1 / (n : ℝ) := by
      apply one_div_le_one_div_of_le hn_pos
      exact_mod_cast Nat.le_add_right _ _
    have hf_le' : f (n + j) ≤ 1 / (n : ℝ) := le_trans hf_le hnj_le
    exact pow_le_pow_left₀ hf_nn hf_le' 3
  calc ∑ j ∈ Finset.range n, (f (n + j))^3
      ≤ ∑ _j ∈ Finset.range n, (1 / (n : ℝ))^3 := Finset.sum_le_sum hbound
    _ = (n : ℝ) * (1 / (n : ℝ))^3 := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ = 1 / (n : ℝ) ^ 2 := by
        have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
        field_simp

/-- `g n ≥ 0` for all `n`. -/
lemma g_nonneg (n : ℕ) : 0 ≤ g n := by
  unfold g
  apply Finset.sum_nonneg
  intro j _
  exact pow_nonneg (f_nonneg _) 3

/-- `g(n) → 0` as `n → ∞`. -/
lemma g_tendsto_zero : Tendsto g atTop (𝓝 0) := by
  -- Squeeze: 0 ≤ g(n) ≤ 1/n^2 for n ≥ 1, and 1/n^2 → 0.
  have h_inv_tendsto : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    -- Squeeze 1/n^2 between 0 and 1/n
    refine squeeze_zero' ?_ ?_ h1
    · exact Filter.Eventually.of_forall (fun n => by positivity)
    · refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
      intro n hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (n : ℝ)^2 = n * n := by ring
        rw [this]
        nlinarith
      apply one_div_le_one_div_of_le hn_pos hsq
  -- Eventually g n ≤ 1/n^2 (for n ≥ 1), so this works.
  refine squeeze_zero' ?_ ?_ h_inv_tendsto
  · exact Filter.Eventually.of_forall (fun n => g_nonneg n)
  · refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro n hn
    exact g_le n hn

/-- The partial sum `∑_{k=0}^{N-1} a k = (g(1) - g(N+1)) / 3`. -/
lemma partial_sum_eq (N : ℕ) :
    3 * ∑ k ∈ Finset.range N, a k = g 1 - g (N + 1) := by
  induction N with
  | zero => simp [g]
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ N + 1 := by omega
    have hdiff := g_diff (N + 1) h1
    unfold a
    linarith

/-- `g 1 = (log 2)^3`. -/
lemma g_one : g 1 = (Real.log 2)^3 := by
  unfold g f
  rw [Finset.sum_range_one]
  norm_num

/-- The partial sums of `a` converge to `(log 2)^3 / 3`. -/
lemma tendsto_partial_sum :
    Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 ((Real.log 2)^3 / 3)) := by
  have h_eq : ∀ N, ∑ k ∈ Finset.range N, a k = (g 1 - g (N + 1)) / 3 := by
    intro N
    have := partial_sum_eq N
    linarith
  -- partial sum N = (g 1 - g(N+1)) / 3 → (g 1 - 0)/3 = (log 2)^3 / 3
  have h_g_shift : Tendsto (fun N : ℕ => g (N + 1)) atTop (𝓝 0) := by
    have h_shift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun N hN => by omega⟩)
    exact g_tendsto_zero.comp h_shift
  have h_combined : Tendsto (fun N => (g 1 - g (N + 1)) / 3) atTop
      (𝓝 ((g 1 - 0) / 3)) := by
    refine Tendsto.div_const ?_ 3
    exact (tendsto_const_nhds).sub h_g_shift
  rw [show ((Real.log 2)^3 / 3 : ℝ) = (g 1 - 0) / 3 from by rw [g_one]; ring]
  refine h_combined.congr ?_
  intro N
  exact (h_eq N).symm

/-- `a n` is nonnegative. -/
lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  unfold a
  have h1 : 0 ≤ f (n + 1) := f_nonneg _
  have h2 : 0 ≤ f (2 * (n + 1)) := f_nonneg _
  have h3 : 0 ≤ f (2 * (n + 1) + 1) := f_nonneg _
  positivity

/-- The series `∑ a n` is summable. -/
lemma summable_a : Summable a := by
  -- Since partial sums converge and a n ≥ 0, the series is summable.
  -- We use that for nonneg series, summability ↔ partial sums bounded.
  apply summable_of_sum_range_le (f := a) (c := (Real.log 2)^3 / 3) a_nonneg
  intro N
  -- partial sum ≤ limit
  have h_eq : 3 * ∑ k ∈ Finset.range N, a k = g 1 - g (N + 1) := partial_sum_eq N
  have hg_nn : 0 ≤ g (N + 1) := g_nonneg _
  have h1 : 3 * ∑ k ∈ Finset.range N, a k ≤ g 1 := by linarith
  rw [g_one] at h1
  linarith

snip end

/-- The closed-form value of the series. -/
noncomputable determine answer : ℝ := (Real.log 2)^3 / 3

problem imc2011_p8 : HasSum a answer := by
  have hsumm : Summable a := summable_a
  have htend : Tendsto (fun N => ∑ k ∈ Finset.range N, a k) atTop (𝓝 answer) :=
    tendsto_partial_sum
  exact (hsumm.hasSum_iff_tendsto_nat).mpr htend

end Imc2011P8
