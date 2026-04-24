/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 3

Let `S_n` be the set of real numbers of the form `x_1 + ... + x_n`, where
`0 ≤ x_k ≤ π/2` and `sin(x_1) + ... + sin(x_n) = 1`.

(a) Show that `S_n` is an interval.
(b) Find the limit of the length of `S_n` as `n → ∞`.

The answer to (b) is `π/2 - 1`.
-/

namespace Imc2004P3

open Real
open scoped BigOperators Topology

/-- The set `S_n` of achievable sums `∑ x_i` under the constraints. -/
def Sn (n : ℕ) : Set ℝ :=
  { s | ∃ x : Fin n → ℝ,
      (∀ i, 0 ≤ x i ∧ x i ≤ π / 2) ∧ (∑ i, sin (x i)) = 1 ∧ (∑ i, x i) = s }

snip begin

/-- Upper bound: every element of `S_n` is at most `π/2`. Uses `sin x ≥ (2/π) * x`. -/
lemma sum_le_pi_div_two {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ π / 2) (hsum : (∑ i, sin (x i)) = 1) :
    (∑ i, x i) ≤ π / 2 := by
  -- From sin x ≥ (2/π) x on [0, π/2]: x ≤ (π/2) sin x, sum and use hsum.
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 / π := by positivity
  have hstep : ∀ i, x i ≤ (π / 2) * sin (x i) := by
    intro i
    have hi := hx i
    have h := Real.mul_le_sin hi.1 hi.2
    -- 2/π * x i ≤ sin (x i), so x i ≤ (π/2) sin (x i)
    have hpi2pos : (0 : ℝ) < π / 2 := by positivity
    have hid : x i = (π / 2) * ((2 / π) * x i) := by field_simp
    have key : (π / 2) * ((2 / π) * x i) ≤ (π / 2) * sin (x i) :=
      mul_le_mul_of_nonneg_left h hpi2pos.le
    linarith
  calc (∑ i, x i) ≤ ∑ i, (π / 2) * sin (x i) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = (π / 2) * ∑ i, sin (x i) := by rw [← Finset.mul_sum]
    _ = (π / 2) * 1 := by rw [hsum]
    _ = π / 2 := by ring

/-- Lower bound: every element of `S_n` is at least `n * arcsin(1/n)` (for `n ≥ 1`).
Uses concavity of `sin` on `[0, π]` via Jensen. -/
lemma sum_ge_n_arcsin {n : ℕ} (hn : 1 ≤ n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ π / 2) (hsum : (∑ i, sin (x i)) = 1) :
    (n : ℝ) * arcsin (1 / n) ≤ (∑ i, x i) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_div_two_pos : (0 : ℝ) < π / 2 := by positivity
  -- The points x i all lie in Icc 0 π (since π/2 ≤ π).
  have hxIcc : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ Set.Icc (0 : ℝ) π := by
    intro i _
    refine ⟨(hx i).1, ?_⟩
    linarith [(hx i).2]
  -- Weights w_i = 1/n, sum to 1.
  set w : Fin n → ℝ := fun _ => (1 : ℝ) / n
  have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ w i := by
    intro i _; dsimp [w]; positivity
  have hw_sum : (∑ i, w i) = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  -- Jensen for concave: ∑ w i * sin (x i) ≤ sin (∑ w i * x i)
  have hjensen := (strictConcaveOn_sin_Icc.concaveOn).le_map_sum
      hw_nn hw_sum hxIcc
  simp only [smul_eq_mul, w] at hjensen
  -- ∑ (1/n) * sin x i ≤ sin (∑ (1/n) * x i)
  -- i.e., (1/n) * ∑ sin x i ≤ sin ((1/n) * ∑ x i)
  have hlhs : (∑ i, 1 / (n : ℝ) * sin (x i)) = 1 / n := by
    rw [← Finset.mul_sum, hsum, mul_one]
  have hrhs : (∑ i, 1 / (n : ℝ) * x i) = 1 / n * ∑ i, x i := by
    rw [Finset.mul_sum]
  rw [hlhs, hrhs] at hjensen
  -- Now: 1/n ≤ sin ((1/n) * ∑ x i)
  set S := ∑ i, x i with hS_def
  -- We have 0 ≤ (1/n) * S, and (1/n) * S ≤ π/2 from upper bound.
  have hS_upper : S ≤ π / 2 := sum_le_pi_div_two hx hsum
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hx i).1)
  have hmean_nonneg : 0 ≤ 1 / (n : ℝ) * S := by positivity
  have hmean_le : 1 / (n : ℝ) * S ≤ π / 2 := by
    have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hinv_le : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn_pos]; exact hn_ge
    calc 1 / (n : ℝ) * S ≤ 1 * S := by
          apply mul_le_mul_of_nonneg_right hinv_le hS_nonneg
      _ = S := one_mul _
      _ ≤ π / 2 := hS_upper
  -- Since 1/n ≤ sin(m) where m = (1/n)*S ∈ [0, π/2], and sin is monotone there,
  -- we have arcsin(1/n) ≤ m.
  have h_1n_mem : (1 : ℝ) / n ∈ Set.Icc (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ 1 / n := by positivity
      linarith
    · rw [div_le_one hn_pos]; exact_mod_cast hn
  have hmean_mem : 1 / (n : ℝ) * S ∈ Set.Icc (-(π / 2)) (π / 2) :=
    ⟨by linarith, hmean_le⟩
  have harcsin_le : arcsin (1 / n) ≤ 1 / (n : ℝ) * S := by
    rw [Real.arcsin_le_iff_le_sin h_1n_mem hmean_mem]
    exact hjensen
  -- Multiply by n.
  have hmul : (n : ℝ) * arcsin (1 / n) ≤ (n : ℝ) * (1 / n * S) :=
    mul_le_mul_of_nonneg_left harcsin_le hn_pos.le
  have hsimpl : (n : ℝ) * (1 / n * S) = S := by
    field_simp
  rw [hsimpl] at hmul
  exact hmul

/-- A path in the constraint set, parameterized by `t ∈ [0, 1]`.
`γ(0)` gives sum `n arcsin(1/n)` and `γ(1)` gives sum `π/2`. -/
noncomputable def pathX (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : Fin n → ℝ := fun i =>
  if i = ⟨0, hn⟩ then arcsin ((1 - t) / n + t) else arcsin ((1 - t) / n)

/-- The sum-of-sines along the path equals 1 for all `t ∈ [0, 1]`. -/
lemma pathX_sum_sin (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, sin (pathX n hn t i)) = 1 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  -- (1-t)/n ∈ [0,1] and (1-t)/n + t ∈ [0,1]
  have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
  have ht1 : (1 - t) ≤ 1 := by linarith [ht.1]
  have htm : 0 ≤ (1 - t) / n ∧ (1 - t) / n ≤ 1 := by
    refine ⟨div_nonneg ht0 hn_pos.le, ?_⟩
    have hle : (1 - t) / n ≤ 1 / n :=
      div_le_div_of_nonneg_right ht1 hn_pos.le
    have : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hn_pos]; exact_mod_cast hn
    linarith
  have htmt : 0 ≤ (1 - t) / n + t ∧ (1 - t) / n + t ≤ 1 := by
    refine ⟨by linarith [htm.1, ht.1], ?_⟩
    -- (1-t)/n + t ≤ 1: equivalent to (1-t)/n ≤ 1-t
    have h1mt : 0 ≤ 1 - t := by linarith [ht.2]
    have hp : (1 - t) / n ≤ 1 - t := by
      have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rcases eq_or_lt_of_le h1mt with heq | hlt
      · rw [← heq]; simp
      · have := div_le_self hlt.le hn_ge
        exact this
    linarith
  have h1 : (-1 : ℝ) ≤ (1 - t) / n + t := by linarith [htmt.1]
  have h2 : (-1 : ℝ) ≤ (1 - t) / n := by linarith [htm.1]
  -- Now compute the sum.
  have key : (∑ i : Fin n, sin (pathX n hn t i))
           = sin (arcsin ((1 - t) / n + t)) +
             ((n : ℝ) - 1) * sin (arcsin ((1 - t) / n)) := by
    -- split off i = ⟨0, hn⟩
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
    have h_rest : (∑ i ∈ Finset.univ.erase (⟨0, hn⟩ : Fin n), sin (pathX n hn t i))
                = ((n : ℝ) - 1) * sin (arcsin ((1 - t) / n)) := by
      have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase (⟨0, hn⟩ : Fin n),
          sin (pathX n hn t i) = sin (arcsin ((1 - t) / n)) := by
        intro i hi
        rw [Finset.mem_erase] at hi
        unfold pathX
        rw [if_neg hi.1]
      rw [Finset.sum_congr rfl h1, Finset.sum_const]
      have hcard : (Finset.univ.erase (⟨0, hn⟩ : Fin n)).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      rw [hcard, nsmul_eq_mul]
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have heq : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel hn
        have : (((n - 1 : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast heq
        push_cast at this
        linarith
      rw [hcast]
    have h_at0 : sin (pathX n hn t (⟨0, hn⟩ : Fin n)) = sin (arcsin ((1 - t) / n + t)) := by
      unfold pathX; simp
    rw [h_rest, h_at0, add_comm]
  rw [key]
  rw [Real.sin_arcsin h1 htmt.2, Real.sin_arcsin h2 htm.2]
  field_simp
  ring

/-- The sum along the path is continuous in `t`. -/
lemma pathX_sum_continuous (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun t => ∑ i, pathX n hn t i) := by
  unfold pathX
  apply continuous_finset_sum
  intro i _
  by_cases h : i = ⟨0, hn⟩
  · simp only [h, ↓reduceIte]
    exact Real.continuous_arcsin.comp
      ((continuous_const.sub continuous_id).div_const _ |>.add continuous_id)
  · simp only [h, ↓reduceIte]
    exact Real.continuous_arcsin.comp
      ((continuous_const.sub continuous_id).div_const _)

/-- At `t = 0`, the sum equals `n * arcsin(1/n)`. -/
lemma pathX_sum_at_zero (n : ℕ) (hn : 1 ≤ n) :
    (∑ i, pathX n hn 0 i) = (n : ℝ) * arcsin (1 / n) := by
  unfold pathX
  have : ∀ i : Fin n, (if i = ⟨0, hn⟩ then arcsin ((1 - (0:ℝ)) / n + 0) else arcsin ((1 - 0) / n))
           = arcsin (1 / n) := by
    intro i; split_ifs <;> { simp }
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- At `t = 1`, the sum equals `π/2`. -/
lemma pathX_sum_at_one (n : ℕ) (hn : 1 ≤ n) :
    (∑ i, pathX n hn 1 i) = π / 2 := by
  have h_at0 : pathX n hn 1 (⟨0, hn⟩ : Fin n) = π / 2 := by
    unfold pathX; simp [Real.arcsin_one]
  have h_rest : ∀ i ∈ (Finset.univ : Finset (Fin n)).erase (⟨0, hn⟩ : Fin n),
      pathX n hn 1 i = 0 := by
    intro i hi
    rw [Finset.mem_erase] at hi
    unfold pathX
    rw [if_neg hi.1]
    simp [Real.arcsin_zero]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
  rw [Finset.sum_congr rfl h_rest, Finset.sum_const, smul_zero, zero_add, h_at0]

/-- The path `pathX n hn t` satisfies the box constraint `x_i ∈ [0, π/2]`. -/
lemma pathX_mem_box (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) : 0 ≤ pathX n hn t i ∧ pathX n hn t i ≤ π / 2 := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
  have ht1 : (1 - t) ≤ 1 := by linarith [ht.1]
  have htm : 0 ≤ (1 - t) / n := div_nonneg ht0 hn_pos.le
  have htmt : 0 ≤ (1 - t) / n + t := by linarith [htm, ht.1]
  unfold pathX
  split_ifs with h
  · refine ⟨Real.arcsin_nonneg.mpr htmt, Real.arcsin_le_pi_div_two _⟩
  · refine ⟨Real.arcsin_nonneg.mpr htm, Real.arcsin_le_pi_div_two _⟩

/-- Main lemma: every value in `Icc (n * arcsin (1/n)) (π/2)` is attained. -/
lemma Icc_subset_Sn {n : ℕ} (hn : 1 ≤ n) :
    Set.Icc ((n : ℝ) * arcsin (1 / n)) (π / 2) ⊆ Sn n := by
  intro s hs
  -- Use IVT on the continuous sum function.
  set f := fun t : ℝ => ∑ i, pathX n hn t i
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (pathX_sum_continuous n hn).continuousOn
  have hf0 : f 0 = (n : ℝ) * arcsin (1 / n) := pathX_sum_at_zero n hn
  have hf1 : f 1 = π / 2 := pathX_sum_at_one n hn
  have hs_mem : s ∈ Set.Icc (f 0) (f 1) := by rw [hf0, hf1]; exact hs
  -- Apply IVT.
  have hzo : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hzo hf_cont hs_mem
  refine ⟨pathX n hn t, ?_, ?_, hft⟩
  · intro i; exact pathX_mem_box n hn ht i
  · exact pathX_sum_sin n hn ht

/-- The set `S_n` equals the closed interval `[n · arcsin(1/n), π/2]`. -/
lemma Sn_eq_Icc {n : ℕ} (hn : 1 ≤ n) :
    Sn n = Set.Icc ((n : ℝ) * arcsin (1 / n)) (π / 2) := by
  apply Set.Subset.antisymm
  · rintro s ⟨x, hx, hsum, hs⟩
    refine ⟨?_, ?_⟩
    · rw [← hs]; exact sum_ge_n_arcsin hn hx hsum
    · rw [← hs]; exact sum_le_pi_div_two hx hsum
  · exact Icc_subset_Sn hn

/-- `n * arcsin(1/n) → 1` as `n → ∞`. -/
lemma tendsto_n_arcsin_inv :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * arcsin (1 / n)) Filter.atTop (𝓝 1) := by
  -- Strategy: let y_n = arcsin(1/n). Then y_n → 0 and sin y_n = 1/n.
  -- n * y_n = y_n / (1/n) = y_n / sin y_n = 1 / sinc y_n → 1 / sinc 0 = 1.
  -- Step 1: arcsin(1/n) → 0 as n → ∞.
  have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have harcsin_tendsto :
      Filter.Tendsto (fun n : ℕ => arcsin (1 / n)) Filter.atTop (𝓝 0) := by
    have := (Real.continuous_arcsin.tendsto 0).comp h1
    simpa [Real.arcsin_zero] using this
  -- Step 2: sinc (arcsin(1/n)) → 1.
  have hsinc_tendsto :
      Filter.Tendsto (fun n : ℕ => Real.sinc (arcsin (1 / n))) Filter.atTop (𝓝 1) := by
    have := (Real.continuous_sinc.tendsto 0).comp harcsin_tendsto
    simpa [Real.sinc_zero] using this
  -- Step 3: for n large (n ≥ 2), arcsin(1/n) > 0, so sinc = sin(arcsin(1/n))/arcsin(1/n)
  -- = (1/n)/arcsin(1/n). So n * arcsin(1/n) = 1/sinc(arcsin(1/n)).
  have heventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) * arcsin (1 / n) = 1 / Real.sinc (arcsin (1 / n)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 1 ≤ n)
    have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have h_1n_pos : (0 : ℝ) < 1 / n := by positivity
    have h_1n_lt1 : (1 : ℝ) / n < 1 := by
      rw [div_lt_one hn_pos]; exact hn_gt1
    have harcsin_pos : 0 < arcsin (1 / n) := Real.arcsin_pos.mpr h_1n_pos
    have harcsin_ne : arcsin (1 / n) ≠ 0 := harcsin_pos.ne'
    have hsin_eq : sin (arcsin (1 / n)) = 1 / n := by
      apply Real.sin_arcsin <;> linarith
    rw [Real.sinc_of_ne_zero harcsin_ne, hsin_eq]
    field_simp
  -- Use tendsto_congr'.
  have hfinal : Filter.Tendsto (fun n : ℕ => 1 / Real.sinc (arcsin (1 / n)))
      Filter.atTop (𝓝 1) := by
    have h := Filter.Tendsto.div (tendsto_const_nhds (x := (1 : ℝ))) hsinc_tendsto one_ne_zero
    have heq : (1 : ℝ) / 1 = 1 := by norm_num
    convert h using 2
    exact heq.symm
  exact (Filter.tendsto_congr' heventually).mpr hfinal

snip end

/-- The answer: the length of `S_n` tends to `π/2 - 1`. -/
noncomputable determine answerB : ℝ := π / 2 - 1

/-- The length of the interval `S_n`, defined as `sSup - sInf`. -/
noncomputable def length (n : ℕ) : ℝ := sSup (Sn n) - sInf (Sn n)

problem imc2004_p3 :
    -- Part (a): for each n ≥ 1, S_n is a closed interval.
    (∀ n : ℕ, 1 ≤ n → ∃ a b : ℝ, Sn n = Set.Icc a b) ∧
    -- Part (b): the length of S_n tends to π/2 - 1.
    Filter.Tendsto (fun n : ℕ => length n) Filter.atTop (𝓝 answerB) := by
  refine ⟨?_, ?_⟩
  · -- Part (a): follows immediately from Sn_eq_Icc.
    intro n hn
    exact ⟨(n : ℝ) * arcsin (1 / n), π / 2, Sn_eq_Icc hn⟩
  · -- Part (b).
    -- For n ≥ 1, length n = π/2 - n * arcsin(1/n).
    -- We need length n → π/2 - 1.
    have heventually :
        ∀ᶠ n : ℕ in Filter.atTop,
          length n = π / 2 - (n : ℝ) * arcsin (1 / n) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      unfold length
      rw [Sn_eq_Icc hn]
      -- For n=1: n * arcsin(1/n) = arcsin(1) = π/2, so interval is [π/2, π/2], empty?
      -- No, it's {π/2}, nondegenerate non-issue.
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hn_ge : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h_1n_nn : (0 : ℝ) ≤ 1 / n := by positivity
      have h_1n_le1 : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hn_pos]; exact hn_ge
      have harcsin_pos_or_zero : 0 ≤ arcsin (1 / n) := Real.arcsin_nonneg.mpr h_1n_nn
      have harcsin_le : arcsin (1 / n) ≤ π / 2 := Real.arcsin_le_pi_div_two _
      -- Use: arcsin(1/n) ≤ (π/2)(1/n), so n*arcsin(1/n) ≤ π/2.
      have hbetter : (n : ℝ) * arcsin (1 / n) ≤ π / 2 := by
        -- Use: 2/π * arcsin(1/n) ≤ sin(arcsin(1/n)) = 1/n
        -- So arcsin(1/n) ≤ (π/2) * (1/n), so n * arcsin(1/n) ≤ π/2.
        have hmem : arcsin (1 / n) ∈ Set.Icc (0 : ℝ) (π / 2) :=
          ⟨harcsin_pos_or_zero, harcsin_le⟩
        have := Real.mul_le_sin hmem.1 hmem.2
        rw [Real.sin_arcsin (by linarith) h_1n_le1] at this
        -- 2/π * arcsin(1/n) ≤ 1/n
        have hpi_pos : (0 : ℝ) < π := Real.pi_pos
        -- Multiply both sides by n*π/2:
        have harcsin_le_pi2_over_n : arcsin (1 / n) ≤ π / (2 * n) := by
          have h2π : (0 : ℝ) < 2 / π := by positivity
          have := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ π / 2 by positivity)
          have hcalc : (π / 2) * (2 / π * arcsin (1 / n)) = arcsin (1 / n) := by
            field_simp
          rw [hcalc] at this
          have hcalc2 : (π / 2) * (1 / n) = π / (2 * n) := by ring
          rw [hcalc2] at this
          exact this
        calc (n : ℝ) * arcsin (1 / n)
            ≤ (n : ℝ) * (π / (2 * n)) := by
              apply mul_le_mul_of_nonneg_left harcsin_le_pi2_over_n hn_pos.le
          _ = π / 2 := by field_simp
      rw [csSup_Icc hbetter, csInf_Icc hbetter]
    rw [Filter.tendsto_congr' heventually]
    -- Want: π/2 - n arcsin(1/n) → π/2 - 1.
    show Filter.Tendsto (fun n : ℕ => π / 2 - (n : ℝ) * arcsin (1 / n))
      Filter.atTop (𝓝 (π / 2 - 1))
    exact (tendsto_const_nhds.sub tendsto_n_arcsin_inv)

end Imc2004P3
