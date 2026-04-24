/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 2

Compute the sum of the series
  `∑_{k=0}^∞ 1/((4k+1)(4k+2)(4k+3)(4k+4))`.

The answer is `(log 2) / 4 - π / 24`.
-/

namespace Imc2010P2

open Finset Filter Real Topology

/-- The general term of the series. -/
noncomputable def a (k : ℕ) : ℝ :=
  1 / (((4 * k : ℝ) + 1) * ((4 * k : ℝ) + 2) * ((4 * k : ℝ) + 3) * ((4 * k : ℝ) + 4))

snip begin

/-- Partial fraction decomposition of the general term. -/
lemma a_partial_fraction (k : ℕ) :
    a k = (1/6) * (1 / ((4 * k : ℝ) + 1)) - (1/2) * (1 / ((4 * k : ℝ) + 2))
        + (1/2) * (1 / ((4 * k : ℝ) + 3)) - (1/6) * (1 / ((4 * k : ℝ) + 4)) := by
  unfold a
  have h1 : ((4 : ℝ) * k + 1) ≠ 0 := by positivity
  have h2 : ((4 : ℝ) * k + 2) ≠ 0 := by positivity
  have h3 : ((4 : ℝ) * k + 3) ≠ 0 := by positivity
  have h4 : ((4 : ℝ) * k + 4) ≠ 0 := by positivity
  field_simp
  ring

/-- The alternating harmonic partial sum `H N = ∑_{n<N} (-1)^n/(n+1)`. -/
noncomputable def H (N : ℕ) : ℝ :=
  ∑ n ∈ range N, ((-1 : ℝ) ^ n) / ((n : ℝ) + 1)

/-- The Leibniz partial sum `L J = ∑_{j<J} (-1)^j/(2j+1)`. -/
noncomputable def L (J : ℕ) : ℝ :=
  ∑ j ∈ range J, ((-1 : ℝ) ^ j) / (2 * (j : ℝ) + 1)

/-- Leibniz partial sum tends to π/4. -/
lemma tendsto_L_pi_div_four : Tendsto L atTop (𝓝 (Real.pi / 4)) := by
  have h := Real.tendsto_sum_pi_div_four
  refine h.congr ?_
  intro J
  simp [L]

/-- Alternating harmonic partial sum converges (by alternating series test). -/
lemma tendsto_H_exists : ∃ l : ℝ, Tendsto H atTop (𝓝 l) := by
  set c : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hc_def
  have hc_anti : Antitone c := by
    intro m n hmn
    simp only [c]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
  have hc_tendsto_zero : Tendsto c atTop (𝓝 0) := by
    have hpos : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hinv := hpos.inv_tendsto_atTop
    refine hinv.congr ?_
    intro n; simp [c]
  have hH_tend := Antitone.tendsto_alternating_series_of_tendsto_zero hc_anti hc_tendsto_zero
  obtain ⟨l, hl⟩ := hH_tend
  refine ⟨l, hl.congr ?_⟩
  intro n
  simp only [H, c]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Abel limit of ∑ (-1)^n x^n / (n+1) is log(1+x)/x for 0<x<1. -/
lemma powerSeries_eq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' n : ℕ, ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n = Real.log (1 + x) / x := by
  have habs : |(-x)| < 1 := by rw [abs_neg, abs_of_pos hx0]; exact hx1
  have hsum0 := hasSum_pow_div_log_of_abs_lt_one habs
  -- hsum0 : HasSum (fun n => (-x)^(n+1)/(n+1)) (-log(1-(-x)))
  have h1m : (1 : ℝ) - -x = 1 + x := by ring
  rw [h1m] at hsum0
  -- hsum0 : HasSum (fun n => (-x)^(n+1)/(n+1)) (-log(1+x))
  -- Take negation: HasSum (fun n => -((-x)^(n+1)/(n+1))) (log(1+x))
  have hsum1 := hsum0.neg
  -- Simplify -((-x)^(n+1)/(n+1)) to ((-1)^n * x^(n+1)/(n+1)).
  -- (-x)^(n+1) = (-1)^(n+1) * x^(n+1), so -(-x)^(n+1) = (-1)^n * x^(n+1) * ... actually:
  -- -(-1)^(n+1) = (-1)^n. So -(-x)^(n+1)/(n+1) = (-1)^n * x^(n+1) / (n+1).
  have hsum2 : HasSum (fun n : ℕ => ((-1 : ℝ))^n * x^(n+1) / ((n : ℝ) + 1))
      (- -Real.log (1 + x)) := by
    refine hsum1.congr_fun ?_
    intro n
    have hxpow : ((-x : ℝ)) ^ (n + 1) = (-1 : ℝ)^(n+1) * x^(n+1) := by
      rw [show (-x : ℝ) = -1 * x from by ring, mul_pow]
    rw [hxpow, pow_succ (-1 : ℝ) n]
    ring
  simp only [neg_neg] at hsum2
  -- hsum2 : HasSum (fun n => (-1)^n * x^(n+1) / (n+1)) (log(1+x))
  -- Divide by x.
  have hx_ne : x ≠ 0 := hx0.ne'
  have hsum3 : HasSum (fun n : ℕ => ((-1 : ℝ))^n * x^(n+1) / ((n : ℝ) + 1) / x)
      (Real.log (1 + x) / x) := hsum2.div_const x
  have hsum4 : HasSum (fun n : ℕ => ((-1 : ℝ)) ^ n / ((n : ℝ) + 1) * x ^ n)
      (Real.log (1 + x) / x) := by
    refine hsum3.congr_fun ?_
    intro n
    rw [pow_succ]
    field_simp
  exact hsum4.tsum_eq

/-- Alternating harmonic partial sum converges to `log 2`, via Abel's theorem. -/
lemma tendsto_H_log_two : Tendsto H atTop (𝓝 (Real.log 2)) := by
  obtain ⟨l, hl⟩ := tendsto_H_exists
  -- Apply Abel's theorem.
  have abel : Tendsto (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n)
      (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    have hH : Tendsto (fun N ↦ ∑ i ∈ range N, ((-1 : ℝ) ^ i / ((i : ℝ) + 1))) atTop (𝓝 l) := by
      refine hl.congr ?_
      intro N
      simp [H]
    exact Real.tendsto_tsum_powerSeries_nhdsWithin_lt hH
  -- Match the power series with log(1+x)/x for 0 < x < 1.
  have hps_eq : (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * x ^ n) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun x => Real.log (1 + x) / x) := by
    rw [eventuallyEq_nhdsWithin_iff]
    have hpos : ∀ᶠ y in 𝓝 (1 : ℝ), 0 < y := by
      refine (eventually_gt_nhds ?_)
      norm_num
    filter_upwards [hpos] with x hx0 hx1
    rw [Set.mem_Iio] at hx1
    exact powerSeries_eq x hx0 hx1
  replace abel := abel.congr' hps_eq
  -- Compute limit of log(1+x)/x at 1 from the left.
  have hlim : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2)) := by
    have hlog_lim : Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝 (1 : ℝ)) (𝓝 (Real.log 2)) := by
      have hcts : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 1 := by
        refine ContinuousAt.log ?_ (by norm_num)
        exact (continuous_const.add continuous_id).continuousAt
      have h := hcts.tendsto
      have heq : (1 : ℝ) + 1 = 2 := by norm_num
      rw [heq] at h
      exact h
    have hid_lim : Tendsto (fun x : ℝ => x) (𝓝 (1 : ℝ)) (𝓝 1) := continuous_id.tendsto _
    have hdiv := hlog_lim.div hid_lim one_ne_zero
    rw [div_one] at hdiv
    exact hdiv.mono_left nhdsWithin_le_nhds
  -- Uniqueness of limits.
  have hl_eq : l = Real.log 2 := tendsto_nhds_unique abel hlim
  rw [← hl_eq]; exact hl

/-- `H(2m)` tends to `log 2`. -/
lemma tendsto_H_2m : Tendsto (fun m : ℕ => H (2 * m)) atTop (𝓝 (Real.log 2)) := by
  have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    exact Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun m hm => by omega⟩)
  exact tendsto_H_log_two.comp h2

/-- `H(4m)` tends to `log 2`. -/
lemma tendsto_H_4m : Tendsto (fun m : ℕ => H (4 * m)) atTop (𝓝 (Real.log 2)) := by
  have h : Tendsto (fun m : ℕ => 4 * m) atTop atTop := by
    exact Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun m hm => by omega⟩)
  exact tendsto_H_log_two.comp h

/-- `L(2m)` tends to `π/4`. -/
lemma tendsto_L_2m : Tendsto (fun m : ℕ => L (2 * m)) atTop (𝓝 (Real.pi / 4)) := by
  have h : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    exact Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun m hm => by omega⟩)
  exact tendsto_L_pi_div_four.comp h

/-- Block decomposition: `H(4m) = ∑_{k<m} [1/(4k+1) - 1/(4k+2) + 1/(4k+3) - 1/(4k+4)]`. -/
lemma H_block_sum (m : ℕ) :
    H (4 * m) = ∑ k ∈ range m,
      (1 / ((4 * k : ℝ) + 1) - 1 / ((4 * k : ℝ) + 2)
        + 1 / ((4 * k : ℝ) + 3) - 1 / ((4 * k : ℝ) + 4)) := by
  induction m with
  | zero => simp [H]
  | succ m ih =>
    have hmul : 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 := by ring
    rw [hmul]
    unfold H
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have hp0 : ((-1 : ℝ)) ^ (4 * m) = 1 := by
      rw [show 4 * m = 2 * (2 * m) from by ring, pow_mul]; norm_num
    have hp1 : ((-1 : ℝ)) ^ (4 * m + 1) = -1 := by rw [pow_succ, hp0]; ring
    have hp2 : ((-1 : ℝ)) ^ (4 * m + 1 + 1) = 1 := by rw [pow_succ, hp1]; ring
    have hp3 : ((-1 : ℝ)) ^ (4 * m + 1 + 1 + 1) = -1 := by rw [pow_succ, hp2]; ring
    rw [hp0, hp1, hp2, hp3]
    rw [Finset.sum_range_succ]
    unfold H at ih
    rw [ih]
    push_cast
    ring

/-- Leibniz block decomposition: `L(2m) = ∑_{k<m} [1/(4k+1) - 1/(4k+3)]`. -/
lemma L_block_sum (m : ℕ) :
    L (2 * m) = ∑ k ∈ range m,
      (1 / ((4 * k : ℝ) + 1) - 1 / ((4 * k : ℝ) + 3)) := by
  induction m with
  | zero => simp [L]
  | succ m ih =>
    have heq : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [heq]
    unfold L at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [ih]
    have hparity0 : ((-1 : ℝ) ^ (2 * m)) = 1 := by
      rw [show 2 * m = 2 * m from rfl, pow_mul]; norm_num
    have hparity1 : ((-1 : ℝ) ^ (2 * m + 1)) = -1 := by
      rw [pow_succ, hparity0]; ring
    rw [hparity0, hparity1]
    push_cast
    ring

/-- Half-alternating block: `∑_{k<m} [1/(4k+2) - 1/(4k+4)] = (1/2) * H(2m)`. -/
lemma D_block_sum (m : ℕ) :
    ∑ k ∈ range m, (1 / ((4 * k : ℝ) + 2) - 1 / ((4 * k : ℝ) + 4)) =
      (1/2) * H (2 * m) := by
  induction m with
  | zero => simp [H]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have heq : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [heq]
    unfold H
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hparity0 : ((-1 : ℝ) ^ (2 * m)) = 1 := by rw [pow_mul]; norm_num
    have hparity1 : ((-1 : ℝ) ^ (2 * m + 1)) = -1 := by rw [pow_succ, hparity0]; ring
    rw [hparity0, hparity1]
    unfold H at ih
    push_cast
    field_simp
    ring

/-- Partial sum of our series up to index `m-1`. -/
noncomputable def S (m : ℕ) : ℝ := ∑ k ∈ range m, a k

/-- The partial sum equals a linear combination of `H(4m)`, `L(2m)`, and `(1/2)H(2m)`. -/
lemma S_eq_combination (m : ℕ) :
    S m = (1/3) * H (4 * m) - (1/6) * L (2 * m) - (1/6) * ((1/2) * H (2 * m)) := by
  unfold S
  -- Rewrite the right-hand side using block sums.
  rw [H_block_sum m, L_block_sum m]
  have hD : (1 : ℝ)/2 * H (2 * m) =
      ∑ k ∈ range m, (1 / ((4 * k : ℝ) + 2) - 1 / ((4 * k : ℝ) + 4)) :=
    (D_block_sum m).symm
  rw [hD]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [a_partial_fraction]
  ring

/-- The partial sum tends to the answer. -/
lemma tendsto_S :
    Tendsto S atTop (𝓝 (Real.log 2 / 4 - Real.pi / 24)) := by
  have hcomb : Tendsto (fun m => (1/3) * H (4 * m) - (1/6) * L (2 * m) -
      (1/6) * ((1/2) * H (2 * m))) atTop
      (𝓝 ((1/3) * Real.log 2 - (1/6) * (Real.pi / 4) -
        (1/6) * ((1/2) * Real.log 2))) := by
    refine ((tendsto_H_4m.const_mul (1/3)).sub (tendsto_L_2m.const_mul (1/6))).sub ?_
    exact (tendsto_H_2m.const_mul (1/2)).const_mul (1/6)
  have htarget : (1/3 : ℝ) * Real.log 2 - (1/6) * (Real.pi / 4) -
      (1/6) * ((1/2) * Real.log 2) = Real.log 2 / 4 - Real.pi / 24 := by
    ring
  rw [← htarget]
  refine hcomb.congr ?_
  intro m
  exact (S_eq_combination m).symm

/-- Summability of our series. -/
lemma summable_a : Summable a := by
  -- Bound a k ≤ 1/((k+1)^4 for k ≥ 0.
  have h_bound : ∀ k : ℕ, a k ≤ 1 / (((k : ℝ) + 1) ^ 4) := by
    intro k
    unfold a
    have h1 : (0 : ℝ) < (4 * k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (4 * k : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (4 * k : ℝ) + 3 := by positivity
    have h4 : (0 : ℝ) < (4 * k : ℝ) + 4 := by positivity
    have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    -- (k+1)^4 ≤ (4k+1)(4k+2)(4k+3)(4k+4): Note (4k+1) ≥ k+1 since 4k+1 - (k+1) = 3k ≥ 0.
    -- Similarly all four factors are ≥ (k+1).
    have hk1 : (k + 1 : ℝ) ≤ 4 * k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hk2 : (k + 1 : ℝ) ≤ 4 * k + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hk3 : (k + 1 : ℝ) ≤ 4 * k + 3 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hk4 : (k + 1 : ℝ) ≤ 4 * k + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hprod : ((k : ℝ) + 1)^4 ≤
        ((4 * k : ℝ) + 1) * ((4 * k : ℝ) + 2) * ((4 * k : ℝ) + 3) * ((4 * k : ℝ) + 4) := by
      have step1 : ((k : ℝ) + 1)^2 ≤ ((4 * k : ℝ) + 1) * ((4 * k : ℝ) + 2) := by
        rw [sq]
        exact mul_le_mul hk1 hk2 hk_pos.le (by linarith)
      have step2 : ((k : ℝ) + 1)^2 ≤ ((4 * k : ℝ) + 3) * ((4 * k : ℝ) + 4) := by
        rw [sq]
        exact mul_le_mul hk3 hk4 hk_pos.le (by linarith)
      have : ((k : ℝ) + 1)^4 = ((k : ℝ) + 1)^2 * ((k : ℝ) + 1)^2 := by ring
      rw [this]
      calc ((k : ℝ) + 1)^2 * ((k : ℝ) + 1)^2
          ≤ (((4 * k : ℝ) + 1) * ((4 * k : ℝ) + 2)) * ((k : ℝ) + 1)^2 :=
            mul_le_mul_of_nonneg_right step1 (by positivity)
        _ ≤ (((4 * k : ℝ) + 1) * ((4 * k : ℝ) + 2)) *
            (((4 * k : ℝ) + 3) * ((4 * k : ℝ) + 4)) :=
            mul_le_mul_of_nonneg_left step2 (by positivity)
        _ = ((4 * k : ℝ) + 1) * ((4 * k : ℝ) + 2) * ((4 * k : ℝ) + 3) * ((4 * k : ℝ) + 4) := by
            ring
    apply one_div_le_one_div_of_le (by positivity)
    exact hprod
  have ha_nn : ∀ k, 0 ≤ a k := by
    intro k
    unfold a
    have h1 : (0 : ℝ) < (4 * k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (4 * k : ℝ) + 2 := by positivity
    have h3 : (0 : ℝ) < (4 * k : ℝ) + 3 := by positivity
    have h4 : (0 : ℝ) < (4 * k : ℝ) + 4 := by positivity
    positivity
  -- Summability of 1/(k+1)^4 follows from p-series via a shift.
  have h_sum : Summable (fun k : ℕ => 1 / (((k : ℝ) + 1) ^ 4)) := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
      summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
    have hshift : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ 4)) := by
      have hinj : Function.Injective (fun k : ℕ => k + 1) := fun a b h => Nat.add_right_cancel h
      exact hp.comp_injective hinj
    refine hshift.congr ?_
    intro k
    push_cast
    ring_nf
  exact Summable.of_nonneg_of_le ha_nn h_bound h_sum

snip end

/-- The closed-form value of the series. -/
noncomputable determine answer : ℝ := Real.log 2 / 4 - Real.pi / 24

problem imc2010_p2 : HasSum a answer := by
  have hs : Summable a := summable_a
  have htend : Tendsto S atTop (𝓝 answer) := tendsto_S
  exact (hs.hasSum_iff_tendsto_nat).mpr htend

end Imc2010P2
