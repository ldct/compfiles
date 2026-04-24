/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2019, Problem 1

Evaluate the product
`∏_{n=3}^∞ (n^3 + 3n)^2 / (n^6 - 64)`.

The answer is `72/7`.
-/

namespace Imc2019P1

open Finset Filter

/-- The general term of the product. -/
noncomputable def a (n : ℕ) : ℝ :=
  ((n : ℝ)^3 + 3 * n)^2 / ((n : ℝ)^6 - 64)

snip begin

/-- The closed form of the partial product from `n = 3` to `N` (where `N ≥ 3`). -/
noncomputable def cf (N : ℕ) : ℝ :=
  72 * (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ)^2 + 3) /
    (7 * ((N : ℝ) + 1) * ((N : ℝ) + 2) * (((N : ℝ) + 1)^2 + 3))

/-- Closed form of the partial product from `n = 3` to `N`. -/
lemma partial_product_closed_form (N : ℕ) (hN : 3 ≤ N) :
    ∏ n ∈ Ico 3 (N + 1), a n = cf N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have : Ico 3 (3 + 1) = ({3} : Finset ℕ) := by decide
    rw [this, prod_singleton]
    unfold a cf
    norm_num
  | succ N hN ih =>
    rw [Finset.prod_Ico_succ_top (by omega : 3 ≤ N + 1), ih]
    unfold a cf
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN_pos : (0 : ℝ) < N := by linarith
    have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'
    have hNm1 : ((N : ℝ) - 1) ≠ 0 := by linarith
    have hNp1 : ((N : ℝ) + 1) ≠ 0 := by linarith
    have hNp2 : ((N : ℝ) + 2) ≠ 0 := by linarith
    have hNp3 : ((N : ℝ) + 3) ≠ 0 := by linarith
    have hsq_N : ((N : ℝ)^2 + 3) ≠ 0 := by positivity
    have hsq_Np1 : (((N : ℝ) + 1)^2 + 3) ≠ 0 := by positivity
    have hsq_Np2 : (((N : ℝ) + 2)^2 + 3) ≠ 0 := by positivity
    -- (N+1)^6 - 64 = (N-1)(N+3) * ((N+1)^2 + 3)^2 - well, factor properly:
    -- (N+1)^6 - 64 = ((N+1)^3 - 8)((N+1)^3 + 8)
    --             = ((N+1)-2)((N+1)^2+2(N+1)+4) * ((N+1)+2)((N+1)^2-2(N+1)+4)
    --             = (N-1)(N+3) * ((N+1)^2+2N+6) * ((N+1)^2-2N-1)... let me use explicit:
    -- (N+1)^2 + 2(N+1) + 4 = N^2 + 4N + 7 = (N+2)^2 + 3
    -- (N+1)^2 - 2(N+1) + 4 = N^2 + 3
    have h_denom_ne : (((N : ℝ) + 1)^6 - 64) ≠ 0 := by
      have expand :
          (((N : ℝ) + 1)^6 - 64) = ((N : ℝ) - 1) * ((N : ℝ) + 3) *
            (((N : ℝ) + 2)^2 + 3) * ((N : ℝ)^2 + 3) := by ring
      rw [expand]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hNm1 hNp3) hsq_Np2) hsq_N
    push_cast
    field_simp
    ring

/-- Step 1: the partial product equals its closed form eventually. -/
lemma partial_product_eq_cf :
    ∀ᶠ N in atTop, ∏ n ∈ Ico 3 (N + 1), a n = cf N := by
  filter_upwards [Filter.eventually_ge_atTop 3] with N hN
  exact partial_product_closed_form N hN

/-- The closed form tends to `72/7`. -/
lemma tendsto_cf : Tendsto (fun N : ℕ => cf N) atTop (nhds (72 / 7 : ℝ)) := by
  -- cf N = (72/7) * [N(N-1)(N^2+3)] / [(N+1)(N+2)((N+1)^2+3)]
  -- The inner ratio tends to 1.
  have htends_inv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htends_inv2 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ)^2)) atTop (nhds 0) := by
    have := htends_inv.mul htends_inv
    simpa [div_mul_div_comm, sq] using this
  -- numerator (divided by N^4): (1 - 1/N)(1 + 3/N^2) → 1
  have hc1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  have hc3 : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) := tendsto_const_nhds
  have hnum : Tendsto (fun N : ℕ =>
      (1 - 1 / (N : ℝ)) * (1 + 3 * (1 / ((N : ℝ)^2)))) atTop (nhds 1) := by
    have h := (hc1.sub htends_inv).mul (hc1.add (hc3.mul htends_inv2))
    simpa using h
  -- denominator (divided by N^4): (1 + 1/N)(1 + 2/N)((1 + 1/N)^2 + 3/N^2) → 1
  have hden : Tendsto (fun N : ℕ =>
      ((1 : ℝ) + 1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) *
        ((1 + 1 / (N : ℝ))^2 + 3 * (1 / ((N : ℝ)^2)))) atTop (nhds 1) := by
    have hfac1 : Tendsto (fun N : ℕ => ((1 : ℝ) + 1 / (N : ℝ))) atTop (nhds 1) := by
      simpa using hc1.add htends_inv
    have hfac2 : Tendsto (fun N : ℕ => ((1 : ℝ) + 2 * (1 / (N : ℝ)))) atTop (nhds 1) := by
      simpa using hc1.add (hc2.mul htends_inv)
    have hfac3 : Tendsto (fun N : ℕ =>
        (((1 : ℝ) + 1 / (N : ℝ))^2 + 3 * (1 / ((N : ℝ)^2)))) atTop (nhds 1) := by
      have h := (hfac1.pow 2).add (hc3.mul htends_inv2)
      simpa using h
    have := (hfac1.mul hfac2).mul hfac3
    simpa using this
  have hden_ne : (1 : ℝ) ≠ 0 := one_ne_zero
  have hratio := hnum.div hden hden_ne
  have h_ratio_target : (1 : ℝ) / 1 = 1 := by norm_num
  rw [h_ratio_target] at hratio
  -- Now cf N = (72/7) * ratio for N ≥ 2 (to avoid division by zero).
  have h_const : Tendsto (fun N : ℕ => (72 / 7 : ℝ) *
      ((1 - 1 / (N : ℝ)) * (1 + 3 * (1 / ((N : ℝ)^2))) /
        (((1 : ℝ) + 1 / (N : ℝ)) * (1 + 2 * (1 / (N : ℝ))) *
          ((1 + 1 / (N : ℝ))^2 + 3 * (1 / ((N : ℝ)^2))))))
      atTop (nhds ((72 / 7 : ℝ) * 1)) :=
    hratio.const_mul (72 / 7 : ℝ)
  rw [mul_one] at h_const
  refine h_const.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  unfold cf
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'
  have hN2_ne : ((N : ℝ)^2) ≠ 0 := pow_ne_zero _ hN_ne
  have hNp1 : ((N : ℝ) + 1) ≠ 0 := by linarith
  have hNp2 : ((N : ℝ) + 2) ≠ 0 := by linarith
  have hsqNp1 : (((N : ℝ) + 1)^2 + 3) ≠ 0 := by positivity
  field_simp

/-- The partial product tends to `72/7` as `N → ∞`. -/
lemma tendsto_partial_product :
    Tendsto (fun N : ℕ => ∏ n ∈ Ico 3 (N + 1), a n) atTop (nhds (72 / 7 : ℝ)) := by
  refine Tendsto.congr' (partial_product_eq_cf.mono ?_) tendsto_cf
  intro N hN
  exact hN.symm

snip end

/-- The value of the infinite product. -/
noncomputable determine answer : ℝ := 72 / 7

problem imc2019_p1 :
    Tendsto (fun N : ℕ => ∏ n ∈ Ico 3 (N + 1), a n) atTop (nhds answer) :=
  tendsto_partial_product

end Imc2019P1
