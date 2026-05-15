/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 8
(IMC 2001, Day 2, Problem 2)

Let `a_0 = √2` and `a_{n+1} = √(2 - √(4 - a_n^2))`.
Show that the sequence `(a_n)` is (strictly) decreasing and tends to `0`.

The key identity, due to the half-angle formula, is
  `a_n = 2 * sin (π / 2 ^ (n+2))`,
i.e. `a_0 = 2 sin(π/4) = √2`, `a_1 = 2 sin(π/8)`, etc.
From this closed form both claims in part (a) of the original problem follow.
-/

namespace Imc2001P8

open Real

/-- The recursively defined sequence `a_0 = √2`, `a_{n+1} = √(2 - √(4 - a_n^2))`. -/
noncomputable def a : ℕ → ℝ
  | 0 => Real.sqrt 2
  | n + 1 => Real.sqrt (2 - Real.sqrt (4 - (a n) ^ 2))

snip begin

/-- For any `n`, the angle `θ_n := π / 2 ^ (n+2)` lies in `(0, π/4]`. -/
lemma theta_pos (n : ℕ) : 0 < π / 2 ^ (n + 2) :=
  div_pos Real.pi_pos (by positivity)

lemma theta_le (n : ℕ) : π / 2 ^ (n + 2) ≤ π / 4 := by
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) ?_
  calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (n + 2) := by
        apply pow_le_pow_right₀ (by norm_num); omega

lemma theta_lt_pi_div_two (n : ℕ) : π / 2 ^ (n + 2) < π / 2 := by
  have h1 : π / 2 ^ (n + 2) ≤ π / 4 := theta_le n
  have h2 : (π / 4 : ℝ) < π / 2 := by
    have hπ : 0 < π := Real.pi_pos
    linarith
  linarith

lemma theta_lt_pi (n : ℕ) : π / 2 ^ (n + 2) < π := by
  have : π / 2 ^ (n + 2) < π / 2 := theta_lt_pi_div_two n
  have hπ : 0 < π := Real.pi_pos
  linarith

lemma two_sin_theta_nonneg (n : ℕ) : 0 ≤ 2 * Real.sin (π / 2 ^ (n + 2)) := by
  have h1 : 0 ≤ π / 2 ^ (n + 2) := (theta_pos n).le
  have h2 : π / 2 ^ (n + 2) ≤ π := (theta_lt_pi n).le
  have := Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  linarith

lemma cos_theta_pos (n : ℕ) : 0 < Real.cos (π / 2 ^ (n + 2)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hθ : 0 < π / 2 ^ (n + 2) := theta_pos n
    have hπ : 0 < π := Real.pi_pos
    linarith
  · exact theta_lt_pi_div_two n

/-- The closed form: `a n = 2 * sin (π / 2 ^ (n+2))`. -/
lemma a_eq_sin (n : ℕ) : a n = 2 * Real.sin (π / 2 ^ (n + 2)) := by
  induction n with
  | zero =>
    show Real.sqrt 2 = 2 * Real.sin (π / 2 ^ 2)
    have h1 : (π / 2 ^ 2 : ℝ) = π / 4 := by norm_num
    rw [h1, Real.sin_pi_div_four]
    ring
  | succ n ih =>
    show Real.sqrt (2 - Real.sqrt (4 - (a n) ^ 2)) = 2 * Real.sin (π / 2 ^ (n + 1 + 2))
    set θ := π / 2 ^ (n + 2) with hθdef
    have hθpos : 0 < θ := theta_pos n
    have hθlt : θ < π / 2 := theta_lt_pi_div_two n
    have hθlt_pi : θ < π := theta_lt_pi n
    have hcos_pos : 0 < Real.cos θ := cos_theta_pos n
    have hsin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθpos.le hθlt_pi.le
    -- Half-angle.
    have hθ_half : π / 2 ^ (n + 1 + 2) = θ / 2 := by
      rw [hθdef]; field_simp; ring
    rw [ih, hθ_half]
    -- We now have `a n = 2 sin θ`, want:
    --   √(2 - √(4 - (2 sin θ)^2)) = 2 sin(θ/2).
    -- Step 1: (2 sin θ)^2 = 4 sin^2 θ, 4 - 4 sin^2 θ = 4 cos^2 θ.
    have h_inside : (4 : ℝ) - (2 * Real.sin θ) ^ 2 = (2 * Real.cos θ) ^ 2 := by
      have hps : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith
    have h_sqrt1 : Real.sqrt (4 - (2 * Real.sin θ) ^ 2) = 2 * Real.cos θ := by
      rw [h_inside]
      rw [Real.sqrt_sq]
      linarith
    rw [h_sqrt1]
    -- Now we want: √(2 - 2 cos θ) = 2 sin(θ/2).
    -- Use: 2 - 2 cos θ = 4 sin^2(θ/2).
    have h_half_angle : (2 : ℝ) - 2 * Real.cos θ = (2 * Real.sin (θ / 2)) ^ 2 := by
      -- sin^2 (x/2) = (1 - cos x) / 2, i.e. 2 - 2 cos x = (2 sin(x/2))^2.
      have := Real.sin_sq_eq_half_sub (θ / 2)
      -- sin^2 (θ/2) = 1/2 - cos(2 * (θ/2))/2 = 1/2 - cos θ / 2.
      have h2 : 2 * (θ / 2) = θ := by ring
      rw [h2] at this
      -- this : sin(θ/2)^2 = 1/2 - cos θ / 2
      nlinarith [this]
    rw [h_half_angle]
    -- √((2 sin(θ/2))^2) = 2 sin(θ/2) since sin(θ/2) ≥ 0.
    have hθ2_pos : 0 < θ / 2 := by linarith
    have hθ2_lt : θ / 2 < π := by
      have hπ : 0 < π := Real.pi_pos
      linarith
    have hsin_half_nn : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ2_pos.le hθ2_lt.le
    rw [Real.sqrt_sq]
    linarith

/-- The sequence `a` is positive. -/
lemma a_pos (n : ℕ) : 0 < a n := by
  rw [a_eq_sin]
  have h1 : 0 < π / 2 ^ (n + 2) := theta_pos n
  have h2 : π / 2 ^ (n + 2) < π := theta_lt_pi n
  have := Real.sin_pos_of_pos_of_lt_pi h1 h2
  linarith

/-- The sequence `a` is (strictly) decreasing. -/
lemma a_strictAnti (n : ℕ) : a (n + 1) < a n := by
  rw [a_eq_sin, a_eq_sin]
  have h0 : 0 < π / 2 ^ (n + 1 + 2) := theta_pos (n + 1)
  have h1 : π / 2 ^ (n + 1 + 2) < π / 2 ^ (n + 2) := by
    apply div_lt_div_of_pos_left Real.pi_pos
    · positivity
    · apply pow_lt_pow_right₀ (by norm_num); omega
  have h2 : π / 2 ^ (n + 2) ≤ π / 2 := by
    have := theta_lt_pi_div_two n; linarith
  -- sin is strictly increasing on [0, π/2].
  have h3 : Real.sin (π / 2 ^ (n + 1 + 2)) < Real.sin (π / 2 ^ (n + 2)) := by
    apply Real.strictMonoOn_sin
    · refine ⟨?_, ?_⟩
      · have hπ : 0 < π := Real.pi_pos; linarith
      · linarith
    · refine ⟨?_, ?_⟩
      · have hθ := theta_pos n
        have hπ : 0 < π := Real.pi_pos
        linarith
      · linarith
    · exact h1
  linarith

/-- `a n → 0` as `n → ∞`. -/
lemma a_tendsto_zero : Filter.Tendsto a Filter.atTop (nhds 0) := by
  -- Sandwich: 0 ≤ a n = 2 sin θ_n ≤ 2 θ_n → 0.
  have h_upper : ∀ n, a n ≤ 2 * (π / 2 ^ (n + 2)) := by
    intro n
    rw [a_eq_sin]
    have hθ_nn : 0 ≤ π / (2 : ℝ) ^ (n + 2) := (theta_pos n).le
    have hsin_le : Real.sin (π / 2 ^ (n + 2)) ≤ π / 2 ^ (n + 2) := sin_le hθ_nn
    linarith
  have h_lower : ∀ n, 0 ≤ a n := fun n => (a_pos n).le
  -- Show 2 * (π / 2^(n+2)) → 0.
  have h_bound :
      Filter.Tendsto (fun n : ℕ => 2 * (π / (2 : ℝ) ^ (n + 2))) Filter.atTop (nhds 0) := by
    have h_pow : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 2)) Filter.atTop Filter.atTop := by
      have h1 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      exact h1.comp (Filter.tendsto_add_atTop_nat 2)
    have h_inv : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ (n + 2))⁻¹) Filter.atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop h_pow
    have hπ_over :
        Filter.Tendsto (fun n : ℕ => π / (2 : ℝ) ^ (n + 2)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => π * ((2 : ℝ) ^ (n + 2))⁻¹) Filter.atTop
          (nhds (π * 0)) := h_inv.const_mul π
      rw [mul_zero] at h1
      refine h1.congr ?_
      intro n; exact (div_eq_mul_inv _ _).symm
    have := hπ_over.const_mul 2
    rw [mul_zero] at this
    exact this
  exact squeeze_zero h_lower h_upper h_bound

snip end

problem imc2001_p8 :
    (∀ n, a (n + 1) < a n) ∧
    Filter.Tendsto a Filter.atTop (nhds 0) := by
  refine ⟨a_strictAnti, a_tendsto_zero⟩

end Imc2001P8
