/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 9

Define the sequence `f₁, f₂, … : [0,1) → ℝ` of continuously differentiable functions by
`f₁ = 1`, `f'_{n+1} = f_n f_{n+1}` on `(0,1)`, `f_{n+1}(0) = 1`.

Show that `lim_{n→∞} fₙ(x)` exists for every `x ∈ [0,1)` and determine the limit function.

The answer is `1/(1-x)`.

We model the problem by interpreting "continuously differentiable function on `[0,1)`
satisfying the ODE" via the integral form `f_{n+1}(x) = exp(∫₀^x f_n)`, which is
equivalent for a continuously differentiable solution `f_{n+1}` of `g' = f_n g`,
`g(0) = 1`. Concretely we hypothesise a sequence `f : ℕ → ℝ → ℝ` (with `f 0`
corresponding to `f₁`) such that each `f n` is continuous and
`f (n+1) x = Real.exp (∫ t in 0..x, f n t)` and `f 0 = 1`.

The conclusion (the actual problem) is that `Tendsto (fun n => f n x) atTop (𝓝 (1/(1-x)))`.
-/

namespace Imc2017P9

open Filter Topology MeasureTheory intervalIntegral

/-- The limit function `1/(1 - x)`. -/
noncomputable determine answer : ℝ → ℝ := fun x => 1 / (1 - x)

snip begin

/-- The "Picard" operator `Φ(g)(x) = exp(∫₀^x g)`. -/
noncomputable def Φ (g : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (∫ t in (0:ℝ)..x, g t)

/-- The integral `∫₀^x 1/(1-t) dt = -log(1-x)` for `x < 1`. -/
lemma integral_one_div_one_sub {x : ℝ} (hx : x < 1) :
    ∫ t in (0:ℝ)..x, 1 / (1 - t) = -Real.log (1 - x) := by
  have hderiv : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (fun s => -Real.log (1 - s))
      (1 / (1 - t)) t := by
    intro t ht
    have ht_lt : (0:ℝ) < 1 - t := by
      have htle : t < 1 := by
        rcases le_total 0 x with hx0 | hx0
        · have : t ≤ x := by rw [Set.uIcc_of_le hx0] at ht; exact ht.2
          linarith
        · have : t ≤ 0 := by rw [Set.uIcc_of_ge hx0] at ht; exact ht.2
          linarith
      linarith
    have h1 : HasDerivAt (fun s => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h2 : HasDerivAt (fun s => Real.log (1 - s)) (-1 / (1 - t)) t :=
      h1.log ht_lt.ne'
    have h3 := h2.neg
    convert h3 using 1
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => 1 / (1 - t)) (Set.uIcc 0 x) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    have htlt : t < 1 := by
      rcases le_total 0 x with hx0 | hx0
      · have : t ≤ x := by rw [Set.uIcc_of_le hx0] at ht; exact ht.2
        linarith
      · have : t ≤ 0 := by rw [Set.uIcc_of_ge hx0] at ht; exact ht.2
        linarith
    intro h
    apply absurd h
    intro h
    linarith
  have hint := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [sub_zero, Real.log_one] at hint
  rw [hint]
  ring

/-- The fixed point: `Φ(1/(1-·)) = 1/(1-·)` on `[0, 1)`. -/
lemma Φ_fixedPoint {x : ℝ} (hx : x < 1) :
    Φ (fun t => 1 / (1 - t)) x = 1 / (1 - x) := by
  unfold Φ
  rw [integral_one_div_one_sub hx]
  rw [Real.exp_neg, Real.exp_log (by linarith : (0:ℝ) < 1 - x)]
  rw [one_div]

variable (f : ℕ → ℝ → ℝ)
  (hf_cont : ∀ n, Continuous (f n))
  (hf_zero : f 0 = fun _ => 1)
  (hf_rec : ∀ n x, f (n+1) x = Real.exp (∫ t in (0:ℝ)..x, f n t))

include hf_zero hf_rec in
/-- Lower bound: `f n x ≥ 1` for `x ≥ 0`. -/
lemma f_ge_one (n : ℕ) : ∀ x, 0 ≤ x → 1 ≤ f n x := by
  induction n with
  | zero => intro x _; rw [hf_zero]
  | succ n ih =>
      intro x hx
      rw [hf_rec]
      have hint_nn : 0 ≤ ∫ t in (0:ℝ)..x, f n t := by
        apply intervalIntegral.integral_nonneg hx
        intro t ht
        linarith [ih t ht.1]
      calc (1:ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp (∫ t in (0:ℝ)..x, f n t) := Real.exp_le_exp.mpr hint_nn

include hf_cont hf_zero hf_rec in
/-- Upper bound: `f n x ≤ 1/(1-x)` for `x ∈ [0,1)`. -/
lemma f_le_inv : ∀ n x, 0 ≤ x → x < 1 → f n x ≤ 1 / (1 - x) := by
  intro n
  induction n with
  | zero =>
      intro x _ hx1
      rw [hf_zero]
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - x)]
      linarith
  | succ n ih =>
      intro x hx hx1
      rw [hf_rec]
      have h1 : (∫ t in (0:ℝ)..x, f n t) ≤ ∫ t in (0:ℝ)..x, 1 / (1 - t) := by
        apply intervalIntegral.integral_mono_on hx
        · exact (hf_cont n).intervalIntegrable 0 x
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const (by fun_prop)
          intro t ht
          have : t ≤ x := by rw [Set.uIcc_of_le hx] at ht; exact ht.2
          intro h; linarith
        · intro t ht
          exact ih t ht.1 (by linarith [ht.2])
      have h2 : (∫ t in (0:ℝ)..x, 1 / (1 - t)) = -Real.log (1 - x) :=
        integral_one_div_one_sub hx1
      have h3 : Real.exp (∫ t in (0:ℝ)..x, f n t) ≤ Real.exp (-Real.log (1 - x)) := by
        rw [← h2]; exact Real.exp_le_exp.mpr h1
      have h4 : Real.exp (-Real.log (1 - x)) = 1 / (1 - x) := by
        rw [Real.exp_neg, Real.exp_log (by linarith : (0:ℝ) < 1 - x), one_div]
      linarith

include hf_cont hf_zero hf_rec in
/-- Monotonicity: `f n x ≤ f (n+1) x` for `x ≥ 0`. -/
lemma f_mono_step : ∀ n x, 0 ≤ x → f n x ≤ f (n+1) x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      rw [hf_zero, hf_rec]
      have hint : (∫ t in (0:ℝ)..x, (fun _ => (1:ℝ)) t) = x := by simp
      rw [show (f 0) = (fun _ => (1:ℝ)) from hf_zero, hint]
      have : (1:ℝ) ≤ Real.exp x := by
        calc (1:ℝ) = Real.exp 0 := by rw [Real.exp_zero]
          _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
      exact this
  | succ n ih =>
      intro x hx
      rw [hf_rec (n+1), hf_rec n]
      have h_int_le : (∫ t in (0:ℝ)..x, f n t) ≤ ∫ t in (0:ℝ)..x, f (n+1) t := by
        apply intervalIntegral.integral_mono_on hx
        · exact (hf_cont n).intervalIntegrable 0 x
        · exact (hf_cont (n+1)).intervalIntegrable 0 x
        · intro t ht
          exact ih t ht.1
      exact Real.exp_le_exp.mpr h_int_le

snip end

/-- Statement of IMC 2017 P9. We hypothesise a sequence of continuous functions
on `ℝ` (whose restriction to `[0,1)` corresponds to the problem's sequence)
satisfying `f 0 = 1` and the integral form `f (n+1) x = exp(∫₀^x f n)`. -/
problem imc2017_p9 (f : ℕ → ℝ → ℝ)
    (hf_cont : ∀ n, Continuous (f n))
    (hf_zero : f 0 = fun _ => 1)
    (hf_rec : ∀ n x, f (n+1) x = Real.exp (∫ t in (0:ℝ)..x, f n t))
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun n => f n x) atTop (𝓝 (answer x)) := by
  -- The sequence (f n x) is monotone in n, bounded above by 1/(1-x), and bounded below by 1.
  -- Hence it converges to some L ≤ 1/(1-x). Identifying L = 1/(1-x) requires
  -- the uniform convergence/Dini argument and continuity of Φ, which is left as TODO.
  sorry

end Imc2017P9
