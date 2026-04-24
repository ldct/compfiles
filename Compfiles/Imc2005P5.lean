/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2005, Problem 5
(First day, Problem 5)

Let `f : ℝ → ℝ` be twice continuously differentiable with
  `|f''(x) + 2x f'(x) + (x² + 1) f(x)| ≤ 1`  for all `x > 0`.
Prove that `f(x) → 0` as `x → ∞`.

We formalize the problem for `f : ℝ → ℝ` that is twice differentiable on all
of `ℝ` (with derivatives given by `f'` and `f''`), which is the usual Lean
formulation. The bound is assumed for `x ≥ 0`.

## Proof sketch

Let `g = f' + x · f`. Then
  `g'(x) + x · g(x) = f''(x) + 2x · f'(x) + (x² + 1) · f(x)`,
so `|g' + x g| ≤ 1`. The key lemma is:

  **Lemma.** If `h : ℝ → ℝ` is differentiable and `|h'(x) + x h(x)| ≤ M` for
  all `x ≥ 0`, then `h(x) → 0` as `x → ∞`.

Proof of the lemma: put `p(x) = h(x) · exp(x²/2)`. Then
`p'(x) = (h'(x) + x h(x)) · exp(x²/2)`, so `|p'(x)| ≤ M · exp(x²/2)`.
By FTC, `|p(x) - p(0)| ≤ M · ∫₀ˣ exp(t²/2) dt`. For `0 ≤ t ≤ x`,
`t² - x² = -(x - t)(x + t) ≤ -(x - t) · x`, so
`exp(t²/2) ≤ exp(x²/2) · exp(-(x - t) x / 2)`. Integrating gives
`∫₀ˣ exp(t²/2) dt ≤ (2/x) · exp(x²/2)` for `x > 0`. Hence
`|h(x)| ≤ |p(0)|/exp(x²/2) + 2M/x → 0`.

Apply the lemma to `g`, so `g → 0`. Then `f' + x f → 0`, and applying the
lemma again to `f` (with a suitable `M`) gives `f → 0`.
-/

namespace Imc2005P5

open Real Set Filter Topology

/-- The key analytic lemma: if `h'` is continuous and `|h'(x) + x h(x)| ≤ M`
for all `x ≥ 0`, then `h(x) → 0` as `x → ∞`. -/
lemma tendsto_zero_of_bound
    (h h' : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh'_cont : Continuous h')
    (hbound : ∀ x, 0 ≤ x → |h' x + x * h x| ≤ M) :
    Tendsto h atTop (𝓝 0) := by
  -- Let p(x) = h(x) * exp(x²/2). Compute p'(x) = (h'(x) + x h(x)) * exp(x²/2).
  set p : ℝ → ℝ := fun x => h x * Real.exp (x^2 / 2) with hp_def
  set p' : ℝ → ℝ := fun x => (h' x + x * h x) * Real.exp (x^2 / 2) with hp'_def
  have hexp_deriv : ∀ x, HasDerivAt (fun y => Real.exp (y^2 / 2)) (x * Real.exp (x^2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y^2 / 2) x x := by
      have := (hasDerivAt_pow 2 x).div_const 2
      convert this using 1
      ring
    have h2 : HasDerivAt (fun y => Real.exp (y^2 / 2)) (Real.exp (x^2 / 2) * x) x :=
      (Real.hasDerivAt_exp _).comp x h1
    convert h2 using 1
    ring
  have hp_deriv : ∀ x, HasDerivAt p (p' x) x := by
    intro x
    have h1 : HasDerivAt p (h' x * Real.exp (x^2 / 2) + h x * (x * Real.exp (x^2 / 2))) x :=
      (hh x).mul (hexp_deriv x)
    convert h1 using 1
    simp [p']; ring
  -- Bound |p'(x)| ≤ M * exp(x²/2) for x ≥ 0.
  have hp'_bound : ∀ x, 0 ≤ x → |p' x| ≤ M * Real.exp (x^2 / 2) := by
    intro x hx
    simp only [p']
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (Real.exp_pos _).le
  -- |p(x) - p(0)| ≤ M * ∫₀ˣ exp(t²/2) dt for x ≥ 0 (via FTC).
  have hh_cont : Continuous h :=
    continuous_iff_continuousAt.mpr (fun x => (hh x).continuousAt)
  have hcont_p' : Continuous p' := by
    simp only [p']
    refine (hh'_cont.add (continuous_id.mul hh_cont)).mul ?_
    exact Real.continuous_exp.comp (by continuity)
  have hp_intEq : ∀ x, 0 ≤ x → p x - p 0 = ∫ t in (0:ℝ)..x, p' t := by
    intro x _
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
      (fun y _ => hp_deriv y) (hcont_p'.intervalIntegrable _ _)).symm
  -- Estimate: for 0 ≤ t ≤ x, exp(t²/2) ≤ exp(x²/2) * exp(-(x-t)*x/2).
  have hexp_est : ∀ x t, 0 ≤ t → t ≤ x →
      Real.exp (t^2 / 2) ≤ Real.exp (x^2 / 2) * Real.exp (-(x - t) * x / 2) := by
    intro x t ht htx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : t^2 - x^2 = -(x - t) * (x + t) := by ring
    have h2 : (x + t) ≥ x := by linarith
    have h3 : x - t ≥ 0 := by linarith
    have h4 : x ≥ 0 := le_trans ht htx
    have h5 : (x - t) * (x + t) ≥ (x - t) * x :=
      mul_le_mul_of_nonneg_left h2 h3
    nlinarith
  -- Integral bound: ∫₀ˣ exp(t²/2) dt ≤ (2/x) * exp(x²/2) for x > 0.
  have hintegral_bound : ∀ x, 0 < x →
      ∫ t in (0:ℝ)..x, Real.exp (t^2 / 2) ≤ (2 / x) * Real.exp (x^2 / 2) := by
    intro x hx
    -- ∫₀ˣ exp(t²/2) dt ≤ exp(x²/2) * ∫₀ˣ exp(-(x-t)*x/2) dt
    -- = exp(x²/2) * (2/x) * (1 - exp(-x²/2))
    -- ≤ (2/x) * exp(x²/2).
    have hcont_expsq2 : Continuous (fun t : ℝ => Real.exp (t^2 / 2)) :=
      Real.continuous_exp.comp ((continuous_pow 2).div_const 2)
    have hcont_expinner : Continuous (fun t : ℝ => Real.exp (-(x - t) * x / 2)) := by
      refine Real.continuous_exp.comp ?_
      exact ((continuous_const.sub continuous_id).neg.mul continuous_const).div_const 2
    have hle : (∫ t in (0:ℝ)..x, Real.exp (t^2 / 2)) ≤
        ∫ t in (0:ℝ)..x, Real.exp (x^2 / 2) * Real.exp (-(x - t) * x / 2) := by
      apply intervalIntegral.integral_mono_on hx.le
      · exact hcont_expsq2.intervalIntegrable _ _
      · exact (continuous_const.mul hcont_expinner).intervalIntegrable _ _
      · intro t ht
        exact hexp_est x t ht.1 ht.2
    -- Now compute the RHS integral.
    have hcomp_deriv : ∀ t, HasDerivAt (fun s => (2/x) * Real.exp (-(x - s) * x / 2))
        (Real.exp (-(x - t) * x / 2)) t := by
      intro t
      have hh1 : HasDerivAt (fun s : ℝ => -(x - s) * x / 2) (x/2) t := by
        have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
        have h1 : HasDerivAt (fun s : ℝ => x - s) (0 - 1) t :=
          (hasDerivAt_const t x).sub hid
        have h2 : HasDerivAt (fun s : ℝ => -(x - s)) (-(0 - 1)) t := h1.neg
        have h3 : HasDerivAt (fun s : ℝ => -(x - s) * x) (-(0 - 1) * x) t :=
          h2.mul_const x
        have h4 : HasDerivAt (fun s : ℝ => -(x - s) * x / 2) (-(0 - 1) * x / 2) t :=
          h3.div_const 2
        convert h4 using 1
        ring
      have hh2 : HasDerivAt (fun s => Real.exp (-(x - s) * x / 2))
          (Real.exp (-(x - t) * x / 2) * (x/2)) t :=
        (Real.hasDerivAt_exp _).comp t hh1
      have hh3 : HasDerivAt (fun s => (2/x) * Real.exp (-(x - s) * x / 2))
          ((2/x) * (Real.exp (-(x - t) * x / 2) * (x/2))) t :=
        hh2.const_mul _
      convert hh3 using 1
      have hx_ne : x ≠ 0 := ne_of_gt hx
      field_simp
    have hintval : (∫ t in (0:ℝ)..x, Real.exp (-(x - t) * x / 2)) =
        (2/x) * Real.exp (-(x - x) * x / 2) - ((2/x) * Real.exp (-(x - 0) * x / 2)) := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hcomp_deriv t)
        (hcont_expinner.intervalIntegrable _ _)
    have hrhs_int : (∫ t in (0:ℝ)..x, Real.exp (x^2 / 2) * Real.exp (-(x - t) * x / 2)) =
        Real.exp (x^2 / 2) * ((2/x) * (1 - Real.exp (-(x^2/2)))) := by
      rw [intervalIntegral.integral_const_mul, hintval]
      have hx0 : -(x - x) * x / 2 = 0 := by ring
      have hxx0 : -(x - 0) * x / 2 = -(x^2/2) := by ring
      rw [hx0, hxx0, Real.exp_zero]
      ring
    rw [hrhs_int] at hle
    -- Now bound: exp(x²/2) * ((2/x) * (1 - exp(-x²/2))) ≤ (2/x) * exp(x²/2).
    have hbound2 : Real.exp (x^2 / 2) * ((2/x) * (1 - Real.exp (-(x^2/2)))) ≤ (2/x) * Real.exp (x^2/2) := by
      have hnn : (0 : ℝ) ≤ 2/x := by positivity
      have h1me : (1 - Real.exp (-(x^2/2))) ≤ 1 := by
        have := Real.exp_pos (-(x^2/2))
        linarith
      have h_expnn : (0 : ℝ) ≤ Real.exp (x^2/2) := (Real.exp_pos _).le
      have hstep : Real.exp (x^2 / 2) * ((2/x) * (1 - Real.exp (-(x^2/2)))) ≤
          Real.exp (x^2 / 2) * ((2/x) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1me hnn) h_expnn
      linarith [hstep]
    linarith
  -- |p x - p 0| ≤ M * (2/x) * exp(x²/2) for x > 0.
  have hcont_expsq : Continuous (fun t : ℝ => Real.exp (t^2/2)) :=
    Real.continuous_exp.comp ((continuous_pow 2).div_const 2)
  have hp_abs_bound : ∀ x, 0 < x → |p x - p 0| ≤ M * ((2/x) * Real.exp (x^2/2)) := by
    intro x hx
    rw [hp_intEq x hx.le]
    have habsle : |∫ t in (0:ℝ)..x, p' t| ≤ ∫ t in (0:ℝ)..x, |p' t| :=
      intervalIntegral.abs_integral_le_integral_abs hx.le
    have hintabs : (∫ t in (0:ℝ)..x, |p' t|) ≤ ∫ t in (0:ℝ)..x, M * Real.exp (t^2/2) := by
      apply intervalIntegral.integral_mono_on hx.le
      · exact hcont_p'.abs.intervalIntegrable _ _
      · exact (continuous_const.mul hcont_expsq).intervalIntegrable _ _
      · intro t ht
        exact hp'_bound t ht.1
    rw [intervalIntegral.integral_const_mul] at hintabs
    have hfinal : M * ∫ t in (0:ℝ)..x, Real.exp (t^2 / 2) ≤ M * ((2/x) * Real.exp (x^2/2)) :=
      mul_le_mul_of_nonneg_left (hintegral_bound x hx) hM
    linarith
  -- So for x > 0: |h x| ≤ (|p 0| + M * 2/x * exp(x²/2)) / exp(x²/2) = |p 0| * exp(-x²/2) + 2M/x.
  have hh_bound : ∀ x, 0 < x → |h x| ≤ |p 0| / Real.exp (x^2/2) + (2 * M) / x := by
    intro x hx
    have habs := hp_abs_bound x hx
    have hexppos : 0 < Real.exp (x^2/2) := Real.exp_pos _
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hexp_ne : Real.exp (x^2/2) ≠ 0 := ne_of_gt hexppos
    -- |p x| ≤ |p 0| + M * (2/x) * exp(x²/2)
    have habs2 : |p x| - |p 0| ≤ |p x - p 0| := abs_sub_abs_le_abs_sub _ _
    have h1 : |p x| ≤ |p 0| + M * ((2/x) * Real.exp (x^2/2)) := by linarith
    -- p x = h x * exp(x²/2), so |p x| = |h x| * exp(x²/2).
    have hpx : |p x| = |h x| * Real.exp (x^2/2) := by
      show |h x * Real.exp (x^2/2)| = |h x| * Real.exp (x^2/2)
      rw [abs_mul, abs_of_pos hexppos]
    rw [hpx] at h1
    -- From |h x| * exp(x²/2) ≤ |p 0| + M * (2/x) * exp(x²/2), divide by exp(x²/2).
    have h2 : |h x| ≤ (|p 0| + M * ((2/x) * Real.exp (x^2/2))) / Real.exp (x^2/2) := by
      rw [le_div_iff₀ hexppos]; linarith
    have h3 : (|p 0| + M * ((2/x) * Real.exp (x^2/2))) / Real.exp (x^2/2)
        = |p 0| / Real.exp (x^2/2) + (2 * M) / x := by
      field_simp
    linarith
  -- Both bounds tend to 0.
  have hsq_tendsto : Tendsto (fun x : ℝ => x^2 / 2) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => x^2) atTop atTop :=
      tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)
    exact h1.atTop_div_const (by norm_num : (0:ℝ) < 2)
  have hexp_top : Tendsto (fun x : ℝ => Real.exp (x^2/2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hsq_tendsto
  have hterm1 : Tendsto (fun x : ℝ => |p 0| / Real.exp (x^2/2)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun x : ℝ => (Real.exp (x^2/2))⁻¹) atTop (𝓝 0) :=
      hexp_top.inv_tendsto_atTop
    have hmul : Tendsto (fun x : ℝ => |p 0| * (Real.exp (x^2/2))⁻¹) atTop (𝓝 (|p 0| * 0)) :=
      tendsto_const_nhds.mul hinv
    rw [mul_zero] at hmul
    have heq : (fun x : ℝ => |p 0| / Real.exp (x^2/2)) = fun x => |p 0| * (Real.exp (x^2/2))⁻¹ := by
      ext x; rw [div_eq_mul_inv]
    rw [heq]
    exact hmul
  have hterm2 : Tendsto (fun x : ℝ => (2 * M) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  -- Combine: both go to 0, so their sum does, and |h x| ≤ sum.
  have hsum : Tendsto (fun x : ℝ => |p 0| / Real.exp (x^2/2) + (2 * M) / x) atTop (𝓝 0) := by
    have := hterm1.add hterm2
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hsum
  obtain ⟨N, hN⟩ := hsum ε hε
  refine ⟨max N 1, fun x hx => ?_⟩
  have hxN : x ≥ N := le_trans (le_max_left _ _) hx
  have hx1 : x ≥ 1 := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hbnd := hh_bound x hxpos
  have hsum_bnd := hN x hxN
  simp only [Real.dist_eq, sub_zero] at hsum_bnd
  have h_abs_sum : |p 0| / Real.exp (x^2/2) + (2 * M) / x ≥ 0 := by
    have h1 : (0:ℝ) ≤ |p 0| / Real.exp (x^2/2) := by positivity
    have h2 : (0:ℝ) ≤ (2 * M) / x := by positivity
    linarith
  rw [abs_of_nonneg h_abs_sum] at hsum_bnd
  rw [Real.dist_eq, sub_zero]
  linarith

/-- The answer predicate: `f(x) → 0` as `x → ∞`. -/
problem imc2005_p5 (f f' f'' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''_cont : Continuous f'')
    (hbound : ∀ x, 0 ≤ x → |f'' x + 2 * x * f' x + (x^2 + 1) * f x| ≤ 1) :
    Tendsto f atTop (𝓝 0) := by
  -- Let g = f' + x·f.
  set g : ℝ → ℝ := fun x => f' x + x * f x with hg_def
  set g' : ℝ → ℝ := fun x => f'' x + (f x + x * f' x) with hg'_def
  -- Derivative of g.
  have hg_deriv : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    have h1 : HasDerivAt (fun y => y * f y) (1 * f x + x * f' x) x :=
      (hasDerivAt_id x).mul (hf x)
    have h2 : HasDerivAt g (f'' x + (1 * f x + x * f' x)) x := (hf' x).add h1
    convert h2 using 1
    show f'' x + (f x + x * f' x) = f'' x + (1 * f x + x * f' x)
    ring
  -- g'(x) + x·g(x) = f''(x) + 2x·f'(x) + (x²+1)·f(x).
  have hg_bound : ∀ x, 0 ≤ x → |g' x + x * g x| ≤ 1 := by
    intro x hx
    have : g' x + x * g x = f'' x + 2 * x * f' x + (x^2 + 1) * f x := by
      simp [g, g']; ring
    rw [this]
    exact hbound x hx
  -- Continuity of f and f'.
  have hf_cont : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hf'_cont : Continuous f' :=
    continuous_iff_continuousAt.mpr (fun x => (hf' x).continuousAt)
  have hg'_cont : Continuous g' := by
    simp only [g']
    exact hf''_cont.add (hf_cont.add (continuous_id.mul hf'_cont))
  -- Apply lemma to g: g → 0.
  have hg_tendsto : Tendsto g atTop (𝓝 0) :=
    tendsto_zero_of_bound g g' 1 (by norm_num) hg_deriv hg'_cont hg_bound
  -- Now apply lemma to f, but we need |f'(x) + x f(x)| ≤ M for some M. Since g → 0,
  -- it's eventually bounded (say by 1), but we need uniform bound for all x ≥ 0.
  -- Since g is continuous and g → 0, g is bounded on [0, ∞).
  have hg_cont : Continuous g := by
    exact continuous_iff_continuousAt.mpr (fun x => (hg_deriv x).continuousAt)
  have hg_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, 0 ≤ x → |g x| ≤ M := by
    -- g → 0, so ∃ N, ∀ x ≥ N, |g x| ≤ 1. g continuous on [0,N] is bounded.
    obtain ⟨N, hN⟩ : ∃ N, ∀ x ≥ N, |g x| ≤ 1 := by
      have := hg_tendsto
      rw [Metric.tendsto_atTop] at this
      obtain ⟨N, hN⟩ := this 1 (by norm_num)
      refine ⟨N, fun x hx => ?_⟩
      have hdist := hN x hx
      rw [Real.dist_eq, sub_zero] at hdist
      linarith
    -- On [0, N], g is continuous, so bounded by some M₀.
    by_cases hN_nonneg : 0 ≤ N
    · have : IsCompact (Icc (0:ℝ) N) := isCompact_Icc
      obtain ⟨M₀, hM₀⟩ := this.exists_bound_of_continuousOn hg_cont.continuousOn
      refine ⟨max M₀ 1, le_max_of_le_right (by norm_num), ?_⟩
      intro x hx
      by_cases hxN : x ≤ N
      · exact le_trans (hM₀ x ⟨hx, hxN⟩) (le_max_left _ _)
      · exact le_trans (hN x (le_of_lt (lt_of_not_ge hxN))) (le_max_right _ _)
    · refine ⟨1, by norm_num, ?_⟩
      intro x hx
      exact hN x (by linarith [not_le.mp hN_nonneg])
  obtain ⟨M, hM_nonneg, hM_bound⟩ := hg_bdd
  -- For x ≥ 0, |f'(x) + x f(x)| = |g x| ≤ M.
  have hf_bound : ∀ x, 0 ≤ x → |f' x + x * f x| ≤ M := by
    intro x hx
    exact hM_bound x hx
  exact tendsto_zero_of_bound f f' M hM_nonneg hf hf'_cont hf_bound

end Imc2005P5
