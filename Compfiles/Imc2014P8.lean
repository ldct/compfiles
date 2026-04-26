/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2014, Problem 8

Let `f(x) = sin x / x` for `x > 0`, and let `n` be a positive integer.
Prove that `|f^{(n)}(x)| < 1/(n+1)`.

The proof uses the integral representation
  `sin x / x = ∫₀¹ cos(xt) dt`
so that
  `f^{(n)}(x) = ∫₀¹ t^n · (d^n/dy^n cos)(xt) dt`
and the iterated derivative of cos is bounded by 1 in absolute value, giving
  `|f^{(n)}(x)| ≤ ∫₀¹ t^n dt = 1/(n+1)`,
with strict inequality because the iterated derivative is not identically ±1
on `(0, x)`.
-/

namespace Imc2014P8

open Real MeasureTheory intervalIntegral Set

/-- The "sinc-like" function: `F x = ∫₀¹ cos (x t) dt`. This equals
`sin x / x` for `x ≠ 0` and `1` for `x = 0`. -/
noncomputable def F (x : ℝ) : ℝ := ∫ t in (0:ℝ)..1, Real.cos (x * t)

snip begin

/-- `F x = sin x / x` for `x > 0`. -/
lemma F_eq_sin_div (x : ℝ) (hx : x ≠ 0) : F x = Real.sin x / x := by
  unfold F
  -- ∫_0^1 cos(xt) dt = sin(x*1)/x - sin(x*0)/x = sin x / x
  have h1 : (∫ t in (0:ℝ)..1, Real.cos (x * t)) =
      (Real.sin (x * 1) - Real.sin (x * 0)) / x := by
    -- Use substitution u = x * t
    have key : ∀ t : ℝ,
        HasDerivAt (fun s => Real.sin (x * s) / x) (Real.cos (x * t)) t := by
      intro t
      have h := ((Real.hasDerivAt_sin (x * t)).comp t
        ((hasDerivAt_id t).const_mul x))
      simp at h
      have h2 : HasDerivAt (fun s => Real.sin (x * s)) (Real.cos (x * t) * x) t := by
        simpa using h
      have h3 : HasDerivAt (fun s => Real.sin (x * s) / x)
          (Real.cos (x * t) * x / x) t := h2.div_const x
      have hx' : Real.cos (x * t) * x / x = Real.cos (x * t) := by
        field_simp
      rwa [hx'] at h3
    have hint : (∫ t in (0:ℝ)..1, Real.cos (x * t)) =
        Real.sin (x * 1) / x - Real.sin (x * 0) / x :=
      integral_eq_sub_of_hasDerivAt (fun t _ => key t)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [hint]; ring
  rw [h1]
  simp

/-- The iterated derivative of `cos` is bounded by `1` in absolute value. -/
lemma abs_iteratedDeriv_cos_le_one (n : ℕ) (y : ℝ) :
    |iteratedDeriv n Real.cos y| ≤ 1 :=
  Real.abs_iteratedDeriv_cos_le_one n y

/-- `cos` is `C^∞`. -/
lemma contDiff_cos : ContDiff ℝ ⊤ Real.cos := Real.contDiff_cos

/-- Auxiliary: representation of the n-th derivative of F. We define
`Fn n x = ∫₀¹ t^n · (iteratedDeriv n cos) (x t) dt`. -/
noncomputable def Fn (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, t ^ n * iteratedDeriv n Real.cos (x * t)

lemma Fn_zero_eq_F (x : ℝ) : Fn 0 x = F x := by
  unfold Fn F
  congr 1; ext t
  simp [iteratedDeriv_zero]

/-- Differentiation under the integral: if `g_n(y) = (iteratedDeriv n cos)(y)`
then `Fn n` has derivative `Fn (n+1)`. -/
lemma hasDerivAt_Fn (n : ℕ) (x : ℝ) : HasDerivAt (Fn n) (Fn (n + 1) x) x := by
  -- The integrand at parameter x is t ↦ t^n * gn(x*t).
  -- Its derivative in x is t ↦ t^n * t * g_{n+1}(x*t) = t^{n+1} * g_{n+1}(x*t).
  -- We use `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on neighborhood (x-1, x+1).
  set g : ℕ → ℝ → ℝ := fun k y => iteratedDeriv k Real.cos y with hg
  -- Deriv of g k at y is g (k+1) y.
  have hg_deriv : ∀ k y, HasDerivAt (g k) (g (k + 1) y) y := by
    intro k y
    have hcd : ContDiff ℝ ⊤ Real.cos := contDiff_cos
    have hd : Differentiable ℝ (g k) := by
      simpa [g] using Real.differentiable_iteratedDeriv_cos k
    have hd' : (deriv (g k)) y = g (k + 1) y := by
      simp [g, ← iteratedDeriv_succ]
    have := (hd y).hasDerivAt
    rw [hd'] at this
    exact this
  -- Bound
  have hbound : ∀ k y, |g k y| ≤ 1 := abs_iteratedDeriv_cos_le_one
  -- Set up parametric integral hypotheses
  have hF_meas : ∀ᶠ x' in nhds x,
      AEStronglyMeasurable (fun t => t ^ n * g n (x' * t))
        (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    filter_upwards with x'
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (by fun_prop) ?_
    have : Continuous (g n) := (Real.differentiable_iteratedDeriv_cos n).continuous
    exact this.comp (by fun_prop)
  have hF_int : IntervalIntegrable (fun t => t ^ n * g n (x * t)) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    refine Continuous.mul (by fun_prop) ?_
    have : Continuous (g n) := (Real.differentiable_iteratedDeriv_cos n).continuous
    exact this.comp (by fun_prop)
  have hF'_meas : AEStronglyMeasurable (fun t => t ^ (n + 1) * g (n + 1) (x * t))
      (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (by fun_prop) ?_
    have : Continuous (g (n + 1)) := (Real.differentiable_iteratedDeriv_cos (n+1)).continuous
    exact this.comp (by fun_prop)
  -- bound |t^{n+1} g_{n+1}(x' t)| ≤ |t|^{n+1}
  set bnd : ℝ → ℝ := fun t => |t| ^ (n + 1) with hbnd
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x' ∈ Set.univ, ‖t ^ (n + 1) * g (n + 1) (x' * t)‖ ≤ bnd t := by
    refine ae_of_all _ ?_
    intro t _ x' _
    simp only [Real.norm_eq_abs, abs_mul, bnd]
    have h1 : |t ^ (n + 1)| = |t| ^ (n + 1) := by
      rw [abs_pow]
    rw [h1]
    have h2 : |g (n + 1) (x' * t)| ≤ 1 := hbound _ _
    nlinarith [abs_nonneg t, pow_nonneg (abs_nonneg t) (n + 1), h2,
               abs_nonneg (g (n+1) (x' * t))]
  have hbound_int : IntervalIntegrable bnd volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x' ∈ Set.univ, HasDerivAt (fun y => t ^ n * g n (y * t))
          (t ^ (n + 1) * g (n + 1) (x' * t)) x' := by
    refine ae_of_all _ ?_
    intro t _ x' _
    -- (y ↦ t^n * g n (y*t))' at x' = t^n * (g n)'(x'*t) * t = t^{n+1} g_{n+1}(x'*t)
    have h1 : HasDerivAt (fun y : ℝ => y * t) t x' := by
      simpa using (hasDerivAt_id x').mul_const t
    have h2 : HasDerivAt (g n) (g (n + 1) (x' * t)) (x' * t) := hg_deriv n (x' * t)
    have h3 : HasDerivAt (fun y => g n (y * t)) (g (n + 1) (x' * t) * t) x' := by
      have := HasDerivAt.scomp x' h2 h1
      simpa [mul_comm] using this
    have h4 : HasDerivAt (fun y => t ^ n * g n (y * t))
        (t ^ n * (g (n + 1) (x' * t) * t)) x' := h3.const_mul (t ^ n)
    have heq : t ^ n * (g (n + 1) (x' * t) * t) = t ^ (n + 1) * g (n + 1) (x' * t) := by ring
    rw [heq] at h4
    exact h4
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (μ := volume) (a := 0) (b := 1) (bound := bnd)
    (Filter.univ_mem) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  -- conclude
  have h := this.2
  -- Goal: HasDerivAt (Fn n) (Fn (n+1) x) x
  -- Fn n x = ∫_0^1 t^n * g n (x*t) dt
  unfold Fn
  convert h using 1

/-- By induction, the n-th iterated derivative of F equals Fn n. -/
lemma iteratedDeriv_F (n : ℕ) :
    iteratedDeriv n F = Fn n := by
  induction n with
  | zero => funext x; rw [iteratedDeriv_zero, Fn_zero_eq_F]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_Fn k x).deriv

/-- For any `n` and any `y` with `0 < y < π/2`, `|iteratedDeriv n cos y| < 1`.
The point: `g_n` is `±sin` or `±cos`, and on `(0, π/2)` both `|sin|` and `|cos|`
are strictly less than `1`. -/
lemma abs_iteratedDeriv_cos_lt_one_of_pos_lt_pi_div_two
    (n : ℕ) {y : ℝ} (hy_pos : 0 < y) (hy_lt : y < π / 2) :
    |iteratedDeriv n Real.cos y| < 1 := by
  -- Case on parity of n.
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = k + k, i.e., n = 2k.  iteratedDeriv (2k) cos = (-1)^k * cos
    have hn : n = 2 * k := by omega
    rw [hn, Real.iteratedDeriv_even_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    -- |cos y| < 1
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · have h2 : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
        (by constructor <;> linarith [Real.pi_pos])
      linarith
    · -- cos y < cos 0 = 1, since cos is strict on [0, π] and 0 < y ≤ π/2 < π
      have hy_le_pi : y ≤ π := by linarith [Real.pi_pos]
      have hcos_lt : Real.cos y < Real.cos 0 :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hy_le_pi hy_pos
      simpa using hcos_lt
  · -- n = 2k+1
    have hn : n = 2 * k + 1 := by omega
    rw [hn, Real.iteratedDeriv_odd_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · have : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy_pos
        (by linarith [Real.pi_pos])
      linarith
    · -- sin y < sin (π/2) = 1, since sin is strictMono on [-π/2, π/2]
      have hsin_lt : Real.sin y < Real.sin (π / 2) :=
        Real.strictMonoOn_sin (by constructor <;> linarith [Real.pi_pos])
          (by constructor <;> linarith [Real.pi_pos]) hy_lt
      simpa using hsin_lt

/-- The strict inequality: for `x > 0`, the iterated derivative of cos is not
identically ±1 on `(0, x)`, so the integral bound is strict. -/
lemma fn_strict_bound (n : ℕ) (x : ℝ) (hx : 0 < x) :
    |Fn n x| < 1 / (n + 1) := by
  -- Step 1: |Fn n x| ≤ ∫_0^1 |t^n g_n(xt)| dt
  set g : ℝ → ℝ := iteratedDeriv n Real.cos with hg_def
  have hg_cont : Continuous g := (Real.differentiable_iteratedDeriv_cos n).continuous
  have h1 : |Fn n x| ≤ ∫ t in (0:ℝ)..1, |t ^ n * g (x * t)| := by
    show |∫ t in (0:ℝ)..1, t ^ n * g (x * t)| ≤ _
    exact abs_integral_le_integral_abs (by norm_num : (0:ℝ) ≤ 1)
  -- Step 2: |t^n g(xt)| ≤ t^n on [0,1]
  have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1, |t ^ n * g (x * t)| ≤ t ^ n := by
    intro t ht
    have htnn : 0 ≤ t := ht.1
    have htpow : 0 ≤ t ^ n := pow_nonneg htnn n
    rw [abs_mul, abs_of_nonneg htpow]
    have hgle : |g (x * t)| ≤ 1 := abs_iteratedDeriv_cos_le_one n (x * t)
    nlinarith [htpow, hgle, abs_nonneg (g (x * t))]
  -- Step 3: pick c = min(1, 1/x) and show strict at c
  set c : ℝ := min 1 (1 / x) with hc_def
  have hc_pos : 0 < c := lt_min one_pos (one_div_pos.mpr hx)
  have hc_le : c ≤ 1 := min_le_left _ _
  have hxc_pos : 0 < x * c := mul_pos hx hc_pos
  have hxc_le : x * c ≤ 1 := by
    rcases le_total x 1 with h | h
    · -- x ≤ 1, so 1/x ≥ 1, so c = 1, so x*c = x ≤ 1.
      have h1x : 1 ≤ 1 / x := by
        rw [le_div_iff₀ hx]; linarith
      have hc1 : c = 1 := by
        rw [hc_def]; exact min_eq_left h1x
      rw [hc1]; linarith
    · -- x ≥ 1, so 1/x ≤ 1, so c ≤ 1/x, so x*c ≤ 1.
      have hcle : c ≤ 1 / x := min_le_right _ _
      calc x * c ≤ x * (1 / x) := by exact mul_le_mul_of_nonneg_left hcle hx.le
        _ = 1 := by field_simp
  have hxc_lt_pi2 : x * c < π / 2 := by
    have hpi_gt : 1 < π / 2 := by linarith [Real.pi_gt_three]
    linarith
  have hglt : |g (x * c)| < 1 :=
    abs_iteratedDeriv_cos_lt_one_of_pos_lt_pi_div_two n hxc_pos hxc_lt_pi2
  have hstrict :
      (∫ t in (0:ℝ)..1, |t ^ n * g (x * t)|) <
        ∫ t in (0:ℝ)..1, t ^ n := by
    refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num : (0:ℝ) < 1) ?_ ?_ ?_ ?_
    · refine Continuous.continuousOn ?_
      refine continuous_abs.comp ?_
      refine Continuous.mul (by fun_prop) ?_
      exact hg_cont.comp (by fun_prop)
    · exact (continuous_pow n).continuousOn
    · intro t ht
      exact hpoint t ⟨ht.1.le, ht.2⟩
    · refine ⟨c, ⟨hc_pos.le, hc_le⟩, ?_⟩
      have hcn_pos : 0 < c ^ n := pow_pos hc_pos n
      rw [abs_mul, abs_of_nonneg (pow_nonneg hc_pos.le n)]
      have : c ^ n * |g (x * c)| < c ^ n * 1 :=
        mul_lt_mul_of_pos_left hglt hcn_pos
      linarith
  -- Step 4: ∫_0^1 t^n dt = 1/(n+1)
  have hint_pow : (∫ t in (0:ℝ)..1, t ^ n) = 1 / (n + 1) := by
    rw [integral_pow]
    have h0 : (0:ℝ) ^ (n + 1) = 0 := zero_pow (Nat.succ_ne_zero n)
    rw [h0, one_pow, sub_zero]
  linarith [h1, hstrict, hint_pow]

snip end

problem imc2014_p8 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
    |iteratedDeriv n F x| < 1 / (n + 1) := by
  rw [iteratedDeriv_F]
  exact fn_strict_bound n x hx

end Imc2014P8
