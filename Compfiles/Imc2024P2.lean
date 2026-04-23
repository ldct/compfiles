/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 2

For `n = 1, 2, ...` let
`S_n = log (n^2-th root of (1^1 * 2^2 * ... * n^n)) - log (sqrt n)`.
Find `lim_{n → ∞} S_n`.

Answer: `-1/4`.

## Solution sketch

We rewrite
`S_n = (1/n^2) * Σ_{k=1}^n k * log k - (1/2) log n`
`    = (1/n) * Σ_{k=1}^n (k/n) * log(k/n) + (log n)/(2n)`.

The second term tends to `0`, and the first is a Riemann sum for
`∫_0^1 x log x dx = -1/4`.
-/

namespace Imc2024P2

open Filter Topology MeasureTheory intervalIntegral Set Real

/-- The sequence `S_n` in the problem.
We state it as `(1/n²) Σ k log k - (log n)/2` for `n ≥ 1`.
For `n = 0`, the expression evaluates to `0` (all terms in the sum are zero). -/
noncomputable def S (n : ℕ) : ℝ :=
  (1 / (n : ℝ)^2) * ∑ k ∈ Finset.range (n + 1), (k : ℝ) * Real.log k
    - (1 / 2) * Real.log n

/-- The limit of `S_n` as `n → ∞`. -/
noncomputable determine answer : ℝ := -(1 / 4)

snip begin

/-- Antiderivative of `x * log x`: `x^2/2 * log x - x^2/4`. -/
private noncomputable def F (x : ℝ) : ℝ := x^2 / 2 * Real.log x - x^2 / 4

private lemma F_zero : F 0 = 0 := by simp [F]

private lemma F_one : F 1 = -(1/4) := by simp [F]

private lemma hasDerivAt_F {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt F (x * Real.log x) x := by
  have h1 : HasDerivAt (fun x : ℝ => x^2 / 2 * Real.log x)
      (x * Real.log x + x / 2) x := by
    have h_a : HasDerivAt (fun x : ℝ => x^2 / 2) (x) x := by
      have := (hasDerivAt_pow 2 x).div_const 2
      convert this using 1
      push_cast; ring
    have h_b := Real.hasDerivAt_log hx
    have := h_a.mul h_b
    convert this using 1
    field_simp
  have h2 : HasDerivAt (fun x : ℝ => x^2 / 4) (x / 2) x := by
    have := (hasDerivAt_pow 2 x).div_const 4
    convert this using 1
    push_cast; ring
  have := h1.sub h2
  convert this using 1
  ring

/-- `F` is continuous at 0 since `x² log x → 0` as `x → 0`. -/
private lemma tendsto_F_zero : Tendsto F (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x^2 * Real.log x) (𝓝 0) (𝓝 0) := by
    -- x^2 log x = x * (x log x), and both factors → 0
    have hcts : Continuous (fun x : ℝ => x * Real.log x) := Real.continuous_mul_log
    have hid : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := continuous_id.tendsto 0
    have hxlx : Tendsto (fun x : ℝ => x * Real.log x) (𝓝 0) (𝓝 0) := by
      have := hcts.tendsto 0
      simpa using this
    have := hid.mul hxlx
    simp only [mul_zero] at this
    convert this using 1
    ext x
    ring
  have h2 : Tendsto (fun x : ℝ => x^2 / 2 * Real.log x) (𝓝 0) (𝓝 0) := by
    have : (fun x : ℝ => x^2 / 2 * Real.log x) = fun x => (x^2 * Real.log x) / 2 := by
      ext x; ring
    rw [this]
    simpa using h1.div_const 2
  have h3 : Tendsto (fun x : ℝ => x^2 / 4) (𝓝 0) (𝓝 0) := by
    have := (continuous_pow 2).tendsto (0 : ℝ)
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at this
    have h := this.div_const 4
    simpa using h
  have : Tendsto F (𝓝 0) (𝓝 (0 - 0)) := h2.sub h3
  simpa using this

/-- The integral of `x log x` on `[0, 1]` is `-1/4`. -/
private lemma integral_mul_log_zero_one :
    ∫ x in (0 : ℝ)..1, x * Real.log x = -(1/4) := by
  have h1 : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := by
    rw [F_zero]
    exact tendsto_F_zero.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto F (𝓝[<] 1) (𝓝 (F 1)) :=
    ((hasDerivAt_F one_ne_zero).continuousAt).continuousWithinAt
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := F) (a := 0) (b := 1) (fa := F 0) (fb := F 1) zero_lt_one
      (fun x hx => hasDerivAt_F (by
        rcases hx with ⟨hx1, _⟩
        exact hx1.ne'))
      (ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le zero_le_one]
        exact Real.continuous_mul_log.continuousOn))
      h1 h2
  rw [F_zero, F_one] at this
  linarith

/-- `log n / (2n) → 0` as `n → ∞` over naturals. -/
private lemma tendsto_log_div_two_n :
    Tendsto (fun n : ℕ => Real.log n / (2 * n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / (2 * x + 0)) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 2 0 1 (by norm_num)
    simpa using this
  have h2 : Tendsto (fun x : ℝ => Real.log x / (2 * x)) atTop (𝓝 0) := by
    simpa using h1
  exact h2.comp tendsto_natCast_atTop_atTop

/-- The integral `∫ (log x + 1) dx = x log x` equality. -/
private lemma integral_log_add_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (Real.log x + 1) = b * Real.log b - a * Real.log a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => x * Real.log x) (f' := fun x => Real.log x + 1)]
  · intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    exact Real.hasDerivAt_mul_log hx_pos.ne'
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    exact ((Real.continuousAt_log hx_pos.ne').add continuousAt_const).continuousWithinAt

/-- `x log x` is antitone on `[0, 1/e]`. -/
private lemma antitoneOn_mul_log : AntitoneOn (fun x : ℝ => x * Real.log x)
    (Set.Icc 0 (Real.exp (-1))) := by
  intro a ⟨ha0, ha1⟩ b ⟨hb0, hb1⟩ hab
  rcases eq_or_lt_of_le ha0 with rfl | ha_pos
  · show b * Real.log b ≤ 0 * Real.log 0
    simp only [zero_mul]
    have hb_le1 : b ≤ 1 := hb1.trans (by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by norm_num))
    exact Real.mul_log_nonpos hb0 hb_le1
  -- For 0 < a ≤ b ≤ 1/e, show b log b ≤ a log a using integration
  -- b log b - a log a = ∫_a^b (log x + 1) dx ≤ 0 since log x ≤ -1 on (0, 1/e]
  apply sub_nonpos.mp
  rw [show b * Real.log b - a * Real.log a = ∫ x in a..b, (Real.log x + 1) from
    (integral_log_add_one ha_pos hab).symm]
  rw [show (0 : ℝ) = ∫ _ in a..b, (0 : ℝ) from by simp]
  apply intervalIntegral.integral_mono_on hab
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    exact ((Real.continuousAt_log hx_pos.ne').add continuousAt_const).continuousWithinAt
  · exact _root_.intervalIntegrable_const
  · intro x ⟨hx1, hx2⟩
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx1
    have hx_le : x ≤ Real.exp (-1) := hx2.trans hb1
    have : Real.log x ≤ -1 := by
      rw [show (-1 : ℝ) = Real.log (Real.exp (-1)) from (Real.log_exp _).symm]
      exact Real.log_le_log hx_pos hx_le
    linarith

/-- `x log x` is monotone on `[1/e, 1]`. -/
private lemma monotoneOn_mul_log : MonotoneOn (fun x : ℝ => x * Real.log x)
    (Set.Icc (Real.exp (-1)) 1) := by
  intro a ⟨ha0, ha1⟩ b ⟨hb0, hb1⟩ hab
  have ha_pos : 0 < a := lt_of_lt_of_le (Real.exp_pos _) ha0
  apply sub_nonneg.mp
  rw [show b * Real.log b - a * Real.log a = ∫ x in a..b, (Real.log x + 1) from
    (integral_log_add_one ha_pos hab).symm]
  apply intervalIntegral.integral_nonneg hab
  intro x ⟨hx1, hx2⟩
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx1
  have hlog : -1 ≤ Real.log x := by
    rw [show (-1 : ℝ) = Real.log (Real.exp (-1)) from (Real.log_exp _).symm]
    exact Real.log_le_log (Real.exp_pos _) (ha0.trans hx1)
  linarith

/-- Bound `|x log x| ≤ 1/e` for `x ∈ [0, 1]`. -/
private lemma abs_mul_log_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x * Real.log x| ≤ Real.exp (-1) := by
  rcases eq_or_lt_of_le hx0 with rfl | hx_pos
  · simp; exact (Real.exp_pos _).le
  rcases lt_or_ge x (Real.exp (-1)) with hlt | hge
  · -- On (0, 1/e], f antitone, so f(x) ≥ f(1/e) = -1/e, and f(x) ≤ 0
    have h_neg : x * Real.log x ≤ 0 := Real.mul_log_nonpos hx_pos.le hx1
    have h_ge : Real.exp (-1) * (-1 : ℝ) ≤ x * Real.log x := by
      -- antitoneOn gives f(1/e) ≥ f(x)? No wait we need ≤
      -- Actually antitoneOn: x ≤ 1/e ⟹ f(1/e) ≤ f(x). So f(x) ≥ f(1/e) = -1/e.
      have habs : (fun y : ℝ => y * Real.log y) (Real.exp (-1)) ≤
          (fun y => y * Real.log y) x := by
        exact antitoneOn_mul_log (by simp [hx_pos.le, hlt.le])
          (by simp [(Real.exp_pos _).le]) hlt.le
      simp only [Real.log_exp] at habs
      linarith
    rw [abs_of_nonpos h_neg]
    have : Real.exp (-1) * (-1 : ℝ) = -Real.exp (-1) := by ring
    linarith
  · -- On [1/e, 1], f monotone, so f(x) ≤ f(1) = 0, and f(x) ≥ f(1/e) = -1/e
    have h_le : x * Real.log x ≤ 0 := Real.mul_log_nonpos hx_pos.le hx1
    have h_ge : Real.exp (-1) * (-1 : ℝ) ≤ x * Real.log x := by
      have hexp_le_one : Real.exp (-1) ≤ 1 := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
        exact Real.exp_le_exp.mpr (by norm_num)
      have : (fun y : ℝ => y * Real.log y) (Real.exp (-1)) ≤
          (fun y => y * Real.log y) x :=
        monotoneOn_mul_log (by simp [hexp_le_one])
          (by simp [hge, hx1]) hge
      simp only [Real.log_exp] at this
      linarith
    rw [abs_of_nonpos h_le]
    have : Real.exp (-1) * (-1 : ℝ) = -Real.exp (-1) := by ring
    linarith

/-- Per-interval bound: if `f` is monotone on `[a, b]`, then
`|f(b)·(b-a) - ∫_a^b f| ≤ (b-a)·|f(b) - f(a)|`.
We state it as: `|f(b) - (1/(b-a)) ∫_a^b f| · (b-a) ≤ |f(b) - f(a)| · (b-a)`. -/
private lemma per_interval_bound_mono {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmono : MonotoneOn f (Set.Icc a b)) (hint : IntervalIntegrable f volume a b) :
    |f b * (b - a) - ∫ x in a..b, f x| ≤ (f b - f a) * (b - a) := by
  have hfab : f a ≤ f b := hmono (by simp [hab]) (by simp [hab]) hab
  -- f(b) * (b - a) is upper bound for integral (f ≤ f b on [a, b])
  -- integral ≥ f(a) * (b - a) (f ≥ f a on [a, b])
  have hu : ∫ x in a..b, f x ≤ f b * (b - a) := by
    have h1 : ∫ x in a..b, f x ≤ ∫ _ in a..b, f b :=
      intervalIntegral.integral_mono_on hab hint _root_.intervalIntegrable_const
        (fun x hx => hmono ⟨hx.1, hx.2⟩ ⟨hab, le_refl b⟩ hx.2)
    simp at h1
    convert h1 using 1
    ring
  have hl : f a * (b - a) ≤ ∫ x in a..b, f x := by
    have h1 : ∫ _ in a..b, f a ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const hint
        (fun x hx => hmono ⟨le_refl a, hab⟩ ⟨hx.1, hx.2⟩ hx.1)
    simp at h1
    convert h1 using 1
    ring
  rw [abs_of_nonneg (by linarith)]
  have : f b - f a ≥ 0 := by linarith
  nlinarith

/-- Per-interval bound for antitone. -/
private lemma per_interval_bound_anti {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hanti : AntitoneOn f (Set.Icc a b)) (hint : IntervalIntegrable f volume a b) :
    |f b * (b - a) - ∫ x in a..b, f x| ≤ (f a - f b) * (b - a) := by
  have hfab : f b ≤ f a := hanti ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  have hu : ∫ x in a..b, f x ≤ f a * (b - a) := by
    have h1 : ∫ x in a..b, f x ≤ ∫ _ in a..b, f a :=
      intervalIntegral.integral_mono_on hab hint _root_.intervalIntegrable_const
        (fun x hx => hanti ⟨le_refl a, hab⟩ ⟨hx.1, hx.2⟩ hx.1)
    simp at h1
    convert h1 using 1
    ring
  have hl : f b * (b - a) ≤ ∫ x in a..b, f x := by
    have h1 : ∫ _ in a..b, f b ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_on hab _root_.intervalIntegrable_const hint
        (fun x hx => hanti ⟨hx.1, hx.2⟩ ⟨hab, le_refl b⟩ hx.2)
    simp at h1
    convert h1 using 1
    ring
  rw [abs_of_nonpos (by linarith)]
  have : f a - f b ≥ 0 := by linarith
  nlinarith

/-- Bound on a "bridging" interval containing 1/e. -/
private lemma per_interval_bridge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(b * Real.log b) * (b - a) - ∫ x in a..b, x * Real.log x| ≤
      2 * Real.exp (-1) * (b - a) := by
  have hint : IntervalIntegrable (fun x => x * Real.log x) volume a b :=
    ContinuousOn.intervalIntegrable (Real.continuous_mul_log.continuousOn)
  have hab_b_log_b : |b * Real.log b| ≤ Real.exp (-1) :=
    abs_mul_log_le (ha.trans hab) hb
  -- |integral| ≤ ∫ |f| ≤ (b - a) · sup |f| ≤ (b - a) · exp(-1)
  have h_int_abs : |∫ x in a..b, x * Real.log x| ≤ Real.exp (-1) * (b - a) := by
    calc |∫ x in a..b, x * Real.log x|
        ≤ ∫ x in a..b, |x * Real.log x| := by
          apply intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ _ in a..b, Real.exp (-1) := by
          apply intervalIntegral.integral_mono_on hab hint.abs _root_.intervalIntegrable_const
          intro x hx
          exact abs_mul_log_le (ha.trans hx.1) (hx.2.trans hb)
      _ = Real.exp (-1) * (b - a) := by simp; ring
  calc |(b * Real.log b) * (b - a) - ∫ x in a..b, x * Real.log x|
      ≤ |(b * Real.log b) * (b - a)| + |∫ x in a..b, x * Real.log x| := abs_sub _ _
    _ = |b * Real.log b| * |b - a| + |∫ x in a..b, x * Real.log x| := by rw [abs_mul]
    _ = |b * Real.log b| * (b - a) + |∫ x in a..b, x * Real.log x| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ b - a)]
    _ ≤ Real.exp (-1) * (b - a) + Real.exp (-1) * (b - a) := by
        have hba : 0 ≤ b - a := by linarith
        have h1 : |b * Real.log b| * (b - a) ≤ Real.exp (-1) * (b - a) := by
          exact mul_le_mul_of_nonneg_right hab_b_log_b hba
        linarith
    _ = 2 * Real.exp (-1) * (b - a) := by ring

/-- Telescoping sum: `∑_{i∈range n}(g i - g (i+1)) = g 0 - g n`. -/
private lemma telescope_sub (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (g i - g (i + 1)) = g 0 - g n := by
  induction n with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Telescoping sum: `∑_{i∈range n}(g (i+1) - g i) = g n - g 0`. -/
private lemma telescope_sub' (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (g (i + 1) - g i) = g n - g 0 := by
  have := telescope_sub g n
  have h : ∑ i ∈ Finset.range n, (g (i + 1) - g i) = -∑ i ∈ Finset.range n, (g i - g (i + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros; ring
  rw [h, this]; ring

/-- Telescoping identity: `Σ_{k=1}^n ∫_{(k-1)/n}^{k/n} f = ∫_0^1 f` when f is continuous. -/
private lemma sum_integral_telescope (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) (hf : Continuous f) :
    ∑ k ∈ Finset.Icc 1 n, ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x = ∫ x in (0 : ℝ)..1, f x := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun (k : ℕ) => (k : ℝ) / n) (μ := volume) (f := f) (n := n)
    (fun k _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_div] at h
  have h1 : ((n : ℕ) : ℝ) / n = 1 := by push_cast; field_simp
  rw [h1] at h
  rw [← h]
  -- Σ_{k∈range n} ∫_{k/n}^{(k+1)/n} f = Σ_{k∈Icc 1 n} ∫_{(k-1)/n}^{k/n} f
  rw [show (Finset.Icc 1 n) = (Finset.range n).image (· + 1) by
    ext k; simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩; omega]
  rw [Finset.sum_image (by
    intros a _ b _ h
    have : a + 1 = b + 1 := h
    omega)]
  apply Finset.sum_congr rfl
  intros k _
  congr 1 <;> push_cast <;> ring

/-- Key Riemann sum convergence: `(1/n) Σ_{k=1}^n f(k/n) → ∫_0^1 f` for `f = x log x`. -/
private lemma tendsto_riemann_sum :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n,
      ((k : ℝ) / n) * Real.log ((k : ℝ) / n)) atTop (𝓝 (-(1/4))) := by
  rw [← integral_mul_log_zero_one]
  set f : ℝ → ℝ := fun x => x * Real.log x with hf_def
  have hf_cts : Continuous f := Real.continuous_mul_log
  -- Error bound per interval
  -- For each n, we'll show |T_n - I| ≤ 6/(e n).
  -- Define error_n k = f(k/n) · (1/n) - ∫_{(k-1)/n}^{k/n} f
  -- Split: antitone part (intervals in [0, 1/e]), monotone part (in [1/e, 1]), and bridge.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Choose N so that 6 * e^(-1) / N < ε.
  obtain ⟨N, hN_pos, hN_bd⟩ : ∃ N : ℕ, 0 < N ∧ 6 * Real.exp (-1) / N < ε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (6 * Real.exp (-1) / ε)
    have he_pos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    refine ⟨N + 1, Nat.succ_pos _, ?_⟩
    have hN1_pos : (0 : ℝ) < (N + 1 : ℕ) := by exact_mod_cast Nat.succ_pos _
    rw [div_lt_iff₀ hN1_pos]
    have h1 : 6 * Real.exp (-1) / ε < (N + 1 : ℝ) := by
      have : (N : ℝ) < N + 1 := by linarith
      linarith
    rw [div_lt_iff₀ hε] at h1
    push_cast
    linarith
  rw [Filter.eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  simp only [Real.dist_eq]
  -- T_n = (1/n) Σ f(k/n)
  set T : ℝ := (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, f ((k : ℝ) / n) with hT_def
  set I : ℝ := ∫ x in (0 : ℝ)..1, f x with hI_def
  -- Compute T_n - I as sum of per-interval errors.
  have h_telescope : ∑ k ∈ Finset.Icc 1 n,
      ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x = I :=
    sum_integral_telescope n hn1 f hf_cts
  -- T - I = Σ (f(k/n)/n - ∫_{(k-1)/n}^{k/n} f)
  have hTI : T - I = ∑ k ∈ Finset.Icc 1 n,
      (f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x) := by
    rw [← h_telescope, Finset.sum_sub_distrib, hT_def]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros; ring
  -- Bound |T - I| using per-interval bounds.
  -- Let m = ⌊n * exp(-1)⌋, so m/n ≤ exp(-1) < (m+1)/n.
  have he_lt : Real.exp (-1) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have he_pos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  set m : ℕ := ⌊(n : ℝ) * Real.exp (-1)⌋₊ with hm_def
  have hm_le : (m : ℝ) ≤ (n : ℝ) * Real.exp (-1) := Nat.floor_le (by positivity)
  have hm_lt_n : m < n := by
    have : (m : ℝ) < (n : ℝ) := by
      calc (m : ℝ) ≤ n * Real.exp (-1) := hm_le
        _ < n * 1 := by gcongr
        _ = n := mul_one _
    exact_mod_cast this
  have hm_le_n : m ≤ n := hm_lt_n.le
  have h_mn_le : (m : ℝ) / n ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hn_pos]
    linarith
  have h_mn_plus_one_ge : Real.exp (-1) ≤ (m + 1 : ℝ) / n := by
    rw [le_div_iff₀ hn_pos]
    have := Nat.lt_floor_add_one ((n : ℝ) * Real.exp (-1))
    push_cast at this
    linarith
  -- Define helper g(k) = f(k/n) so we can telescope.
  let g : ℕ → ℝ := fun k => f ((k : ℝ) / n)
  -- Bound of |f| on [0, 1]
  have h_abs_g : ∀ k ∈ Finset.Icc 0 n, |g k| ≤ Real.exp (-1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    apply abs_mul_log_le
    · exact div_nonneg (by exact_mod_cast hk.1) hn_pos.le
    · rw [div_le_one hn_pos]; exact_mod_cast hk.2
  -- Antitone bound per term for k ∈ Icc 1 m
  have anti_bound : ∀ k ∈ Finset.Icc 1 m,
      |f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x|
      ≤ (g (k - 1) - g k) * (1/n) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk_ge : 1 ≤ k := hk.1
    have hk_le_m : k ≤ m := hk.2
    have h_a : (0 : ℝ) ≤ ((k - 1 : ℝ)/n) := by
      apply div_nonneg _ hn_pos.le
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk_ge
      linarith
    have h_ab : ((k - 1 : ℝ)/n) ≤ ((k : ℝ)/n) := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      linarith
    have h_b : ((k : ℝ)/n) ≤ Real.exp (-1) := by
      have : ((k : ℝ)/n) ≤ ((m : ℝ)/n) := by
        apply div_le_div_of_nonneg_right _ hn_pos.le
        exact_mod_cast hk_le_m
      linarith
    have h_anti_sub : AntitoneOn f (Set.Icc ((k - 1 : ℝ)/n) ((k : ℝ)/n)) :=
      antitoneOn_mul_log.mono (fun x hx => ⟨h_a.trans hx.1, hx.2.trans h_b⟩)
    have h_diff : ((k : ℝ)/n) - ((k - 1 : ℝ)/n) = 1/n := by
      field_simp; ring
    have h_bd := per_interval_bound_anti h_ab h_anti_sub (hf_cts.intervalIntegrable _ _)
    rw [h_diff] at h_bd
    have h_gk1 : g (k - 1) = f ((k - 1 : ℝ) / n) := by
      show f (((k - 1 : ℕ) : ℝ) / n) = f ((k - 1 : ℝ) / n)
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk_ge]; push_cast; ring
      rw [this]
    rw [h_gk1]
    exact h_bd
  -- Monotone bound per term for k ∈ Icc (m+2) n
  have mono_bound : ∀ k ∈ Finset.Icc (m + 2) n,
      |f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x|
      ≤ (g k - g (k - 1)) * (1/n) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk_ge : m + 2 ≤ k := hk.1
    have hk_le : k ≤ n := hk.2
    have h_a : ((k - 1 : ℝ)/n) ≥ Real.exp (-1) := by
      have h_n : (m + 1 : ℝ) ≤ (k - 1 : ℝ) := by
        have : ((m + 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
        push_cast at this
        linarith
      have h_div : ((m + 1 : ℝ)/n) ≤ ((k - 1 : ℝ)/n) :=
        div_le_div_of_nonneg_right h_n hn_pos.le
      linarith
    have h_ab : ((k - 1 : ℝ)/n) ≤ ((k : ℝ)/n) := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      linarith
    have h_b : ((k : ℝ)/n) ≤ 1 := by
      rw [div_le_one hn_pos]; exact_mod_cast hk_le
    have h_mono_sub : MonotoneOn f (Set.Icc ((k - 1 : ℝ)/n) ((k : ℝ)/n)) :=
      monotoneOn_mul_log.mono (fun x hx => ⟨h_a.trans hx.1, hx.2.trans h_b⟩)
    have h_diff : ((k : ℝ)/n) - ((k - 1 : ℝ)/n) = 1/n := by
      field_simp; ring
    have h_bd := per_interval_bound_mono h_ab h_mono_sub (hf_cts.intervalIntegrable _ _)
    rw [h_diff] at h_bd
    have hk_ge_1 : 1 ≤ k := by linarith
    have h_gk1 : g (k - 1) = f ((k - 1 : ℝ) / n) := by
      show f (((k - 1 : ℕ) : ℝ) / n) = f ((k - 1 : ℝ) / n)
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk_ge_1]; push_cast; ring
      rw [this]
    rw [h_gk1]
    exact h_bd
  -- Antitone part sum bound using telescope
  have anti_sum : ∑ k ∈ Finset.Icc 1 m, (g (k - 1) - g k) = g 0 - g m := by
    have h_icc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [h_icc, Finset.sum_Ico_eq_sum_range]
    have h_range : m + 1 - 1 = m := by omega
    rw [h_range]
    have : ∑ k ∈ Finset.range m, (g (1 + k - 1) - g (1 + k)) =
           ∑ k ∈ Finset.range m, (g k - g (k + 1)) := by
      apply Finset.sum_congr rfl
      intros i _
      congr 1
      · congr 1; omega
      · congr 1; omega
    rw [this]
    exact telescope_sub g m
  -- Monotone part sum bound using telescope (index shift)
  have mono_sum : ∑ k ∈ Finset.Icc (m + 2) n, (g k - g (k - 1)) = g n - g (m + 1) := by
    by_cases hcase : m + 2 ≤ n
    · have h_icc : Finset.Icc (m + 2) n = Finset.Ico (m + 2) (n + 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [h_icc, Finset.sum_Ico_eq_sum_range]
      have h_range : n + 1 - (m + 2) = n - (m + 1) := by omega
      rw [h_range]
      -- Σ_{i ∈ range (n - (m+1))} (g((m+2)+i) - g((m+2)+i-1)) = Σ (g(m+2+i) - g(m+1+i))
      have h_tele : ∑ i ∈ Finset.range (n - (m + 1)),
          (g (m + 2 + i) - g (m + 2 + i - 1)) = g n - g (m + 1) := by
        have h_eq : ∀ i, m + 2 + i - 1 = m + 1 + i := fun i => by omega
        have h_eq2 : ∀ i, m + 2 + i = (m + 1) + (i + 1) := fun i => by omega
        have key : ∑ i ∈ Finset.range (n - (m + 1)),
            (g (m + 1 + (i + 1)) - g (m + 1 + i)) = g n - g (m + 1) := by
          have := telescope_sub' (fun i => g (m + 1 + i)) (n - (m + 1))
          simp only [add_zero] at this
          have h_nm : m + 1 + (n - (m + 1)) = n := by omega
          rw [h_nm] at this
          convert this using 1
        calc ∑ i ∈ Finset.range (n - (m + 1)), (g (m + 2 + i) - g (m + 2 + i - 1))
            = ∑ i ∈ Finset.range (n - (m + 1)), (g (m + 1 + (i + 1)) - g (m + 1 + i)) := by
              apply Finset.sum_congr rfl
              intros i _
              rw [h_eq, h_eq2]
          _ = g n - g (m + 1) := key
      exact h_tele
    · rw [show Finset.Icc (m + 2) n = ∅ from by
        rw [Finset.Icc_eq_empty]; omega]
      simp
      have hn_le : n ≤ m + 1 := by omega
      -- But wait, m < n < m + 1 forces n = m... but m < n from hm_lt_n
      -- So m + 1 ≤ n. Combined with n ≤ m + 1 gives n = m + 1.
      have : n = m + 1 := by omega
      rw [this]
      simp
  -- Bridge bound: k = m + 1 if m + 1 ≤ n
  have bridge_k_in : m + 1 ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    refine ⟨Nat.succ_pos _, ?_⟩
    omega
  -- Bridge error bound
  have bridge_bound : |f (((m + 1 : ℕ) : ℝ) / n) * (1/n) -
      ∫ x in (((m + 1 : ℕ) - 1 : ℝ)/n)..(((m + 1 : ℕ) : ℝ)/n), f x| ≤
      2 * Real.exp (-1) * (1/n) := by
    have h_a : (0 : ℝ) ≤ ((m : ℝ)/n) := div_nonneg (by exact_mod_cast Nat.zero_le _) hn_pos.le
    have h_ab : ((m : ℝ)/n) ≤ ((m + 1 : ℝ)/n) := by
      apply div_le_div_of_nonneg_right _ hn_pos.le; linarith
    have h_b : ((m + 1 : ℝ)/n) ≤ 1 := by
      rw [div_le_one hn_pos]
      have : m + 1 ≤ n := by
        by_contra h
        push_neg at h
        omega
      exact_mod_cast this
    have h_diff : ((m + 1 : ℝ)/n) - ((m : ℝ)/n) = 1/n := by field_simp; ring
    have h_bd := per_interval_bridge h_a h_ab h_b
    rw [h_diff] at h_bd
    have h_rw_m_plus_1 : (((m + 1 : ℕ) : ℝ)) / (n : ℝ) = ((m + 1 : ℝ)) / n := by
      push_cast; rfl
    have h_rw_sub : (((m + 1 : ℕ) - 1 : ℝ)) / (n : ℝ) = (m : ℝ) / n := by
      have : ((m + 1 : ℕ) - 1 : ℝ) = (m : ℝ) := by push_cast; ring
      rw [this]
    rw [h_rw_m_plus_1, h_rw_sub]
    exact h_bd
  -- Combine: Σ |err| over Icc 1 n decomposes as Σ over (Icc 1 m) + {m+1} + Icc (m+2) n
  -- But only if m + 1 ≤ n. We have m < n so m + 1 ≤ n.
  have hm_plus_1_le_n : m + 1 ≤ n := hm_lt_n
  have h_split_sum : ∀ (h : ℕ → ℝ),
      ∑ k ∈ Finset.Icc 1 n, h k =
      (∑ k ∈ Finset.Icc 1 m, h k) + h (m + 1) + ∑ k ∈ Finset.Icc (m + 2) n, h k := by
    intro h
    have h_dec : Finset.Icc 1 n =
        Finset.Icc 1 m ∪ {m + 1} ∪ Finset.Icc (m + 2) n := by
      ext k; simp [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
    have h_disj1 : Disjoint (Finset.Icc 1 m) ({m + 1} : Finset ℕ) := by
      rw [Finset.disjoint_singleton_right]; simp [Finset.mem_Icc]
    have h_disj2 : Disjoint (Finset.Icc 1 m ∪ ({m + 1} : Finset ℕ)) (Finset.Icc (m + 2) n) := by
      rw [Finset.disjoint_union_left]
      refine ⟨?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro a ha hb
        simp [Finset.mem_Icc] at ha hb
        omega
      · rw [Finset.disjoint_singleton_left]
        simp [Finset.mem_Icc]
    rw [h_dec, Finset.sum_union h_disj2, Finset.sum_union h_disj1]
    simp
  -- Now bound |T - I|
  have h_bound : |T - I| ≤ 4 * Real.exp (-1) / n := by
    rw [hTI]
    calc |∑ k ∈ Finset.Icc 1 n,
          (f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x)|
        ≤ ∑ k ∈ Finset.Icc 1 n,
            |f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = (∑ k ∈ Finset.Icc 1 m,
            |f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x|)
          + |f (((m + 1 : ℕ) : ℝ) / n) * (1/n) -
              ∫ x in (((m + 1 : ℕ) - 1 : ℝ)/n)..(((m + 1 : ℕ) : ℝ)/n), f x|
          + ∑ k ∈ Finset.Icc (m + 2) n,
            |f ((k : ℝ) / n) * (1/n) - ∫ x in ((k - 1 : ℝ)/n)..((k : ℝ)/n), f x| :=
          h_split_sum _
      _ ≤ (∑ k ∈ Finset.Icc 1 m, (g (k - 1) - g k) * (1/n))
          + 2 * Real.exp (-1) * (1/n)
          + ∑ k ∈ Finset.Icc (m + 2) n, (g k - g (k - 1)) * (1/n) := by
          apply add_le_add
          apply add_le_add
          · exact Finset.sum_le_sum anti_bound
          · exact bridge_bound
          · exact Finset.sum_le_sum mono_bound
      _ = ((g 0 - g m) + (g n - g (m + 1))) * (1/n) + 2 * Real.exp (-1) * (1/n) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, anti_sum, mono_sum]
          ring
      _ ≤ (Real.exp (-1) + Real.exp (-1)) * (1/n) + 2 * Real.exp (-1) * (1/n) := by
          have hg0 : g 0 = 0 := by simp [g, f, hf_def]
          rw [hg0, zero_sub]
          have h_neg_gm : -g m ≤ Real.exp (-1) := by
            have h_abs : |g m| ≤ Real.exp (-1) :=
              h_abs_g m (by simp [Finset.mem_Icc]; exact hm_le_n)
            linarith [neg_abs_le (g m)]
          have h_diff : g n - g (m + 1) ≤ Real.exp (-1) := by
            have h1 : |g n| ≤ Real.exp (-1) := h_abs_g n (by simp [Finset.mem_Icc])
            have h2 : |g (m + 1)| ≤ Real.exp (-1) :=
              h_abs_g (m + 1) (by simp [Finset.mem_Icc]; omega)
            -- Actually g(1) = 1 log 1 = 0, but more generally let's use g n = 0
            -- Since n/n = 1 and f(1) = 0
            have hgn : g n = 0 := by
              simp [g, f, hf_def, hn_ne]
            rw [hgn, zero_sub]
            linarith [neg_abs_le (g (m + 1))]
          have h1nn : (0 : ℝ) ≤ 1/n := by positivity
          have := mul_le_mul_of_nonneg_right (add_le_add h_neg_gm h_diff) h1nn
          linarith
      _ = 4 * Real.exp (-1) / n := by
          field_simp
          ring
  have h_bound' : |T - I| ≤ 6 * Real.exp (-1) / n := by
    have : 4 * Real.exp (-1) / (n : ℝ) ≤ 6 * Real.exp (-1) / n := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have : (0 : ℝ) ≤ Real.exp (-1) := (Real.exp_pos _).le
      linarith
    linarith
  have : |T - I| < ε := by
    calc |T - I| ≤ 6 * Real.exp (-1) / n := h_bound'
      _ ≤ 6 * Real.exp (-1) / N := by
        apply div_le_div_of_nonneg_left (by positivity)
        · exact_mod_cast hN_pos
        · exact_mod_cast hnN
      _ < ε := hN_bd
  exact this

snip end

snip end

problem imc2024_p2 :
    Tendsto S atTop (𝓝 answer) := by
  unfold S answer
  -- Split: S n = (log n)/(2n) + (1/n) Σ_{k=1}^n (k/n) log(k/n)
  have hS_eq : ∀ n : ℕ, 1 ≤ n → (1 / (n : ℝ)^2) * ∑ k ∈ Finset.range (n + 1),
      (k : ℝ) * Real.log k - (1 / 2) * Real.log n =
      Real.log n / (2 * n) + (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n,
        ((k : ℝ) / n) * Real.log ((k : ℝ) / n) := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
    -- Σ_{k=0}^n k log k = Σ_{k=1}^n k log k (since k=0 contributes 0)
    have h_sum_eq : ∑ k ∈ Finset.range (n + 1), (k : ℝ) * Real.log k
                 = ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k := by
      rw [show Finset.Icc 1 n = Finset.range (n + 1) \ {0} by
        ext k; simp [Finset.mem_Icc, Finset.mem_range]; omega]
      rw [Finset.sum_sdiff_eq_sub (by simp)]
      simp
    rw [h_sum_eq]
    -- Σ k log k = Σ k (log(k/n) + log n) = Σ k log(k/n) + (Σ k) log n
    have h_split : ∀ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k =
        (k : ℝ) * Real.log ((k : ℝ) / n) + k * Real.log n := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk.1
      rw [Real.log_div hk_pos.ne' hn_ne]
      ring
    rw [Finset.sum_congr rfl h_split, Finset.sum_add_distrib]
    -- Σ_{k=1}^n k = n(n+1)/2
    have h_sum_k : ∑ k ∈ Finset.Icc 1 n, (k : ℝ) = n * (n + 1) / 2 := by
      have h1 : ∑ k ∈ Finset.Icc 1 n, (k : ℝ) = ∑ k ∈ Finset.range (n + 1), (k : ℝ) := by
        rw [show Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) by
          ext k; simp [Finset.mem_Icc, Finset.mem_range]; omega]
        rw [Finset.sum_insert (by simp)]
        simp
      rw [h1]
      have h2 : (∑ i ∈ Finset.range (n + 1), i) * 2 = (n + 1) * n :=
        Finset.sum_range_id_mul_two (n + 1)
      have h3 : ((∑ i ∈ Finset.range (n + 1), (i : ℝ))) * 2 = (n + 1 : ℝ) * n := by
        have h2' : ((∑ i ∈ Finset.range (n + 1), (i : ℕ) : ℕ) : ℝ) * 2 =
            (((n + 1) * n : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at h2'
        linarith
      linarith
    rw [show (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log n)
        = (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) * Real.log n from
      (Finset.sum_mul _ _ _).symm]
    rw [h_sum_k]
    have h_factor_n : ∀ k ∈ Finset.Icc 1 n,
        (k : ℝ) * Real.log ((k : ℝ) / n) = n * (((k : ℝ) / n) * Real.log ((k : ℝ) / n)) := by
      intro k hk
      field_simp
    rw [Finset.sum_congr rfl h_factor_n, ← Finset.mul_sum]
    field_simp
    ring
  have h_main : Tendsto (fun n : ℕ => Real.log n / (2 * n) + (1 / (n : ℝ)) *
      ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) / n) * Real.log ((k : ℝ) / n))
      atTop (𝓝 (-(1/4))) := by
    have := (tendsto_log_div_two_n.add tendsto_riemann_sum)
    simpa using this
  apply Tendsto.congr' _ h_main
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hS_eq n hn).symm

end Imc2024P2
