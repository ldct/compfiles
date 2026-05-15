/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 3 (Day 1)

Let `f(x) = 2 x (1 - x)` and `f_n = f ∘ … ∘ f` (n-fold iterate).

(a) Find `lim_n ∫_0^1 f_n`.

(b) Compute `∫_0^1 f_n` for each `n ≥ 1`.

## Answers

(a) `lim_n ∫_0^1 f_n = 1/2`.

(b) `∫_0^1 f_n = 1/2 - 1/(2(2^n + 1))`.

## Solution sketch

The key identity is the closed form:

  `f_n(x) = 1/2 - 2^(2^n - 1) · (x - 1/2)^(2^n)`     (★)

(proved by induction on `n ≥ 1`). Integrating over `[0, 1]` and using
`∫_0^1 (x - 1/2)^(2^n) dx = 2/(2^n + 1) · (1/2)^(2^n + 1) = 1/((2^n + 1) · 2^(2^n))`,
we get

  `∫_0^1 f_n = 1/2 - 2^(2^n - 1) · 1/((2^n + 1) · 2^(2^n))
            = 1/2 - 1/(2 (2^n + 1))`.

Part (a) follows by letting `n → ∞`: `2 (2^n + 1) → ∞`, so
`1/(2(2^n + 1)) → 0`.
-/

namespace Imc1998P3

open MeasureTheory intervalIntegral Set Real

/-- The map `f(x) = 2 x (1 - x)`. -/
noncomputable def f (x : ℝ) : ℝ := 2 * x * (1 - x)

/-- The `n`-fold iterate `f_n = f ∘ … ∘ f`. -/
noncomputable def fIter : ℕ → ℝ → ℝ
  | 0     => id
  | n + 1 => fIter n ∘ f

/-- The closed-form value of `∫_0^1 f_n` for `n ≥ 1`. -/
noncomputable def intAnswer (n : ℕ) : ℝ := 1/2 - 1 / (2 * (2 ^ n + 1))

snip begin

/-- The closed-form expression that we will prove equals `f_n(x)` for `n ≥ 1`:
`closedForm n x = 1/2 - 2^(2^n - 1) · (x - 1/2)^(2^n)`. -/
noncomputable def closedForm (n : ℕ) (x : ℝ) : ℝ :=
  1/2 - (2 : ℝ) ^ (2 ^ n - 1) * (x - 1/2) ^ (2 ^ n)

/-- Helper: `f x = 1/2 - 2 (x - 1/2)^2`, which is the `n = 1` case of the
closed form. -/
lemma f_eq (x : ℝ) : f x = 1/2 - 2 * (x - 1/2) ^ 2 := by
  unfold f; ring

/-- The induction step:
`closedForm (k+1) x = closedForm k (f x)`. -/
lemma closedForm_succ (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    closedForm (k + 1) x = closedForm k (f x) := by
  unfold closedForm
  -- closedForm k (f x) = 1/2 - 2^(2^k - 1) * (f x - 1/2)^(2^k)
  have hfx : f x - 1/2 = -(2 * (x - 1/2)^2) := by rw [f_eq]; ring
  rw [hfx]
  congr 1
  have h2k_pos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  have h2k_even : Even (2 ^ k) := by
    refine ⟨2 ^ (k - 1), ?_⟩
    conv_lhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ]; ring
  rw [Even.neg_pow h2k_even]
  rw [mul_pow, ← pow_mul]
  -- Goal: 2^(2^(k+1) - 1) * (x - 1/2)^(2^(k+1))
  --     = 2^(2^k - 1) * (2^(2^k) * (x - 1/2)^(2 * 2^k))
  have hk1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hkk1 : (2 : ℕ) ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
    rw [hk1]; omega
  have hmul : 2 * (2 : ℕ) ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
  rw [hmul, hkk1, pow_add]
  ring

/-- The closed-form identity: `f_n(x) = 1/2 - 2^(2^n - 1) (x - 1/2)^(2^n)` for `n ≥ 1`. -/
lemma fIter_eq_closedForm : ∀ n : ℕ, 1 ≤ n → ∀ x, fIter n x = closedForm n x
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, x => by
      simp [fIter, closedForm, f_eq]
  | n + 2, _, x => by
      have hn1 : 1 ≤ n + 1 := by omega
      -- fIter (n+2) x = fIter (n+1) (f x)
      show fIter (n + 1) (f x) = closedForm (n + 2) x
      rw [fIter_eq_closedForm (n + 1) hn1 (f x)]
      rw [closedForm_succ (n + 1) hn1 x]

/-- The integrand `(x - 1/2)^k` integrated over `[0, 1]` equals
`1/((k+1) * 2^k)` for even `k`. -/
lemma integral_pow_centered (k : ℕ) (hk : Even k) :
    ∫ x in (0:ℝ)..1, (x - 1/2) ^ k = 1 / ((k + 1) * 2 ^ k) := by
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (y - 1/2)^(k+1) / ((k : ℝ)+1))
                  ((x - 1/2)^k) x := by
    intro x
    have h_xs : HasDerivAt (fun y : ℝ => y - 1/2) (1 : ℝ) x := by
      simpa using (hasDerivAt_id x).sub_const (1/2 : ℝ)
    have hd : HasDerivAt (fun y : ℝ => (y - 1/2)^(k+1))
                (((k:ℝ)+1) * (x - 1/2)^k) x := by
      have hp := h_xs.pow (k+1)
      have heq : ((((k:ℕ)+1 : ℕ) : ℝ)) * (x - 1/2)^((k+1) - 1) * 1
                  = ((k:ℝ)+1) * (x - 1/2)^k := by
        push_cast; simp
      have : (fun y : ℝ => (y - 1/2)^(k+1)) = (fun y : ℝ => y - 1/2)^(k+1) := by
        funext y; simp [Pi.pow_apply]
      rw [this, ← heq]; exact hp
    have hd3 := hd.div_const ((k:ℝ)+1)
    convert hd3 using 1
    field_simp
  have hcont : IntervalIntegrable (fun x : ℝ => (x - 1/2)^k) volume 0 1 := by
    apply Continuous.intervalIntegrable; continuity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
                (f := fun x => (x - 1/2)^(k+1) / ((k:ℝ)+1))
                (f' := fun x => (x - 1/2)^k)
                (a := (0 : ℝ)) (b := 1)
                (fun x _ => hderiv x) hcont
  rw [hFTC]
  -- Now goal involves explicit (1 - 1/2)^(k+1) and (0 - 1/2)^(k+1)
  have heven_succ : Odd (k + 1) := Even.add_one hk
  -- Reduce the function applications to expression form.
  show ((1 : ℝ) - 1/2)^(k+1) / ((k:ℝ)+1) - ((0 : ℝ) - 1/2)^(k+1) / ((k:ℝ)+1)
        = 1 / (((k:ℝ) + 1) * 2 ^ k)
  have h01 : ((1 : ℝ) - 1/2) = 1/2 := by ring
  have h02 : ((0 : ℝ) - 1/2) = -(1/2) := by ring
  rw [h01, h02, Odd.neg_pow heven_succ]
  have h21 : ((1/2 : ℝ))^(k+1) / ((k:ℝ)+1) - -(1/2)^(k+1) / ((k:ℝ)+1)
              = (1/2)^k / ((k:ℝ)+1) := by
    rw [pow_succ]; field_simp; ring
  rw [h21]
  have hpow : ((1/2 : ℝ))^k = 1 / 2^k := by rw [div_pow, one_pow]
  rw [hpow]
  have h2pos : (0 : ℝ) < (2 : ℝ)^k := by positivity
  field_simp

/-- The integral of the closed form. -/
lemma integral_closedForm (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..1, closedForm n x = intAnswer n := by
  unfold closedForm intAnswer
  set k : ℕ := 2 ^ n with hk_def
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (by simp [hk_def])
  have hk_ge : 2 ≤ k := by
    rw [hk_def]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hk_even : Even k := by
    refine ⟨2 ^ (n - 1), ?_⟩
    conv_lhs => rw [hk_def, show n = (n - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have hcont1 : IntervalIntegrable (fun _ : ℝ => (1/2 : ℝ)) volume 0 1 := by
    apply Continuous.intervalIntegrable; continuity
  have hcont2 : IntervalIntegrable
        (fun x : ℝ => (2:ℝ)^(k - 1) * (x - 1/2)^k) volume 0 1 := by
    apply Continuous.intervalIntegrable; continuity
  rw [intervalIntegral.integral_sub hcont1 hcont2]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_pow_centered k hk_even]
  rw [intervalIntegral.integral_const]
  -- Goal: (1 - 0) • (1/2) - 2^(k-1) * (1 / ((k+1) * 2^k)) = 1/2 - 1 / (2 * (2^n + 1))
  have hk_real : ((k : ℝ)) = (2 : ℝ)^n := by
    rw [hk_def]; push_cast; rfl
  -- Simplify 2^(k-1) * 1/((k+1) * 2^k) = 1/(2*(k+1))
  have h2pow : (2 : ℝ) ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ]
  have h2pos : (0 : ℝ) < (2:ℝ)^(k-1) := by positivity
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [h2pow, hk_real]
  field_simp
  ring

/-- Therefore, for `n ≥ 1`, the integral has the closed form. -/
lemma integral_fIter (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..1, fIter n x = intAnswer n := by
  have hext : ∀ x ∈ Set.Ioo (0 : ℝ) 1, fIter n x = closedForm n x := by
    intro x _; exact fIter_eq_closedForm n hn x
  -- Use that fIter and closedForm agree pointwise (everywhere actually).
  have hext' : ∀ x, fIter n x = closedForm n x := fun x =>
    fIter_eq_closedForm n hn x
  have : (fun x => fIter n x) = fun x => closedForm n x := funext hext'
  rw [this]
  exact integral_closedForm n hn

/-- The limit `1/(2(2^n + 1)) → 0` as `n → ∞`. -/
lemma tendsto_inv_two_pow :
    Filter.Tendsto (fun n : ℕ => 1 / (2 * ((2 : ℝ) ^ n + 1))) Filter.atTop
        (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h3 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 h1
  have h2 : Filter.Tendsto (fun n : ℕ => 2 * ((2 : ℝ) ^ n + 1))
              Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h3
  have h4 : Filter.Tendsto (fun n : ℕ => (2 * ((2 : ℝ) ^ n + 1))⁻¹) Filter.atTop
              (nhds 0) := h2.inv_tendsto_atTop
  exact h4.congr (fun n => (one_div _).symm)

snip end

/-- Part (b): closed form for `∫_0^1 f_n` (for `n ≥ 1`). -/
problem imc1998_p3b (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..1, fIter n x = 1/2 - 1 / (2 * (2 ^ n + 1)) := by
  have := integral_fIter n hn
  unfold intAnswer at this
  exact this

/-- Part (a): the limit of the integral is `1/2`. -/
problem imc1998_p3a :
    Filter.Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..1, fIter n x) Filter.atTop
      (nhds (1/2 : ℝ)) := by
  -- For n ≥ 1: ∫_0^1 f_n = 1/2 - 1/(2(2^n+1)) → 1/2.
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      1/2 - 1 / (2 * ((2 : ℝ) ^ n + 1)) = ∫ x in (0:ℝ)..1, fIter n x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hb := imc1998_p3b n hn
    linarith
  refine Filter.Tendsto.congr' hev ?_
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / (2 * ((2 : ℝ) ^ n + 1))) Filter.atTop
              (nhds 0) := tendsto_inv_two_pow
  have hg : Filter.Tendsto (fun n : ℕ => (1/2 : ℝ) - 1 / (2 * ((2 : ℝ) ^ n + 1)))
              Filter.atTop (nhds ((1/2 : ℝ) - 0)) :=
    (tendsto_const_nhds (x := (1/2 : ℝ))).sub h0
  simpa using hg

end Imc1998P3
