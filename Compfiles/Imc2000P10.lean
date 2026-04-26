/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 10 (Day 2, Problem 4)

Suppose the graph of a polynomial of degree `6` is tangent to a straight line
at three points `A₁, A₂, A₃`, where `A₂` lies between `A₁` and `A₃`.

(a) Prove that if the lengths of the segments `A₁A₂` and `A₂A₃` are equal,
then the areas of the figures bounded by these segments and the graph of the
polynomial are equal as well.

(b) Let `k = A₂A₃ / A₁A₂` and let `K` be the ratio of the appropriate areas.
Prove that `2/7 · k^5 < K < 7/2 · k^5`.

We follow the official solution. WLOG (by translation/rotation) the line is
`y = a₅ x` with `A₂` at the origin, so `A₁ = -a` and `A₃ = b` with `a, b > 0`.
Tangency at `±a, b` (double points) forces the polynomial to differ from the
line by `c · (x + a)² (x - b)² · x²` for some `c ≠ 0`. The area between the
graph and the line on `[-a, 0]` equals `|c| · ∫_{-a}^0 (x+a)²(x-b)² x² dx`,
and similarly on `[0, b]`. Direct integration gives the closed forms

  `∫_{-a}^0 (x+a)²(x-b)² x² dx = a^7 / 210 · (7k² + 7k + 2)`,
  `∫_{0}^{b} (x+a)²(x-b)² x² dx = a^7 / 210 · (2k² + 7k + 7)`,

where `k = b/a`. The ratio is `K = k^5 · (2k² + 7k + 7) / (7k² + 7k + 2)`,
and the rational factor decreases from `7/2` to `2/7` on `(0, ∞)`,
yielding the bounds.

We formalize the algebraic core: for `a, b > 0` and the integrand
`f(x) = (x + a)² (x - b)² x²`, we prove the two integral identities and
deduce both (a) (case `a = b`) and (b) (the strict bounds on the ratio).
-/

namespace Imc2000P10

open scoped intervalIntegral
open MeasureTheory

/-- The non-negative integrand `(x+a)²(x-b)² x²` whose integrals over the two
intervals give the bounded areas between the polynomial and the line. -/
noncomputable def f (a b x : ℝ) : ℝ := (x + a)^2 * (x - b)^2 * x^2

/-- An explicit antiderivative of `f a b`, computed by expanding the polynomial
and integrating term by term. We have

  `f a b x = x^6 + 2(a-b) x^5 + ((a-b)^2 - 2ab) x^4 - 2ab(a-b) x^3 + a²b² x^2`,

so `F a b x = x^7/7 + (a-b) x^6/3 + ((a-b)^2 - 2ab) x^5/5
              - ab(a-b) x^4/2 + a²b² x^3/3`. -/
noncomputable def F (a b x : ℝ) : ℝ :=
  x^7 / 7 + (a - b) * x^6 / 3 + ((a - b)^2 - 2 * a * b) * x^5 / 5
    - a * b * (a - b) * x^4 / 2 + a^2 * b^2 * x^3 / 3

snip begin

/-- `F a b` is a primitive of `f a b`. -/
lemma hasDerivAt_F (a b x : ℝ) : HasDerivAt (F a b) (f a b x) x := by
  unfold F f
  -- Compute derivative term by term.
  have h1 : HasDerivAt (fun x : ℝ => x^7 / 7) (x^6) x := by
    have := (hasDerivAt_pow 7 x).div_const 7
    simpa [show ((7 : ℕ) : ℝ) = 7 from rfl] using this
  have h2 : HasDerivAt (fun x : ℝ => (a - b) * x^6 / 3) (2 * (a - b) * x^5) x := by
    have hp : HasDerivAt (fun x : ℝ => x^6) (6 * x^5) x := by
      simpa using hasDerivAt_pow 6 x
    have := (hp.const_mul (a - b)).div_const 3
    convert this using 1; ring
  have h3 : HasDerivAt (fun x : ℝ => ((a - b)^2 - 2 * a * b) * x^5 / 5)
      (((a - b)^2 - 2 * a * b) * x^4) x := by
    have hp : HasDerivAt (fun x : ℝ => x^5) (5 * x^4) x := by
      simpa using hasDerivAt_pow 5 x
    have := (hp.const_mul ((a - b)^2 - 2 * a * b)).div_const 5
    convert this using 1; ring
  have h4 : HasDerivAt (fun x : ℝ => a * b * (a - b) * x^4 / 2)
      (2 * a * b * (a - b) * x^3) x := by
    have hp : HasDerivAt (fun x : ℝ => x^4) (4 * x^3) x := by
      simpa using hasDerivAt_pow 4 x
    have := (hp.const_mul (a * b * (a - b))).div_const 2
    convert this using 1; ring
  have h5 : HasDerivAt (fun x : ℝ => a^2 * b^2 * x^3 / 3) (a^2 * b^2 * x^2) x := by
    have hp : HasDerivAt (fun x : ℝ => x^3) (3 * x^2) x := by
      simpa using hasDerivAt_pow 3 x
    have := (hp.const_mul (a^2 * b^2)).div_const 3
    convert this using 1; ring
  have hsum := ((((h1.add h2).add h3).sub h4).add h5)
  convert hsum using 1
  ring

lemma f_continuous (a b : ℝ) : Continuous (f a b) := by
  unfold f
  exact ((continuous_id.add continuous_const).pow 2).mul
    ((continuous_id.sub continuous_const).pow 2) |>.mul (continuous_pow 2)

/-- Closed form: `∫_{-a}^0 (x+a)² (x-b)² x² dx = a^7 (7k² + 7k + 2) / 210`
where `k = b/a`. We state it equivalently without the substitution. -/
lemma integral_left_eq (a b : ℝ) :
    ∫ x in (-a)..0, f a b x =
      (7 * a^5 * b^2 + 7 * a^6 * b + 2 * a^7) / 210 := by
  have hint : IntervalIntegrable (f a b) volume (-a) 0 :=
    (f_continuous a b).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_F a b x) hint]
  unfold F
  ring

/-- Closed form: `∫_{0}^{b} (x+a)² (x-b)² x² dx = (2b⁷ + 7ab⁶ + 7a²b⁵) / 210`. -/
lemma integral_right_eq (a b : ℝ) :
    ∫ x in (0 : ℝ)..b, f a b x =
      (2 * b^7 + 7 * a * b^6 + 7 * a^2 * b^5) / 210 := by
  have hint : IntervalIntegrable (f a b) volume 0 b :=
    (f_continuous a b).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hasDerivAt_F a b x) hint]
  unfold F
  ring

/-- Positivity of the left integral when `a > 0`. -/
lemma integral_left_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < ∫ x in (-a)..0, f a b x := by
  rw [integral_left_eq]
  have h7 : (0 : ℝ) < 210 := by norm_num
  rw [lt_div_iff₀ h7, zero_mul]
  have h1 : 0 < 7 * a^5 * b^2 := by positivity
  have h2 : 0 < 7 * a^6 * b := by positivity
  have h3 : 0 < 2 * a^7 := by positivity
  linarith

/-- Positivity of the right integral when `b > 0`. -/
lemma integral_right_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < ∫ x in (0 : ℝ)..b, f a b x := by
  rw [integral_right_eq]
  have h7 : (0 : ℝ) < 210 := by norm_num
  rw [lt_div_iff₀ h7, zero_mul]
  have h1 : 0 < 2 * b^7 := by positivity
  have h2 : 0 < 7 * a * b^6 := by positivity
  have h3 : 0 < 7 * a^2 * b^5 := by positivity
  linarith

/-- Part (a): when `a = b`, the two integrals are equal. -/
lemma integral_eq_of_eq (a : ℝ) :
    ∫ x in (-a)..0, f a a x = ∫ x in (0 : ℝ)..a, f a a x := by
  rw [integral_left_eq, integral_right_eq]
  ring

/-- The polynomial-factor inequality:
for `0 < k`, the rational function `(2k²+7k+7)/(7k²+7k+2)` lies strictly
between `2/7` and `7/2`. -/
lemma rational_factor_bounds {k : ℝ} (hk : 0 < k) :
    2/7 < (2 * k^2 + 7 * k + 7) / (7 * k^2 + 7 * k + 2) ∧
    (2 * k^2 + 7 * k + 7) / (7 * k^2 + 7 * k + 2) < 7/2 := by
  have hden_pos : 0 < 7 * k^2 + 7 * k + 2 := by positivity
  refine ⟨?_, ?_⟩
  · -- 2/7 < (2k²+7k+7)/(7k²+7k+2)
    -- Equivalent to 2 (7k²+7k+2) < 7 (2k²+7k+7), i.e. 14k²+14k+4 < 14k²+49k+49.
    rw [lt_div_iff₀ hden_pos]
    nlinarith [sq_nonneg k, hk]
  · -- (2k²+7k+7)/(7k²+7k+2) < 7/2
    rw [div_lt_iff₀ hden_pos]
    nlinarith [sq_nonneg k, hk]

/-- The ratio `K = right / left = k^5 · (2k²+7k+7) / (7k²+7k+2)`. -/
lemma ratio_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..b, f a b x) / (∫ x in (-a)..0, f a b x) =
      (b/a)^5 * ((2 * (b/a)^2 + 7 * (b/a) + 7) / (7 * (b/a)^2 + 7 * (b/a) + 2)) := by
  rw [integral_left_eq, integral_right_eq]
  have ha' : a ≠ 0 := ne_of_gt ha
  have ha2 : a^2 ≠ 0 := pow_ne_zero _ ha'
  have ha5 : a^5 ≠ 0 := pow_ne_zero _ ha'
  have ha7 : a^7 ≠ 0 := pow_ne_zero _ ha'
  have hden_a : (0 : ℝ) < 7 * a^5 * b^2 + 7 * a^6 * b + 2 * a^7 := by positivity
  have hden_a_ne : (7 * a^5 * b^2 + 7 * a^6 * b + 2 * a^7) ≠ 0 := ne_of_gt hden_a
  have hden_k : (0 : ℝ) < 7 * (b/a)^2 + 7 * (b/a) + 2 := by positivity
  have hden_k_ne : (7 * (b/a)^2 + 7 * (b/a) + 2) ≠ 0 := ne_of_gt hden_k
  -- Direct: clear denominators via field_simp then verify by ring.
  field_simp

snip end

/-- Part (a): if `|A₁A₂| = |A₂A₃|` (i.e. `a = b`), the bounded areas are equal. -/
problem imc2000_p10_a (a : ℝ) (_ha : 0 < a) :
    ∫ x in (-a)..0, f a a x = ∫ x in (0 : ℝ)..a, f a a x :=
  integral_eq_of_eq a

/-- Part (b): for the bounded areas associated with `a, b > 0` and `k = b/a`,
the ratio `K` of the two bounded areas satisfies `2/7 · k^5 < K < 7/2 · k^5`. -/
problem imc2000_p10_b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let K := (∫ x in (0 : ℝ)..b, f a b x) / (∫ x in (-a)..0, f a b x)
    let k := b / a
    2/7 * k^5 < K ∧ K < 7/2 * k^5 := by
  intro K k
  have hk_pos : 0 < k := div_pos hb ha
  have hk5_pos : 0 < k^5 := by positivity
  have hratio : K = k^5 * ((2 * k^2 + 7 * k + 7) / (7 * k^2 + 7 * k + 2)) := by
    show (∫ x in (0 : ℝ)..b, f a b x) / (∫ x in (-a)..0, f a b x) = _
    exact ratio_eq ha hb
  obtain ⟨hlow, hupp⟩ := rational_factor_bounds hk_pos
  refine ⟨?_, ?_⟩
  · rw [hratio]
    have heq : 2/7 * k^5 = k^5 * (2/7) := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_left hlow hk5_pos
  · rw [hratio]
    have heq : 7/2 * k^5 = k^5 * (7/2) := by ring
    rw [heq]
    exact mul_lt_mul_of_pos_left hupp hk5_pos

end Imc2000P10
