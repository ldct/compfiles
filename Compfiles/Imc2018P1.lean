/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 1

Let `(aₙ), (bₙ)` be sequences of positive numbers. Show the equivalence of:
* (1) There exists a sequence `(cₙ)` of positive numbers such that
      `∑ aₙ/cₙ` and `∑ cₙ/bₙ` both converge.
* (2) `∑ √(aₙ/bₙ)` converges.
-/

namespace Imc2018P1

snip begin

/-- AM-GM for two nonnegative reals: `√(x y) ≤ (x + y)/2`. -/
lemma sqrt_mul_le_add_div_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x * y) ≤ (x + y) / 2 := by
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hsq : Real.sqrt (x * y) ^ 2 ≤ ((x + y) / 2) ^ 2 := by
    rw [Real.sq_sqrt hxy]; nlinarith [sq_nonneg (x - y)]
  have hnn : 0 ≤ (x + y) / 2 := by linarith
  nlinarith [hsq, Real.sqrt_nonneg (x * y),
             sq_nonneg (Real.sqrt (x * y) - (x + y) / 2)]

/-- For positive `a, b`: `a / √(a b) = √(a / b)`. -/
lemma a_div_sqrt_ab (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / Real.sqrt (a * b) = Real.sqrt (a / b) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hsab : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr hab
  have hb_ne : (b : ℝ) ≠ 0 := hb.ne'
  have hab_ne : (a * b : ℝ) ≠ 0 := hab.ne'
  have hlhs_nn : 0 ≤ a / Real.sqrt (a * b) := div_nonneg ha.le hsab.le
  -- Show (a / √(a b))² = a / b.
  have hsq : (a / Real.sqrt (a * b)) ^ 2 = a / b := by
    rw [div_pow, Real.sq_sqrt hab.le]
    field_simp
  rw [← Real.sqrt_sq hlhs_nn, hsq]

/-- For positive `a, b`: `√(a b) / b = √(a / b)`. -/
lemma sqrt_ab_div_b (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) / b = Real.sqrt (a / b) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hsab_nn : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have hlhs_nn : 0 ≤ Real.sqrt (a * b) / b := div_nonneg hsab_nn hb.le
  have hb_ne : (b : ℝ) ≠ 0 := hb.ne'
  have hsq : (Real.sqrt (a * b) / b) ^ 2 = a / b := by
    rw [div_pow, Real.sq_sqrt hab.le]
    field_simp
  rw [← Real.sqrt_sq hlhs_nn, hsq]

snip end

problem imc2018_p1 (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) :
    (∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        Summable (fun n => a n / c n) ∧ Summable (fun n => c n / b n)) ↔
    Summable (fun n => Real.sqrt (a n / b n)) := by
  constructor
  · -- (1) ⟹ (2): √(aₙ/bₙ) ≤ (aₙ/cₙ + cₙ/bₙ)/2.
    rintro ⟨c, hc, h1, h2⟩
    have hsum : Summable (fun n => (a n / c n + c n / b n) / 2) :=
      (h1.add h2).div_const 2
    refine Summable.of_nonneg_of_le (fun n => Real.sqrt_nonneg _) ?_ hsum
    intro n
    have hacn : 0 ≤ a n / c n := div_nonneg (ha n).le (hc n).le
    have hcbn : 0 ≤ c n / b n := div_nonneg (hc n).le (hb n).le
    have hc_ne : c n ≠ 0 := (hc n).ne'
    have hb_ne : b n ≠ 0 := (hb n).ne'
    have hprod : (a n / c n) * (c n / b n) = a n / b n := by
      field_simp
    have hrewrite : Real.sqrt (a n / b n) = Real.sqrt ((a n / c n) * (c n / b n)) := by
      rw [hprod]
    rw [hrewrite]
    exact sqrt_mul_le_add_div_two hacn hcbn
  · -- (2) ⟹ (1): Take cₙ = √(aₙ bₙ); then aₙ/cₙ = cₙ/bₙ = √(aₙ/bₙ).
    intro hsum
    refine ⟨fun n => Real.sqrt (a n * b n), ?_, ?_, ?_⟩
    · intro n; exact Real.sqrt_pos.mpr (mul_pos (ha n) (hb n))
    · have hcongr : (fun n => a n / Real.sqrt (a n * b n)) =
          (fun n => Real.sqrt (a n / b n)) := by
        funext n; exact a_div_sqrt_ab (a n) (b n) (ha n) (hb n)
      rw [hcongr]; exact hsum
    · have hcongr : (fun n => Real.sqrt (a n * b n) / b n) =
          (fun n => Real.sqrt (a n / b n)) := by
        funext n; exact sqrt_ab_div_b (a n) (b n) (ha n) (hb n)
      rw [hcongr]; exact hsum

end Imc2018P1
