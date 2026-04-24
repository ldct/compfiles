/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 7

Let `a₀ = 0` and `a_{n+1}³ = a_n² - 8`. Prove that the series
`∑ₙ |a_{n+1} - a_n|` converges.
-/

namespace Imc2018P7

open scoped BigOperators

snip begin

/-- Cube root of 4 is positive. -/
lemma cbrt4_pos : 0 < (4 : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _

/-- `(4^(1/3))^3 = 4`. -/
lemma cbrt4_cube : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 4 := by
  rw [← Real.rpow_natCast ((4 : ℝ) ^ ((1 : ℝ) / 3)) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- `(4^(1/3))² = 4^(2/3)`, and this is at least `(4^(1/3))² ≥ 2` (actually equals `4^(2/3) ≈ 2.52`). -/
lemma cbrt4_sq_ge : (2 : ℝ) ≤ ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
  -- (4^(1/3))^2 = 4^(2/3). We have 4^(2/3) ≥ 2 iff (4^(2/3))^3 ≥ 8, i.e., 4^2 = 16 ≥ 8. Yes.
  have h1 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (4 : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num : (4 : ℝ) ≥ 0)]
    norm_num
  rw [h1]
  -- Show 2 ≤ 4^(2/3) by cubing: 8 ≤ 16.
  have h2 : (2 : ℝ) ^ 3 ≤ ((4 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 := by
    rw [← Real.rpow_natCast ((4 : ℝ) ^ _) 3, ← Real.rpow_mul (by norm_num : (4 : ℝ) ≥ 0)]
    norm_num
  nlinarith [Real.rpow_nonneg (by norm_num : (4 : ℝ) ≥ 0) ((2 : ℝ) / 3),
             sq_nonneg ((4 : ℝ) ^ ((2 : ℝ) / 3) - 2)]

/-- Cube of `-(4^(1/3))` is `-4`. -/
lemma neg_cbrt4_cube : (-((4 : ℝ) ^ ((1 : ℝ) / 3))) ^ 3 = -4 := by
  rw [neg_pow, cbrt4_cube]
  norm_num

/-- Cube function is strictly monotone on reals. -/
lemma cube_strictMono : StrictMono (fun x : ℝ => x ^ 3) :=
  Odd.strictMono_pow ⟨1, rfl⟩

/-- `x^3 ≤ y^3 ↔ x ≤ y` over reals. -/
lemma cube_le_cube_iff (x y : ℝ) : x ^ 3 ≤ y ^ 3 ↔ x ≤ y :=
  cube_strictMono.le_iff_le

/-- If `x^3 = y`, then `x` is uniquely determined. -/
lemma cube_eq_cube (x y : ℝ) : x ^ 3 = y ^ 3 → x = y := by
  intro h
  have h1 : x ≤ y := (cube_le_cube_iff x y).mp h.le
  have h2 : y ≤ x := (cube_le_cube_iff y x).mp h.ge
  linarith

/-- The ratio bound `r = 4^(1/3) / 3 < 1`. -/
lemma ratio_lt_one : (4 : ℝ) ^ ((1 : ℝ) / 3) / 3 < 1 := by
  have h : (4 : ℝ) ^ ((1 : ℝ) / 3) < 3 := by
    have h2 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < 3 ^ 3 := by rw [cbrt4_cube]; norm_num
    nlinarith [cbrt4_pos, sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3) - 3),
               sq_nonneg ((4 : ℝ) ^ ((1 : ℝ) / 3) + 3)]
  linarith

lemma ratio_nonneg : (0 : ℝ) ≤ (4 : ℝ) ^ ((1 : ℝ) / 3) / 3 := by
  have := cbrt4_pos
  positivity

snip end

problem imc2018_p7 (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (hrec : ∀ n, (a (n + 1)) ^ 3 = (a n) ^ 2 - 8) :
    Summable (fun n => |a (n + 1) - a n|) := by
  -- Step 1: a 1 = -2.
  have ha1 : a 1 = -2 := by
    have h := hrec 0
    rw [ha0] at h
    -- a(1)^3 = 0 - 8 = -8
    have h8 : (a 1) ^ 3 = (-2) ^ 3 := by rw [h]; norm_num
    exact cube_eq_cube _ _ h8
  -- Step 2: bounds for n ≥ 1: -2 ≤ a n ≤ -4^(1/3).
  set C : ℝ := (4 : ℝ) ^ ((1 : ℝ) / 3) with hC_def
  have hC_pos : 0 < C := cbrt4_pos
  have hC_cube : C ^ 3 = 4 := cbrt4_cube
  have hC_sq : 2 ≤ C ^ 2 := cbrt4_sq_ge
  -- Prove by induction: for all n ≥ 1, -2 ≤ a n ∧ a n ≤ -C.
  have hbounds : ∀ n : ℕ, -2 ≤ a (n + 1) ∧ a (n + 1) ≤ -C := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [ha1]
      · rw [ha1]
        -- -2 ≤ -C iff C ≤ 2, i.e., C^3 ≤ 8, i.e., 4 ≤ 8.
        have hC_le_2 : C ≤ 2 := by
          have h2 : C ^ 3 ≤ 2 ^ 3 := by rw [hC_cube]; norm_num
          exact (cube_le_cube_iff C 2).mp h2
        linarith
    | succ n ih =>
      obtain ⟨hL, hU⟩ := ih
      -- a(n+1) ∈ [-2, -C]. So a(n+1)^2 ∈ [C^2, 4].
      -- (a(n+1))^2 = |a(n+1)|^2, and |a(n+1)| ∈ [C, 2].
      have habs_bound : C ≤ |a (n + 1)| ∧ |a (n + 1)| ≤ 2 := by
        rw [abs_of_nonpos (by linarith [hC_pos.le])]
        exact ⟨by linarith, by linarith⟩
      have habs_sq : C ^ 2 ≤ (a (n + 1)) ^ 2 ∧ (a (n + 1)) ^ 2 ≤ 4 := by
        obtain ⟨hL', hU'⟩ := habs_bound
        have hsq_eq : (a (n + 1)) ^ 2 = |a (n + 1)| ^ 2 := (sq_abs _).symm
        rw [hsq_eq]
        refine ⟨?_, ?_⟩
        · exact pow_le_pow_left₀ hC_pos.le hL' 2
        · calc |a (n + 1)| ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hU' 2
            _ = 4 := by norm_num
      -- Now (a (n+2))^3 = a(n+1)^2 - 8 ∈ [C^2 - 8, -4].
      have hrec' := hrec (n + 1)
      obtain ⟨hsqL, hsqU⟩ := habs_sq
      have hcube_L : -8 ≤ (a (n + 1 + 1)) ^ 3 := by
        rw [hrec']
        linarith
      have hcube_U : (a (n + 1 + 1)) ^ 3 ≤ -4 := by
        rw [hrec']
        linarith
      -- So a(n+2) ∈ [-2, -C].
      refine ⟨?_, ?_⟩
      · -- (-2)^3 = -8 ≤ a(n+2)^3, so -2 ≤ a(n+2).
        have h : (-(2 : ℝ)) ^ 3 ≤ (a (n + 1 + 1)) ^ 3 := by norm_num; linarith
        exact (cube_le_cube_iff _ _).mp h
      · -- a(n+2)^3 ≤ -4 = (-C)^3.
        have hneg_C_cube : (-C) ^ 3 = -4 := by
          have : (-C) ^ 3 = - (C ^ 3) := by ring
          rw [this, hC_cube]
        have h : (a (n + 1 + 1)) ^ 3 ≤ (-C) ^ 3 := by rw [hneg_C_cube]; linarith
        exact (cube_le_cube_iff _ _).mp h
  -- Step 3: Contraction inequality. For all n ≥ 1,
  -- |a(n+2) - a(n+1)| ≤ (C/3) * |a(n+1) - a(n)|.
  set r : ℝ := C / 3 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; positivity
  have hr_lt_one : r < 1 := ratio_lt_one
  -- Key contraction: for n ≥ 1:
  -- a(n+2)^3 - a(n+1)^3 = a(n+1)^2 - a(n)^2
  -- (a(n+2) - a(n+1)) * (a(n+2)^2 + a(n+2)*a(n+1) + a(n+1)^2) = (a(n+1) - a(n))*(a(n+1) + a(n))
  have hcontract : ∀ n, |a (n + 2 + 1) - a (n + 2)| ≤ r * |a (n + 2) - a (n + 1)| := by
    intro n
    -- Use bounds for a(n+1), a(n+2), a(n+3). Note: n+1, n+2, n+3 ≥ 1.
    -- hbounds k gives bounds for a (k+1). So we use hbounds n, hbounds (n+1), hbounds (n+2).
    obtain ⟨hL1, hU1⟩ := hbounds n       -- bounds for a(n+1)
    obtain ⟨hL2, hU2⟩ := hbounds (n + 1) -- bounds for a(n+2)
    obtain ⟨hL3, hU3⟩ := hbounds (n + 2) -- bounds for a(n+3)
    have hC_le_2 : C ≤ 2 := by
      have h2 : C ^ 3 ≤ 2 ^ 3 := by rw [hC_cube]; norm_num
      exact (cube_le_cube_iff C 2).mp h2
    -- n+2+1 = n+3, n+1+1 = n+2. Just rewrite.
    show |a (n + 3) - a (n + 2)| ≤ r * |a (n + 2) - a (n + 1)|
    -- Cube identity: x^3 - y^3 = (x - y)(x^2 + xy + y^2).
    have hcube_id : (a (n + 3)) ^ 3 - (a (n + 2)) ^ 3 =
        (a (n + 3) - a (n + 2)) * ((a (n + 3)) ^ 2 + a (n + 3) * a (n + 2) + (a (n + 2)) ^ 2) := by
      ring
    -- a(n+3)^3 = a(n+2)^2 - 8, a(n+2)^3 = a(n+1)^2 - 8.
    have hd3 : (a (n + 3)) ^ 3 = (a (n + 2)) ^ 2 - 8 := by
      have := hrec (n + 2); convert this using 2
    have hd2 : (a (n + 2)) ^ 3 = (a (n + 1)) ^ 2 - 8 := by
      have := hrec (n + 1); convert this using 2
    have hcube_diff : (a (n + 3)) ^ 3 - (a (n + 2)) ^ 3 = (a (n + 2)) ^ 2 - (a (n + 1)) ^ 2 := by
      rw [hd3, hd2]; ring
    have hsq_id : (a (n + 2)) ^ 2 - (a (n + 1)) ^ 2 =
        (a (n + 2) - a (n + 1)) * (a (n + 2) + a (n + 1)) := by ring
    -- Combine: (diff a(n+3) a(n+2)) * S = (diff a(n+2) a(n+1)) * sum
    -- where S = a(n+3)^2 + a(n+3)*a(n+2) + a(n+2)^2 and sum = a(n+2)+a(n+1).
    -- Bound S ≥ 3*C^2 since each of a(n+3), a(n+2) ∈ [-2, -C], so products and squares ≥ C^2.
    set S : ℝ := (a (n + 3)) ^ 2 + a (n + 3) * a (n + 2) + (a (n + 2)) ^ 2 with hS_def
    have hS_ge : 3 * C ^ 2 ≤ S := by
      -- a(n+3)^2 ≥ C^2 (since |a(n+3)| ≥ C).
      -- a(n+2)^2 ≥ C^2.
      -- a(n+3)*a(n+2) ≥ C^2 (product of two negatives with |·| ≥ C).
      have habs_n3 : C ≤ |a (n + 3)| := by rw [abs_of_nonpos (by linarith)]; linarith
      have habs_n2 : C ≤ |a (n + 2)| := by rw [abs_of_nonpos (by linarith)]; linarith
      have hsq_n3 : C ^ 2 ≤ (a (n + 3)) ^ 2 := by
        rw [← sq_abs (a (n + 3))]
        exact pow_le_pow_left₀ hC_pos.le habs_n3 2
      have hsq_n2 : C ^ 2 ≤ (a (n + 2)) ^ 2 := by
        rw [← sq_abs (a (n + 2))]
        exact pow_le_pow_left₀ hC_pos.le habs_n2 2
      have hprod : C ^ 2 ≤ a (n + 3) * a (n + 2) := by
        -- a(n+3), a(n+2) ≤ -C < 0, so product ≥ C * C = C^2
        have h1 : 0 < -a (n + 3) := by linarith
        have h2 : 0 < -a (n + 2) := by linarith
        have h3 : C ≤ -a (n + 3) := by linarith
        have h4 : C ≤ -a (n + 2) := by linarith
        have : C * C ≤ (-a (n + 3)) * (-a (n + 2)) := by
          apply mul_le_mul h3 h4 hC_pos.le h1.le
        nlinarith
      rw [hS_def]
      linarith
    have hS_pos : 0 < S := by nlinarith [sq_nonneg C, hC_pos]
    -- sum bound: |a(n+2) + a(n+1)| ≤ 4.
    have hsum_abs : |a (n + 2) + a (n + 1)| ≤ 4 := by
      rw [abs_le]
      refine ⟨by linarith, by linarith [hC_pos]⟩
    -- From the two cube/square identities:
    have hkey : (a (n + 3) - a (n + 2)) * S =
        (a (n + 2) - a (n + 1)) * (a (n + 2) + a (n + 1)) := by
      have := hcube_diff
      rw [hcube_id, hsq_id] at this
      linarith
    -- Take absolute values.
    have habs_key : |a (n + 3) - a (n + 2)| * S =
        |a (n + 2) - a (n + 1)| * |a (n + 2) + a (n + 1)| := by
      have h1 : |(a (n + 3) - a (n + 2)) * S| =
          |(a (n + 2) - a (n + 1)) * (a (n + 2) + a (n + 1))| := by rw [hkey]
      rw [abs_mul, abs_mul, abs_of_pos hS_pos] at h1
      exact h1
    -- Now divide: |a(n+3) - a(n+2)| = |a(n+2) - a(n+1)| * |sum| / S ≤ |a(n+2) - a(n+1)| * 4 / (3*C^2).
    -- Then 4/(3*C^2) = C/3 since C * C^2 = C^3 = 4 → C^2 = 4/C → 4/(3 C^2) = 4 C / (3*4) = C/3.
    -- Compute: 3*C^2 * r = 3*C^2 * (C/3) = C^3 = 4.
    have hrC2 : 3 * C ^ 2 * r = 4 := by
      rw [hr_def]
      have : 3 * C ^ 2 * (C / 3) = C ^ 3 := by ring
      rw [this, hC_cube]
    -- Split cases on whether |a(n+2) - a(n+1)| = 0.
    by_cases hzero : |a (n + 2) - a (n + 1)| = 0
    · -- Then diff is 0, so a(n+2) = a(n+1). Then a(n+3)^3 = a(n+2)^2 - 8 = a(n+1)^2 - 8 = a(n+2)^3,
      -- so a(n+3) = a(n+2), hence LHS is 0.
      have heq : a (n + 2) = a (n + 1) := by
        have := abs_eq_zero.mp hzero; linarith
      have : (a (n + 3)) ^ 3 = (a (n + 2)) ^ 3 := by rw [hd3, hd2, heq]
      have heq' : a (n + 3) = a (n + 2) := cube_eq_cube _ _ this
      rw [heq']
      simp
      exact mul_nonneg hr_pos.le (abs_nonneg _)
    · have habs_pos : 0 < |a (n + 2) - a (n + 1)| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
      -- Derive the bound:  |a(n+3) - a(n+2)| ≤ r * |a(n+2) - a(n+1)|.
      -- Equivalent: |a(n+3) - a(n+2)| * S ≤ r * |a(n+2) - a(n+1)| * S.
      -- LHS = |a(n+2) - a(n+1)| * |sum|, RHS = r * |a(n+2) - a(n+1)| * S.
      -- So we need |sum| ≤ r * S.
      -- Use |sum| ≤ 4 and r * S ≥ r * 3 * C^2 = 4, so |sum| ≤ 4 ≤ r * S.
      have hrS_ge_4 : 4 ≤ r * S := by
        have : r * (3 * C ^ 2) ≤ r * S := by
          apply mul_le_mul_of_nonneg_left hS_ge hr_pos.le
        have heq4 : r * (3 * C ^ 2) = 4 := by linarith [hrC2]
        linarith
      -- sum bound gives |sum| ≤ 4 ≤ r * S
      have hsum_le_rS : |a (n + 2) + a (n + 1)| ≤ r * S := le_trans hsum_abs hrS_ge_4
      -- From habs_key: |diff_new| * S = |diff_old| * |sum| ≤ |diff_old| * (r * S)
      -- So (|diff_new| - r * |diff_old|) * S ≤ 0. Since S > 0, we get |diff_new| ≤ r * |diff_old|.
      have : |a (n + 3) - a (n + 2)| * S ≤ (r * |a (n + 2) - a (n + 1)|) * S := by
        calc |a (n + 3) - a (n + 2)| * S
            = |a (n + 2) - a (n + 1)| * |a (n + 2) + a (n + 1)| := habs_key
          _ ≤ |a (n + 2) - a (n + 1)| * (r * S) := by
              apply mul_le_mul_of_nonneg_left hsum_le_rS (abs_nonneg _)
          _ = (r * |a (n + 2) - a (n + 1)|) * S := by ring
      exact le_of_mul_le_mul_right this hS_pos
  -- Step 4: |a(n+2) - a(n+1)| ≤ r^n * |a_2 - a_1| for all n ≥ 0.
  -- So the tail from index 2 on is geometric.
  have hgeom : ∀ n, |a (n + 2) - a (n + 1)| ≤ r ^ n * |a 2 - a 1| := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      -- (k+1)+2 = k+3, (k+1)+1 = k+2. hcontract k gives |a(k+3) - a(k+2)| ≤ r * |a(k+2) - a(k+1)|.
      have := hcontract k
      -- Use it: |a(k+3) - a(k+2)| ≤ r * |a(k+2) - a(k+1)| ≤ r * (r^k * |a 2 - a 1|) = r^(k+1) * ...
      calc |a (k + 1 + 2) - a (k + 1 + 1)|
          = |a (k + 3) - a (k + 2)| := by ring_nf
        _ ≤ r * |a (k + 2) - a (k + 1)| := hcontract k
        _ ≤ r * (r ^ k * |a 2 - a 1|) := by
            apply mul_le_mul_of_nonneg_left ih hr_pos.le
        _ = r ^ (k + 1) * |a 2 - a 1| := by ring
  -- Step 5: summability.
  -- The sequence f n = |a(n+1) - a(n)|.
  -- f 0 = |a 1 - a 0| = 2. For n ≥ 1, f n = |a(n+1) - a(n)|. Set g k = f (k+1) = |a(k+2) - a(k+1)|.
  -- g k ≤ r^k * |a 2 - a 1|. The RHS is summable (geometric), so g is summable.
  -- Hence f is summable (adding finitely many terms doesn't affect summability).
  -- Summable g:
  have hsum_g : Summable (fun k => |a (k + 2) - a (k + 1)|) := by
    have hgeom_sum : Summable (fun k : ℕ => r ^ k * |a 2 - a 1|) :=
      (summable_geometric_of_lt_one hr_pos.le hr_lt_one).mul_right _
    apply Summable.of_nonneg_of_le (fun n => abs_nonneg _) hgeom hgeom_sum
  -- Now f = g shifted. In Lean, Summable.comp_injective with k ↦ k+1.
  -- Actually just use: Summable f ↔ Summable (fun k => f (k+1)) (since f 0 is finitely many terms).
  -- Use `summable_nat_add_iff`.
  -- `summable_nat_add_iff 1 : Summable (fun n => f (n + 1)) ↔ Summable f`.
  have heq : (fun n => |a (n + 1 + 1) - a (n + 1)|) = (fun k => |a (k + 2) - a (k + 1)|) := by
    funext k
    rfl
  have hshift : Summable (fun n => (fun m => |a (m + 1) - a m|) (n + 1)) := by
    show Summable (fun n => |a (n + 1 + 1) - a (n + 1)|)
    rw [heq]
    exact hsum_g
  exact (summable_nat_add_iff 1).mp hshift

end Imc2018P7
