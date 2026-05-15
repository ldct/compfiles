/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 5

Let `R` be a ring of characteristic zero (we take this to mean that the
underlying additive group is torsion-free). Let `e, f, g ∈ R` be idempotents
(i.e. `e^2 = e`, etc.) with `e + f + g = 0`. Prove that `e = f = g = 0`.
-/

namespace Imc2000P5

snip begin

/-- Core algebraic lemma in a torsion-free ring: if `e`, `f`, `g` are idempotents summing to
zero, then they are all zero. -/
lemma core {R : Type*} [Ring R] [IsAddTorsionFree R]
    (e f g : R) (he : e * e = e) (hf : f * f = f) (hg : g * g = g)
    (hsum : e + f + g = 0) : e = 0 ∧ f = 0 ∧ g = 0 := by
  -- First, `g = -(e + f)`.
  have hg_eq : g = -(e + f) := by
    linear_combination (norm := abel) hsum
  -- Expand g² = g using g = -(e+f):
  -- (-(e+f))*(-(e+f)) = -(e+f), i.e., e² + e*f + f*e + f² = -(e+f).
  -- Using e² = e, f² = f: e + e*f + f*e + f = -(e+f), so e*f + f*e = -(e+f) - e - f = 2g.
  have hefsum : e * f + f * e = g + g := by
    have h1 : g * g = g := hg
    have h2 : g * g = e + e * f + f * e + f := by
      rw [hg_eq]; rw [neg_mul_neg]
      rw [add_mul, mul_add, mul_add, he, hf]
      abel
    rw [h2] at h1
    -- h1 : e + e * f + f * e + f = g
    -- We want e * f + f * e = g + g. Using e + f = -g: e + f + (g + g) = g.
    -- So g + g = g - (e+f) = g + g. Need to show e*f + f*e = g + g.
    -- From h1: e*f + f*e = g - e - f. And e + f = -g, so -e - f = g.
    -- Thus e*f + f*e = g + g.
    linear_combination (norm := abel) h1 - hsum
  -- Now compute e*f*e two ways.
  -- (1) e*(e*f + f*e) = e²*f + e*f*e = e*f + e*f*e.
  --     Also = e*(g+g) = e*g + e*g. And e*g = e*(-(e+f)) = -e² - e*f = -e - e*f.
  --     So e*f + e*f*e = -e - e*f + (-e - e*f) = -2e - 2(e*f).
  --     Hence e*f*e = -2e - 3(e*f).
  have hefe1 : e * f * e + (e * f + e * f + e * f) + (e + e) = 0 := by
    have h0 : e * (e * f + f * e) = e * (g + g) := by rw [hefsum]
    have hlhs : e * (e * f + f * e) = e * f + e * f * e := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, he]
    have heg_val : e * g = -e - e * f := by
      rw [hg_eq, mul_neg, mul_add, he]; noncomm_ring
    have hrhs : e * (g + g) = (-e - e * f) + (-e - e * f) := by
      rw [mul_add, heg_val]
    rw [hlhs, hrhs] at h0
    linear_combination (norm := abel) h0
  -- (2) (e*f + f*e)*e = e*f*e + f*e² = e*f*e + f*e.
  --     Also = (g+g)*e = g*e + g*e. And g*e = -(e+f)*e = -e - f*e.
  --     So e*f*e + f*e = -2e - 2(f*e). Hence e*f*e = -2e - 3(f*e).
  have hefe2 : e * f * e + (f * e + f * e + f * e) + (e + e) = 0 := by
    have h0 : (e * f + f * e) * e = (g + g) * e := by rw [hefsum]
    have hlhs : (e * f + f * e) * e = e * f * e + f * e := by
      rw [add_mul, mul_assoc f e e, he]
    have hge_val : g * e = -e - f * e := by
      rw [hg_eq, neg_mul, add_mul, he]; noncomm_ring
    have hrhs : (g + g) * e = (-e - f * e) + (-e - f * e) := by
      rw [add_mul, hge_val]
    rw [hlhs, hrhs] at h0
    linear_combination (norm := abel) h0
  -- Subtract: get (e*f + e*f + e*f) = (f*e + f*e + f*e).
  have h3comm : e * f + e * f + e * f = f * e + f * e + f * e := by
    linear_combination (norm := abel) hefe1 - hefe2
  -- Apply torsion-freeness: e*f = f*e.
  have hcomm : e * f = f * e := by
    have h3ne : (3 : ℕ) ≠ 0 := by norm_num
    have hc : (3 : ℕ) • (e * f) = (3 : ℕ) • (f * e) := by
      rw [show (3 : ℕ) • (e * f) = e * f + e * f + e * f by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, two_nsmul]]
      rw [show (3 : ℕ) • (f * e) = f * e + f * e + f * e by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, two_nsmul]]
      exact h3comm
    exact IsAddTorsionFree.nsmul_right_injective h3ne hc
  -- Now `e*f + f*e = g + g` becomes `e*f + e*f = g + g`. So 2•(e*f) = 2•g, hence e*f = g.
  have hefg : e * f = g := by
    have h2ne : (2 : ℕ) ≠ 0 := by norm_num
    have h2 : (2 : ℕ) • (e * f) = (2 : ℕ) • g := by
      rw [two_nsmul, two_nsmul]
      conv_lhs => rw [show e * f + e * f = e * f + f * e from by rw [hcomm]]
      exact hefsum
    exact IsAddTorsionFree.nsmul_right_injective h2ne h2
  -- Then `e + f + e*f = 0`.
  have hsum_ef : e + f + e * f = 0 := by rw [hefg]; exact hsum
  -- Multiply by `e` on the left: e + e*f + e*(e*f) = 0, and e*(e*f) = e*f. So e + 2•(e*f) = 0.
  have he_eq : e + (e * f + e * f) = 0 := by
    have h0 : e * (e + f + e * f) = e * 0 := by rw [hsum_ef]
    rw [mul_zero] at h0
    have h_expand : e * (e + f + e * f) = e + e * f + e * (e * f) := by
      rw [mul_add, mul_add, he]
    have h_eef : e * (e * f) = e * f := by rw [← mul_assoc, he]
    rw [h_expand, h_eef] at h0
    linear_combination (norm := abel) h0
  -- Multiply by `f` on the left: f*e + f + f*(e*f) = 0.  f*(e*f) = (f*e)*f = (e*f)*f = e*f.
  -- Also f*e = e*f. So e*f + f + e*f = 0, i.e., f + 2•(e*f) = 0.
  have hf_eq : f + (e * f + e * f) = 0 := by
    have h0 : f * (e + f + e * f) = f * 0 := by rw [hsum_ef]
    rw [mul_zero] at h0
    have h_expand : f * (e + f + e * f) = f * e + f + f * (e * f) := by
      rw [mul_add, mul_add, hf]
    have h_fef : f * (e * f) = e * f := by
      rw [← mul_assoc, ← hcomm, mul_assoc, hf]
    rw [h_expand, h_fef, ← hcomm] at h0
    linear_combination (norm := abel) h0
  -- So `e = f`.
  have hef : e = f := by
    linear_combination (norm := abel) he_eq - hf_eq
  -- From e = f and e*f = g: e*f = e*e = e, so g = e.
  have heg : e = g := by
    have h1 : e * f = e := by rw [← hef]; exact he
    rw [← hefg, h1]
  -- Finally, e + e + e = 0 from hsum.
  have h3e_eq : e + e + e = 0 := by
    have h := hsum
    rw [← hef, ← heg] at h
    exact h
  -- Hence 3•e = 0, so e = 0 by torsion-freeness.
  have h3e : (3 : ℕ) • e = (3 : ℕ) • (0 : R) := by
    rw [show (3 : ℕ) • e = e + e + e by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, two_nsmul]]
    rw [show (3 : ℕ) • (0 : R) = 0 + 0 + 0 by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, two_nsmul]]
    linear_combination (norm := abel) h3e_eq
  have h3ne : (3 : ℕ) ≠ 0 := by norm_num
  have he0 : e = 0 := IsAddTorsionFree.nsmul_right_injective h3ne h3e
  exact ⟨he0, hef ▸ he0, heg ▸ he0⟩

snip end

problem imc2000_p5 {R : Type*} [Ring R] [IsAddTorsionFree R]
    (e f g : R) (he : e * e = e) (hf : f * f = f) (hg : g * g = g)
    (hsum : e + f + g = 0) : e = 0 ∧ f = 0 ∧ g = 0 :=
  core e f g he hf hg hsum

end Imc2000P5
