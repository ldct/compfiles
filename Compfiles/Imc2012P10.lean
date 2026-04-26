/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2012, Problem 10 (Day 2, Problem 5)

Let `c ≥ 1` be a real number. Let `G` be an abelian group and `A ⊂ G` a finite
set with `|A + A| ≤ c|A|`. Prove that `|A + A + … + A| ≤ c^k |A|` for every
positive integer `k` (where the sum on the left has `k` copies of `A`).

This is the Plünnecke–Ruzsa inequality, which is available in Mathlib as
`Finset.pluennecke_ruzsa_inequality_nsmul_add`.
-/

namespace Imc2012P10

open scoped Pointwise

problem imc2012_p10
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (c : ℝ) (hc : 1 ≤ c) (A : Finset G)
    (hA : ((A + A).card : ℝ) ≤ c * A.card)
    (k : ℕ) (hk : 1 ≤ k) :
    ((k • A).card : ℝ) ≤ c ^ k * A.card := by
  -- If A is empty, both sides are 0 (since k ≥ 1, k • ∅ = ∅).
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · subst hAe
    have hk' : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    rw [Finset.nsmul_empty hk']
    simp
  -- Plünnecke–Ruzsa: #(k • A) ≤ (#(A + A) / #A)^k * #A in ℚ≥0.
  have key := Finset.pluennecke_ruzsa_inequality_nsmul_add (A := A) (B := A) hAne k
  -- Cast to ℝ.
  have hAcard_pos : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hAcard_ne : (A.card : ℝ) ≠ 0 := ne_of_gt hAcard_pos
  -- Push key from ℚ≥0 to ℝ.
  have key_real : ((k • A).card : ℝ) ≤ ((A + A).card / A.card : ℝ) ^ k * A.card := by
    have := key
    have h1 : (((k • A).card : ℚ≥0) : ℝ) = ((k • A).card : ℝ) := by push_cast; rfl
    have h2 : ((((A + A).card : ℚ≥0) / (A.card : ℚ≥0) : ℚ≥0) : ℝ)
                = ((A + A).card / A.card : ℝ) := by push_cast; rfl
    have h3 : (((A.card : ℚ≥0)) : ℝ) = (A.card : ℝ) := by push_cast; rfl
    have hcast : (((k • A).card : ℚ≥0) : ℝ)
                  ≤ (((((A + A).card : ℚ≥0) / (A.card : ℚ≥0)) ^ k * (A.card : ℚ≥0) : ℚ≥0) : ℝ) := by
      exact_mod_cast this
    rw [h1] at hcast
    have h4 : (((((A + A).card : ℚ≥0) / (A.card : ℚ≥0)) ^ k * (A.card : ℚ≥0) : ℚ≥0) : ℝ)
              = ((A + A).card / A.card : ℝ) ^ k * A.card := by
      push_cast; ring
    rw [h4] at hcast
    exact hcast
  -- Now we have ((A+A).card / A.card) ≤ c, and powers preserve inequalities for nonneg.
  have hratio : ((A + A).card / A.card : ℝ) ≤ c := by
    rw [div_le_iff₀ hAcard_pos]
    exact hA
  have hratio_nonneg : (0 : ℝ) ≤ (A + A).card / A.card := by positivity
  have hpow : ((A + A).card / A.card : ℝ) ^ k ≤ c ^ k :=
    pow_le_pow_left₀ hratio_nonneg hratio k
  calc ((k • A).card : ℝ)
      ≤ ((A + A).card / A.card : ℝ) ^ k * A.card := key_real
    _ ≤ c ^ k * A.card := by
        have hAnn : (0 : ℝ) ≤ A.card := by positivity
        gcongr

end Imc2012P10
