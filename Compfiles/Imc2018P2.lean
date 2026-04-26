/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 2
(IMC 2018, Day 1, Problem 2)

Does there exist a field whose multiplicative group is isomorphic to its
additive group?

Answer: No.
-/

namespace Imc2018P2

problem imc2018_p2 (F : Type*) [Field F] :
    ¬ Nonempty (Fˣ ≃* Multiplicative F) := by
  rintro ⟨e⟩
  -- Step 1: `e 1 = 1`, i.e. `Multiplicative.toAdd (e 1) = 0`.
  have he_one : e 1 = 1 := map_one e
  -- Step 2: `e(-1) + e(-1) = 0` in `F`.
  have he_neg_sq : e (-1) * e (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, he_one]
  -- Reading `Multiplicative F` multiplication as addition in `F`.
  have h_double_neg_one :
      Multiplicative.toAdd (e (-1)) + Multiplicative.toAdd (e (-1)) = 0 := by
    have := he_neg_sq
    -- `(*) : Multiplicative F → Multiplicative F → Multiplicative F` is `(+)` on `F`.
    change Multiplicative.toAdd (e (-1) * e (-1)) = Multiplicative.toAdd (1 : Multiplicative F)
    rw [this]
  -- Step 3: Show `(2 : F) = 0`. Otherwise we derive a contradiction.
  -- Let `α = Multiplicative.toAdd (e (-1))`. Then `2 * α = 0`.
  have h2α : 2 * Multiplicative.toAdd (e (-1)) = 0 := by
    linear_combination h_double_neg_one
  -- Case analysis on whether `(2 : F) = 0`.
  have hchar2 : (2 : F) = 0 := by
    by_contra h2
    -- If `2 ≠ 0`, then `toAdd (e (-1)) = 0`, so `e (-1) = 1 = e 1`, so `-1 = 1`.
    have hα : Multiplicative.toAdd (e (-1)) = 0 := by
      rcases mul_eq_zero.mp h2α with h | h
      · exact absurd h h2
      · exact h
    have h_e_neg : e (-1) = 1 := by
      apply Multiplicative.toAdd.injective
      exact hα
    have h_neg_one_eq_one : (-1 : Fˣ) = 1 := e.injective (by rw [h_e_neg, he_one])
    -- So `(-1 : F) = 1`, hence `(2 : F) = 0`, contradiction.
    have hcoe : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := by rw [h_neg_one_eq_one]
    simp at hcoe
    -- `hcoe : -1 = 1 in F`
    apply h2
    linear_combination -hcoe
  -- Step 4: With char 2, every unit `x` satisfies `x² = 1`, hence `x = 1`.
  have h_units_trivial : ∀ x : Fˣ, x = 1 := by
    intro x
    -- `e(x²) = e(x) * e(x)`, and `2 * Multiplicative.toAdd (e x) = 0`.
    have hx_double :
        Multiplicative.toAdd (e x) + Multiplicative.toAdd (e x) = 0 := by
      have h2x : (2 : F) * Multiplicative.toAdd (e x) = 0 := by
        rw [hchar2, zero_mul]
      linear_combination h2x
    have h_ex_sq : e (x * x) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (e x * e x) =
          Multiplicative.toAdd (1 : Multiplicative F)
      change Multiplicative.toAdd (e x) + Multiplicative.toAdd (e x) = 0
      exact hx_double
    have h_x_sq : x * x = 1 := by
      have := e.injective (h_ex_sq.trans he_one.symm)
      exact this
    -- Now `x² = 1` in `Fˣ`, hence `(x - 1) * (x + 1) = 0` in `F`. In char 2, `x = 1`.
    have hx_F : (x : F) * (x : F) = 1 := by
      have := congr_arg (fun u : Fˣ => (u : F)) h_x_sq
      simpa using this
    have hfact : ((x : F) - 1) * ((x : F) - 1) = 0 := by
      -- In char 2: `(x-1)² = x² - 2x + 1`. With `x² = 1` and `2 = 0`, this is `0`.
      linear_combination hx_F + (1 - (x : F)) * hchar2
    have hx_eq : (x : F) = 1 := by
      have h := mul_self_eq_zero.mp hfact
      linear_combination h
    -- From `(x : F) = 1` we get `x = 1` as units.
    apply Units.ext
    simpa using hx_eq
  -- Step 5: Cardinality contradiction.
  -- `Fˣ` has only one element (just `1`), so `Multiplicative F ≃ Fˣ` has one element.
  -- But `F` has at least two elements (`0` and `1`).
  have h_zero_ne_one : (0 : F) ≠ 1 := zero_ne_one
  -- Lift `0` and `1` of `F` to `Multiplicative F` and use `e.symm` to map them to `Fˣ`.
  let z : Multiplicative F := Multiplicative.ofAdd (0 : F)
  let o : Multiplicative F := Multiplicative.ofAdd (1 : F)
  have hzo : z ≠ o := by
    intro h
    apply h_zero_ne_one
    exact Multiplicative.ofAdd.injective h
  have h_ez : e.symm z = 1 := h_units_trivial _
  have h_eo : e.symm o = 1 := h_units_trivial _
  apply hzo
  have := h_ez.trans h_eo.symm
  exact e.symm.injective this

end Imc2018P2
