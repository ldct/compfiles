/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2013, Problem 8
(IMC 2013, Day 2, Problem 8)

Suppose that `v₁, …, v_d` are unit vectors in `ℝ^d`. Prove that there
exists a unit vector `u` such that `|u ⋅ vᵢ| ≤ 1/√d` for all `i`.

## Proof outline

* If the `vᵢ` are linearly dependent, take `u` to be any unit vector
  perpendicular to their span. Then `u ⋅ vᵢ = 0`.
* Otherwise, the `vᵢ` form a basis of `ℝ^d`. Let `w₁, …, w_d` be the
  dual basis: `wᵢ ⋅ vⱼ = δᵢⱼ`. Since `wᵢ ⋅ vᵢ = 1` and `|vᵢ| = 1`,
  Cauchy–Schwarz gives `|wᵢ| ≥ 1`. For `ε ∈ {±1}^d`, set
  `u_ε = ∑ᵢ εᵢ wᵢ`. Then `u_ε ⋅ v_k = ε_k`, so `|u_ε ⋅ v_k| = 1`.
  Averaging `|u_ε|²` over `ε` (cross terms vanish) gives
  `∑ |wᵢ|² ≥ d`. Hence some `ε*` satisfies `|u_{ε*}|² ≥ d`, and
  `u = u_{ε*} / |u_{ε*}|` works: `|u ⋅ v_k| = 1 / |u_{ε*}| ≤ 1/√d`.
-/

namespace Imc2013P8

open scoped InnerProductSpace
open Finset BigOperators

problem imc2013_p8 (d : ℕ) (_hd : 0 < d) (v : Fin d → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, ‖v i‖ = 1) :
    ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧
      ∀ i, |⟪u, v i⟫_ℝ| ≤ 1 / Real.sqrt d := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast _hd)
  by_cases hli : LinearIndependent ℝ v
  · -- Linearly independent case: use the dual basis.
    -- TODO: full proof using dual basis averaging argument.
    sorry
  · -- Linearly dependent case: take u perpendicular to span(v).
    have hspan_ne : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
      intro hspan
      apply hli
      refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
      · rw [hspan]
      · simp [hdim]
    -- The orthogonal complement is nontrivial.
    have hperp_ne : (Submodule.span ℝ (Set.range v))ᗮ ≠ ⊥ := by
      intro h
      apply hspan_ne
      exact Submodule.orthogonal_eq_bot_iff.mp h
    -- So there exists a nonzero element in the orthogonal complement.
    obtain ⟨w, hw_mem, hw_ne⟩ :
        ∃ w ∈ (Submodule.span ℝ (Set.range v))ᗮ, w ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne
    -- Normalize w to a unit vector u.
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
    refine ⟨(‖w‖)⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw_norm_pos),
          inv_mul_cancel₀ (ne_of_gt hw_norm_pos)]
    · intro i
      have hvi_mem : v i ∈ Submodule.span ℝ (Set.range v) :=
        Submodule.subset_span (Set.mem_range_self i)
      -- v i is orthogonal to w (so w is orthogonal to v i).
      have hortho : ⟪v i, w⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal _ _).mp hw_mem _ hvi_mem
      have hortho' : ⟪w, v i⟫_ℝ = 0 := by
        rw [real_inner_comm]; exact hortho
      rw [real_inner_smul_left, hortho', mul_zero, abs_zero]
      positivity

end Imc2013P8
