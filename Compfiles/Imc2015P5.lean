/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# International Mathematical Competition 2015, Problem 5

Let `n ≥ 2`, let `A₁, A₂, …, A_{n+1}` be `n+1` points in `n`-dimensional Euclidean space
not lying on the same hyperplane, and let `B` be a point strictly inside the convex
hull of `A₁, …, A_{n+1}`. Prove that `∠ AᵢBAⱼ > 90°` holds for at least `n` pairs
`(i,j)` with `1 ≤ i < j ≤ n+1`.

## Sketch of proof

Let `vᵢ = Aᵢ - B`. The angle `∠ AᵢBAⱼ` is `> π/2` iff `⟪vᵢ, vⱼ⟫ < 0`. Since `B` is
strictly inside the convex hull of an affinely independent set, there exist positive
weights `wᵢ > 0` with `∑ wᵢ = 1` and `∑ wᵢ • Aᵢ = B`. Equivalently, `∑ wᵢ • vᵢ = 0`.

Form the graph on `{1, …, n+1}` whose edges are exactly the pairs `{i,j}` with
`⟪vᵢ, vⱼ⟫ < 0`. A connected graph on `n+1` vertices has at least `n` edges, so it
suffices to show this graph is connected.

If the graph were disconnected, write `[n+1] = V ⊔ W` with `V, W ≠ ∅` and no edges
between them. Set `x = ∑_{i ∈ V} wᵢ vᵢ` and `y = ∑_{j ∈ W} wⱼ vⱼ`. Then
`x + y = 0`, so `‖x + y‖² = 0`, i.e.
`‖x‖² + ‖y‖² + 2⟨x, y⟩ = 0`.
But `⟨x, y⟩ = ∑_{i ∈ V, j ∈ W} wᵢ wⱼ ⟪vᵢ, vⱼ⟫ ≥ 0` (no negative-inner-product edges
between `V` and `W`, so each `⟪vᵢ, vⱼ⟫ ≥ 0`). All three terms are nonnegative,
forcing `‖x‖ = 0`, hence `x = 0`. Then `B = (∑_{i ∈ V} wᵢ Aᵢ) / (∑_V wᵢ)` is a
convex combination of a proper subset of the vertices, contradicting affine
independence (and the fact that `B` is strictly interior).
-/

namespace Imc2015P5

open scoped EuclideanGeometry RealInnerProductSpace
open Real

-- snip begin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For nonzero vectors `x, y`, we have `⟪x, y⟫ < 0 ↔ angle x y > π/2`. -/
lemma inner_neg_iff_angle_gt {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪x, y⟫ < 0 ↔ π / 2 < InnerProductGeometry.angle x y := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hprod : (0 : ℝ) < ‖x‖ * ‖y‖ := mul_pos hxn hyn
  have hcos : Real.cos (InnerProductGeometry.angle x y) = ⟪x, y⟫ / (‖x‖ * ‖y‖) :=
    InnerProductGeometry.cos_angle x y
  have hθlb : 0 ≤ InnerProductGeometry.angle x y := InnerProductGeometry.angle_nonneg x y
  have hθub : InnerProductGeometry.angle x y ≤ π := InnerProductGeometry.angle_le_pi x y
  -- ⟪x,y⟫ < 0 ↔ cos(angle) < 0
  have iff1 : ⟪x, y⟫ < 0 ↔ Real.cos (InnerProductGeometry.angle x y) < 0 := by
    rw [hcos]
    constructor
    · intro h; exact div_neg_of_neg_of_pos h hprod
    · intro h
      by_contra h2
      push_neg at h2
      have : 0 ≤ ⟪x, y⟫ / (‖x‖ * ‖y‖) := div_nonneg h2 hprod.le
      linarith
  -- cos(angle) < 0 ↔ π/2 < angle (on [0, π])
  have iff2 : Real.cos (InnerProductGeometry.angle x y) < 0 ↔
      π / 2 < InnerProductGeometry.angle x y := by
    constructor
    · intro h
      by_contra hle
      push_neg at hle
      have : 0 ≤ Real.cos (InnerProductGeometry.angle x y) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
      linarith
    · intro h
      have : Real.cos (InnerProductGeometry.angle x y) < Real.cos (π / 2) := by
        apply Real.strictAntiOn_cos
        · exact Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        · exact Set.mem_Icc.mpr ⟨hθlb, hθub⟩
        · exact h
      rwa [Real.cos_pi_div_two] at this
  exact iff1.trans iff2

-- snip end

/-- IMC 2015 Problem 5. -/
problem imc2015_p5 (n : ℕ) (hn : 2 ≤ n)
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = n)
    (A : Fin (n+1) → V) (hA : AffineIndependent ℝ A) (B : V)
    (hB : B ∈ interior (convexHull ℝ (Set.range A))) :
    n ≤ ((Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter
        (fun p => p.1 < p.2 ∧ π / 2 < ∠ (A p.1) B (A p.2))).card := by
  classical
  -- Step 1: Extract barycentric weights w_i > 0, ∑ w = 1, ∑ w • A = B.
  have hspan : affineSpan ℝ (Set.range A) = ⊤ := by
    rw [hA.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_fin, hV]
  let b : AffineBasis (Fin (n+1)) ℝ V := ⟨A, hA, hspan⟩
  have hbpts : (b : Fin (n+1) → V) = A := rfl
  have hBmem : B ∈ interior (convexHull ℝ (Set.range (b : Fin (n+1) → V))) := by
    simpa [hbpts] using hB
  rw [b.interior_convexHull] at hBmem
  set w : Fin (n+1) → ℝ := fun i => b.coord i B with hw_def
  have hw_pos : ∀ i, 0 < w i := hBmem
  have hw_sum : ∑ i, w i = 1 := b.sum_coord_apply_eq_one B
  have hw_baryB : ∑ i, w i • A i = B := by
    -- `linear_combination_coord_eq_self` gives `∑ b.coord i v • b i = v` for `v : V`.
    have := b.linear_combination_coord_eq_self B
    simpa [hbpts] using this
  -- Step 2: Define v i = A i - B. Then ∑ w i • v i = 0.
  set v : Fin (n+1) → V := fun i => A i - B with hv_def
  have hv_sum : ∑ i, w i • v i = 0 := by
    have : ∑ i, w i • v i = (∑ i, w i • A i) - (∑ i, w i) • B := by
      simp only [v, smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [this, hw_baryB, hw_sum, one_smul, sub_self]
  -- Step 3: v i ≠ 0 for all i (B is interior, A i is a vertex).
  have hv_ne : ∀ i, v i ≠ 0 := by
    intro i hi
    have hAi : A i = B := by
      have : A i - B = 0 := hi
      have := sub_eq_zero.mp this
      exact this
    -- v i = 0 means A i = B. Then b.coord j B = b.coord j (b i) = if j = i then 1 else 0.
    -- Pick j ≠ i; then w j = 0, contradicting hw_pos.
    have h2 : 2 ≤ n + 1 := by omega
    have hnontriv : Nontrivial (Fin (n+1)) := ⟨0, ⟨1, by omega⟩, by
      intro h; simp [Fin.ext_iff] at h⟩
    obtain ⟨j, hj⟩ := exists_ne i
    have hcoord_j : b.coord j B = 0 := by
      rw [← hAi]
      show b.coord j (b i) = 0
      exact b.coord_apply_ne hj
    have : w j = 0 := hcoord_j
    have := hw_pos j
    linarith
  -- Step 4: Translate the angle condition. ∠(A i) B (A j) > π/2 ↔ ⟪v i, v j⟫ < 0.
  have hangle_iff : ∀ i j : Fin (n+1),
      π / 2 < ∠ (A i) B (A j) ↔ ⟪v i, v j⟫ < 0 := by
    intro i j
    show π / 2 < InnerProductGeometry.angle (A i - B) (A j - B) ↔ ⟪v i, v j⟫ < 0
    rw [show A i - B = v i from rfl, show A j - B = v j from rfl]
    exact (inner_neg_iff_angle_gt (hv_ne i) (hv_ne j)).symm
  -- Step 5: Reduce to bounding the count of pairs with negative inner product.
  set negPairs : Finset (Fin (n+1) × Fin (n+1)) :=
    (Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter
      (fun p => p.1 < p.2 ∧ ⟪v p.1, v p.2⟫ < 0)
  with hneg_def
  have hsame : ((Finset.univ : Finset (Fin (n+1) × Fin (n+1))).filter
        (fun p => p.1 < p.2 ∧ π / 2 < ∠ (A p.1) B (A p.2))) = negPairs := by
    apply Finset.filter_congr
    intros p _
    rw [hangle_iff p.1 p.2]
  rw [hsame]
  -- Step 6: It suffices to show the "negative inner product" graph on Fin (n+1)
  -- is connected; then the standard fact that a connected graph on n+1 vertices has
  -- at least n edges gives the required bound.
  -- TODO: complete this connectivity argument and the ensuing edge-count bookkeeping.
  -- The argument: if disconnected, take a connected component S and its complement T
  -- (both nonempty). For i ∈ S, j ∈ T we have ⟪v_i, v_j⟫ ≥ 0. Then
  --     0 = ‖∑_i w_i v_i‖² = ‖∑_{i∈S} w_i v_i‖² + ‖∑_{j∈T} w_j v_j‖²
  --         + 2 ∑_{i∈S,j∈T} w_i w_j ⟪v_i, v_j⟫,
  -- with all three summands ≥ 0. Forces ∑_{i∈S} w_i v_i = 0, contradicting affine
  -- independence (B would coincide with a convex combination over a strict subset of A's).
  sorry

end Imc2015P5
