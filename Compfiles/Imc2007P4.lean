/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# International Mathematical Competition 2007, Problem 4
(IMC 2007, Day 1, Problem 4)

Let `G` be a finite group partitioned as the disjoint union of three sets
`A`, `B`, `C`. For subsets `U, V, W ⊆ G`, define
`N(U, V, W) = #{(x, y, z) ∈ U × V × W : x * y * z = e}`.
Prove that `N(A, B, C) = N(C, B, A)`.
-/

namespace Imc2007P4

open Finset

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]

/-- `N U V W` counts triples `(x, y, z) ∈ U × V × W` with `x * y * z = 1`. -/
def N (U V W : Finset G) : ℕ :=
  ((U ×ˢ V ×ˢ W).filter (fun t : G × G × G => t.1 * t.2.1 * t.2.2 = 1)).card

snip begin

omit [DecidableEq G] [Fintype G] in
/-- Key algebraic fact: if `x * y * z = 1` in a group, then `y * z * x = 1`. -/
lemma cyc_eq_one {x y z : G} (h : x * y * z = 1) : y * z * x = 1 := by
  -- z = (x*y)⁻¹ = y⁻¹ * x⁻¹
  have hz : z = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [hz, mul_inv_rev]
  group

omit [Fintype G] in
/-- Cyclic invariance: `N(U, V, W) = N(V, W, U)`. -/
lemma N_cyclic (U V W : Finset G) : N U V W = N V W U := by
  unfold N
  apply Finset.card_bij (fun (t : G × G × G) _ => (t.2.1, t.2.2, t.1))
  · -- maps into the right filter
    rintro ⟨x, y, z⟩ ht
    simp only [mem_filter, mem_product] at ht ⊢
    obtain ⟨⟨hx, hy, hz⟩, hxyz⟩ := ht
    exact ⟨⟨hy, hz, hx⟩, cyc_eq_one hxyz⟩
  · -- injective
    rintro ⟨x₁, y₁, z₁⟩ _ ⟨x₂, y₂, z₂⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hy, hz, hx⟩ := h
    simp [hx, hy, hz]
  · -- surjective
    rintro ⟨y, z, x⟩ hyzx
    simp only [mem_filter, mem_product] at hyzx
    obtain ⟨⟨hy, hz, hx⟩, hyzx_eq⟩ := hyzx
    refine ⟨(x, y, z), ?_, rfl⟩
    simp only [mem_filter, mem_product]
    refine ⟨⟨hx, hy, hz⟩, ?_⟩
    -- need x * y * z = 1 from y * z * x = 1
    have := cyc_eq_one (cyc_eq_one hyzx_eq)
    exact this

/-- `N(U, V, univ) = |U| * |V|`: for each `(x, y) ∈ U × V`, `z = (xy)⁻¹` is
the unique element with `xyz = 1`. -/
lemma N_univ_right (U V : Finset G) : N U V (Finset.univ : Finset G) = U.card * V.card := by
  unfold N
  -- Bijection (x, y, z) ↔ (x, y)
  rw [← Finset.card_product]
  apply Finset.card_bij (fun (t : G × G × G) _ => (t.1, t.2.1))
  · rintro ⟨x, y, z⟩ ht
    simp only [mem_filter, mem_product, mem_univ] at ht
    simp [ht.1.1, ht.1.2.1]
  · rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ hij
    simp only [Prod.mk.injEq] at hij
    simp only [mem_filter, mem_product, mem_univ] at h₁ h₂
    obtain ⟨hx, hy⟩ := hij
    -- z is determined by x, y: z = (x*y)⁻¹
    have hz₁ : z₁ = (x₁ * y₁)⁻¹ := eq_inv_of_mul_eq_one_right h₁.2
    have hz₂ : z₂ = (x₂ * y₂)⁻¹ := eq_inv_of_mul_eq_one_right h₂.2
    simp [hx, hy, hz₁, hz₂]
  · rintro ⟨x, y⟩ hxy
    simp only [mem_product] at hxy
    refine ⟨(x, y, (x * y)⁻¹), ?_, rfl⟩
    simp only [mem_filter, mem_product, mem_univ, and_true]
    refine ⟨⟨hxy.1, hxy.2⟩, ?_⟩
    rw [mul_inv_cancel]

omit [Fintype G] in
/-- Additivity of `N` in the third argument under disjoint union. -/
lemma N_add_right (U V W₁ W₂ : Finset G) (hd : Disjoint W₁ W₂) :
    N U V (W₁ ∪ W₂) = N U V W₁ + N U V W₂ := by
  unfold N
  rw [Finset.product_union, Finset.product_union, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_filter_filter
  apply Finset.disjoint_product.mpr
  right
  apply Finset.disjoint_product.mpr
  right
  exact hd

omit [Fintype G] in
/-- Additivity of `N` in the first argument. -/
lemma N_add_left (U₁ U₂ V W : Finset G) (hd : Disjoint U₁ U₂) :
    N (U₁ ∪ U₂) V W = N U₁ V W + N U₂ V W := by
  unfold N
  rw [Finset.union_product, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_filter_filter
  apply Finset.disjoint_product.mpr
  left
  exact hd

omit [Fintype G] in
/-- Cyclic on three letters (twice): `N(U, V, W) = N(W, U, V)`. -/
lemma N_cyclic2 (U V W : Finset G) : N U V W = N W U V := by
  rw [N_cyclic, N_cyclic]

snip end

/-- IMC 2007 P4. -/
problem imc2007_p4
    (A B C : Finset G)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hABC : A ∪ B ∪ C = (Finset.univ : Finset G)) :
    N A B C = N C B A := by
  -- N_{ABC} = N_{ABG} - N_{ABA} - N_{ABB}
  -- N_{ABG} = |A| * |B| = N_{BAG}
  -- N_{BAG} = N_{BAA} + N_{BAB} + N_{BAC}
  -- Also N_{ABA} = N_{BAA} (cyclic), N_{ABB} = N_{BAB} (cyclic twice)
  -- So N_{ABC} = N_{BAC} = N_{CBA} (cyclic).
  have hAB_BC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_union_left]; exact ⟨hAC, hBC⟩
  have hABC_eq : A ∪ B ∪ C = (Finset.univ : Finset G) := hABC
  -- N A B G = N A B (A ∪ B ∪ C) = N A B A + N A B B + N A B C
  have hG : (Finset.univ : Finset G) = A ∪ B ∪ C := hABC.symm
  have key1 : N A B (Finset.univ : Finset G) = N A B A + N A B B + N A B C := by
    rw [hG]
    rw [N_add_right _ _ _ _ hAB_BC]
    rw [N_add_right _ _ _ _ hAB]
  have key2 : N B A (Finset.univ : Finset G) = N B A A + N B A B + N B A C := by
    rw [hG]
    rw [N_add_right _ _ _ _ hAB_BC]
    rw [N_add_right _ _ _ _ hAB]
  have hABG : N A B (Finset.univ : Finset G) = A.card * B.card := N_univ_right A B
  have hBAG : N B A (Finset.univ : Finset G) = B.card * A.card := N_univ_right B A
  have hcomm : A.card * B.card = B.card * A.card := Nat.mul_comm _ _
  -- N A B A = N B A A (cyclic: ABA -> BAA)
  have hABA : N A B A = N B A A := N_cyclic A B A
  -- N A B B = N B B A (cyclic) = N B A B (cyclic again from BBA -> BAB)
  have hABB : N A B B = N B A B := by
    rw [N_cyclic A B B, N_cyclic B B A]
  have : N A B C = N B A C := by
    have eq1 : A.card * B.card = N A B A + N A B B + N A B C := by rw [← hABG]; exact key1
    have eq2 : B.card * A.card = N B A A + N B A B + N B A C := by rw [← hBAG]; exact key2
    have : N A B A + N A B B + N A B C = N B A A + N B A B + N B A C := by
      rw [← eq1, ← eq2]; exact hcomm
    rw [hABA, hABB] at this
    omega
  rw [this]
  -- N B A C = N C B A (cyclic twice: BAC -> CBA)
  rw [N_cyclic2]

end Imc2007P4
