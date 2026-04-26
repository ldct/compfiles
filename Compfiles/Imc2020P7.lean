/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 7

Let `G` be a group and `n ≥ 2` an integer. Let `H₁, H₂` be subgroups of `G`
satisfying `[G : H₁] = [G : H₂] = n` and `[G : H₁ ∩ H₂] = n(n − 1)`.
Prove that `H₁` and `H₂` are conjugate in `G`.
-/

namespace Imc2020P7

open MulAction Subgroup

problem imc2020_p7 {G : Type*} [Group G] (n : ℕ) (hn : 2 ≤ n)
    (H₁ H₂ : Subgroup G)
    (hH₁ : H₁.index = n) (hH₂ : H₂.index = n)
    (hinter : (H₁ ⊓ H₂).index = n * (n - 1)) :
    ∃ g : G, H₂ = (H₁.map (MulEquiv.toMonoidHom (MulAut.conj g))) := by
  -- We consider the action of H₁ on α := G ⧸ H₂ (by restriction of the natural G-action).
  -- The orbit O of [1] under this H₁-action has size [H₁ : H₁ ⊓ H₂] = n - 1.
  -- Since |α| = n, the complement Oᶜ has size 1. As the complement of an H₁-invariant
  -- set, it is H₁-invariant; being a singleton {[g₀]}, [g₀] is fixed by all of H₁,
  -- i.e., for all h ∈ H₁, h*g₀*H₂ = g₀*H₂, so g₀⁻¹ h g₀ ∈ H₂. Index comparison gives equality.
  have hn0 : n ≠ 0 := by omega
  haveI hfi₁ : H₁.FiniteIndex := ⟨by rw [hH₁]; exact hn0⟩
  haveI hfi₂ : H₂.FiniteIndex := ⟨by rw [hH₂]; exact hn0⟩
  -- Compute (H₁ ⊓ H₂).relIndex H₁ = n - 1
  have hK_idx : (H₁ ⊓ H₂).relIndex H₁ = n - 1 := by
    have h1 : (H₁ ⊓ H₂).relIndex H₁ * H₁.index = (H₁ ⊓ H₂).index :=
      relIndex_mul_index inf_le_left
    rw [hH₁, hinter, mul_comm n (n - 1)] at h1
    exact Nat.eq_of_mul_eq_mul_right (by omega) h1
  let α := G ⧸ H₂
  let x₀ : α := ((1 : G) : α)
  have hstab_G : stabilizer G x₀ = H₂ := stabilizer_quotient H₂
  -- Stabilizer of x₀ in H₁
  have hstab_H₁ : stabilizer H₁ x₀ = (H₁ ⊓ H₂).subgroupOf H₁ := by
    ext ⟨h, hh⟩
    simp only [mem_stabilizer_iff, mem_subgroupOf, mem_inf]
    show (h : G) • x₀ = x₀ ↔ (h ∈ H₁ ∧ h ∈ H₂)
    rw [show ((h : G) • x₀ = x₀) ↔ (h ∈ stabilizer G x₀) from mem_stabilizer_iff.symm,
        hstab_G]
    tauto
  -- Orbit of x₀ under H₁ has ncard = (H₁ ⊓ H₂).relIndex H₁ = n - 1
  have horbit_card : (orbit H₁ x₀).ncard = n - 1 := by
    rw [← index_stabilizer, hstab_H₁]
    exact hK_idx
  -- |α| = n
  have hα_card : Nat.card α = n := hH₂
  haveI : Finite α := Nat.finite_of_card_ne_zero (hα_card ▸ hn0)
  -- So (orbit)ᶜ has 1 element
  have horbit_compl_card : ((orbit H₁ x₀ : Set α))ᶜ.ncard = 1 := by
    have hadd : ((orbit H₁ x₀) : Set α).ncard + (((orbit H₁ x₀) : Set α)ᶜ).ncard = n := by
      have h1 := Set.ncard_add_ncard_compl (orbit H₁ x₀ : Set α)
      rw [h1]; exact hα_card
    omega
  -- Get singleton element y in complement
  obtain ⟨y, hyeq⟩ : ∃ y, ((orbit H₁ x₀ : Set α))ᶜ = {y} := Set.ncard_eq_one.mp horbit_compl_card
  have hy_not_in_orbit : y ∉ orbit H₁ x₀ := by
    have : y ∈ ((orbit H₁ x₀ : Set α))ᶜ := by rw [hyeq]; rfl
    exact this
  have hunique : ∀ z ∈ ((orbit H₁ x₀ : Set α))ᶜ, z = y := by
    intro z hz
    rw [hyeq] at hz
    exact hz
  -- Get a representative g₀ ∈ G with ⟦g₀⟧ = y
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, ((g₀ : G) : α) = y := Quot.exists_rep y
  -- For all h ∈ H₁, h • y = y
  have hfixed : ∀ h ∈ H₁, (h : G) • y = y := by
    intro h hh
    have hhy_not_in_orbit : h • y ∉ orbit H₁ x₀ := by
      intro hmem
      apply hy_not_in_orbit
      -- h • y ∈ orbit ⟹ y = h⁻¹ • (h • y) ∈ orbit
      have : y = h⁻¹ • (h • y) := by rw [smul_smul, inv_mul_cancel, one_smul]
      rw [this]
      obtain ⟨⟨g, hg⟩, hgeq⟩ := hmem
      refine ⟨⟨h⁻¹ * g, H₁.mul_mem (H₁.inv_mem hh) hg⟩, ?_⟩
      show (h⁻¹ * g : G) • x₀ = h⁻¹ • h • y
      rw [mul_smul]
      show h⁻¹ • ((g : G) • x₀) = h⁻¹ • h • y
      rw [show ((g : G) • x₀) = h • y from hgeq]
    have : h • y = y := hunique _ hhy_not_in_orbit
    exact this
  -- Hence for all h ∈ H₁, ⟦h*g₀⟧ = ⟦g₀⟧, so g₀⁻¹ * h⁻¹ * g₀ ∈ H₂
  have hconj_in : ∀ h ∈ H₁, g₀⁻¹ * h⁻¹ * g₀ ∈ H₂ := by
    intro h hh
    have hfix : (h : G) • y = y := hfixed h hh
    rw [← hg₀] at hfix
    change ((h * g₀ : G) : α) = ((g₀ : G) : α) at hfix
    rw [QuotientGroup.eq] at hfix
    have : (h * g₀)⁻¹ * g₀ = g₀⁻¹ * h⁻¹ * g₀ := by group
    rw [this] at hfix
    exact hfix
  -- Since h⁻¹ ∈ H₁ too, we also get g₀⁻¹ * h * g₀ ∈ H₂
  have hconj_in' : ∀ h ∈ H₁, g₀⁻¹ * h * g₀ ∈ H₂ := by
    intro h hh
    have := hconj_in h⁻¹ (H₁.inv_mem hh)
    rwa [inv_inv] at this
  -- Use g₀⁻¹ as the conjugating element
  use g₀⁻¹
  -- Goal: H₂ = H₁.map (MulAut.conj g₀⁻¹).toMonoidHom
  -- The map sends h to g₀⁻¹ * h * g₀⁻¹⁻¹ = g₀⁻¹ * h * g₀
  -- Show H₁.map ≤ H₂
  have hsub : H₁.map (MulEquiv.toMonoidHom (MulAut.conj g₀⁻¹)) ≤ H₂ := by
    intro x hx
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    exact hconj_in' h hh
  -- Index of the conjugate equals H₁.index = n
  have hidx_conj : (H₁.map (MulEquiv.toMonoidHom (MulAut.conj g₀⁻¹))).index = n := by
    rw [index_map_of_bijective (MulAut.conj g₀⁻¹).bijective]
    exact hH₁
  -- FiniteIndex instance
  haveI : (H₁.map (MulEquiv.toMonoidHom (MulAut.conj g₀⁻¹))).FiniteIndex :=
    ⟨by rw [hidx_conj]; exact hn0⟩
  -- Both have index n, H₁.map ≤ H₂, so equal
  symm
  by_contra hne
  have hlt : H₁.map (MulEquiv.toMonoidHom (MulAut.conj g₀⁻¹)) < H₂ := lt_of_le_of_ne hsub hne
  have := index_strictAnti hlt
  rw [hidx_conj, hH₂] at this
  exact lt_irrefl n this

end Imc2020P7
