/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2022, Problem 6

Let `p > 2` be a prime. Prove that there is a permutation
`(x_1, x_2, …, x_{p-1})` of `(1, 2, …, p-1)` such that
`x_1·x_2 + x_2·x_3 + … + x_{p-2}·x_{p-1} ≡ 2 (mod p)`.
-/

namespace Imc2022P6

open Finset

/-- We encode "permutation of `{1, 2, …, p-1}`" as a bijection
`σ : Fin (p-1) → Fin (p-1)`, where we view `σ i` as the value `σ i + 1 ∈ {1, …, p-1}`. -/
problem imc2022_p6 (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    ∃ σ : Equiv.Perm (Fin (p - 1)),
      (∑ i : Fin (p - 2),
          ((((σ ⟨i.val, by have := i.isLt; omega⟩).val + 1 : ℕ) : ZMod p) *
           (((σ ⟨i.val + 1, by have := i.isLt; omega⟩).val + 1 : ℕ) : ZMod p))) = 2 := by
  haveI hfp : Fact p.Prime := ⟨hp⟩
  -- Define σ i to be the value k such that (k+1) ≡ (i+1)⁻¹ (mod p).
  -- Then (σ i).val + 1 ≡ (i+1)⁻¹ (mod p).
  -- Helper: for 1 ≤ m < p, m is nonzero in ZMod p.
  have nonzero : ∀ m : ℕ, 1 ≤ m → m < p → (m : ZMod p) ≠ 0 := by
    intro m hm1 hmp heq
    have : (m : ZMod p).val = 0 := by rw [heq]; exact ZMod.val_zero
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hmp] at this
    omega
  -- The underlying function sends i to (((i+1 : ZMod p)⁻¹).val - 1), as a Fin (p-1).
  -- (i+1)⁻¹.val ∈ {1, ..., p-1}, so subtracting 1 lands in {0, ..., p-2} = Fin (p-1).
  have hsub_valid : ∀ k : Fin (p - 1),
      (((k.val + 1 : ℕ) : ZMod p)⁻¹).val - 1 < p - 1 := by
    intro k
    have hk1 : k.val + 1 < p := by have := k.isLt; omega
    have hk_pos : 1 ≤ k.val + 1 := by omega
    have hne : ((k.val + 1 : ℕ) : ZMod p) ≠ 0 := nonzero _ hk_pos hk1
    have hne' : (((k.val + 1 : ℕ) : ZMod p)⁻¹) ≠ 0 := inv_ne_zero hne
    have hval_lt := ZMod.val_lt (((k.val + 1 : ℕ) : ZMod p)⁻¹)
    have hval_pos : 1 ≤ (((k.val + 1 : ℕ) : ZMod p)⁻¹).val := by
      by_contra hle
      push_neg at hle
      have : (((k.val + 1 : ℕ) : ZMod p)⁻¹).val = 0 := by omega
      exact hne' ((ZMod.val_eq_zero _).mp this)
    omega
  let f : Fin (p - 1) → Fin (p - 1) := fun k =>
    ⟨(((k.val + 1 : ℕ) : ZMod p)⁻¹).val - 1, hsub_valid k⟩
  -- Show f is bijective, hence a permutation.
  have hf_inj : Function.Injective f := by
    intro k l hkl
    simp only [f, Fin.mk.injEq] at hkl
    have hk : k.val + 1 < p := by have := k.isLt; omega
    have hl : l.val + 1 < p := by have := l.isLt; omega
    have hk_pos : 1 ≤ k.val + 1 := by omega
    have hl_pos : 1 ≤ l.val + 1 := by omega
    have hkne : ((k.val + 1 : ℕ) : ZMod p) ≠ 0 := nonzero _ hk_pos hk
    have hlne : ((l.val + 1 : ℕ) : ZMod p) ≠ 0 := nonzero _ hl_pos hl
    have hk_inv_pos : 1 ≤ (((k.val + 1 : ℕ) : ZMod p)⁻¹).val := by
      by_contra hle; push_neg at hle
      have h0 : (((k.val + 1 : ℕ) : ZMod p)⁻¹).val = 0 := by omega
      exact (inv_ne_zero hkne) ((ZMod.val_eq_zero _).mp h0)
    have hl_inv_pos : 1 ≤ (((l.val + 1 : ℕ) : ZMod p)⁻¹).val := by
      by_contra hle; push_neg at hle
      have h0 : (((l.val + 1 : ℕ) : ZMod p)⁻¹).val = 0 := by omega
      exact (inv_ne_zero hlne) ((ZMod.val_eq_zero _).mp h0)
    have hvaleq : (((k.val + 1 : ℕ) : ZMod p)⁻¹).val = (((l.val + 1 : ℕ) : ZMod p)⁻¹).val := by
      omega
    have hinveq : (((k.val + 1 : ℕ) : ZMod p)⁻¹) = (((l.val + 1 : ℕ) : ZMod p)⁻¹) :=
      ZMod.val_injective _ hvaleq
    have heq : ((k.val + 1 : ℕ) : ZMod p) = ((l.val + 1 : ℕ) : ZMod p) := inv_injective hinveq
    have := congrArg ZMod.val heq
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at this
    exact Fin.ext (by omega)
  let σ : Equiv.Perm (Fin (p - 1)) := Equiv.ofBijective f hf_inj.bijective_of_finite
  refine ⟨σ, ?_⟩
  -- The sum.
  -- For k = σ i, (k.val + 1 : ZMod p) = (i+1)⁻¹.
  have hσ_spec : ∀ i : Fin (p - 1),
      (((σ i).val + 1 : ℕ) : ZMod p) = ((i.val + 1 : ℕ) : ZMod p)⁻¹ := by
    intro i
    show ((f i).val + 1 : ℕ) = ((i.val + 1 : ℕ) : ZMod p)⁻¹
    simp only [f]
    have hi : i.val + 1 < p := by have := i.isLt; omega
    have hi_pos : 1 ≤ i.val + 1 := by omega
    have hne : ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := nonzero _ hi_pos hi
    have hne' : (((i.val + 1 : ℕ) : ZMod p)⁻¹) ≠ 0 := inv_ne_zero hne
    have hpos : 1 ≤ (((i.val + 1 : ℕ) : ZMod p)⁻¹).val := by
      by_contra hle; push_neg at hle
      have h0 : (((i.val + 1 : ℕ) : ZMod p)⁻¹).val = 0 := by omega
      exact hne' ((ZMod.val_eq_zero _).mp h0)
    rw [show ((((((i.val + 1 : ℕ) : ZMod p)⁻¹).val - 1) + 1 : ℕ) : ZMod p)
        = (((((i.val + 1 : ℕ) : ZMod p)⁻¹).val : ℕ) : ZMod p) from by
      rw [show (((i.val + 1 : ℕ) : ZMod p)⁻¹).val - 1 + 1
        = (((i.val + 1 : ℕ) : ZMod p)⁻¹).val from by omega]]
    exact ZMod.natCast_zmod_val _
  -- Rewrite each term of the sum.
  have hp2' : 2 < p := hp2
  have hsum_rw : ∀ (i : Fin (p - 2)),
      (((σ ⟨i.val, by have := i.isLt; omega⟩).val + 1 : ℕ) : ZMod p) *
      (((σ ⟨i.val + 1, by have := i.isLt; omega⟩).val + 1 : ℕ) : ZMod p) =
        ((i.val + 1 : ℕ) : ZMod p)⁻¹ - ((i.val + 2 : ℕ) : ZMod p)⁻¹ := by
    intro i
    have hi : i.val < p - 2 := i.isLt
    set j : ℕ := i.val with hj
    have hi1 : j + 1 < p := by omega
    have hi2 : j + 2 < p := by omega
    have hi1_pos : 1 ≤ j + 1 := by omega
    have hi2_pos : 1 ≤ j + 2 := by omega
    have hne1 : ((j + 1 : ℕ) : ZMod p) ≠ 0 := nonzero _ hi1_pos hi1
    have hne2 : ((j + 2 : ℕ) : ZMod p) ≠ 0 := nonzero _ hi2_pos hi2
    rw [hσ_spec ⟨j, by omega⟩, hσ_spec ⟨j + 1, by omega⟩]
    show (((↑j + 1 : ℕ) : ZMod p))⁻¹ * (((↑(j + 1) + 1 : ℕ) : ZMod p))⁻¹ =
      ((j + 1 : ℕ) : ZMod p)⁻¹ - ((j + 2 : ℕ) : ZMod p)⁻¹
    rw [show ((↑(j + 1) + 1 : ℕ) : ZMod p) = ((j + 2 : ℕ) : ZMod p) from by push_cast; ring]
    rw [show ((↑j + 1 : ℕ) : ZMod p) = ((j + 1 : ℕ) : ZMod p) from by push_cast; ring]
    have key : ((j + 1 : ℕ) : ZMod p)⁻¹ - ((j + 2 : ℕ) : ZMod p)⁻¹
          = (((j + 2 : ℕ) : ZMod p) - ((j + 1 : ℕ) : ZMod p))
            * (((j + 1 : ℕ) : ZMod p)⁻¹ * ((j + 2 : ℕ) : ZMod p)⁻¹) := by
      field_simp
    rw [key]
    have : ((j + 2 : ℕ) : ZMod p) - ((j + 1 : ℕ) : ZMod p) = 1 := by push_cast; ring
    rw [this, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => hsum_rw i)]
  -- Convert sum over Fin (p-2) back to range (p-2) then telescope
  rw [show (∑ i : Fin (p - 2),
        (((i.val + 1 : ℕ) : ZMod p)⁻¹ - ((i.val + 2 : ℕ) : ZMod p)⁻¹))
      = ∑ i ∈ Finset.range (p - 2),
        (((i + 1 : ℕ) : ZMod p)⁻¹ - ((i + 2 : ℕ) : ZMod p)⁻¹) from by
    rw [← Fin.sum_univ_eq_sum_range]]
  rw [Finset.sum_range_sub' (f := fun i => ((i + 1 : ℕ) : ZMod p)⁻¹)]
  have h0 : ((0 + 1 : ℕ) : ZMod p)⁻¹ = 1 := by push_cast; exact inv_one
  rw [h0]
  have hp_cast : (((p - 2 : ℕ) + 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
    rw [show ((p - 2 : ℕ) + 1 : ℕ) = p - 1 from by omega]
    have hp1 : 1 ≤ p := by omega
    push_cast [Nat.cast_sub hp1]
    rw [ZMod.natCast_self]; ring
  rw [hp_cast]
  rw [show ((-1 : ZMod p))⁻¹ = -1 from by
    rw [show (-1 : ZMod p) = -(1 : ZMod p) from rfl, inv_neg, inv_one]]
  ring

end Imc2022P6
