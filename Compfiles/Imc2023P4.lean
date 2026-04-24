/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2023, Problem 4

Let `p` be a prime number and let `k` be a positive integer. Suppose that the
numbers `aᵢ = iᵏ + i` for `i = 0, 1, …, p − 1` form a complete residue system
modulo `p`. What is the set of possible remainders of `a₂` upon division by `p`?

Answer: `{4}` for `p > 3`, `{1}` for `p = 3`.
-/

namespace Imc2023P4

/-- The set of possible residues of `a₂ = 2^k + 2` mod `p`, given that
`a_i = i^k + i` forms a complete residue system mod p. -/
determine answer (p : ℕ) : Set ℕ :=
  if p = 3 then {1} else {4}

snip begin

/-- For a finite field of size > 2 and prime, `∏_{α ∈ 𝔽ₚ*} (α^{k-1} + 1) = 1`
implies `2^{k-1} = 1`. (The hard number-theoretic lemma from the solution.) -/
lemma key_product_lemma {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (k : ℕ) (hk : 0 < k)
    (hprod : (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (α ^ (k - 1) + 1)) = 1) :
    (2 : ZMod p) ^ (k - 1) = 1 := by
  sorry

snip end

problem imc2023_p4 (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k)
    (hres : Function.Surjective (fun i : Fin p => ((i.val ^ k + i.val : ℕ) : ZMod p))) :
    ((2 ^ k + 2 : ℕ) % p) ∈ answer p := by
  haveI hfp : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  -- First rule out p = 2.
  rcases lt_or_eq_of_le hp2 with hp_gt2 | hp_eq2
  swap
  · -- p = 2: show contradiction from hres.
    exfalso
    have hp_eq : p = 2 := hp_eq2.symm
    subst hp_eq
    -- In ZMod 2, f(0) = 0 and f(1) = 1 + 1 = 0, so 1 is not in the image.
    obtain ⟨i, hi⟩ := hres 1
    -- Beta-reduce hi.
    change ((i.val ^ k + i.val : ℕ) : ZMod 2) = 1 at hi
    have hi_cases : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
    rcases hi_cases with h0 | h1
    · rw [h0, zero_pow hk.ne'] at hi
      -- hi : ((0 + 0 : ℕ) : ZMod 2) = 1
      have hv : ((0 + 0 : ℕ) : ZMod 2).val = (1 : ZMod 2).val := by rw [hi]
      simp [ZMod.val_one] at hv
    · rw [h1, one_pow] at hi
      -- hi : ((1 + 1 : ℕ) : ZMod 2) = 1
      have hv : ((1 + 1 : ℕ) : ZMod 2).val = (1 : ZMod 2).val := by rw [hi]
      rw [ZMod.val_natCast] at hv
      simp [ZMod.val_one] at hv
  -- Now p ≥ 3.
  have hp3 : 3 ≤ p := hp_gt2
  rcases lt_or_eq_of_le hp3 with hp_gt3 | hp_eq3
  swap
  · -- p = 3 case.
    have hp_eq : p = 3 := hp_eq3.symm
    subst hp_eq
    simp only [answer, if_true, Set.mem_singleton_iff]
    -- We need (2^k + 2) % 3 = 1. Use surjectivity: f(i) for i = 0, 1, 2 cover {0, 1, 2}.
    -- f(0) = 0, f(1) = 2, so f(2) = 1 in ZMod 3, i.e., 2^k + 2 ≡ 1 (mod 3).
    -- The value 2^k mod 3 is 2 if k is odd, 1 if k is even.
    -- For surjectivity, need f(2) = 2^k + 2 ≡ 1, so 2^k ≡ 2 (mod 3), i.e., k odd.
    -- Extract that some i : Fin 3 maps to (1 : ZMod 3).
    obtain ⟨i, hi⟩ := hres 1
    -- Beta-reduce the lambda.
    change ((i.val ^ k + i.val : ℕ) : ZMod 3) = 1 at hi
    -- The only i : Fin 3 with f(i) = 1 is i = 2.
    have hi_val : i.val = 2 := by
      have h_fin : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
        have := i.isLt; omega
      rcases h_fin with h0 | h1 | h2
      · exfalso
        rw [h0, zero_pow hk.ne'] at hi
        have hv : ((0 + 0 : ℕ) : ZMod 3).val = (1 : ZMod 3).val := by rw [hi]
        simp [ZMod.val_one] at hv
      · exfalso
        rw [h1, one_pow] at hi
        have hv : ((1 + 1 : ℕ) : ZMod 3).val = (1 : ZMod 3).val := by rw [hi]
        rw [ZMod.val_natCast] at hv
        simp [ZMod.val_one] at hv
      · exact h2
    rw [hi_val] at hi
    -- hi : ((2^k + 2 : ℕ) : ZMod 3) = 1
    have h_val : ((2 ^ k + 2 : ℕ) : ZMod 3).val = (1 : ZMod 3).val := by rw [hi]
    rw [ZMod.val_natCast] at h_val
    have h1 : (1 : ZMod 3).val = 1 := ZMod.val_one 3
    rw [h1] at h_val
    exact h_val
  -- p > 3 case.
  have hp_ge4 : 4 ≤ p := hp_gt3
  have hp_ne4 : p ≠ 4 := by intro h; subst h; exact absurd hp (by decide)
  have hp_gt4 : 4 < p := lt_of_le_of_ne hp_ge4 (fun h => hp_ne4 h.symm)
  -- The key step: deduce that 2^(k-1) ≡ 1 (mod p).
  -- The argument: ∏ f(i) = ∏ i = 0 (both include 0), but removing 0 gives
  -- ∏_{i≠0} (i^k + i) = ∏_{i≠0} i  (since f restricted to nonzero is a bijection to nonzero).
  -- LHS = ∏_{i≠0} i * (i^{k-1} + 1), so ∏_{i≠0}(i^{k-1}+1) = 1.
  -- By key_product_lemma, 2^{k-1} = 1 in ZMod p, so 2^k = 2, and 2^k + 2 = 4.
  have h_surj_nonzero : ∀ y : ZMod p, y ≠ 0 →
      ∃ i : Fin p, i.val ≠ 0 ∧ ((i.val ^ k + i.val : ℕ) : ZMod p) = y := by
    intro y hy
    obtain ⟨i, hi⟩ := hres y
    refine ⟨i, ?_, hi⟩
    intro hi0
    apply hy
    rw [← hi]
    show ((i.val ^ k + i.val : ℕ) : ZMod p) = 0
    rw [hi0, zero_pow hk.ne']
    simp
  -- Surjectivity on Fin p → ZMod p means f is a bijection (finite equal cardinality).
  have hcard : Fintype.card (Fin p) = Fintype.card (ZMod p) := by
    rw [Fintype.card_fin, ZMod.card]
  have h_bij : Function.Bijective
      (fun i : Fin p => ((i.val ^ k + i.val : ℕ) : ZMod p)) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hres, hcard⟩
  -- Set up the product on ZMod p.
  -- For simplicity, use the bijection Fin p ≃ ZMod p (as Finset).
  have h_prod_all : (∏ α : ZMod p, (α ^ k + α)) = (∏ α : ZMod p, α) := by
    -- Both equal 0, because 0 is in the product.
    have hz : (0 : ZMod p) ∈ (Finset.univ : Finset (ZMod p)) := Finset.mem_univ _
    have h1 : (∏ α : ZMod p, (α ^ k + α)) = 0 :=
      Finset.prod_eq_zero hz (by simp [zero_pow hk.ne'])
    have h2 : (∏ α : ZMod p, α) = 0 :=
      Finset.prod_eq_zero hz rfl
    rw [h1, h2]
  -- Define the polynomial-like map on ZMod p directly.
  let g : ZMod p → ZMod p := fun α => α ^ k + α
  -- Show g is bijective: it is the composition of h_bij's function with the
  -- standard bijection between Fin p and ZMod p.
  have h_g_bij : Function.Bijective g := by
    -- g ∘ (cast : Fin p → ZMod p) = original f (up to defeq)
    -- Instead, show g is surjective, then use finite cardinality.
    have h_g_surj : Function.Surjective g := by
      intro y
      obtain ⟨i, hi⟩ := hres y
      refine ⟨(i.val : ZMod p), ?_⟩
      show (i.val : ZMod p) ^ k + (i.val : ZMod p) = y
      have : ((i.val ^ k + i.val : ℕ) : ZMod p) = (i.val : ZMod p) ^ k + (i.val : ZMod p) := by
        push_cast; ring
      rw [← this]; exact hi
    exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨h_g_surj, rfl⟩
  -- The key claim: ∏_{α ≠ 0} (α^k + α) = ∏_{α ≠ 0} α.
  have h_prod_nonzero :
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (α ^ k + α)) =
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, α) := by
    -- Use that g permutes ZMod p and sends 0 to 0.
    -- So g restricts to a bijection on ZMod p \ {0}.
    have h_g_zero : g 0 = 0 := by simp [g, zero_pow hk.ne']
    have h_g_zero_iff : ∀ α : ZMod p, g α = 0 ↔ α = 0 := by
      intro α
      refine ⟨?_, fun h => by rw [h]; exact h_g_zero⟩
      intro h
      exact h_g_bij.1 (h.trans h_g_zero.symm)
    -- Use prod_nbij' with the inverse from bijectivity.
    let g_inv : ZMod p → ZMod p := Function.invFun g
    have h_g_inv : Function.LeftInverse g_inv g := Function.leftInverse_invFun h_g_bij.1
    have h_g_right : Function.RightInverse g_inv g :=
      Function.rightInverse_invFun h_g_bij.2
    apply Finset.prod_nbij' (fun α => g α) (fun β => g_inv β)
    · intro α hα
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hα
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [h_g_zero_iff]; exact hα.2
    · intro β hβ
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hβ
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h0
      have : g (g_inv β) = g 0 := by rw [h0]
      rw [h_g_right, h_g_zero] at this
      exact hβ.2 this
    · intro α _; exact h_g_inv α
    · intro β _; exact h_g_right β
    · intros; rfl
  -- Now factor: ∏ α * (α^{k-1} + 1) = ∏ α, so ∏ (α^{k-1} + 1) = 1.
  have h_factor : ∀ α : ZMod p, α ≠ 0 → α ^ k + α = α * (α ^ (k - 1) + 1) := by
    intro α hα
    have : α ^ k = α * α ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]; ring
  have h_prod_factored :
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (α ^ k + α)) =
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, α) *
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (α ^ (k - 1) + 1)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro α hα
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hα
    exact h_factor α hα.2
  -- Combine with h_prod_nonzero to get ∏ (α^{k-1}+1) = 1.
  have h_prod_nonzero_nonzero :
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, α) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro α hα
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hα
    exact hα.2
  have h_prod_key :
      (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (α ^ (k - 1) + 1)) = 1 := by
    have := h_prod_nonzero.symm.trans h_prod_factored
    -- this : ∏ α = ∏ α * ∏ (α^{k-1}+1)
    have h1 : (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, α) *
              (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (α ^ (k - 1) + 1)) =
              (∏ α ∈ (Finset.univ : Finset (ZMod p)) \ {0}, α) * 1 := by
      rw [mul_one]; exact this.symm
    exact mul_left_cancel₀ h_prod_nonzero_nonzero h1
  -- Apply the key lemma to get 2^(k-1) = 1.
  have h_two_pow : (2 : ZMod p) ^ (k - 1) = 1 := key_product_lemma hp_gt3 k hk h_prod_key
  -- Derive 2^k + 2 ≡ 4 (mod p).
  simp only [answer, if_neg (show p ≠ 3 by omega), Set.mem_singleton_iff]
  have h_two_k : (2 : ZMod p) ^ k = 2 := by
    have : k = (k - 1) + 1 := by omega
    rw [this, pow_succ, h_two_pow, one_mul]
  have h_val : ((2 ^ k + 2 : ℕ) : ZMod p) = 4 := by
    push_cast
    rw [h_two_k]
    norm_num
  -- Now convert to % p form.
  have h4 : (4 : ZMod p).val = 4 := by
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by push_cast; rfl]
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hp_gt4
  have : ((2 ^ k + 2 : ℕ) : ZMod p).val = (4 : ZMod p).val := by rw [h_val]
  rw [ZMod.val_natCast] at this
  rw [h4] at this
  exact this

end Imc2023P4
