/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.GaloisField

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 2
(IMC 2003, Day 1, Problem 2)

Let `a₁, ..., a₅₁` be nonzero elements of a field. We simultaneously
replace each of them with the sum of the other 50. In this way
we get 51 new numbers. Suppose that the new numbers are, in some order,
the same as the original ones. Prove that the characteristic of the
field must be 2 or 7. Conversely, both 2 and 7 are achievable.

Answer: the set of possible characteristics is `{2, 7}`.
-/

namespace Imc2003P2

/-- The set of possible characteristics. -/
determine answer : Set ℕ := {2, 7}

-- snip begin

/-- If `49` vanishes in a field of prime characteristic `p`, then `p = 7`. -/
lemma char_of_49_eq_zero {F : Type*} [Field F] (p : ℕ) [hp : Fact p.Prime]
    [CharP F p] (h : (49 : F) = 0) : p = 7 := by
  have h49 : (49 : ℕ) = 7 ^ 2 := by norm_num
  have hdvd : p ∣ 49 := by
    have : ((49 : ℕ) : F) = 0 := by push_cast; exact h
    exact (CharP.cast_eq_zero_iff F p 49).mp this
  rw [h49] at hdvd
  have hp7 : p ∣ 7 := hp.out.dvd_of_dvd_pow hdvd
  have h7p : (7 : ℕ).Prime := by decide
  exact (Nat.prime_dvd_prime_iff_eq hp.out h7p).mp hp7

/-- For any fintype `α` with `σ : α ≃ α` and any `f : α → β`,
`univ.val.map (f ∘ σ) = univ.val.map f` as multisets. -/
lemma univ_val_map_comp_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    (σ : α ≃ α) (f : α → β) :
    (Finset.univ : Finset α).val.map (fun i => f (σ i)) =
    (Finset.univ : Finset α).val.map f := by
  -- univ.map σ.toEmbedding = univ, so their val's are equal up to map σ.
  have hmap : (Finset.univ : Finset α).map σ.toEmbedding = Finset.univ :=
    Finset.map_univ_equiv σ
  have hval : ((Finset.univ : Finset α).map σ.toEmbedding).val =
      (Finset.univ : Finset α).val := by rw [hmap]
  have hmap_val : ((Finset.univ : Finset α).map σ.toEmbedding).val =
      (Finset.univ : Finset α).val.map σ := Finset.map_val _ _
  have h1 : (Finset.univ : Finset α).val = (Finset.univ : Finset α).val.map σ := by
    rw [← hmap_val, hval]
  calc (Finset.univ : Finset α).val.map (fun i => f (σ i))
      = ((Finset.univ : Finset α).val.map σ).map f := by
          rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset α).val.map f := by rw [← h1]

/-- Key fact: if a char-≠ 2 field has a multiset `s` of nonzero elements equal to its
negation as a multiset, then `s.card` is even. -/
lemma card_even_of_eq_neg {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    (s : Multiset F) (hnz : ∀ x ∈ s, x ≠ 0)
    (hsym : s = s.map (fun x => -x)) :
    Even s.card := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    subst hn
    by_cases hs_empty : s = 0
    · subst hs_empty; simp
    · obtain ⟨x, hx_mem⟩ : ∃ x, x ∈ s := Multiset.exists_mem_of_ne_zero hs_empty
      set t := s.erase x with ht_def
      have hs : s = x ::ₘ t := (Multiset.cons_erase hx_mem).symm
      have hx_ne : x ≠ 0 := hnz x hx_mem
      have hx_ne_neg : x ≠ -x := by
        intro heq
        have h2x : (2 : F) * x = 0 := by linear_combination heq
        rcases mul_eq_zero.mp h2x with h | h
        · exact hchar h
        · exact hx_ne h
      have hneg_mem : -x ∈ s := by
        have : -x ∈ s.map (fun y => -y) := by
          refine Multiset.mem_map.mpr ⟨x, hx_mem, ?_⟩
          rfl
        rw [← hsym] at this; exact this
      have hneg_mem_t : -x ∈ t := by
        rw [hs] at hneg_mem
        rw [Multiset.mem_cons] at hneg_mem
        rcases hneg_mem with h | h
        · exact absurd h.symm hx_ne_neg
        · exact h
      set u := t.erase (-x) with hu_def
      have ht_eq : t = (-x) ::ₘ u := (Multiset.cons_erase hneg_mem_t).symm
      have hs_eq : s = x ::ₘ ((-x) ::ₘ u) := by rw [hs, ht_eq]
      have hcard_s : s.card = u.card + 2 := by
        rw [hs_eq]; simp [Multiset.card_cons]
      have hnz_u : ∀ y ∈ u, y ≠ 0 := by
        intro y hy
        apply hnz
        rw [hs_eq]
        exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hy)
      have hsym_u : u = u.map (fun y => -y) := by
        have h0 : s.map (fun y => -y) =
            (-x) ::ₘ ((-(-x)) ::ₘ u.map (fun y => -y)) := by
          rw [hs_eq]; simp [Multiset.map_cons]
        have h1 : (-(-x) : F) = x := neg_neg x
        have h2 : s.map (fun y => -y) =
            (-x) ::ₘ (x ::ₘ u.map (fun y => -y)) := by
          rw [h0, h1]
        rw [h2] at hsym
        rw [hs_eq] at hsym
        have hswap : x ::ₘ ((-x) ::ₘ u) = (-x) ::ₘ (x ::ₘ u) := Multiset.cons_swap _ _ _
        rw [hswap] at hsym
        have h3 : x ::ₘ u = x ::ₘ u.map (fun y => -y) :=
          (Multiset.cons_inj_right (-x)).mp hsym
        exact (Multiset.cons_inj_right x).mp h3
      have hcard_u_lt : u.card < s.card := by rw [hcard_s]; omega
      have heven_u : Even u.card := ih u.card hcard_u_lt u hnz_u hsym_u rfl
      rw [hcard_s]
      exact heven_u.add (by decide : Even 2)

-- snip end

/-- The problem statement. -/
problem imc2003_p2 :
    (∀ (F : Type) [Field F] (a : Fin 51 → F),
      (∀ i, a i ≠ 0) →
      (∃ σ : Equiv.Perm (Fin 51), ∀ i, (∑ j, a j) - a i = a (σ i)) →
      ringChar F ∈ answer) ∧
    (∃ (F : Type) (_ : Field F) (_ : CharP F 7) (a : Fin 51 → F),
      (∀ i, a i ≠ 0) ∧ ∃ σ : Equiv.Perm (Fin 51), ∀ i, (∑ j, a j) - a i = a (σ i)) ∧
    (∃ (F : Type) (_ : Field F) (_ : CharP F 2) (a : Fin 51 → F),
      (∀ i, a i ≠ 0) ∧ ∃ σ : Equiv.Perm (Fin 51), ∀ i, (∑ j, a j) - a i = a (σ i)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Forward direction.
    intro F _inst a hnz ⟨σ, hσ⟩
    set S : F := ∑ j, a j with hSdef
    have hsum_b : (∑ i, (S - a i)) = S := by
      have h1 : (∑ i, (S - a i)) = ∑ i, a (σ i) := Finset.sum_congr rfl (fun i _ => hσ i)
      rw [h1, Equiv.sum_comp σ a, ← hSdef]
    have hcard : (Finset.univ : Finset (Fin 51)).card = 51 := by
      simp [Finset.card_univ, Fintype.card_fin]
    have hsum_sub : (∑ i : Fin 51, (S - a i)) = 51 * S - S := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, ← hSdef]
      ring
    have h49S : 49 * S = 0 := by
      have h1 : 51 * S - S = S := hsum_sub ▸ hsum_b
      linear_combination h1
    obtain ⟨p, hp_char⟩ := CharP.exists F
    have hp_prime_or_zero : p = 0 ∨ p.Prime := (CharP.char_is_prime_or_zero F p).symm.imp id id
    have hringChar : ringChar F = p := CharP.eq F (ringChar.charP F) hp_char
    rcases hp_prime_or_zero with hp0 | hp_prime
    · -- Char 0 case: reach contradiction.
      subst hp0
      have h49ne : (49 : F) ≠ 0 := by
        intro h
        have h' : ((49 : ℕ) : F) = 0 := by push_cast; exact h
        have hdvd : (0 : ℕ) ∣ 49 := (CharP.cast_eq_zero_iff F 0 49).mp h'
        have : (49 : ℕ) = 0 := Nat.eq_zero_of_zero_dvd hdvd
        norm_num at this
      have hS0 : S = 0 := by
        rcases mul_eq_zero.mp h49S with h | h
        · exact absurd h h49ne
        · exact h
      have h2ne : (2 : F) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : F) = 0 := by push_cast; exact h
        have hdvd : (0 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff F 0 2).mp h'
        have : (2 : ℕ) = 0 := Nat.eq_zero_of_zero_dvd hdvd
        norm_num at this
      exfalso
      have hb : ∀ i, -a i = a (σ i) := by
        intro i
        have hi := hσ i
        rw [hS0, zero_sub] at hi
        exact hi
      let s : Multiset F := (Finset.univ : Finset (Fin 51)).val.map a
      have hs_card : s.card = 51 := by simp [s]
      have hs_nz : ∀ x ∈ s, x ≠ 0 := by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨i, _, rfl⟩
        exact hnz i
      have hs_sym : s = s.map (fun x => -x) := by
        show (Finset.univ : Finset (Fin 51)).val.map a =
          ((Finset.univ : Finset (Fin 51)).val.map a).map (fun x => -x)
        rw [Multiset.map_map]
        have heq1 : ((fun x : F => -x) ∘ a) = fun i => a (σ i) := by
          funext i; exact hb i
        rw [show ((fun x : F => -x) ∘ a) = ((fun x : F => -x) ∘ a) from rfl]
        rw [heq1]
        exact (univ_val_map_comp_equiv σ a).symm
      have := card_even_of_eq_neg h2ne s hs_nz hs_sym
      rw [hs_card] at this
      exact (by decide : ¬ Even 51) this
    · haveI : Fact p.Prime := ⟨hp_prime⟩
      rcases mul_eq_zero.mp h49S with h49 | hS0
      · right
        show ringChar F = 7
        rw [hringChar]
        exact char_of_49_eq_zero p h49
      · left
        show ringChar F = 2
        rw [hringChar]
        by_contra hp2
        have h2ne : (2 : F) ≠ 0 := by
          intro h
          have h' : ((2 : ℕ) : F) = 0 := by push_cast; exact h
          have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h'
          have h2p : (2 : ℕ).Prime := Nat.prime_two
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp_prime h2p).mp hdvd)
        have hb : ∀ i, -a i = a (σ i) := by
          intro i
          have hi := hσ i
          rw [hS0, zero_sub] at hi
          exact hi
        let s : Multiset F := (Finset.univ : Finset (Fin 51)).val.map a
        have hs_card : s.card = 51 := by simp [s]
        have hs_nz : ∀ x ∈ s, x ≠ 0 := by
          intro x hx
          rcases Multiset.mem_map.mp hx with ⟨i, _, rfl⟩
          exact hnz i
        have hs_sym : s = s.map (fun x => -x) := by
          show (Finset.univ : Finset (Fin 51)).val.map a =
            ((Finset.univ : Finset (Fin 51)).val.map a).map (fun x => -x)
          rw [Multiset.map_map]
          have heq1 : ((fun x : F => -x) ∘ a) = fun i => a (σ i) := by
            funext i; exact hb i
          rw [heq1]
          exact (univ_val_map_comp_equiv σ a).symm
        have := card_even_of_eq_neg h2ne s hs_nz hs_sym
        rw [hs_card] at this
        exact (by decide : ¬ Even 51) this
  · -- Char 7 achievable: F = ZMod 7, a_i = 1 for all i.
    haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
    refine ⟨ZMod 7, inferInstance, ZMod.charP 7, fun _ => 1, ?_, Equiv.refl _, ?_⟩
    · intro _; exact one_ne_zero
    · have hsum : (∑ _j : Fin 51, (1 : ZMod 7)) = 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rfl
      intro i
      rw [hsum]
      rfl
  · -- Char 2 achievable: use GaloisField 2 2, which has 4 elements.
    -- Pick ω ∉ {0, 1}. Then 1, ω, ω+1 are distinct nonzero elements with sum 0.
    -- Use 17 copies of each. σ = identity works since in char 2, -x = x.
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let F := GaloisField 2 2
    haveI : Fintype F := Fintype.ofFinite F
    haveI : CharP F 2 := inferInstance
    -- Get ω ≠ 0, 1.
    have hcard : Fintype.card F = 4 := by
      have : Nat.card F = 2 ^ 2 := GaloisField.card 2 2 (by decide)
      have h1 : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
      omega
    classical
    have hex : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
      by_contra h
      push Not at h
      -- h : ∀ x, x = 0 ∨ x = 1 (after push Not, ¬(x ≠ 0 ∧ x ≠ 1) becomes x = 0 ∨ x = 1)
      have hsub : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := by
        intro x _
        -- h x : x ≠ 0 → x = 1
        by_cases hx0 : x = 0
        · rw [hx0]; exact Finset.mem_insert_self _ _
        · have : x = 1 := h x hx0
          rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have h_le_card : Finset.univ.card ≤ ({0, 1} : Finset F).card := Finset.card_le_card hsub
      have h01 : ({0, 1} : Finset F).card ≤ 2 := by
        calc ({0, 1} : Finset F).card ≤ ({1} : Finset F).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      have : Fintype.card F ≤ 2 := by
        calc Fintype.card F = Finset.univ.card := rfl
          _ ≤ _ := h_le_card
          _ ≤ 2 := h01
      omega
    obtain ⟨ω, hω0, hω1⟩ := hex
    have h2F : (2 : F) = 0 := by
      have := (CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl _)
      exact_mod_cast this
    -- Define a via Fin 17 × Fin 3 ≃ Fin 51.
    -- Block 0 (Fin 3) → 1, block 1 → ω, block 2 → ω+1.
    let b : Fin 3 → F := fun k => if k.val = 0 then 1 else if k.val = 1 then ω else ω + 1
    have hb_ne : ∀ k, b k ≠ 0 := by
      intro k
      show (if k.val = 0 then (1 : F) else if k.val = 1 then ω else ω + 1) ≠ 0
      split_ifs with h0 h1
      · exact one_ne_zero
      · exact hω0
      · intro hc
        apply hω1
        have hωneg : ω = -1 := by linear_combination hc
        rw [hωneg]
        linear_combination -h2F
    have hb0 : b 0 = 1 := by
      show (if (0 : Fin 3).val = 0 then (1 : F) else if (0 : Fin 3).val = 1 then ω else ω + 1) = 1
      rfl
    have hb1 : b 1 = ω := by
      show (if (1 : Fin 3).val = 0 then (1 : F) else if (1 : Fin 3).val = 1 then ω else ω + 1) = ω
      rfl
    have hb2 : b 2 = ω + 1 := by
      show (if (2 : Fin 3).val = 0 then (1 : F) else if (2 : Fin 3).val = 1 then ω else ω + 1) = ω + 1
      rfl
    have hb_sum : (∑ k : Fin 3, b k) = 0 := by
      rw [Fin.sum_univ_three, hb0, hb1, hb2]
      linear_combination h2F + ω * h2F
    -- Use the equivalence Fin 17 × Fin 3 ≃ Fin 51.
    let e : Fin 17 × Fin 3 ≃ Fin 51 := finProdFinEquiv
    let a : Fin 51 → F := fun i => b (e.symm i).2
    refine ⟨F, inferInstance, inferInstance, a, ?_, Equiv.refl _, ?_⟩
    · intro i; exact hb_ne _
    · intro i
      show (∑ j, a j) - a i = a ((Equiv.refl (Fin 51)) i)
      simp only [Equiv.refl_apply]
      have hS : (∑ j : Fin 51, a j) = 0 := by
        show (∑ j : Fin 51, b (e.symm j).2) = 0
        rw [← Equiv.sum_comp e (fun j => b (e.symm j).2)]
        simp only [Equiv.symm_apply_apply]
        rw [Fintype.sum_prod_type]
        simp [hb_sum]
      rw [hS, zero_sub]
      linear_combination -(a i) * h2F

end Imc2003P2
