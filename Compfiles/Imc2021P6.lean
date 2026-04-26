/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 6

For a prime `p`, let `GL₂(ℤ/pℤ)` be the group of invertible `2 × 2` matrices
mod `p`, and let `S_p` be the symmetric group on `p` elements. Show that there
is no injective group homomorphism `φ : GL₂(ℤ/pℤ) → S_p`.
-/

namespace Imc2021P6

open Matrix

snip begin

/-- The shear matrix `[[1, 1], [0, 1]]` as an element of `GL₂(ZMod p)`. -/
noncomputable def shearMat (p : ℕ) [Fact p.Prime] : GL (Fin 2) (ZMod p) :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by
    rw [Matrix.det_fin_two_of]; simp)

/-- The underlying matrix of `shearMat p` is `[[1, 1], [0, 1]]`. -/
lemma shearMat_val (p : ℕ) [Fact p.Prime] :
    (shearMat p).val = !![1, 1; 0, 1] := rfl

/-- Raising the shear matrix to a natural power. -/
lemma shearMat_val_pow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((shearMat p) ^ n).val = !![1, (n : ZMod p); 0, 1] := by
  induction n with
  | zero =>
    show (1 : GL (Fin 2) (ZMod p)).val = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    show ((shearMat p) ^ k * (shearMat p)).val = _
    change (((shearMat p) ^ k).val * (shearMat p).val) = _
    rw [ih, shearMat_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (first | (simp [Matrix.mul_apply, Fin.sum_univ_two]; ring) |
               simp [Matrix.mul_apply, Fin.sum_univ_two])

/-- The shear matrix has order `p`. -/
lemma orderOf_shearMat (p : ℕ) [hp : Fact p.Prime] :
    orderOf (shearMat p) = p := by
  have hp_prime := hp.out
  have h2 : (2 : ℕ) ≤ p := hp_prime.two_le
  apply orderOf_eq_prime
  · apply Units.ext
    have := shearMat_val_pow p p
    rw [this]
    show (!![1, (p : ZMod p); 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
    rw [ZMod.natCast_self]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro h
    haveI : Fact (1 < p) := ⟨hp_prime.one_lt⟩
    have hv : ((shearMat p).val) 0 1 = ((1 : GL (Fin 2) (ZMod p)).val) 0 1 := by
      rw [h]
    rw [shearMat_val] at hv
    simp at hv

/-- `-1 : GL₂(ZMod p)` commutes with the shear matrix. -/
lemma neg_one_commute_shearMat (p : ℕ) [hp : Fact p.Prime] :
    Commute (-1 : GL (Fin 2) (ZMod p)) (shearMat p) := by
  unfold Commute SemiconjBy
  rw [neg_one_mul, mul_neg_one]

/-- For odd prime `p`, `-1 : GL₂(ZMod p)` has order 2. -/
lemma orderOf_neg_one_GL (p : ℕ) [hp : Fact p.Prime] (hpo : Odd p) :
    orderOf (-1 : GL (Fin 2) (ZMod p)) = 2 := by
  have hp_prime := hp.out
  apply orderOf_eq_prime
  · rw [neg_one_sq]
  · intro h
    -- `(-1 : GL) = 1` means the underlying matrices are equal.
    have hv : ((-1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0
            = ((1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 := by
      rw [h]
    -- LHS = -1, RHS = 1
    have hlhs : ((-1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = -1 := by
      show (-(1 : Matrix (Fin 2) (Fin 2) (ZMod p))) 0 0 = -1
      simp
    have hrhs : ((1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := by
      simp
    rw [hlhs, hrhs] at hv
    -- `-1 = 1` in `ZMod p` ⇒ `2 = 0` in ZMod p
    have h2zero : ((2 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) = 0 := by linear_combination -(hv : (-1 : ZMod p) = 1)
      exact_mod_cast this
    have hp_dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2zero
    have hpeq2 : p = 2 := by
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd
      have hpge : 2 ≤ p := hp_prime.two_le
      omega
    rcases hpo with ⟨k, hk⟩; omega

/-- The product `(-1) * shearMat p` has order `2 * p` for odd prime `p`. -/
lemma orderOf_neg_shearMat (p : ℕ) [hp : Fact p.Prime] (hpo : Odd p) :
    orderOf ((-1 : GL (Fin 2) (ZMod p)) * shearMat p) = 2 * p := by
  have hcop : Nat.Coprime (orderOf (-1 : GL (Fin 2) (ZMod p))) (orderOf (shearMat p)) := by
    rw [orderOf_neg_one_GL p hpo, orderOf_shearMat p]
    rw [Nat.coprime_two_left]
    exact hpo
  rw [(neg_one_commute_shearMat p).orderOf_mul_eq_mul_orderOf_of_coprime hcop,
      orderOf_neg_one_GL p hpo, orderOf_shearMat p]

/-- No element of `Perm (Fin p)` has order `2 * p` for odd prime `p`. -/
lemma no_perm_of_order_two_mul_p (p : ℕ) [hp : Fact p.Prime] (hpo : Odd p)
    (σ : Equiv.Perm (Fin p)) : orderOf σ ≠ 2 * p := by
  intro hord
  have hp_prime := hp.out
  have hp2 : p ≥ 2 := hp_prime.two_le
  have hp_odd_ne : ¬ 2 ∣ p := by
    intro hd
    rcases hpo with ⟨k, hk⟩; omega
  have hlcm := Equiv.Perm.lcm_cycleType σ
  rw [hord] at hlcm
  -- p divides lcm = 2p so p divides some element of cycleType
  have hp_dvd_lcm : (p : ℕ) ∣ σ.cycleType.lcm := by
    rw [hlcm]; exact ⟨2, by ring⟩
  -- lcm is also divisible by 2
  have h2_dvd_lcm : (2 : ℕ) ∣ σ.cycleType.lcm := by
    rw [hlcm]; exact ⟨p, rfl⟩
  -- By the definition of lcm on multisets in a UFM, p divides lcm ↔ p divides
  -- the lcm of some nonempty subset, hence p divides some element.
  have exists_p_dvd : ∃ c ∈ σ.cycleType, (p : ℕ) ∣ c := by
    -- σ.cycleType.lcm = σ.cycleType.toList.foldr gcdMonoid.lcm 1.
    -- By induction on list, if p is prime and divides lcm of list, p divides some element.
    have : ∀ (s : Multiset ℕ), (p : ℕ) ∣ s.lcm → s ≠ 0 → ∃ c ∈ s, (p : ℕ) ∣ c := by
      intro s hdvd hne
      induction s using Multiset.induction_on with
      | empty => exact absurd rfl hne
      | cons a t ih =>
        simp only [Multiset.lcm_cons] at hdvd
        by_cases hat : (p : ℕ) ∣ a
        · exact ⟨a, Multiset.mem_cons_self _ _, hat⟩
        · -- p ∣ lcm(a, t.lcm), so p ∣ a * t.lcm, but p is prime, so p ∣ t.lcm
          have : (p : ℕ) ∣ t.lcm := by
            have hgl : lcm a t.lcm ∣ a * t.lcm := lcm_dvd_mul a t.lcm
            have := hdvd.trans hgl
            rcases hp_prime.dvd_mul.mp this with h | h
            · exact absurd h hat
            · exact h
          by_cases htempty : t = 0
          · subst htempty
            simp only [Multiset.lcm_zero] at this
            have hp1 : p = 1 := Nat.eq_one_of_dvd_one this
            exact absurd hp1 hp_prime.one_lt.ne'
          obtain ⟨c, hc_mem, hc_dvd⟩ := ih this htempty
          exact ⟨c, Multiset.mem_cons_of_mem hc_mem, hc_dvd⟩
    have hcne : σ.cycleType ≠ 0 := by
      rw [Ne, Equiv.Perm.cycleType_eq_zero]
      intro hσ
      rw [hσ] at hord
      simp at hord
      exact absurd hord (by omega : (1 : ℕ) ≠ 2 * p)
    exact this _ hp_dvd_lcm hcne
  obtain ⟨c, hc_mem, hp_dvd_c⟩ := exists_p_dvd
  -- Similarly, some d ∈ cycleType has 2 ∣ d.
  have exists_2_dvd : ∃ d ∈ σ.cycleType, (2 : ℕ) ∣ d := by
    have : ∀ (s : Multiset ℕ), (2 : ℕ) ∣ s.lcm → s ≠ 0 → ∃ d ∈ s, (2 : ℕ) ∣ d := by
      intro s hdvd hne
      induction s using Multiset.induction_on with
      | empty => exact absurd rfl hne
      | cons a t ih =>
        simp only [Multiset.lcm_cons] at hdvd
        by_cases hat : (2 : ℕ) ∣ a
        · exact ⟨a, Multiset.mem_cons_self _ _, hat⟩
        · have hgl : lcm a t.lcm ∣ a * t.lcm := lcm_dvd_mul a t.lcm
          have hmul := hdvd.trans hgl
          have h2prime : Nat.Prime 2 := Nat.prime_two
          have : (2 : ℕ) ∣ t.lcm := by
            rcases h2prime.dvd_mul.mp hmul with h | h
            · exact absurd h hat
            · exact h
          by_cases htempty : t = 0
          · subst htempty
            simp only [Multiset.lcm_zero] at this
            have h21 : (2 : ℕ) = 1 := Nat.eq_one_of_dvd_one this
            exact absurd h21 (by decide)
          obtain ⟨d, hd_mem, hd_dvd⟩ := ih this htempty
          exact ⟨d, Multiset.mem_cons_of_mem hd_mem, hd_dvd⟩
    have hcne : σ.cycleType ≠ 0 := by
      rw [Ne, Equiv.Perm.cycleType_eq_zero]
      intro hσ; rw [hσ] at hord; simp at hord; omega
    exact this _ h2_dvd_lcm hcne
  obtain ⟨d, hd_mem, h2_dvd_d⟩ := exists_2_dvd
  -- Each element of cycleType divides orderOf = 2p, and is ≥ 2.
  have hc_dvd_2p : c ∣ 2 * p := by
    have := Equiv.Perm.dvd_of_mem_cycleType hc_mem
    rwa [hord] at this
  have hd_dvd_2p : d ∣ 2 * p := by
    have := Equiv.Perm.dvd_of_mem_cycleType hd_mem
    rwa [hord] at this
  have hc_ge : 2 ≤ c := Equiv.Perm.two_le_of_mem_cycleType hc_mem
  have hd_ge : 2 ≤ d := Equiv.Perm.two_le_of_mem_cycleType hd_mem
  -- Sum of cycleType ≤ p.
  have hsum_le : σ.cycleType.sum ≤ p := by
    have := σ.sum_cycleType_le
    simpa [Fintype.card_fin] using this
  -- c is one of {p, 2p} since p ∣ c and c ∣ 2p and c ≥ 2
  have hc_cases : c = p ∨ c = 2 * p := by
    obtain ⟨k, hk⟩ := hp_dvd_c
    -- c = p * k. And c ∣ 2p gives k ∣ 2. So k ∈ {1, 2}.
    have hk_dvd : p * k ∣ 2 * p := hk ▸ hc_dvd_2p
    rw [mul_comm p k] at hk_dvd
    have hk_dvd' : k ∣ 2 := by
      have hp_pos : 0 < p := hp_prime.pos
      exact (Nat.mul_dvd_mul_iff_right hp_pos).mp hk_dvd
    have hk_le : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk_dvd'
    interval_cases k
    · simp at hk; omega
    · left; omega
    · right; omega
  -- But c ≤ sum ≤ p, so c = p.
  have hc_le_sum : c ≤ σ.cycleType.sum :=
    Multiset.le_sum_of_mem hc_mem
  have hc_le_p : c ≤ p := le_trans hc_le_sum hsum_le
  have hc_eq : c = p := by
    rcases hc_cases with h | h
    · exact h
    · omega
  -- Show c ≠ d (as values): c = p is odd, d is even.
  have hcd_diff : c ≠ d := by
    rw [hc_eq]
    intro hpd; rw [← hpd] at h2_dvd_d; exact hp_odd_ne h2_dvd_d
  -- Hence the multiset has at least two elements (with distinct values), so sum ≥ c + d ≥ p + 2.
  have hsum_ge : c + d ≤ σ.cycleType.sum := by
    -- Pull out c, then d is still in the remaining multiset.
    have hc_sum : σ.cycleType = c ::ₘ (σ.cycleType.erase c) := by
      rw [Multiset.cons_erase hc_mem]
    have hd_in_erase : d ∈ σ.cycleType.erase c := by
      rw [Multiset.mem_erase_of_ne (Ne.symm hcd_diff)]
      exact hd_mem
    calc c + d ≤ c + (σ.cycleType.erase c).sum := by
            have := Multiset.le_sum_of_mem hd_in_erase
            omega
      _ = (c ::ₘ (σ.cycleType.erase c)).sum := by rw [Multiset.sum_cons]
      _ = σ.cycleType.sum := by rw [← hc_sum]
  -- Combine: p + 2 ≤ c + d ≤ sum ≤ p. Contradiction.
  omega

snip end

problem imc2021_p6 (p : ℕ) [Fact p.Prime] :
    ¬ ∃ φ : (GL (Fin 2) (ZMod p)) →* Equiv.Perm (Fin p),
      Function.Injective φ := by
  rintro ⟨φ, hφ⟩
  have hp_prime := (Fact.out : p.Prime)
  rcases hp_prime.eq_two_or_odd' with rfl | hpo
  · -- p = 2 case: compare cardinalities. |GL₂(F₂)| = 6 > 2 = |S₂|.
    have hcard : Fintype.card (GL (Fin 2) (ZMod 2)) ≤ Fintype.card (Equiv.Perm (Fin 2)) :=
      Fintype.card_le_of_injective φ hφ
    -- |GL₂(F₂)| = ∏_{i<2} (2² - 2^i) = (4-1)(4-2) = 6
    have hgl : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
      rw [Matrix.card_GL_field]
      simp [Fin.prod_univ_two, ZMod.card]
    have hs2 : Fintype.card (Equiv.Perm (Fin 2)) = 2 := by
      rw [Fintype.card_perm, Fintype.card_fin]; decide
    rw [hs2] at hcard
    rw [Nat.card_eq_fintype_card] at hgl
    rw [hgl] at hcard
    omega
  · -- p odd case: use that orderOf (-1 * shearMat p) = 2p but no such perm order.
    set M := (-1 : GL (Fin 2) (ZMod p)) * shearMat p
    have hordM : orderOf M = 2 * p := orderOf_neg_shearMat p hpo
    have hordφM : orderOf (φ M) = 2 * p := by
      rw [orderOf_injective φ hφ M, hordM]
    exact no_perm_of_order_two_mul_p p hpo (φ M) hordφM

end Imc2021P6
