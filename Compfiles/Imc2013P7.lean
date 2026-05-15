/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Combinatorics] }

/-!
# International Mathematical Competition 2013, Problem 7

Let `p` and `q` be relatively prime positive integers. Then
`∑_{k=0}^{pq-1} (-1)^(⌊k/p⌋ + ⌊k/q⌋) = 0` if `pq` is even and `= 1` if `pq` is odd.
-/

namespace Imc2013P7

open Finset

snip begin

/-- The sum ∑_{i=0}^{n-1} (-1)^i equals 1 if n is odd and 0 if n is even. -/
lemma sum_neg_one_pow_range (n : ℕ) :
    ∑ i ∈ range n, (-1 : ℤ) ^ i = if Odd n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd n with hn | hn
    · have he : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
      have ho : Odd (n + 1) := Even.add_one hn
      rw [if_neg he, if_pos ho, hn.neg_one_pow]; ring
    · have he : Even (n + 1) := Odd.add_one hn
      have hne : ¬ Odd (n + 1) := Nat.not_odd_iff_even.mpr he
      rw [if_pos hn, if_neg hne, hn.neg_one_pow]; ring

/-- For `0 ≤ k < p*q` and `p > 0`, we have `⌊(p*q-1-k)/p⌋ = q - 1 - ⌊k/p⌋`. -/
lemma floor_pq_sub_one_sub_div {p q k : ℕ} (hp : 0 < p) (_hq : 0 < q) (hk : k < p * q) :
    (p * q - 1 - k) / p = q - 1 - k / p := by
  have h1 : k / p < q := by
    rw [Nat.div_lt_iff_lt_mul hp]; rwa [Nat.mul_comm] at hk
  set a := k / p
  set r := k % p
  have hr : r < p := Nat.mod_lt _ hp
  have heq : a * p + r = k := Nat.div_add_mod' k p
  have ha_le : a + 1 ≤ q := h1
  -- key: p*q = a*p + (q-1-a)*p + p
  have h_qa_sum : a + (q - 1 - a) + 1 = q := by omega
  have hpq_split : p * q = a * p + (q - 1 - a) * p + p := by
    have : p * q = p * (a + (q - 1 - a) + 1) := by rw [h_qa_sum]
    linarith [this]
  -- Therefore p*q - 1 - k = (q-1-a)*p + (p-1-r). Set abbrev.
  set s := (q - 1 - a) * p
  have hpq_eq : p * q - 1 - k = s + (p - 1 - r) := by omega
  rw [hpq_eq]
  -- (q-1-a)*p + (p-1-r) divided by p.
  rw [show (q - 1 - a) * p + (p - 1 - r) = (p - 1 - r) + p * (q - 1 - a) by ring,
      Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt (by omega : p - 1 - r < p)]
  ring

snip end

problem imc2013_p7 (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime p q) :
    ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k / p + k / q) =
      if Odd (p * q) then 1 else 0 := by
  have hpq_pos : 0 < p * q := Nat.mul_pos hp hq
  by_cases hpq_odd : Odd (p * q)
  · -- pq odd case: both p, q odd, sum equals 1.
    rw [if_pos hpq_odd]
    have hpodd : Odd p := (Nat.odd_mul.mp hpq_odd).1
    have hqodd : Odd q := (Nat.odd_mul.mp hpq_odd).2
    -- Step 1: replace ⌊k/p⌋ + ⌊k/q⌋ with k%p + k%q in the sign.
    have step1 : ∀ k ∈ range (p * q),
        (-1 : ℤ) ^ (k / p + k / q) = (-1) ^ (k % p + k % q) := by
      intro k _
      have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
      have hq2 : q % 2 = 1 := Nat.odd_iff.mp hqodd
      -- Use k = (k/p)*p + k%p, p odd ⇒ k ≡ k/p + k%p (mod 2).
      have hk1 : (k / p) * p + k % p = k := Nat.div_add_mod' k p
      have hk2 : (k / q) * q + k % q = k := Nat.div_add_mod' k q
      -- Compute parity (k/p + k/q) mod 2 = (k%p + k%q) mod 2.
      -- Set abbrevs to avoid omega's nonlinear issue.
      set ap := (k / p) * p
      set aq := (k / q) * q
      have hap_par : ap % 2 = (k / p) % 2 := by
        show ((k / p) * p) % 2 = (k / p) % 2
        conv_lhs => rw [Nat.mul_mod, hp2]
        simp
      have haq_par : aq % 2 = (k / q) % 2 := by
        show ((k / q) * q) % 2 = (k / q) % 2
        conv_lhs => rw [Nat.mul_mod, hq2]
        simp
      have e1 : (ap + k % p) % 2 = k % 2 := by rw [hk1]
      have e2 : (aq + k % q) % 2 = k % 2 := by rw [hk2]
      have parity : (k / p + k / q) % 2 = (k % p + k % q) % 2 := by omega
      rw [neg_one_pow_eq_pow_mod_two (R := ℤ) (n := k / p + k / q),
          neg_one_pow_eq_pow_mod_two (R := ℤ) (n := k % p + k % q),
          parity]
    rw [sum_congr rfl step1]
    -- Step 2: reindex via CRT bijection.
    classical
    rw [show
        ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k % p + k % q) =
        ∑ ij ∈ (range p) ×ˢ (range q), (-1 : ℤ) ^ (ij.1 + ij.2) from ?_]
    · -- product sum factors.
      rw [sum_product]
      simp_rw [pow_add]
      rw [← sum_mul_sum]
      rw [sum_neg_one_pow_range, sum_neg_one_pow_range]
      rw [if_pos hpodd, if_pos hqodd]; ring
    · -- The reindexing.
      apply Finset.sum_nbij' (s := range (p * q))
          (t := (range p) ×ˢ (range q))
          (i := fun k => (k % p, k % q))
          (j := fun ij => (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ))
      -- hi : i sends s to t.
      · intro k hk
        simp only [mem_range] at hk
        simp only [mem_product, mem_range]
        exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hq⟩
      -- hj : j sends t to s.
      · intro ij hij
        simp only [mem_product, mem_range] at hij
        simp only [mem_range]
        exact Nat.chineseRemainder_lt_mul hcop ij.1 ij.2
          (Nat.pos_iff_ne_zero.mp hp) (Nat.pos_iff_ne_zero.mp hq)
      -- left_inv : j (i k) = k for k ∈ s.
      · intro k hk
        simp only [mem_range] at hk
        have hcrt := (Nat.chineseRemainder hcop (k % p) (k % q)).2
        have hmod1 : (Nat.chineseRemainder hcop (k % p) (k % q) : ℕ) ≡ k % p [MOD p] := hcrt.1
        have hmod2 : (Nat.chineseRemainder hcop (k % p) (k % q) : ℕ) ≡ k % q [MOD q] := hcrt.2
        have h1 : (Nat.chineseRemainder hcop (k % p) (k % q) : ℕ) ≡ k [MOD p] :=
          hmod1.trans (Nat.mod_modEq k p).symm.symm
        have h2 : (Nat.chineseRemainder hcop (k % p) (k % q) : ℕ) ≡ k [MOD q] :=
          hmod2.trans (Nat.mod_modEq k q).symm.symm
        have hpq_mod : (Nat.chineseRemainder hcop (k % p) (k % q) : ℕ) ≡ k [MOD p * q] :=
          (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
        have hlt : (Nat.chineseRemainder hcop (k % p) (k % q) : ℕ) < p * q :=
          Nat.chineseRemainder_lt_mul hcop _ _
            (Nat.pos_iff_ne_zero.mp hp) (Nat.pos_iff_ne_zero.mp hq)
        exact Nat.ModEq.eq_of_lt_of_lt hpq_mod hlt hk
      -- right_inv : i (j ij) = ij for ij ∈ t.
      · intro ij hij
        simp only [mem_product, mem_range] at hij
        obtain ⟨hi, hj⟩ := hij
        have hcrt := (Nat.chineseRemainder hcop ij.1 ij.2).2
        have hmod1 : (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ) ≡ ij.1 [MOD p] := hcrt.1
        have hmod2 : (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ) ≡ ij.2 [MOD q] := hcrt.2
        have e1 : (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ) % p = ij.1 := by
          have heq : (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ) % p = ij.1 % p := hmod1
          rw [heq, Nat.mod_eq_of_lt hi]
        have e2 : (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ) % q = ij.2 := by
          have heq : (Nat.chineseRemainder hcop ij.1 ij.2 : ℕ) % q = ij.2 % q := hmod2
          rw [heq, Nat.mod_eq_of_lt hj]
        exact Prod.ext e1 e2
      -- h : f a = g (i a)
      · intro k hk; rfl
  · -- pq even case: sum equals 0 by k ↔ pq-1-k pairing.
    rw [if_neg hpq_odd]
    have hpq_even : Even (p * q) := Nat.not_odd_iff_even.mp hpq_odd
    -- p+q is odd.
    have hpq_sum_odd : Odd (p + q) := by
      rcases Nat.even_or_odd p with hpe | hpo
      · have hqo : Odd q := by
          by_contra hnq
          have hqe : Even q := Nat.not_odd_iff_even.mp hnq
          have h2g : 2 ∣ Nat.gcd p q := Nat.dvd_gcd hpe.two_dvd hqe.two_dvd
          rw [hcop] at h2g; omega
        exact hpe.add_odd hqo
      · rcases Nat.even_or_odd q with hqe | hqo
        · exact hpo.add_even hqe
        · exact absurd (hpo.mul hqo) hpq_odd
    -- Sign-flipping pair: σ(k) = pq - 1 - k.
    have swap_eq :
        ∀ k ∈ range (p * q),
          (-1 : ℤ) ^ ((p * q - 1 - k) / p + (p * q - 1 - k) / q) =
          - (-1) ^ (k / p + k / q) := by
      intro k hk
      simp only [mem_range] at hk
      have hkp : k / p < q := by
        rw [Nat.div_lt_iff_lt_mul hp]; rwa [Nat.mul_comm] at hk
      have hk' : k < q * p := by rwa [Nat.mul_comm] at hk
      have hkq : k / q < p := by
        rw [Nat.div_lt_iff_lt_mul hq]; exact hk
      rw [floor_pq_sub_one_sub_div hp hq hk]
      have hflr2 : (q * p - 1 - k) / q = p - 1 - k / q := floor_pq_sub_one_sub_div hq hp hk'
      have hpq_eq : p * q - 1 - k = q * p - 1 - k := by rw [Nat.mul_comm]
      rw [hpq_eq, hflr2]
      have hsum_eq : (q - 1 - k / p) + (p - 1 - k / q) = (p + q - 2) - (k / p + k / q) := by
        omega
      rw [hsum_eq]
      have hpq_ge : 2 ≤ p + q := by omega
      have hpq2_odd : Odd (p + q - 2) := by
        obtain ⟨m, hm⟩ := hpq_sum_odd
        refine ⟨m - 1, ?_⟩; omega
      have hpq2_mod : (p + q - 2) % 2 = 1 := Nat.odd_iff.mp hpq2_odd
      have hb_le : k / p + k / q ≤ p + q - 2 := by omega
      rw [neg_one_pow_eq_pow_mod_two (R := ℤ) (n := (p + q - 2) - (k / p + k / q)),
          neg_one_pow_eq_pow_mod_two (R := ℤ) (n := k / p + k / q)]
      rcases Nat.mod_two_eq_zero_or_one (k / p + k / q) with h0 | h1
      · have hm : ((p + q - 2) - (k / p + k / q)) % 2 = 1 := by omega
        rw [hm, h0]; ring
      · have hm : ((p + q - 2) - (k / p + k / q)) % 2 = 0 := by omega
        rw [hm, h1]; ring
    have invol_sum :
        ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k / p + k / q) =
        ∑ k ∈ range (p * q),
          (-1 : ℤ) ^ ((p * q - 1 - k) / p + (p * q - 1 - k) / q) := by
      apply Finset.sum_nbij' (s := range (p * q)) (t := range (p * q))
          (i := fun k => p * q - 1 - k) (j := fun k => p * q - 1 - k)
      · intro k hk; simp only [mem_range] at hk ⊢; omega
      · intro k hk; simp only [mem_range] at hk ⊢; omega
      · intro k hk; simp only [mem_range] at hk; omega
      · intro k hk; simp only [mem_range] at hk; omega
      · intro k hk
        simp only [mem_range] at hk
        have : p * q - 1 - (p * q - 1 - k) = k := by omega
        rw [this]
    have h_neg : ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k / p + k / q) =
                 - ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k / p + k / q) := by
      calc ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k / p + k / q)
          = ∑ k ∈ range (p * q),
              (-1 : ℤ) ^ ((p * q - 1 - k) / p + (p * q - 1 - k) / q) := invol_sum
        _ = ∑ k ∈ range (p * q), - (-1 : ℤ) ^ (k / p + k / q) := sum_congr rfl swap_eq
        _ = - ∑ k ∈ range (p * q), (-1 : ℤ) ^ (k / p + k / q) := by
            rw [← sum_neg_distrib]
    linarith

end Imc2013P7
