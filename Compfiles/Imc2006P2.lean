/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2006, Problem 2

Find the number of positive integers `x` satisfying `x < 10^2006` and
`10^2006 ∣ x^2 - x`.

Answer: `3`.

## Proof outline

Solutions in `[0, 10^2006)` are in bijection with the idempotents of
`ZMod (10^2006)`. By the Chinese Remainder Theorem,
`ZMod (10^2006) ≃+* ZMod (2^2006) × ZMod (5^2006)`, and idempotents correspond
to pairs of idempotents in the two factors. In a prime-power modulus, the
only idempotents are `0` and `1`, giving `2 * 2 = 4` idempotents in total.
Three of these correspond to positive values of `x`, so the answer is `3`.
-/

namespace Imc2006P2

open scoped Classical

/-- The positive solutions of `N ∣ x * (x - 1)` with `0 < x < N`. We express the divisibility
over the integers to avoid natural-number subtraction. -/
def positiveSolutionSet (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun x => 0 < x ∧ (N : ℤ) ∣ (x : ℤ) * ((x : ℤ) - 1)

determine solution_value : ℕ := 3

snip begin

/-- In a prime-power modulus `p^k` with `k ≥ 1`, the only idempotents are `0` and `1`. -/
lemma idempotent_zmod_primePow {p : ℕ} (hp : p.Prime) {k : ℕ} (_hk : 0 < k)
    (x : ZMod (p^k)) (hx : x * x = x) : x = 0 ∨ x = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpk_pos : 0 < p^k := pow_pos hp.pos k
  haveI : NeZero (p^k) := ⟨Nat.pos_iff_ne_zero.mp hpk_pos⟩
  -- Let `n = x.val`.
  set n : ℕ := x.val with hn_def
  have hn_lt : n < p^k := ZMod.val_lt x
  have hx_eq : ((n : ℤ) : ZMod (p^k)) = x := by
    rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val x
  -- `p^k ∣ n*(n-1)` in `ℤ`.
  have hdvd : (p^k : ℤ) ∣ (n : ℤ) * ((n : ℤ) - 1) := by
    have hz : (((n : ℤ) * ((n : ℤ) - 1) : ℤ) : ZMod (p^k)) = 0 := by
      push_cast
      have hxn : (n : ZMod (p^k)) = x := by
        have := hx_eq; push_cast at this; exact this
      rw [hxn]
      have : x * (x - 1) = x * x - x := by ring
      rw [this, hx]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^k)).mp hz
    rwa [Int.natCast_pow] at this
  -- `p` is prime in ℤ.
  have hp_int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- Case-split on whether `p ∣ n`.
  by_cases hpn : (p : ℤ) ∣ (n : ℤ)
  · -- `p ∣ n`, so `p ∤ n - 1` (else `p ∣ 1`). Hence `p^k ∣ n`.
    have hp_not_nm1 : ¬ (p : ℤ) ∣ ((n : ℤ) - 1) := by
      intro h
      have h1 : (p : ℤ) ∣ 1 := by
        have := hpn.sub h
        simpa using this
      have hpos : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
      have := Int.le_of_dvd one_pos h1
      linarith
    -- So `p^k ∣ n`.
    have hpk_dvd_n : (p : ℤ)^k ∣ (n : ℤ) :=
      hp_int_prime.pow_dvd_of_dvd_mul_right k hp_not_nm1 hdvd
    rw [← Int.natCast_pow] at hpk_dvd_n
    left
    have hn0 : n = 0 := by
      rw [Int.natCast_dvd_natCast] at hpk_dvd_n
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · exfalso
        exact Nat.not_lt.mpr (Nat.le_of_dvd h hpk_dvd_n) hn_lt
    rw [← hx_eq, hn0]; push_cast; rfl
  · -- `p ∤ n`. Hence `p^k ∣ n - 1`.
    have hpk_dvd_nm1 : (p : ℤ)^k ∣ ((n : ℤ) - 1) :=
      hp_int_prime.pow_dvd_of_dvd_mul_left k hpn hdvd
    right
    have hn1 : n = 1 := by
      -- `(p^k : ℤ) ∣ n - 1` with `0 ≤ n < p^k`.
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        apply hpn
        rw [h]; exact dvd_zero _
      · -- `n ≥ 1`, so `n - 1 ≥ 0`, and `n - 1 < p^k`.
        have hnm1_nn : (0 : ℤ) ≤ (n : ℤ) - 1 := by
          have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h
          linarith
        have hnm1_lt : (n : ℤ) - 1 < (p^k : ℤ) := by
          have : (n : ℤ) < (p^k : ℤ) := by
            have := hn_lt
            exact_mod_cast this
          linarith
        -- `(p^k : ℤ) ∣ n - 1` with `0 ≤ n - 1 < p^k` means `n - 1 = 0`.
        have hpk_pos_int : (0 : ℤ) < (p^k : ℤ) := by exact_mod_cast hpk_pos
        have : (n : ℤ) - 1 = 0 := by
          rcases hpk_dvd_nm1 with ⟨c, hc⟩
          have hc_nn : 0 ≤ c := by
            by_contra hc_neg
            push Not at hc_neg
            have : (p : ℤ)^k * c < 0 :=
              mul_neg_of_pos_of_neg (by exact_mod_cast hpk_pos) hc_neg
            rw [← hc] at this
            linarith
          have hc_lt : c < 1 := by
            by_contra hc1
            push Not at hc1
            have : (p : ℤ)^k ≤ (p : ℤ)^k * c := by
              calc (p : ℤ)^k = (p : ℤ)^k * 1 := (mul_one _).symm
                _ ≤ (p : ℤ)^k * c := by
                  exact mul_le_mul_of_nonneg_left hc1 (le_of_lt (by exact_mod_cast hpk_pos))
            rw [← hc] at this
            linarith
          have hc0 : c = 0 := by omega
          rw [hc, hc0, mul_zero]
        linarith
    rw [← hx_eq, hn1]; push_cast; rfl

/-- The idempotents of `ZMod (p^k)` as a Finset, for `p` prime and `k ≥ 1`. -/
lemma card_idempotents_primePow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    haveI : NeZero (p^k) := ⟨Nat.pos_iff_ne_zero.mp (pow_pos hp.pos k)⟩
    ((Finset.univ : Finset (ZMod (p^k))).filter fun x => x * x = x).card = 2 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpk_pos : 0 < p^k := pow_pos hp.pos k
  haveI : NeZero (p^k) := ⟨Nat.pos_iff_ne_zero.mp hpk_pos⟩
  -- Show filtered set equals {0, 1}.
  have heq : (Finset.univ.filter fun x : ZMod (p^k) => x * x = x) =
      ({0, 1} : Finset (ZMod (p^k))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      exact idempotent_zmod_primePow hp hk x hx
    · rintro (rfl | rfl) <;> ring
  rw [heq]
  have hne : (0 : ZMod (p^k)) ≠ 1 := by
    have hpk_ge : 2 ≤ p^k := by
      calc 2 ≤ p := hp.two_le
        _ = p^1 := (pow_one p).symm
        _ ≤ p^k := Nat.pow_le_pow_right hp.pos hk
    intro h
    have h0 : (0 : ZMod (p^k)).val = 0 := ZMod.val_zero
    have h1 : (1 : ZMod (p^k)).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr (by omega)]
    rw [h] at h0
    rw [h1] at h0
    exact absurd h0 one_ne_zero
  rw [Finset.card_insert_of_notMem (by simp [hne])]
  simp

/-- The set of all solutions of `N ∣ x * (x - 1)` with `0 ≤ x < N`. -/
def allSolutionSet (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun x => (N : ℤ) ∣ (x : ℤ) * ((x : ℤ) - 1)

/-- Bijection between solutions in `[0, N)` and idempotents of `ZMod N`. -/
lemma allSolutionSet_card_eq_idempotents {N : ℕ} [NeZero N] :
    (allSolutionSet N).card =
      ((Finset.univ : Finset (ZMod N)).filter fun x => x * x = x).card := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Bijection: `n ↦ (n : ZMod N)` with inverse `e ↦ e.val`.
  refine Finset.card_bij' (fun n _ => (n : ZMod N)) (fun e _ => (ZMod.val e))
    ?_ ?_ ?_ ?_
  · -- Maps to: `n ∈ allSolutionSet N → (n : ZMod N) * (n : ZMod N) = (n : ZMod N)`.
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [allSolutionSet, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨_, hdvd⟩ := hn
    -- From `(N : ℤ) ∣ n * (n - 1)`, derive `n * n = n` in ZMod N.
    have hz : ((n : ℤ) * ((n : ℤ) - 1) : ZMod N) = 0 := by
      rw [show ((n : ℤ) * ((n : ℤ) - 1) : ZMod N) =
        (((n : ℤ) * ((n : ℤ) - 1) : ℤ) : ZMod N) from by push_cast; ring]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hdvd
    have : (n : ZMod N) * ((n : ZMod N) - 1) = 0 := by
      have := hz; push_cast at this; exact this
    have hfin : (n : ZMod N) * (n : ZMod N) = (n : ZMod N) := by
      have h2 : (n : ZMod N) * ((n : ZMod N) - 1) = (n : ZMod N) * (n : ZMod N) - (n : ZMod N) := by
        ring
      rw [h2] at this
      linear_combination this
    exact hfin
  · -- Maps to: `e ∈ idempotents → e.val ∈ allSolutionSet`.
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp only [allSolutionSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt e, ?_⟩
    -- Need `(N : ℤ) ∣ e.val * (e.val - 1)`.
    have hz : ((e.val : ℤ) * ((e.val : ℤ) - 1) : ZMod N) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      have h2 : e * (e - 1) = e * e - e := by ring
      rw [h2, he]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by
      rw [show (((e.val : ℤ) * ((e.val : ℤ) - 1) : ℤ) : ZMod N) =
        ((e.val : ℤ) * ((e.val : ℤ) - 1) : ZMod N) from by push_cast; ring]
      exact hz)
    exact this
  · -- Left inverse: `(n : ZMod N).val = n` when `n < N`.
    intro n hn
    simp only [allSolutionSet, Finset.mem_filter, Finset.mem_range] at hn
    exact ZMod.val_cast_of_lt hn.1
  · -- Right inverse: `((e.val : ℕ) : ZMod N) = e`.
    intro e _
    exact ZMod.natCast_zmod_val e

/-- Pair-split: idempotents of `ZMod (a * b)` when `Coprime a b` correspond to pairs of
idempotents in `ZMod a × ZMod b`. -/
lemma card_idempotents_mul_coprime {a b : ℕ} [NeZero a] [NeZero b]
    (hab : a.Coprime b) :
    haveI : NeZero (a * b) :=
      ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne a))
                                            (Nat.pos_of_ne_zero (NeZero.ne b)))⟩
    ((Finset.univ : Finset (ZMod (a * b))).filter fun x => x * x = x).card =
      ((Finset.univ : Finset (ZMod a)).filter fun x => x * x = x).card *
      ((Finset.univ : Finset (ZMod b)).filter fun x => x * x = x).card := by
  haveI : NeZero (a * b) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne a))
                                          (Nat.pos_of_ne_zero (NeZero.ne b)))⟩
  -- Use CRT ring equivalence `ZMod (a*b) ≃+* ZMod a × ZMod b`.
  let e := ZMod.chineseRemainder hab
  -- Idempotents are preserved under the ring equivalence.
  have hcard : ((Finset.univ : Finset (ZMod (a * b))).filter fun x => x * x = x).card =
      ((Finset.univ : Finset (ZMod a × ZMod b)).filter fun p => p * p = p).card := by
    refine Finset.card_bij' (fun x _ => e.toEquiv x) (fun p _ => e.symm.toEquiv p)
      ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have := hx
      have hhom : e (x * x) = e x * e x := map_mul _ _ _
      rw [this] at hhom
      simpa using hhom.symm
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hhom : e.symm (p * p) = e.symm p * e.symm p := map_mul _ _ _
      rw [hp] at hhom
      exact hhom.symm
    · intro x _; simp
    · intro p _; simp
  rw [hcard]
  -- Now count pairs of idempotents.
  rw [show ((Finset.univ : Finset (ZMod a × ZMod b)).filter fun p => p * p = p) =
    ((Finset.univ : Finset (ZMod a)).filter fun x => x * x = x) ×ˢ
    ((Finset.univ : Finset (ZMod b)).filter fun x => x * x = x) from ?_]
  · rw [Finset.card_product]
  · ext ⟨u, v⟩
    simp [Prod.mk_mul_mk, Prod.mk.injEq]

/-- Key lemma: for `N = a * b` with `a, b` prime powers and coprime, the positive solutions
to `N ∣ x(x-1)` in `[0, N)` has cardinality `3`. -/
lemma positiveSolutionSet_card_primePow_primePow
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    (positiveSolutionSet (p^j * q^k)).card = 3 := by
  have hp_pos : 0 < p^j := pow_pos hp.pos j
  have hq_pos : 0 < q^k := pow_pos hq.pos k
  haveI : NeZero (p^j) := ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩
  haveI : NeZero (q^k) := ⟨Nat.pos_iff_ne_zero.mp hq_pos⟩
  haveI : NeZero (p^j * q^k) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos hp_pos hq_pos)⟩
  have hcop : (p^j).Coprime (q^k) := by
    exact (Nat.coprime_pow_left_iff hj _ _).mpr
      ((Nat.coprime_pow_right_iff hk _ _).mpr
        ((Nat.coprime_primes hp hq).mpr hpq))
  have hN_pos : 0 < p^j * q^k := Nat.mul_pos hp_pos hq_pos
  have hall_card : (allSolutionSet (p^j * q^k)).card = 4 := by
    rw [allSolutionSet_card_eq_idempotents]
    rw [card_idempotents_mul_coprime hcop]
    rw [card_idempotents_primePow hp hj, card_idempotents_primePow hq hk]
  have h0_mem : 0 ∈ allSolutionSet (p^j * q^k) := by
    unfold allSolutionSet
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hN_pos, ?_⟩
    show ((p^j * q^k : ℕ) : ℤ) ∣ ((0 : ℕ) : ℤ) * (((0 : ℕ) : ℤ) - 1)
    rw [Nat.cast_zero, zero_mul]
    exact dvd_zero _
  have herase : positiveSolutionSet (p^j * q^k) =
      (allSolutionSet (p^j * q^k)).erase 0 := by
    ext x
    unfold positiveSolutionSet allSolutionSet
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hx_range, hx_pos, hx_dvd⟩
      refine ⟨?_, hx_range, hx_dvd⟩
      omega
    · rintro ⟨hx_ne, hx_range, hx_dvd⟩
      refine ⟨hx_range, ?_, hx_dvd⟩
      omega
  rw [herase, Finset.card_erase_of_mem h0_mem, hall_card]

snip end

problem imc2006_p2 :
    (positiveSolutionSet (10^2006)).card = solution_value := by
  have h10_eq : (10 : ℕ)^2006 = 2^2006 * 5^2006 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.mul_pow]
  rw [h10_eq]
  exact positiveSolutionSet_card_primePow_primePow Nat.prime_two (by decide)
    (by decide) (by omega) (by omega)

end Imc2006P2
