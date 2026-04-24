/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Competition 2022, Problem 3

Let `p` be a prime. A flea sits at `0 ∈ ℝ`. Each minute it may stay, move left
by `1`, or move right by `1`. After `p − 1` minutes it wants to be at `0`
again. Let `f(p)` be the number of such strategies. Find `f(p) mod p`.

Answer:
- `f(3) ≡ 0 (mod 3)`;
- if `p ≡ 1 (mod 3)`, then `f(p) ≡ 1 (mod p)`;
- if `p ≡ 2 (mod 3)`, then `f(p) ≡ −1 (mod p)`.
-/

namespace Imc2022P3

/-- The number of strategies: count functions s : Fin (p-1) → {-1, 0, 1} with
`∑ i, s i = 0`. Represented as count of tuples in `Fin (p-1) → ({-1,0,1} ⊆ ℤ)`. -/
noncomputable def f (p : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Fin (p - 1) → Fin 3 =>
    (∑ i, ((s i).val : ℤ) - (p - 1 : ℤ)) = 0).card
  -- Note: encoding s i = 0 as "left (-1)", 1 as "stay (0)", 2 as "right (+1)",
  -- so the flea moves (s i).val - 1 each minute; sum = ∑(s i).val - (p-1) = 0.

/-- The residue class of `f(p)` mod `p`. -/
determine answer (p : ℕ) : ZMod p :=
  if p = 3 then 0
  else if p % 3 = 1 then 1
  else -1

-- snip begin

open Polynomial in
/-- Rewrite `f p` in terms of the sum condition without the subtraction. -/
lemma f_eq_count (p : ℕ) (hp : 1 ≤ p) :
    f p =
      (Finset.univ.filter fun s : Fin (p - 1) → Fin 3 =>
        (∑ i, (s i).val) = p - 1).card := by
  unfold f
  congr 1
  apply Finset.filter_congr
  intro s _
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p - 1 : ℤ) := by omega
  have hnat : (∑ i, ((s i).val : ℤ)) = ((∑ i, (s i).val : ℕ) : ℤ) := by push_cast; rfl
  rw [hnat, ← hp1]
  constructor
  · intro h; exact_mod_cast (by linarith : ((∑ i, (s i).val : ℕ) : ℤ) = ((p - 1 : ℕ) : ℤ))
  · intro h; have : ((∑ i, (s i).val : ℕ) : ℤ) = ((p - 1 : ℕ) : ℤ) := by exact_mod_cast h
    linarith

open Polynomial in
/-- The generating polynomial encoding flea strategies: the coefficient of `X^(p-1)`
in `(1 + X + X^2)^(p-1)` equals `f p`. -/
theorem f_eq_coeff (p : ℕ) (hp : 1 ≤ p) :
    (f p : ZMod p) =
      ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)).coeff (p - 1) := by
  -- Rewrite 1+X+X² as ∑_{j:Fin 3} X^j.
  have hsum3 : (1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) =
      ∑ j : Fin 3, Polynomial.X ^ (j : ℕ) := by
    simp [Fin.sum_univ_three, pow_zero, pow_one, pow_two]
  rw [hsum3, Finset.sum_pow']
  rw [Polynomial.finset_sum_coeff]
  have heach : ∀ s : Fin (p - 1) → Fin 3,
      (∏ i : Fin (p - 1), Polynomial.X ^ ((s i : Fin 3) : ℕ) : (ZMod p)[X]) =
        Polynomial.X ^ (∑ i, ((s i : Fin 3) : ℕ)) := by
    intro s
    rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [heach, Polynomial.coeff_X_pow]
  rw [f_eq_count p hp]
  -- Want: (card : ZMod p) = ∑_s if (∑(s i).val) = p-1 then 1 else 0
  -- Since piFinset (fun _ => univ) = univ (as Finset) -- use Fintype.piFinset_univ
  have hpi : Fintype.piFinset (fun _ : Fin (p - 1) => (Finset.univ : Finset (Fin 3))) =
             (Finset.univ : Finset (Fin (p - 1) → Fin 3)) :=
    Fintype.piFinset_univ
  rw [hpi]
  -- Goal: (card filter : ZMod p) = ∑ s, (if p-1 = ∑(s i) then 1 else 0)
  symm
  have hfeq : (fun s : Fin (p - 1) → Fin 3 =>
            (if p - 1 = ∑ i, ((s i : Fin 3) : ℕ) then (1 : ZMod p) else 0)) =
          (fun s => if (∑ i, (s i).val) = p - 1 then (1 : ZMod p) else 0) := by
    funext s
    by_cases h : (∑ i, (s i).val) = p - 1
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg]
      intro heq
      exact h heq.symm
  rw [hfeq, Finset.sum_boole]

open Polynomial in
/-- The key polynomial identity in `ZMod p[X]`:
  `(1 + X + X^2)^(p-1) * (1 - X^p) = (1 - X^3)^(p-1) * (1 - X)`. -/
theorem key_identity (p : ℕ) [hp : Fact p.Prime] :
    ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)) *
      (1 - Polynomial.X ^ p) =
    ((1 - Polynomial.X ^ 3 : (ZMod p)[X]) ^ (p - 1)) * (1 - Polynomial.X) := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hcp : CharP (ZMod p) p := ZMod.charP p
  -- In ZMod p: (1 - X)^p = 1 - X^p by Frobenius
  have hfrob : ((1 : (ZMod p)[X]) - Polynomial.X) ^ p = 1 - Polynomial.X ^ p := by
    rw [sub_pow_char]
    simp
  -- Factor: (1-X)^p = (1-X) * (1-X)^(p-1)
  have hsplit : ((1 : (ZMod p)[X]) - Polynomial.X) ^ p =
      (1 - Polynomial.X) * ((1 - Polynomial.X) ^ (p - 1)) := by
    have hpeq : (p - 1) + 1 = p := Nat.sub_add_cancel hp1
    calc ((1 : (ZMod p)[X]) - Polynomial.X) ^ p
        = ((1 : (ZMod p)[X]) - Polynomial.X) ^ ((p - 1) + 1) := by rw [hpeq]
      _ = ((1 : (ZMod p)[X]) - Polynomial.X) ^ (p - 1) * (1 - Polynomial.X) := pow_succ _ _
      _ = (1 - Polynomial.X) * (1 - Polynomial.X) ^ (p - 1) := by ring
  -- (1+X+X²)(1-X) = 1-X³, so (1+X+X²)^(p-1)(1-X)^(p-1) = (1-X³)^(p-1)
  have hfact : ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) * (1 - Polynomial.X)) =
      1 - Polynomial.X ^ 3 := by ring
  have hpow : ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)) *
      ((1 - Polynomial.X) ^ (p - 1)) = (1 - Polynomial.X ^ 3) ^ (p - 1) := by
    rw [← mul_pow, hfact]
  calc ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)) *
         (1 - Polynomial.X ^ p)
      = ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)) *
          ((1 - Polynomial.X) ^ p) := by rw [hfrob]
    _ = ((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)) *
          ((1 - Polynomial.X) * ((1 - Polynomial.X) ^ (p - 1))) := by rw [hsplit]
    _ = (((1 + Polynomial.X + Polynomial.X ^ 2 : (ZMod p)[X]) ^ (p - 1)) *
          ((1 - Polynomial.X) ^ (p - 1))) * (1 - Polynomial.X) := by ring
    _ = (1 - Polynomial.X ^ 3) ^ (p - 1) * (1 - Polynomial.X) := by rw [hpow]

/-- Identity `C(p-1, k) ≡ (-1)^k (mod p)` for `0 ≤ k ≤ p-1`. -/
theorem choose_pred_prime (p k : ℕ) [hp : Fact p.Prime] (hk : k ≤ p - 1) :
    ((p - 1).choose k : ZMod p) = (-1 : ZMod p) ^ k := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ p - 1 := Nat.le_of_succ_le hk
    have hkp : k + 1 < p := by omega
    have hk1p : k + 1 ≤ p := hkp.le
    -- Pascal: choose p (k+1) = choose (p-1) (k+1) + choose (p-1) k
    have hpas : p.choose (k + 1) = (p - 1).choose (k + 1) + (p - 1).choose k := by
      have hpeq : p = (p - 1) + 1 := (Nat.sub_add_cancel hp1).symm
      conv_lhs => rw [hpeq]
      rw [Nat.choose_succ_succ, Nat.add_comm]
    -- p divides choose p (k+1) since 0 < k+1 < p
    have hdvd : p ∣ p.choose (k + 1) :=
      hp.out.dvd_choose_self (by omega) hkp
    -- In ZMod p: choose p (k+1) = 0, so choose (p-1) (k+1) = -choose (p-1) k
    have hpcast : (p.choose (k + 1) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd
    have heq : ((p - 1).choose (k + 1) : ZMod p) + ((p - 1).choose k : ZMod p) = 0 := by
      have : (((p - 1).choose (k + 1) + (p - 1).choose k : ℕ) : ZMod p) = 0 := by
        rw [← hpas]; exact hpcast
      push_cast at this; exact this
    have hneg : ((p - 1).choose (k + 1) : ZMod p) = -((p - 1).choose k : ZMod p) := by
      linear_combination heq
    rw [hneg, ih hk', pow_succ]; ring

open Polynomial in
/-- Coefficient of X^n in (1 - X^3)^m in any commutative ring. -/
lemma coeff_one_sub_X_cubed_pow {R : Type*} [CommRing R] (m n : ℕ) :
    ((1 - Polynomial.X ^ 3 : R[X]) ^ m).coeff n =
      if 3 ∣ n ∧ n / 3 ≤ m then (-1) ^ (n / 3) * (m.choose (n / 3) : R) else 0 := by
  have hexp : ((1 - Polynomial.X ^ 3 : R[X]) ^ m) =
      ∑ k ∈ Finset.range (m + 1),
        Polynomial.C ((-1) ^ k * (m.choose k : R)) * Polynomial.X ^ (3 * k) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, mul_one, map_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1,
        ← Polynomial.C_eq_natCast]
    have hneg : (-Polynomial.X ^ 3 : R[X]) ^ k = (-1) ^ k * Polynomial.X ^ (3 * k) := by
      rw [neg_pow]
      rw [show (Polynomial.X ^ 3 : R[X]) ^ k = Polynomial.X ^ (3 * k) from by
        rw [← pow_mul]]
    rw [hneg]; ring
  rw [hexp, Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with hcond
  · obtain ⟨hdvd, hle⟩ := hcond
    rw [Finset.sum_eq_single (n / 3)]
    · rw [if_pos (Nat.div_mul_cancel hdvd |>.symm.trans (by ring))]
      ring
    · intro k _ hne
      have : ¬ (n = 3 * k) := by
        intro h; apply hne
        rw [h, Nat.mul_div_cancel_left _ (by norm_num : (3:ℕ) > 0)]
      rw [if_neg this]; ring
    · intro hn
      rw [Finset.mem_range] at hn; omega
  · push_neg at hcond
    apply Finset.sum_eq_zero
    intro k hk
    by_cases h3k : n = 3 * k
    · exfalso
      have hdvd : 3 ∣ n := ⟨k, h3k⟩
      have hk3 : n / 3 = k := by
        rw [h3k, Nat.mul_div_cancel_left _ (by norm_num : (3:ℕ) > 0)]
      rw [Finset.mem_range] at hk
      have := hcond hdvd; rw [hk3] at this; omega
    · rw [if_neg h3k]; ring

-- snip end

problem imc2022_p3 (p : ℕ) (hp : p.Prime) :
    (f p : ZMod p) = answer p := by
  -- Approach: Using f_eq_coeff and key_identity, the coefficient of X^(p-1) in
  -- (1+X+X^2)^(p-1) equals the coefficient of X^(p-1) in (1-X^3)^(p-1)*(1-X) in ZMod p.
  -- Expanding the latter and using choose_pred_prime gives the three-case answer.
  sorry

end Imc2022P3
