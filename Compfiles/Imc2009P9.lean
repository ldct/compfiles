/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 9
(Day 2, Problem 4)

Let `p` be a prime number. Let `W` be the smallest set of polynomials over
`F_p = ZMod p` such that
- `x + 1 ∈ W` and `x^(p-2) + x^(p-3) + ⋯ + x^2 + 2x + 1 ∈ W`;
- if `h_1, h_2 ∈ W`, then the remainder of `h_1(h_2(x))` modulo `x^p - x` is in
  `W`.

Find `|W|`.

Answer: `|W| = p!`.

The mathematical idea: identify polynomials of degree `< p` with functions
`F_p → F_p`. The first generator `f_1 = x + 1` represents the cyclic
permutation `i ↦ i + 1`, and the second generator `f_2` represents the
transposition `0 ↔ 1` (using Fermat's little theorem). These generate the
symmetric group `S_p` (a `p`-cycle and an adjacent transposition generate
`S_p` for `p` prime). The closure of these generators under composition
modulo `x^p - x` realizes precisely the polynomial functions corresponding
to permutations of `F_p`, of which there are `p!`.
-/

namespace Imc2009P9

open Polynomial

/-- The second generator polynomial:
`x^(p-2) + x^(p-3) + ⋯ + x^2 + 2x + 1 = (∑_{k=0}^{p-2} X^k) + X`.

We rewrite the original expression by noting that the original
`x^(p-2) + x^(p-3) + ⋯ + x^2 + 2x + 1` equals
`(x^(p-2) + ⋯ + x^2 + x + 1) + x = (∑_{k=0}^{p-2} x^k) + x`.

As a function on `F_p`, this is the swap `0 ↔ 1`: use Fermat's little
theorem `x^(p-1) = 1` for `x ≠ 0`, so `(x^(p-1) - 1) / (x - 1) = 0` for
`x ≠ 1` and equals `p - 1` for `x = 1`. -/
noncomputable def gen2' (p : ℕ) : (ZMod p)[X] :=
  (∑ k ∈ Finset.range (p - 1), (X : (ZMod p)[X]) ^ k) + X

/-- The polynomial `x^p - x`, used as the modulus in the closure rule. -/
noncomputable def modPoly (p : ℕ) : (ZMod p)[X] := X ^ p - X

/-- The set `W` defined inductively as the smallest set of polynomials in
`F_p[X]` containing the two generators and closed under composition modulo
`x^p - x`. -/
inductive W (p : ℕ) : (ZMod p)[X] → Prop
  | gen1 : W p (X + 1)
  | gen2 : W p (gen2' p)
  | comp (h₁ h₂ : (ZMod p)[X]) : W p h₁ → W p h₂ → W p ((h₁.comp h₂) %ₘ (modPoly p))

/-- The answer: `|W| = p!`. -/
determine answer (p : ℕ) : ℕ := p.factorial

snip begin

/-- Polynomials representing bijections `F_p → F_p`, viewed as elements of
`F_p[X]` of degree less than `p`. -/
noncomputable def permPolys (p : ℕ) : Set ((ZMod p)[X]) :=
  {f | f.natDegree < p ∧ Function.Bijective (fun x : ZMod p => f.eval x)}

/-- The map sending a polynomial to its induced function on `F_p`. -/
noncomputable def evalMap (p : ℕ) (f : (ZMod p)[X]) : ZMod p → ZMod p :=
  fun x => f.eval x

/-- The polynomial `X^p - X` is monic when `p` is prime (so `2 ≤ p`). -/
lemma modPoly_monic (p : ℕ) [hp : Fact p.Prime] : (modPoly p).Monic := by
  unfold modPoly
  have hp2 : 2 ≤ p := hp.out.two_le
  apply Polynomial.monic_X_pow_sub
  -- degree X < p
  rw [degree_X]
  exact_mod_cast hp2

/-- Reduction modulo `X^p - X` of a polynomial `f` agrees with `f` on `F_p`. -/
lemma eval_modByMonic_eq (p : ℕ) [hp : Fact p.Prime] (f : (ZMod p)[X]) (x : ZMod p) :
    (f %ₘ modPoly p).eval x = f.eval x := by
  have hkey : f %ₘ modPoly p + modPoly p * (f /ₘ modPoly p) = f :=
    modByMonic_add_div f (modPoly p)
  have hmod_eval : (modPoly p).eval x = 0 := by
    unfold modPoly
    simp [ZMod.pow_card]
  have := congrArg (Polynomial.eval x) hkey
  simp only [eval_add, eval_mul, hmod_eval, zero_mul, add_zero] at this
  exact this

/-- The natDegree of `modPoly p = X^p - X` is `p` for `p` prime. -/
lemma modPoly_natDegree (p : ℕ) [hp : Fact p.Prime] : (modPoly p).natDegree = p := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hmonic : (modPoly p).Monic := modPoly_monic p
  -- modPoly p has natDegree ≤ p from the bound, and = p from monic + leading coeff.
  -- Use: for monic poly, natDegree equals the degree of the leading X^p term.
  have hX_pow : (X : (ZMod p)[X]) ^ p = X ^ p := rfl
  unfold modPoly
  -- natDegree (X^p - X) = max (natDegree X^p) (natDegree X) = p when p > 1.
  apply le_antisymm
  · -- natDegree (X^p - X) ≤ p.
    refine (natDegree_sub_le _ _).trans ?_
    rw [natDegree_X, natDegree_X_pow]
    omega
  · -- p ≤ natDegree (X^p - X). Coefficient at p is 1.
    apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_sub, coeff_X_pow, if_pos rfl, coeff_X]
    have : ¬ (1 : ℕ) = p := by omega
    rw [if_neg this]
    simp

/-- The natDegree of `gen2' p` is at most `p - 2` for `p ≥ 2`, hence `< p`. -/
lemma gen2'_natDegree_lt (p : ℕ) [hp : Fact p.Prime] : (gen2' p).natDegree < p := by
  have hp2 : 2 ≤ p := hp.out.two_le
  unfold gen2'
  -- natDegree of sum ≤ p-2; natDegree X = 1; so total ≤ max (p-2) 1 < p.
  refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
  rw [natDegree_X]
  refine (max_lt ?_ ?_)
  · -- natDegree (∑ k ∈ range (p-1), X^k) ≤ p-2 < p
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
    -- The bound is the max over the finset of natDegree (X^k) = k for k < p-1.
    have hbound : ∀ k ∈ Finset.range (p - 1), (X ^ k : (ZMod p)[X]).natDegree ≤ p - 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [natDegree_X_pow]
      omega
    -- Use Finset.fold_max_le.
    refine lt_of_le_of_lt ?_ (show p - 2 < p from by omega)
    exact Finset.sup_le hbound
  · omega

/-- Every element of `W p` (for `p` prime) has degree less than `p`. -/
lemma W_natDegree_lt (p : ℕ) [hp : Fact p.Prime] {f : (ZMod p)[X]} (hf : W p f) :
    f.natDegree < p := by
  have hp2 : 2 ≤ p := hp.out.two_le
  induction hf with
  | gen1 =>
    -- natDegree (X + 1) = 1 < p.
    have h1 : (X + 1 : (ZMod p)[X]).natDegree = 1 := by
      have : (X + 1 : (ZMod p)[X]) = X + C 1 := by simp
      rw [this, natDegree_X_add_C]
    rw [h1]; omega
  | gen2 =>
    exact gen2'_natDegree_lt p
  | comp h₁ h₂ _ _ _ _ =>
    -- (h₁.comp h₂) %ₘ (modPoly p) has natDegree < p (= natDegree of modPoly p).
    have hmonic : (modPoly p).Monic := modPoly_monic p
    have hne : modPoly p ≠ 1 := by
      intro h
      have : (modPoly p).natDegree = 0 := by rw [h, natDegree_one]
      rw [modPoly_natDegree] at this; omega
    have hbound := natDegree_modByMonic_lt (h₁.comp h₂) hmonic hne
    rw [modPoly_natDegree] at hbound
    exact hbound

/-- Sum of geometric series: `(x - 1) * ∑_{k<n} x^k = x^n - 1` in any
commutative ring. -/
lemma geom_sum_mul_aux {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (x - 1) * (∑ k ∈ Finset.range n, x ^ k) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- For `x : ZMod p` with `x ≠ 0` and `x ≠ 1`, `∑_{k<p-1} x^k = 0`. -/
lemma geom_sum_pred_eq_zero (p : ℕ) [hp : Fact p.Prime] {x : ZMod p}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∑ k ∈ Finset.range (p - 1), x ^ k = 0 := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  -- (x - 1) * (∑ k < p-1, x^k) = x^(p-1) - 1 = 0 by Fermat (since x ≠ 0).
  have h1 : (x - 1) * (∑ k ∈ Finset.range (p - 1), x ^ k) = x ^ (p - 1) - 1 :=
    geom_sum_mul_aux x (p - 1)
  -- x^(p-1) = 1 for x ≠ 0 in ZMod p (Fermat's little).
  have hfermat : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  rw [hfermat, sub_self] at h1
  -- (x-1) * S = 0 with x-1 ≠ 0 implies S = 0.
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h hxsub
  · exact h

/-- Geometric sum at 0: `∑_{k<p-1} 0^k = 1` for `p ≥ 2`. -/
lemma geom_sum_at_zero (p : ℕ) [hp : Fact p.Prime] :
    ∑ k ∈ Finset.range (p - 1), (0 : ZMod p) ^ k = 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : 0 < p - 1 := by omega
  -- Split: range (p-1) = range ((p-2)+1), starting from k=0.
  rw [show p - 1 = (p - 2) + 1 from by omega]
  rw [Finset.sum_range_succ']
  -- Now goal: ∑ k ∈ range (p-2), 0^(k+1) + 0^0 = 1.
  rw [pow_zero]
  have hzero : ∑ k ∈ Finset.range (p - 2), (0 : ZMod p) ^ (k + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [pow_succ, mul_zero]
  rw [hzero, zero_add]

/-- Geometric sum at 1: `∑_{k<p-1} 1^k = p - 1 = -1` in `ZMod p`. -/
lemma geom_sum_at_one (p : ℕ) [hp : Fact p.Prime] :
    ∑ k ∈ Finset.range (p - 1), (1 : ZMod p) ^ k = -1 := by
  simp only [one_pow, Finset.sum_const, Finset.card_range]
  -- (p - 1 : ℕ) • (1 : ZMod p) = ((p - 1 : ℕ) : ZMod p) = -1.
  rw [nsmul_eq_mul, mul_one]
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hcast : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
    have : ((p - 1 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) - ((1 : ℕ) : ZMod p) := by
      push_cast
      rw [Nat.cast_sub hp1]
      push_cast; ring
    simpa using this
  rw [hcast, ZMod.natCast_self, zero_sub]

/-- Evaluation of `gen2' p` at any `x : ZMod p`: it's the swap 0 ↔ 1. -/
lemma gen2'_eval (p : ℕ) [hp : Fact p.Prime] (x : ZMod p) :
    (gen2' p).eval x = if x = 0 then 1 else if x = 1 then 0 else x := by
  unfold gen2'
  simp only [eval_add, eval_finset_sum, eval_pow, eval_X]
  by_cases hx0 : x = 0
  · subst hx0
    rw [if_pos rfl]
    rw [geom_sum_at_zero]
    ring
  · rw [if_neg hx0]
    by_cases hx1 : x = 1
    · subst hx1
      rw [if_pos rfl]
      rw [geom_sum_at_one]
      ring
    · rw [if_neg hx1]
      rw [geom_sum_pred_eq_zero p hx0 hx1]
      ring

/-- The function induced by `gen2' p` on `ZMod p`. It is the swap of 0 and 1. -/
lemma gen2'_bijective (p : ℕ) [hp : Fact p.Prime] :
    Function.Bijective (fun x : ZMod p => (gen2' p).eval x) := by
  -- The function is its own inverse (involutive), hence bijective.
  have hinvol : Function.Involutive (fun x : ZMod p => (gen2' p).eval x) := by
    intro x
    simp only [gen2'_eval]
    by_cases hx0 : x = 0
    · subst hx0; simp
    · by_cases hx1 : x = 1
      · subst hx1; simp
      · rw [if_neg hx0, if_neg hx1]
        rw [if_neg hx0, if_neg hx1]
  exact hinvol.bijective

/-- Evaluation of polynomial composition: `(h₁.comp h₂).eval x = h₁.eval (h₂.eval x)`. -/
lemma eval_comp_apply (p : ℕ) (h₁ h₂ : (ZMod p)[X]) (x : ZMod p) :
    (h₁.comp h₂).eval x = h₁.eval (h₂.eval x) := by
  exact eval_comp

/-- Every element of `W p` induces a bijection on `F_p`. -/
lemma W_bijective (p : ℕ) [hp : Fact p.Prime] {f : (ZMod p)[X]} (hf : W p f) :
    Function.Bijective (fun x : ZMod p => f.eval x) := by
  induction hf with
  | gen1 =>
    -- x ↦ x + 1 has inverse x ↦ x - 1.
    have : (fun x : ZMod p => (X + 1 : (ZMod p)[X]).eval x) = fun x => x + 1 := by
      funext x; simp
    rw [this]
    exact ⟨fun a b h => by simpa using h, fun y => ⟨y - 1, by ring⟩⟩
  | gen2 => exact gen2'_bijective p
  | comp h₁ h₂ _ _ ih₁ ih₂ =>
    -- f = (h₁.comp h₂) %ₘ (modPoly p). Eval = eval h₁.comp h₂ = (h₁.eval) ∘ (h₂.eval).
    have hcoincide : (fun x : ZMod p => ((h₁.comp h₂) %ₘ modPoly p).eval x) =
        (fun x : ZMod p => h₁.eval x) ∘ (fun x : ZMod p => h₂.eval x) := by
      funext x
      rw [eval_modByMonic_eq, eval_comp]
      rfl
    rw [hcoincide]
    exact ih₁.comp ih₂

snip end

/-- Statement of the IMC 2009 Problem 9 (Day 2, Problem 4): the cardinality of `W p`
equals `p!`.

Mathematical proof outline:
1. Every `f ∈ W` has `natDegree < p` (proved as `W_natDegree_lt`).
2. Every `f ∈ W` induces a bijection `ZMod p → ZMod p` (proved as `W_bijective`).
3. Two polynomials of `natDegree < p` over `ZMod p` agreeing on all of
   `ZMod p` are equal (since `ZMod p` has exactly `p` elements and two such
   polynomials differ by a polynomial of degree `< p` with `p` roots, hence
   the zero polynomial).
4. So the evaluation map gives an injection `{f // W p f} ↪ Equiv.Perm (ZMod p)`.
5. Composition of polynomials in `W` corresponds to composition of permutations,
   so the image of `{f // W p f}` is the submonoid of `Equiv.Perm (ZMod p)`
   generated by the images of `gen1` and `gen2'`.
6. The image of `gen1` is the cycle `σ : x ↦ x + 1` (a `p`-cycle since `p`
   is prime); the image of `gen2'` is the swap `τ = swap 0 1`.
7. By `closure_prime_cycle_swap`, the subgroup generated by `{σ, τ}` is
   the entire symmetric group on `ZMod p`. In a finite group, the
   monoid-closure equals the group-closure, so the submonoid generated by
   `{σ, τ}` is all of `Equiv.Perm (ZMod p)`.
8. Hence the evaluation map is also surjective, so we get a bijection
   `{f // W p f} ≃ Equiv.Perm (ZMod p)`.
9. Therefore
   `Nat.card {f // W p f} = Nat.card (Equiv.Perm (ZMod p)) = (Fintype.card (ZMod p))! = p!`. -/
problem imc2009_p9 (p : ℕ) (hp : p.Prime) (hp_odd : Odd p) :
    Nat.card {f : (ZMod p)[X] // W p f} = answer p := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- TODO: complete the formalization following the outline above. The chief
  -- difficulty is showing the image of `W` (as a submonoid of `Equiv.Perm`)
  -- equals all of `Equiv.Perm (ZMod p)`, which uses
  -- `closure_prime_cycle_swap` (giving subgroup-closure = ⊤) together with
  -- the fact that in a finite group the submonoid generated by a set
  -- coincides with the subgroup generated.
  sorry

end Imc2009P9
