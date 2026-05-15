/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2004, Problem 2

Let `P(x) = x² - 1`. How many distinct real solutions does `P^{2004}(x) = 0`
have, where `P^n` denotes the `n`-fold iterate?

Answer: `2005`.
-/

namespace Imc2004P2

open scoped BigOperators

/-- The polynomial function `P(x) = x² - 1`. -/
def P (x : ℝ) : ℝ := x^2 - 1

snip begin

/-- For `a ≥ 0`, `P x = a` iff `x = √(a+1)` or `x = -√(a+1)`. -/
lemma P_eq_iff_nonneg {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    P x = a ↔ x = Real.sqrt (a + 1) ∨ x = -Real.sqrt (a + 1) := by
  unfold P
  have hap : 0 ≤ a + 1 := by linarith
  constructor
  · intro h
    have h2 : x^2 = a + 1 := by linarith
    have habs : |x| = Real.sqrt (a + 1) := by
      rw [← Real.sqrt_sq_eq_abs, h2]
    rcases abs_eq (Real.sqrt_nonneg (a+1)) |>.mp habs with hx | hx
    · left; exact hx
    · right; exact hx
  · rintro (h | h)
    · rw [h, Real.sq_sqrt hap]; ring
    · rw [h, neg_pow, Real.sq_sqrt hap]; ring

/-- `P x = -1` iff `x = 0`. -/
lemma P_eq_neg_one_iff (x : ℝ) : P x = -1 ↔ x = 0 := by
  unfold P
  constructor
  · intro h
    have : x^2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · intro h; rw [h]; ring

/-- `P x ≥ -1` always. -/
lemma P_ge_neg_one (x : ℝ) : -1 ≤ P x := by
  unfold P; nlinarith [sq_nonneg x]

/-- For `n ≥ 1` and any `x`, `P^[n] x ≥ -1`. -/
lemma iterate_ge_neg_one {n : ℕ} (hn : 1 ≤ n) (x : ℝ) : -1 ≤ P^[n] x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ', Function.comp_apply]
  exact P_ge_neg_one _

/-- For `a > 0` and `n ≥ 1`, the set `{x | P^[n] x = a}` has exactly 2 elements. -/
lemma iterate_eq_pos_ncard : ∀ {n : ℕ}, 1 ≤ n →
    ∀ a : ℝ, 0 < a → {x : ℝ | P^[n] x = a}.ncard = 2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    intro a ha
    have hap : 0 < a + 1 := by linarith
    have hsqrt_pos : 0 < Real.sqrt (a + 1) := Real.sqrt_pos.mpr hap
    have hsqrt_gt_1 : 1 < Real.sqrt (a + 1) := by
      have h1 : Real.sqrt 1 < Real.sqrt (a + 1) :=
        Real.sqrt_lt_sqrt (by norm_num) (by linarith)
      rwa [Real.sqrt_one] at h1
    by_cases hk : k = 0
    · subst hk
      have hset : {x : ℝ | P^[0+1] x = a} = {Real.sqrt (a+1), -Real.sqrt (a+1)} := by
        ext x
        simp only [zero_add, Function.iterate_one, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact P_eq_iff_nonneg ha.le x
      rw [hset]
      have hne : Real.sqrt (a + 1) ≠ -Real.sqrt (a + 1) := by
        intro h; linarith
      rw [Set.ncard_pair hne]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have ih' := ih hk1
      have hset : {x : ℝ | P^[k+1] x = a} =
          {x : ℝ | P^[k] x = Real.sqrt (a+1)} ∪ {x : ℝ | P^[k] x = -Real.sqrt (a+1)} := by
        ext x
        simp only [Function.iterate_succ', Function.comp_apply, Set.mem_setOf_eq,
          Set.mem_union]
        exact P_eq_iff_nonneg ha.le _
      have hempty : {x : ℝ | P^[k] x = -Real.sqrt (a+1)} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have hge := iterate_ge_neg_one hk1 x
        rw [h] at hge
        linarith
      rw [hset, hempty, Set.union_empty]
      exact ih' _ hsqrt_pos

/-- The set `{x | P^[n] x = a}` is finite whenever `n ≥ 1` and `a > 0`. -/
lemma iterate_eq_pos_finite {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    {x : ℝ | P^[n] x = a}.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [iterate_eq_pos_ncard hn a ha]; norm_num)

/-- Key recurrence: for `n ≥ 1`,
`{x | P^[n+1] x = 0} = {x | P^[n] x = 1} ⊔ {x | P^[n-1] x = 0}`,
with the second set coming from `P^[n] x = -1 ↔ P^[n-1] x = 0`. -/
lemma iterate_zero_succ_set_eq {n : ℕ} (hn : 1 ≤ n) :
    {x : ℝ | P^[n+1] x = 0} =
    {x : ℝ | P^[n] x = 1} ∪ {x : ℝ | P^[n-1] x = 0} := by
  have hneg1 : {x : ℝ | P^[n] x = -1} = {x : ℝ | P^[n-1] x = 0} := by
    conv_lhs => rw [show n = (n-1) + 1 by omega]
    ext x
    simp only [Function.iterate_succ', Function.comp_apply, Set.mem_setOf_eq]
    exact P_eq_neg_one_iff _
  rw [← hneg1]
  ext x
  simp only [Function.iterate_succ', Function.comp_apply, Set.mem_setOf_eq, Set.mem_union]
  have key : ∀ y : ℝ, P y = 0 ↔ y = 1 ∨ y = -1 := by
    intro y
    unfold P
    constructor
    · intro h
      have h2 : (y - 1) * (y + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> ring
  exact key _

/-- Disjointness of the two sets in the recurrence. -/
lemma iterate_zero_succ_disjoint {n : ℕ} :
    Disjoint {x : ℝ | P^[n] x = 1} {x : ℝ | P^[n] x = -1} := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  norm_num at h2

/-- Main claim: `{x | P^[n] x = 0}` has cardinality `n + 1` and is finite. -/
lemma iterate_eq_zero_ncard :
    ∀ n : ℕ, {x : ℝ | P^[n] x = 0}.Finite ∧ {x : ℝ | P^[n] x = 0}.ncard = n + 1 := by
  -- Two-step induction.
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      have hset : {x : ℝ | P^[0] x = 0} = {0} := by
        ext; simp [Function.iterate_zero]
      refine ⟨?_, ?_⟩
      · rw [hset]; exact Set.finite_singleton 0
      · rw [hset, Set.ncard_singleton]
    | 1 =>
      have hset : {x : ℝ | P^[1] x = 0} = {1, -1} := by
        ext x
        simp only [Function.iterate_one, Set.mem_setOf_eq, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        unfold P
        constructor
        · intro h
          have h2 : x^2 = 1 := by linarith
          have h3 : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
          rcases mul_eq_zero.mp h3 with hx | hx
          · left; linarith
          · right; linarith
        · rintro (h | h) <;> rw [h] <;> ring
      refine ⟨?_, ?_⟩
      · rw [hset]; exact (Set.finite_singleton (-1)).insert 1
      · rw [hset, Set.ncard_pair (by norm_num)]
    | (k + 2) =>
      -- Apply recurrence: {x | P^[k+2] x = 0} = {x | P^[k+1] x = 1} ∪ {x | P^[k] x = 0}
      have hk1 : 1 ≤ k + 1 := by omega
      have hstep := iterate_zero_succ_set_eq hk1
      simp only [show k + 1 - 1 = k from rfl] at hstep
      have hset : {x : ℝ | P^[k+1+1] x = 0} =
          {x : ℝ | P^[k+1] x = 1} ∪ {x : ℝ | P^[k] x = 0} := hstep
      have hcard1 : {x : ℝ | P^[k+1] x = 1}.ncard = 2 :=
        iterate_eq_pos_ncard hk1 1 (by norm_num)
      have hfin1 : {x : ℝ | P^[k+1] x = 1}.Finite :=
        iterate_eq_pos_finite hk1 (by norm_num : (0:ℝ) < 1)
      obtain ⟨hfin2, hcard2⟩ := ih k (by omega)
      have hdisj : Disjoint {x : ℝ | P^[k+1] x = 1} {x : ℝ | P^[k] x = 0} := by
        -- Note: {x | P^[k] x = 0} = {x | P^[k+1] x = -1}.
        have : {x : ℝ | P^[k] x = 0} = {x : ℝ | P^[k+1] x = -1} := by
          ext x
          simp only [Set.mem_setOf_eq]
          rw [Function.iterate_succ', Function.comp_apply, P_eq_neg_one_iff]
        rw [this]
        exact iterate_zero_succ_disjoint
      refine ⟨?_, ?_⟩
      · rw [show k + 2 = k + 1 + 1 from rfl, hset]
        exact hfin1.union hfin2
      · rw [show k + 2 = k + 1 + 1 from rfl, hset]
        rw [Set.ncard_union_eq hdisj hfin1 hfin2]
        rw [hcard1, hcard2]
        omega

snip end

/-- The answer to the problem: 2005. -/
determine answer : ℕ := 2005

problem imc2004_p2 :
    {x : ℝ | P^[2004] x = 0}.ncard = answer := by
  show {x : ℝ | P^[2004] x = 0}.ncard = 2005
  exact (iterate_eq_zero_ncard 2004).2

end Imc2004P2
