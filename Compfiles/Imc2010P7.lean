/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 7

Let `a 0, a 1, …, a n` be positive reals with `a (k+1) - a k ≥ 1` for all
`k`. Prove that
  `1 + (1/a₀) ∏_{k=1}^n (1 + 1/(a_k - a_0))`
    `≤ ∏_{k=0}^n (1 + 1/a_k)`.
-/

namespace Imc2010P7

open Finset

snip begin

/-- Under the gap hypothesis, `a k ≥ a 0 + k`. -/
lemma a_ge_a_zero_add (a : ℕ → ℝ)
    (hgap : ∀ k, a (k + 1) - a k ≥ 1) :
    ∀ k, a k ≥ a 0 + k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hgap k
    push_cast
    linarith

/-- Positivity of `a k - a 0` for `k ≥ 1`. -/
lemma a_sub_a_zero_pos (a : ℕ → ℝ)
    (hgap : ∀ k, a (k + 1) - a k ≥ 1) (k : ℕ) (hk : 1 ≤ k) :
    0 < a k - a 0 := by
  have h := a_ge_a_zero_add a hgap k
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- The combined inductive claim.

We bundle two properties into one predicate on `n` and prove it by induction:
  * P1(n): `1 + (1/a₀) ∏_{k∈Ioc 0 n} (1 + 1/(a_k - a_0)) ≤ ∏_{k∈range (n+1)} (1 + 1/a_k)`
  * P2(n): For any `m ≥ a n + 1`,
      `(1/a₀) (∏_{k∈Ioc 0 n} (1 + 1/(a_k - a_0))) * (1/(m - a_0))`
        ≤ `(∏_{k∈range (n+1)} (1 + 1/a_k)) * (1/m)`.
-/
lemma combined (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (hgap : ∀ k, a (k + 1) - a k ≥ 1) :
    ∀ n,
      (1 + (1 / a 0) * ∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0)) ≤
        ∏ k ∈ range (n + 1), (1 + 1 / a k)) ∧
      (∀ m : ℝ, m ≥ a n + 1 →
        (1 / a 0) * (∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0))) * (1 / (m - a 0)) ≤
          (∏ k ∈ range (n + 1), (1 + 1 / a k)) * (1 / m)) := by
  have ha0_pos : 0 < a 0 := hpos 0
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- Ioc 0 0 = ∅; product is 1. range 1 = {0}.
      simp
    · intro m hm
      have hma0 : a 0 + 1 ≤ m := hm
      have hm_pos : 0 < m := by linarith
      have hma0_pos : 0 < m - a 0 := by linarith
      -- Goal: 1/a₀ * (∏ ∅ …) * (1/(m-a₀)) ≤ (∏ {0} …) * (1/m)
      simp only [Finset.Ioc_self, Finset.prod_empty, mul_one,
        Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      -- Goal: 1/a₀ * (1/(m-a₀)) ≤ (1 + 1/a₀) * (1/m)
      -- Clear denominators and use a₀ + 1 ≤ m.
      rw [div_mul_div_comm, one_mul]
      have : (1 + 1 / a 0) = (a 0 + 1) / a 0 := by field_simp
      rw [this, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ha0_pos, hma0, mul_nonneg ha0_pos.le (by linarith : (0 : ℝ) ≤ m - a 0 - 1)]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hn1_sub_pos : 0 < a (n + 1) - a 0 :=
      a_sub_a_zero_pos a hgap (n + 1) (by omega)
    have hn1_pos : 0 < a (n + 1) := hpos (n + 1)
    have hQ_pos : ∀ k, 0 < 1 + 1 / a k := by
      intro k
      have : 0 < 1 / a k := by have := hpos k; positivity
      linarith
    have hP_pos : ∀ k, 1 ≤ k → 0 < 1 + 1 / (a k - a 0) := by
      intro k h1
      have : 0 < a k - a 0 := a_sub_a_zero_pos a hgap k h1
      have : 0 < 1 / (a k - a 0) := by positivity
      linarith
    have hm_ge : a (n + 1) ≥ a n + 1 := by have := hgap n; linarith
    have ih2_at := ih2 (a (n + 1)) hm_ge
    have prod_P_succ : ∏ k ∈ Ioc 0 (n + 1), (1 + 1 / (a k - a 0)) =
        (∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0))) * (1 + 1 / (a (n + 1) - a 0)) :=
      Finset.prod_Ioc_succ_top (Nat.zero_le n) _
    have prod_Q_succ : ∏ k ∈ range (n + 2), (1 + 1 / a k) =
        (∏ k ∈ range (n + 1), (1 + 1 / a k)) * (1 + 1 / a (n + 1)) :=
      Finset.prod_range_succ _ (n + 1)
    have hprodQ_pos : 0 < ∏ k ∈ range (n + 1), (1 + 1 / a k) := by
      apply Finset.prod_pos; intros; exact hQ_pos _
    have hprodP_pos : 0 < ∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0)) := by
      apply Finset.prod_pos
      intro k hk
      rw [Finset.mem_Ioc] at hk
      exact hP_pos k hk.1
    set A : ℝ := (1 / a 0) * ∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0)) with hA_def
    set B : ℝ := ∏ k ∈ range (n + 1), (1 + 1 / a k) with hB_def
    have hA_pos : 0 < A := by
      apply mul_pos (one_div_pos.mpr ha0_pos) hprodP_pos
    have hB_pos : 0 < B := hprodQ_pos
    have ih2' : A * (1 / (a (n + 1) - a 0)) ≤ B * (1 / a (n + 1)) := ih2_at
    refine ⟨?_, ?_⟩
    · -- P1(n+1).
      rw [prod_P_succ, prod_Q_succ]
      -- Rewrite LHS as 1 + A * (1 + 1/(a(n+1)-a₀)).
      have lhs_eq : 1 + (1 / a 0) *
          ((∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0))) * (1 + 1 / (a (n + 1) - a 0))) =
          (1 + A) + A * (1 / (a (n + 1) - a 0)) := by
        rw [hA_def]; ring
      rw [lhs_eq]
      have rhs_eq : B * (1 + 1 / a (n + 1)) = B + B * (1 / a (n + 1)) := by ring
      rw [rhs_eq]
      linarith
    · intro m hm
      have hm_pos : 0 < m := by linarith [hpos (n+1)]
      have hm_sub_a0 : 0 < m - a 0 := by
        have := a_ge_a_zero_add a hgap (n + 1)
        linarith
      rw [prod_P_succ, prod_Q_succ]
      -- Rewrite LHS: (1/a₀) * (prod_small * new_P) * (1/(m-a₀)) =
      --   A * (1 + 1/(a(n+1)-a₀)) * (1/(m-a₀)).
      have lhs_eq : (1 / a 0) *
          ((∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0))) * (1 + 1 / (a (n + 1) - a 0))) *
          (1 / (m - a 0)) =
          A * (1 + 1 / (a (n + 1) - a 0)) * (1 / (m - a 0)) := by
        rw [hA_def]; ring
      rw [lhs_eq]
      -- RHS is B * (1 + 1/a(n+1)) * (1/m).
      -- Convert LHS and RHS into factored forms.
      have hn1_sub_ne : a (n + 1) - a 0 ≠ 0 := hn1_sub_pos.ne'
      have hn1_ne : a (n + 1) ≠ 0 := hn1_pos.ne'
      have hm_ne : m ≠ 0 := hm_pos.ne'
      have hmsub_ne : m - a 0 ≠ 0 := hm_sub_a0.ne'
      have eq_lhs : A * (1 + 1 / (a (n + 1) - a 0)) * (1 / (m - a 0)) =
          (A * (1 / (a (n + 1) - a 0))) * ((a (n + 1) - a 0 + 1) / (m - a 0)) := by
        field_simp
      have eq_rhs : B * (1 + 1 / a (n + 1)) * (1 / m) =
          (B * (1 / a (n + 1))) * ((a (n + 1) + 1) / m) := by
        field_simp
      rw [eq_lhs, eq_rhs]
      have hfactor2_pos_lhs : 0 < (a (n + 1) - a 0 + 1) / (m - a 0) :=
        div_pos (by linarith) hm_sub_a0
      have hfactor_rhs_pos : 0 < B * (1 / a (n + 1)) :=
        mul_pos hB_pos (by positivity)
      have hfactor2 : (a (n + 1) - a 0 + 1) / (m - a 0) ≤ (a (n + 1) + 1) / m := by
        rw [div_le_div_iff₀ hm_sub_a0 hm_pos]
        nlinarith [ha0_pos]
      calc (A * (1 / (a (n + 1) - a 0))) * ((a (n + 1) - a 0 + 1) / (m - a 0))
          ≤ (B * (1 / a (n + 1))) * ((a (n + 1) - a 0 + 1) / (m - a 0)) :=
            mul_le_mul_of_nonneg_right ih2' hfactor2_pos_lhs.le
        _ ≤ (B * (1 / a (n + 1))) * ((a (n + 1) + 1) / m) :=
            mul_le_mul_of_nonneg_left hfactor2 hfactor_rhs_pos.le

snip end

problem imc2010_p7 (n : ℕ) (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (hgap : ∀ k, a (k + 1) - a k ≥ 1) :
    1 + (1 / a 0) * ∏ k ∈ Ioc 0 n, (1 + 1 / (a k - a 0)) ≤
      ∏ k ∈ range (n + 1), (1 + 1 / a k) :=
  (combined a hpos hgap n).1

end Imc2010P7
