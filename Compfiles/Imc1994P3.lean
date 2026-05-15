/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 1994, Problem 3

Given a set `S` of `2n - 1` distinct irrational numbers, prove there exist
`n` distinct elements `x₁, …, xₙ ∈ S` such that for all nonnegative rationals
`a₁, …, aₙ` with `a₁ + … + aₙ > 0`, the sum `a₁ x₁ + … + aₙ xₙ` is irrational.

## Proof outline

Induct on `n`. For `n = 1` the singleton `{x}` works since `x` is irrational
and any positive rational times `x` is irrational.

For the inductive step, suppose the claim holds for `n - 1`. Given `S` with
`|S| = 2n - 1`, pick `T ⊆ S` of size `n - 1` with the property (using the
inductive hypothesis on any `(2n - 3)`-subset of `S`). The remaining `n`
elements of `S \ T` are denoted `y₀, …, y_{n-1}`.

If the conclusion fails, then for each `k` the singleton `T ∪ {y_k}` does not
have the property: there are nonneg rationals `b_{i,k}, c_k` not all zero with
`∑ᵢ b_{i,k} xᵢ + c_k y_k = r_k ∈ ℚ`. We have `c_k ≠ 0` (else this contradicts
`T`'s property), so WLOG `c_k = 1` and `∑ᵢ b_{i,k} > 0` (since `y_k` is
irrational).

Also, by the inductive hypothesis applied "in reverse" to the `n` elements
`y₀, …, y_{n-1}` (using that no `n`-subset of `S` has the property by
assumption — but wait, `T ∪ {y_k}` only has `n` elements so this is the same
statement; the actual argument: the `n`-element set `{y₀, …, y_{n-1}}` itself
does not have the property), there are `d_k ∈ ℚ⁺` not all zero with
`∑_k d_k y_k = R ∈ ℚ`.

Substituting `y_k = -∑ᵢ b_{i,k} xᵢ + r_k` gives
`∑ᵢ (∑_k d_k b_{i,k}) xᵢ ∈ ℚ`,
where the coefficients `∑_k d_k b_{i,k}` are nonnegative and not all zero
(this requires care). This contradicts `T`'s property.

This formalization captures the full statement; the proof is left as `sorry`
with a structured outline because the induction and the careful tracking of
coefficient positivity is involved.
-/

namespace Imc1994P3

open scoped BigOperators

/-- The "rational-independence" property of a finite set `T` of irrationals:
every positive nonneg-rational linear combination of elements of `T` is
irrational. -/
def RatIndep (T : Finset ℝ) : Prop :=
  ∀ a : ℝ → ℚ, (∀ x ∈ T, 0 ≤ a x) → (0 < ∑ x ∈ T, (a x : ℝ)) →
    Irrational (∑ x ∈ T, (a x : ℝ) * x)

/-- Base case `n = 1`: any singleton of an irrational has the property. -/
lemma ratIndep_singleton {x : ℝ} (hx : Irrational x) : RatIndep {x} := by
  intro a _ hpos
  rw [Finset.sum_singleton] at hpos ⊢
  -- hpos : 0 < (a x : ℝ);  goal : Irrational ((a x : ℝ) * x)
  have hax_pos : (0 : ℝ) < (a x : ℝ) := hpos
  have hax_ne : (a x : ℝ) ≠ 0 := ne_of_gt hax_pos
  have hax_q_ne : a x ≠ 0 := by
    intro h; rw [h] at hax_ne; simp at hax_ne
  -- Irrational of (q : ℝ) * x for nonzero rational q and irrational x
  exact hx.ratCast_mul hax_q_ne

problem imc1994_p3 (n : ℕ) (hn : 1 ≤ n) (S : Finset ℝ)
    (hS_card : S.card = 2 * n - 1)
    (hS_irr : ∀ x ∈ S, Irrational x) :
    ∃ T : Finset ℝ, T ⊆ S ∧ T.card = n ∧ RatIndep T := by
  -- Base case n = 1 is easy; we handle it explicitly. The inductive step is
  -- left as `sorry` with a detailed outline below.
  rcases eq_or_lt_of_le hn with h1 | h1
  · -- n = 1: take any singleton
    rw [← h1] at hS_card
    -- hS_card : S.card = 2 * 1 - 1 = 1
    norm_num at hS_card
    -- S has exactly one element x; T := S works.
    obtain ⟨x, hxS⟩ : ∃ x, x ∈ S := by
      have : S.Nonempty := Finset.card_pos.mp (by omega)
      exact this
    refine ⟨{x}, ?_, ?_, ratIndep_singleton (hS_irr x hxS)⟩
    · intro y hy; rw [Finset.mem_singleton] at hy; rw [hy]; exact hxS
    · simp [← h1]
  -- TODO: Full formalization of the inductive proof. Outline:
  --
  -- Induction on n. Base case n = 1: take T = {x} for any x ∈ S.
  --
  -- Inductive step: by IH applied to any (2n-3)-subset of S, obtain
  -- T₀ ⊆ S with |T₀| = n-1 and RatIndep T₀. Let y₀,...,y_{n-1} enumerate
  -- S \ T₀ (n elements).
  --
  -- Suppose for contradiction no n-subset of S satisfies RatIndep.
  -- In particular for each k ∈ {0,...,n-1}, T₀ ∪ {y_k} fails RatIndep, so
  -- there are b_{i,k} (i indexing T₀), c_k ∈ ℚ⁺, not all zero, with
  --   ∑_i b_{i,k} (xᵢ:ℝ) + c_k y_k = r_k ∈ ℚ.
  -- If c_k = 0 this contradicts RatIndep T₀, so c_k > 0; rescale c_k = 1
  -- and note ∑_i b_{i,k} > 0 (since y_k is irrational).
  --
  -- Also, the n-element set {y₀,...,y_{n-1}} fails RatIndep (by assumption),
  -- so there are d_k ∈ ℚ⁺, not all zero, with ∑_k d_k y_k = R ∈ ℚ.
  -- (All d_k ≥ 0; sum is positive.)
  --
  -- Substituting y_k = r_k - ∑_i b_{i,k} (xᵢ:ℝ):
  --   R = ∑_k d_k y_k = ∑_k d_k (r_k - ∑_i b_{i,k} xᵢ)
  --     = (∑_k d_k r_k) - ∑_i (∑_k d_k b_{i,k}) xᵢ.
  -- Hence ∑_i (∑_k d_k b_{i,k}) xᵢ = (∑_k d_k r_k) - R ∈ ℚ.
  --
  -- The coefficients e_i := ∑_k d_k b_{i,k} are nonneg. They are not all
  -- zero: pick k with d_k > 0; for that k, ∑_i b_{i,k} > 0 so some
  -- b_{i₀,k} > 0, giving e_{i₀} ≥ d_k * b_{i₀,k} > 0.
  --
  -- Hence ∑_i e_i xᵢ is rational with nonneg-rational positive-sum
  -- coefficients, contradicting RatIndep T₀.
  sorry

end Imc1994P3
