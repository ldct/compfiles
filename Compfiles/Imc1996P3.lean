/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 3 (Day 1)

Let `V` be a (finite-dimensional) vector space over `ℝ` of dimension `n`.
A linear operator `A : V →ₗ[ℝ] V` is called an *involution* if `A * A = 1`.

(i) Prove that for every involution `A`, the space `V` is the direct sum of the
    `(+1)`- and `(-1)`-eigenspaces of `A` (so `V` admits a basis of
    eigenvectors of `A`).

(ii) Find the maximum number of distinct pairwise commuting involutions on `V`.
     The answer is `2^n`.

## Proof outline (official solution)

(i) Every `v ∈ V` decomposes as
      `v = (v + A v)/2 + (v - A v)/2`,
    where the first summand satisfies `A((v + A v)/2) = (A v + v)/2` (using
    `A^2 = id`), so it lies in `eigenspace A 1`, while the second satisfies
    `A((v - A v)/2) = (A v - v)/2 = -(v - A v)/2`, so it lies in
    `eigenspace A (-1)`. The two eigenspaces have trivial intersection
    (an eigenvector for `1` and `-1` simultaneously is zero). Hence
    `V = eigenspace A 1 ⊕ eigenspace A (-1)`, which gives a basis of
    eigenvectors.

(ii) Any commuting family of diagonalizable operators is simultaneously
     diagonalizable: induct on `dim V`. Pick `A_1` from the family;
     decompose `V = ⨁ V_λ` into `A_1`-eigenspaces. Since each `A_i`
     commutes with `A_1`, each `V_λ` is `A_i`-invariant, and the restrictions
     of `A_2, …` are again involutions, so we recurse on each `V_λ`. In a
     common eigenbasis, each involution is a diagonal matrix with `±1`
     entries, giving at most `2^n` distinct commuting involutions. The bound
     is attained by taking all `2^n` such diagonal matrices.

## Status

Part (i) is fully proved.

Part (ii) requires simultaneous diagonalization of a commuting family
together with a counting argument. It is stated with the closed-form
answer `2^n`, but the proof is left as `sorry` with a detailed TODO.
-/

namespace Imc1996P3

open Module.End

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An involution: a linear operator `A` with `A * A = 1`. -/
def IsInvolution (A : V →ₗ[ℝ] V) : Prop := A * A = 1

snip begin

/-- For an involution `A`, every vector decomposes as a sum of vectors in the
`(+1)`- and `(-1)`-eigenspaces. -/
lemma exists_eigen_decomp (A : V →ₗ[ℝ] V) (hA : IsInvolution A) (v : V) :
    ∃ u w : V, A u = u ∧ A w = -w ∧ v = u + w := by
  -- u = (v + A v) / 2, w = (v - A v) / 2.
  refine ⟨(1/2 : ℝ) • (v + A v), (1/2 : ℝ) • (v - A v), ?_, ?_, ?_⟩
  · -- A ((1/2) • (v + A v)) = (1/2) • (A v + A^2 v) = (1/2) • (A v + v)
    have hAA : (A * A) v = v := by rw [hA]; rfl
    rw [LinearMap.map_smul, map_add]
    have : A (A v) = v := by simpa [Module.End.mul_apply] using hAA
    rw [this]
    rw [show v + A v = A v + v from by abel]
  · have hAA : (A * A) v = v := by rw [hA]; rfl
    rw [LinearMap.map_smul, map_sub]
    have : A (A v) = v := by simpa [Module.End.mul_apply] using hAA
    rw [this]
    rw [show A v - v = -(v - A v) from by abel]
    rw [smul_neg]
  · rw [← smul_add]
    rw [show v + A v + (v - A v) = (2 : ℝ) • v from by
        rw [two_smul]; abel]
    rw [smul_smul]
    norm_num

/-- The `+1` and `-1` eigenspaces span `V`. -/
lemma eigenspaces_sup_eq_top (A : V →ₗ[ℝ] V) (hA : IsInvolution A) :
    eigenspace A 1 ⊔ eigenspace A (-1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, w, hu, hw, hvuw⟩ := exists_eigen_decomp A hA v
  rw [hvuw]
  apply Submodule.add_mem_sup
  · rw [mem_eigenspace_iff, hu, one_smul]
  · rw [mem_eigenspace_iff, hw]
    rw [show ((-1 : ℝ)) • w = -w from by rw [neg_one_smul]]

/-- The `+1` and `-1` eigenspaces have trivial intersection. -/
lemma eigenspaces_inf_eq_bot (A : V →ₗ[ℝ] V) :
    eigenspace A 1 ⊓ eigenspace A (-1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨h1, h2⟩ := hv
  rw [mem_eigenspace_iff] at h1 h2
  rw [one_smul] at h1
  rw [show ((-1 : ℝ)) • v = -v from by rw [neg_one_smul]] at h2
  rw [Submodule.mem_bot]
  -- v = -v from h1 = A v = -v (h2), so 2 v = 0, so v = 0.
  have hvneg : v = -v := h1.symm.trans h2
  have h2v : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hvneg]
    exact add_neg_cancel v
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h2v).resolve_left h2ne

snip end

/-- Part (i): every involution on `V` admits a direct-sum decomposition of
`V` into its `(+1)`- and `(-1)`-eigenspaces. (This is equivalent to having a
basis of eigenvectors.) -/
problem imc1996_p3_part1 (A : V →ₗ[ℝ] V) (hA : IsInvolution A) :
    IsCompl (eigenspace A 1) (eigenspace A (-1)) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    exact eigenspaces_inf_eq_bot A
  · rw [codisjoint_iff]
    exact eigenspaces_sup_eq_top A hA

/-- The answer to part (ii): the maximum number of distinct pairwise
commuting involutions on a vector space of dimension `n` is `2^n`. -/
determine maxCommutingInvolutions (n : ℕ) : ℕ := 2 ^ n

/-- Part (ii): on an `n`-dimensional real vector space, the maximum size of a
set of pairwise commuting involutions is `2^n`.

We state existence and the upper bound. -/
problem imc1996_p3_part2 (n : ℕ) (V : Type) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hn : Module.finrank ℝ V = n) :
    -- Upper bound: any set `S` of pairwise commuting involutions on `V` has
    -- cardinality at most `2^n`.
    (∀ S : Finset (V →ₗ[ℝ] V),
      (∀ A ∈ S, IsInvolution A) →
      (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) →
      S.card ≤ maxCommutingInvolutions n) ∧
    -- Achievability: there exists such a set of size `2^n`.
    (∃ S : Finset (V →ₗ[ℝ] V),
      (∀ A ∈ S, IsInvolution A) ∧
      (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) ∧
      S.card = maxCommutingInvolutions n) := by
  -- TODO: full proof.
  --
  -- Upper bound. Let `S` be a finite set of pairwise commuting involutions.
  -- By induction on `n = dim V`:
  --   n = 0: V = 0, only the zero map is an involution, |S| ≤ 1 = 2^0.
  --   n ≥ 1: if S = ∅ or S = {id} or S = {-id}, trivial. Otherwise, pick
  --     A ∈ S with A ≠ ±id; then `eigenspace A 1` and `eigenspace A (-1)`
  --     are both nonzero proper subspaces, and `V = V₊ ⊕ V₋` by Part (i).
  --     Each `B ∈ S` commutes with A, so leaves both `V₊` and `V₋`
  --     invariant. Define `f : S → S₊ × S₋` by sending `B` to its restrictions
  --     `(B|_{V₊}, B|_{V₋})`; both restrictions are commuting involutions on
  --     subspaces of dimension `< n`. The map `f` is injective: if `B|_{V₊}
  --     = B'|_{V₊}` and `B|_{V₋} = B'|_{V₋}`, then `B = B'` on all of `V` by
  --     the direct sum decomposition. By the inductive hypothesis,
  --     `|S₊| ≤ 2^{dim V₊}`, `|S₋| ≤ 2^{dim V₋}`, so
  --     `|S| ≤ 2^{dim V₊} · 2^{dim V₋} = 2^{dim V₊ + dim V₋} = 2^n`.
  --
  -- Achievability. Choose a basis `e₁, …, eₙ` of V. For each subset
  -- `T ⊆ {1, …, n}`, define `A_T` as the involution with `A_T eᵢ = eᵢ` for
  -- `i ∈ T` and `A_T eᵢ = -eᵢ` for `i ∉ T`. These are pairwise commuting
  -- (diagonal matrices commute), distinct, and there are `2^n` of them.
  sorry

end Imc1996P3
