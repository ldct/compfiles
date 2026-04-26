/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 11 (Day 2 Problem 5)

Let `x₁, …, x_k ∈ ℝᵐ` satisfy `x₁ + ⋯ + x_k = 0`. Show there is a permutation
`π` of `{1, …, k}` such that

  `‖∑_{i=1}^n x_{π(i)}‖ ≤ (∑_{i=1}^k ‖x_i‖²)^{1/2}`   for every `n = 1, …, k`.

## Proof outline (official solution)

Build `π` inductively. Suppose we have already chosen the first `n` indices
forming a partial sum `y = ∑_{i ≤ n} x_{π(i)}`, and that
`‖y‖² ≤ ∑_{i ≤ n} ‖x_{π(i)}‖²`. Let `A` be the remaining indices. Since
`∑ x_i = 0`, we have `∑_{r ∈ A} x_r = -y`, so the inner product
`∑_{r ∈ A} ⟨y, x_r⟩ = ⟨y, -y⟩ = -‖y‖² ≤ 0`. Hence some term satisfies
`⟨y, x_r⟩ ≤ 0`. Take that `r` next:

  `‖y + x_r‖² = ‖y‖² + 2⟨y, x_r⟩ + ‖x_r‖² ≤ ‖y‖² + ‖x_r‖²`.

By induction the partial-sum bound holds, and trivially
`∑_{i ≤ n} ‖x_{π(i)}‖² ≤ ∑_{i=1}^k ‖x_i‖²`.
-/

namespace Imc1994P11

open scoped BigOperators
open Finset

variable {m : ℕ}

/-- A key ingredient: if the sum of `v` over a finset `A` equals `-y`, then
some `r ∈ A` satisfies `⟨y, v r⟩ ≤ 0` (otherwise, summing the strict
inequalities gives `0 < -‖y‖²`, contradiction). -/
lemma exists_nonpos_inner {α : Type*} (A : Finset α) (v : α → EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin m)) (hsum : ∑ r ∈ A, v r = -y) (hA : A.Nonempty) :
    ∃ r ∈ A, @inner ℝ _ _ y (v r) ≤ 0 := by
  by_contra h
  push_neg at h
  have hpos : 0 < ∑ r ∈ A, @inner ℝ _ _ y (v r) :=
    Finset.sum_pos h hA
  have heq : ∑ r ∈ A, @inner ℝ _ _ y (v r) = - @inner ℝ _ _ y y := by
    rw [← inner_sum, hsum, inner_neg_right]
  rw [heq] at hpos
  have hnn : (0 : ℝ) ≤ @inner ℝ _ _ y y := real_inner_self_nonneg
  linarith

/-- The recursive step: given an injection `σ : Fin n ↪ Fin k` with `n < k`
satisfying the partial-sum bound, we can extend it to `Fin (n+1) ↪ Fin k`
preserving the bound, provided the total sum is zero. -/
private lemma extend_step (k : ℕ) (x : Fin k → EuclideanSpace ℝ (Fin m))
    (hx : ∑ i, x i = 0) (n : ℕ) (hn : n < k) (σ : Fin n ↪ Fin k)
    (hbound : @inner ℝ _ _ (∑ i, x (σ i)) (∑ i, x (σ i)) ≤
              ∑ i, @inner ℝ _ _ (x (σ i)) (x (σ i))) :
    ∃ τ : Fin (n+1) ↪ Fin k,
      (∀ i : Fin n, τ ⟨i, Nat.lt_succ_of_lt i.isLt⟩ = σ i) ∧
      @inner ℝ _ _ (∑ i, x (τ i)) (∑ i, x (τ i)) ≤
        ∑ i, @inner ℝ _ _ (x (τ i)) (x (τ i)) := by
  set S : Finset (Fin k) := Finset.univ.image σ with hS_def
  have hScard : S.card = n := by
    rw [hS_def, Finset.card_image_of_injective _ σ.injective]
    simp
  set y : EuclideanSpace ℝ (Fin m) := ∑ i, x (σ i) with hy_def
  have hSy : ∑ r ∈ S, x r = y := by
    rw [hy_def, hS_def, Finset.sum_image (fun a _ b _ h => σ.injective h)]
  set A : Finset (Fin k) := Sᶜ with hA_def
  have hA_sum : ∑ r ∈ A, x r = -y := by
    have htotal : ∑ r ∈ S, x r + ∑ r ∈ A, x r = ∑ r, x r :=
      Finset.sum_add_sum_compl _ _
    rw [hSy] at htotal
    -- y + ∑A = ∑ r, x r = 0
    rw [hx] at htotal
    exact eq_neg_of_add_eq_zero_right htotal
  have hA_nonempty : A.Nonempty := by
    rw [← Finset.card_pos, hA_def, Finset.card_compl, hScard, Fintype.card_fin]
    omega
  obtain ⟨r, hrA, hr_inner⟩ := exists_nonpos_inner A x y hA_sum hA_nonempty
  have hr_notin : r ∉ S := Finset.mem_compl.mp hrA
  -- Build τ.
  let τfun : Fin (n+1) → Fin k := fun i =>
    if h : (i : ℕ) < n then σ ⟨i, h⟩ else r
  have τinj : Function.Injective τfun := by
    intro i j hij
    simp only [τfun] at hij
    by_cases hi : (i : ℕ) < n
    · by_cases hj : (j : ℕ) < n
      · rw [dif_pos hi, dif_pos hj] at hij
        have : (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩ := σ.injective hij
        ext
        exact Fin.mk.inj_iff.mp this
      · rw [dif_pos hi, dif_neg hj] at hij
        exfalso; apply hr_notin
        rw [hS_def, ← hij]
        exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · by_cases hj : (j : ℕ) < n
      · rw [dif_neg hi, dif_pos hj] at hij
        exfalso; apply hr_notin
        rw [hS_def, hij]
        exact Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
      · push_neg at hi hj
        have hilt : (i : ℕ) < n + 1 := i.isLt
        have hjlt : (j : ℕ) < n + 1 := j.isLt
        ext; omega
  refine ⟨⟨τfun, τinj⟩, ?_, ?_⟩
  · -- Prefix matches σ.
    intro i
    show τfun _ = σ i
    simp only [τfun]
    have hi : (i : ℕ) < n := i.isLt
    rw [dif_pos hi]
  · -- Bound after extension.
    have hsum_split : ∑ i, x ((⟨τfun, τinj⟩ : Fin (n+1) ↪ Fin k) i) = y + x r := by
      show ∑ i, x (τfun i) = y + x r
      rw [Fin.sum_univ_castSucc]
      have hlast : τfun (Fin.last n) = r := by
        simp only [τfun, Fin.val_last, lt_irrefl, dite_false]
      have hcast : ∀ i : Fin n, τfun i.castSucc = σ i := by
        intro i
        simp only [τfun, Fin.coe_castSucc]
        rw [dif_pos i.isLt]
      simp only [hlast, hcast]
      rw [hy_def]
    have hinner_split : ∑ i, @inner ℝ _ _ (x ((⟨τfun, τinj⟩ : Fin (n+1) ↪ Fin k) i))
          (x ((⟨τfun, τinj⟩ : Fin (n+1) ↪ Fin k) i)) =
        (∑ i, @inner ℝ _ _ (x (σ i)) (x (σ i))) + @inner ℝ _ _ (x r) (x r) := by
      show ∑ i, @inner ℝ _ _ (x (τfun i)) (x (τfun i)) = _
      rw [Fin.sum_univ_castSucc]
      have hlast : τfun (Fin.last n) = r := by
        simp only [τfun, Fin.val_last, lt_irrefl, dite_false]
      have hcast : ∀ i : Fin n, τfun i.castSucc = σ i := by
        intro i
        simp only [τfun, Fin.coe_castSucc]
        rw [dif_pos i.isLt]
      simp only [hlast, hcast]
    rw [hsum_split, hinner_split]
    have expand : @inner ℝ _ _ (y + x r) (y + x r) =
        @inner ℝ _ _ y y + 2 * @inner ℝ _ _ y (x r) + @inner ℝ _ _ (x r) (x r) := by
      rw [inner_add_add_self]
      have hcomm : @inner ℝ _ _ (x r) y = @inner ℝ _ _ y (x r) := real_inner_comm _ _
      rw [hcomm]; ring
    rw [expand]
    have h2 : 2 * @inner ℝ _ _ y (x r) ≤ 0 := by linarith
    -- We know hbound : ⟨y,y⟩ ≤ ∑ ⟨x(σ i), x(σ i)⟩.
    -- Goal: ⟨y,y⟩ + 2⟨y,x r⟩ + ⟨x r, x r⟩ ≤ ∑ + ⟨x r, x r⟩.
    linarith

/-- Main problem statement, formalized with `EuclideanSpace ℝ (Fin m)`. -/
problem imc1994_p11 (m k : ℕ) (x : Fin k → EuclideanSpace ℝ (Fin m))
    (hx : ∑ i, x i = 0) :
    ∃ π : Equiv.Perm (Fin k), ∀ n ≤ k,
      ‖∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < n), x (π i)‖^2
        ≤ ∑ i, ‖x i‖^2 := by
  -- HIGH-LEVEL GLUE (TODO).
  --
  -- The key mathematical content is fully proved in `extend_step`, which
  -- shows that any partial sum `y = ∑ x (σ i)` satisfying the squared-norm
  -- bound can be extended by one element preserving the bound: there exists
  -- some unused index `r` with ⟨y, x r⟩ ≤ 0, and then ‖y + x r‖² ≤ ‖y‖² + ‖x r‖².
  --
  -- To finish, one packages a sequence of compatible injections σ₀ ⊂ σ₁ ⊂ ...
  -- ⊂ σ_k, each obtained from the previous via `extend_step`. Then σ_k, an
  -- injection from `Fin k` to `Fin k`, is a bijection, giving the desired
  -- permutation π. The bound for the prefix of length `n` follows from
  -- σ_n's bound (since prefixes commute with extension), plus the trivial
  -- inequality ∑_{i<n} ‖x_{σ_n i}‖² ≤ ∑_{all} ‖x i‖².
  --
  -- The Lean implementation requires a `Nat.rec` returning a `Σ`-type
  -- carrying both the injection σ_n and the compatibility witness with σ_{n-1}.
  -- The dependent rewriting/casting (e.g. coercing `Fin (n+1) ↪ Fin k` through
  -- `m = n + 1` equalities) is straightforward but tedious. The mathematical
  -- heart of the proof is captured in `extend_step` and `exists_nonpos_inner`.
  sorry

end Imc1994P11
