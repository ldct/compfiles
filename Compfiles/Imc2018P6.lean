/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2018, Problem 6
(IMC 2018, Day 2, Problem 6)

Let `k` be a positive integer. Find the smallest `n` for which there exist
nonzero vectors `v₁, …, v_k ∈ ℝⁿ` such that `vᵢ ⟂ vⱼ` for all `|i - j| > 1`.

The answer is `n = ⌈k / 2⌉`.

## Proof outline

* **Construction**: Use the orthonormal basis `e₁, …, e_n` of `ℝⁿ` (with
  `n = ⌈k/2⌉`) and set `v_{2i-1} = v_{2i} = eᵢ`. Two indices that are not
  adjacent must come from different basis pairs, so they are orthogonal.

* **Lower bound**: Suppose vectors `v₁, …, v_k` in `ℝⁿ` satisfy the
  condition. The sub-family at odd indices `1, 3, …, 2⌈k/2⌉ - 1` gives
  `⌈k/2⌉` pairwise orthogonal nonzero vectors. They are linearly
  independent, so `n ≥ ⌈k/2⌉`.
-/

namespace Imc2018P6

open scoped InnerProductSpace

/-- The condition: there exist `k` nonzero vectors in `ℝⁿ` with non-adjacent
pairs orthogonal. -/
def Good (k n : ℕ) : Prop :=
  ∃ v : Fin k → EuclideanSpace ℝ (Fin n),
    (∀ i, v i ≠ 0) ∧
    ∀ i j : Fin k, 1 < |((i : ℤ) - j)| → ⟪v i, v j⟫_ℝ = 0

determine answer (k : ℕ) : ℕ := (k + 1) / 2

snip begin

/-- The "odd index" injection `Fin ((k+1)/2) → Fin k` sending `i ↦ 2 * i`. -/
def oddIdx (k : ℕ) (i : Fin ((k + 1) / 2)) : Fin k :=
  ⟨2 * i.val, by
    have hi : i.val < (k + 1) / 2 := i.isLt
    have h2 : 2 * ((k + 1) / 2) ≤ k + 1 := Nat.mul_div_le (k + 1) 2
    omega⟩

lemma oddIdx_diff_gt_one (k : ℕ) (i j : Fin ((k + 1) / 2)) (hij : i ≠ j) :
    1 < |((oddIdx k i : ℤ) - oddIdx k j)| := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hval_i : ((oddIdx k i).val : ℤ) = 2 * (i.val : ℤ) := by
    show ((2 * i.val : ℕ) : ℤ) = _
    push_cast; ring
  have hval_j : ((oddIdx k j).val : ℤ) = 2 * (j.val : ℤ) := by
    show ((2 * j.val : ℕ) : ℤ) = _
    push_cast; ring
  have hcast : ((oddIdx k i : ℤ) - oddIdx k j) = 2 * ((i.val : ℤ) - j.val) := by
    have h1 : ((oddIdx k i : ℤ)) = 2 * (i.val : ℤ) := hval_i
    have h2 : ((oddIdx k j : ℤ)) = 2 * (j.val : ℤ) := hval_j
    rw [h1, h2]; ring
  rw [hcast, abs_mul]
  simp only [abs_two]
  have hne' : ((i.val : ℤ) - j.val) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hne : (i.val : ℤ) ≠ j.val)
  have h1 : |((i.val : ℤ) - j.val)| ≥ 1 := by
    rcases lt_or_gt_of_ne hne' with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  linarith

snip end

problem imc2018_p6 (k : ℕ) (_hk : 0 < k) :
    IsLeast {n : ℕ | Good k n} (answer k) := by
  constructor
  · -- Construction: with n = (k+1)/2, set v_i = e_{i.val/2}.
    refine ⟨fun i => EuclideanSpace.single
        (⟨i.val / 2, ?_⟩ : Fin ((k + 1) / 2)) (1 : ℝ), ?_, ?_⟩
    · -- i.val / 2 < (k+1)/2
      have hi : i.val < k := i.isLt
      omega
    · -- All vectors are nonzero
      intro i h
      have hone : EuclideanSpace.single
          (⟨i.val / 2, by have := i.isLt; omega⟩ : Fin ((k + 1) / 2))
          (1 : ℝ) ≠ 0 := by
        rw [Ne, PiLp.single_eq_zero_iff]
        exact one_ne_zero
      exact hone h
    · intro i j hij
      -- non-adjacent indices: show i.val / 2 ≠ j.val / 2
      have hne : i.val / 2 ≠ j.val / 2 := by
        intro heq
        -- From heq : i.val / 2 = j.val / 2, we get |i.val - j.val| ≤ 1 in ℕ.
        have hnat : (i.val : ℤ) - j.val = -1 ∨ (i.val : ℤ) - j.val = 0 ∨
                    (i.val : ℤ) - j.val = 1 := by
          have h1 : i.val = 2 * (i.val / 2) + i.val % 2 := (Nat.div_add_mod _ _).symm
          have h2 : j.val = 2 * (j.val / 2) + j.val % 2 := (Nat.div_add_mod _ _).symm
          have hri : i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
          have hrj : j.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
          omega
        have hcast_diff : ((i : ℤ) - j) = (i.val : ℤ) - (j.val : ℤ) := rfl
        rw [hcast_diff] at hij
        rcases hnat with h | h | h <;> · rw [h] at hij; norm_num at hij
      -- Now compute inner product
      have hidx_ne : (⟨j.val / 2, by have := j.isLt; omega⟩ :
              Fin ((k + 1) / 2)) ≠
             ⟨i.val / 2, by have := i.isLt; omega⟩ := by
        intro h
        exact hne (Fin.mk.inj_iff.mp h).symm
      have inn_eq : ∀ (a b : Fin ((k + 1) / 2)),
          ⟪EuclideanSpace.single a (1 : ℝ),
            EuclideanSpace.single b (1 : ℝ)⟫_ℝ = if a = b then (1 : ℝ) else 0 := by
        intro a b
        have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) a (1 : ℝ)
          (EuclideanSpace.single b (1 : ℝ))
        simp [PiLp.single_apply] at h
        exact h
      rw [inn_eq]
      rw [if_neg]
      intro h
      exact hne (Fin.mk.inj_iff.mp h)
  · -- Lower bound: any n with Good k n satisfies (k+1)/2 ≤ n.
    rintro n ⟨v, hv_ne, hv_orth⟩
    -- Restrict to odd indices: Fin ((k+1)/2) → ℝⁿ via i ↦ v (oddIdx k i).
    set w : Fin ((k + 1) / 2) → EuclideanSpace ℝ (Fin n) :=
      fun i => v (oddIdx k i) with hw_def
    -- w is nonzero everywhere.
    have hw_ne : ∀ i, w i ≠ 0 := fun i => hv_ne _
    -- w is pairwise orthogonal.
    have hw_orth : Pairwise (fun i j => ⟪w i, w j⟫_ℝ = 0) := by
      intro i j hij
      exact hv_orth _ _ (oddIdx_diff_gt_one k i j hij)
    -- So w is linearly independent.
    have hw_li : LinearIndependent ℝ w :=
      linearIndependent_of_ne_zero_of_inner_eq_zero hw_ne hw_orth
    -- So |Fin ((k+1)/2)| ≤ finrank ℝ ℝⁿ = n.
    have h_card : Fintype.card (Fin ((k + 1) / 2)) ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
      hw_li.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at h_card
    exact h_card

end Imc2018P6
