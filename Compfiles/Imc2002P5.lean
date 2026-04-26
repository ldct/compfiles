/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Real.Cardinality

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 5
(IMC 2002, Day 1, Problem 5(a))

Does there exist a monotone function `f : [0,1] → [0,1]` such that for every
`y ∈ [0,1]` the fiber `f⁻¹{y}` is uncountable?

Answer: No.

Proof. Each fiber `f⁻¹{y} ∩ [0,1]` is order-connected because `f` is monotone.
An uncountable order-connected subset of `ℝ` contains two distinct points
`a < b`, and hence the entire open interval `(a, b)`. We thus obtain a family
`y ↦ (a_y, b_y)` of pairwise disjoint nonempty open intervals indexed by
`[0,1]`. By separability of `ℝ`, such a family must be countable, but `[0,1]`
is uncountable — a contradiction.
-/

namespace Imc2002P5

open Set

snip begin

/-- An order-connected uncountable subset of `ℝ` contains a nonempty open
interval. -/
lemma exists_Ioo_subset_of_ordConnected_not_countable
    {S : Set ℝ} (hS : S.OrdConnected) (huncnt : ¬ S.Countable) :
    ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ S := by
  -- An uncountable set is in particular not a subsingleton.
  have hns : ¬ S.Subsingleton := by
    intro hsub
    exact huncnt hsub.countable
  -- So there exist two distinct elements of `S`.
  rcases not_subsingleton_iff.mp hns with ⟨x, hx, y, hy, hxy⟩
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · -- x < y
    refine ⟨x, y, hlt, ?_⟩
    intro z hz
    exact hS.out hx hy ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  · -- y < x
    refine ⟨y, x, hlt, ?_⟩
    intro z hz
    exact hS.out hy hx ⟨le_of_lt hz.1, le_of_lt hz.2⟩

snip end

problem imc2002_p5 :
    ¬ ∃ f : ℝ → ℝ,
        MonotoneOn f (Icc (0 : ℝ) 1) ∧
        MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
        ∀ y ∈ Icc (0 : ℝ) 1, ¬ (f ⁻¹' {y} ∩ Icc (0 : ℝ) 1).Countable := by
  rintro ⟨f, hmono, _hmap, hfib⟩
  -- For each `y ∈ [0,1]`, the fiber-in-Icc is order-connected.
  have hOrd : ∀ y ∈ Icc (0 : ℝ) 1,
      (f ⁻¹' {y} ∩ Icc (0 : ℝ) 1).OrdConnected := by
    intro y _hy
    refine ⟨?_⟩
    intro a ha b hb c hc
    -- c ∈ [0,1]: it lies in [a,b] ⊆ [0,1].
    have hc01 : c ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans ha.2.1 hc.1, le_trans hc.2 hb.2.2⟩
    refine ⟨?_, hc01⟩
    -- f c = y: by monotonicity, f a ≤ f c ≤ f b, and f a = f b = y, so f c = y.
    have hfa : f a = y := ha.1
    have hfb : f b = y := hb.1
    have hac : f a ≤ f c := hmono ha.2 hc01 hc.1
    have hcb : f c ≤ f b := hmono hc01 hb.2 hc.2
    have : f c = y := le_antisymm (hfb ▸ hcb) (hfa ▸ hac)
    simpa [Set.mem_preimage] using this
  -- For each `y ∈ [0,1]`, choose an open interval `Ioo (a y) (b y)` inside the fiber.
  choose a b hab hsub using fun y (hy : y ∈ Icc (0 : ℝ) 1) =>
    exists_Ioo_subset_of_ordConnected_not_countable (hOrd y hy) (hfib y hy)
  -- Define `I : Icc 0 1 → Set ℝ` by `I ⟨y, hy⟩ = Ioo (a y hy) (b y hy)`.
  let I : Icc (0 : ℝ) 1 → Set ℝ := fun yy => Ioo (a yy.1 yy.2) (b yy.1 yy.2)
  -- Each `I yy` is open and nonempty, and the family is pairwise disjoint
  -- because the fibers are.
  have hI_open : ∀ yy, IsOpen (I yy) := fun yy => isOpen_Ioo
  have hI_ne : ∀ yy, (I yy).Nonempty := fun yy => nonempty_Ioo.mpr (hab yy.1 yy.2)
  have hI_disj : Pairwise (Function.onFun Disjoint I) := by
    intro u v huv
    -- The fibers `f ⁻¹' {u.1}` and `f ⁻¹' {v.1}` are disjoint.
    have hfib_disj : Disjoint (f ⁻¹' {(u.1 : ℝ)}) (f ⁻¹' {(v.1 : ℝ)}) := by
      apply Disjoint.preimage
      rw [disjoint_singleton]
      intro h
      apply huv
      exact Subtype.ext h
    -- I u ⊆ f ⁻¹' {u.1}, I v ⊆ f ⁻¹' {v.1}.
    have hIu_sub : I u ⊆ f ⁻¹' {(u.1 : ℝ)} := by
      intro z hz
      have := hsub u.1 u.2 hz
      exact this.1
    have hIv_sub : I v ⊆ f ⁻¹' {(v.1 : ℝ)} := by
      intro z hz
      have := hsub v.1 v.2 hz
      exact this.1
    exact hfib_disj.mono hIu_sub hIv_sub
  -- By separability of ℝ, the index type `Icc 0 1` is countable.
  have hcount : Countable (Icc (0 : ℝ) 1) :=
    hI_disj.countable_of_isOpen_disjoint hI_open hI_ne
  -- But `Icc 0 1` is uncountable.
  have huncnt : ¬ (Icc (0 : ℝ) 1).Countable := by
    rw [Cardinal.Real.Icc_countable_iff]; norm_num
  apply huncnt
  rw [Set.countable_coe_iff] at hcount
  exact hcount

end Imc2002P5
