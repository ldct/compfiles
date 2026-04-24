/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 11
(IMC 2001, Day 2, Problem 5)

Prove that there is no function `f : ℝ → ℝ` with `f(0) > 0` such that
`f(x + y) ≥ f(x) + y * f(f(x))` for all `x, y ∈ ℝ`.
-/

namespace Imc2001P11

snip begin

/-- If `f(f(x)) ≤ 0` for all `x`, then the hypothesis forces `f` to be
non-increasing on `ℝ`. -/
lemma f_antitone_of_ff_nonpos
    (f : ℝ → ℝ)
    (hf : ∀ x y : ℝ, f x + y * f (f x) ≤ f (x + y))
    (hff : ∀ x : ℝ, f (f x) ≤ 0) :
    ∀ a b : ℝ, a ≤ b → f b ≤ f a := by
  intro a b hab
  -- Take x = b, y = a - b ≤ 0. Then f(b + (a-b)) ≥ f(b) + (a-b)·f(f(b)).
  -- Since a - b ≤ 0 and f(f(b)) ≤ 0, (a-b)·f(f(b)) ≥ 0, so f(a) ≥ f(b).
  have h1 : f b + (a - b) * f (f b) ≤ f (b + (a - b)) := hf b (a - b)
  have hab' : a - b ≤ 0 := by linarith
  have hprod : 0 ≤ (a - b) * f (f b) :=
    mul_nonneg_of_nonpos_of_nonpos hab' (hff b)
  have : b + (a - b) = a := by ring
  rw [this] at h1
  linarith

snip end

problem imc2001_p11 :
    ¬ ∃ f : ℝ → ℝ, 0 < f 0 ∧
      ∀ x y : ℝ, f x + y * f (f x) ≤ f (x + y) := by
  rintro ⟨f, hf0, hf⟩
  -- Step 1: Show there exists z with f(f(z)) > 0.
  -- Suppose not: f(f(x)) ≤ 0 for all x. Then f is non-increasing.
  -- From f(0) > 0 ≥ f(f(z)), non-increasing gives: if f(z) ≤ 0, then f(f(z)) ≥ f(0) > 0,
  -- contradiction. So f(z) > 0 for all z. But then f(f(z)) > 0 too, also contradiction.
  have hexists_pos : ∃ z : ℝ, 0 < f (f z) := by
    by_contra hneg
    push Not at hneg
    have hff : ∀ x : ℝ, f (f x) ≤ 0 := hneg
    have hanti := f_antitone_of_ff_nonpos f hf hff
    -- For all z, f(z) > 0.
    have hfpos : ∀ z : ℝ, 0 < f z := by
      intro z
      by_contra hfz
      push Not at hfz
      -- f(z) ≤ 0, so f(f(z)) ≥ f(0) > 0 (non-increasing reversed)
      have : f 0 ≤ f (f z) := hanti (f z) 0 hfz
      have : 0 < f (f z) := lt_of_lt_of_le hf0 this
      exact absurd this (not_lt.mpr (hff z))
    -- But then f(f(0)) > 0, contradicting hff
    exact absurd (hfpos (f 0)) (not_lt.mpr (hff 0))
  obtain ⟨z, hz_pos⟩ := hexists_pos
  -- Step 2: f grows to infinity. Specifically, for all x ≥ z:
  -- f(x) ≥ f(z) + (x - z) * f(f(z)), so lim f = +∞.
  have hgrow : ∀ w : ℝ, f z + w * f (f z) ≤ f (z + w) := fun w => hf z w
  -- Step 3: Pick a sufficiently large argument. We want to choose x, y > 0 such that
  --   (a) f(x) ≥ 0
  --   (b) f(f(x)) > 1
  --   (c) y * (f(f(x)) - 1) ≥ x + 1  (so y * f(f(x)) ≥ x + y + 1)
  --   (d) f(f(x + y + 1)) ≥ 0
  --   (e) y > 0
  -- Since f(z + w) → ∞ as w → ∞, we have f(u) → ∞ as u → ∞,
  -- so f(f(u)) → ∞ too.
  -- First, f(u) ≥ 1 for all u ≥ u₀ for some u₀. Then f(f(u)) ≥ some large, etc.

  -- Lemma: for any M, there is N such that u ≥ N ⟹ f(u) ≥ M.
  have hfto : ∀ M : ℝ, ∃ N : ℝ, ∀ u ≥ N, M ≤ f u := by
    intro M
    -- f(z + w) ≥ f z + w * f(f z). For this to be ≥ M, need w ≥ (M - f z)/f(f z).
    set c := f (f z)
    have hc : 0 < c := hz_pos
    refine ⟨z + (M - f z)/c, ?_⟩
    intro u hu
    have hw : u - z ≥ (M - f z)/c := by linarith
    have key : f z + (u - z) * c ≤ f (z + (u - z)) := hgrow (u - z)
    have hzu : z + (u - z) = u := by ring
    rw [hzu] at key
    have : (M - f z) ≤ (u - z) * c := by
      have := (div_le_iff₀ hc).mp hw
      linarith
    linarith
  -- Lemma: f(f(u)) → ∞ as u → ∞.
  have hffto : ∀ M : ℝ, ∃ N : ℝ, ∀ u ≥ N, M ≤ f (f u) := by
    intro M
    -- First ensure f(u) ≥ N₁ where N₁ gives f(N₁') ≥ M.
    obtain ⟨N1, hN1⟩ := hfto M
    obtain ⟨N0, hN0⟩ := hfto N1
    refine ⟨N0, ?_⟩
    intro u hu
    exact hN1 (f u) (hN0 u hu)
  -- Step 4: Pick the right x and y.
  -- We want x large enough that f(x) ≥ 0 and f(f(x)) ≥ 2.
  -- Then choose y such that y > 0, y ≥ x + 1 and f(f(x + y + 1)) ≥ 0.
  obtain ⟨N_fge, hN_fge⟩ := hfto 0
  obtain ⟨N_ffge, hN_ffge⟩ := hffto 2
  obtain ⟨N_ff0, hN_ff0⟩ := hffto 0
  set x := max (max N_fge N_ffge) 1 with hx_def
  have hx_fge : 0 ≤ f x := hN_fge x (le_trans (le_max_left _ _) (le_max_left _ _))
  have hx_ffge : 2 ≤ f (f x) := hN_ffge x (le_trans (le_max_right _ _) (le_max_left _ _))
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  -- Choose y ≥ max (x + 1) (N_ff0 - x - 1) + 1, and y > 0.
  set y := max (max (x + 1) (N_ff0 - x - 1)) 1 with hy_def
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hy_x1 : x + 1 ≤ y :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hy_for_ff0 : N_ff0 ≤ x + y + 1 := by
    have : N_ff0 - x - 1 ≤ y :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hff_xy1 : 0 ≤ f (f (x + y + 1)) := hN_ff0 (x + y + 1) hy_for_ff0
  -- Step 5: Derive the contradiction.
  -- From the functional inequality applied to (x, y):
  --   f(x + y) ≥ f(x) + y * f(f(x))
  -- We have f(x) ≥ 0 and y * f(f(x)) ≥ y * 2 = 2y ≥ y + (x+1) = x + y + 1.
  -- So f(x + y) ≥ x + y + 1.
  have hstep1 : f x + y * f (f x) ≤ f (x + y) := hf x y
  have hy_ff : x + y + 1 ≤ y * f (f x) := by
    have : y * 2 ≤ y * f (f x) := by
      apply mul_le_mul_of_nonneg_left hx_ffge (le_of_lt hy_pos)
    linarith
  have hbig : x + y + 1 ≤ f (x + y) := by linarith
  -- Now: f(f(x + y)) ≥ f(x + y + 1) + (f(x + y) - (x + y + 1)) * f(f(x + y + 1))
  -- Apply the functional inequality with (x + y + 1, f(x + y) - (x + y + 1)):
  have hstep2 : f (x + y + 1) + (f (x + y) - (x + y + 1)) * f (f (x + y + 1)) ≤
                f ((x + y + 1) + (f (x + y) - (x + y + 1))) := hf _ _
  have h_arg_eq : (x + y + 1) + (f (x + y) - (x + y + 1)) = f (x + y) := by ring
  rw [h_arg_eq] at hstep2
  have h_diff_nn : 0 ≤ f (x + y) - (x + y + 1) := by linarith
  have h_prod_nn : 0 ≤ (f (x + y) - (x + y + 1)) * f (f (x + y + 1)) :=
    mul_nonneg h_diff_nn hff_xy1
  -- So f(f(x + y)) ≥ f(x + y + 1).
  have hstep3 : f (x + y + 1) ≤ f (f (x + y)) := by linarith
  -- From hf at (x + y, 1): f(x + y + 1) ≥ f(x + y) + f(f(x + y)).
  have hstep4 : f (x + y) + 1 * f (f (x + y)) ≤ f (x + y + 1) := hf (x + y) 1
  have hstep5 : f (x + y) + f (f (x + y)) ≤ f (x + y + 1) := by linarith
  -- So f(f(x + y)) ≥ f(x + y) + f(f(x + y)).
  have hstep6 : f (x + y) + f (f (x + y)) ≤ f (f (x + y)) := le_trans hstep5 hstep3
  -- So f(x + y) ≤ 0.
  have hxy_nonpos : f (x + y) ≤ 0 := by linarith
  -- But f(x + y) ≥ x + y + 1 > 0, contradiction.
  have : 0 < f (x + y) := by linarith
  linarith

end Imc2001P11
