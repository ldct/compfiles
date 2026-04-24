/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 8

(Also listed as Day 2, Problem 2.)

Find all functions `f : ℝ → ℝ` such that for every pair `a < b` of real numbers,
the image `f([a,b])` is a closed interval of length `b - a`.

Answer: `f(x) = x + c` or `f(x) = -x + c` for some constant `c ∈ ℝ`.
-/

namespace Imc2006P8

/-- The condition that for every `a < b`, `f '' [a,b]` is a closed interval of length `b - a`. -/
def Good (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ p q : ℝ, p ≤ q ∧ q - p = b - a ∧ f '' Set.Icc a b = Set.Icc p q

/-- The set of solutions: `f(x) = x + c` or `f(x) = -x + c`. -/
determine solution_set : Set (ℝ → ℝ) :=
  {f | ∃ c : ℝ, f = fun x => x + c} ∪ {f | ∃ c : ℝ, f = fun x => -x + c}

snip begin

/-- A `Good` function is 1-Lipschitz. -/
lemma lipschitz_of_good {f : ℝ → ℝ} (hf : Good f) :
    ∀ x y : ℝ, |f x - f y| ≤ |x - y| := by
  intro x y
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · -- x < y
    obtain ⟨p, q, hpq, hlen, himg⟩ := hf x y hxy
    have hfx : f x ∈ Set.Icc p q := by
      rw [← himg]
      exact ⟨x, ⟨le_refl _, hxy.le⟩, rfl⟩
    have hfy : f y ∈ Set.Icc p q := by
      rw [← himg]
      exact ⟨y, ⟨hxy.le, le_refl _⟩, rfl⟩
    have h1 : |f x - f y| ≤ q - p := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [hfx.1, hfx.2, hfy.1, hfy.2]
      · linarith [hfx.1, hfx.2, hfy.1, hfy.2]
    have h2 : |x - y| = y - x := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    linarith
  · subst hxy; simp
  · -- y < x
    obtain ⟨p, q, hpq, hlen, himg⟩ := hf y x hxy
    have hfx : f x ∈ Set.Icc p q := by
      rw [← himg]
      exact ⟨x, ⟨hxy.le, le_refl _⟩, rfl⟩
    have hfy : f y ∈ Set.Icc p q := by
      rw [← himg]
      exact ⟨y, ⟨le_refl _, hxy.le⟩, rfl⟩
    have h1 : |f x - f y| ≤ q - p := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [hfx.1, hfx.2, hfy.1, hfy.2]
      · linarith [hfx.1, hfx.2, hfy.1, hfy.2]
    have h2 : |x - y| = x - y := abs_of_nonneg (by linarith)
    linarith

/-- A `Good` function preserves distances: `|f x - f y| = |x - y|`. -/
lemma isometry_of_good {f : ℝ → ℝ} (hf : Good f) :
    ∀ x y : ℝ, |f x - f y| = |x - y| := by
  have hLip : ∀ x y : ℝ, |f x - f y| ≤ |x - y| := lipschitz_of_good hf
  intro x y
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · -- x < y: use the image-length condition.
    obtain ⟨p, q, hpq, hlen, himg⟩ := hf x y hxy
    -- There exist a, b ∈ [x, y] with f a = p (min) and f b = q (max).
    have hp_mem : p ∈ f '' Set.Icc x y := by
      rw [himg]; exact ⟨le_refl _, hpq⟩
    have hq_mem : q ∈ f '' Set.Icc x y := by
      rw [himg]; exact ⟨hpq, le_refl _⟩
    obtain ⟨a, ha, hap⟩ := hp_mem
    obtain ⟨b, hb, hbq⟩ := hq_mem
    -- |f a - f b| = q - p = y - x, but also ≤ |a - b| ≤ y - x.
    have hab_diff : |f a - f b| = y - x := by
      rw [hap, hbq, abs_sub_comm]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)]
      linarith
    have hab_le : |a - b| ≤ y - x := by
      have ha1 : x ≤ a := ha.1
      have ha2 : a ≤ y := ha.2
      have hb1 : x ≤ b := hb.1
      have hb2 : b ≤ y := hb.2
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hab_lip : |f a - f b| ≤ |a - b| := hLip a b
    -- Conclude |a - b| = y - x
    have hab_eq : |a - b| = y - x := le_antisymm hab_le (hab_diff ▸ hab_lip)
    -- So {a, b} = {x, y}. Check both orderings.
    have ha1 : x ≤ a := ha.1
    have ha2 : a ≤ y := ha.2
    have hb1 : x ≤ b := hb.1
    have hb2 : b ≤ y := hb.2
    -- Either a = x ∧ b = y, or a = y ∧ b = x.
    have hxy_eq_abs : |x - y| = y - x := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    rcases le_or_gt a b with hab | hab
    · -- a ≤ b. |a - b| = b - a = y - x, so a = x, b = y.
      have : b - a = y - x := by
        have := hab_eq
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at this
        exact this
      have ha_x : a = x := by linarith
      have hb_y : b = y := by linarith
      -- So f x = p, f y = q (or the roles could be swapped in principle, but this
      -- particular witness gives us f a = p and f b = q, i.e. f x = p, f y = q).
      have hfx_eq : f x = p := by rw [← ha_x]; exact hap
      have hfy_eq : f y = q := by rw [← hb_y]; exact hbq
      rw [hfx_eq, hfy_eq, hxy_eq_abs]
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)]
      linarith
    · -- b < a. |a - b| = a - b = y - x, so b = x, a = y.
      have : a - b = y - x := by
        have := hab_eq
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)] at this
        exact this
      have hb_x : b = x := by linarith
      have ha_y : a = y := by linarith
      have hfy_eq : f y = p := by rw [← ha_y]; exact hap
      have hfx_eq : f x = q := by rw [← hb_x]; exact hbq
      rw [hfx_eq, hfy_eq, hxy_eq_abs]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)]
      linarith
  · subst hxy; simp
  · -- y < x: apply the previous case.
    obtain ⟨p, q, hpq, hlen, himg⟩ := hf y x hxy
    have hp_mem : p ∈ f '' Set.Icc y x := by
      rw [himg]; exact ⟨le_refl _, hpq⟩
    have hq_mem : q ∈ f '' Set.Icc y x := by
      rw [himg]; exact ⟨hpq, le_refl _⟩
    obtain ⟨a, ha, hap⟩ := hp_mem
    obtain ⟨b, hb, hbq⟩ := hq_mem
    have hab_diff : |f a - f b| = x - y := by
      rw [hap, hbq, abs_sub_comm]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)]
      linarith
    have hab_le : |a - b| ≤ x - y := by
      have ha1 : y ≤ a := ha.1
      have ha2 : a ≤ x := ha.2
      have hb1 : y ≤ b := hb.1
      have hb2 : b ≤ x := hb.2
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hab_lip : |f a - f b| ≤ |a - b| := hLip a b
    have hab_eq : |a - b| = x - y := le_antisymm hab_le (hab_diff ▸ hab_lip)
    have ha1 : y ≤ a := ha.1
    have ha2 : a ≤ x := ha.2
    have hb1 : y ≤ b := hb.1
    have hb2 : b ≤ x := hb.2
    have hxy_eq_abs : |x - y| = x - y := abs_of_nonneg (by linarith)
    rcases le_or_gt a b with hab | hab
    · have : b - a = x - y := by
        have := hab_eq
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at this
        exact this
      have ha_y : a = y := by linarith
      have hb_x : b = x := by linarith
      have hfy_eq : f y = p := by rw [← ha_y]; exact hap
      have hfx_eq : f x = q := by rw [← hb_x]; exact hbq
      rw [hfx_eq, hfy_eq, hxy_eq_abs]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)]
      linarith
    · have : a - b = x - y := by
        have := hab_eq
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - b)] at this
        exact this
      have hb_y : b = y := by linarith
      have ha_x : a = x := by linarith
      have hfx_eq : f x = p := by rw [← ha_x]; exact hap
      have hfy_eq : f y = q := by rw [← hb_y]; exact hbq
      rw [hfx_eq, hfy_eq, hxy_eq_abs]
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - p)]
      linarith

/-- Any distance-preserving `f : ℝ → ℝ` is of the form `x ↦ x + c` or `x ↦ -x + c`. -/
lemma isom_real_classify (f : ℝ → ℝ) (hf : ∀ x y, |f x - f y| = |x - y|) :
    (∃ c, f = fun x => x + c) ∨ (∃ c, f = fun x => -x + c) := by
  set c := f 0 with hc_def
  -- For every x, f x - c = ±x.
  have hval : ∀ x, f x = x + c ∨ f x = -x + c := by
    intro x
    have h := hf x 0
    rw [sub_zero] at h
    rw [abs_eq_abs] at h -- |a| = |b| ↔ a = b ∨ a = -b
    rcases h with h | h
    · left; linarith
    · right; linarith
  -- The two cases must be consistent: decide based on f 1.
  have h1 := hval 1
  rcases h1 with h1 | h1
  · -- f 1 = 1 + c. Claim f x = x + c for all x.
    left
    refine ⟨c, ?_⟩
    funext x
    rcases hval x with hx | hx
    · exact hx
    · -- f x = -x + c. Use |f 1 - f x| = |1 - x|.
      have := hf 1 x
      rw [h1, hx] at this
      -- |1 + c - (-x + c)| = |1 - x|, i.e. |1 + x| = |1 - x|.
      -- So 1 + x = 1 - x (giving x = 0, fine) or 1 + x = -(1 - x) = x - 1 (impossible).
      have heq : |1 + x| = |1 - x| := by
        have h' : |(1 : ℝ) + c - (-x + c)| = |1 + x| := by
          congr 1; ring
        rw [h'] at this
        exact this
      rw [abs_eq_abs] at heq
      rcases heq with heq | heq
      · -- 1 + x = 1 - x → x = 0
        have hx0 : x = 0 := by linarith
        rw [hx, hx0]; ring
      · -- 1 + x = -(1 - x) → impossible unless... 1 + x = -1 + x → 1 = -1, contradiction.
        linarith
  · -- f 1 = -1 + c. Claim f x = -x + c for all x.
    right
    refine ⟨c, ?_⟩
    funext x
    rcases hval x with hx | hx
    · have := hf 1 x
      rw [h1, hx] at this
      have heq : |-1 - x| = |1 - x| := by
        have h' : |(-1 : ℝ) + c - (x + c)| = |-1 - x| := by
          congr 1; ring
        rw [h'] at this
        exact this
      -- |-1 - x| = |1 + x|.
      have heq' : |1 + x| = |1 - x| := by
        rw [← heq]
        rw [show (-1 - x : ℝ) = -(1 + x) by ring, abs_neg]
      rw [abs_eq_abs] at heq'
      rcases heq' with heq' | heq'
      · have hx0 : x = 0 := by linarith
        rw [hx, hx0]; ring
      · linarith
    · exact hx

/-- The converse: if `f = fun x => x + c`, then `f` is `Good`. -/
lemma good_of_add_const (c : ℝ) : Good (fun x => x + c) := by
  intro a b hab
  refine ⟨a + c, b + c, by linarith, by ring, ?_⟩
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨y - c, ⟨by linarith, by linarith⟩, by ring⟩

/-- The converse: if `f = fun x => -x + c`, then `f` is `Good`. -/
lemma good_of_neg_add_const (c : ℝ) : Good (fun x => -x + c) := by
  intro a b hab
  refine ⟨-b + c, -a + c, by linarith, by ring, ?_⟩
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨-(y - c), ⟨by linarith, by linarith⟩, by ring⟩

snip end

problem imc2006_p8 : {f : ℝ → ℝ | Good f} = solution_set := by
  ext f
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_union]
  constructor
  · intro hf
    have hisom := isometry_of_good hf
    exact isom_real_classify f hisom
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact good_of_add_const c
    · exact good_of_neg_add_const c

end Imc2006P8
