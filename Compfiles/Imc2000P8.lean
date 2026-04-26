/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 8 (Day 2, Problem 2)

Let `f : ℝ → ℝ` be continuous on `[0, 1]` and *nowhere monotone*: for every
non-degenerate closed subinterval `[a, b] ⊆ [0, 1]`, the function `f` is
neither monotone nor antitone on `[a, b]`. Show that the set of local
minima of `f` is dense in `[0, 1]`.

We formalize the conclusion as: for every `x ∈ [0, 1]` and every `ε > 0`,
there exists a point `y ∈ (x - ε, x + ε) ∩ [0, 1]` which is a local minimum
of `f` on `ℝ`.

The proof follows the standard argument. Pick a center `c ∈ (x - ε, x + ε)`
with `0 < c < 1`, and a small `α > 0` so that `[c - α, c + α] ⊆
[0, 1] ∩ (x - ε, x + ε)`. Since `f` is not monotone on `[c - α, c]`, there
exist `p ≤ q` in this interval with `f q < f p`. Since `f` is not antitone
on `[c, c + α]`, there exist `r ≤ s` in that interval with `f r < f s`. The
continuous function `f` attains its minimum on the compact interval
`[p, s]` at some point `m`; since `f q < f p` and `f r < f s`, the minimum
is not attained at the endpoints `p` or `s`. Hence `p < m < s`, which means
`(p, s)` is an open neighborhood of `m` on which `f m` is a lower bound.
Therefore `m` is a local minimum lying in `(x - α, x + α)`.
-/

namespace Imc2000P8

open Set

problem imc2000_p8
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hnm : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
              ¬ MonotoneOn f (Set.Icc a b) ∧ ¬ AntitoneOn f (Set.Icc a b)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ ε > 0,
      ∃ y, y ∈ Set.Ioo (x - ε) (x + ε) ∩ Set.Icc (0 : ℝ) 1 ∧ IsLocalMin f y := by
  intro x hx ε hε
  obtain ⟨hx0, hx1⟩ := hx
  -- Pick a center c with x - ε < c < x + ε and 0 < c < 1.
  -- Take c := (max (x - ε) 0 + min (x + ε) 1) / 2.
  let L : ℝ := max (x - ε) 0
  let R : ℝ := min (x + ε) 1
  have hL_lo : x - ε ≤ L := le_max_left _ _
  have hL_lo0 : 0 ≤ L := le_max_right _ _
  have hR_hi : R ≤ x + ε := min_le_left _ _
  have hR_hi1 : R ≤ 1 := min_le_right _ _
  have hL_lt_R : L < R := by
    show max (x - ε) 0 < min (x + ε) 1
    have h1 : x - ε < x + ε := by linarith
    have h2 : x - ε < 1 := by linarith
    have h3 : (0 : ℝ) < x + ε := by linarith
    have h4 : (0 : ℝ) < 1 := by norm_num
    exact max_lt (lt_min h1 h2) (lt_min h3 h4)
  let c : ℝ := (L + R) / 2
  have hcL : L < c := by
    show L < (L + R) / 2
    linarith
  have hcR : c < R := by
    show (L + R) / 2 < R
    linarith
  have hc_pos : 0 < c := lt_of_le_of_lt hL_lo0 hcL
  have hc_lt_one : c < 1 := lt_of_lt_of_le hcR hR_hi1
  have hc_lo : x - ε < c := lt_of_le_of_lt hL_lo hcL
  have hc_hi : c < x + ε := lt_of_lt_of_le hcR hR_hi
  -- Choose α small enough.
  let α : ℝ := min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) / 2
  have h1 : (0 : ℝ) < c := hc_pos
  have h2 : (0 : ℝ) < 1 - c := by linarith
  have h3 : (0 : ℝ) < c - (x - ε) := by linarith
  have h4 : (0 : ℝ) < (x + ε) - c := by linarith
  have hmin1 : (0 : ℝ) < min c (1 - c) := lt_min h1 h2
  have hmin2 : (0 : ℝ) < min (c - (x - ε)) ((x + ε) - c) := lt_min h3 h4
  have hmin_pos : (0 : ℝ) < min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) :=
    lt_min hmin1 hmin2
  have hα_pos : 0 < α := by
    show 0 < min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) / 2
    linarith
  have hα_lt_min : α < min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) := by
    show min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) / 2 <
         min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c))
    linarith
  have hα_le_c : α < c := by
    have step1 : min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) ≤ min c (1 - c) :=
      min_le_left _ _
    have step2 : min c (1 - c) ≤ c := min_le_left _ _
    linarith
  have hα_le_one_sub_c : α < 1 - c := by
    have step1 : min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) ≤ min c (1 - c) :=
      min_le_left _ _
    have step2 : min c (1 - c) ≤ 1 - c := min_le_right _ _
    linarith
  have hα_lo : c - α > x - ε := by
    have step1 : min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) ≤
        min (c - (x - ε)) ((x + ε) - c) := min_le_right _ _
    have step2 : min (c - (x - ε)) ((x + ε) - c) ≤ c - (x - ε) := min_le_left _ _
    linarith
  have hα_hi : c + α < x + ε := by
    have step1 : min (min c (1 - c)) (min (c - (x - ε)) ((x + ε) - c)) ≤
        min (c - (x - ε)) ((x + ε) - c) := min_le_right _ _
    have step2 : min (c - (x - ε)) ((x + ε) - c) ≤ (x + ε) - c := min_le_right _ _
    linarith
  have hca_pos : 0 ≤ c - α := by linarith
  have hca_lt_c : c - α < c := by linarith
  have hca_le_one : c - α ≤ 1 := by linarith
  have hc_lt_ca : c < c + α := by linarith
  have hca_le_one' : c + α ≤ 1 := by linarith
  -- Apply nowhere-monotone on [c - α, c]: f is not monotone on it.
  have hnm_left := (hnm (c - α) c hca_pos hca_lt_c (by linarith)).1
  -- Apply nowhere-antitone on [c, c + α]: f is not antitone on it.
  have hnm_right := (hnm c (c + α) (le_of_lt hc_pos) hc_lt_ca hca_le_one').2
  -- Extract p ≤ q in [c - α, c] with f q < f p.
  rw [MonotoneOn] at hnm_left
  push Not at hnm_left
  obtain ⟨p, hp, q, hq, hpq, hfpq⟩ := hnm_left
  -- Extract r ≤ s in [c, c + α] with f r < f s.
  rw [AntitoneOn] at hnm_right
  push Not at hnm_right
  obtain ⟨r, hr, s, hs, hrs, hfrs⟩ := hnm_right
  have hp_le_q : p ≤ q := hpq
  have hr_le_s : r ≤ s := hrs
  have hfq_lt_fp : f q < f p := hfpq
  have hfr_lt_fs : f r < f s := hfrs
  have hp_lo : c - α ≤ p := hp.1
  have hp_hi : p ≤ c := hp.2
  have hq_lo : c - α ≤ q := hq.1
  have hq_hi : q ≤ c := hq.2
  have hr_lo : c ≤ r := hr.1
  have hr_hi : r ≤ c + α := hr.2
  have hs_lo : c ≤ s := hs.1
  have hs_hi : s ≤ c + α := hs.2
  have hp_lt_q : p < q := lt_of_le_of_ne hp_le_q (by
    intro heq; rw [heq] at hfq_lt_fp; exact lt_irrefl _ hfq_lt_fp)
  have hr_lt_s : r < s := lt_of_le_of_ne hr_le_s (by
    intro heq; rw [heq] at hfr_lt_fs; exact lt_irrefl _ hfr_lt_fs)
  have hp_lt_s : p < s := by linarith
  have hp_le_s : p ≤ s := le_of_lt hp_lt_s
  have hps_sub_unit : Set.Icc p s ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    obtain ⟨hyl, hyr⟩ := hy
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  have hcont_ps : ContinuousOn f (Set.Icc p s) := hcont.mono hps_sub_unit
  have hps_compact : IsCompact (Set.Icc p s) := isCompact_Icc
  have hps_ne : (Set.Icc p s).Nonempty := ⟨p, le_refl _, hp_le_s⟩
  obtain ⟨m, hm_mem, hm_min⟩ := hps_compact.exists_isMinOn hps_ne hcont_ps
  have hq_in_ps : q ∈ Set.Icc p s := ⟨hp_le_q, by linarith⟩
  have hr_in_ps : r ∈ Set.Icc p s := ⟨by linarith, hr_le_s⟩
  have hm_le_q : f m ≤ f q := hm_min hq_in_ps
  have hm_le_r : f m ≤ f r := hm_min hr_in_ps
  have hm_ne_p : m ≠ p := by
    intro heq
    rw [heq] at hm_le_q
    linarith
  have hm_ne_s : m ≠ s := by
    intro heq
    rw [heq] at hm_le_r
    linarith
  have hpm : p < m := lt_of_le_of_ne hm_mem.1 (Ne.symm hm_ne_p)
  have hms : m < s := lt_of_le_of_ne hm_mem.2 hm_ne_s
  have hps_open_sub : Set.Ioo p s ⊆ Set.Icc p s := fun y hy =>
    ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hm_in_ioo : m ∈ Set.Ioo p s := ⟨hpm, hms⟩
  have hloc : IsLocalMin f m := by
    have hnhds : Set.Icc p s ∈ nhds m := by
      apply mem_nhds_iff.mpr
      exact ⟨Set.Ioo p s, hps_open_sub, isOpen_Ioo, hm_in_ioo⟩
    exact hm_min.isLocalMin hnhds
  refine ⟨m, ⟨⟨?_, ?_⟩, ?_, ?_⟩, hloc⟩
  · -- x - ε < m
    linarith
  · -- m < x + ε
    linarith
  · -- 0 ≤ m
    linarith
  · -- m ≤ 1
    linarith

end Imc2000P8
