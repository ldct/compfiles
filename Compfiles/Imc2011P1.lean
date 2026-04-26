/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2011, Problem 1

Let `f : ℝ → ℝ` be a continuous function. A point `x` is called a *shadow point*
if there exists `y ∈ ℝ` with `y > x` such that `f(y) > f(x)`. Let `a < b` be
real numbers and suppose that
- all points of the open interval `(a, b)` are shadow points;
- `a` and `b` are not shadow points.

Prove that
(a) `f(x) ≤ f(b)` for all `a < x < b`;
(b) `f(a) = f(b)`.

## Solution

(a) Suppose for contradiction `c ∈ (a, b)` with `f(c) > f(b)`. The restriction
of `f` to `[c, b]` attains its maximum at some `d ∈ [c, b]` (compactness). Since
`f(d) ≥ f(c) > f(b)`, `d ≠ b`, so `d ∈ [c, b) ⊂ (a, b)` and therefore `d` is a
shadow point. Pick `y > d` with `f(y) > f(d)`. Either `y ≤ b`, contradicting
maximality of `f(d)` on `[c, b]`; or `y > b`, and then `f(y) > f(d) > f(b)`
contradicts `b` not being a shadow point.

(b) From (a), `f(x) ≤ f(b)` on `(a, b)`. Continuity at `a` gives `f(a) ≤ f(b)`.
Since `a` is not a shadow point, `f(y) ≤ f(a)` for all `y > a`; taking `y = b`
gives `f(b) ≤ f(a)`.
-/

namespace Imc2011P1

/-- `x` is a shadow point of `f` if there is some `y > x` with `f y > f x`. -/
def ShadowPoint (f : ℝ → ℝ) (x : ℝ) : Prop := ∃ y, x < y ∧ f x < f y

snip begin

/-- Part (a): under the hypothesis, `f x ≤ f b` on `(a, b)`. -/
lemma part_a {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hI : ∀ x ∈ Set.Ioo a b, ShadowPoint f x)
    (hb : ¬ ShadowPoint f b) :
    ∀ x ∈ Set.Ioo a b, f x ≤ f b := by
  intro c hc
  by_contra hlt
  push Not at hlt
  -- f attains max on [c, b] at some d.
  have hcb : c ≤ b := hc.2.le
  have hcompact : IsCompact (Set.Icc c b) := isCompact_Icc
  have hne : (Set.Icc c b).Nonempty := ⟨c, Set.left_mem_Icc.mpr hcb⟩
  obtain ⟨d, hd_mem, hd_max⟩ := hcompact.exists_isMaxOn hne hf.continuousOn
  -- f c ≤ f d, so f b < f d.
  have hfc_le : f c ≤ f d := hd_max (Set.left_mem_Icc.mpr hcb)
  have hfb_lt : f b < f d := lt_of_lt_of_le hlt hfc_le
  -- So d ≠ b, hence d < b.
  have hd_ne_b : d ≠ b := fun h => by rw [h] at hfb_lt; exact lt_irrefl _ hfb_lt
  have hd_lt_b : d < b := lt_of_le_of_ne hd_mem.2 hd_ne_b
  -- d ∈ (a, b): from d ≥ c > a and d < b.
  have hac : a < c := hc.1
  have ha_lt_d : a < d := lt_of_lt_of_le hac hd_mem.1
  have hd_mem' : d ∈ Set.Ioo a b := ⟨ha_lt_d, hd_lt_b⟩
  -- d is a shadow point.
  obtain ⟨y, hdy, hfy⟩ := hI d hd_mem'
  -- Case on y ≤ b or y > b.
  by_cases hyb : y ≤ b
  · -- y ∈ (d, b], so y ∈ [c, b]; f y ≤ f d, contradiction with f d < f y.
    have hcy : c ≤ y := le_trans hd_mem.1 hdy.le
    have hy_mem : y ∈ Set.Icc c b := ⟨hcy, hyb⟩
    have : f y ≤ f d := hd_max hy_mem
    linarith
  · -- y > b, but then f y > f d > f b so b is a shadow point, contradiction.
    push Not at hyb
    exact hb ⟨y, hyb, lt_trans hfb_lt hfy⟩

snip end

problem imc2011_p1 {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hI : ∀ x ∈ Set.Ioo a b, ShadowPoint f x)
    (ha : ¬ ShadowPoint f a) (hb : ¬ ShadowPoint f b) :
    (∀ x ∈ Set.Ioo a b, f x ≤ f b) ∧ f a = f b := by
  have hA : ∀ x ∈ Set.Ioo a b, f x ≤ f b := part_a hf hI hb
  refine ⟨hA, ?_⟩
  -- (b) f a ≤ f b by continuity; f b ≤ f a since a is not a shadow point.
  have h_le : f a ≤ f b := by
    -- Take the limit from the right at a: f x → f a with f x ≤ f b eventually.
    have hcont_at : ContinuousAt f a := hf.continuousAt
    -- Use the sequence a + (b - a)/n.
    by_contra h
    push Not at h  -- f b < f a
    -- Since f is continuous at a, there is a neighborhood where f x > f b.
    have hpos : 0 < f a - f b := by linarith
    have : ∀ᶠ x in nhds a, |f x - f a| < (f a - f b) / 2 := by
      have := (Metric.tendsto_nhds.mp hcont_at.tendsto) ((f a - f b) / 2) (by linarith)
      simpa [Real.dist_eq] using this
    -- Also eventually x ∈ (a, b).
    have h_right : ∀ᶠ x in nhds a, x < b := by
      exact (eventually_lt_nhds hab).mono (fun x hx => hx)
    have h_left : ∀ᶠ x in nhdsWithin a (Set.Ioi a), a < x :=
      self_mem_nhdsWithin
    have h1 : ∀ᶠ x in nhdsWithin a (Set.Ioi a), |f x - f a| < (f a - f b) / 2 :=
      nhdsWithin_le_nhds this
    have h2 : ∀ᶠ x in nhdsWithin a (Set.Ioi a), x < b :=
      nhdsWithin_le_nhds h_right
    have hcomb : ∀ᶠ x in nhdsWithin a (Set.Ioi a),
        a < x ∧ x < b ∧ |f x - f a| < (f a - f b) / 2 :=
      h_left.and (h2.and h1) |>.mono (fun x ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩)
    -- This filter is non-bot.
    have : (nhdsWithin a (Set.Ioi a)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
      (by rw [closure_Ioi]; exact Set.self_mem_Ici)
    obtain ⟨x, hax, hxb, hxabs⟩ := hcomb.exists
    -- f x ≤ f b from part (a).
    have : f x ≤ f b := hA x ⟨hax, hxb⟩
    -- But |f x - f a| < (f a - f b)/2 means f x > f a - (f a - f b)/2 = (f a + f b)/2 > f b.
    have habs : f a - f x < (f a - f b) / 2 := by
      have := abs_lt.mp hxabs
      linarith
    linarith
  have h_ge : f b ≤ f a := by
    -- a is not a shadow point, so there's no y > a with f y > f a. Apply to y = b.
    by_contra h
    push Not at h
    exact ha ⟨b, hab, h⟩
  linarith

end Imc2011P1
