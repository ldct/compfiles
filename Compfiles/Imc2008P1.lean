/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2008, Problem 1

Find all continuous functions `f : ℝ → ℝ` such that `f(x) - f(y)` is rational
whenever `x - y` is rational.

Answer: `f(x) = a * x + b` with `a ∈ ℚ` and `b ∈ ℝ`.
-/

namespace Imc2008P1

/-- The set of functions `f : ℝ → ℝ` of the form `x ↦ a * x + b` for some
rational `a` and real `b`. -/
def AffineRat : Set (ℝ → ℝ) :=
  {f | ∃ (a : ℚ) (b : ℝ), f = fun x => (a : ℝ) * x + b}

/-- The hypothesis of the problem: `f(x) - f(y)` is rational whenever
`x - y` is rational. -/
def RatDifference (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, (∃ q : ℚ, x - y = q) → ∃ r : ℚ, f x - f y = r

determine answer : Set (ℝ → ℝ) := AffineRat

snip begin

/-- A preconnected subset of `ℝ` that is contained in the image of `ℚ` is a
singleton (or empty). -/
lemma subsingleton_of_preconnected_subset_rat {s : Set ℝ}
    (hs : IsPreconnected s) (hrat : s ⊆ Set.range ((↑) : ℚ → ℝ)) :
    s.Subsingleton := by
  intro x hx y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- x < y: pick an irrational in (x, y).
    have hord : Set.OrdConnected s := hs.ordConnected
    have hIcc : Set.Icc x y ⊆ s := hord.out hx hy
    obtain ⟨z, hz_irr, hzx, hzy⟩ := exists_irrational_btwn hlt
    have hzmem : z ∈ s := hIcc ⟨hzx.le, hzy.le⟩
    obtain ⟨q, hq⟩ := hrat hzmem
    exact hz_irr ⟨q, hq⟩
  · -- y < x: symmetric.
    have hord : Set.OrdConnected s := hs.ordConnected
    have hIcc : Set.Icc y x ⊆ s := hord.out hy hx
    obtain ⟨z, hz_irr, hzx, hzy⟩ := exists_irrational_btwn hgt
    have hzmem : z ∈ s := hIcc ⟨hzx.le, hzy.le⟩
    obtain ⟨q, hq⟩ := hrat hzmem
    exact hz_irr ⟨q, hq⟩

/-- A continuous function `g : ℝ → ℝ` whose values are all rational is constant. -/
lemma constant_of_rat_valued {g : ℝ → ℝ} (hcont : Continuous g)
    (hrat : ∀ x, ∃ q : ℚ, g x = q) :
    ∀ x y, g x = g y := by
  intro x y
  have hrange_sub : Set.range g ⊆ Set.range ((↑) : ℚ → ℝ) := by
    rintro v ⟨u, rfl⟩
    obtain ⟨q, hq⟩ := hrat u
    exact ⟨q, hq.symm⟩
  have hpre : IsPreconnected (Set.range g) :=
    isPreconnected_range hcont
  have hsub : (Set.range g).Subsingleton :=
    subsingleton_of_preconnected_subset_rat hpre hrange_sub
  exact hsub ⟨x, rfl⟩ ⟨y, rfl⟩

snip end

problem imc2008_p1 (f : ℝ → ℝ) (hcont : Continuous f) :
    RatDifference f ↔ f ∈ answer := by
  show RatDifference f ↔ f ∈ AffineRat
  constructor
  · intro hrd
    -- Define a := f(1) - f(0). Since 1 - 0 = 1 ∈ ℚ, a ∈ ℚ.
    obtain ⟨a, ha⟩ : ∃ a : ℚ, f 1 - f 0 = a := hrd 1 0 ⟨1, by norm_num⟩
    -- Define b := f(0).
    set b : ℝ := f 0 with hb
    -- Step 1: For each rational q, the function x ↦ f(x+q) - f(x) is constant.
    -- In particular, f(x+q) - f(x) = f(q) - f(0) = f(q) - b.
    have hshift : ∀ (q : ℚ) (x : ℝ), f (x + q) - f x = f q - b := by
      intro q x
      -- Consider g(t) = f(t + q) - f t. This is continuous and takes rational values.
      set g : ℝ → ℝ := fun t => f (t + q) - f t with hg_def
      have hg_cont : Continuous g := by
        exact (hcont.comp (continuous_id.add continuous_const)).sub hcont
      have hg_rat : ∀ t, ∃ r : ℚ, g t = r := by
        intro t
        exact hrd (t + q) t ⟨q, by ring⟩
      -- g is constant.
      have hgc : g x = g 0 := constant_of_rat_valued hg_cont hg_rat x 0
      simp only [hg_def] at hgc
      -- hgc : f (x + q) - f x = f (0 + q) - f 0
      rw [show (0 : ℝ) + (q : ℝ) = (q : ℝ) from by ring] at hgc
      show f (x + (q : ℝ)) - f x = f (q : ℝ) - b
      linarith
    -- Step 2: For each rational q, f(q) - f(0) = q * a.
    -- Define c : ℚ → ℝ, c q = f q - f 0. Show c is additive and homogeneous
    -- over ℤ, hence c q = q * c 1 = q * a.
    have hcq : ∀ q : ℚ, f q - b = q * a := by
      -- Let c q := f q - b. Show:
      -- (a) c 0 = 0.
      -- (b) c (q + r) = c q + c r (using hshift applied in two ways).
      -- (c) c (n * q) = n * c q for n : ℕ and then ℤ.
      -- (d) Hence c is a ℤ-linear map ℚ → ℝ, so c q = q * c 1 for all q ∈ ℚ.
      -- We directly prove by writing q = num / den.
      set c : ℚ → ℝ := fun q => f (q : ℝ) - b with hc_def
      have hc_zero : c 0 = 0 := by simp [hc_def, b]
      have hc_one : c 1 = a := by simp [hc_def, b, ha]
      -- additivity: c (q + r) = c q + c r for q r : ℚ.
      have hc_add : ∀ q r : ℚ, c (q + r) = c q + c r := by
        intro q r
        -- Use hshift: f(q + r) - f q = f r - b; also f q - b = c q, so
        -- f(q + r) = f q + f r - b. Therefore c(q+r) = f q + f r - 2b = (f q - b) + (f r - b).
        have h1 : f ((q : ℝ) + (r : ℝ)) - f (q : ℝ) = f (r : ℝ) - b := by
          have := hshift r (q : ℝ)
          simpa using this
        have h2 : f ((q + r : ℚ) : ℝ) = f ((q : ℝ) + (r : ℝ)) := by
          congr 1; push_cast; ring
        rw [hc_def]
        simp only
        rw [h2]
        linarith
      -- Homogeneity over ℕ: c (n * q) = n * c q.
      have hc_nsmul : ∀ (n : ℕ) (q : ℚ), c (n * q) = n * c q := by
        intro n q
        induction n with
        | zero => simp [hc_zero]
        | succ k ih =>
          have : ((k + 1 : ℕ) : ℚ) * q = (k : ℚ) * q + q := by push_cast; ring
          rw [this, hc_add, ih]
          push_cast; ring
      -- c is odd: c (-q) = - c q. Use c(q) + c(-q) = c(0) = 0.
      have hc_neg : ∀ q : ℚ, c (-q) = - c q := by
        intro q
        have : c q + c (-q) = c (q + -q) := (hc_add q (-q)).symm
        rw [add_neg_cancel] at this
        rw [hc_zero] at this
        linarith
      -- Homogeneity over ℤ: c (n * q) = n * c q.
      have hc_zsmul : ∀ (n : ℤ) (q : ℚ), c (n * q) = n * c q := by
        intro n q
        rcases n with n | n
        · -- n = Int.ofNat n (i.e., ≥ 0)
          have hcast : ((Int.ofNat n : ℤ) : ℚ) = (n : ℚ) := by norm_cast
          have hcastR : ((Int.ofNat n : ℤ) : ℝ) = (n : ℝ) := by norm_cast
          rw [hcast, hcastR, hc_nsmul]
        · -- n = Int.negSucc n (i.e., < 0)
          have hcast : ((Int.negSucc n : ℤ) : ℚ) = -((n + 1 : ℕ) : ℚ) := by
            push_cast; ring
          have hcastR : ((Int.negSucc n : ℤ) : ℝ) = -((n + 1 : ℕ) : ℝ) := by
            push_cast; ring
          rw [hcast, hcastR]
          rw [show (-((n + 1 : ℕ) : ℚ)) * q = -(((n + 1 : ℕ) : ℚ) * q) from by ring]
          rw [hc_neg, hc_nsmul]
          push_cast; ring
      -- Now: for q = num/den with den > 0: den * (c q) = c (den * q) = c num = num * c 1 = num * a.
      -- Hence c q = (num / den) * a = q * a.
      intro q
      show c q = q * a
      have hden : (q.den : ℝ) ≠ 0 := by
        exact_mod_cast q.pos.ne'
      have hden_q : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.pos.ne'
      -- ((q.den : ℤ) : ℚ) * q = q.num as rationals.
      have hmul : ((q.den : ℤ) : ℚ) * q = q.num := by
        rw [show ((q.den : ℤ) : ℚ) = (q.den : ℚ) from by push_cast; rfl]
        rw [mul_comm]
        exact_mod_cast Rat.mul_den_eq_num q
      have h1 : c (((q.den : ℤ) : ℚ) * q) = (q.den : ℝ) * c q := by
        rw [hc_zsmul]
        push_cast; ring
      have h2 : c (((q.num : ℤ) : ℚ) * 1) = (q.num : ℝ) * c 1 := hc_zsmul q.num 1
      have h3 : (q.num : ℝ) * c 1 = (q.num : ℝ) * a := by rw [hc_one]
      -- Combine: (q.den : ℝ) * c q = c (q.den * q) = c q.num = q.num * c 1 = q.num * a.
      have h4 : (q.den : ℝ) * c q = (q.num : ℝ) * a := by
        rw [← h1, hmul]
        rw [show ((q.num : ℤ) : ℚ) = ((q.num : ℤ) : ℚ) * 1 from by ring]
        rw [h2, h3]
      -- q as real = q.num / q.den.
      have hqreal : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
        rw [Rat.cast_def]
      -- Divide both sides of h4 by q.den.
      have hden_pos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
      field_simp
      rw [hqreal]
      field_simp
      linarith
    -- Step 3: Now define h(x) = f(x) - a*x - b. Then h is continuous,
    -- h(q) = 0 for all q ∈ ℚ, and by density + continuity, h ≡ 0.
    have hf_eq : ∀ x : ℝ, f x = (a : ℝ) * x + b := by
      -- Define h(x) = f(x) - a*x - b and show h ≡ 0.
      set h : ℝ → ℝ := fun x => f x - (a : ℝ) * x - b with hh_def
      have hh_cont : Continuous h := by
        exact (hcont.sub (continuous_const.mul continuous_id)).sub continuous_const
      -- h(q) = 0 for q : ℚ.
      have hh_rat : ∀ q : ℚ, h (q : ℝ) = 0 := by
        intro q
        have := hcq q
        simp [hh_def]
        linarith
      -- By density of ℚ in ℝ and continuity of h, h ≡ 0.
      intro x
      have hden : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
      -- Use uniqueness of continuous functions agreeing on a dense set.
      have heq : h = fun _ : ℝ => (0 : ℝ) := by
        apply hden.equalizer hh_cont continuous_const
        funext q
        exact hh_rat q
      have h0 : h x = 0 := congr_fun heq x
      -- Unfold h.
      have : f x - (a : ℝ) * x - b = 0 := h0
      linarith
    refine ⟨a, b, ?_⟩
    funext x
    exact hf_eq x
  · rintro ⟨a, b, rfl⟩ x y ⟨q, hq⟩
    refine ⟨a * q, ?_⟩
    have hxy : x - y = (q : ℝ) := hq
    have : (a : ℝ) * x + b - ((a : ℝ) * y + b) = (a : ℝ) * (x - y) := by ring
    rw [this, hxy]
    push_cast; ring

end Imc2008P1
