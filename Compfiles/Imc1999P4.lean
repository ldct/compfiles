/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1999, Problem 4 (Day 1)

Find all strictly monotonic functions `f : (0, ∞) → (0, ∞)` satisfying
`f(x² / f(x)) = x` for all `x > 0`.

The answer is: `f(x) = C · x` for some constant `C > 0`.

## Solution sketch

A strictly monotonic `f` is injective. From `f(x² / f(x)) = x`, applying the
substitution `x → f x` and using injectivity yields `f(f(x)) = f(x)² / x`.
By induction `f^[n](x) = x · g(x)^n`, where `g(x) := f(x)/x`.

If `f` is strictly *decreasing*, then `x ↦ x²/f(x)` is strictly increasing
(both `x²` increases and `1/f(x)` increases, as `f(x)` decreases), so
`f(x²/f(x))` is strictly decreasing. But it equals `x`, which is strictly
increasing — contradiction. So `f` is strictly increasing.

Strict monotonicity of `f^[n]` gives `g(x) ≤ g(y)` for `x ≤ y` (let `n → ∞`),
and the corresponding fact for the inverse iteration gives `g(x) ≥ g(y)`.
Therefore `g` is constant, i.e. `f(x) = C·x`.
-/

namespace Imc1999P4

open Function

/-- Predicate: `f : ℝ → ℝ` (treated as a function on `(0,∞)`) is strictly
monotonic on the positive reals, sends positives to positives, and satisfies
`f(x² / f(x)) = x` for all `x > 0`. -/
def IsSolution (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → 0 < f x) ∧
  ((∀ ⦃a b⦄, 0 < a → a < b → f a < f b) ∨
   (∀ ⦃a b⦄, 0 < a → a < b → f b < f a)) ∧
  (∀ x, 0 < x → f (x^2 / f x) = x)

/-- The forward direction of IMC 1999 P4: every solution is of the form `f(x) = C·x`
for some `C > 0`. -/
problem imc1999_p4_forward
    (f : ℝ → ℝ) (hf : IsSolution f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 0 < x → f x = C * x := by
  obtain ⟨hpos, hmono, heq⟩ := hf
  -- Step 1: rule out the strictly decreasing case.
  have hmono_inc : ∀ ⦃a b⦄, 0 < a → a < b → f a < f b := by
    rcases hmono with hinc | hdec
    · exact hinc
    · exfalso
      -- For any 0 < a < b, a²/f(a) < b²/f(b), so f(a²/f(a)) > f(b²/f(b)) by hdec,
      -- i.e. a > b — contradiction.
      have key : ∀ a b : ℝ, 0 < a → a < b → a^2 / f a < b^2 / f b := by
        intro a b ha hab
        have hb : 0 < b := lt_trans ha hab
        have hfa : 0 < f a := hpos a ha
        have hfb : 0 < f b := hpos b hb
        have hfab : f b < f a := hdec ha hab
        have h1 : a^2 < b^2 := by nlinarith
        have hinvineq : 1/f a < 1/f b := by
          rw [div_lt_div_iff₀ hfa hfb]; linarith
        have hb2 : 0 < b^2 := by positivity
        have ha2 : 0 ≤ a^2 := sq_nonneg a
        have hifa : 0 < 1/f a := by positivity
        calc a^2 / f a = a^2 * (1/f a) := by ring
          _ ≤ b^2 * (1/f a) :=
              mul_le_mul_of_nonneg_right (le_of_lt h1) (le_of_lt hifa)
          _ < b^2 * (1/f b) := mul_lt_mul_of_pos_left hinvineq hb2
          _ = b^2 / f b := by ring
      -- Now apply at a = 1, b = 2.
      have h12 : (1:ℝ)^2 / f 1 < 2^2 / f 2 := key 1 2 one_pos (by norm_num)
      have hpos1 : 0 < (1:ℝ)^2 / f 1 := by
        have : 0 < f 1 := hpos 1 one_pos; positivity
      have hpos2 : 0 < (2:ℝ)^2 / f 2 := by
        have : 0 < f 2 := hpos 2 (by norm_num); positivity
      have hf1 : f ((1:ℝ)^2 / f 1) = 1 := heq 1 one_pos
      have hf2 : f ((2:ℝ)^2 / f 2) = 2 := heq 2 (by norm_num)
      have : f ((2:ℝ)^2 / f 2) < f ((1:ℝ)^2 / f 1) := hdec hpos1 h12
      rw [hf1, hf2] at this
      linarith
  -- Step 2: f is injective on positives.
  have hinj : ∀ ⦃a b⦄, 0 < a → 0 < b → f a = f b → a = b := by
    intro a b ha hb hfab
    rcases lt_trichotomy a b with hlt | heq2 | hgt
    · exact absurd hfab (ne_of_lt (hmono_inc ha hlt))
    · exact heq2
    · exact absurd hfab.symm (ne_of_lt (hmono_inc hb hgt))
  -- Step 3: f(f(x)) = f(x)^2 / x.
  have hff : ∀ x, 0 < x → f (f x) = (f x)^2 / x := by
    intro x hx
    have hfx : 0 < f x := hpos x hx
    have hffx : 0 < f (f x) := hpos _ hfx
    -- Apply heq at f x:
    have h1 : f ((f x)^2 / f (f x)) = f x := heq (f x) hfx
    -- Both `(f x)^2 / f(f x)` and `x` are preimages of `f x` under `f`
    -- (the latter by definition). By injectivity they coincide.
    have hpfx : 0 < (f x)^2 / f (f x) := by positivity
    have h2 : (f x)^2 / f (f x) = x := hinj hpfx hx h1
    -- Hence f(f x) * x = (f x)^2.
    have hxne : x ≠ 0 := ne_of_gt hx
    have hffxne : f (f x) ≠ 0 := ne_of_gt hffx
    have hsq : (f x)^2 = x * f (f x) := by
      have := h2
      field_simp at this
      linarith
    rw [eq_div_iff hxne]
    linarith
  -- Step 4: by induction, f^[n](x) = x * (f x / x)^n.
  -- We define g x := f x / x, then f^[n] x = x * g x ^ n on positives.
  -- We show this leads to: g(f x) = g x, and combined with strict monotonicity
  -- in n, g is constant.
  -- Define g.
  set g : ℝ → ℝ := fun x => f x / x with hg_def
  have hg_pos : ∀ x, 0 < x → 0 < g x := by
    intro x hx
    have : 0 < f x := hpos x hx
    simp only [hg_def]; positivity
  -- Key relation g(f x) = g x:
  have hg_inv : ∀ x, 0 < x → g (f x) = g x := by
    intro x hx
    have hfx := hpos x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hfxne : f x ≠ 0 := ne_of_gt hfx
    simp only [hg_def]
    rw [hff x hx]
    field_simp
  -- Step 5: The iteration claim. Define a_n = f^[n] x for x > 0.
  -- We prove by induction f^[n] x = x * (g x)^n.
  have hiter : ∀ n : ℕ, ∀ x, 0 < x → f^[n] x = x * (g x)^n := by
    intro n
    induction n with
    | zero => intro x hx; simp
    | succ n ih =>
      intro x hx
      -- f^[n+1] x = f^[n] (f x) = (f x) * (g (f x))^n = (f x) * (g x)^n by hg_inv
      rw [iterate_succ_apply f n x, ih (f x) (hpos x hx), hg_inv x hx]
      -- now (f x) * g x ^ n = x * g x ^ (n+1)
      have hxne : (x:ℝ) ≠ 0 := ne_of_gt hx
      have hgx_eq : g x = f x / x := by simp only [hg_def]
      rw [hgx_eq, pow_succ]
      field_simp
  -- Step 6: Iterate of f preserves strict monotonicity (on positives).
  -- For n iterations: x ≤ y, both positive, gives f^[n] x ≤ f^[n] y.
  have h_iter_pos : ∀ n : ℕ, ∀ x, 0 < x → 0 < f^[n] x := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [iterate_succ', comp_apply]
      exact hpos _ (ih x hx)
  have h_iter_mono : ∀ n : ℕ, ∀ ⦃a b⦄, 0 < a → a < b → f^[n] a < f^[n] b := by
    intro n
    induction n with
    | zero => intro a b ha hab; simpa using hab
    | succ n ih =>
      intro a b ha hab
      rw [iterate_succ_apply' f n a, iterate_succ_apply' f n b]
      exact hmono_inc (h_iter_pos n a ha) (ih ha hab)
  -- Step 7: g is monotone non-decreasing (on positives).
  -- For 0 < a ≤ b: a * (g a)^n ≤ b * (g b)^n for all n. If g a > g b, then for large n,
  -- LHS dominates, contradiction.
  have hg_mono : ∀ ⦃a b⦄, 0 < a → a ≤ b → g a ≤ g b := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    have hb : 0 < b := lt_trans ha hlt
    have hga := hg_pos a ha
    have hgb := hg_pos b hb
    -- Suppose g b < g a. We derive a contradiction.
    by_contra hcontra
    push Not at hcontra
    -- hcontra : g b < g a
    -- We have for all n: f^[n] a < f^[n] b, i.e., a * (g a)^n < b * (g b)^n.
    have hineq : ∀ n : ℕ, a * (g a)^n < b * (g b)^n := by
      intro n
      have := h_iter_mono n ha hlt
      rw [hiter n a ha, hiter n b hb] at this
      exact this
    -- Rearranging: (g a / g b)^n < b / a. Take n large enough — contradiction since g a / g b > 1.
    have hr : 1 < g a / g b := by
      rw [lt_div_iff₀ hgb]; linarith
    have hba_pos : 0 < b / a := div_pos hb ha
    -- From a * (g a)^n < b * (g b)^n and g b > 0, we get (g a / g b)^n < b / a.
    have hineq2 : ∀ n : ℕ, (g a / g b)^n < b / a := by
      intro n
      have h := hineq n
      have hgbn_pos : 0 < (g b)^n := pow_pos hgb n
      have hgan_pos : 0 < (g a)^n := pow_pos hga n
      rw [div_pow]
      rw [div_lt_div_iff₀ hgbn_pos ha]
      have : a * (g a)^n < b * (g b)^n := h
      linarith
    -- But (g a / g b)^n → ∞ since g a / g b > 1.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, b / a < (g a / g b) ^ N := by
      have := pow_unbounded_of_one_lt (b / a) hr
      exact this
    exact absurd (hineq2 N) (not_lt.mpr (le_of_lt hN))
  -- Step 8: g is also monotone non-increasing.
  -- This uses the inverse iteration: from f^[n] (x²/f x) = ..., specifically
  -- the function h(x) = x²/f(x) iterates as h^[n](x) = x / (g x)^n along orbits.
  -- We use: h is strictly increasing (since f is) and equals f^{-1}, so for
  -- 0 < a < b, h^[n](a) < h^[n](b), i.e. a/(g a)^n < b/(g b)^n. If g a < g b
  -- strictly, take n large to get contradiction.
  -- Define h.
  set h : ℝ → ℝ := fun x => x^2 / f x with hh_def
  have hh_pos : ∀ x, 0 < x → 0 < h x := by
    intro x hx; have : 0 < f x := hpos x hx; simp only [hh_def]; positivity
  -- f ∘ h = id on positives, by heq.
  have hfh : ∀ x, 0 < x → f (h x) = x := by
    intro x hx; simpa [hh_def] using heq x hx
  -- h is strictly increasing on positives. Proof: from x < y, suppose h x ≥ h y;
  -- then since f is increasing on positives, f (h x) ≥ f (h y), so x ≥ y, contradiction.
  have hh_mono : ∀ ⦃a b⦄, 0 < a → a < b → h a < h b := by
    intro a b ha hab
    have hb : 0 < b := lt_trans ha hab
    have hfha : f (h a) = a := hfh a ha
    have hfhb : f (h b) = b := hfh b hb
    by_contra hcontra
    push Not at hcontra
    -- hcontra : h b ≤ h a
    rcases eq_or_lt_of_le hcontra with heq2 | hlt
    · -- h b = h a → applying f: b = a, contradicting a < b.
      have hbeq : f (h b) = f (h a) := by rw [heq2]
      rw [hfhb, hfha] at hbeq
      -- hbeq : b = a; but a < b
      exact absurd hbeq (ne_of_gt hab)
    · -- h b < h a → f (h b) < f (h a), i.e., b < a, contradicting a < b.
      have hhb_pos : 0 < h b := hh_pos b hb
      have hhf := hmono_inc hhb_pos hlt
      rw [hfha, hfhb] at hhf
      exact absurd hhf (asymm hab)
  -- h iterates: h^[n] x = x / (g x)^n.
  have h_hiter : ∀ n : ℕ, ∀ x, 0 < x → h^[n] x = x / (g x)^n := by
    intro n x hx
    -- f∘h = id on positives, so f^[n] (h^[n] x) = x.
    -- Set y = h^[n] x. Then f^[n] y = x = y * (g y)^n, so y = x / (g y)^n.
    -- Need to show g y = g x: g is constant along orbits (g(f x) = g x).
    -- We have y = h^[n] x, and we want g (h^[n] x) = g x.
    -- Inductively: g (h x) = g x, since f (h x) = x, so g x = g (f (h x)) = g (h x)
    -- by hg_inv applied at h x.
    -- Then g (h^[n] x) = g x by induction.
    have h_hiter_pos : ∀ n : ℕ, 0 < h^[n] x := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        rw [iterate_succ', comp_apply]
        exact hh_pos _ ih
    have hg_along_h : ∀ n : ℕ, g (h^[n] x) = g x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [iterate_succ', comp_apply]
        -- g (h (h^[n] x)) = g (f (h (h^[n] x))) = g (h^[n] x) = g x
        have := hg_inv (h (h^[n] x)) (hh_pos _ (h_hiter_pos n))
        rw [hfh (h^[n] x) (h_hiter_pos n)] at this
        rw [← this]
        exact ih
    -- Now: f^[n] (h^[n] x) = x.
    have hcomp : f^[n] (h^[n] x) = x := by
      induction n with
      | zero => simp
      | succ n ih =>
        -- f^[n+1] (h^[n+1] x) = f^[n] (f (h^[n+1] x))
        --                     = f^[n] (f (h (h^[n] x)))
        --                     = f^[n] (h^[n] x) = x.
        have e1 : f^[n+1] (h^[n+1] x) = f^[n] (f (h^[n+1] x)) :=
          iterate_succ_apply f n (h^[n+1] x)
        have e2 : h^[n+1] x = h (h^[n] x) := iterate_succ_apply' h n x
        rw [e1, e2, hfh _ (h_hiter_pos n), ih]
    -- And f^[n] (h^[n] x) = (h^[n] x) * (g (h^[n] x))^n = (h^[n] x) * (g x)^n.
    have hcomp2 : f^[n] (h^[n] x) = h^[n] x * (g x)^n := by
      rw [hiter n (h^[n] x) (h_hiter_pos n), hg_along_h n]
    rw [hcomp2] at hcomp
    -- (h^[n] x) * (g x)^n = x  ⇒ h^[n] x = x / (g x)^n.
    have hgx_pos : 0 < (g x)^n := pow_pos (hg_pos x hx) n
    rw [eq_div_iff (ne_of_gt hgx_pos)]
    linarith
  -- h is monotone too — its iterates therefore preserve strict order.
  -- First: h^[n] x > 0 for x > 0.
  have h_hiter_pos_all : ∀ n : ℕ, ∀ x, 0 < x → 0 < h^[n] x := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [iterate_succ_apply']
      exact hh_pos _ (ih x hx)
  have h_hiter_mono : ∀ n : ℕ, ∀ ⦃a b⦄, 0 < a → a < b → h^[n] a < h^[n] b := by
    intro n
    induction n with
    | zero => intro a b ha hab; simpa using hab
    | succ n ih =>
      intro a b ha hab
      rw [iterate_succ_apply' h n a, iterate_succ_apply' h n b]
      exact hh_mono (h_hiter_pos_all n a ha) (ih ha hab)
  -- Step 9: g is non-increasing (i.e., g a ≥ g b for a ≤ b).
  have hg_anti : ∀ ⦃a b⦄, 0 < a → a ≤ b → g b ≤ g a := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    have hb : 0 < b := lt_trans ha hlt
    have hga := hg_pos a ha
    have hgb := hg_pos b hb
    by_contra hcontra
    push Not at hcontra
    -- hcontra : g a < g b
    -- For all n: a/(g a)^n < b/(g b)^n. Multiplying out: a * (g b)^n < b * (g a)^n.
    -- Equivalently (g b / g a)^n < b/a. But g b / g a > 1, contradiction for large n.
    have hineq : ∀ n : ℕ, h^[n] a < h^[n] b := fun n => h_hiter_mono n ha hlt
    have hineq2 : ∀ n : ℕ, a / (g a)^n < b / (g b)^n := by
      intro n
      have := hineq n
      rwa [h_hiter n a ha, h_hiter n b hb] at this
    have hr : 1 < g b / g a := by rw [lt_div_iff₀ hga]; linarith
    have hineq3 : ∀ n : ℕ, (g b / g a)^n < b / a := by
      intro n
      have hh1 := hineq2 n
      have hgan_pos : 0 < (g a)^n := pow_pos hga n
      have hgbn_pos : 0 < (g b)^n := pow_pos hgb n
      -- a / (g a)^n < b / (g b)^n means a * (g b)^n < b * (g a)^n.
      have hh' : a * (g b)^n < b * (g a)^n := by
        rw [div_lt_div_iff₀ hgan_pos hgbn_pos] at hh1
        linarith
      rw [div_pow]
      rw [div_lt_div_iff₀ hgan_pos ha]
      linarith
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (b/a) hr
    exact absurd (hineq3 N) (not_lt.mpr (le_of_lt hN))
  -- Step 10: combining hg_mono and hg_anti, g is constant on positives.
  have hg_const : ∀ ⦃a b⦄, 0 < a → 0 < b → g a = g b := by
    intro a b ha hb
    rcases le_total a b with h1 | h1
    · exact le_antisymm (hg_mono ha h1) (hg_anti ha h1)
    · exact le_antisymm (hg_mono hb h1) (hg_anti hb h1) |>.symm
  -- Step 11: conclude.
  refine ⟨g 1, hg_pos 1 one_pos, ?_⟩
  intro x hx
  have hgx : g x = g 1 := hg_const hx one_pos
  -- g x = g 1, i.e., f x / x = g 1, so f x = (g 1) * x.
  have hxne : x ≠ 0 := ne_of_gt hx
  have : f x / x = g 1 := by simp only [hg_def] at hgx; exact hgx
  field_simp at this
  linarith

/-- Conversely, every `f(x) = C·x` with `C > 0` satisfies the conditions. -/
problem imc1999_p4_backward
    (C : ℝ) (hC : 0 < C) :
    IsSolution (fun x => C * x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; positivity
  · left
    intro a b _ hab
    exact mul_lt_mul_of_pos_left hab hC
  · intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hCne : C ≠ 0 := ne_of_gt hC
    show C * (x^2 / (C * x)) = x
    field_simp

end Imc1999P4
