/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 9 (Day 2 Problem 3)

Let `f : ℝ → ℝ` have `n + 1` derivatives on `ℝ`. For `a < b` with
`ln((Σ_{k≤n} f^{(k)}(b)) / (Σ_{k≤n} f^{(k)}(a))) = b - a`,
there exists `c ∈ (a, b)` with `f^{(n+1)}(c) = f(c)`.

## Proof outline

Set `S(x) = Σ_{k=0}^n f^{(k)}(x)` and `g(x) = S(x) · e^{-x}`. The hypothesis
becomes `g(a) = g(b)`. Since `S'(x) = Σ_{k=1}^{n+1} f^{(k)}(x)
  = S(x) - f(x) + f^{(n+1)}(x)`, we have
`g'(x) = (S'(x) - S(x)) e^{-x} = (f^{(n+1)}(x) - f(x)) e^{-x}`.
Rolle's theorem applied to `g` on `[a, b]` produces `c ∈ (a, b)` with
`g'(c) = 0`, hence `f^{(n+1)}(c) = f(c)`.

Following the IMC's textbook formulation, the hypothesis is stated using
`Real.log`. To make the log equation usable we additionally assume
`0 < S(a)` and `0 < S(b)`; these are implicit in the original statement
since the log is meant in the usual real-valued sense.
-/

namespace Imc1994P9

open Set Finset

/-- Partial sum `S(x) = Σ_{k=0}^n f^{(k)}(x)`. -/
noncomputable def S (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), iteratedDeriv k f x

snip begin

/-- Each iterated derivative (up to order `n`) of a `C^{n+1}` function is
differentiable. -/
lemma differentiable_iteratedDeriv_of_contDiff
    {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (n + 1) f) (k : ℕ) (hk : k ≤ n) :
    Differentiable ℝ (iteratedDeriv k f) := by
  have hkn : (k : ℕ∞) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le hk
  exact hf.differentiable_iteratedDeriv k (by exact_mod_cast hkn)

/-- `S n f` is differentiable everywhere (when `f` is `C^{n+1}`),
and its derivative is `Σ_{k=0}^{n} f^{(k+1)}`. -/
lemma hasDerivAt_S {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (n + 1) f) (x : ℝ) :
    HasDerivAt (S n f) (∑ k ∈ range (n + 1), iteratedDeriv (k + 1) f x) x := by
  unfold S
  have h_each : ∀ k ∈ range (n + 1),
      HasDerivAt (fun y => iteratedDeriv k f y) (iteratedDeriv (k + 1) f x) x := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hdiff : Differentiable ℝ (iteratedDeriv k f) :=
      differentiable_iteratedDeriv_of_contDiff hf k hk'
    have h1 : HasDerivAt (iteratedDeriv k f) (deriv (iteratedDeriv k f) x) x :=
      (hdiff x).hasDerivAt
    have heq : deriv (iteratedDeriv k f) = iteratedDeriv (k + 1) f := by
      rw [← iteratedDeriv_succ]
    rw [heq] at h1
    exact h1
  exact HasDerivAt.fun_sum h_each

/-- Telescoping identity:
`Σ_{k=0}^n f^{(k+1)}(x) - Σ_{k=0}^n f^{(k)}(x) = f^{(n+1)}(x) - f(x)`. -/
lemma telescope_sum_iteratedDeriv (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (∑ k ∈ range (n + 1), iteratedDeriv (k + 1) f x) -
        (∑ k ∈ range (n + 1), iteratedDeriv k f x)
      = iteratedDeriv (n + 1) f x - iteratedDeriv 0 f x := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ (f := fun k => iteratedDeriv (k + 1) f x) (n := m + 1),
          sum_range_succ (f := fun k => iteratedDeriv k f x) (n := m + 1)]
      linarith [ih]

snip end

problem imc1994_p9 (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (n + 1) f)
    (a b : ℝ) (hab : a < b)
    (hSa : 0 < S n f a) (hSb : 0 < S n f b)
    (hlog : Real.log (S n f b / S n f a) = b - a) :
    ∃ c ∈ Ioo a b, iteratedDeriv (n + 1) f c = f c := by
  -- From the log hypothesis, deduce `S n f b = S n f a * exp (b - a)`.
  have hratio_pos : 0 < S n f b / S n f a := div_pos hSb hSa
  have hSa_ne : S n f a ≠ 0 := ne_of_gt hSa
  have hexp : S n f b / S n f a = Real.exp (b - a) := by
    have := Real.exp_log hratio_pos
    rw [hlog] at this; exact this.symm
  have hSb_eq : S n f b = S n f a * Real.exp (b - a) := by
    have : S n f b / S n f a * S n f a = Real.exp (b - a) * S n f a := by
      rw [hexp]
    rw [div_mul_cancel₀ _ hSa_ne] at this
    linarith
  -- Define g(x) := S n f x * exp(-x); the hypothesis becomes g a = g b.
  set g : ℝ → ℝ := fun x => S n f x * Real.exp (-x) with hg_def
  have hga_eq_gb : g a = g b := by
    simp only [g, hSb_eq]
    have hexp_split : Real.exp (b - a) * Real.exp (-b) = Real.exp (-a) := by
      rw [← Real.exp_add]; ring_nf
    calc S n f a * Real.exp (-a)
        = S n f a * (Real.exp (b - a) * Real.exp (-b)) := by rw [hexp_split]
      _ = S n f a * Real.exp (b - a) * Real.exp (-b) := by ring
  -- Compute g'(x) = (f^{(n+1)} x - f x) * exp(-x).
  have hg_deriv : ∀ x, HasDerivAt g
      ((iteratedDeriv (n + 1) f x - f x) * Real.exp (-x)) x := by
    intro x
    have hS' := hasDerivAt_S hf x
    have hexp_deriv : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h1 : HasDerivAt (fun x : ℝ => -x) (-1) x := (hasDerivAt_id x).neg
      have := h1.exp
      convert this using 1
      ring
    have hmul := hS'.mul hexp_deriv
    -- The product rule yields the derivative
    --   (Σ_{k=0}^n f^{(k+1)} x) * exp(-x) + S n f x * (-exp(-x))
    -- which equals (f^{(n+1)} x - f x) * exp(-x) by telescoping.
    have htele := telescope_sum_iteratedDeriv n f x
    have hf0 : iteratedDeriv 0 f x = f x := by simp [iteratedDeriv_zero]
    have hsub : (∑ k ∈ range (n + 1), iteratedDeriv (k + 1) f x) - S n f x
        = iteratedDeriv (n + 1) f x - f x := by
      unfold S; rw [← hf0]; exact htele
    have hgoal :
        (∑ k ∈ range (n + 1), iteratedDeriv (k + 1) f x) * Real.exp (-x)
          + S n f x * (-Real.exp (-x))
        = (iteratedDeriv (n + 1) f x - f x) * Real.exp (-x) := by
      have : (∑ k ∈ range (n + 1), iteratedDeriv (k + 1) f x) * Real.exp (-x)
          + S n f x * (-Real.exp (-x))
          = ((∑ k ∈ range (n + 1), iteratedDeriv (k + 1) f x) - S n f x)
              * Real.exp (-x) := by ring
      rw [this, hsub]
    rw [← hgoal]
    exact hmul
  -- Apply Rolle's theorem to g on [a, b].
  have hg_cont : ContinuousOn g (Icc a b) := by
    intro x _; exact (hg_deriv x).continuousAt.continuousWithinAt
  have hg_ioo : ∀ x ∈ Ioo a b, HasDerivAt g
      ((iteratedDeriv (n + 1) f x - f x) * Real.exp (-x)) x :=
    fun x _ => hg_deriv x
  obtain ⟨c, hc, hgc⟩ :=
    exists_hasDerivAt_eq_zero hab hg_cont hga_eq_gb hg_ioo
  refine ⟨c, hc, ?_⟩
  have hexp_pos : 0 < Real.exp (-c) := Real.exp_pos _
  have hexp_ne : Real.exp (-c) ≠ 0 := ne_of_gt hexp_pos
  have h1 : iteratedDeriv (n + 1) f c - f c = 0 := by
    have := mul_eq_zero.mp hgc
    rcases this with h | h
    · exact h
    · exact absurd h hexp_ne
  linarith

end Imc1994P9
