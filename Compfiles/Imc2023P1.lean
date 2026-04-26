/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2023, Problem 1

Find all functions `f : ℝ → ℝ` that have a continuous second derivative and
for which `f(7x + 1) = 49 f(x)` holds for all `x ∈ ℝ`.

Answer: `f(x) = c (6x + 1)²` for some `c ∈ ℝ`.
-/

namespace Imc2023P1

/-- The set of solutions. -/
determine answer : Set (ℝ → ℝ) :=
  { f | ∃ c : ℝ, ∀ x, f x = c * (6 * x + 1) ^ 2 }

snip begin

/-- `f` has a derivative if `ContDiff ℝ 2`. -/
lemma hasDerivAt_of_contDiff2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  (hf.differentiable (by decide) x).hasDerivAt

/-- `deriv f` has a derivative if `ContDiff ℝ 2 f`. -/
lemma hasDerivAt_deriv_of_contDiff2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  (hf.differentiable_deriv_two x).hasDerivAt

/-- The iteration `x ↦ (x - 1) / 7` converges to `-1/6` from any start. -/
lemma iter_tendsto (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (fun y => (y - 1) / 7)^[n] x) Filter.atTop
      (nhds (-1/6 : ℝ)) := by
  -- Show (T^[n] x + 1/6) = (1/7)^n * (x + 1/6) where T y = (y-1)/7.
  set T : ℝ → ℝ := fun y => (y - 1) / 7 with hT_def
  have hT_iter : ∀ n : ℕ, T^[n] x + 1/6 = (1/7 : ℝ)^n * (x + 1/6) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply, hT_def, pow_succ]
        have : (T^[k] x - 1) / 7 + 1/6 = (1/7) * (T^[k] x + 1/6) := by ring
        rw [this, ih]; ring
  have hconv : Filter.Tendsto (fun n : ℕ => (1/7 : ℝ)^n * (x + 1/6)) Filter.atTop
      (nhds ((0 : ℝ) * (x + 1/6))) := by
    have hbase : Filter.Tendsto (fun n : ℕ => (1/7 : ℝ)^n) Filter.atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      · norm_num
      · norm_num
    exact hbase.mul_const _
  rw [zero_mul] at hconv
  have h_eq : (fun n : ℕ => T^[n] x) = fun n : ℕ => ((1/7 : ℝ)^n * (x + 1/6)) - 1/6 := by
    funext n
    have := hT_iter n
    linarith
  rw [h_eq]
  have := hconv.sub_const (1/6)
  have hneg : (0 : ℝ) - 1/6 = -1/6 := by norm_num
  rw [hneg] at this
  convert this using 2

/-- If `g : ℝ → ℝ` is continuous and `g((x-1)/7) = g(x)` for all `x`, then `g` is constant. -/
lemma const_of_functional {g : ℝ → ℝ} (hg : Continuous g)
    (heq : ∀ x, g ((x - 1) / 7) = g x) : ∀ x, g x = g (-1/6) := by
  intro x
  set T : ℝ → ℝ := fun y => (y - 1) / 7 with hT_def
  -- For all n, g (T^[n] x) = g x.
  have hn : ∀ n : ℕ, g (T^[n] x) = g x := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply]
        rw [show T (T^[k] x) = (T^[k] x - 1) / 7 from rfl]
        rw [heq (T^[k] x)]
        exact ih
  -- T^[n] x → -1/6, so by continuity g (T^[n] x) → g (-1/6).
  have htend : Filter.Tendsto (fun n : ℕ => g (T^[n] x)) Filter.atTop (nhds (g (-1/6))) := by
    exact (hg.tendsto _).comp (iter_tendsto x)
  -- But g (T^[n] x) = g x constantly.
  have hconst : (fun n : ℕ => g (T^[n] x)) = fun _ => g x := funext hn
  rw [hconst] at htend
  exact (tendsto_nhds_unique htend tendsto_const_nhds).symm

snip end

problem imc2023_p1 (f : ℝ → ℝ) (hf_cont_deriv : ContDiff ℝ 2 f) :
    f ∈ answer ↔ ∀ x : ℝ, f (7 * x + 1) = 49 * f x := by
  constructor
  · -- Forward: if f = c (6x+1)², verify functional equation.
    rintro ⟨c, hc⟩ x
    rw [hc (7 * x + 1), hc x]
    ring
  · -- Backward: from FE, derive f = c (6x+1)².
    intro hFE
    -- Let h(x) = f(7x+1). Then h'(x) = 7 f'(7x+1), h''(x) = 49 f''(7x+1).
    -- Also h(x) = 49 f(x), so h'(x) = 49 f'(x), h''(x) = 49 f''(x).
    -- Hence f''(7x+1) = f''(x).
    have hdiff_f : Differentiable ℝ f := hf_cont_deriv.differentiable (by decide)
    have hdiff_df : Differentiable ℝ (deriv f) := hf_cont_deriv.differentiable_deriv_two
    -- Derive FE for deriv f.
    have hFE' : ∀ x, deriv f (7 * x + 1) = 7 * deriv f x := by
      intro x
      -- Set h(x) = f(7x+1). HasDerivAt of h at x is 7 * f'(7x+1).
      have h_inner : HasDerivAt (fun x => 7 * x + 1) (7 : ℝ) x := by
        have h1 : HasDerivAt (fun x : ℝ => 7 * x) 7 x := by
          simpa using (hasDerivAt_id x).const_mul 7
        simpa using h1.add_const 1
      have h_outer_raw : HasDerivAt (f ∘ (fun x => 7 * x + 1))
          (deriv f (7 * x + 1) * 7) x :=
        (hasDerivAt_of_contDiff2 hf_cont_deriv (7 * x + 1)).comp x h_inner
      have h_outer : HasDerivAt (fun x => f (7 * x + 1)) (deriv f (7 * x + 1) * 7) x :=
        h_outer_raw
      -- Also h(x) = 49 f(x).
      have h_lin : HasDerivAt (fun x => 49 * f x) (49 * deriv f x) x :=
        (hasDerivAt_of_contDiff2 hf_cont_deriv x).const_mul 49
      have heq : (fun x => f (7 * x + 1)) = fun x => 49 * f x := funext hFE
      rw [heq] at h_outer
      have := h_outer.unique h_lin
      linarith
    -- Derive FE for deriv (deriv f).
    have hFE'' : ∀ x, deriv (deriv f) (7 * x + 1) = deriv (deriv f) x := by
      intro x
      have h_inner : HasDerivAt (fun x => 7 * x + 1) (7 : ℝ) x := by
        have h1 : HasDerivAt (fun x : ℝ => 7 * x) 7 x := by
          simpa using (hasDerivAt_id x).const_mul 7
        simpa using h1.add_const 1
      have h_outer_raw : HasDerivAt ((deriv f) ∘ (fun x => 7 * x + 1))
          (deriv (deriv f) (7 * x + 1) * 7) x :=
        (hasDerivAt_deriv_of_contDiff2 hf_cont_deriv (7 * x + 1)).comp x h_inner
      have h_outer : HasDerivAt (fun x => deriv f (7 * x + 1))
          (deriv (deriv f) (7 * x + 1) * 7) x := h_outer_raw
      have h_lin : HasDerivAt (fun x => 7 * deriv f x) (7 * deriv (deriv f) x) x :=
        (hasDerivAt_deriv_of_contDiff2 hf_cont_deriv x).const_mul 7
      have heq : (fun x => deriv f (7 * x + 1)) = fun x => 7 * deriv f x := funext hFE'
      rw [heq] at h_outer
      have := h_outer.unique h_lin
      linarith
    -- Rewrite as g((x-1)/7) = g(x).
    have hFE''_inv : ∀ x, deriv (deriv f) ((x - 1) / 7) = deriv (deriv f) x := by
      intro x
      have := hFE'' ((x - 1) / 7)
      have h7 : (7 : ℝ) * ((x - 1) / 7) + 1 = x := by ring
      rw [h7] at this
      exact this.symm
    -- Continuity of deriv (deriv f).
    have hcont_ddf : Continuous (deriv (deriv f)) := by
      have h := hf_cont_deriv.continuous_iteratedDeriv 2 (by exact_mod_cast (le_refl 2))
      have heq : iteratedDeriv 2 f = deriv (deriv f) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [heq] at h
      exact h
    -- f'' is constant, equal to f''(-1/6).
    set A : ℝ := deriv (deriv f) (-1/6) with hA_def
    have hf''_const : ∀ x, deriv (deriv f) x = A :=
      const_of_functional hcont_ddf hFE''_inv
    -- Now deriv f - A * x has zero derivative, so it's constant.
    set B : ℝ := deriv f 0 with hB_def
    have hdf_eq : ∀ x, deriv f x = A * x + B := by
      -- Let h(x) = deriv f x - A * x. Then h' = 0.
      have hderiv : ∀ x, HasDerivAt (fun y => deriv f y - A * y) 0 x := by
        intro x
        have h1 : HasDerivAt (deriv f) A x := by
          have := hasDerivAt_deriv_of_contDiff2 hf_cont_deriv x
          rw [hf''_const x] at this
          exact this
        have h2 : HasDerivAt (fun y : ℝ => A * y) A x := by
          simpa using (hasDerivAt_id x).const_mul A
        have := h1.sub h2
        simpa using this
      -- A function with zero derivative is constant.
      have hconst : ∀ x, (fun y => deriv f y - A * y) x = (fun y => deriv f y - A * y) 0 := by
        intro x
        have := is_const_of_deriv_eq_zero (f := fun y => deriv f y - A * y)
          (fun y => (hderiv y).differentiableAt)
          (fun y => (hderiv y).deriv) x 0
        exact this
      intro x
      have := hconst x
      simp at this
      linarith
    -- Now define C = f 0. Then f x = (A/2) x² + B x + C.
    set C : ℝ := f 0 with hC_def
    have hf_eq : ∀ x, f x = (A/2) * x^2 + B * x + C := by
      -- Let h(x) = f x - ((A/2) x² + B x). Then h'(x) = f'(x) - (A x + B) = 0.
      have hderiv : ∀ x, HasDerivAt (fun y => f y - ((A/2) * y^2 + B * y)) 0 x := by
        intro x
        have h1 : HasDerivAt f (deriv f x) x := hasDerivAt_of_contDiff2 hf_cont_deriv x
        have hx2 : HasDerivAt (fun y : ℝ => y^2) (2 * x ^ 1) x := by
          simpa using hasDerivAt_pow 2 x
        have hA2x2 : HasDerivAt (fun y : ℝ => (A/2) * y^2) ((A/2) * (2 * x^1)) x :=
          hx2.const_mul (A/2)
        have hBx : HasDerivAt (fun y : ℝ => B * y) B x := by
          simpa using (hasDerivAt_id x).const_mul B
        have hsum : HasDerivAt (fun y : ℝ => (A/2) * y^2 + B * y) ((A/2) * (2 * x^1) + B) x :=
          hA2x2.add hBx
        have hdiff := h1.sub hsum
        have hrw : deriv f x - ((A/2) * (2 * x^1) + B) = 0 := by
          rw [hdf_eq x]; ring
        rw [hrw] at hdiff
        exact hdiff
      have hconst : ∀ x, (fun y => f y - ((A/2) * y^2 + B * y)) x =
          (fun y => f y - ((A/2) * y^2 + B * y)) 0 := by
        intro x
        exact is_const_of_deriv_eq_zero (f := fun y => f y - ((A/2) * y^2 + B * y))
          (fun y => (hderiv y).differentiableAt)
          (fun y => (hderiv y).deriv) x 0
      intro x
      have := hconst x
      simp at this
      linarith
    -- Now match coefficients: f(7x+1) = 49 f(x) for all x.
    -- LHS = (A/2)(7x+1)² + B(7x+1) + C.
    -- RHS = 49 ((A/2) x² + B x + C).
    -- Expanding LHS - RHS = 0 gives polynomial identity in x, so coefficients vanish.
    have hABC : A = 72 * C ∧ B = 12 * C := by
      -- Use FE at x = 0: f(1) = 49 f(0).
      -- LHS: A/2 + B + C, RHS: 49 C. So A/2 + B = 48 C.
      have h0 : (A/2) + B + C = 49 * C := by
        have h1 : f (7 * 0 + 1) = 49 * f 0 := hFE 0
        have : f 1 = 49 * f 0 := by simpa using h1
        rw [hf_eq 1, hf_eq 0] at this
        linarith
      -- FE at x = -1/6: f(-1/6) = 49 f(-1/6) so f(-1/6) = 0.
      have hfix : f (-1/6) = 0 := by
        have h1 := hFE (-1/6)
        have h7 : (7 : ℝ) * (-1/6) + 1 = -1/6 := by ring
        rw [h7] at h1
        linarith
      -- FE at x = 1: f(8) = 49 f(1).
      -- LHS: (A/2)*64 + 8B + C = 32 A + 8 B + C.
      -- RHS: 49 (A/2 + B + C) = 49*(49C) = 2401 C.
      -- Actually let's use x = -1/6 in the polynomial form to extract info.
      -- f(-1/6) = 0: (A/2)(1/36) - B/6 + C = 0, i.e., A/72 - B/6 + C = 0, i.e., A - 12 B + 72 C = 0.
      have hfix_poly : (A/2) * (-1/6)^2 + B * (-1/6) + C = 0 := by
        rw [← hf_eq]; exact hfix
      have hfix_eq : A / 72 - B / 6 + C = 0 := by
        have : (A/2) * (-1/6)^2 + B * (-1/6) + C = A/72 - B/6 + C := by ring
        linarith [hfix_poly, this]
      -- FE at x = 1: f(8) = 49 f(1).
      have h1 : f (7 * 1 + 1) = 49 * f 1 := hFE 1
      have : f 8 = 49 * f 1 := by norm_num at h1; exact h1
      rw [hf_eq 8, hf_eq 1] at this
      -- (A/2)*64 + 8B + C = 49 (A/2 + B + C)
      -- 32 A + 8 B + C = 49 A / 2 + 49 B + 49 C
      -- Multiply through: 64 A + 16 B + 2 C = 49 A + 98 B + 98 C
      -- 15 A - 82 B - 96 C = 0
      -- Combined with A/2 + B - 48 C = 0 (i.e. A + 2B - 96 C = 0) and A - 12 B + 72 C = 0:
      -- From first: A/2 + B = 48 C ⟹ A = 96 C - 2B
      -- Sub into A - 12 B + 72 C = 0: 96C - 2B - 12 B + 72 C = 0, so 168 C = 14 B, so B = 12 C.
      -- Then A = 96 C - 24 C = 72 C.
      constructor
      · linarith
      · linarith
    obtain ⟨hA, hB⟩ := hABC
    refine ⟨C, ?_⟩
    intro x
    rw [hf_eq x, hA, hB]
    ring

end Imc2023P1
