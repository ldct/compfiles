/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 5
(IMC 2003, Day 1, Problem 5)

Let `g : [0,1] → ℝ` be continuous. Define a sequence of functions by
`f 0 = g` and `f (n+1) x = (1/x) * ∫_0^x f n t dt` for `x > 0`.

Find `lim_{n→∞} f n x` for `x ∈ (0, 1]`.

Answer: `g 0`.
-/

namespace Imc2003P5

open Filter Topology MeasureTheory intervalIntegral Set

/-- The iterated averaging operator on `g`. For `n = 0` it is `g`. For `n+1`, it is
    `(1/x) ∫_0^x (f n t) dt`, extended by `g 0` at `x = 0`. -/
noncomputable def f (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, x => g x
  | n+1, x => if x = 0 then g 0 else (1/x) * ∫ t in (0 : ℝ)..x, f g n t

snip begin

/-- The auxiliary operator `T` applied to a continuous function. -/
lemma f_zero (g : ℝ → ℝ) (x : ℝ) : f g 0 x = g x := rfl

lemma f_succ_of_pos (g : ℝ → ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    f g (n+1) x = (1/x) * ∫ t in (0 : ℝ)..x, f g n t := by
  show (if x = 0 then g 0 else (1/x) * ∫ t in (0 : ℝ)..x, f g n t) = _
  rw [if_neg hx.ne']

snip end

/-- The limit equals `g 0` for all `x ∈ (0, 1]`. -/
problem imc2003_p5 (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 1))
    (x : ℝ) (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    Tendsto (fun n => f g n x) atTop (𝓝 (g 0)) := by
  -- Proof outline: The key idea is the explicit formula
  --   f (n+1) x = (1/x) ∫₀^x g(t) · (log(x/t))^n / n! dt
  -- Alternatively, after substitution t = x e^(-u), this becomes
  --   f (n+1) x = ∫₀^∞ g(x e^(-u)) · u^n / n! · e^(-u) du.
  -- The Gamma-distributed weight concentrates at u = n, so x e^(-u) → 0,
  -- and continuity of g yields f n x → g 0.
  -- A second approach (used in the official solution) proves this first for
  -- nondecreasing g via induction (showing f n is monotone and bounded), then
  -- extends to general continuous g using the squeeze with the running sup/inf.
  sorry

end Imc2003P5
