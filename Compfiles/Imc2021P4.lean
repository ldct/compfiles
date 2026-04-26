/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 4

Let `f : ℝ → ℝ` be a function. Suppose that for every `ε > 0`, there
exists `g : ℝ → (0, ∞)` such that for every pair `(x, y)`,

  if `|x - y| < min (g x) (g y)`, then `|f x - f y| < ε`.

Prove that `f` is the pointwise limit of a sequence of continuous
`ℝ → ℝ` functions (i.e. `f` is of Baire class `1`).
-/

namespace Imc2021P4

problem imc2021_p4 (f : ℝ → ℝ)
    (hyp : ∀ ε > 0, ∃ g : ℝ → ℝ, (∀ x, 0 < g x) ∧
      ∀ x y, |x - y| < min (g x) (g y) → |f x - f y| < ε) :
    ∃ (φ : ℕ → ℝ → ℝ), (∀ n, Continuous (φ n)) ∧
      ∀ x, Filter.Tendsto (fun n => φ n x) Filter.atTop (nhds (f x)) := by
  -- Following the official solution (Lebesgue characterization).
  -- For each n, hypothesis with ε = 1/(n+1) gives a gauge gₙ : ℝ → ℝ₊ with
  --     |x-y| < min (gₙ x) (gₙ y) → |f x - f y| < 1/(n+1).
  -- One shows every superlevel set {x : f x ≥ c} is Gδ:
  --     {x : f x ≥ c} = ⋂_{n,k} ⋃_{y : f y ≥ c}
  --       (y - min(1/k, gₙ y), y + min(1/k, gₙ y)).
  -- ⊆: take y = x. ⊇: if f x < c, choose n with f x < c - 1/(n+1) and k
  -- with gₙ x > 1/k; if x lies in the RHS pick witness y, then
  -- |x-y| < min(gₙ y, 1/k) ≤ min(gₙ y, gₙ x), so |f x - f y| < 1/(n+1),
  -- contradicting f y ≥ c and f x < c - 1/(n+1).
  -- Sublevel sets are Fσ symmetrically. Lebesgue's theorem then gives
  -- that f is Baire class 1. Mathlib does not currently have Lebesgue's
  -- theorem on Baire class 1 functions, so completing this proof would
  -- require formalizing that theorem from scratch (a substantial side
  -- project: piecewise-linear approximations on a refined partition of
  -- unity of ℝ adapted to the gauges, and a careful pointwise
  -- convergence argument).
  -- Extract a gauge sequence as concrete partial progress:
  choose g hg_pos hg_close using fun n : ℕ => hyp (1 / (n + 1 : ℝ))
    (by positivity)
  sorry

end Imc2021P4
