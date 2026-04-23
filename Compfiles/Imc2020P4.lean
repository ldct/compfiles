/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 4

A polynomial `p` with real coefficients satisfies `p(x+1) − p(x) = x^100` for
all `x ∈ ℝ`. Prove that `p(1−t) ≥ p(t)` for `0 ≤ t ≤ 1/2`.
-/

namespace Imc2020P4

open Polynomial

problem imc2020_p4 (p : ℝ[X])
    (hp : ∀ x : ℝ, p.eval (x + 1) - p.eval x = x ^ 100)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    p.eval t ≤ p.eval (1 - t) := by
  -- TODO: hard; proof uses complex analysis / max principle on a rectangle.
  sorry

end Imc2020P4
