/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2015, Round 2, Problem 1

The first term x₁ of a sequence is 2014. Each subsequent term of the
sequence is defined in terms of the previous term. The iterative formula is

  x_{n+1} = ((√2 + 1) xₙ − 1) / ((√2 + 1) + xₙ).

Find the 2015th term x₂₀₁₅.

Observation: writing xₙ = tan θₙ, the recurrence gives
θ_{n+1} = θₙ − 3π/8 (since tan(3π/8) = √2 + 1), so the sequence has period 8
(in the sense that 8 · (3π/8) = 3π ≡ 0 (mod π)).
Thus x_{n+8} = xₙ. Since 2015 ≡ 7 (mod 8), x_{2015} = x₇.
Computing symbolically, x₇ = (x₁ − 1)/(x₁ + 1) = 2013/2015.
-/

namespace UK2015R2P1

noncomputable def seq : ℕ → ℝ
  | 0 => 2014  -- corresponds to x₁ in the problem
  | n + 1 => ((Real.sqrt 2 + 1) * seq n - 1) / ((Real.sqrt 2 + 1) + seq n)

noncomputable determine answer : ℝ := 2013 / 2015

problem uk2015_r2_p1 : seq 2014 = answer := by
  sorry

end UK2015R2P1
