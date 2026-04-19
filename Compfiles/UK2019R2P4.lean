/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2019, Round 2, Problem 4

Find all functions f from the positive real numbers to the positive real numbers
for which f(x) ≤ f(y) whenever x ≤ y and
f(x⁴) + f(x²) + f(x) + f(1) = x⁴ + x² + x + 1 for all x > 0.
-/

namespace UK2019R2P4

determine solution_set : Set ({x : ℝ // 0 < x} → {x : ℝ // 0 < x}) :=
  { fun x => x }

problem uk2019_r2_p4 :
    { f : {x : ℝ // 0 < x} → {x : ℝ // 0 < x} |
        Monotone f ∧
        ∀ x : {x : ℝ // 0 < x},
          (f ⟨x.1^4, by have := x.2; positivity⟩ : ℝ)
            + (f ⟨x.1^2, by have := x.2; positivity⟩ : ℝ)
            + (f x : ℝ) + (f ⟨1, by norm_num⟩ : ℝ)
          = x.1^4 + x.1^2 + x.1 + 1 } =
    solution_set := by
  sorry

end UK2019R2P4
