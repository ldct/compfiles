/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2019, Round 2, Problem 3

Let p be an odd prime. How many non-empty subsets of
{1, 2, 3, . . . , p − 2, p − 1} have a sum which is divisible by p?
-/

namespace UK2019R2P3

/-- Standard roots-of-unity filter argument: the answer is
    `(2^(p−1) − 2) / p + 1`. -/
determine solution_count (p : ℕ) : ℕ := (2 ^ (p - 1) - 2) / p + 1

problem uk2019_r2_p3 (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ((Finset.Icc 1 (p - 1)).powerset.filter
        (fun S => S.Nonempty ∧ p ∣ S.sum id)).card = solution_count p := by
  sorry

end UK2019R2P3
