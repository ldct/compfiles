/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2005, Round 1, Problem 5

Let S be a set of rational numbers with the following properties:
i) 1/2 ∈ S;
ii) If x ∈ S, then both 1/(x+1) ∈ S and x/(x+1) ∈ S.
Prove that S contains all rational numbers in the interval 0 < x < 1.
-/

namespace UK2005R1P5

problem uk2005_r1_p5 (S : Set ℚ)
    (h1 : (1 / 2 : ℚ) ∈ S)
    (h2 : ∀ x ∈ S, 1 / (x + 1) ∈ S ∧ x / (x + 1) ∈ S) :
    ∀ q : ℚ, 0 < q → q < 1 → q ∈ S := by
  sorry

end UK2005R1P5
