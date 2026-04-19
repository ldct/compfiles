/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# British Mathematical Olympiad 2009, Round 1, Problem 6

The obtuse-angled triangle ABC has sides of length a, b and c opposite
the angles ∠A, ∠B and ∠C respectively. Prove that
a³ cos A + b³ cos B + c³ cos C < abc.
-/

namespace UK2009R1P6

open Real

problem uk2009_r1_p6 (A B C a b c : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hABC : A + B + C = π)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsine : a / sin A = b / sin B ∧ b / sin B = c / sin C)
    (hobtuse : π / 2 < A ∨ π / 2 < B ∨ π / 2 < C) :
    a^3 * cos A + b^3 * cos B + c^3 * cos C < a * b * c := by
  sorry

end UK2009R1P6
