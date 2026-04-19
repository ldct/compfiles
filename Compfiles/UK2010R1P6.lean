/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2010, Round 1, Problem 6

Long John Silverman has captured a treasure map from Adam McBones. Adam has
buried the treasure at the point (x, y) with integer co-ordinates (not
necessarily positive). He has indicated on the map the values of x² + y and
x + y², and these numbers are distinct. Prove that Long John has to dig only
in one place to find the treasure.

That is: if (x, y) and (a, b) are pairs of integers with x² + y = a² + b,
x + y² = a + b² and x² + y ≠ x + y², then (x, y) = (a, b).
-/

namespace UK2010R1P6

problem uk2010_r1_p6 :
    ∀ x y a b : ℤ,
      x^2 + y = a^2 + b →
      x + y^2 = a + b^2 →
      x^2 + y ≠ x + y^2 →
      (x, y) = (a, b) := by
  sorry

end UK2010R1P6
