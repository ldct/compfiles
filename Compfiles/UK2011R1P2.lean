/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2011, Round 1, Problem 2

Let s be an integer greater than 6. A solid cube of side s has a square
hole of side x < 6 drilled directly through from one face to the opposite
face (so the drill removes a cuboid). The volume of the remaining solid is
numerically equal to the total surface area of the remaining solid.
Determine all possible integer values of x.

Volume of remaining solid: s³ − x²·s.
Surface area: 6s² − 2x² + 4xs (two faces lose an x² square; the hole adds
four x·s rectangles inside).
Equation: s³ − x²·s = 6s² − 2x² + 4xs.
-/

namespace UK2011R1P2

def valid_x : Set ℤ :=
  { x | 0 < x ∧ x < 6 ∧ ∃ s : ℤ, s > 6 ∧ s^3 - x^2 * s = 6 * s^2 - 2 * x^2 + 4 * x * s }

determine answer : Set ℤ := {5}

problem uk2011_r1_p2 : valid_x = answer := by
  sorry

end UK2011R1P2
