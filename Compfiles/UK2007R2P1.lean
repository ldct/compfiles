/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2007, Round 2, Problem 1

Triangle ABC has integer-length sides, and AC = 2007. The internal bisector
of ∠BAC meets BC at D. Given that AB = CD, determine AB and BC.

By the angle-bisector length/ratio theorem, BD/DC = AB/AC, so if AB = c,
BC = a, AC = b = 2007 and CD = c, then BD = a − c and (a − c)/c = c/2007,
i.e. 2007(a − c) = c², giving a = c + c²/2007. Thus 2007 | c², and using
2007 = 3² · 223, we get 3·223 | c, so c is a multiple of 669. The triangle
inequality then pins down c = 1593 (c must satisfy c < 2 · 2007 = 4014, etc).
-/

namespace UK2007R2P1

/-- The pair (AB, BC) determined by the problem. -/
determine solution_pair : ℕ × ℕ := (1593, 1729)

problem uk2007_r2_p1 :
    ∀ a b c : ℕ,
      0 < a → 0 < b → 0 < c →
      b = 2007 →
      -- triangle inequality (non-degenerate integer triangle)
      a < b + c → b < a + c → c < a + b →
      -- AB = CD, where D is on BC with BD/DC = AB/AC (angle bisector);
      -- CD = c means BD = a - c and (a - c) * b = c * c
      c ≤ a →
      (a - c) * b = c * c →
      (c, a) = solution_pair := by
  sorry

end UK2007R2P1
