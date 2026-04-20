/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 1

Place the following numbers in increasing order of size, and justify your
reasoning: 3^{3^4}, 3^{4^3}, 3^{4^4}, 4^{3^3} and 4^{3^4}.
Note that a^{b^c} means a^(b^c).

Computations:
- 3^(3^4) = 3^81
- 3^(4^3) = 3^64
- 3^(4^4) = 3^256
- 4^(3^3) = 4^27 = 2^54
- 4^(3^4) = 4^81 = 2^162

Order: 4^(3^3) < 3^(4^3) < 3^(3^4) < 4^(3^4) < 3^(4^4).
-/

namespace UK2015R1P1

problem uk2015_r1_p1 :
    (4 : ℕ)^(3^3) < 3^(4^3) ∧
    (3 : ℕ)^(4^3) < 3^(3^4) ∧
    (3 : ℕ)^(3^4) < 4^(3^4) ∧
    (4 : ℕ)^(3^4) < 3^(4^4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end UK2015R1P1
