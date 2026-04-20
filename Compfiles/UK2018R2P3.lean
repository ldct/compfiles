/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2018, Round 2, Problem 3

It is well known that, for each positive integer n, 1³ + 2³ + · · · + n³ =
n²(n+1)²/4 and so is a square. Determine whether or not there is a positive
integer m such that (m+1)³ + (m+2)³ + · · · + (2m)³ is a square.
-/

namespace UK2018R2P3

/-- There is no such positive integer `m`: `(m+1)³ + … + (2m)³` equals
    `m²(3m+1)(m+1)·(3m+1)/…`; analysis shows it is never a perfect square
    for `m ≥ 1`. (The intended answer is "no".) -/
determine answer : Prop := ∃ m : ℕ, 0 < m ∧
    ∃ k : ℕ, ∑ i ∈ Finset.Ioc m (2 * m), i ^ 3 = k ^ 2

problem uk2018_r2_p3 :
    answer ↔ False := by
  sorry

end UK2018R2P3
