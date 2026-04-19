/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2013, Round 2, Problem 3

Consider the set of positive integers which, when written in binary, have
exactly 2013 digits and more 0s than 1s. Let n be the number of such
integers and let s be their sum. Prove that, when written in binary,
n + s has more 0s than 1s.
-/

namespace UK2013R2P3

/-- The set of positive integers whose binary representation has exactly
`d` digits, with more 0s than 1s. -/
def S (d : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ (d - 1)) (2 ^ d)).filter
    (fun k => (Nat.digits 2 k).count 1 < (Nat.digits 2 k).count 0)

/-- The number of such integers (for d = 2013). -/
def n : ℕ := (S 2013).card

/-- Their sum. -/
def s : ℕ := ∑ k ∈ S 2013, k

/-- In the binary representation of n + s, there are more 0s than 1s. -/
problem uk2013_r2_p3 :
    (Nat.digits 2 (n + s)).count 1 < (Nat.digits 2 (n + s)).count 0 := by
  sorry

end UK2013R2P3
