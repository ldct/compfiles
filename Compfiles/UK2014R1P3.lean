/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2014, Round 1, Problem 3

A number written in base 10 is a string of 3^2013 digit 3s. No other
digit appears. Find the highest power of 3 which divides this number.
-/

namespace UK2014R1P3

/-- The number N consisting of 3^2013 threes equals
    (10^(3^2013) − 1) / 3. By lifting the exponent,
    v_3(10^(3^2013) − 1) = 2013 + v_3(9) = 2015, so v_3(N) = 2014. -/
determine solution_value : ℕ := 2014

/-- The repunit-of-threes number of length 3^n: 333…3 (with 3^n digits). -/
noncomputable def threesNumber (n : ℕ) : ℕ := (10^(3^n) - 1) / 3

problem uk2014_r1_p3 :
    ∀ k : ℕ, 3^k ∣ threesNumber 2013 ↔ k ≤ solution_value := by
  sorry

end UK2014R1P3
