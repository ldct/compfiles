/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2021, Round 1, Problem 4

In the equation AAA + AA = B,BBC,DED,BEE,BBB,BBE the letters A, B, C,
D and E represent different base 10 digits (so the right hand side is
a sixteen digit number and AA is a two digit number). Given that C = 9,
find A, B, D and E.
-/

namespace UK2021R1P4

/-- Build the 16-digit integer B,BBC,DED,BEE,BBB,BBE (in base 10). -/
def rhsNumber (B C D E : ℕ) : ℕ :=
  B * 10^15 + B * 10^14 + B * 10^13 + C * 10^12 +
  D * 10^11 + E * 10^10 + D * 10^9 +
  B * 10^8 + E * 10^7 + E * 10^6 +
  B * 10^5 + B * 10^4 + B * 10^3 +
  B * 10^2 + B * 10^1 + E

/-- AAA is a three-digit repdigit, AA is a two-digit repdigit. -/
def lhsNumber (A : ℕ) : ℕ := (A * 100 + A * 10 + A) + (A * 10 + A)

determine solution : ℕ × ℕ × ℕ × ℕ := (3, 2, 0, 5)

problem uk2021_r1_p4 :
    ∃! ABDE : ℕ × ℕ × ℕ × ℕ,
      let A := ABDE.1
      let B := ABDE.2.1
      let D := ABDE.2.2.1
      let E := ABDE.2.2.2
      A < 10 ∧ B < 10 ∧ D < 10 ∧ E < 10 ∧
      (A ≠ B) ∧ (A ≠ 9) ∧ (A ≠ D) ∧ (A ≠ E) ∧
      (B ≠ 9) ∧ (B ≠ D) ∧ (B ≠ E) ∧
      (9 ≠ D) ∧ (9 ≠ E) ∧ (D ≠ E) ∧
      lhsNumber A = rhsNumber B 9 D E ∧
      ABDE = solution := by
  sorry

end UK2021R1P4
