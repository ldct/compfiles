/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2019, Round 1, Problem 6

Ada the ant starts at a point O on a plane. At the start of each minute she
chooses North, South, East or West, and marches 1 metre in that direction.
At the end of 2018 minutes she finds herself back at O. Let n be the number
of possible journeys which she could have made. What is the highest power
of 10 which divides n?
-/

namespace UK2019R1P6

/-- The four directions, as unit vectors. -/
inductive Dir | N | S | E | W
deriving DecidableEq, Fintype

def Dir.dx : Dir → ℤ
  | .N => 0 | .S => 0 | .E => 1 | .W => -1

def Dir.dy : Dir → ℤ
  | .N => 1 | .S => -1 | .E => 0 | .W => 0

/-- A journey is a sequence of 2018 directions. -/
abbrev Journey := Fin 2018 → Dir

/-- Journeys that return to the origin. -/
def returnJourneys : Finset Journey :=
  (Finset.univ : Finset Journey).filter
    (fun j => (∑ i : Fin 2018, (j i).dx) = 0 ∧
              (∑ i : Fin 2018, (j i).dy) = 0)

/-- n is the number of such journeys. -/
def n : ℕ := returnJourneys.card

determine solution_value : ℕ := 0

/-- The highest power of 10 that divides n is 10^0 = 1. -/
problem uk2019_r1_p6 :
    10 ^ solution_value ∣ n ∧ ¬ (10 ^ (solution_value + 1) ∣ n) := by
  sorry

end UK2019R1P6
