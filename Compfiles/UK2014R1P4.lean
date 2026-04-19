/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2014, Round 1, Problem 4

Isaac is planning a nine-day holiday. Every day he will go surfing, or
water skiing, or he will rest. On any given day he does just one of these
three things. He never does different water-sports on consecutive days.
How many schedules are possible for the holiday?
-/

namespace UK2014R1P4

/-- The three possible daily activities. -/
inductive Activity | surf | ski | rest
deriving DecidableEq, Fintype

open Activity

/-- Whether an activity is a water-sport. -/
def isWater : Activity → Bool
  | surf => true
  | ski => true
  | rest => false

/-- A schedule is valid iff no two consecutive days are *different*
water-sports. -/
def Valid (s : Fin 9 → Activity) : Prop :=
  ∀ i : Fin 9, ∀ h : i.val + 1 < 9,
    ¬ (isWater (s i) = true ∧ isWater (s ⟨i.val + 1, h⟩) = true ∧
       s i ≠ s ⟨i.val + 1, h⟩)

instance : DecidablePred Valid := by
  intro s; unfold Valid; infer_instance

/-- Number of valid schedules. -/
def validSchedules : Finset (Fin 9 → Activity) :=
  (Finset.univ : Finset (Fin 9 → Activity)).filter Valid

determine solution_value : ℕ := 3363

problem uk2014_r1_p4 : validSchedules.card = solution_value := by
  native_decide

end UK2014R1P4
