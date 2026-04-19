/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2015, Round 1, Problem 3

A hotel has ten rooms along each side of a corridor. An olympiad team
leader wishes to book seven rooms on the corridor so that no two reserved
rooms on the same side of the corridor are adjacent. In how many ways can
this be done?
-/

namespace UK2015R1P3

/-- A booking is a pair (L, R) of subsets of `Fin 10` (the rooms on each
side). It is valid if |L| + |R| = 7 and no two booked rooms on the same
side are adjacent. -/
def Valid (LR : Finset (Fin 10) × Finset (Fin 10)) : Prop :=
  LR.1.card + LR.2.card = 7 ∧
  (∀ i : Fin 9, ¬ (i.castSucc ∈ LR.1 ∧ i.succ ∈ LR.1)) ∧
  (∀ i : Fin 9, ¬ (i.castSucc ∈ LR.2 ∧ i.succ ∈ LR.2))

instance : DecidablePred Valid := by
  intro LR; unfold Valid; infer_instance

def bookings : Finset (Finset (Fin 10) × Finset (Fin 10)) :=
  (Finset.univ : Finset (Finset (Fin 10) × Finset (Fin 10))).filter Valid

determine solution_value : ℕ := 4352

problem uk2015_r1_p3 : bookings.card = solution_value := by
  native_decide

end UK2015R1P3
