/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2018, Round 1, Problem 2

In a 100-day period, each of six friends goes swimming on exactly 75 days.
There are n days on which at least five of the friends swim. What are the
largest and smallest possible values of n?
-/

namespace UK2018R1P2

/-- A swimming pattern: for each friend (`Fin 6`) and each day (`Fin 100`),
a Boolean indicating whether that friend swam on that day. -/
abbrev Pattern := Fin 6 → Fin 100 → Bool

/-- Days on which a given friend swam. -/
def daysSwum (p : Pattern) (f : Fin 6) : Finset (Fin 100) :=
  Finset.univ.filter (fun d => p f d = true)

/-- Number of friends swimming on a given day. -/
def friendsSwimming (p : Pattern) (d : Fin 100) : ℕ :=
  (Finset.univ.filter (fun f : Fin 6 => p f d = true)).card

/-- Days on which at least 5 friends swim. -/
def bigDays (p : Pattern) : Finset (Fin 100) :=
  Finset.univ.filter (fun d => 5 ≤ friendsSwimming p d)

/-- Valid patterns: each friend swims on exactly 75 days. -/
def Valid (p : Pattern) : Prop :=
  ∀ f : Fin 6, (daysSwum p f).card = 75

determine n_max : ℕ := 90
determine n_min : ℕ := 50

problem uk2018_r1_p2 :
    (∃ p : Pattern, Valid p ∧ (bigDays p).card = n_max) ∧
    (∃ p : Pattern, Valid p ∧ (bigDays p).card = n_min) ∧
    (∀ p : Pattern, Valid p → (bigDays p).card ≤ n_max) ∧
    (∀ p : Pattern, Valid p → n_min ≤ (bigDays p).card) := by
  sorry

end UK2018R1P2
