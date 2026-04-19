/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2011, Round 1, Problem 4

Isaac has a large supply of counters, and places one in each of the 1 × 1
squares of an 8 × 8 chessboard. Each counter is either red, white or blue.
A particular pattern of coloured counters is called an arrangement.
Determine whether there are more arrangements which contain an even number
of red counters or more arrangements which contain an odd number of red
counters. Note that 0 is an even number.
-/

namespace UK2011R1P4

/-- The three colours. -/
inductive Colour | red | white | blue
deriving DecidableEq, Fintype

open Colour

/-- An arrangement is a colouring of the 64 squares of an 8 × 8 board. -/
abbrev Arrangement := Fin 8 × Fin 8 → Colour

instance : Fintype Arrangement := Pi.instFintype

/-- The number of red counters in an arrangement. -/
def redCount (a : Arrangement) : ℕ :=
  (Finset.univ.filter fun p => a p = red).card

/-- The set of arrangements with an even number of red counters. -/
def evenRedSet : Finset Arrangement :=
  (Finset.univ : Finset Arrangement).filter (fun a => Even (redCount a))

/-- The set of arrangements with an odd number of red counters. -/
def oddRedSet : Finset Arrangement :=
  (Finset.univ : Finset Arrangement).filter (fun a => Odd (redCount a))

/-- There are strictly more even-red arrangements than odd-red arrangements. -/
problem uk2011_r1_p4 : oddRedSet.card < evenRedSet.card := by
  sorry

end UK2011R1P4
