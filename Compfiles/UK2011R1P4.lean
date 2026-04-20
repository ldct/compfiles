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

/-- Sign of a colour: red has sign -1, white and blue have sign +1. -/
def signC : Colour → ℤ
  | red => -1
  | white => 1
  | blue => 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- There are strictly more even-red arrangements than odd-red arrangements. -/
problem uk2011_r1_p4 : oddRedSet.card < evenRedSet.card := by
  -- For each arrangement a, ∏_p signC(a p) = (-1)^(redCount a).
  have hprod_on : ∀ (s : Finset (Fin 8 × Fin 8)) (a : Arrangement),
      (∏ p ∈ s, signC (a p)) = (-1 : ℤ) ^ (s.filter (fun p => a p = red)).card := by
    intro s a
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x t hxt ih =>
      rw [Finset.prod_insert hxt, Finset.filter_insert, ih]
      by_cases hred : a x = red
      · simp [hred]
        have : x ∉ t.filter (fun p => a p = red) := by
          intro h; exact hxt (Finset.mem_of_mem_filter _ h)
        rw [Finset.card_insert_of_notMem this]
        simp [signC, hred, pow_succ]
      · simp [hred]
        cases hac : a x with
        | red => exact absurd hac hred
        | white => simp [signC]
        | blue => simp [signC]
  have hprod : ∀ a : Arrangement,
      (∏ p : Fin 8 × Fin 8, signC (a p)) = (-1 : ℤ) ^ (redCount a) := by
    intro a; exact hprod_on Finset.univ a
  -- Sum factorizes.
  have hfact : (∑ a : Arrangement, ∏ p : Fin 8 × Fin 8, signC (a p)) =
      ∏ _p : Fin 8 × Fin 8, (∑ c : Colour, signC c) := by
    rw [← Fintype.prod_sum (fun (_ : Fin 8 × Fin 8) (c : Colour) => signC c)]
  have hsum_colour : (∑ c : Colour, signC c) = 1 := by
    rw [show (Finset.univ : Finset Colour) = {red, white, blue} from by decide]
    simp [signC]
  rw [hsum_colour, Finset.prod_const_one] at hfact
  have hsum_eq : (∑ a : Arrangement, (-1 : ℤ) ^ (redCount a)) = 1 := by
    rw [← hfact]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact (hprod a).symm
  -- Split by parity.
  have hunion : (Finset.univ : Finset Arrangement) = evenRedSet ∪ oddRedSet := by
    refine Finset.Subset.antisymm ?_ (Finset.subset_univ _)
    intro a _
    rcases Nat.even_or_odd (redCount a) with he | ho
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩)
  have hdisj : Disjoint evenRedSet oddRedSet := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    have he : Even (redCount a) := (Finset.mem_filter.mp ha).2
    have ho : Odd (redCount a) := (Finset.mem_filter.mp ha').2
    exact (Nat.not_even_iff_odd.mpr ho) he
  have hsplit : (∑ a : Arrangement, (-1 : ℤ) ^ (redCount a)) =
      (evenRedSet.card : ℤ) - (oddRedSet.card : ℤ) := by
    rw [hunion, Finset.sum_union hdisj]
    have h1 : ∑ a ∈ evenRedSet, (-1 : ℤ) ^ (redCount a) = (evenRedSet.card : ℤ) := by
      have hall : ∀ a ∈ evenRedSet, (-1 : ℤ) ^ (redCount a) = 1 := by
        intro a ha
        exact Even.neg_one_pow (Finset.mem_filter.mp ha).2
      calc ∑ a ∈ evenRedSet, (-1 : ℤ) ^ (redCount a)
          = ∑ _a ∈ evenRedSet, (1 : ℤ) := Finset.sum_congr rfl hall
        _ = (evenRedSet.card : ℤ) := by
            rw [Finset.sum_const]
            push_cast
            ring
    have h2 : ∑ a ∈ oddRedSet, (-1 : ℤ) ^ (redCount a) = -(oddRedSet.card : ℤ) := by
      have hall : ∀ a ∈ oddRedSet, (-1 : ℤ) ^ (redCount a) = -1 := by
        intro a ha
        exact Odd.neg_one_pow (Finset.mem_filter.mp ha).2
      calc ∑ a ∈ oddRedSet, (-1 : ℤ) ^ (redCount a)
          = ∑ _a ∈ oddRedSet, (-1 : ℤ) := Finset.sum_congr rfl hall
        _ = -(oddRedSet.card : ℤ) := by
            rw [Finset.sum_const]
            push_cast
            ring
    rw [h1, h2]; ring
  rw [hsplit] at hsum_eq
  have hlt : (oddRedSet.card : ℤ) < (evenRedSet.card : ℤ) := by linarith
  exact_mod_cast hlt

end UK2011R1P4
