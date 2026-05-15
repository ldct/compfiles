/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2013, Problem 10
(IMC 2013, Day 2, Problem 10)

Consider a circular necklace with `2013` beads, each white or green.
A painting is *good* if among any `21` successive beads there is at
least one green bead. Prove that the number of good paintings is odd.
(Rotations/reflections give distinct paintings.)

## Proof outline

Let `N k` denote the number of *open* (linear) good colorings of length
`k`, i.e. colorings of `Fin k` such that any `21` consecutive positions
contain at least one green bead.

For `k ≤ 20`, every coloring is vacuously good, so `N k = 2 ^ k`. In
particular `N 0 = 1` is odd and `N 1, …, N 20` are even.

For `k ≥ 21`, conditioning on the position `ℓ ∈ {k-21, …, k-1}` of the
last green bead gives the recurrence
`N k = N (k-1) + N (k-2) + … + N (k-21)`.
Applying the recurrence twice yields `N k ≡ N (k-22) (mod 2)`. Hence
`N k` is odd iff `k ≡ 0` or `k ≡ 21 (mod 22)`.

For the *circular* count of length `2013`: pick any fixed bead and
condition on the run of `x` white beads at the start and `y` white
beads at the end of the cut linear sequence (so `x + y ≤ 20`); the
middle is a good open lace of length `2011 - x - y`. Therefore
the circular count equals
`∑_{x+y ≤ 20} N (2011 - x - y) = ∑_{s=0}^{20} (s + 1) · N (2011 - s)`.
Modulo `2`, only the terms with `s` even survive, giving
`N 2011 + N 2009 + … + N 1991`. Among the lengths
`2011, 2009, …, 1991`, only `2001 = 91 · 22 - 1 ≡ 21 (mod 22)`
gives an odd `N`, so the total is odd.
-/

namespace Imc2013P10

/-- A coloring of the necklace; `true` represents green, `false` represents white. -/
abbrev Coloring : Type := Fin 2013 → Bool

/-- A coloring is *good* if among any `21` successive beads (taken cyclically)
    there is at least one green bead. -/
def Good (c : Coloring) : Prop :=
  ∀ i : Fin 2013, ∃ j : Fin 21, c (i + ⟨j.val, by omega⟩) = true

instance : DecidablePred Good := fun _ => Fintype.decidableForallFintype

problem imc2013_p10 :
    Odd (Finset.univ.filter (fun c : Coloring => Good c)).card := by
  -- TODO: Following the official solution.
  -- Define `N k` = number of good open (linear) colorings `Fin k → Bool`.
  -- Show `N 0 = 1` (odd) and `N k = 2 ^ k` for `1 ≤ k ≤ 20` (even).
  -- For `k ≥ 21`, prove the recurrence
  --   `N k = ∑_{j=1}^{21} N (k - j)`
  -- by conditioning on the position of the last green bead in the
  -- (forced-nonempty) window `[k-21, k-1]`.
  -- Iterating once gives `N k ≡ N (k-22) (mod 2)`, hence `N k` is odd iff
  -- `k ≡ 0 ∨ k ≡ 21 (mod 22)`.
  --
  -- For the circular count: fix bead `0` and split on `(x, y)` with
  -- `x + y ≤ 20`, where `x` is the number of leading whites and `y` the
  -- number of trailing whites in the linear sequence obtained by cutting
  -- between bead `2012` and bead `0`. Setting `s = x + y`, the count is
  --   `∑_{s=0}^{20} (s + 1) · N (2011 - s)`.
  -- Modulo 2 this reduces to `∑_{s even} N (2011 - s)`, i.e.
  --   `N 2011 + N 2009 + ⋯ + N 1991`.
  -- These exponents mod 22 are `2011 ≡ 9, 2009 ≡ 7, …, 2001 ≡ 21, …, 1991 ≡ 11`.
  -- Only `N 2001` is odd, so the total is odd.
  sorry

end Imc2013P10
