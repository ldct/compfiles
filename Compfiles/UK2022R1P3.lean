/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2022, Round 1, Problem 3

For each integer 0 ≤ n ≤ 11, Eliza has exactly three identical pieces of
gold that weigh 2ⁿ grams. In how many different ways can she form a pile
of gold weighing 2021 grams? (Two piles are different if they contain
different numbers of gold pieces of some weight. The arrangement of the
pieces in the piles is irrelevant.)
-/

namespace UK2022R1P3

/-- A pile is a choice, for each n ∈ {0,…,11}, of how many 2ⁿ-gram pieces
to use (at most 3 of each). -/
def piles : Finset (Fin 12 → Fin 4) :=
  (Finset.univ : Finset (Fin 12 → Fin 4)).filter
    (fun c => (∑ n : Fin 12, (c n).val * 2 ^ n.val) = 2021)

determine solution_value : ℕ := 21

problem uk2022_r1_p3 : piles.card = solution_value := by
  sorry

end UK2022R1P3
