/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# British Mathematical Olympiad 2024, Round 2, Problem 4

Let m < n be positive integers. Start with n piles, each of m objects.
Repeatedly carry out the following operation: choose two piles and remove
n objects in total from the two piles. For which (m, n) is it possible to
empty all the piles?
-/

namespace UK2024R2P4

/-- One step: from configuration `c : Fin n → ℕ`, pick two distinct indices
i ≠ j, subtract a ≥ 0 from c i and b ≥ 0 from c j with a + b = n, where
a ≤ c i and b ≤ c j. -/
inductive Step (n : ℕ) : (Fin n → ℕ) → (Fin n → ℕ) → Prop
  | mk (c : Fin n → ℕ) (i j : Fin n) (hij : i ≠ j) (a b : ℕ)
      (hab : a + b = n) (ha : a ≤ c i) (hb : b ≤ c j) :
      Step n c (fun k => if k = i then c i - a else if k = j then c j - b else c k)

/-- Reflexive-transitive closure of `Step`. -/
inductive Reaches (n : ℕ) : (Fin n → ℕ) → (Fin n → ℕ) → Prop
  | refl (c) : Reaches n c c
  | trans {c₁ c₂ c₃} : Step n c₁ c₂ → Reaches n c₂ c₃ → Reaches n c₁ c₃

/-- Initial configuration: each pile has `m` objects. -/
def initial (m n : ℕ) : Fin n → ℕ := fun _ => m

/-- We can empty all piles from the initial configuration. -/
def CanEmpty (m n : ℕ) : Prop :=
  Reaches n (initial m n) (fun _ => 0)

/-- Answer: we can empty iff `m * n` is even. -/
determine solution_predicate : ℕ → ℕ → Prop := fun m n => Even (m * n)

problem uk2024_r2_p4 (m n : ℕ) (hm : 0 < m) (hmn : m < n) :
    CanEmpty m n ↔ solution_predicate m n := by
  sorry

end UK2024R2P4
