/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2013, Problem 9

Does there exist an infinite set `M` of positive integers such that for any
`a, b ∈ M` with `a < b`, the sum `a + b` is square-free?

The answer is YES.
-/

namespace Imc2013P9

/-- The answer is `True`: such an infinite set exists. -/
determine answer : Prop := True

problem imc2013_p9 :
    answer ↔
    ∃ M : Set ℕ, M.Infinite ∧ (∀ a ∈ M, 0 < a) ∧
      (∀ a ∈ M, ∀ b ∈ M, a < b → Squarefree (a + b)) := by
  unfold answer
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  -- TODO: Following the official solution.
  -- Inductively build 1 = n_1 < 2 = n_2 < ... with all n_i + n_j square-free
  -- (for i < j). Given n_1, ..., n_k, set M = ((n_1 + ... + n_k + 2k)!)^2
  -- and seek n_{k+1} = 1 + M*x for an appropriate x ∈ ℕ.
  --
  -- For each i ≤ k, any prime p whose square divides n_i + n_{k+1} = n_i + 1 + M*x
  -- must satisfy p > 2k (since for p ≤ 2k, p² | M and p² | M*x, but p² ∤ n_i + 1
  -- because n_i + 1 ≤ n_1 + ... + n_k + 2k < (n_1 + ... + n_k + 2k)! = √M
  -- unless n_i + 1 = 0, which it isn't).
  --
  -- Counting bad x ∈ [1, N]: for each i ≤ k and each prime p with
  -- 2k < p < √(M(N+1)), there are at most N/p² + 1 values of x with
  -- p² | n_i + 1 + M*x. Total bad count is bounded by
  -- N * k * ∑_{p > 2k} 1/p² + k * √(M(N+1)) < N/2 + k√(M(N+1)) < N
  -- for N large enough. So a good x exists.
  sorry

end Imc2013P9
