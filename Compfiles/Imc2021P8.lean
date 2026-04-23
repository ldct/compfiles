/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# International Mathematical Competition 2021, Problem 8

Let `n` be a positive integer. At most how many distinct unit vectors can be
selected in `ℝⁿ` such that from any three of them, at least two are orthogonal?

Answer: `2n`.
-/

namespace Imc2021P8

/-- The maximum number of unit vectors in ℝⁿ such that every 3 contain
an orthogonal pair. Answer: `2n`. -/
determine answer (n : ℕ) : ℕ := 2 * n

/-- The collection of `2n` unit vectors: the standard basis and its negation.
Indexed by `Fin (2 * n)`: the first `n` indices give `e_i`, the last `n` give `-e_i`. -/
noncomputable def example_vec (n : ℕ) : Fin (2 * n) → EuclideanSpace ℝ (Fin n) := fun k =>
  if h : k.val < n then
    EuclideanSpace.single ⟨k.val, h⟩ (1 : ℝ)
  else
    -EuclideanSpace.single ⟨k.val - n, by
      have hkn : n ≤ k.val := Nat.le_of_not_lt h
      have hk2 : k.val < 2 * n := k.isLt
      omega⟩ (1 : ℝ)

problem imc2021_p8 (n : ℕ) (hn : 0 < n) :
    IsGreatest
      { N | ∃ v : Fin N → EuclideanSpace ℝ (Fin n),
        Function.Injective v ∧
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
          inner ℝ (v i) (v j) = (0 : ℝ) ∨
          inner ℝ (v j) (v k) = (0 : ℝ) ∨
          inner ℝ (v i) (v k) = (0 : ℝ)) }
      (answer n) := by
  -- TODO: Two parts.
  --
  -- Membership (2n is achievable): The example_vec construction gives 2n unit
  -- vectors {±e_i : i ∈ Fin n}. Any three such vectors contain a pair with
  -- distinct indices (since each coordinate has only 2 associated vectors).
  -- Pairs with distinct coordinate indices are orthogonal.
  --
  -- Upper bound (N ≤ 2n): Projector-trace argument. For each unit vector v_i
  -- define the rank-1 projection P_i = v_i v_i^T. The hypothesis gives
  -- tr(P_i P_j P_k) = 0 for distinct i,j,k. Let Q = Σ P_i with eigenvalues
  -- t_i ≥ 0 and Σ t_i = tr(Q) = N. Then
  --   Σ t_i^3 = tr(Q^3) = N + 6 Σ_{i<j} tr(P_i P_j) = 3 Σ t_i^2 - 2N.
  -- Since (t-2)^2(t+1) ≥ 0 gives t^3 - 3t^2 + 4 ≥ 0,
  --   -2N = Σ(t_i^3 - 3 t_i^2) ≥ -4n, i.e., N ≤ 2n.
  sorry

end Imc2021P8
