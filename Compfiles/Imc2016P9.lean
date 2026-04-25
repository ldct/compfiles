/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2016, Problem 9

Let `k` be a positive integer. For each nonnegative integer `n`, let `f(n)`
be the number of solutions `(x_1, …, x_k) ∈ ℤ^k` of
`|x_1| + … + |x_k| ≤ n`. Prove that for every `n ≥ 1`,
`f(n-1) * f(n+1) ≤ f(n)^2`.
-/

namespace Imc2016P9

open Finset

/-- The set of lattice points in the closed `ℓ¹`-ball of radius `n` in `ℤ^k`. -/
noncomputable def latticeBall (k n : ℕ) : Finset (Fin k → ℤ) :=
  ((Fintype.piFinset fun _ : Fin k => Finset.Icc (-(n:ℤ)) (n:ℤ))).filter
    (fun x => ∑ i, |x i| ≤ n)

/-- `f k n` counts the number of `(x_1,…,x_k) ∈ ℤ^k` with `∑ |x_i| ≤ n`. -/
noncomputable def f (k n : ℕ) : ℕ := (latticeBall k n).card

problem imc2016_p9 (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    f k (n - 1) * f k (n + 1) ≤ (f k n) ^ 2 := by
  sorry


end Imc2016P9
