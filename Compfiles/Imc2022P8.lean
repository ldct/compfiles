/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2022, Problem 8

Let `n, k ≥ 3` be integers, and let `S` be a circle. Let `n` blue and
`k` red points be chosen uniformly and independently at random on `S`.
Let `F` be the intersection of the convex hulls of the red and blue
points, and `m` the number of vertices of `F` (`m = 0` if `F` is empty).
Find the expected value of `m`.

Answer: `E(m) = 2kn/(n+k-1) - 2·k!·n!/(k+n-1)!`.

NOTE: We phrase the expected value as a combinatorial sum over
equally-likely cyclic color patterns, which for points in generic
position on a circle equals the measure-theoretic expectation.
-/

namespace Imc2022P8

/-- For a pair `(n, k)` and a cyclic colouring `c : Fin (n + k) → Bool`
(`true` = blue, `false` = red) with exactly `n` blue points, let
`mVal n k c` be the number of "color changes" in the cyclic sequence,
minus 2 if the colors form two contiguous arcs (giving the number of
vertices of the convex-hull intersection). -/
def mVal (n k : ℕ) (c : Fin (n + k) → Bool) : ℕ :=
  let changes := (Finset.univ : Finset (Fin (n + k))).filter
    (fun i => c i ≠ c ⟨(i.val + 1) % (n + k), Nat.mod_lt _ (by
      have : 0 < i.val + 1 := by omega
      have h : 0 < n + k := i.pos
      exact h)⟩) |>.card
  if changes = 2 then 0 else changes

/-- The set of valid colourings with exactly `n` trues (blue points). -/
def validCols (n k : ℕ) : Finset (Fin (n + k) → Bool) :=
  Finset.univ.filter
    (fun c => (Finset.univ.filter (fun i => c i = true)).card = n)

/-- The determined expected value (rational). -/
determine answer (n k : ℕ) : ℚ :=
  (2 * k * n : ℚ) / (n + k - 1) -
    (2 * Nat.factorial k * Nat.factorial n : ℚ) / Nat.factorial (k + n - 1)

problem imc2022_p8 (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    (∑ c ∈ validCols n k, (mVal n k c : ℚ)) / (validCols n k).card =
      answer n k := by
  -- TODO: Following the official solution.
  -- m equals #(color changes in cyclic sequence) except in the 2-arc
  -- case where the adjusted m is 0 (not 2). Expected color changes is
  -- 2nk/(n+k-1) by linearity; probability of the 2-arc case times 2
  -- yields the correction term 2·n!·k!/(n+k-1)!.
  sorry

end Imc2022P8
