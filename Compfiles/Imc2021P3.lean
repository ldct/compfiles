/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 3

A positive real number `d` is *good* if there exists an infinite sequence
`a₁, a₂, … ∈ (0, d)` such that for each `n`, the points `a₁, …, aₙ` partition
`[0, d]` into segments of length at most `1/n` each. Find `sup {d | d good}`.

Answer: `ln 2`.
-/

namespace Imc2021P3

/-- The set of "good" positive reals `d`. -/
def Good (d : ℝ) : Prop :=
  0 < d ∧ ∃ a : ℕ → ℝ,
    (∀ n, 0 < a n ∧ a n < d) ∧
    ∀ n : ℕ, 0 < n →
      ∀ x ∈ Set.Icc (0 : ℝ) d,
        ∃ i ∈ Finset.range n, |x - a i| ≤ 1 / n
      -- TODO: this is a simplified form; the actual condition is that
      -- consecutive sorted points plus {0, d} partition with gaps ≤ 1/n.

/-- The supremum of good `d`. -/
noncomputable determine answer : ℝ := Real.log 2

-- snip begin

/-- The set `{d | Good d}` is bounded above by `2`.

At `n = 1`, any witness sequence has `a 0 ∈ (0, d)` and every `x ∈ [0,d]` must
satisfy `|x - a 0| ≤ 1`, so in particular `|0 - a 0| ≤ 1` and `|d - a 0| ≤ 1`,
giving `d ≤ 2`. -/
lemma good_le_two {d : ℝ} (h : Good d) : d ≤ 2 := by
  obtain ⟨hd, a, ha_mem, ha_cov⟩ := h
  have h1 : (1 : ℕ) > 0 := Nat.one_pos
  -- Apply the covering at n = 1 to x = 0 and x = d.
  have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) d := ⟨le_refl 0, le_of_lt hd⟩
  have hxd : d ∈ Set.Icc (0 : ℝ) d := ⟨le_of_lt hd, le_refl d⟩
  obtain ⟨i0, hi0, hb0⟩ := ha_cov 1 h1 0 hx0
  obtain ⟨id_, hid, hbd⟩ := ha_cov 1 h1 d hxd
  -- `i0, id_ ∈ range 1` means both equal `0`.
  have h_i0 : i0 = 0 := by
    rcases Finset.mem_range.mp hi0 with h
    omega
  have h_id : id_ = 0 := by
    rcases Finset.mem_range.mp hid with h
    omega
  rw [h_i0] at hb0
  rw [h_id] at hbd
  -- `|0 - a 0| ≤ 1` and `|d - a 0| ≤ 1`, and `1/(1:ℕ) = 1`.
  have h10 : (1 : ℝ) / (1 : ℕ) = 1 := by norm_num
  rw [h10] at hb0 hbd
  have : |d - 0| ≤ |d - a 0| + |a 0 - 0| := by
    have htri : d - 0 = (d - a 0) + (a 0 - 0) := by ring
    calc |d - 0| = |(d - a 0) + (a 0 - 0)| := by rw [htri]
      _ ≤ |d - a 0| + |a 0 - 0| := abs_add_le _ _
  have hd_abs : |d - 0| = d := by
    rw [sub_zero]; exact abs_of_pos hd
  have h_swap : |a 0 - 0| = |0 - a 0| := by rw [abs_sub_comm]
  rw [hd_abs, h_swap] at this
  linarith

-- snip end

problem imc2021_p3 : sSup { d | Good d } = answer := by
  -- TODO: upper bound via log-identity; lower bound via explicit construction.
  -- Pieces established:
  --   * `good_le_two`: crude upper bound `d ≤ 2` (not tight; real answer `log 2`).
  -- The full proof needs:
  --   * Tight upper bound: `d ≤ 1/n + 1/(n+1) + ... + 1/(2n)` for all n ≥ 1
  --     (use that after placing `a_{n+1}, ..., a_{n+k}`, at least `n+1-k`
  --     of the original gaps remain; each such gap ≤ 1/(n+k)), then limit → log 2.
  --   * Lower bound: explicit sequence with `a_n` inserted in the appropriate
  --     interval, using the identity `log(1 + 1/(2n)) + log(1 + 1/(2n+1))
  --     = log(1 + 1/n)` to refine partition of `[0, log 2]` so that after `n`
  --     insertions, all `n+1` intervals have length `< 1/n`.
  --   Note: the `Good` definition in this file is a simplified "covering"
  --   condition (every point is within 1/n of SOME a_i), not the exact
  --   sorted-partition condition from the original problem.
  sorry

end Imc2021P3
