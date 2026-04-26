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

/-- The set of "good" positive reals `d`.

We say `d` is good if there is an infinite sequence `a : ℕ → ℝ` with values in
`(0, d)` such that for every `n ≥ 1`, sorting `{0, a 0, …, a (n-1), d}` gives
consecutive gaps all bounded by `1/n`.

Equivalent reformulation: for every `n ≥ 1` and every `x ∈ [0, d]` there is
some `i < n` (or one of the endpoints `0`, `d`) at distance `≤ 1/n` from `x`,
AND the maximum gap between consecutive sorted points is at most `1/n`.

For convenience we use the equivalent "every consecutive gap ≤ 1/n" form via
the supremum-of-min-distance characterisation. -/
def Good (d : ℝ) : Prop :=
  0 < d ∧ ∃ a : ℕ → ℝ,
    (∀ n, 0 < a n ∧ a n < d) ∧
    ∀ n : ℕ, 0 < n →
      -- consecutive gaps in the sorted sequence `{0, a 0, …, a (n-1), d}`
      -- are bounded by `1/n`. We express this via the equivalent statement
      -- that every `x ∈ [0,d]` lies in some interval `[p, q]` with
      -- `p, q ∈ {0, d} ∪ {a i | i < n}` and `q - p ≤ 1/n`.
      ∀ x ∈ Set.Icc (0 : ℝ) d,
        ∃ p q : ℝ, p ≤ x ∧ x ≤ q ∧ q - p ≤ 1 / n ∧
          (p = 0 ∨ ∃ i ∈ Finset.range n, p = a i) ∧
          (q = d ∨ ∃ j ∈ Finset.range n, q = a j)

/-- The supremum of good `d`. -/
noncomputable determine answer : ℝ := Real.log 2

-- snip begin

/-- The set `{d | Good d}` is bounded above by `2`.

At `n = 1`, the only available interior point is `a 0`, so `[0, d]` is split
into `[0, a 0]` and `[a 0, d]`, each of length `≤ 1`, giving `d ≤ 2`. -/
lemma good_le_two {d : ℝ} (h : Good d) : d ≤ 2 := by
  obtain ⟨hd, a, ha_mem, ha_cov⟩ := h
  have h1 : (0 : ℕ) < 1 := Nat.one_pos
  have hx0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) d := ⟨le_refl 0, le_of_lt hd⟩
  have hxd : d ∈ Set.Icc (0 : ℝ) d := ⟨le_of_lt hd, le_refl d⟩
  obtain ⟨p0, q0, hp0_le, h0_le_q0, hq0p0, hp0_cases, hq0_cases⟩ :=
    ha_cov 1 h1 0 hx0
  obtain ⟨pd, qd, hpd_le, hd_le_qd, hqdpd, hpd_cases, hqd_cases⟩ :=
    ha_cov 1 h1 d hxd
  -- For x = 0: p0 ≤ 0 ≤ q0, and p0 must be 0 (since the only options p0 = 0
  -- or p0 = a i with i < 1 force i = 0; but a 0 > 0 and p0 ≤ 0).
  have h_inv_one : (1 : ℝ) / (1 : ℕ) = 1 := by norm_num
  rw [h_inv_one] at hq0p0 hqdpd
  -- Determine p0 = 0 (using p0 ≤ 0).
  have hp0_zero : p0 = 0 := by
    rcases hp0_cases with h | ⟨i, hi, hpi⟩
    · exact h
    · exfalso
      have : i = 0 := by
        rcases Finset.mem_range.mp hi with h
        omega
      rw [this] at hpi
      have : a 0 ≤ 0 := hpi ▸ hp0_le
      have := (ha_mem 0).1
      linarith
  -- Determine qd = d (using qd ≥ d).
  have hqd_d : qd = d := by
    rcases hqd_cases with h | ⟨j, hj, hqj⟩
    · exact h
    · exfalso
      have : j = 0 := by
        rcases Finset.mem_range.mp hj with h
        omega
      rw [this] at hqj
      have : d ≤ a 0 := hqj ▸ hd_le_qd
      have := (ha_mem 0).2
      linarith
  -- Now q0 - 0 ≤ 1, i.e. q0 ≤ 1. Similarly d - pd ≤ 1.
  rw [hp0_zero] at hq0p0
  rw [hqd_d] at hqdpd
  -- We need pd ≤ q0 to chain: d - 0 = (d - pd) + (pd - q0) + (q0 - 0).
  -- But we don't have pd ≤ q0 directly. Instead use: q0 must be either d
  -- or a i, and pd must be either 0 or a j.
  -- Case on q0 and pd.
  rcases hq0_cases with hq0d | ⟨i, hi, hqi⟩
  · -- q0 = d, then d ≤ 1 ≤ 2.
    rw [hq0d] at hq0p0
    linarith
  · rcases hpd_cases with hpd0 | ⟨j, hj, hpj⟩
    · -- pd = 0, then d ≤ 1 ≤ 2.
      rw [hpd0] at hqdpd
      linarith
    · -- q0 = a i, pd = a j, both with i, j < 1, so i = j = 0.
      have hi0 : i = 0 := by
        rcases Finset.mem_range.mp hi with h
        omega
      have hj0 : j = 0 := by
        rcases Finset.mem_range.mp hj with h
        omega
      rw [hi0] at hqi
      rw [hj0] at hpj
      -- q0 = a 0 = pd, so d - 0 = (d - pd) + (q0 - 0) ≤ 1 + 1 = 2.
      have hq0_eq_pd : q0 = pd := by rw [hqi, hpj]
      have hsum : d - 0 = (d - pd) + (q0 - 0) := by
        rw [hq0_eq_pd]; ring
      linarith

/-- Tight upper bound `d ≤ 1/n + 1/(n+1) + ⋯ + 1/(2n)` for any `n ≥ 1`.

After placing `a_1, …, a_n`, the sorted gap sequence `ℓ_1 ≤ ⋯ ≤ ℓ_{n+1}` of
`[0,d]` partitioned by these points has the property that adding `k` more
points can increase the count of "small" gaps by at most `k`, so at least
`n + 1 - k` of the gaps `ℓ_{k+1}, …, ℓ_{n+1}` survive into the partition at
step `n+k`, giving `ℓ_{n+1-k} ≤ 1/(n+k)`. Summing `ℓ_i = ℓ_{n+1-(n+1-i)}`
gives `d = ∑ ℓ_i ≤ ∑_{k=0}^n 1/(n+k)`.

This is the tight upper bound; taking `n → ∞` yields `d ≤ log 2`.

TODO: full formalisation requires sorting the points and tracking gaps. -/
lemma good_le_harmonic_block {d : ℝ} (_h : Good d) (n : ℕ) (_hn : 0 < n) :
    d ≤ ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (n + k) := by
  sorry

/-- The supremum bound `d ≤ log 2`: take `n → ∞` in `good_le_harmonic_block`,
using `∑_{k=0}^n 1/(n+k) → log 2`. -/
lemma good_le_log_two {d : ℝ} (_h : Good d) : d ≤ Real.log 2 := by
  sorry

/-- Lower bound: `log 2` is good (or at least `d` arbitrarily close to it).

Construction: partition `[0, log 2]` into `n` parts of lengths
`log(1 + 1/(n+i-1))` for `i = 1, …, n`. Each part has length
`< 1/n` (since `log(1 + x) < x`). Going from `n` to `n+1` uses
`log(1 + 1/n) = log(1 + 1/(2n)) + log(1 + 1/(2n+1))`, so a single new point
suffices. -/
lemma log_two_le_sSup_good : Real.log 2 ≤ sSup { d | Good d } := by
  sorry

-- snip end

problem imc2021_p3 : sSup { d | Good d } = answer := by
  -- We have the two-sided bounds:
  --   * `good_le_log_two`: every good `d` satisfies `d ≤ log 2`.
  --   * `log_two_le_sSup_good`: `log 2 ≤ sSup`.
  -- The first gives `sSup ≤ log 2` (with `BddAbove` from `good_le_two`).
  show sSup { d | Good d } = Real.log 2
  apply le_antisymm
  · -- Upper bound: sSup ≤ log 2.
    refine csSup_le ?_ ?_
    · -- nonempty: e.g. d = 1/2 with constant-ish sequence is good (or use
      -- the construction lemma below). For now, defer.
      sorry
    · intro d hd
      exact good_le_log_two hd
  · exact log_two_le_sSup_good

end Imc2021P3
