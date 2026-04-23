/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 8

Compute

  `lim_{n → ∞} (1 / log log n) · Σ_{k=1}^n (-1)^k · C(n, k) · log k`.

Answer: `1`.
-/

namespace Imc2020P8

open Real

/-- The sum `Σ_{k=1}^n (-1)^k · C(n, k) · log k`. Since `log 1 = 0`, the
`k = 1` term contributes `0`, so we may as well sum over `k = 1..n`. -/
noncomputable def S (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.log k

/-- The answer: the limit equals `1`. -/
determine answer : ℝ := 1

problem imc2020_p8 :
    Filter.Tendsto (fun n : ℕ => S n / Real.log (Real.log n))
      Filter.atTop (nhds answer) := by
  -- TODO: Following the official solution via the Frullani integral
  --   log k = ∫_0^∞ (e^{-x} - e^{-kx}) / x dx.
  -- Substituting into S n gives
  --   S n = ∫_0^∞ ((1 - e^{-x}) - (1 - e^{-x})^n - something) / x dx.
  -- After careful splitting at M with M · e^M = n, the tail is O(1) and
  -- the main term matches (1 + o(1)) · log log n.
  sorry

end Imc2020P8
