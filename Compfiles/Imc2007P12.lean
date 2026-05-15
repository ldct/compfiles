/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 12
(IMC 2007, Day 2, Problem 6)

Let `f` be a nonzero real polynomial. Define `f₀ = f` and
`f_{n+1} = f_n + f_n'`. Prove that for all sufficiently large `n`, the
polynomial `f_n` has only real roots (i.e., it splits completely over `ℝ`).
-/

namespace Imc2007P12

open Polynomial

/-- The iteration `f_{n+1} = f_n + f_n'` starting from `f`. -/
noncomputable def iter (f : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => f
  | n + 1 => iter f n + (iter f n).derivative

problem imc2007_p12 (f : Polynomial ℝ) (hf : f ≠ 0) :
    ∃ N, ∀ n ≥ N, (iter f n).Splits := by
  -- The IMC 2007 solution uses Rolle's theorem and a careful argument
  -- about the minimum distance between consecutive roots of f_n', and
  -- shows that the values of f_n at its derivative's roots eventually
  -- alternate sign (positive at even-indexed local extrema, negative at
  -- odd-indexed ones), forcing all roots of f_n to be real.
  sorry

end Imc2007P12
