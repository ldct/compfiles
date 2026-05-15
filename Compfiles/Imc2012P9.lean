/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2012, Problem 9 (Day 2, Problem 4)

Let `n ≥ 2` be an integer.  Find all real numbers `a` such that there exist real
numbers `x₁, …, xₙ` satisfying
`x₁ (1 - x₂) = x₂ (1 - x₃) = … = xₙ₋₁ (1 - xₙ) = xₙ (1 - x₁) = a`.

Answer:  `a ∈ (-∞, 1/4] ∪ { 1 / (4 cos² (k π / n)) : 1 ≤ k, k < n/2 }`.
-/

namespace Imc2012P9

open scoped Real

/-- The set of valid values of `a` for a given `n`:
the union of the half-line `(-∞, 1/4]` and the discrete set
`{ 1 / (4 cos² (k π / n)) : 1 ≤ k < n/2 }`. -/
determine answer (n : ℕ) : Set ℝ :=
  Set.Iic (1 / 4) ∪
  { a : ℝ | ∃ k : ℕ, 1 ≤ k ∧ 2 * k < n ∧ a = 1 / (4 * (Real.cos (k * π / n)) ^ 2) }

-- snip begin

/-- For `a ≤ 1/4`, the constant solution `xᵢ = (1 - √(1 - 4a)) / 2` works. -/
lemma exists_constant_of_le_quarter
    {n : ℕ} {a : ℝ} (ha : a ≤ 1 / 4) :
    ∃ x : ZMod n → ℝ,
      (∀ i : ZMod n, x i * (1 - x (i + 1)) = a) := by
  -- Pick a real root `r` of `r(1-r) = a`, possible iff `1 - 4a ≥ 0`.
  set d : ℝ := Real.sqrt (1 - 4 * a) with hd_def
  have h14 : 0 ≤ 1 - 4 * a := by linarith
  have hd_sq : d ^ 2 = 1 - 4 * a := by
    have := Real.sq_sqrt h14
    rw [sq, ← this]; ring
  set r : ℝ := (1 - d) / 2 with hr_def
  have hr : r * (1 - r) = a := by
    have : 1 - r = (1 + d) / 2 := by rw [hr_def]; ring
    rw [this, hr_def]
    have : (1 - d) / 2 * ((1 + d) / 2) = (1 - d ^ 2) / 4 := by ring
    rw [this, hd_sq]; ring
  refine ⟨fun _ => r, fun i => ?_⟩
  exact hr

/-- Easy direction: every `a ≤ 1/4` belongs to the answer set. -/
lemma mem_answer_of_le_quarter
    {n : ℕ} {a : ℝ} (ha : a ≤ 1 / 4) : a ∈ answer n := by
  exact Or.inl ha

-- snip end

problem imc2012_p9 (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    (∃ x : ZMod n → ℝ,
        ∀ i : ZMod n, x i * (1 - x (i + 1)) = a) ↔
      a ∈ answer n := by
  -- TODO: full proof.  The official solution iterates the Möbius transform
  -- `φ(x) = 1 - a/x` whose matrix `M = ((1, -a), (1, 0))` has eigenvalues
  -- `(1 ± i √(4a-1))/2` for `a > 1/4`.  The cycle condition `φⁿ = id` on
  -- `ℝℙ¹` is equivalent to `λ₁ⁿ = λ₂ⁿ`, i.e. `arg λ₁ = k π / n` for some
  -- `1 ≤ k < n/2`, which yields `a = 1 / (4 cos² (k π / n))`.
  --
  -- The easy direction `a ≤ 1/4 → ∃ x` is given by `exists_constant_of_le_quarter`
  -- above; for the discrete values of `a > 1/4`, one chooses
  -- `x_i = Re(λ₁^i z) / Re(λ₁^(i-1) z)` for a suitable complex `z`.
  sorry

end Imc2012P9
