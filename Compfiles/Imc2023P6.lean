/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2023, Problem 6

Ivan writes the matrix `[[2, 3], [2, 4]]` on the board. Then he performs the
following operation on the matrix several times: he chooses a row or a column
of the matrix, and he multiplies or divides the chosen row or column entry-wise
by the other row or column, respectively.

Can Ivan end up with the matrix `[[2, 4], [2, 3]]` after finitely many steps?

Answer: No.
-/

namespace Imc2023P6

/-- A 2×2 matrix of positive real entries, represented as `(a, b, c, d)` for
`[[a, b], [c, d]]`. -/
abbrev Mat := ℝ × ℝ × ℝ × ℝ

/-- One step of Ivan's operation: either multiply or divide a row/column
entry-wise by the other. There are 8 operations (2 rows/columns × 2 choices of
which × 2 for mult or div). All outputs must still have positive entries. -/
inductive Step : Mat → Mat → Prop
  -- Multiply row 1 by row 2 entrywise: (a,b,c,d) → (a*c, b*d, c, d)
  | mulR1 (a b c d : ℝ) : Step (a, b, c, d) (a * c, b * d, c, d)
  -- Multiply row 2 by row 1: (a,b,c,d) → (a, b, c*a, d*b)
  | mulR2 (a b c d : ℝ) : Step (a, b, c, d) (a, b, c * a, d * b)
  -- Divide row 1 by row 2: (a,b,c,d) → (a/c, b/d, c, d)
  | divR1 (a b c d : ℝ) : Step (a, b, c, d) (a / c, b / d, c, d)
  -- Divide row 2 by row 1: (a,b,c,d) → (a, b, c/a, d/b)
  | divR2 (a b c d : ℝ) : Step (a, b, c, d) (a, b, c / a, d / b)
  -- Multiply column 1 by column 2: (a,b,c,d) → (a*b, b, c*d, d)
  | mulC1 (a b c d : ℝ) : Step (a, b, c, d) (a * b, b, c * d, d)
  -- Multiply column 2 by column 1: (a,b,c,d) → (a, b*a, c, d*c)
  | mulC2 (a b c d : ℝ) : Step (a, b, c, d) (a, b * a, c, d * c)
  -- Divide column 1 by column 2: (a,b,c,d) → (a/b, b, c/d, d)
  | divC1 (a b c d : ℝ) : Step (a, b, c, d) (a / b, b, c / d, d)
  -- Divide column 2 by column 1: (a,b,c,d) → (a, b/a, c, d/c)
  | divC2 (a b c d : ℝ) : Step (a, b, c, d) (a, b / a, c, d / c)

/-- Reflexive transitive closure of `Step`. -/
def Reach : Mat → Mat → Prop := Relation.ReflTransGen Step

/-- The answer to the problem. -/
determine answer : Bool := false

snip begin

open Real

/-- Invariant: the "log-determinant" `log a · log d − log b · log c`. -/
noncomputable def logDet (M : Mat) : ℝ :=
  Real.log M.1 * Real.log M.2.2.2 - Real.log M.2.1 * Real.log M.2.2.1

/-- Positivity predicate. -/
def AllPos (M : Mat) : Prop :=
  0 < M.1 ∧ 0 < M.2.1 ∧ 0 < M.2.2.1 ∧ 0 < M.2.2.2

lemma step_preserves_pos {M N : Mat} (h : Step M N) (hM : AllPos M) : AllPos N := by
  obtain ⟨ha, hb, hc, hd⟩ := hM
  cases h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | exact ha | exact hb | exact hc | exact hd
      | positivity

lemma step_preserves_logDet {M N : Mat} (h : Step M N) (hM : AllPos M) :
    logDet N = logDet M := by
  obtain ⟨ha, hb, hc, hd⟩ := hM
  cases h <;> simp [logDet, Real.log_mul, Real.log_div,
    ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, ne_of_gt hd] <;> ring

lemma reach_preserves_pos {M N : Mat} (h : Reach M N) (hM : AllPos M) : AllPos N := by
  induction h with
  | refl => exact hM
  | tail _ hst ih => exact step_preserves_pos hst ih

lemma reach_preserves_logDet {M N : Mat} (h : Reach M N) (hM : AllPos M) :
    logDet N = logDet M := by
  induction h with
  | refl => rfl
  | tail hrel hst ih =>
      rw [step_preserves_logDet hst (reach_preserves_pos hrel hM), ih]

snip end

problem imc2023_p6 :
    answer = true ↔ Reach (2, 3, 2, 4) (2, 4, 2, 3) := by
  constructor
  · intro h; simp [answer] at h
  · -- We show reach is impossible because logDet differs.
    intro hreach
    -- Start has AllPos.
    have hstart : AllPos (2, 3, 2, 4) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [AllPos]
    -- logDet preserved.
    have heq : logDet (2, 4, 2, 3) = logDet (2, 3, 2, 4) :=
      reach_preserves_logDet hreach hstart
    -- But logDet (2,3,2,4) = log 2 * log 4 - log 3 * log 2
    --                     = log 2 * (log 4 - log 3)   [sign: log 4 > log 3 so positive]
    -- And logDet (2,4,2,3) = log 2 * log 3 - log 4 * log 2
    --                     = log 2 * (log 3 - log 4)   [negative]
    -- Both nonzero because log 2 ≠ 0 and log 3 ≠ log 4. Contradiction.
    -- More specifically, logDet (2,4,2,3) < 0 < logDet (2,3,2,4).
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog3_lt_log4 : Real.log 3 < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have h1 : 0 < logDet (2, 3, 2, 4) := by
      show 0 < Real.log 2 * Real.log 4 - Real.log 3 * Real.log 2
      have := mul_pos hlog2_pos (sub_pos.mpr hlog3_lt_log4)
      nlinarith
    have h2 : logDet (2, 4, 2, 3) < 0 := by
      show Real.log 2 * Real.log 3 - Real.log 4 * Real.log 2 < 0
      have := mul_pos hlog2_pos (sub_pos.mpr hlog3_lt_log4)
      nlinarith
    linarith

end Imc2023P6
