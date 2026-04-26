/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 1

A standard parabola is the graph of a quadratic polynomial `y = x² + ax + b`
with leading coefficient `1`. Three standard parabolas with vertices
`V₁, V₂, V₃` intersect pairwise at the points `A₁, A₂, A₃`. Let `s(x, y) =
(x, -y)` denote the reflection in the `x`-axis. Prove that the standard
parabolas with vertices `s(A₁), s(A₂), s(A₃)` intersect pairwise at the
points `s(V₁), s(V₂), s(V₃)`.
-/

namespace Imc2002P1

/-- The (standard) parabola with vertex `V = (v, w)` as a set of points. The equation
of this parabola is `y = (x - v)² + w`. -/
def parabola (V : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {P | P.2 = (P.1 - V.1) ^ 2 + V.2}

/-- Reflection across the `x`-axis. -/
def s (P : ℝ × ℝ) : ℝ × ℝ := (P.1, -P.2)

snip begin

/-- Key lemma: the parabola with vertex `V` contains `A` iff the parabola with
vertex `s A` contains `s V`. -/
lemma mem_parabola_iff (V A : ℝ × ℝ) : A ∈ parabola V ↔ s V ∈ parabola (s A) := by
  simp only [parabola, s, Set.mem_setOf_eq]
  constructor
  · intro h
    have : A.2 = (A.1 - V.1) ^ 2 + V.2 := h
    nlinarith [sq_nonneg (A.1 - V.1), sq_nonneg (V.1 - A.1)]
  · intro h
    have : -V.2 = (V.1 - A.1) ^ 2 + -A.2 := h
    nlinarith [sq_nonneg (A.1 - V.1), sq_nonneg (V.1 - A.1)]

snip end

problem imc2002_p1
    (V₁ V₂ V₃ A₁ A₂ A₃ : ℝ × ℝ)
    -- Standard parabolas with vertices V₁, V₂, V₃ intersect pairwise at A₁, A₂, A₃.
    -- We interpret this as: the parabolas with vertices Vᵢ and Vⱼ both pass through Aₖ
    -- where (i, j, k) is a permutation of (1, 2, 3). Following the statement, A₁ is
    -- the intersection of the parabolas with vertices V₂ and V₃, etc.
    (h12 : A₃ ∈ parabola V₁ ∧ A₃ ∈ parabola V₂)
    (h13 : A₂ ∈ parabola V₁ ∧ A₂ ∈ parabola V₃)
    (h23 : A₁ ∈ parabola V₂ ∧ A₁ ∈ parabola V₃) :
    -- Standard parabolas with vertices s(A₁), s(A₂), s(A₃) intersect pairwise at
    -- s(V₁), s(V₂), s(V₃).
    (s V₃ ∈ parabola (s A₁) ∧ s V₃ ∈ parabola (s A₂)) ∧
    (s V₂ ∈ parabola (s A₁) ∧ s V₂ ∈ parabola (s A₃)) ∧
    (s V₁ ∈ parabola (s A₂) ∧ s V₁ ∈ parabola (s A₃)) := by
  obtain ⟨h12a, h12b⟩ := h12
  obtain ⟨h13a, h13b⟩ := h13
  obtain ⟨h23a, h23b⟩ := h23
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- s V₃ ∈ parabola (s A₁), from A₁ ∈ parabola V₃
    exact (mem_parabola_iff V₃ A₁).mp h23b
  · -- s V₃ ∈ parabola (s A₂), from A₂ ∈ parabola V₃
    exact (mem_parabola_iff V₃ A₂).mp h13b
  · -- s V₂ ∈ parabola (s A₁), from A₁ ∈ parabola V₂
    exact (mem_parabola_iff V₂ A₁).mp h23a
  · -- s V₂ ∈ parabola (s A₃), from A₃ ∈ parabola V₂
    exact (mem_parabola_iff V₂ A₃).mp h12b
  · -- s V₁ ∈ parabola (s A₂), from A₂ ∈ parabola V₁
    exact (mem_parabola_iff V₁ A₂).mp h13a
  · -- s V₁ ∈ parabola (s A₃), from A₃ ∈ parabola V₁
    exact (mem_parabola_iff V₁ A₃).mp h12a

end Imc2002P1
