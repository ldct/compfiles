/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2018, Problem 8

Let `Ω = {(x, y, z) ∈ ℤ³ : y + 1 ≥ x ≥ y ≥ z ≥ 0}`. A frog moves along `Ω` by
unit jumps (changing exactly one coordinate by `±1`, while staying inside `Ω`).
For each positive integer `n`, find the number of paths from `(0, 0, 0)` to
`(n, n, n)` in exactly `3n` jumps.

Answer: `1/(2n+1) · C(3n, n)`. We express it as `C(3n, n) - 2 · C(3n, n-1)`,
which is the integer form of the same number (a Fuss–Catalan-like ballot
number).
-/

namespace Imc2018P8

/-- The region `Ω = {(x, y, z) ∈ ℤ³ : y + 1 ≥ x ≥ y ≥ z ≥ 0}`. -/
def Omega : Set (ℤ × ℤ × ℤ) :=
  { p | p.2.1 + 1 ≥ p.1 ∧ p.1 ≥ p.2.1 ∧ p.2.1 ≥ p.2.2 ∧ p.2.2 ≥ 0 }

/-- The six unit jumps: `±e₁, ±e₂, ±e₃`. -/
def isUnitJump (p q : ℤ × ℤ × ℤ) : Prop :=
  (q.1 = p.1 + 1 ∧ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2) ∨
  (q.1 = p.1 - 1 ∧ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2) ∨
  (q.1 = p.1 ∧ q.2.1 = p.2.1 + 1 ∧ q.2.2 = p.2.2) ∨
  (q.1 = p.1 ∧ q.2.1 = p.2.1 - 1 ∧ q.2.2 = p.2.2) ∨
  (q.1 = p.1 ∧ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2 + 1) ∨
  (q.1 = p.1 ∧ q.2.1 = p.2.1 ∧ q.2.2 = p.2.2 - 1)

/-- A frog path from `(0,0,0)` to `(n,n,n)` of length `3n` inside `Ω`. -/
structure FrogPath (n : ℕ) where
  /-- The vertices of the path, indexed `0, 1, …, 3n`. -/
  f : Fin (3 * n + 1) → ℤ × ℤ × ℤ
  start : f ⟨0, by positivity⟩ = (0, 0, 0)
  finish : f ⟨3 * n, by omega⟩ = ((n : ℤ), (n : ℤ), (n : ℤ))
  in_omega : ∀ i, f i ∈ Omega
  jumps : ∀ i : Fin (3 * n), isUnitJump (f i.castSucc) (f i.succ)

/-- The number of frog paths in `Ω` from `(0,0,0)` to `(n,n,n)` of length `3n`. -/
noncomputable def numPaths (n : ℕ) : ℕ := Nat.card (FrogPath n)

/-- The answer: `numPaths n = C(3n, n) - 2 · C(3n, n-1)`, equivalently
`C(3n,n) / (2n+1)`. -/
determine answer : ℕ → ℕ := fun n =>
  Nat.choose (3 * n) n - 2 * Nat.choose (3 * n) (n - 1)

/-- The number of paths from `(0,0,0)` to `(n,n,n)` of length `3n` inside `Ω`
equals `C(3n, n) - 2 C(3n, n-1) = 1/(2n+1) · C(3n, n)`. -/
problem imc2018_p8 (n : ℕ) (hn : 1 ≤ n) :
    numPaths n = answer n := by
  -- Solution sketch:
  -- The map `π : Ω → Ψ` sending `(x, y, z) ↦ (x + y, z)` where
  -- `Ψ = {(u, v) ∈ ℤ² : v ≥ 0, u ≥ 2v}` is a bijection sending unit
  -- jumps to unit jumps. So we count paths in `Ψ` from `(0,0)` to `(2n, n)`.
  -- By the reflection principle (paths constrained to `u ≥ 2v` and `v ≥ 0`),
  -- this number equals
  --   `C(3n, n) - 2 C(3n, n-1) = C(3n, n) / (2n + 1)`.
  -- This is a Fuss–Catalan-type ballot count.
  sorry

end Imc2018P8
