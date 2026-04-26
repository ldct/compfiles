/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2014, Problem 9

A subset of `ℝⁿ` is `k`-almost contained by a hyperplane if fewer than `k`
points of the set are not on the hyperplane. A finite set is `k`-generic if no
hyperplane `k`-almost contains it. For each pair `(k, n)` of positive integers,
find the minimal `d(k, n)` such that every finite `k`-generic set in `ℝⁿ`
contains a `k`-generic subset of at most `d(k, n)` elements.

Answer: `d(k, n) = k * n` if `k ≥ 2` and `n ≥ 2`; otherwise `d(k, n) = k + n`.
-/

namespace Imc2014P9

open scoped BigOperators
open Set

/-- A "hyperplane" in `ℝⁿ` is the zero set of an affine function
`x ↦ ⟨v, x⟩ + c` with `v ≠ 0`. -/
structure Hyperplane (n : ℕ) where
  /-- Normal vector (must be nonzero). -/
  normal : EuclideanSpace ℝ (Fin n)
  /-- Affine constant. -/
  offset : ℝ
  normal_ne_zero : normal ≠ 0

/-- The carrier set of a hyperplane. -/
def Hyperplane.carrier {n : ℕ} (H : Hyperplane n) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | inner ℝ H.normal x + H.offset = 0}

instance {n : ℕ} : CoeTC (Hyperplane n) (Set (EuclideanSpace ℝ (Fin n))) :=
  ⟨Hyperplane.carrier⟩

/-- A subset `S` is `k`-almost contained by `H` if fewer than `k` points of `S`
are not on `H`. -/
def KAlmostContained {n : ℕ} (k : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n)))
    (H : Hyperplane n) : Prop :=
  letI : DecidablePred (fun x : EuclideanSpace ℝ (Fin n) => x ∉ H.carrier) :=
    fun _ => Classical.dec _
  (S.filter (fun x => x ∉ H.carrier)).card < k

/-- A finite set is `k`-generic if no hyperplane `k`-almost contains it. -/
def KGeneric {n : ℕ} (k : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ H : Hyperplane n, ¬ KAlmostContained k S H

/-- The proposed answer for `d(k, n)`. -/
def answer (k n : ℕ) : ℕ :=
  if 2 ≤ k ∧ 2 ≤ n then k * n else k + n

determine d : ℕ → ℕ → ℕ := answer

/--
The value `d k n` is the minimal natural number such that every finite
`k`-generic set in `ℝⁿ` contains a `k`-generic subset of cardinality at
most `d k n`.

This combines two statements:
* (existence) every finite `k`-generic set contains a `k`-generic subset of
  size `≤ d k n`;
* (minimality) there exists a `k`-generic set every `k`-generic subset of
  which has size `≥ d k n` (equivalently, the answer cannot be improved).
-/
problem imc2014_p9 (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∀ S : Finset (EuclideanSpace ℝ (Fin n)), KGeneric k S →
        ∃ T ⊆ S, KGeneric k T ∧ T.card ≤ d k n) ∧
    (∃ S : Finset (EuclideanSpace ℝ (Fin n)), KGeneric k S ∧
        ∀ T ⊆ S, KGeneric k T → d k n ≤ T.card) := by
  sorry

-- TODO: Full proof.
--
-- Solution outline (from the official solution):
--
-- Case `n = 1`: a "hyperplane" is a point; a set is `k`-generic iff at least
-- `k + 1` points are nonzero, equivalently the set has at least `k + 1`
-- points. So `d(k, 1) = k + 1`.
--
-- Case `k = 1`: build the subset by adding points one at a time, each outside
-- the affine span of the previous ones. After at most `n + 1` steps no
-- hyperplane contains all of them. So `d(1, n) = n + 1`.
--
-- Case `k, n ≥ 2`:
-- * Lower bound: the construction with `k` nonzero points on each of the `n`
--   coordinate axes (total `k * n`) is `k`-generic, and removing any single
--   point destroys `k`-genericity (the coordinate hyperplane perpendicular to
--   that axis then `k`-almost contains the set).
-- * Upper bound: in any minimal `k`-generic set every point lies on some
--   "ample" hyperplane that skips exactly `k` points. Iterate to obtain `n`
--   ample hyperplanes whose intersection is a single residual point; the
--   total count is at most `k * n + 1`. A re-ordering / averaging argument
--   shows the residual point can be removed, giving `k * n`.

end Imc2014P9
