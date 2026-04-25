/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2013, Problem 3
(IMC 2013, Day 1, Problem 3)

There are `2n` students in a school (`n ≥ 2`). Each week `n` students go on a trip.
After several trips, every two students were together on at least one trip.
What is the minimum number of trips needed?

Answer: `6`.

## Solution sketch

**Lower bound.** Each student must share a trip with the `2n - 1` other students.
A trip containing them covers `n - 1` partners; thus each student appears in at
least `⌈(2n-1)/(n-1)⌉ = 3` trips. The total attendance is at least `6n`; each
trip seats `n`, so at least `6` trips are needed.

**Upper bound.** A construction with `6` trips exists for every `n ≥ 2`. When `n`
is even, partition the students into 4 equal groups `A,B,C,D` (each of size `n/2`)
and take the six pairwise unions `A∪B, C∪D, A∪C, B∪D, A∪D, B∪C`. When `n` is a
multiple of `3`, partition into `6` equal groups and use a suitable system of `6`
triples covering all pairs of groups. For general `n ≥ 2`, write `n = 2x + 3y`
with `x, y ≥ 0` and combine the two constructions.
-/

namespace Imc2013P3

open Finset

/-- A `cover n k` is a sequence of `k` trips, each of size `n`, such that every
pair of students from `Fin (2*n)` is contained in some trip. -/
def IsCover (n k : ℕ) (T : Fin k → Finset (Fin (2*n))) : Prop :=
  (∀ i, (T i).card = n) ∧
  ∀ s₁ s₂ : Fin (2*n), s₁ ≠ s₂ → ∃ i, s₁ ∈ T i ∧ s₂ ∈ T i

/-- The set of trip counts that admit a valid cover. -/
def CoverCounts (n : ℕ) : Set ℕ :=
  { k | ∃ T : Fin k → Finset (Fin (2*n)), IsCover n k T }

snip begin

/-- For each student, the set of trips they attend. -/
private def attends {n k : ℕ} (T : Fin k → Finset (Fin (2*n))) (s : Fin (2*n)) :
    Finset (Fin k) :=
  Finset.univ.filter (fun i => s ∈ T i)

/-- Every student attends at least 3 trips, when `n ≥ 2`. -/
private lemma three_le_attends {n k : ℕ} (hn : 2 ≤ n)
    (T : Fin k → Finset (Fin (2*n))) (hT : IsCover n k T) (s : Fin (2*n)) :
    3 ≤ (attends T s).card := by
  -- Each trip `i` containing `s` has `n - 1` other students; their union covers all `2n - 1` others.
  -- Define the set of "partners" of `s` reached via trips in `attends T s`.
  -- This set is `Finset.univ \ {s}`, of cardinality `2n - 1`.
  -- It is a subset of `⋃_{i ∈ attends T s} (T i \ {s})`, each summand of size `≤ n - 1`.
  set A := attends T s with hA_def
  -- Cardinality of partners.
  have h2n : (Finset.univ : Finset (Fin (2*n))).card = 2 * n := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- For each `i ∈ A`, `(T i).erase s` has cardinality `n - 1`.
  have hcard_erase : ∀ i ∈ A, ((T i).erase s).card = n - 1 := by
    intro i hi
    have hin : s ∈ T i := by
      simp [A, attends] at hi; exact hi
    rw [Finset.card_erase_of_mem hin, hT.1 i]
  -- The "partners" finset.
  set P : Finset (Fin (2*n)) := Finset.univ.erase s with hP_def
  have hPcard : P.card = 2 * n - 1 := by
    rw [hP_def, Finset.card_erase_of_mem (Finset.mem_univ s), h2n]
  -- `P ⊆ ⋃_{i ∈ A} (T i).erase s`.
  have hPsub : P ⊆ A.biUnion (fun i => (T i).erase s) := by
    intro x hx
    have hxs : x ≠ s := by
      have := Finset.mem_erase.mp hx
      exact this.1
    obtain ⟨i, hxi, hsi⟩ := hT.2 x s hxs
    simp only [Finset.mem_biUnion]
    refine ⟨i, ?_, ?_⟩
    · simp [A, attends, hsi]
    · rw [Finset.mem_erase]; exact ⟨hxs, hxi⟩
  -- Hence `2n - 1 ≤ A.card * (n - 1)`.
  have hbound : 2 * n - 1 ≤ A.card * (n - 1) := by
    have h1 : P.card ≤ A.card * (n - 1) := by
      calc P.card ≤ (A.biUnion (fun i => (T i).erase s)).card := Finset.card_le_card hPsub
        _ ≤ ∑ i ∈ A, ((T i).erase s).card := Finset.card_biUnion_le
        _ = ∑ _i ∈ A, (n - 1) := Finset.sum_congr rfl hcard_erase
        _ = A.card * (n - 1) := by rw [Finset.sum_const]; ring
    rw [hPcard] at h1; exact h1
  -- Now `2n - 1 ≤ A.card * (n - 1)` and `n ≥ 2` give `A.card ≥ 3`.
  -- Indeed, if `A.card ≤ 2`, then `A.card * (n - 1) ≤ 2(n - 1) = 2n - 2 < 2n - 1`.
  by_contra hlt
  have h2 : A.card ≤ 2 := by omega
  have h3 : A.card * (n - 1) ≤ 2 * (n - 1) := Nat.mul_le_mul_right _ h2
  omega

snip end

/-- The answer: 6 trips are minimal. -/
problem imc2013_p3 (n : ℕ) (hn : 2 ≤ n) :
    IsLeast (CoverCounts n) 6 := by
  refine ⟨?_, ?_⟩
  · -- 6 ∈ CoverCounts n: there is a cover with 6 trips.
    -- TODO: Construction. Write n = 2x + 3y with x, y ≥ 0 (using n ≥ 2). Partition
    -- the 2n students into 4 "A-groups" of size x (call them A, B, C, D) and 6
    -- "G-groups" of size y (call them G₁, ..., G₆). Each trip consists of two
    -- A-groups (2x students) plus three G-groups (3y students), total n. The six
    -- trips are indexed by pairs of A-groups: AB, CD, AC, BD, AD, BC. Their G-triples
    -- form a {2}-cover of {G₁,...,G₆} arranged so that every (A-group, G-group) pair
    -- co-occurs in some trip. An explicit choice of G-triples is:
    --   T_AB = {1,2,4}, T_CD = {1,4,5}, T_AC = {3,4,6},
    --   T_BD = {1,3,6}, T_AD = {2,5,6}, T_BC = {2,3,5}.
    -- These are the cyclic shifts of {1,2,4} mod 6 (a perfect difference set).
    sorry
  · -- 6 is a lower bound: every cover has ≥ 6 trips.
    rintro k ⟨T, hT⟩
    -- Sum over students of |attends T s| ≥ 6n; this equals sum over trips of |T i| = k * n.
    -- Hence k * n ≥ 6n, so k ≥ 6.
    have hpos : 0 < n := by omega
    -- Double-counting:  ∑_s |attends s| = ∑_i |T i|.
    have hdouble :
        ∑ s : Fin (2*n), (attends T s).card = ∑ i : Fin k, (T i).card := by
      -- Use the indicator double-sum.
      classical
      have h1 :
          ∑ s : Fin (2*n), (attends T s).card =
            ∑ s : Fin (2*n), ∑ i : Fin k, if s ∈ T i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        rw [attends, Finset.card_filter]
      have h2 :
          ∑ i : Fin k, (T i).card =
            ∑ i : Fin k, ∑ s : Fin (2*n), if s ∈ T i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
            Nat.smul_one_eq_cast, Nat.cast_id]
      rw [h1, h2, Finset.sum_comm]
    -- Lower bound on LHS: each term ≥ 3.
    have hLHS : 6 * n ≤ ∑ s : Fin (2*n), (attends T s).card := by
      have h2n : (Finset.univ : Finset (Fin (2*n))).card = 2 * n := by
        rw [Finset.card_univ, Fintype.card_fin]
      calc 6 * n = (2 * n) * 3 := by ring
        _ = (Finset.univ : Finset (Fin (2*n))).card * 3 := by rw [h2n]
        _ = ∑ _s : Fin (2*n), 3 := by rw [Finset.sum_const]; ring
        _ ≤ ∑ s : Fin (2*n), (attends T s).card :=
            Finset.sum_le_sum (fun s _ => three_le_attends hn T hT s)
    -- Upper bound on RHS: each term = n.
    have hRHS : ∑ i : Fin k, (T i).card = k * n := by
      calc ∑ i : Fin k, (T i).card = ∑ _i : Fin k, n :=
            Finset.sum_congr rfl (fun i _ => hT.1 i)
        _ = k * n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
    rw [hdouble, hRHS] at hLHS
    -- 6 * n ≤ k * n, n > 0, so 6 ≤ k.
    exact Nat.le_of_mul_le_mul_right (by linarith) hpos

end Imc2013P3
