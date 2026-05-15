/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2012, Problem 1

For every positive integer `n`, let `p(n)` denote the number of ways to express
`n` as a sum of positive integers. (For instance, `p(4) = 5`.) Also define
`p(0) = 1`. Prove that `p(n) - p(n-1)` is the number of ways to express `n` as
a sum of integers each strictly greater than `1`.
-/

namespace Imc2012P1

/-- `p n` is the number of partitions of `n`. -/
noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `q n` is the number of partitions of `n` with every part strictly greater than `1`. -/
noncomputable def q (n : ℕ) : ℕ :=
  ((Nat.Partition.restricted n (fun i => 2 ≤ i)) : Finset (Nat.Partition n)).card

snip begin

/-- Partitions of `n` with no part equal to `1` are exactly the partitions of `n`
    with every part at least `2`. -/
lemma mem_restricted_iff {n : ℕ} (π : Nat.Partition n) :
    π ∈ Nat.Partition.restricted n (fun i => 2 ≤ i) ↔ ∀ i ∈ π.parts, i ≠ 1 := by
  unfold Nat.Partition.restricted
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    have := h i hi
    omega
  · intro h i hi
    have hpos := π.parts_pos hi
    have hne := h i hi
    omega

/-- Add a `1` to a partition of `n-1` to get a partition of `n` (for `n ≥ 1`). -/
def addOne {n : ℕ} (hn : 1 ≤ n) (π : Nat.Partition (n - 1)) : Nat.Partition n where
  parts := 1 ::ₘ π.parts
  parts_pos := by
    intro i hi
    rw [Multiset.mem_cons] at hi
    rcases hi with h1 | h2
    · omega
    · exact π.parts_pos h2
  parts_sum := by
    rw [Multiset.sum_cons, π.parts_sum]
    omega

/-- Remove a `1` from a partition of `n` containing a `1`. -/
def removeOne {n : ℕ} (π : Nat.Partition n) (h : 1 ∈ π.parts) : Nat.Partition (n - 1) where
  parts := π.parts.erase 1
  parts_pos := by
    intro i hi
    have : i ∈ π.parts := Multiset.mem_of_mem_erase hi
    exact π.parts_pos this
  parts_sum := by
    have hsum := π.parts_sum
    have : (π.parts.erase 1).sum + 1 = π.parts.sum := by
      have hcons : 1 ::ₘ π.parts.erase 1 = π.parts := Multiset.cons_erase h
      have := congrArg Multiset.sum hcons
      rw [Multiset.sum_cons] at this
      omega
    omega

/-- Partitions of `n` decompose into those containing a `1` and those not containing a `1`. -/
lemma card_split (n : ℕ) :
    Fintype.card (Nat.Partition n) =
      (Finset.univ.filter (fun π : Nat.Partition n => 1 ∈ π.parts)).card +
      (Finset.univ.filter (fun π : Nat.Partition n => 1 ∉ π.parts)).card := by
  rw [← Finset.card_univ]
  exact (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Nat.Partition n))) (p := fun π => 1 ∈ π.parts)).symm

/-- Bijection between partitions of `n` containing a `1` and partitions of `n-1`. -/
noncomputable def containsOneEquiv {n : ℕ} (hn : 1 ≤ n) :
    {π : Nat.Partition n // 1 ∈ π.parts} ≃ Nat.Partition (n - 1) where
  toFun := fun ⟨π, hπ⟩ => removeOne π hπ
  invFun := fun π => ⟨addOne hn π, by unfold addOne; simp⟩
  left_inv := by
    rintro ⟨π, hπ⟩
    apply Subtype.ext
    apply Nat.Partition.ext
    show (addOne hn (removeOne π hπ)).parts = π.parts
    unfold addOne removeOne
    simp
    exact Multiset.cons_erase hπ
  right_inv := by
    intro π
    apply Nat.Partition.ext
    show (removeOne (addOne hn π) _).parts = π.parts
    unfold addOne removeOne
    simp

lemma card_contains_one {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter (fun π : Nat.Partition n => 1 ∈ π.parts)).card =
      Fintype.card (Nat.Partition (n - 1)) := by
  have h1 : (Finset.univ.filter (fun π : Nat.Partition n => 1 ∈ π.parts)).card =
      Fintype.card {π : Nat.Partition n // 1 ∈ π.parts} := by
    rw [Fintype.card_subtype]
  rw [h1]
  exact Fintype.card_congr (containsOneEquiv hn)

lemma card_no_one (n : ℕ) :
    (Finset.univ.filter (fun π : Nat.Partition n => 1 ∉ π.parts)).card = q n := by
  unfold q Nat.Partition.restricted
  congr 1
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i hi
    have hpos := π.parts_pos hi
    by_contra hne
    push Not at hne
    interval_cases i
    · exact h hi
  · intro h h1
    have := h 1 h1
    omega

snip end

problem imc2012_p1 (n : ℕ) (hn : 1 ≤ n) :
    p n = p (n - 1) + q n := by
  unfold p
  rw [card_split n, card_contains_one hn, card_no_one]

end Imc2012P1
