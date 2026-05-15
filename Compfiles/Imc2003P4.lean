/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Combinatorics] }

/-!
# International Mathematical Competition 2003, Problem 4
(IMC 2003, Day 1, Problem 4)

Find all pairs `(a, b)` of positive integers for which the set of positive
integers can be partitioned as `A ⊔ B` with `a · A = b · B`.

Answer: such a partition exists iff `a ≠ b` and (`a ∣ b` or `b ∣ a`).
-/

namespace Imc2003P4

/-- Predicate: there exists a partition of `ℤ⁺` as `A ⊔ B` with `aA = bB`. -/
def hasPartition (a b : ℕ) : Prop :=
  ∃ A B : Set ℕ,
    (∀ x ∈ A, 0 < x) ∧ (∀ x ∈ B, 0 < x) ∧
    A ∪ B = {n | 0 < n} ∧ A ∩ B = ∅ ∧
    (fun x => a * x) '' A = (fun x => b * x) '' B

/-- The answer: pairs `(a, b)` where `a ≠ b` and one divides the other. -/
determine answer : Set (ℕ × ℕ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ≠ p.2 ∧ (p.1 ∣ p.2 ∨ p.2 ∣ p.1)}

snip begin

/-- Parity of the `n`-adic valuation: number of times `n` divides `k`, mod 2.
For `n ≥ 2`, this is well-defined via strong recursion. For `k = 0` or `n ∤ k`
it returns `false` (treating "zero valuation" as even, i.e., "odd count" is `false`). -/
def vparity (n : ℕ) : ℕ → Bool := fun k =>
  if h : 2 ≤ n ∧ 0 < k ∧ n ∣ k then
    !(vparity n (k / n))
  else false
decreasing_by exact Nat.div_lt_self h.2.1 h.1

/-- Recurrence for `vparity`: when `2 ≤ n`, `0 < k`, and `n ∣ k`. -/
lemma vparity_step {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (hdvd : n ∣ k) :
    vparity n k = !(vparity n (k / n)) := by
  rw [vparity]
  rw [dif_pos ⟨hn, hk, hdvd⟩]

/-- Base case: `vparity n k = false` if `n ∤ k`. -/
lemma vparity_of_not_dvd {n k : ℕ} (hndvd : ¬ n ∣ k) :
    vparity n k = false := by
  rw [vparity]
  rw [dif_neg]
  rintro ⟨_, _, h⟩
  exact hndvd h

/-- Base case: `vparity n 0 = false`. -/
lemma vparity_zero (n : ℕ) : vparity n 0 = false := by
  rw [vparity]; rw [dif_neg]
  rintro ⟨_, h, _⟩; exact absurd h (by norm_num)

/-- When `2 ≤ n`, multiplying by `n` flips the parity: `vparity n (n * k) = !vparity n k`
for `k > 0`. -/
lemma vparity_mul {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) :
    vparity n (n * k) = !(vparity n k) := by
  have hnk : 0 < n * k := Nat.mul_pos (by omega) hk
  have hdvd : n ∣ n * k := ⟨k, rfl⟩
  have hdiv : (n * k) / n = k := by
    rw [Nat.mul_div_cancel_left _ (by omega : 0 < n)]
  rw [vparity_step hn hnk hdvd, hdiv]


/-- Main construction: for `n ≥ 2`, partition `ℤ⁺` by parity of `n`-adic valuation.
`A = {k : vparity n k = true}`, `B = {k : vparity n k = false and 0 < k}`.
Then `A ⊔ B = ℤ⁺` and `n · B = A` (i.e., `A = {n*k : k ∈ B}`). -/
noncomputable def partitionA (n : ℕ) : Set ℕ := {k | 0 < k ∧ vparity n k = true}

noncomputable def partitionB (n : ℕ) : Set ℕ := {k | 0 < k ∧ vparity n k = false}

lemma partitionA_pos (n : ℕ) : ∀ x ∈ partitionA n, 0 < x := fun _ hx => hx.1

lemma partitionB_pos (n : ℕ) : ∀ x ∈ partitionB n, 0 < x := fun _ hx => hx.1

lemma partitionA_union_B (n : ℕ) : partitionA n ∪ partitionB n = {k | 0 < k} := by
  ext k
  simp only [partitionA, partitionB, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hk
    by_cases h : vparity n k = true
    · left; exact ⟨hk, h⟩
    · right
      refine ⟨hk, ?_⟩
      cases hv : vparity n k
      · rfl
      · rw [hv] at h; exact absurd rfl h

lemma partitionA_inter_B (n : ℕ) : partitionA n ∩ partitionB n = ∅ := by
  ext k
  simp only [partitionA, partitionB, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  rw [h1] at h2; cases h2

/-- Key: multiplying `B` by `n` gives `A`. -/
lemma mul_partitionB_eq_A {n : ℕ} (hn : 2 ≤ n) :
    (fun x => n * x) '' partitionB n = partitionA n := by
  ext k
  simp only [Set.mem_image, partitionA, partitionB, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hx, hvx⟩, rfl⟩
    refine ⟨Nat.mul_pos (by omega) hx, ?_⟩
    rw [vparity_mul hn hx, hvx]; rfl
  · rintro ⟨hk, hvk⟩
    -- We need to show k = n * x for some x ∈ B.
    -- Since vparity n k = true, we have n ∣ k.
    have hdvd : n ∣ k := by
      by_contra h
      rw [vparity_of_not_dvd h] at hvk; cases hvk
    obtain ⟨x, hx⟩ := hdvd
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with hx0 | hxpos
      · exfalso; rw [hx0, mul_zero] at hx; omega
      · exact hxpos
    refine ⟨x, ⟨hxpos, ?_⟩, hx.symm⟩
    · -- vparity n x = false
      have hpp : vparity n k = !(vparity n x) := by
        rw [hx, vparity_mul hn hxpos]
      rw [hpp] at hvk
      cases hv : vparity n x
      · rfl
      · rw [hv] at hvk; simp at hvk

/-- The partition works: for `n ≥ 2`, `(1, n)` gives a valid partition with `1 · A = n · B`. -/
lemma hasPartition_one_n {n : ℕ} (hn : 2 ≤ n) : hasPartition 1 n := by
  refine ⟨partitionA n, partitionB n, partitionA_pos n, partitionB_pos n,
    partitionA_union_B n, partitionA_inter_B n, ?_⟩
  have h1 : (fun x => 1 * x) '' (partitionA n) = partitionA n := by
    ext k; simp
  rw [h1, ← mul_partitionB_eq_A hn]

/-- Scaling: if `(a, b)` admits a partition, so does `(ka, kb)` for `k ≥ 1`. -/
lemma hasPartition_scale {a b k : ℕ} (_hk : 0 < k) (h : hasPartition a b) :
    hasPartition (k * a) (k * b) := by
  obtain ⟨A, B, hA, hB, hUn, hIn, hAB⟩ := h
  refine ⟨A, B, hA, hB, hUn, hIn, ?_⟩
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hxA, rfl⟩
    -- y = k * a * x; need y = k * b * x' with x' ∈ B
    have hmem : a * x ∈ (fun x => a * x) '' A := ⟨x, hxA, rfl⟩
    rw [hAB] at hmem
    obtain ⟨x', hx'B, hx'eq⟩ := hmem
    refine ⟨x', hx'B, ?_⟩
    show k * b * x' = k * a * x
    have heq : b * x' = a * x := hx'eq
    calc k * b * x' = k * (b * x') := by ring
      _ = k * (a * x) := by rw [heq]
      _ = k * a * x := by ring
  · rintro ⟨x', hx'B, rfl⟩
    have hmem : b * x' ∈ (fun x => b * x) '' B := ⟨x', hx'B, rfl⟩
    rw [← hAB] at hmem
    obtain ⟨x, hxA, hxeq⟩ := hmem
    refine ⟨x, hxA, ?_⟩
    show k * a * x = k * b * x'
    have heq : a * x = b * x' := hxeq
    calc k * a * x = k * (a * x) := by ring
      _ = k * (b * x') := by rw [heq]
      _ = k * b * x' := by ring

/-- Symmetry: if `(a, b)` admits a partition, so does `(b, a)`. -/
lemma hasPartition_symm {a b : ℕ} (h : hasPartition a b) : hasPartition b a := by
  obtain ⟨A, B, hA, hB, hUn, hIn, hAB⟩ := h
  refine ⟨B, A, hB, hA, ?_, ?_, hAB.symm⟩
  · rw [Set.union_comm]; exact hUn
  · rw [Set.inter_comm]; exact hIn

snip end

problem imc2003_p4 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    hasPartition a b ↔ (a, b) ∈ answer := by
  show hasPartition a b ↔ (0 < a ∧ 0 < b ∧ a ≠ b ∧ (a ∣ b ∨ b ∣ a))
  constructor
  · -- Forward: hasPartition implies a ≠ b and one divides the other.
    rintro ⟨A, B, hApos, hBpos, hUn, hIn, hAB⟩
    refine ⟨ha, hb, ?_, ?_⟩
    · -- a ≠ b.
      intro hab
      -- If a = b, then a•A = a•B, so A = B (by injectivity).
      -- But A ∩ B = ∅ and A ∪ B is nonempty, contradiction.
      subst hab
      have hAeqB : A = B := by
        ext x
        constructor
        · intro hxA
          have : a * x ∈ (fun x => a * x) '' A := ⟨x, hxA, rfl⟩
          rw [hAB] at this
          obtain ⟨y, hyB, hy⟩ := this
          have hay : a * y = a * x := hy
          have : x = y := (Nat.eq_of_mul_eq_mul_left ha hay.symm)
          rw [this]; exact hyB
        · intro hxB
          have : a * x ∈ (fun x => a * x) '' B := ⟨x, hxB, rfl⟩
          rw [← hAB] at this
          obtain ⟨y, hyA, hy⟩ := this
          have hay : a * y = a * x := hy
          have : x = y := (Nat.eq_of_mul_eq_mul_left ha hay.symm)
          rw [this]; exact hyA
      -- 1 ∈ A ∪ B
      have h1 : (1 : ℕ) ∈ A ∪ B := by rw [hUn]; exact (by norm_num : (0 : ℕ) < 1)
      rcases h1 with h1A | h1B
      · have : (1 : ℕ) ∈ A ∩ B := ⟨h1A, hAeqB ▸ h1A⟩
        rw [hIn] at this; exact this.elim
      · have : (1 : ℕ) ∈ A ∩ B := ⟨hAeqB ▸ h1B, h1B⟩
        rw [hIn] at this; exact this.elim
    · -- a ∣ b ∨ b ∣ a.
      -- 1 ∈ A ∪ B.
      have h1 : (1 : ℕ) ∈ A ∪ B := by rw [hUn]; exact (by norm_num : (0 : ℕ) < 1)
      rcases h1 with h1A | h1B
      · -- 1 ∈ A, so a = a * 1 ∈ a•A = b•B, so b ∣ a.
        right
        have hmem : a * 1 ∈ (fun x => a * x) '' A := ⟨1, h1A, rfl⟩
        rw [hAB] at hmem
        obtain ⟨y, _, hy⟩ := hmem
        refine ⟨y, ?_⟩
        show a = b * y
        have heq : b * y = a * 1 := hy
        linarith [heq]
      · -- 1 ∈ B, so b = b * 1 ∈ b•B = a•A, so a ∣ b.
        left
        have hmem : b * 1 ∈ (fun x => b * x) '' B := ⟨1, h1B, rfl⟩
        rw [← hAB] at hmem
        obtain ⟨y, _, hy⟩ := hmem
        refine ⟨y, ?_⟩
        show b = a * y
        have heq : a * y = b * 1 := hy
        linarith [heq]
  · -- Backward: given answer, construct partition.
    rintro ⟨_, _, hab, hdvd⟩
    rcases hdvd with ⟨n, hn⟩ | ⟨n, hn⟩
    · -- a ∣ b: b = a * n, so (a, b) = (a * 1, a * n).
      -- Since a ≠ b, n ≠ 1, so n ≥ 2 (or n = 0, but then b = 0, contradiction).
      have hn_pos : 0 < n := by
        by_contra h
        push Not at h
        interval_cases n
        · rw [mul_zero] at hn; omega
      have hn_ne_1 : n ≠ 1 := by
        intro h
        rw [h, mul_one] at hn
        exact hab hn.symm
      have hn_ge_2 : 2 ≤ n := by omega
      have : hasPartition (a * 1) (a * n) := by
        exact hasPartition_scale ha (hasPartition_one_n hn_ge_2)
      rw [mul_one] at this
      rw [← hn] at this
      exact this
    · -- b ∣ a: a = b * n, symmetric.
      have hn_pos : 0 < n := by
        by_contra h
        push Not at h
        interval_cases n
        · rw [mul_zero] at hn; omega
      have hn_ne_1 : n ≠ 1 := by
        intro h
        rw [h, mul_one] at hn
        exact hab hn
      have hn_ge_2 : 2 ≤ n := by omega
      have : hasPartition (b * 1) (b * n) := by
        exact hasPartition_scale hb (hasPartition_one_n hn_ge_2)
      rw [mul_one] at this
      rw [← hn] at this
      exact hasPartition_symm this

end Imc2003P4
