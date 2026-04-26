/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2005, Problem 2

For `n ≥ 3`, let `S_n = {0, 1, 2}^n`,
`A_n = {x ∈ S_n : |{x_i, x_{i+1}, x_{i+2}}| ≠ 1 for all i ≤ n-2}`, and
`B_n = {x ∈ S_n : x_i = x_{i+1} ⇒ x_i ≠ 0}`. Prove `|A_{n+1}| = 3 |B_n|`.

We use `0`-based indexing and identify `{0,1,2}` with `ZMod 3`.
-/

namespace Imc2005P2

open Finset

/-- `A n` is the set of sequences in `(ZMod 3)^n` with no three consecutive equal entries. -/
def A (n : ℕ) : Finset (Fin n → ZMod 3) :=
  univ.filter (fun x => ∀ i ∈ range n, ∀ h2 : i + 2 < n,
    ¬ (x ⟨i, by omega⟩ = x ⟨i + 1, by omega⟩ ∧ x ⟨i, by omega⟩ = x ⟨i + 2, h2⟩))

/-- `B n` is the set of sequences in `(ZMod 3)^n` such that two consecutive equal
entries are not 0. -/
def B (n : ℕ) : Finset (Fin n → ZMod 3) :=
  univ.filter (fun y => ∀ i ∈ range n, ∀ h1 : i + 1 < n,
    y ⟨i, by omega⟩ = y ⟨i + 1, h1⟩ → y ⟨i, by omega⟩ ≠ 0)

snip begin

/-- Forward map: given `(c, y) ∈ ZMod 3 × B n`, build `x : Fin (n+1) → ZMod 3`
with `x 0 = c` and `x (i+1) = x i + y i`. Concretely
`x ⟨k, _⟩ = c + ∑_{j < k} y j`. -/
def buildSeq (n : ℕ) (c : ZMod 3) (y : Fin n → ZMod 3) : Fin (n + 1) → ZMod 3 :=
  fun k => c + ∑ j ∈ univ.filter (fun j : Fin n => j.val < k.val), y j

/-- Inverse map: given `x : Fin (n+1) → ZMod 3`, define `y i = x (i+1) - x i`. -/
def diffSeq (n : ℕ) (x : Fin (n + 1) → ZMod 3) : Fin n → ZMod 3 :=
  fun i => x ⟨i.val + 1, by omega⟩ - x ⟨i.val, by omega⟩

lemma buildSeq_zero (n : ℕ) (c : ZMod 3) (y : Fin n → ZMod 3) :
    buildSeq n c y ⟨0, by omega⟩ = c := by
  simp [buildSeq]

lemma buildSeq_succ (n : ℕ) (c : ZMod 3) (y : Fin n → ZMod 3) (k : ℕ)
    (hk : k + 1 < n + 1) :
    buildSeq n c y ⟨k + 1, hk⟩ =
      buildSeq n c y ⟨k, by omega⟩ + y ⟨k, by omega⟩ := by
  unfold buildSeq
  have hk' : k < n := by omega
  set s1 : Finset (Fin n) := univ.filter (fun j : Fin n => j.val < k + 1)
  set s2 : Finset (Fin n) := univ.filter (fun j : Fin n => j.val < k)
  have hk_nmem : (⟨k, hk'⟩ : Fin n) ∉ s2 := by simp [s2]
  have hs1 : s1 = insert (⟨k, hk'⟩ : Fin n) s2 := by
    ext j
    simp only [s1, s2, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
      · exact Or.inr h
      · left; exact Fin.ext h
    · rintro (rfl | h)
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  rw [hs1, sum_insert hk_nmem]
  ring

lemma buildSeq_diff_at (n : ℕ) (c : ZMod 3) (y : Fin n → ZMod 3) (k : ℕ) (hk : k < n) :
    buildSeq n c y ⟨k + 1, by omega⟩ - buildSeq n c y ⟨k, by omega⟩ = y ⟨k, hk⟩ := by
  rw [buildSeq_succ n c y k (by omega)]
  ring

lemma diffSeq_buildSeq (n : ℕ) (c : ZMod 3) (y : Fin n → ZMod 3) :
    diffSeq n (buildSeq n c y) = y := by
  funext i
  unfold diffSeq
  have h := buildSeq_diff_at n c y i.val i.isLt
  have e3 : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
  rw [← e3]
  exact h

lemma buildSeq_diffSeq (n : ℕ) (x : Fin (n + 1) → ZMod 3) :
    buildSeq n (x ⟨0, by omega⟩) (diffSeq n x) = x := by
  funext k
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => simpa using buildSeq_zero n (x ⟨0, by omega⟩) (diffSeq n x)
  | succ m ih =>
    have hm : m + 1 < n + 1 := hk
    have hm' : m < n + 1 := by omega
    have hmn : m < n := by omega
    rw [buildSeq_succ n (x ⟨0, by omega⟩) (diffSeq n x) m hm]
    rw [ih hm']
    show x ⟨m, hm'⟩ + diffSeq n x ⟨m, hmn⟩ = x ⟨m + 1, hm⟩
    unfold diffSeq
    show x ⟨m, hm'⟩ + (x ⟨m + 1, by omega⟩ - x ⟨m, by omega⟩) = x ⟨m + 1, hm⟩
    ring

/-- The buildSeq map sends valid `(c, y) ∈ ZMod 3 × B n` into `A (n+1)`. -/
lemma buildSeq_mem_A (n : ℕ) (c : ZMod 3) (y : Fin n → ZMod 3) (hy : y ∈ B n) :
    buildSeq n c y ∈ A (n + 1) := by
  unfold B at hy
  unfold A
  rw [mem_filter] at hy
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  obtain ⟨_, hy⟩ := hy
  intro i hi h2
  rintro ⟨he1, he2⟩
  have hin : i < n := by omega
  have hi1n : i + 1 < n := by omega
  -- y i = 0 from x i = x (i+1)
  have hd_i : buildSeq n c y ⟨i + 1, by omega⟩ - buildSeq n c y ⟨i, by omega⟩ = y ⟨i, hin⟩ :=
    buildSeq_diff_at n c y i hin
  have hzero1 : buildSeq n c y ⟨i + 1, by omega⟩ - buildSeq n c y ⟨i, by omega⟩ = 0 := by
    rw [he1]; ring
  have hy_i : y ⟨i, hin⟩ = 0 := by rw [← hd_i]; exact hzero1
  -- y (i+1) = 0 from x (i+1) = x (i+2). x (i+1) = x i (from he1) and x i = x (i+2) (from he2).
  have hd_i1 : buildSeq n c y ⟨(i + 1) + 1, by omega⟩ - buildSeq n c y ⟨i + 1, by omega⟩
      = y ⟨i + 1, hi1n⟩ := buildSeq_diff_at n c y (i + 1) hi1n
  have h_i2 : (⟨i + 2, h2⟩ : Fin (n+1)) = ⟨(i + 1) + 1, by omega⟩ := by
    apply Fin.ext
    show i + 2 = (i + 1) + 1
    omega
  have hzero2 : buildSeq n c y ⟨(i + 1) + 1, by omega⟩ - buildSeq n c y ⟨i + 1, by omega⟩ = 0 := by
    have e1 : buildSeq n c y ⟨i + 1, by omega⟩ = buildSeq n c y ⟨i, by omega⟩ := he1.symm
    have e2 : buildSeq n c y ⟨(i + 1) + 1, by omega⟩ = buildSeq n c y ⟨i, by omega⟩ := by
      rw [show (⟨(i + 1) + 1, by omega⟩ : Fin (n+1)) = ⟨i + 2, h2⟩ from by apply Fin.ext; omega]
      exact he2.symm
    rw [e1, e2]; ring
  have hy_i1 : y ⟨i + 1, hi1n⟩ = 0 := by rw [← hd_i1]; exact hzero2
  have heq : y ⟨i, hin⟩ = y ⟨i + 1, hi1n⟩ := by rw [hy_i, hy_i1]
  exact hy i (mem_range.mpr hin) hi1n heq hy_i

/-- The diffSeq map sends valid `x ∈ A (n+1)` to `diffSeq x ∈ B n`. -/
lemma diffSeq_mem_B (n : ℕ) (x : Fin (n + 1) → ZMod 3) (hx : x ∈ A (n + 1)) :
    diffSeq n x ∈ B n := by
  unfold A at hx
  unfold B
  rw [mem_filter] at hx
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  obtain ⟨_, hx⟩ := hx
  intro i hi h1 heq h0
  -- diffSeq n x ⟨i, _⟩ = 0 means x (i+1) = x i.
  -- diffSeq n x ⟨i, _⟩ = diffSeq n x ⟨i+1, _⟩ = 0 means also x (i+2) = x (i+1) = x i.
  have hin1 : i < n + 1 := by omega
  have hi2 : i + 2 < n + 1 := by omega
  have h0' : x ⟨i + 1, by omega⟩ - x ⟨i, by omega⟩ = 0 := h0
  have h_eq_01 : x ⟨i, by omega⟩ = x ⟨i + 1, by omega⟩ := by linear_combination -h0'
  -- diffSeq n x ⟨i + 1, h1⟩ = 0 too
  have h0'' : diffSeq n x ⟨i + 1, h1⟩ = 0 := heq.symm.trans h0
  have h0''' : x ⟨(i + 1) + 1, by omega⟩ - x ⟨i + 1, by omega⟩ = 0 := h0''
  have h_eq_12 : x ⟨i + 1, by omega⟩ = x ⟨(i + 1) + 1, by omega⟩ := by linear_combination -h0'''
  have h_i2_eq : (⟨(i + 1) + 1, by omega⟩ : Fin (n+1)) = ⟨i + 2, hi2⟩ := by
    apply Fin.ext
    show (i + 1) + 1 = i + 2
    omega
  -- Apply hx at i.
  have hi_n1 : i ∈ range (n + 1) := mem_range.mpr (by omega)
  exact hx i hi_n1 hi2 ⟨h_eq_01, by rw [h_eq_01, h_eq_12, h_i2_eq]⟩

/-- The bijection `ZMod 3 × B n ≃ A (n+1)`. -/
def equivAB (n : ℕ) : (ZMod 3 × B n) ≃ A (n + 1) where
  toFun := fun p => ⟨buildSeq n p.1 p.2.1, buildSeq_mem_A n p.1 p.2.1 p.2.2⟩
  invFun := fun x => (x.1 ⟨0, by omega⟩, ⟨diffSeq n x.1, diffSeq_mem_B n x.1 x.2⟩)
  left_inv := by
    rintro ⟨c, y, hy⟩
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, ?_⟩
    · exact buildSeq_zero n c y
    · exact diffSeq_buildSeq n c y
  right_inv := by
    rintro ⟨x, hx⟩
    simp only [Subtype.mk.injEq]
    exact buildSeq_diffSeq n x

snip end

problem imc2005_p2 (n : ℕ) : (A (n + 1)).card = 3 * (B n).card := by
  have h := Fintype.card_congr (equivAB n)
  rw [Fintype.card_prod] at h
  have h1 : Fintype.card (ZMod 3) = 3 := by decide
  rw [h1] at h
  have hA : Fintype.card (A (n + 1)) = (A (n + 1)).card := Fintype.card_coe _
  have hB : Fintype.card (B n) = (B n).card := Fintype.card_coe _
  rw [hA, hB] at h
  linarith

end Imc2005P2
