/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 1997, Problem 6 (Day 1)

Let `F` be a family of finite subsets of `ℕ` such that for any two sets
`A, B ∈ F` the intersection `A ∩ B` is nonempty.

(a) Must there exist a finite set `Y ⊆ ℕ` such that
    `A ∩ B ∩ Y ≠ ∅` for all `A, B ∈ F`?

(b) Same question, but assuming additionally that all sets in `F` have the
    same cardinality.

## Answers

(a) **No**.  Counter-example: take
        `Aₙ = {1, 3, 5, …, 2n − 1, 2n}`,
        `Bₙ = {2, 4, 6, …, 2n,    2n + 1}`,
    and let `F = {Aₙ : n ≥ 1} ∪ {Bₙ : n ≥ 1}`.  Any two sets in this family
    intersect nontrivially (e.g. `Aₙ ∩ Bₙ = {2n}`), but no finite `Y` meets
    every pairwise intersection: if `max Y < 2n`, then `Aₙ ∩ Bₙ ∩ Y = ∅`.

(b) **Yes**.  We prove the stronger statement: if `F` and `G` are two
    families of finite subsets of `ℕ` such that every `A ∈ F` and every
    `B ∈ G` intersect, with `|A| = r` for all `A ∈ F` and `|B| = s` for all
    `B ∈ G`, then there is a finite `Y ⊆ ℕ` with `A ∩ B ∩ Y ≠ ∅` for all
    `A ∈ F`, `B ∈ G`.

    Proof by induction on `r + s`.  The base case `r = s = 1` is trivial
    (singletons in `F` and `G` must coincide).  Otherwise, fix `A₀ ∈ F` and
    `B₀ ∈ G`, and partition `F` and `G` by their traces on `A₀ ∪ B₀`:
    for nonempty `C, D ⊆ A₀ ∪ B₀`, set
        `F(C) = {A ∈ F : A ∩ (A₀ ∪ B₀) = C}`,
        `G(D) = {B ∈ G : B ∩ (A₀ ∪ B₀) = D}`.
    For each pair `(C, D)`: if `C ∩ D ≠ ∅`, take `Y_{C,D} = C`. Otherwise
    every `A ∈ F(C)`, `B ∈ G(D)` intersect *outside* `A₀ ∪ B₀`, so the
    families `{A \ C : A ∈ F(C)}` and `{B \ D : B ∈ G(D)}` have strictly
    smaller cardinalities (`r − |C|, s − |D|` with `|C|, |D| ≥ 1`), and the
    inductive hypothesis applies.  Take the (finite) union of all `Y_{C,D}`.

## Formalization notes

We use `Set (Finset ℕ)` to represent the family `F`, since each member is a
finite subset of `ℕ` but the family itself can be infinite.

The proof of (b) is a substantive double induction (on `r + s`, with a
non-trivial case-split on subsets of the finite "head" `A₀ ∪ B₀`); we leave
it as a `sorry` with the full roadmap above.
-/

namespace Imc1997P6

open Finset

/-- The pairwise-intersection hypothesis on a family. -/
def PairwiseInter (F : Set (Finset ℕ)) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → (A ∩ B).Nonempty

/-- "Y is a finite transversal of all pairwise intersections in F." -/
def IsTransversal (F : Set (Finset ℕ)) (Y : Finset ℕ) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → ((A ∩ B) ∩ Y).Nonempty

/-! ### Part (a): a counter-example. -/

/-- `Aₙ = {1, 3, 5, …, 2n − 1, 2n}` for `n ≥ 1`. -/
def Aset (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => 2 * i + 1) ∪ {2 * n}

/-- `Bₙ = {2, 4, 6, …, 2n, 2n + 1}` for `n ≥ 1`. -/
def Bset (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => 2 * i + 2) ∪ {2 * n + 1}

/-- The counter-example family for part (a). -/
def counterFamily : Set (Finset ℕ) :=
  {S | ∃ n, 1 ≤ n ∧ (S = Aset n ∨ S = Bset n)}

/-- Membership in `Aset n`. -/
lemma mem_Aset {n k : ℕ} :
    k ∈ Aset n ↔ (∃ i < n, k = 2 * i + 1) ∨ k = 2 * n := by
  simp only [Aset, Finset.mem_union, Finset.mem_image, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr rfl

/-- Membership in `Bset n`. -/
lemma mem_Bset {n k : ℕ} :
    k ∈ Bset n ↔ (∃ i < n, k = 2 * i + 2) ∨ k = 2 * n + 1 := by
  simp only [Bset, Finset.mem_union, Finset.mem_image, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr rfl

/-- `1 ∈ Aset n` whenever `n ≥ 1`. -/
lemma one_mem_Aset {n : ℕ} (hn : 1 ≤ n) : 1 ∈ Aset n := by
  rw [mem_Aset]
  exact Or.inl ⟨0, hn, rfl⟩

/-- `2 ∈ Bset n` whenever `n ≥ 1`. -/
lemma two_mem_Bset {n : ℕ} (hn : 1 ≤ n) : 2 ∈ Bset n := by
  rw [mem_Bset]
  exact Or.inl ⟨0, hn, rfl⟩

/-- The "top" element `2n` is always in `Aset n`. -/
lemma two_n_mem_Aset (n : ℕ) : 2 * n ∈ Aset n := by
  rw [mem_Aset]; exact Or.inr rfl

/-- The "top" element `2n+1` is always in `Bset n`. -/
lemma two_n_succ_mem_Bset (n : ℕ) : 2 * n + 1 ∈ Bset n := by
  rw [mem_Bset]; exact Or.inr rfl

/-- For `1 ≤ n ≤ m`, the even element `2n` lies in `Bset m`. -/
lemma two_n_mem_Bset_of_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : 2 * n ∈ Bset m := by
  rw [mem_Bset]
  refine Or.inl ⟨n - 1, ?_, ?_⟩
  · omega
  · omega

/-- For `m < n`, the odd element `2m+1` lies in `Aset n`. -/
lemma two_m_succ_mem_Aset_of_lt {m n : ℕ} (hmn : m < n) : 2 * m + 1 ∈ Aset n := by
  rw [mem_Aset]
  exact Or.inl ⟨m, hmn, rfl⟩

/-- The intersection `Aset n ∩ Bset n` equals `{2n}`. -/
lemma Aset_inter_Bset_self (n : ℕ) (hn : 1 ≤ n) :
    Aset n ∩ Bset n = {2 * n} := by
  ext k
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hA, hB⟩
    rw [mem_Aset] at hA
    rw [mem_Bset] at hB
    rcases hA with ⟨i, hi, rfl⟩ | rfl
    · -- k = 2i+1 odd; must equal even or 2n+1.
      rcases hB with ⟨j, hj, hij⟩ | hk
      · omega
      · omega
    · -- k = 2n; must be in Bset.
      rcases hB with ⟨j, hj, hj2⟩ | hk2
      · -- 2n = 2j+2, fine.  But result should be 2n; trivially.
        rfl
      · omega
  · rintro rfl
    refine ⟨two_n_mem_Aset n, two_n_mem_Bset_of_le hn (le_refl _)⟩

/-- Part (a): the answer is **no**. We exhibit a family `F` with pairwise
nonempty intersections, but admitting no finite transversal `Y`. -/
problem imc1997_p6_part_a :
    ∃ F : Set (Finset ℕ), PairwiseInter F ∧ ¬ ∃ Y : Finset ℕ, IsTransversal F Y := by
  refine ⟨counterFamily, ?_, ?_⟩
  · -- PairwiseInter.
    rintro A ⟨n, hn, rfl | rfl⟩ B ⟨m, hm, rfl | rfl⟩
    · -- Aset n ∩ Aset m: contains 1.
      exact ⟨1, Finset.mem_inter.mpr ⟨one_mem_Aset hn, one_mem_Aset hm⟩⟩
    · -- Aset n ∩ Bset m.
      rcases le_or_gt n m with hnm | hmn
      · exact ⟨2 * n, Finset.mem_inter.mpr
          ⟨two_n_mem_Aset n, two_n_mem_Bset_of_le hn hnm⟩⟩
      · exact ⟨2 * m + 1, Finset.mem_inter.mpr
          ⟨two_m_succ_mem_Aset_of_lt hmn, two_n_succ_mem_Bset m⟩⟩
    · -- Bset n ∩ Aset m.
      rcases le_or_gt m n with hmn | hnm
      · exact ⟨2 * m, Finset.mem_inter.mpr
          ⟨two_n_mem_Bset_of_le hm hmn, two_n_mem_Aset m⟩⟩
      · exact ⟨2 * n + 1, Finset.mem_inter.mpr
          ⟨two_n_succ_mem_Bset n, two_m_succ_mem_Aset_of_lt hnm⟩⟩
    · -- Bset n ∩ Bset m: contains 2.
      exact ⟨2, Finset.mem_inter.mpr ⟨two_mem_Bset hn, two_mem_Bset hm⟩⟩
  · -- No finite transversal.
    rintro ⟨Y, hY⟩
    -- Pick `n` so that `2n` is strictly larger than every element of `Y`.
    set N : ℕ := Y.sup id with hN_def
    -- Pick n so that 2 * n > N and n ≥ 1.
    obtain ⟨n, hn1, hnN⟩ : ∃ n : ℕ, 1 ≤ n ∧ N < 2 * n :=
      ⟨N + 1, by omega, by omega⟩
    have hAn : Aset n ∈ counterFamily := ⟨n, hn1, Or.inl rfl⟩
    have hBn : Bset n ∈ counterFamily := ⟨n, hn1, Or.inr rfl⟩
    obtain ⟨k, hk⟩ := hY hAn hBn
    rw [Finset.mem_inter] at hk
    obtain ⟨hkAB, hkY⟩ := hk
    -- Aset n ∩ Bset n = {2n}.
    rw [Aset_inter_Bset_self n hn1, Finset.mem_singleton] at hkAB
    subst hkAB
    -- `2*n ∈ Y` so `2*n ≤ Y.sup id = N`, contradicting `N < 2*n`.
    have h2n_le : (2 * n : ℕ) ≤ N := Finset.le_sup (f := id) hkY
    omega

/-! ### Part (b): same-size families do admit a transversal. -/

/-- Part (b): the answer is **yes** when all members of `F` have a common
finite cardinality `r`. -/
problem imc1997_p6_part_b
    (F : Set (Finset ℕ)) (hF : PairwiseInter F)
    (r : ℕ) (hsize : ∀ ⦃A⦄, A ∈ F → A.card = r) :
    ∃ Y : Finset ℕ, IsTransversal F Y := by
  -- TODO. Apply the more general two-family lemma (`twoFamilyTransversal`
  -- below) with `F = G` and `r = s`, choosing `Y` to be its output.
  sorry

/-! ### The strengthened lemma used in (b). -/

/-- The two-family strengthening, proved by induction on `r + s`.
This is the technical heart of part (b). -/
lemma twoFamilyTransversal :
    ∀ N : ℕ, ∀ (F G : Set (Finset ℕ)) (r s : ℕ),
      r + s ≤ N →
      (∀ ⦃A⦄, A ∈ F → A.card = r) →
      (∀ ⦃B⦄, B ∈ G → B.card = s) →
      (∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ G → (A ∩ B).Nonempty) →
      ∃ Y : Finset ℕ, ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ G → ((A ∩ B) ∩ Y).Nonempty := by
  -- TODO. Strong induction on `N`. The case-split:
  --
  -- 1. If `F = ∅` or `G = ∅`, take `Y = ∅` (the conclusion is vacuous).
  -- 2. If `r = 0` (so every `A ∈ F` is empty): pairwise non-emptiness fails
  --    unless `F = ∅`, already handled. (Symmetric for `s = 0`.)
  -- 3. Pick `A₀ ∈ F`, `B₀ ∈ G`. Let `H = A₀ ∪ B₀` (a finite set in `ℕ`).
  --    For each pair of nonempty `C ⊆ H`, `D ⊆ H` consider
  --      `F_C = {A ∈ F : A ∩ H = C}`,
  --      `G_D = {B ∈ G : B ∩ H = D}`.
  --    Note `F = ⋃_C F_C` (over nonempty `C ⊆ H`), since every `A ∈ F`
  --    meets `A₀` so `A ∩ H ⊇ A ∩ A₀ ≠ ∅`. Similarly `G = ⋃_D G_D`.
  --
  --    For each pair `(C, D)`:
  --      • If `C ∩ D ≠ ∅`, every pair `(A, B)` with `A ∈ F_C, B ∈ G_D`
  --        satisfies `(A ∩ B) ⊇ C ∩ D ≠ ∅`, and so any element of `C ∩ D`
  --        gives a transversal singleton: take `Y_{C,D} = C ∩ D`.
  --      • If `C ∩ D = ∅`, then for any `A ∈ F_C, B ∈ G_D`, the (nonempty)
  --        `A ∩ B` is disjoint from `H` (because `A ∩ H = C, B ∩ H = D`,
  --        and `C ∩ D = ∅`). Hence the families
  --          `F_C' = {A \ C : A ∈ F_C}` (each of cardinality `r − |C|`),
  --          `G_D' = {B \ D : B ∈ G_D}` (each of cardinality `s − |D|`),
  --        still have pairwise nonempty intersections (those intersections
  --        live outside `H`, so are unchanged by removing `C`, `D`).
  --        Since `|C|, |D| ≥ 1`, the new size sum is `< r + s ≤ N`, so the
  --        inductive hypothesis (with `N' = N − 1`) gives `Y_{C,D}'`.
  --        Take `Y_{C,D} = Y_{C,D}'`.
  --
  --    The finite union `Y = ⋃_{C,D ⊆ H, C, D ≠ ∅} Y_{C,D}` is the desired
  --    finite transversal: given any `A ∈ F, B ∈ G`, set `C = A ∩ H`,
  --    `D = B ∩ H`; then `(A ∩ B ∩ Y) ⊇ (A ∩ B ∩ Y_{C,D}) ≠ ∅`.
  sorry

end Imc1997P6
