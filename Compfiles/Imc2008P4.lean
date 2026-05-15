/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics, .Algebra] }

/-!
# International Mathematical Competition 2008, Problem 4
(IMC 2008, Day 1, Problem 4)

A triple `(a₁, a₂, a₃)` of nonnegative real numbers is said to be *better* than
`(b₁, b₂, b₃)` if at least two of the strict inequalities `a₁ > b₁`,
`a₂ > b₂`, `a₃ > b₃` hold. A triple `(x, y, z)` is *special* if `x, y, z` are
nonnegative and `x + y + z = 1`.

Find all natural numbers `n` such that there exists a set `S` of `n` special
triples with the property that every special triple is "worse" than (i.e. has a
better triple in) `S`.

Answer: all `n ≥ 4`.
-/

namespace Imc2008P4

/-- A triple is *special* if its coordinates are nonnegative and sum to 1. -/
def IsSpecial (t : ℝ × ℝ × ℝ) : Prop :=
  0 ≤ t.1 ∧ 0 ≤ t.2.1 ∧ 0 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = 1

/-- A triple `a` is *better* than `b` if at least two strict coordinate
inequalities `a.i > b.i` hold. -/
def Better (a b : ℝ × ℝ × ℝ) : Prop :=
  (a.1 > b.1 ∧ a.2.1 > b.2.1) ∨ (a.1 > b.1 ∧ a.2.2 > b.2.2) ∨
    (a.2.1 > b.2.1 ∧ a.2.2 > b.2.2)

/-- The condition that a finite set `S` of special triples covers every special
triple via the better-relation. -/
def Covers (S : Finset (ℝ × ℝ × ℝ)) : Prop :=
  (∀ s ∈ S, IsSpecial s) ∧
    ∀ t : ℝ × ℝ × ℝ, IsSpecial t → ∃ s ∈ S, Better s t

snip begin

/-- The four explicit triples used in the n = 4 construction. -/
noncomputable def t1 : ℝ × ℝ × ℝ := (0, 8/15, 7/15)
noncomputable def t2 : ℝ × ℝ × ℝ := (2/5, 0, 3/5)
noncomputable def t3 : ℝ × ℝ × ℝ := (3/5, 2/5, 0)
noncomputable def t4 : ℝ × ℝ × ℝ := (2/15, 11/15, 2/15)

lemma isSpecial_t1 : IsSpecial t1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [t1] <;> norm_num

lemma isSpecial_t2 : IsSpecial t2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [t2] <;> norm_num

lemma isSpecial_t3 : IsSpecial t3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [t3] <;> norm_num

lemma isSpecial_t4 : IsSpecial t4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [t4] <;> norm_num

/-- The 4-element set covering every special triple. -/
noncomputable def S4 : Finset (ℝ × ℝ × ℝ) := {t1, t2, t3, t4}

/-- Adding one more arbitrary special triple to a covering set keeps it covering. -/
lemma Covers.insert {S : Finset (ℝ × ℝ × ℝ)} (hS : Covers S) {x : ℝ × ℝ × ℝ}
    (hx : IsSpecial x) : Covers (insert x S) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hx
    · exact hS.1 s hs
  · intro t ht
    obtain ⟨s, hsS, hsB⟩ := hS.2 t ht
    exact ⟨s, Finset.mem_insert.mpr (Or.inr hsS), hsB⟩

/-- The 4-triple example covers every special triple. (Hard direction —
case analysis on the position of `(x, y, z)` in the simplex; deferred.) -/
lemma covers_S4 : Covers S4 := by
  -- TODO: fill in the case analysis verifying that every special triple is
  -- dominated (in at least two coordinates) by one of t1, t2, t3, t4.
  sorry

/-- A parametrized family of special triples on the boundary, indexed by
`t ∈ [0, 1)`: `(t, 1 - t, 0)`. -/
noncomputable def boundaryTriple (t : ℝ) : ℝ × ℝ × ℝ := (t, 1 - t, 0)

lemma isSpecial_boundaryTriple {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsSpecial (boundaryTriple t) := by
  refine ⟨h0, ?_, le_refl _, ?_⟩
  · simp [boundaryTriple]; linarith
  · simp [boundaryTriple]

lemma boundaryTriple_injective : Function.Injective boundaryTriple := by
  intro a b h
  unfold boundaryTriple at h
  exact (Prod.mk.injEq _ _ _ _).mp h |>.1

/-- Given a finite set `S` of special triples that already covers, and any
target cardinality `m ≥ S.card`, we can extend `S` to a covering set of
cardinality exactly `m`. -/
lemma exists_covers_of_card_ge {S : Finset (ℝ × ℝ × ℝ)} (hS : Covers S)
    (m : ℕ) (hm : S.card ≤ m) :
    ∃ T : Finset (ℝ × ℝ × ℝ), T.card = m ∧ Covers T := by
  -- Pick m distinct boundary triples; combine with S; trim/extend as needed.
  -- Concretely: let A = (Finset.range m).image (fun i => boundaryTriple (i / (m + 1) : ℝ)).
  -- Then |S ∪ A| ≥ |A| = m. Take a subset of size m containing S.
  classical
  -- Use the family k ↦ boundaryTriple (k / (m + 1)) for k = 0, 1, ..., m.
  let f : ℕ → ℝ × ℝ × ℝ := fun k => boundaryTriple ((k : ℝ) / (m + 1 : ℝ))
  have hm1_pos : (0 : ℝ) < (m + 1 : ℝ) := by positivity
  have hf_inj : Function.Injective f := by
    intro a b hab
    have : ((a : ℝ) / (m + 1 : ℝ)) = ((b : ℝ) / (m + 1 : ℝ)) :=
      boundaryTriple_injective hab
    have := (div_left_inj' hm1_pos.ne').mp this
    exact_mod_cast this
  have hf_special : ∀ k ∈ Finset.range (m + 1), IsSpecial (f k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    apply isSpecial_boundaryTriple
    · positivity
    · rw [div_le_one hm1_pos]
      have : k ≤ m := Nat.le_of_lt_succ hk
      have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
      linarith
  let A : Finset (ℝ × ℝ × ℝ) := (Finset.range (m + 1)).image f
  have hA_card : A.card = m + 1 := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_range]
  -- Combined set covers (since S already covers).
  have hSA : Covers (S ∪ A) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact hS.1 s hs
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
        exact hf_special k hk
    · intro t ht
      obtain ⟨s, hsS, hsB⟩ := hS.2 t ht
      exact ⟨s, Finset.mem_union.mpr (Or.inl hsS), hsB⟩
  have hSA_card : m ≤ (S ∪ A).card := by
    have : A.card ≤ (S ∪ A).card := Finset.card_le_card Finset.subset_union_right
    omega
  -- Take a subset of S ∪ A of size m containing S.
  obtain ⟨T, hT_S, hT_sub, hT_card⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_union_left : S ⊆ S ∪ A)
      hm hSA_card
  refine ⟨T, hT_card, ?_, ?_⟩
  · intro s hs
    exact hSA.1 s (hT_sub hs)
  · intro t ht
    obtain ⟨s, hsS, hsB⟩ := hS.2 t ht
    exact ⟨s, hT_S hsS, hsB⟩

/-- No 3-element set of special triples can cover every special triple. -/
lemma not_covers_of_card_le_three {S : Finset (ℝ × ℝ × ℝ)}
    (hS_card : S.card ≤ 3) : ¬ Covers S := by
  -- TODO: extremal argument. Take the coordinatewise minima `(a, b, c)` over
  -- the triples in `S`; they sum to at most 1. After rescaling/transposition,
  -- exhibit an explicit special triple not dominated by any element of `S`.
  sorry

snip end

/-- The set of natural numbers `n` for which a valid configuration of size `n`
exists. -/
determine answer : Set ℕ := { n | 4 ≤ n }

problem imc2008_p4 :
    ∀ n : ℕ, n ∈ answer ↔ ∃ S : Finset (ℝ × ℝ × ℝ), S.card = n ∧ Covers S := by
  intro n
  constructor
  · -- n ≥ 4 ⟹ a valid set exists. Extend S4 with extra special triples.
    intro hn
    have hn' : 4 ≤ n := hn
    -- S4 has card 4 because t1, t2, t3, t4 are pairwise distinct.
    have hfst : ∀ {a b : ℝ × ℝ × ℝ}, a = b → a.1 = b.1 := fun h => by rw [h]
    have hsnd : ∀ {a b : ℝ × ℝ × ℝ}, a = b → a.2.1 = b.2.1 := fun h => by rw [h]
    have ht12 : t1 ≠ t2 := fun h => by
      have h1 : t1.1 = t2.1 := hfst h; unfold t1 t2 at h1; norm_num at h1
    have ht13 : t1 ≠ t3 := fun h => by
      have h1 : t1.1 = t3.1 := hfst h; unfold t1 t3 at h1; norm_num at h1
    have ht14 : t1 ≠ t4 := fun h => by
      have h1 : t1.1 = t4.1 := hfst h; unfold t1 t4 at h1; norm_num at h1
    have ht23 : t2 ≠ t3 := fun h => by
      have h1 : t2.1 = t3.1 := hfst h; unfold t2 t3 at h1; norm_num at h1
    have ht24 : t2 ≠ t4 := fun h => by
      have h1 : t2.2.1 = t4.2.1 := hsnd h; unfold t2 t4 at h1; norm_num at h1
    have ht34 : t3 ≠ t4 := fun h => by
      have h1 : t3.1 = t4.1 := hfst h; unfold t3 t4 at h1; norm_num at h1
    have hS4_card : S4.card = 4 := by
      simp [S4, Finset.card_insert_of_notMem, ht12, ht13, ht14, ht23, ht24, ht34]
    obtain ⟨T, hT_card, hT⟩ := exists_covers_of_card_ge covers_S4 n (by rw [hS4_card]; exact hn')
    exact ⟨T, hT_card, hT⟩
  · -- A valid set of size n forces n ≥ 4: by `not_covers_of_card_le_three`.
    rintro ⟨S, hS_card, hS⟩
    show 4 ≤ n
    by_contra hlt
    have hn_lt : n < 4 := by omega
    have : S.card ≤ 3 := by omega
    exact not_covers_of_card_le_three this hS

end Imc2008P4
