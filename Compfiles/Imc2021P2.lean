/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2021, Problem 2

Let `n` and `k` be fixed positive integers, and let `a` be an arbitrary
non-negative integer. Choose a random `k`-element subset `X` of
`{1, 2, …, k + a}` uniformly, and independently a random `n`-element
subset `Y` of `{1, …, k + n + a}` uniformly. Prove that
`P(min(Y) > max(X))` does not depend on `a`.

We express the "probability" concretely as a ratio of finite cardinalities.
The claim is that

  (# favorable pairs) / (|X-space| · |Y-space|) = 1 / C(n+k, k),

independent of `a`.
-/

namespace Imc2021P2

open Finset

/-- The set of pairs `(X, Y)` where `X` is a `k`-subset of `Icc 1 (k+a)` and
`Y` is an `n`-subset of `Icc 1 (k+n+a)`. -/
noncomputable def allPairs (n k a : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((Icc 1 (k + a)).powersetCard k) ×ˢ ((Icc 1 (k + n + a)).powersetCard n)

/-- The subset of `allPairs` for which `max X < min Y`. -/
noncomputable def goodPairs (n k a : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (allPairs n k a).filter (fun p => p.1.max < p.2.min)

snip begin

/-- Translate the `max < min` condition into a comparison of `max'`/`min'`. -/
lemma max_lt_min_iff_max'_lt_min' {X Y : Finset ℕ} (hXne : X.Nonempty) (hYne : Y.Nonempty) :
    X.max < Y.min ↔ X.max' hXne < Y.min' hYne := by
  constructor
  · intro h
    by_contra hc
    have hc' : Y.min' hYne ≤ X.max' hXne := not_lt.mp hc
    have hlt : (X.max' hXne : WithBot ℕ) < (Y.min' hYne : WithBot ℕ) := by
      rw [← Finset.coe_max' hXne] at h
      have hmin_eq : Y.min = ((Y.min' hYne : ℕ) : WithBot ℕ) := by
        rw [← Finset.coe_min' hYne]; rfl
      rw [hmin_eq] at h
      exact h
    exact absurd (WithBot.coe_lt_coe.mp hlt) (not_lt.mpr hc')
  · intro h
    rw [← Finset.coe_max' hXne]
    have hmin_eq : Y.min = ((Y.min' hYne : ℕ) : WithBot ℕ) := by
      rw [← Finset.coe_min' hYne]; rfl
    rw [hmin_eq]
    exact WithBot.coe_lt_coe.mpr h

/-- Split a finite set `S ⊆ ℕ` into the `k` smallest elements and the rest. -/
noncomputable def splitAt (k : ℕ) (S : Finset ℕ) : Finset ℕ × Finset ℕ :=
  (S.filter (fun x => (S.filter (· ≤ x)).card ≤ k),
   S.filter (fun x => k < (S.filter (· ≤ x)).card))

lemma splitAt_fst (k : ℕ) (S : Finset ℕ) :
    (splitAt k S).1 = S.filter (fun x => (S.filter (· ≤ x)).card ≤ k) := rfl

lemma splitAt_snd (k : ℕ) (S : Finset ℕ) :
    (splitAt k S).2 = S.filter (fun x => k < (S.filter (· ≤ x)).card) := rfl

lemma splitAt_disjoint (k : ℕ) (S : Finset ℕ) :
    Disjoint (splitAt k S).1 (splitAt k S).2 := by
  rw [splitAt_fst, splitAt_snd, disjoint_filter]
  intro x _ h; omega

lemma splitAt_union (k : ℕ) (S : Finset ℕ) :
    (splitAt k S).1 ∪ (splitAt k S).2 = S := by
  rw [splitAt_fst, splitAt_snd]
  ext x
  simp only [mem_union, mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hx
    by_cases h : (S.filter (· ≤ x)).card ≤ k
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, by omega⟩

lemma splitAt_subset_left (k : ℕ) (S : Finset ℕ) : (splitAt k S).1 ⊆ S := by
  rw [splitAt_fst]; exact filter_subset _ _

lemma splitAt_subset_right (k : ℕ) (S : Finset ℕ) : (splitAt k S).2 ⊆ S := by
  rw [splitAt_snd]; exact filter_subset _ _

/-- Every element of the "small" part is strictly less than every element of the "large" part. -/
lemma splitAt_lt (k : ℕ) (S : Finset ℕ) :
    ∀ x ∈ (splitAt k S).1, ∀ y ∈ (splitAt k S).2, x < y := by
  intro x hx y hy
  rw [splitAt_fst] at hx
  rw [splitAt_snd] at hy
  simp only [mem_filter] at hx hy
  obtain ⟨hxS, hx⟩ := hx
  obtain ⟨hyS, hy⟩ := hy
  by_contra hxy
  rw [not_lt] at hxy
  -- y ≤ x, so {z ∈ S | z ≤ y} ⊆ {z ∈ S | z ≤ x}
  have : (S.filter (· ≤ y)).card ≤ (S.filter (· ≤ x)).card := by
    apply card_le_card
    intro z hz
    simp only [mem_filter] at hz ⊢
    exact ⟨hz.1, le_trans hz.2 hxy⟩
  omega

/-- Rank function is injective on S. -/
lemma rank_injOn (S : Finset ℕ) :
    Set.InjOn (fun x => (S.filter (· ≤ x)).card) (S : Set ℕ) := by
  intro x hx y hy hxy
  simp only [mem_coe] at hx hy
  rcases lt_trichotomy x y with h | h | h
  · exfalso
    have : (S.filter (· ≤ x)).card < (S.filter (· ≤ y)).card := by
      apply card_lt_card
      refine ⟨?_, ?_⟩
      · intro z hz; simp only [mem_filter] at hz ⊢
        exact ⟨hz.1, le_trans hz.2 h.le⟩
      · intro hsub'
        have : y ∈ S.filter (· ≤ x) := hsub' (mem_filter.2 ⟨hy, le_refl _⟩)
        have hyx : y ≤ x := (mem_filter.1 this).2
        omega
    simp only at hxy
    omega
  · exact h
  · exfalso
    have : (S.filter (· ≤ y)).card < (S.filter (· ≤ x)).card := by
      apply card_lt_card
      refine ⟨?_, ?_⟩
      · intro z hz; simp only [mem_filter] at hz ⊢
        exact ⟨hz.1, le_trans hz.2 h.le⟩
      · intro hsub'
        have : x ∈ S.filter (· ≤ y) := hsub' (mem_filter.2 ⟨hx, le_refl _⟩)
        have hxy' : x ≤ y := (mem_filter.1 this).2
        omega
    simp only at hxy
    omega

/-- Rank function takes values in 1..|S| for x ∈ S. -/
lemma rank_mem_Icc (S : Finset ℕ) (x : ℕ) (hx : x ∈ S) :
    1 ≤ (S.filter (· ≤ x)).card ∧ (S.filter (· ≤ x)).card ≤ S.card := by
  refine ⟨?_, ?_⟩
  · rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
    exact ⟨x, mem_filter.2 ⟨hx, le_refl _⟩⟩
  · exact card_le_card (filter_subset _ _)

/-- When `S.card = n + k`, the split has exactly `k` elements on the left and `n` on the right. -/
lemma splitAt_card_of_size {n k : ℕ} (S : Finset ℕ) (hS : S.card = n + k) :
    (splitAt k S).1.card = k ∧ (splitAt k S).2.card = n := by
  classical
  -- Left: bounded by k via rank ∈ {1..k}
  have hleft : (splitAt k S).1.card ≤ k := by
    let r : ℕ → ℕ := fun x => (S.filter (· ≤ x)).card - 1
    have hsubS : (splitAt k S).1 ⊆ S := splitAt_subset_left k S
    have hinj : Set.InjOn r ((splitAt k S).1 : Set ℕ) := by
      intro x hx y hy hxy
      simp only [mem_coe] at hx hy
      have hxS := hsubS hx
      have hyS := hsubS hy
      have hrinj := rank_injOn S (show x ∈ (S : Set ℕ) by simpa using hxS)
        (show y ∈ (S : Set ℕ) by simpa using hyS)
      have h1 := (rank_mem_Icc S x hxS).1
      have h2 := (rank_mem_Icc S y hyS).1
      simp only [r] at hxy
      apply hrinj
      show (S.filter (· ≤ x)).card = (S.filter (· ≤ y)).card
      omega
    have hmap : Set.MapsTo r ((splitAt k S).1 : Set ℕ) (range k : Set ℕ) := by
      intro x hx
      simp only [mem_coe, splitAt_fst, mem_filter] at hx
      simp only [mem_coe, mem_range, r]
      have := (rank_mem_Icc S x hx.1).1
      omega
    have : (splitAt k S).1.card ≤ (range k).card := by
      have := Finset.card_le_card_of_injOn r (fun x hx => hmap hx) hinj
      exact this
    simpa using this
  -- Right: bounded by n via rank ∈ {k+1..n+k}
  have hright : (splitAt k S).2.card ≤ n := by
    let r : ℕ → ℕ := fun x => (S.filter (· ≤ x)).card - (k + 1)
    have hsubS : (splitAt k S).2 ⊆ S := splitAt_subset_right k S
    have hinj : Set.InjOn r ((splitAt k S).2 : Set ℕ) := by
      intro x hx y hy hxy
      simp only [mem_coe] at hx hy
      have hxS := hsubS hx
      have hyS := hsubS hy
      have hxgt : k < (S.filter (· ≤ x)).card := by
        have : x ∈ (splitAt k S).2 := hx
        rw [splitAt_snd, mem_filter] at this
        exact this.2
      have hygt : k < (S.filter (· ≤ y)).card := by
        have : y ∈ (splitAt k S).2 := hy
        rw [splitAt_snd, mem_filter] at this
        exact this.2
      simp only [r] at hxy
      apply rank_injOn S (show x ∈ (S : Set ℕ) by simpa using hxS)
        (show y ∈ (S : Set ℕ) by simpa using hyS)
      show (S.filter (· ≤ x)).card = (S.filter (· ≤ y)).card
      omega
    have hmap : Set.MapsTo r ((splitAt k S).2 : Set ℕ) (range n : Set ℕ) := by
      intro x hx
      simp only [mem_coe, splitAt_snd, mem_filter] at hx
      simp only [mem_coe, mem_range, r]
      have hxS := hx.1
      have hgt := hx.2
      have hle := (rank_mem_Icc S x hxS).2
      rw [hS] at hle
      omega
    have : (splitAt k S).2.card ≤ (range n).card := by
      exact Finset.card_le_card_of_injOn r (fun x hx => hmap hx) hinj
    simpa using this
  -- Total = n+k
  have hsum : (splitAt k S).1.card + (splitAt k S).2.card = n + k := by
    rw [← card_union_of_disjoint (splitAt_disjoint k S), splitAt_union, hS]
  refine ⟨?_, ?_⟩ <;> omega

/-- For `S ⊆ Icc 1 (k+n+a)` of size `n+k`, `(splitAt k S).1 ⊆ Icc 1 (k+a)`. -/
lemma splitAt_left_subset_Icc {n k a : ℕ} (S : Finset ℕ) (hS : S.card = n + k)
    (hSub : S ⊆ Icc 1 (k + n + a)) :
    (splitAt k S).1 ⊆ Icc 1 (k + a) := by
  intro x hx
  have hxS : x ∈ S := splitAt_subset_left k S hx
  have hxIcc : x ∈ Icc 1 (k + n + a) := hSub hxS
  simp only [mem_Icc] at hxIcc ⊢
  refine ⟨hxIcc.1, ?_⟩
  by_contra hxgt
  rw [not_le] at hxgt
  have hn_right : (splitAt k S).2.card = n := (splitAt_card_of_size S hS).2
  have hcount : (splitAt k S).2 ⊆ Icc (x + 1) (k + n + a) := by
    intro y hy
    have hyS : y ∈ S := splitAt_subset_right k S hy
    have hyIcc : y ∈ Icc 1 (k + n + a) := hSub hyS
    have hxy : x < y := splitAt_lt k S x hx y hy
    simp only [mem_Icc] at hyIcc ⊢
    exact ⟨hxy, hyIcc.2⟩
  have := card_le_card hcount
  rw [hn_right, Nat.card_Icc] at this
  omega

/-- max of small part is less than min of large part. -/
lemma splitAt_max_lt_min {n k : ℕ} (S : Finset ℕ) (hS : S.card = n + k)
    (hk : 0 < k) (hn : 0 < n) :
    (splitAt k S).1.max < (splitAt k S).2.min := by
  have h1 : (splitAt k S).1.card = k := (splitAt_card_of_size S hS).1
  have h2 : (splitAt k S).2.card = n := (splitAt_card_of_size S hS).2
  have hne1 : (splitAt k S).1.Nonempty := card_pos.mp (by omega)
  have hne2 : (splitAt k S).2.Nonempty := card_pos.mp (by omega)
  rw [max_lt_min_iff_max'_lt_min' hne1 hne2]
  exact splitAt_lt k S _ (Finset.max'_mem _ hne1) _ (Finset.min'_mem _ hne2)

/-- Reconstruction lemma: `splitAt k (X ∪ Y) = (X, Y)` when `X.card = k` and `max X < min Y`. -/
lemma splitAt_union_eq {X Y : Finset ℕ} {k : ℕ} (hX : X.card = k)
    (hmax : X.max < Y.min) :
    splitAt k (X ∪ Y) = (X, Y) := by
  classical
  -- Every x ∈ X is strictly less than every y ∈ Y.
  have hlt_elems : ∀ x ∈ X, ∀ y ∈ Y, x < y := by
    intro x hxX y hyY
    have hXne : X.Nonempty := ⟨x, hxX⟩
    have hYne : Y.Nonempty := ⟨y, hyY⟩
    have hlt := (max_lt_min_iff_max'_lt_min' hXne hYne).mp hmax
    have hxx : x ≤ X.max' hXne := X.le_max' x hxX
    have hyy : Y.min' hYne ≤ y := Y.min'_le y hyY
    omega
  have hdisj : Disjoint X Y := by
    rw [disjoint_left]
    intro x hxX hxY
    exact lt_irrefl x (hlt_elems x hxX x hxY)
  have key_X : ∀ z ∈ X, ((X ∪ Y).filter (· ≤ z)).card ≤ k := by
    intro z hzX
    have hsub : (X ∪ Y).filter (· ≤ z) ⊆ X := by
      intro w hw
      simp only [mem_filter, mem_union] at hw
      rcases hw.1 with hwX | hwY
      · exact hwX
      · exfalso
        have := hlt_elems z hzX w hwY
        have : w ≤ z := hw.2
        have h2 := hlt_elems z hzX w hwY
        omega
    calc ((X ∪ Y).filter (· ≤ z)).card ≤ X.card := card_le_card hsub
      _ = k := hX
  have key_Y : ∀ z ∈ Y, k < ((X ∪ Y).filter (· ≤ z)).card := by
    intro z hzY
    have hXsub : X ⊆ (X ∪ Y).filter (· ≤ z) := by
      intro w hwX
      simp only [mem_filter, mem_union]
      exact ⟨Or.inl hwX, (hlt_elems w hwX z hzY).le⟩
    have hz_in : z ∈ (X ∪ Y).filter (· ≤ z) := by
      simp only [mem_filter, mem_union]
      exact ⟨Or.inr hzY, le_refl _⟩
    have hz_notin : z ∉ X := by
      intro hzX
      exact (disjoint_left.1 hdisj) hzX hzY
    have hss : X ⊂ (X ∪ Y).filter (· ≤ z) :=
      ⟨hXsub, fun hsub => hz_notin (hsub hz_in)⟩
    have := card_lt_card hss
    omega
  -- Now prove equality
  refine Prod.ext ?_ ?_
  · -- (splitAt k (X ∪ Y)).1 = X
    rw [splitAt_fst]
    ext z
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hzXY | hzY, hle⟩
      · exact hzXY
      · exfalso
        have := key_Y z hzY
        omega
    · intro hzX
      exact ⟨Or.inl hzX, key_X z hzX⟩
  · -- (splitAt k (X ∪ Y)).2 = Y
    rw [splitAt_snd]
    ext z
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hzX | hzY, hlt⟩
      · exfalso
        have := key_X z hzX
        omega
      · exact hzY
    · intro hzY
      exact ⟨Or.inr hzY, key_Y z hzY⟩

/-- Cardinality of `allPairs`. -/
lemma allPairs_card (n k a : ℕ) :
    (allPairs n k a).card = Nat.choose (k + a) k * Nat.choose (k + n + a) n := by
  unfold allPairs
  rw [card_product, card_powersetCard, card_powersetCard,
      Nat.card_Icc, Nat.card_Icc]
  congr 2

/-- Cardinality of `goodPairs`. -/
lemma goodPairs_card (n k a : ℕ) (hk : 0 < k) (hn : 0 < n) :
    (goodPairs n k a).card = Nat.choose (k + n + a) (n + k) := by
  classical
  -- Bijection goodPairs ↔ powersetCard (n+k) (Icc 1 (k+n+a))
  have hcard : (goodPairs n k a).card =
      ((Icc 1 (k + n + a)).powersetCard (n + k)).card := by
    apply Finset.card_nbij' (fun p => p.1 ∪ p.2) (fun S => splitAt k S)
    · -- forward: goodPairs → powersetCard
      intro p hp
      have hp' : p ∈ goodPairs n k a := hp
      rw [goodPairs, allPairs] at hp'
      simp only [mem_filter, mem_product, mem_powersetCard] at hp'
      obtain ⟨⟨⟨hX1, hXc⟩, hY1, hYc⟩, hmax⟩ := hp'
      show p.1 ∪ p.2 ∈ (Icc 1 (k + n + a)).powersetCard (n + k)
      rw [mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro z hz
        simp only [mem_union] at hz
        rcases hz with hz | hz
        · have : Icc 1 (k + a) ⊆ Icc 1 (k + n + a) := by
            intro w hw; simp only [mem_Icc] at hw ⊢; omega
          exact this (hX1 hz)
        · exact hY1 hz
      · -- |X ∪ Y| = n + k
        have hdisj : Disjoint p.1 p.2 := by
          rw [disjoint_left]
          intro x hxX hxY
          have hXne : p.1.Nonempty := ⟨x, hxX⟩
          have hYne : p.2.Nonempty := ⟨x, hxY⟩
          have hlt := (max_lt_min_iff_max'_lt_min' hXne hYne).mp hmax
          have hxx : x ≤ p.1.max' hXne := p.1.le_max' x hxX
          have hxy : p.2.min' hYne ≤ x := p.2.min'_le x hxY
          omega
        rw [card_union_of_disjoint hdisj, hXc, hYc]; ring
    · -- backward: powersetCard → goodPairs
      intro S hS
      have hS' : S ∈ (Icc 1 (k + n + a)).powersetCard (n + k) := hS
      rw [mem_powersetCard] at hS'
      obtain ⟨hSsub, hScard⟩ := hS'
      show splitAt k S ∈ goodPairs n k a
      rw [goodPairs, allPairs]
      simp only [mem_filter, mem_product, mem_powersetCard]
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · exact splitAt_left_subset_Icc S hScard hSsub
      · exact (splitAt_card_of_size S hScard).1
      · intro x hx
        exact hSsub (splitAt_subset_right k S hx)
      · exact (splitAt_card_of_size S hScard).2
      · exact splitAt_max_lt_min S hScard hk hn
    · -- left inverse: splitAt (X ∪ Y) = (X, Y)
      intro p hp
      have hp' : p ∈ goodPairs n k a := hp
      rw [goodPairs, allPairs] at hp'
      simp only [mem_filter, mem_product, mem_powersetCard] at hp'
      obtain ⟨⟨⟨_, hXc⟩, _, _⟩, hmax⟩ := hp'
      exact splitAt_union_eq hXc hmax
    · -- right inverse: X ∪ Y = S (where (X,Y) = splitAt S)
      intro S _
      exact splitAt_union k S
  rw [hcard, card_powersetCard, Nat.card_Icc]
  congr 1


snip end

/-- The problem: the ratio

  `|goodPairs| / |allPairs| = 1 / C(n+k, k)`,

independent of `a`. We state this in cleared form:

  `|goodPairs| * C(n+k, k) = |allPairs|`.
-/
problem imc2021_p2 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (a : ℕ) :
    ((goodPairs n k a).card : ℚ) * (Nat.choose (n + k) k) =
    ((allPairs n k a).card : ℚ) := by
  rw [goodPairs_card n k a hk hn, allPairs_card]
  -- Identity: C(k+n+a, n+k) · C(n+k, k) = C(k+a, k) · C(k+n+a, n)
  -- Both equal (k+n+a)! / ((k+a-k)! · k! · n!) ... let's verify.
  -- C(k+n+a, n+k) · C(n+k, k) = (k+n+a)! / ((n+k)!(a)!) · (n+k)!/(k!n!)
  --                           = (k+n+a)! / (a! k! n!)
  -- C(k+a, k) · C(k+n+a, n) = (k+a)!/(k!a!) · (k+n+a)!/((k+a)!n!)
  --                        = (k+n+a)! / (k! a! n!)
  -- Same. Push cast and use choose_mul_choose or direct factorials.
  have h1 : Nat.choose (k + n + a) (n + k) * Nat.choose (n + k) k =
            Nat.choose (k + a) k * Nat.choose (k + n + a) n := by
    -- Use Nat.choose_mul_choose: C(n,k) * C(k,m) = C(n,m) * C(n-m, k-m)
    -- Simpler: expand using choose_mul_factorial or rewrite both sides.
    have h_le1 : n + k ≤ k + n + a := by omega
    have h_le2 : k ≤ n + k := by omega
    have h_le3 : k ≤ k + a := by omega
    have h_le4 : n ≤ k + n + a := by omega
    -- Multiply both sides by factorials to get a factorial identity.
    -- Instead: use Nat.choose_mul_choose_eq or prove via factorials.
    -- LHS: (k+n+a)! / ((a)! (n+k)!) · (n+k)! / (k! n!) = (k+n+a)! / (a! k! n!)
    -- Multiply by (a! k! n!) - we need injection.
    -- Easiest: convert via (Nat.choose_mul_factorial_mul_factorial).
    have e1 : Nat.choose (k + n + a) (n + k) * Nat.choose (n + k) k * (a.factorial * k.factorial * n.factorial) =
              (k + n + a).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial h_le1
      have h2 := Nat.choose_mul_factorial_mul_factorial h_le2
      -- C(k+n+a, n+k) * (n+k)! * (k+n+a - (n+k))! = (k+n+a)!
      -- (k+n+a) - (n+k) = a
      have ha : k + n + a - (n + k) = a := by omega
      rw [ha] at this
      -- (n+k)! = C(n+k, k) * k! * (n+k-k)!, and (n+k-k) = n
      have hb : n + k - k = n := by omega
      rw [hb] at h2
      calc Nat.choose (k + n + a) (n + k) * Nat.choose (n + k) k * (a.factorial * k.factorial * n.factorial)
          = Nat.choose (k + n + a) (n + k) * (Nat.choose (n + k) k * k.factorial * n.factorial) * a.factorial := by ring
        _ = Nat.choose (k + n + a) (n + k) * (n + k).factorial * a.factorial := by rw [h2]
        _ = (k + n + a).factorial := by
            calc _ = Nat.choose (k + n + a) (n + k) * (n + k).factorial * a.factorial := rfl
              _ = _ := by linarith [this]
    have e2 : Nat.choose (k + a) k * Nat.choose (k + n + a) n * (a.factorial * k.factorial * n.factorial) =
              (k + n + a).factorial := by
      have h3 := Nat.choose_mul_factorial_mul_factorial h_le3
      have h4 := Nat.choose_mul_factorial_mul_factorial h_le4
      have ha : k + a - k = a := by omega
      have hb : k + n + a - n = k + a := by omega
      rw [ha] at h3
      rw [hb] at h4
      -- h3: C(k+a, k) * k! * a! = (k+a)!
      -- h4: C(k+n+a, n) * n! * (k+a)! = (k+n+a)!
      calc Nat.choose (k + a) k * Nat.choose (k + n + a) n * (a.factorial * k.factorial * n.factorial)
          = Nat.choose (k + n + a) n * n.factorial * (Nat.choose (k + a) k * k.factorial * a.factorial) := by ring
        _ = Nat.choose (k + n + a) n * n.factorial * (k + a).factorial := by rw [h3]
        _ = (k + n + a).factorial := by linarith [h4]
    -- Cancel the positive factor
    have hpos : 0 < a.factorial * k.factorial * n.factorial := by
      exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
        (Nat.factorial_pos _)
    exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)
  -- Now cast to ℚ
  have h1q : (Nat.choose (k + n + a) (n + k) : ℚ) * (Nat.choose (n + k) k : ℚ) =
             (Nat.choose (k + a) k : ℚ) * (Nat.choose (k + n + a) n : ℚ) := by
    exact_mod_cast h1
  push_cast
  linarith [h1q]

end Imc2021P2
