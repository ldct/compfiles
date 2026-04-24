/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2022, Problem 5

We colour all the sides and diagonals of a regular polygon `P` with `43`
vertices either red or blue so that every vertex is an endpoint of `20` red
segments and `22` blue segments. A triangle formed by vertices of `P` is
called monochromatic if all of its sides have the same colour. Suppose there
are `2022` blue monochromatic triangles. How many red monochromatic triangles
are there?

Answer: `859`.
-/

namespace Imc2022P5

open Finset

/-- The number of red monochromatic triangles. -/
determine answer : ℕ := 859

snip begin

/-- All triples (i,j,k) with i<j<k. -/
private def allTri : Finset (Fin 43 × Fin 43 × Fin 43) :=
  Finset.univ.filter (fun t : Fin 43 × Fin 43 × Fin 43 => t.1 < t.2.1 ∧ t.2.1 < t.2.2)

/-- Red monochromatic triangles. -/
private def redTri (c : Fin 43 → Fin 43 → Bool) : Finset (Fin 43 × Fin 43 × Fin 43) :=
  Finset.univ.filter (fun t : Fin 43 × Fin 43 × Fin 43 =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    c t.1 t.2.1 = true ∧ c t.2.1 t.2.2 = true ∧ c t.1 t.2.2 = true)

/-- Blue monochromatic triangles. -/
private def blueTri (c : Fin 43 → Fin 43 → Bool) : Finset (Fin 43 × Fin 43 × Fin 43) :=
  Finset.univ.filter (fun t : Fin 43 × Fin 43 × Fin 43 =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    c t.1 t.2.1 = false ∧ c t.2.1 t.2.2 = false ∧ c t.1 t.2.2 = false)

/-- All monochromatic triangles. -/
private def monoTri (c : Fin 43 → Fin 43 → Bool) : Finset (Fin 43 × Fin 43 × Fin 43) :=
  Finset.univ.filter (fun t : Fin 43 × Fin 43 × Fin 43 =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    (c t.1 t.2.1 = c t.2.1 t.2.2) ∧ (c t.2.1 t.2.2 = c t.1 t.2.2))

/-- Ordered cherries at vertex v: (a,b) with a,b,v distinct and c(v,a)=c(v,b). -/
private def cherriesAt (c : Fin 43 → Fin 43 → Bool) (v : Fin 43) :
    Finset (Fin 43 × Fin 43) :=
  Finset.univ.filter (fun p : Fin 43 × Fin 43 =>
    p.1 ≠ v ∧ p.2 ≠ v ∧ p.1 ≠ p.2 ∧ c v p.1 = c v p.2)

/-- Global ordered cherry set: (v,a,b) with v,a,b distinct and c(v,a)=c(v,b). -/
private def globalCherries (c : Fin 43 → Fin 43 → Bool) :
    Finset (Fin 43 × Fin 43 × Fin 43) :=
  Finset.univ.filter (fun t : Fin 43 × Fin 43 × Fin 43 =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ c t.1 t.2.1 = c t.1 t.2.2)

-- Cardinality of allTri is C(43,3) = 12341.
private lemma allTri_card : allTri.card = 12341 := by
  rw [allTri, show (12341 : ℕ) = Nat.choose 43 3 by decide]
  -- Map from Finset.powersetCard 3 univ is a cleaner proof, but let's try native_decide.
  native_decide

-- The blue-degree (number of j ≠ i with c i j = false) is 22.
private lemma blue_deg (c : Fin 43 → Fin 43 → Bool)
    (hirrefl : ∀ i, c i i = false)
    (hred_deg : ∀ i, (Finset.univ.filter fun j : Fin 43 => j ≠ i ∧ c i j = true).card = 20)
    (i : Fin 43) :
    (Finset.univ.filter fun j : Fin 43 => j ≠ i ∧ c i j = false).card = 22 := by
  have total : (Finset.univ.filter fun j : Fin 43 => j ≠ i).card = 42 := by
    rw [Finset.filter_ne']
    simp [Finset.card_erase_of_mem]
  have hsplit :
      (Finset.univ.filter fun j : Fin 43 => j ≠ i).card =
      (Finset.univ.filter fun j : Fin 43 => j ≠ i ∧ c i j = true).card +
      (Finset.univ.filter fun j : Fin 43 => j ≠ i ∧ c i j = false).card := by
    rw [← Finset.filter_card_add_filter_neg_card_eq_card (p := fun j : Fin 43 => c i j = true)
         (s := Finset.univ.filter fun j : Fin 43 => j ≠ i)]
    congr 1
    · congr 1
      ext j
      simp [and_comm]
    · congr 1
      ext j
      simp [and_comm, Bool.not_eq_true]
  rw [total, hred_deg] at hsplit
  omega

-- For each v, cherries at v count red and blue contributions separately.
private lemma cherriesAt_card (c : Fin 43 → Fin 43 → Bool)
    (hirrefl : ∀ i, c i i = false)
    (hred_deg : ∀ i, (Finset.univ.filter fun j : Fin 43 => j ≠ i ∧ c i j = true).card = 20)
    (v : Fin 43) : (cherriesAt c v).card = 842 := by
  -- Split cherriesAt into color-true and color-false parts.
  have hsplit :
      cherriesAt c v =
        (cherriesAt c v).filter (fun p => c v p.1 = true) ∪
        (cherriesAt c v).filter (fun p => c v p.1 = false) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases Bool.eq_false_or_eq_true (c v a) with h1 | h1
      · left; exact ⟨h, h1⟩
      · right; exact ⟨h, h1⟩
    · cases h with
      | inl h => exact h.1
      | inr h => exact h.1
  have hdisj :
      Disjoint ((cherriesAt c v).filter (fun p : Fin 43 × Fin 43 => c v p.1 = true))
               ((cherriesAt c v).filter (fun p : Fin 43 × Fin 43 => c v p.1 = false)) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    rw [h1] at h2
    exact Bool.noConfusion h2
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  -- Red cherries at v: pairs of distinct red neighbors = 20 * 19.
  have hred :
      ((cherriesAt c v).filter (fun p : Fin 43 × Fin 43 => c v p.1 = true)).card = 20 * 19 := by
    set S := Finset.univ.filter fun j : Fin 43 => j ≠ v ∧ c v j = true with hS
    have hScard : S.card = 20 := hred_deg v
    have hEq :
        ((cherriesAt c v).filter (fun p : Fin 43 × Fin 43 => c v p.1 = true)) =
          (S ×ˢ S).filter (fun p : Fin 43 × Fin 43 => p.1 ≠ p.2) := by
      ext ⟨a, b⟩
      simp only [cherriesAt, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_product, hS]
      refine ⟨fun ⟨⟨ha, hb, hab, hcol⟩, hca⟩ => ?_, fun ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩ => ?_⟩
      · refine ⟨⟨⟨ha, hca⟩, hb, ?_⟩, hab⟩
        rw [← hcol]; exact hca
      · refine ⟨⟨ha1, hb1, hab, ?_⟩, ha2⟩
        rw [ha2, hb2]
    rw [hEq]
    -- (S ×ˢ S).filter (p.1 ≠ p.2) card = |S|*|S| - |S| = |S|*(|S|-1)
    have : (S ×ˢ S).filter (fun p : Fin 43 × Fin 43 => p.1 ≠ p.2) =
           S ×ˢ S \ S.image (fun x => (x, x)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_image,
                 Prod.mk.injEq]
      refine ⟨fun ⟨⟨ha, hb⟩, hab⟩ => ⟨⟨ha, hb⟩, fun ⟨x, _, hxa, hxb⟩ => hab (hxa.symm.trans hxb)⟩,
             fun ⟨⟨ha, hb⟩, hne⟩ => ⟨⟨ha, hb⟩, fun hab => hne ⟨a, ha, rfl, hab⟩⟩⟩
    rw [this]
    rw [Finset.card_sdiff_of_subset (by
      intro ⟨a, b⟩ h
      simp only [Finset.mem_image, Prod.mk.injEq] at h
      obtain ⟨x, hx, hxa, hxb⟩ := h
      simp [Finset.mem_product, ← hxa, ← hxb, hx])]
    rw [Finset.card_product, hScard]
    have himg : (S.image (fun x : Fin 43 => (x, x))).card = S.card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
    rw [himg, hScard]
  -- Blue cherries at v: pairs of distinct blue neighbors = 22 * 21.
  have hblue :
      ((cherriesAt c v).filter (fun p : Fin 43 × Fin 43 => c v p.1 = false)).card = 22 * 21 := by
    set S := Finset.univ.filter fun j : Fin 43 => j ≠ v ∧ c v j = false with hS
    have hScard : S.card = 22 := blue_deg c hirrefl hred_deg v
    have hEq :
        ((cherriesAt c v).filter (fun p : Fin 43 × Fin 43 => c v p.1 = false)) =
          (S ×ˢ S).filter (fun p : Fin 43 × Fin 43 => p.1 ≠ p.2) := by
      ext ⟨a, b⟩
      simp only [cherriesAt, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_product, hS]
      refine ⟨fun ⟨⟨ha, hb, hab, hcol⟩, hca⟩ => ?_, fun ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩ => ?_⟩
      · refine ⟨⟨⟨ha, hca⟩, hb, ?_⟩, hab⟩
        rw [← hcol]; exact hca
      · refine ⟨⟨ha1, hb1, hab, ?_⟩, ha2⟩
        rw [ha2, hb2]
    rw [hEq]
    have : (S ×ˢ S).filter (fun p : Fin 43 × Fin 43 => p.1 ≠ p.2) =
           S ×ˢ S \ S.image (fun x => (x, x)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_image,
                 Prod.mk.injEq]
      refine ⟨fun ⟨⟨ha, hb⟩, hab⟩ => ⟨⟨ha, hb⟩, fun ⟨x, _, hxa, hxb⟩ => hab (hxa.symm.trans hxb)⟩,
             fun ⟨⟨ha, hb⟩, hne⟩ => ⟨⟨ha, hb⟩, fun hab => hne ⟨a, ha, rfl, hab⟩⟩⟩
    rw [this]
    rw [Finset.card_sdiff_of_subset (by
      intro ⟨a, b⟩ h
      simp only [Finset.mem_image, Prod.mk.injEq] at h
      obtain ⟨x, hx, hxa, hxb⟩ := h
      simp [Finset.mem_product, ← hxa, ← hxb, hx])]
    rw [Finset.card_product, hScard]
    have himg : (S.image (fun x : Fin 43 => (x, x))).card = S.card := by
      apply Finset.card_image_of_injective
      intro x y hxy
      exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
    rw [himg, hScard]
  rw [hred, hblue]

/-- For a triple T = (i,j,k), the "same-color edge-pair count at each vertex":
  cond1 at vertex j (edges ij and jk), cond2 at vertex i (edges ij and ik),
  cond3 at vertex k (edges jk and ik). -/
private def triSame (c : Fin 43 → Fin 43 → Bool) (T : Fin 43 × Fin 43 × Fin 43) : ℕ :=
  (if c T.1 T.2.1 = c T.2.1 T.2.2 then 1 else 0) +
  (if c T.1 T.2.1 = c T.1 T.2.2 then 1 else 0) +
  (if c T.2.1 T.2.2 = c T.1 T.2.2 then 1 else 0)

/-- Sort three distinct Fin 43 elements into strictly increasing order. -/
private def sortTriple (x y z : Fin 43) : Fin 43 × Fin 43 × Fin 43 :=
  if x < y then
    if y < z then (x, y, z)
    else if x < z then (x, z, y)
    else (z, x, y)
  else
    if x < z then (y, x, z)
    else if y < z then (y, z, x)
    else (z, y, x)

private lemma sortTriple_mem_allTri {x y z : Fin 43} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : sortTriple x y z ∈ allTri := by
  have hxyv : (x.val) ≠ y.val := fun h => hxy (Fin.ext h)
  have hxzv : (x.val) ≠ z.val := fun h => hxz (Fin.ext h)
  have hyzv : (y.val) ≠ z.val := fun h => hyz (Fin.ext h)
  simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and, sortTriple,
             Fin.lt_def]
  split_ifs with h1 h2 h3 h4 h5 <;>
    (try simp only [not_lt] at *) <;>
    first
    | (refine ⟨?_, ?_⟩ <;> omega)
    | (exfalso; omega)

-- Global cherries partition by first coordinate v, giving sum = 43 * 842.
private lemma globalCherries_card (c : Fin 43 → Fin 43 → Bool)
    (hirrefl : ∀ i, c i i = false)
    (hred_deg : ∀ i, (Finset.univ.filter fun j : Fin 43 => j ≠ i ∧ c i j = true).card = 20) :
    (globalCherries c).card = 43 * 842 := by
  have hpartition :
      (globalCherries c).card =
        ∑ v : Fin 43, (cherriesAt c v).card := by
    -- Using a bijection (v, (a,b)) ↔ (v,a,b) with the cherry predicate.
    rw [← Finset.card_sigma (s := (Finset.univ : Finset (Fin 43)))
          (t := fun v => cherriesAt c v)]
    symm
    apply Finset.card_bij
      (fun (x : Σ v : Fin 43, Fin 43 × Fin 43) _ => (x.1, x.2.1, x.2.2))
    · rintro ⟨v, a, b⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, cherriesAt,
                 Finset.mem_filter] at hx
      obtain ⟨hav, hbv, hab, hcol⟩ := hx
      simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, hab, hcol⟩
      · intro h; exact hav h.symm
      · intro h; exact hbv h.symm
    · rintro ⟨v1, a1, b1⟩ _ ⟨v2, a2, b2⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨hv, ha, hb⟩ := h
      subst hv; subst ha; subst hb; rfl
    · rintro ⟨v, a, b⟩ hx
      simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hva, hvb, hab, hcol⟩ := hx
      refine ⟨⟨v, a, b⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, cherriesAt, Finset.mem_filter]
      refine ⟨?_, ?_, hab, hcol⟩
      · intro h; exact hva h.symm
      · intro h; exact hvb h.symm
  rw [hpartition]
  simp_rw [fun v => cherriesAt_card c hirrefl hred_deg v]
  simp

-- For each T ∈ allTri, fiber cardinality under sortTriple equals 2·triSame T.
-- That is: 2·triSame(T) = 4·[T mono] + 2.
private lemma triSame_eq (c : Fin 43 → Fin 43 → Bool)
    (T : Fin 43 × Fin 43 × Fin 43) (hT : T ∈ allTri) :
    2 * triSame c T =
      4 * (if T ∈ monoTri c then 1 else 0) + 2 := by
  simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨hij, hjk⟩ := hT
  simp only [monoTri, Finset.mem_filter, Finset.mem_univ, true_and, triSame,
             hij, hjk, true_and]
  rcases Bool.eq_false_or_eq_true (c T.1 T.2.1) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (c T.2.1 T.2.2) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (c T.1 T.2.2) with h3 | h3 <;>
  simp [h1, h2, h3]

private lemma monoTri_subset_allTri (c : Fin 43 → Fin 43 → Bool) :
    monoTri c ⊆ allTri := by
  intro T hT
  simp only [monoTri, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hT.1, hT.2.1⟩

set_option maxRecDepth 4000 in
private lemma sum_triSame (c : Fin 43 → Fin 43 → Bool) :
    ∑ T ∈ allTri, 2 * triSame c T = 4 * (monoTri c).card + 2 * allTri.card := by
  rw [show (∑ T ∈ allTri, 2 * triSame c T) =
       ∑ T ∈ allTri, (4 * (if T ∈ monoTri c then 1 else 0) + 2) from
         Finset.sum_congr rfl (fun T hT => triSame_eq c T hT)]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_ite_mem]
  rw [Finset.inter_eq_right.mpr (monoTri_subset_allTri c)]
  rw [Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_const, smul_eq_mul]
  ring

-- Pattern 1: t.1 < t.2.1 < t.2.2 (i,j,k order). Cherry condition c(i,j)=c(i,k).
private lemma cherry_pattern1 (c : Fin 43 → Fin 43 → Bool) :
    ((globalCherries c).filter (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2)).card =
    (allTri.filter (fun T => c T.1 T.2.1 = c T.1 T.2.2)).card := by
  apply Finset.card_bij (fun t _ => t)
  · intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hg, hlt⟩ := ht
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rw [Finset.mem_filter]
    refine ⟨?_, hg.2.2.2⟩
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hlt
  · intros; assumption
  · intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hall, hcol⟩ := hT
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    refine ⟨T, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hall⟩
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, hcol⟩
    · intro h; exact absurd (h ▸ hall.1) (lt_irrefl _)
    · intro h; exact absurd (h ▸ hall.1.trans hall.2) (lt_irrefl _)
    · intro h; exact absurd (h ▸ hall.2) (lt_irrefl _)

-- Pattern 2: t.1 < t.2.2 < t.2.1 (perm (i,k,j): σ(T) = (T.1, T.2.2, T.2.1)).
-- Cherry condition c(T.1, T.2.2) = c(T.1, T.2.1), i.e. c(i,j)=c(i,k) → cond2.
private lemma cherry_pattern2 (c : Fin 43 → Fin 43 → Bool) :
    ((globalCherries c).filter (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1)).card =
    (allTri.filter (fun T => c T.1 T.2.1 = c T.1 T.2.2)).card := by
  apply Finset.card_bij (fun t _ => (t.1, t.2.2, t.2.1))
  · rintro ⟨a, b, d⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hg, hlt⟩ := ht
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, allTri, Finset.mem_univ, true_and]
    refine ⟨⟨hlt.1, hlt.2⟩, ?_⟩
    exact hg.2.2.2.symm
  · rintro ⟨a, b, d⟩ _ ⟨a', b', d'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h1, h2, h3]
  · rintro ⟨i, j, k⟩ hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hall, hcol⟩ := hT
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    refine ⟨(i, k, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hall.1, hall.2⟩
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, hcol.symm⟩
    · intro h; exact absurd (h ▸ hall.1.trans hall.2) (lt_irrefl _)
    · intro h; exact absurd (h ▸ hall.1) (lt_irrefl _)
    · intro h; exact absurd (h ▸ hall.2) (lt_irrefl _)

-- Pattern 3: t.2.1 < t.1 < t.2.2 (perm (j,i,k): σ(T) = (T.2.1, T.1, T.2.2)).
-- Cherry: c(t.1, t.2.1) = c(t.1, t.2.2) ≡ c(j,i)=c(j,k) ≡ c(i,j)=c(j,k) → cond1.
private lemma cherry_pattern3 (c : Fin 43 → Fin 43 → Bool) (hsym : ∀ i j, c i j = c j i) :
    ((globalCherries c).filter (fun t => t.2.1 < t.1 ∧ t.1 < t.2.2)).card =
    (allTri.filter (fun T => c T.1 T.2.1 = c T.2.1 T.2.2)).card := by
  apply Finset.card_bij (fun t _ => (t.2.1, t.1, t.2.2))
  · rintro ⟨v, a, b⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hg, hlt⟩ := ht
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, allTri, Finset.mem_univ, true_and]
    refine ⟨⟨hlt.1, hlt.2⟩, ?_⟩
    rw [hsym v a] at hg
    exact hg.2.2.2
  · rintro ⟨v, a, b⟩ _ ⟨v', a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h1, h2, h3]
  · rintro ⟨i, j, k⟩ hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hall, hcol⟩ := hT
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    have hij : (i : Fin 43).val < (j : Fin 43).val := hall.1
    have hjk : (j : Fin 43).val < (k : Fin 43).val := hall.2
    refine ⟨(j, i, k), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hall.1, hall.2⟩
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · rw [hsym j i]; exact hcol

-- Pattern 4: t.2.2 < t.1 < t.2.1 (perm (j,k,i): σ(T) = (T.2.1, T.2.2, T.1)).
-- Cherry: c(j,k)=c(j,i) ≡ c(j,k)=c(i,j) → cond1: c(i,j)=c(j,k).
private lemma cherry_pattern4 (c : Fin 43 → Fin 43 → Bool) (hsym : ∀ i j, c i j = c j i) :
    ((globalCherries c).filter (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1)).card =
    (allTri.filter (fun T => c T.1 T.2.1 = c T.2.1 T.2.2)).card := by
  -- Map: (v,a,b) ↦ (b,v,a) (i.e. (t.2.2, t.1, t.2.1)).
  apply Finset.card_bij (fun t _ => (t.2.2, t.1, t.2.1))
  · rintro ⟨v, a, b⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hg, hlt⟩ := ht
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, allTri, Finset.mem_univ, true_and]
    refine ⟨⟨hlt.1, hlt.2⟩, ?_⟩
    -- need c b v = c v a (as c T.1 T.2.1 = c T.2.1 T.2.2, where T=(b,v,a))
    -- we have c v a = c v b from hg.2.2.2
    rw [hsym b v]
    exact hg.2.2.2.symm
  · rintro ⟨v, a, b⟩ _ ⟨v', a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h1, h2, h3]
  · rintro ⟨i, j, k⟩ hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hall, hcol⟩ := hT
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    have hij : (i : Fin 43).val < (j : Fin 43).val := hall.1
    have hjk : (j : Fin 43).val < (k : Fin 43).val := hall.2
    refine ⟨(j, k, i), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hall.1, hall.2⟩
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · -- need c j k = c j i; we have c i j = c j k, i.e. hcol
      rw [hsym j i]; exact hcol.symm

-- Pattern 5: t.2.1 < t.2.2 < t.1 (perm (k,i,j): σ(T) = (T.2.2, T.1, T.2.1)).
-- Cherry: c(k,i)=c(k,j) ≡ c(i,k)=c(j,k) → cond3: c(i,k) = c(j,k).
private lemma cherry_pattern5 (c : Fin 43 → Fin 43 → Bool) (hsym : ∀ i j, c i j = c j i) :
    ((globalCherries c).filter (fun t => t.2.1 < t.2.2 ∧ t.2.2 < t.1)).card =
    (allTri.filter (fun T => c T.1 T.2.2 = c T.2.1 T.2.2)).card := by
  -- Map: (v,a,b) ↦ (a,b,v) = (t.2.1, t.2.2, t.1).
  apply Finset.card_bij (fun t _ => (t.2.1, t.2.2, t.1))
  · rintro ⟨v, a, b⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hg, hlt⟩ := ht
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, allTri, Finset.mem_univ, true_and]
    refine ⟨⟨hlt.1, hlt.2⟩, ?_⟩
    -- need c a v = c b v (T = (a,b,v))
    have hh : c v a = c v b := hg.2.2.2
    rw [hsym a v, hsym b v]
    exact hh
  · rintro ⟨v, a, b⟩ _ ⟨v', a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h1, h2, h3]
  · rintro ⟨i, j, k⟩ hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hall, hcol⟩ := hT
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    have hij : (i : Fin 43).val < (j : Fin 43).val := hall.1
    have hjk : (j : Fin 43).val < (k : Fin 43).val := hall.2
    refine ⟨(k, i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hall.1, hall.2⟩
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · intro h; have : (_ : ℕ) = _ := congrArg Fin.val h; omega
    · -- need c k i = c k j; we have c i k = c j k, i.e. hcol
      rw [hsym k i, hsym k j]; exact hcol

-- Pattern 6: t.2.2 < t.2.1 < t.1 (perm (k,j,i): σ(T) = (T.2.2, T.2.1, T.1)).
-- Cherry: c(t.1, t.2.1) = c(t.1, t.2.2) ≡ c(k,j)=c(k,i) ≡ c(j,k)=c(i,k) → cond3.
private lemma cherry_pattern6 (c : Fin 43 → Fin 43 → Bool) (hsym : ∀ i j, c i j = c j i) :
    ((globalCherries c).filter (fun t => t.2.2 < t.2.1 ∧ t.2.1 < t.1)).card =
    (allTri.filter (fun T => c T.1 T.2.2 = c T.2.1 T.2.2)).card := by
  apply Finset.card_bij (fun t _ => (t.2.2, t.2.1, t.1))
  · rintro ⟨v, a, b⟩ ht
    rw [Finset.mem_filter] at ht
    obtain ⟨hg, hlt⟩ := ht
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    simp only [Finset.mem_filter, allTri, Finset.mem_univ, true_and]
    refine ⟨⟨hlt.1, hlt.2⟩, ?_⟩
    have : c v a = c v b := hg.2.2.2
    rw [hsym v a, hsym v b] at this
    exact this.symm
  · rintro ⟨v, a, b⟩ _ ⟨v', a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [h1, h2, h3]
  · rintro ⟨i, j, k⟩ hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hall, hcol⟩ := hT
    simp only [allTri, Finset.mem_filter, Finset.mem_univ, true_and] at hall
    refine ⟨(k, j, i), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hall.1, hall.2⟩
    simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; exact absurd (h ▸ hall.2) (lt_irrefl _)
    · intro h; exact absurd (h ▸ hall.1.trans hall.2) (lt_irrefl _)
    · intro h; exact absurd (h ▸ hall.1) (lt_irrefl _)
    · rw [hsym k j, hsym k i]; exact hcol.symm

-- Six pattern predicates:
private def pat1 (t : Fin 43 × Fin 43 × Fin 43) : Prop := t.1 < t.2.1 ∧ t.2.1 < t.2.2
private def pat2 (t : Fin 43 × Fin 43 × Fin 43) : Prop := t.1 < t.2.2 ∧ t.2.2 < t.2.1
private def pat3 (t : Fin 43 × Fin 43 × Fin 43) : Prop := t.2.1 < t.1 ∧ t.1 < t.2.2
private def pat4 (t : Fin 43 × Fin 43 × Fin 43) : Prop := t.2.2 < t.1 ∧ t.1 < t.2.1
private def pat5 (t : Fin 43 × Fin 43 × Fin 43) : Prop := t.2.1 < t.2.2 ∧ t.2.2 < t.1
private def pat6 (t : Fin 43 × Fin 43 × Fin 43) : Prop := t.2.2 < t.2.1 ∧ t.2.1 < t.1

instance : DecidablePred pat1 := fun t => by unfold pat1; infer_instance
instance : DecidablePred pat2 := fun t => by unfold pat2; infer_instance
instance : DecidablePred pat3 := fun t => by unfold pat3; infer_instance
instance : DecidablePred pat4 := fun t => by unfold pat4; infer_instance
instance : DecidablePred pat5 := fun t => by unfold pat5; infer_instance
instance : DecidablePred pat6 := fun t => by unfold pat6; infer_instance

-- Exactly one of the 6 patterns holds for any t in globalCherries.
private lemma pattern_exhaustive (c : Fin 43 → Fin 43 → Bool)
    {t : Fin 43 × Fin 43 × Fin 43} (ht : t ∈ globalCherries c) :
    pat1 t ∨ pat2 t ∨ pat3 t ∨ pat4 t ∨ pat5 t ∨ pat6 t := by
  simp only [globalCherries, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hva, hvb, hab, _⟩ := ht
  simp only [pat1, pat2, pat3, pat4, pat5, pat6]
  rcases lt_trichotomy t.1 t.2.1 with h1 | h1 | h1
  · rcases lt_trichotomy t.2.1 t.2.2 with h2 | h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd h2 hab
    · rcases lt_trichotomy t.1 t.2.2 with h3 | h3 | h3
      · exact Or.inr (Or.inl ⟨h3, h2⟩)
      · exact absurd h3 hvb
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h1⟩)))
  · exact absurd h1 hva
  · rcases lt_trichotomy t.2.1 t.2.2 with h2 | h2 | h2
    · rcases lt_trichotomy t.1 t.2.2 with h3 | h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h3⟩))
      · exact absurd h3 hvb
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))))
    · exact absurd h2 hab
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, h1⟩))))

-- Patterns are mutually exclusive by strict order properties.
-- We use Fin 43's `<` compared via `.val` for omega.

-- Assign each triple t a pattern index in Fin 6 by its coordinate order.
private def patIdx (t : Fin 43 × Fin 43 × Fin 43) : Fin 6 :=
  if pat1 t then 0
  else if pat2 t then 1
  else if pat3 t then 2
  else if pat4 t then 3
  else if pat5 t then 4
  else 5

private lemma patIdx_mapsTo (c : Fin 43 → Fin 43 → Bool) :
    ∀ t ∈ globalCherries c, patIdx t ∈ (Finset.univ : Finset (Fin 6)) := by
  intro t _; exact Finset.mem_univ _

-- Each pattern-filtered set equals the patIdx-fiber at that index.
private lemma filter_pat_eq_fiber1 (c : Fin 43 → Fin 43 → Bool) :
    (globalCherries c).filter pat1 =
      ((globalCherries c).filter fun t => patIdx t = 0) := by
  ext t
  simp only [Finset.mem_filter]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · simp only [patIdx]; rw [if_pos h2]
  · simp only [patIdx] at h2
    split_ifs at h2 with hp1 hp2 hp3 hp4 hp5
    · exact hp1
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2

private lemma filter_pat_eq_fiber2 (c : Fin 43 → Fin 43 → Bool) :
    (globalCherries c).filter pat2 =
      ((globalCherries c).filter fun t => patIdx t = 1) := by
  ext t
  simp only [Finset.mem_filter]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · have hn1 : ¬ pat1 t := by
      rintro ⟨ha, hb⟩; rcases h2 with ⟨hc, hd⟩
      have : (t.2.1 : Fin 43).val < t.2.2.val := hb
      have : (t.2.2 : Fin 43).val < t.2.1.val := hd
      omega
    simp only [patIdx]; rw [if_neg hn1, if_pos h2]
  · simp only [patIdx] at h2
    split_ifs at h2 with hp1 hp2 hp3 hp4 hp5
    · exact Fin.noConfusion h2
    · exact hp2
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2
    · exact Fin.noConfusion h2

private lemma filter_pat_eq_fiber3 (c : Fin 43 → Fin 43 → Bool) :
    (globalCherries c).filter pat3 =
      ((globalCherries c).filter fun t => patIdx t = 2) := by
  ext t
  simp only [Finset.mem_filter]
  refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · have hn1 : ¬ pat1 t := fun ⟨ha, _⟩ => by
      have : (t.1 : Fin 43).val < t.2.1.val := ha
      have : (t.2.1 : Fin 43).val < t.1.val := h2.1
      omega
    have hn2 : ¬ pat2 t := fun ⟨ha, _⟩ => by
      have : (t.1 : Fin 43).val < t.2.2.val := ha
      have : (t.1 : Fin 43).val < t.2.2.val := h2.2
      have : (t.2.1 : Fin 43).val < t.1.val := h2.1
      -- pat2 says t.1 < t.2.2 ∧ t.2.2 < t.2.1. but pat3: t.2.1 < t.1.
      -- t.2.1 < t.1 < t.2.2 < t.2.1 — contradiction.
      have hlt : (t.2.2 : Fin 43).val < t.2.1.val := by
        have := ha.trans_le (le_of_lt (h2.2)); sorry
      omega
    sorry
  · sorry

-- Actually let me just prove the partition directly without the fiber machinery.
-- The 6 pat filters are pairwise disjoint and their union is globalCherries.
private lemma globalCherries_partition (c : Fin 43 → Fin 43 → Bool) :
    (globalCherries c).card =
      ((globalCherries c).filter pat1).card +
      ((globalCherries c).filter pat2).card +
      ((globalCherries c).filter pat3).card +
      ((globalCherries c).filter pat4).card +
      ((globalCherries c).filter pat5).card +
      ((globalCherries c).filter pat6).card := by
  -- Use Finset.card_eq_sum_card_fiberwise with patIdx: globalCherries → Fin 6.
  rw [Finset.card_eq_sum_card_fiberwise (f := patIdx) (t := (Finset.univ : Finset (Fin 6)))
      (patIdx_mapsTo c)]
  -- Sum over 6 fibers.
  rw [show (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  -- Now each summand is ((globalCherries c).filter fun t => patIdx t = i).card.
  -- Swap argument order of eq.
  have hcongr : ∀ (i : Fin 6), ((globalCherries c).filter fun t => patIdx t = i).card =
      ((globalCherries c).filter fun t => i = patIdx t).card := by
    intro i
    apply Finset.card_bij (fun t _ => t)
    · intro t ht; simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, ht.2.symm⟩
    · intros; assumption
    · intro t ht; simp only [Finset.mem_filter] at ht
      exact ⟨t, by simp only [Finset.mem_filter]; exact ⟨ht.1, ht.2.symm⟩, rfl⟩
  -- Now we need: sum of 6 fiber cards = sum of pat_i filter cards.
  -- Use pattern_exhaustive and disjointness to establish fiber = pat_i filter.
  sorry

-- Mono triangles partition into red and blue monochromatic.
private lemma monoTri_split (c : Fin 43 → Fin 43 → Bool) :
    (monoTri c).card = (redTri c).card + (blueTri c).card := by
  have hunion : (monoTri c) = (redTri c) ∪ (blueTri c) := by
    ext ⟨i, j, k⟩
    simp only [monoTri, redTri, blueTri, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
               true_and]
    constructor
    · rintro ⟨hij, hjk, hcol1, hcol2⟩
      rcases Bool.eq_false_or_eq_true (c i j) with h | h
      · left
        refine ⟨hij, hjk, h, ?_, ?_⟩
        · rw [← hcol1, h]
        · rw [← hcol2, ← hcol1, h]
      · right
        refine ⟨hij, hjk, h, ?_, ?_⟩
        · rw [← hcol1, h]
        · rw [← hcol2, ← hcol1, h]
    · rintro (⟨hij, hjk, h1, h2, h3⟩ | ⟨hij, hjk, h1, h2, h3⟩)
      · exact ⟨hij, hjk, by rw [h1, h2], by rw [h2, h3]⟩
      · exact ⟨hij, hjk, by rw [h1, h2], by rw [h2, h3]⟩
  have hdisj : Disjoint (redTri c) (blueTri c) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j, k⟩ hr hb
    simp only [redTri, blueTri, Finset.mem_filter, Finset.mem_univ, true_and] at hr hb
    rw [hb.2.2.1] at hr
    exact Bool.noConfusion hr.2.2.1
  rw [hunion, Finset.card_union_of_disjoint hdisj]

-- Helper: the sum of indicators of a predicate over allTri equals card of filtered set.
private lemma sum_indicator_eq_card (f : Fin 43 × Fin 43 × Fin 43 → Prop) [DecidablePred f] :
    ∑ T ∈ allTri, (if f T then (1 : ℕ) else 0) = (allTri.filter f).card := by
  rw [Finset.sum_boole]
  rfl

-- Combine the 6 pattern lemmas to get the core identity.
set_option maxRecDepth 4000 in
private lemma cherry_triangle_identity (c : Fin 43 → Fin 43 → Bool)
    (hsym : ∀ i j, c i j = c j i) :
    (globalCherries c).card = 4 * (monoTri c).card + 2 * allTri.card := by
  rw [← sum_triSame c]
  rw [globalCherries_partition c]
  -- Rewrite each pattern-filtered card using its cherry_pattern bijection.
  rw [show ((globalCherries c).filter pat1).card =
        (allTri.filter (fun T => c T.1 T.2.1 = c T.1 T.2.2)).card from cherry_pattern1 c,
      show ((globalCherries c).filter pat2).card =
        (allTri.filter (fun T => c T.1 T.2.1 = c T.1 T.2.2)).card from cherry_pattern2 c,
      show ((globalCherries c).filter pat3).card =
        (allTri.filter (fun T => c T.1 T.2.1 = c T.2.1 T.2.2)).card from cherry_pattern3 c hsym,
      show ((globalCherries c).filter pat4).card =
        (allTri.filter (fun T => c T.1 T.2.1 = c T.2.1 T.2.2)).card from cherry_pattern4 c hsym,
      show ((globalCherries c).filter pat5).card =
        (allTri.filter (fun T => c T.1 T.2.2 = c T.2.1 T.2.2)).card from cherry_pattern5 c hsym,
      show ((globalCherries c).filter pat6).card =
        (allTri.filter (fun T => c T.1 T.2.2 = c T.2.1 T.2.2)).card from cherry_pattern6 c hsym]
  -- Goal: |cond2| + |cond2| + |cond1| + |cond1| + |cond3| + |cond3| = Σ 2·triSame
  -- Rewrite RHS using triSame and distribute the sum.
  have hRHS : ∑ T ∈ allTri, 2 * triSame c T =
      2 * (allTri.filter (fun T => c T.1 T.2.1 = c T.2.1 T.2.2)).card +
      2 * (allTri.filter (fun T => c T.1 T.2.1 = c T.1 T.2.2)).card +
      2 * (allTri.filter (fun T => c T.2.1 T.2.2 = c T.1 T.2.2)).card := by
    simp only [triSame]
    rw [Finset.sum_congr rfl (fun T _ =>
      show 2 * (((if c T.1 T.2.1 = c T.2.1 T.2.2 then (1:ℕ) else 0) +
          (if c T.1 T.2.1 = c T.1 T.2.2 then 1 else 0)) +
          (if c T.2.1 T.2.2 = c T.1 T.2.2 then 1 else 0)) =
        2 * (if c T.1 T.2.1 = c T.2.1 T.2.2 then 1 else 0) +
        2 * (if c T.1 T.2.1 = c T.1 T.2.2 then 1 else 0) +
        2 * (if c T.2.1 T.2.2 = c T.1 T.2.2 then 1 else 0) from by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [sum_indicator_eq_card, sum_indicator_eq_card, sum_indicator_eq_card]
  rw [hRHS]
  -- The cond3 filter uses (c T.2.1 T.2.2 = c T.1 T.2.2) but cherry_pattern5/6 use
  -- (c T.1 T.2.2 = c T.2.1 T.2.2). Equal by symmetry of =.
  have hflip : (allTri.filter (fun T => c T.2.1 T.2.2 = c T.1 T.2.2)).card =
               (allTri.filter (fun T => c T.1 T.2.2 = c T.2.1 T.2.2)).card := by
    apply Finset.card_bij (fun T _ => T)
    · intro T hT
      simp only [Finset.mem_filter] at hT ⊢
      exact ⟨hT.1, hT.2.symm⟩
    · intros; assumption
    · intro T hT
      simp only [Finset.mem_filter] at hT
      exact ⟨T, by simp only [Finset.mem_filter]; exact ⟨hT.1, hT.2.symm⟩, rfl⟩
  rw [hflip]
  ring

snip end

/-- `c (i, j) = true` means the edge `{i,j}` is red, `false` means blue.
`c` is symmetric and irreflexive. -/
problem imc2022_p5 (c : Fin 43 → Fin 43 → Bool)
    (hsym : ∀ i j, c i j = c j i)
    (hirrefl : ∀ i, c i i = false)
    (hred_deg : ∀ i, (Finset.univ.filter fun j => j ≠ i ∧ c i j = true).card = 20)
    (hblue_tri : (Finset.univ.filter fun t : Fin 43 × Fin 43 × Fin 43 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        c t.1 t.2.1 = false ∧ c t.2.1 t.2.2 = false ∧ c t.1 t.2.2 = false).card = 2022) :
    (Finset.univ.filter fun t : Fin 43 × Fin 43 × Fin 43 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        c t.1 t.2.1 = true ∧ c t.2.1 t.2.2 = true ∧ c t.1 t.2.2 = true).card = answer := by
  -- Rewrite goal and hypothesis in terms of our named sets.
  show (redTri c).card = answer
  -- Establish blueTri and monoTri.
  have hBT : (blueTri c).card = 2022 := hblue_tri
  have hMS := monoTri_split c
  -- Core identity.
  have hCT := cherry_triangle_identity c hsym
  have hGC := globalCherries_card c hirrefl hred_deg
  have hAT := allTri_card
  -- Solve arithmetic.
  rw [hAT] at hCT
  rw [hGC] at hCT
  -- 43 * 842 = 4 * monoTri.card + 2 * 12341
  -- 36206 = 4 * monoTri.card + 24682
  -- monoTri.card = 2881
  have hm : (monoTri c).card = 2881 := by omega
  rw [hm] at hMS
  -- redTri.card + blueTri.card = 2881, blueTri.card = 2022 => redTri.card = 859
  simp only [answer]
  omega

end Imc2022P5
