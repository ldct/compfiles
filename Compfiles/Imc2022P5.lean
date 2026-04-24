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

-- The core identity: global cherries count = 4·mono + 2·total.
private lemma cherry_triangle_identity (c : Fin 43 → Fin 43 → Bool)
    (hsym : ∀ i j, c i j = c j i) :
    (globalCherries c).card = 4 * (monoTri c).card + 2 * allTri.card := by
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
