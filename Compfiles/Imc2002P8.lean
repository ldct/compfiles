/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2002, Problem 8
(IMC 2002, Day 2, Problem 2)

At a mathematical contest, 200 students took part. They received 6 problems
to solve, and each problem was solved by at least 120 of them. Prove that
there exist two students such that every problem was solved by at least one
of the two.
-/

namespace Imc2002P8

open Finset

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in

problem imc2002_p8
    (solved : Fin 200 → Fin 6 → Prop)
    [∀ s p, Decidable (solved s p)]
    (hmany : ∀ p : Fin 6, 120 ≤ (Finset.univ.filter (fun s : Fin 200 => solved s p)).card) :
    ∃ s₁ s₂ : Fin 200, s₁ ≠ s₂ ∧ ∀ p : Fin 6, solved s₁ p ∨ solved s₂ p := by
  -- For each problem p, let missed p = {s | ¬ solved s p}; |missed p| ≤ 80.
  set missed : Fin 6 → Finset (Fin 200) :=
    fun p => Finset.univ.filter (fun s => ¬ solved s p) with hmissed_def
  have hmissed_card : ∀ p : Fin 6, (missed p).card ≤ 80 := by
    intro p
    have h200 : (Finset.univ : Finset (Fin 200)).card = 200 := by
      rw [Finset.card_univ, Fintype.card_fin]
    have hpart := (Finset.univ : Finset (Fin 200)).card_filter_add_card_filter_not
      (fun s => solved s p)
    rw [h200] at hpart
    have := hmany p
    change _ + (missed p).card = _ at hpart
    omega
  by_contra hcon
  -- hcon : ¬ ∃ s₁ s₂, s₁ ≠ s₂ ∧ ∀ p, solved s₁ p ∨ solved s₂ p
  -- We derive: ∀ s₁ s₂, s₁ ≠ s₂ → ∃ p, ¬ solved s₁ p ∧ ¬ solved s₂ p
  have hcon' : ∀ s₁ s₂ : Fin 200, s₁ ≠ s₂ → ∃ p : Fin 6, ¬ solved s₁ p ∧ ¬ solved s₂ p := by
    intro s₁ s₂ hne
    by_contra hneg
    apply hcon
    refine ⟨s₁, s₂, hne, ?_⟩
    intro p
    by_contra hp
    apply hneg
    refine ⟨p, ?_, ?_⟩
    · intro h; apply hp; left; exact h
    · intro h; apply hp; right; exact h
  clear hcon
  -- Every pair of distinct students fails: some problem is missed by both.
  -- Define the set of ordered pairs (s₁, s₂) with s₁ ≠ s₂; its card is 200*199.
  set T : Finset (Fin 200 × Fin 200) :=
    Finset.univ.filter (fun (q : Fin 200 × Fin 200) => q.1 ≠ q.2) with hT_def
  have hT_card : T.card = 200 * 199 := by
    -- T = univ \ diagonal
    have hdiag : Finset.univ.filter (fun (q : Fin 200 × Fin 200) => q.1 = q.2) =
        Finset.univ.image (fun s : Fin 200 => (s, s)) := by
      ext ⟨a, b⟩
      rw [Finset.mem_filter, Finset.mem_image]
      simp only [Finset.mem_univ, true_and]
      refine ⟨fun h => ⟨a, ?_⟩, fun h => ?_⟩
      · exact Prod.ext rfl h
      · obtain ⟨s, hs⟩ := h
        have h1 := (Prod.mk.inj hs).1
        have h2 := (Prod.mk.inj hs).2
        rw [← h1, ← h2]
    have hfilter_eq := (Finset.univ : Finset (Fin 200 × Fin 200)).card_filter_add_card_filter_not
      (fun q : Fin 200 × Fin 200 => q.1 = q.2)
    rw [hdiag] at hfilter_eq
    have h1 : (Finset.univ : Finset (Fin 200 × Fin 200)).card = 40000 := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    have h2 : (Finset.univ.image (fun s : Fin 200 => (s, s))).card = 200 := by
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
      rw [Finset.card_univ, Fintype.card_fin]
    rw [h1, h2] at hfilter_eq
    -- hfilter_eq : 200 + (filter (fun q => ¬ q.1 = q.2) univ).card = 40000
    show (Finset.univ.filter (fun (q : Fin 200 × Fin 200) => q.1 ≠ q.2)).card = 200 * 199
    have : (Finset.univ.filter (fun (q : Fin 200 × Fin 200) => q.1 ≠ q.2)) =
           (Finset.univ.filter (fun (q : Fin 200 × Fin 200) => ¬ q.1 = q.2)) := rfl
    rw [this]
    omega
  -- For each p, define bad pairs for p.
  let U : Fin 6 → Finset (Fin 200 × Fin 200) :=
    fun p => Finset.univ.filter (fun q => ¬ solved q.1 p ∧ ¬ solved q.2 p)
  have hU_card : ∀ p : Fin 6, (U p).card ≤ 80 * 80 := by
    intro p
    have heq : U p = missed p ×ˢ missed p := by
      ext ⟨a, b⟩
      simp [U, missed]
    rw [heq, Finset.card_product]
    exact Nat.mul_le_mul (hmissed_card p) (hmissed_card p)
  -- Each pair in T lies in some U p (since the pair fails and thus misses some problem).
  have hT_sub : T ⊆ (Finset.univ : Finset (Fin 6)).biUnion U := by
    intro q hq
    obtain ⟨a, b⟩ := q
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter]
    exact hcon' a b hq
  -- So |T| ≤ Σ_p |U p| ≤ 6 * 6400 = 38400 < 39800.
  have hsum_le : T.card ≤ ∑ p : Fin 6, (U p).card :=
    (Finset.card_le_card hT_sub).trans (Finset.card_biUnion_le)
  have hsum_bound : ∑ p : Fin 6, (U p).card ≤ 6 * (80 * 80) := by
    calc ∑ p : Fin 6, (U p).card ≤ ∑ _p : Fin 6, 80 * 80 :=
          Finset.sum_le_sum (fun p _ => hU_card p)
      _ = 6 * (80 * 80) := by
          simp
  have : T.card ≤ 6 * (80 * 80) := hsum_le.trans hsum_bound
  rw [hT_card] at this
  omega

end Imc2002P8
