/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 9
(IMC 2007, Day 2, Problem 3)

Let `C ⊆ ℝ` be a nonempty, closed, bounded set and let `f : C → C` be a
continuous, nondecreasing function. Show that there exists a point `p ∈ C`
with `f(p) = p`.
-/

namespace Imc2007P9

snip begin

/-
Sketch. Let `T = {x ∈ C : x ≤ f x}`. Since `inf C ∈ C`, and
`f (inf C) ∈ C`, we have `inf C ≤ f (inf C)`, so `inf C ∈ T` and `T` is
nonempty. `T` is bounded above by `sup C`. Let `p = sup T`. Choose a
sequence in `T` converging to `p`; since `T ⊆ C` and `C` is closed,
`p ∈ C`. Continuity and monotonicity give `p ≤ f p`, so `p ∈ T`. Then
`f p ∈ C` and by monotonicity `f p ≤ f (f p)`, so `f p ∈ T`, hence
`f p ≤ p`. Thus `f p = p`.
-/

snip end

problem imc2007_p9
    (C : Set ℝ) (hne : C.Nonempty) (hclo : IsClosed C)
    (hbdd : Bornology.IsBounded C)
    (f : C → C) (hcont : Continuous f) (hmono : Monotone f) :
    ∃ p : C, f p = p := by
  -- `C` is bounded above and below; let `a = sInf C`, `b = sSup C`.
  have hba : BddAbove C := hbdd.bddAbove
  have hbb : BddBelow C := hbdd.bddBelow
  set a : ℝ := sInf C with ha_def
  set b : ℝ := sSup C with hb_def
  have ha_mem : a ∈ C := hclo.csInf_mem hne hbb
  have hb_mem : b ∈ C := hclo.csSup_mem hne hba
  -- Consider the set `T = { x : C | (x : ℝ) ≤ f x }`.
  let T : Set C := { x : C | (x : ℝ) ≤ (f x : ℝ) }
  -- `⟨a, ha_mem⟩ ∈ T` since `a ≤ f a`.
  have haT : (⟨a, ha_mem⟩ : C) ∈ T := by
    show (a : ℝ) ≤ (f ⟨a, ha_mem⟩ : ℝ)
    have : (f ⟨a, ha_mem⟩ : ℝ) ∈ C := (f ⟨a, ha_mem⟩).2
    exact csInf_le hbb this
  have hTne : T.Nonempty := ⟨⟨a, ha_mem⟩, haT⟩
  -- Take the image `T' = Subtype.val '' T ⊆ C ⊆ ℝ`.
  let T' : Set ℝ := Subtype.val '' T
  have hT'ne : T'.Nonempty := hTne.image _
  have hT'sub : T' ⊆ C := by
    rintro _ ⟨⟨y, hy⟩, _, rfl⟩; exact hy
  have hT'bdd : BddAbove T' := hba.mono hT'sub
  set p : ℝ := sSup T' with hp_def
  -- Show `p ∈ C` by taking a sequence in `T'` converging to `p`.
  have hp_mem_C : p ∈ C := by
    -- Every element of `T'` is `≤ p`, and `p = sSup T'`. There is a
    -- sequence in `T'` converging to `p`; since `T' ⊆ C` and `C` is closed,
    -- `p ∈ C`.
    have hp_ub : ∀ x ∈ T', x ≤ p := fun x hx => le_csSup hT'bdd hx
    have hp_mc : ∀ ε > 0, ∃ x ∈ T', p - ε < x := by
      intro ε hε
      have hlt : p - ε < p := by linarith
      obtain ⟨x, hx_mem, hx_gt⟩ := exists_lt_of_lt_csSup hT'ne hlt
      exact ⟨x, hx_mem, hx_gt⟩
    -- Build a sequence (xₙ) with xₙ ∈ T' and p - 1/(n+1) < xₙ ≤ p.
    have : ∀ n : ℕ, ∃ x ∈ T', p - 1 / (n + 1 : ℝ) < x := by
      intro n
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      exact hp_mc _ hpos
    choose xseq hxseq_mem hxseq_gt using this
    have hxseq_le : ∀ n, xseq n ≤ p := fun n => hp_ub _ (hxseq_mem n)
    have hxseq_tendsto : Filter.Tendsto xseq Filter.atTop (nhds p) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      -- Choose N so that 1/(N+1) < ε.
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn_ge : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have h1 : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
        apply one_div_le_one_div_of_le
        · exact_mod_cast Nat.succ_pos N
        · linarith
      have h2 : 1 / (N + 1 : ℝ) < ε := by
        have hNpos : (0 : ℝ) < N + 1 := by positivity
        rw [div_lt_iff₀ hNpos]
        have : 1 / ε < N + 1 := by linarith
        have hεpos : (0 : ℝ) < ε := hε
        rw [div_lt_iff₀ hεpos] at this
        linarith
      rw [Real.dist_eq, abs_lt]
      constructor
      · have := hxseq_gt n
        linarith
      · have := hxseq_le n
        linarith
    -- Apply closedness: xseq n ∈ C, xseq n → p, so p ∈ C.
    exact hclo.mem_of_tendsto hxseq_tendsto
      (Filter.Eventually.of_forall (fun n => hT'sub (hxseq_mem n)))
  -- Now set pC := ⟨p, hp_mem_C⟩ : C.
  set pC : C := ⟨p, hp_mem_C⟩ with hpC_def
  -- Show p ≤ f p.
  have hp_le_fp : p ≤ (f pC : ℝ) := by
    -- From a sequence in T' converging to p, use continuity of f and monotonicity.
    have hp_mc : ∀ ε > 0, ∃ x ∈ T', p - ε < x := by
      intro ε hε
      have hlt : p - ε < p := by linarith
      obtain ⟨x, hx_mem, hx_gt⟩ := exists_lt_of_lt_csSup hT'ne hlt
      exact ⟨x, hx_mem, hx_gt⟩
    have : ∀ n : ℕ, ∃ x ∈ T', p - 1 / (n + 1 : ℝ) < x := by
      intro n
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      exact hp_mc _ hpos
    choose xseq hxseq_mem hxseq_gt using this
    have hxseq_le : ∀ n, xseq n ≤ p := fun n => le_csSup hT'bdd (hxseq_mem n)
    -- Extract the preimages in T ⊆ C.
    have hxpre : ∀ n, ∃ y : C, y ∈ T ∧ (y : ℝ) = xseq n := by
      intro n
      obtain ⟨y, hy_mem, hy_eq⟩ := hxseq_mem n
      exact ⟨y, hy_mem, hy_eq⟩
    choose yseq hyseq_memT hyseq_eq using hxpre
    have hyseq_lefyseq : ∀ n, (yseq n : ℝ) ≤ (f (yseq n) : ℝ) := fun n => hyseq_memT n
    -- (yseq n : ℝ) → p via hyseq_eq.
    have hxseq_tendsto : Filter.Tendsto xseq Filter.atTop (nhds p) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      have hn_ge : (N : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
        apply one_div_le_one_div_of_le
        · exact_mod_cast Nat.succ_pos N
        · linarith
      have h2 : 1 / (N + 1 : ℝ) < ε := by
        have hNpos : (0 : ℝ) < N + 1 := by positivity
        rw [div_lt_iff₀ hNpos]
        have hh : 1 / ε < N + 1 := by linarith
        rw [div_lt_iff₀ hε] at hh
        linarith
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [hxseq_gt n]
      · linarith [hxseq_le n]
    have hyseq_tendsto : Filter.Tendsto (fun n => (yseq n : ℝ)) Filter.atTop (nhds p) := by
      have h_eq : ∀ n, (yseq n : ℝ) = xseq n := hyseq_eq
      refine hxseq_tendsto.congr ?_
      intro n; exact (h_eq n).symm
    -- yseq n → pC in C (subtype topology).
    have hyseq_tendsto_C : Filter.Tendsto yseq Filter.atTop (nhds pC) := by
      rw [tendsto_subtype_rng]
      exact hyseq_tendsto
    -- By continuity, f (yseq n) → f pC.
    have hfyseq_tendsto_C : Filter.Tendsto (fun n => f (yseq n)) Filter.atTop (nhds (f pC)) :=
      hcont.tendsto pC |>.comp hyseq_tendsto_C
    have hfyseq_tendsto : Filter.Tendsto (fun n => (f (yseq n) : ℝ)) Filter.atTop
        (nhds (f pC : ℝ)) := by
      have hcont_val : Continuous (fun x : C => (f x : ℝ)) :=
        continuous_subtype_val.comp hcont
      exact (hcont_val.tendsto pC).comp hyseq_tendsto_C
    -- For all n, (yseq n : ℝ) ≤ (f (yseq n) : ℝ). Take limit.
    exact le_of_tendsto_of_tendsto' hyseq_tendsto hfyseq_tendsto hyseq_lefyseq
  -- Now pC ∈ T.
  have hpCT : pC ∈ T := hp_le_fp
  -- Show f pC ≤ pC, i.e., (f pC : ℝ) ≤ p.
  -- By monotonicity: pC ≤ f pC in C means (pC : ℝ) ≤ (f pC : ℝ), so f pC ≤ f (f pC),
  -- i.e., f pC ∈ T. Thus (f pC : ℝ) ∈ T' ≤ p.
  have hfpC_T : f pC ∈ T := by
    show (f pC : ℝ) ≤ (f (f pC) : ℝ)
    have hle : pC ≤ f pC := hp_le_fp
    have := hmono hle
    exact this
  have hfpC_T' : (f pC : ℝ) ∈ T' := ⟨f pC, hfpC_T, rfl⟩
  have hfpC_le_p : (f pC : ℝ) ≤ p := le_csSup hT'bdd hfpC_T'
  -- Conclude f pC = pC.
  refine ⟨pC, ?_⟩
  apply Subtype.ext
  show (f pC : ℝ) = (pC : ℝ)
  linarith

end Imc2007P9
