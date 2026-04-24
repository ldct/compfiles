/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2023, Problem 8

Let `T` be a tree with `n` vertices. For every pair `{u, v}` of vertices, let
`d(u, v)` denote the distance between them. Consider

  `W(T) = ∑_{{u,v}} d(u,v)`,        `H(T) = ∑_{{u,v}} 1/d(u,v)`.

Prove that `W(T) · H(T) ≥ (n - 1)³ (n + 2) / 4`.
-/

namespace Imc2023P8

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

-- snip begin

/-- Cauchy-Schwarz on a finite set `s` where `d i > 0` for all `i ∈ s`:
    `|s|² ≤ (Σ d) * (Σ 1/d)`. -/
lemma cs_sum_le {ι : Type*} (s : Finset ι) (d : ι → ℚ)
    (hpos : ∀ p ∈ s, 0 < d p) :
    (s.card : ℚ) ^ 2 ≤ (∑ p ∈ s, d p) * (∑ p ∈ s, 1 / d p) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (R := ℚ)
    s (r := fun _ => (1 : ℚ)) (f := d) (g := fun p => 1 / d p)
    (fun i hi => (hpos i hi).le)
    (fun i hi => by have := hpos i hi; positivity)
    (fun i hi => by have := hpos i hi; field_simp)
  have hcard : (∑ _i ∈ s, (1 : ℚ)) = (s.card : ℚ) := by simp
  rw [hcard] at h
  exact h

/-- For `d ≥ 2` in ℚ, we have `d + 1/d ≥ 5/2`. -/
lemma add_inv_ge (d : ℚ) (hd : 2 ≤ d) : 5 / 2 ≤ d + 1 / d := by
  have hd0 : 0 < d := by linarith
  rw [← sub_nonneg]
  have heq : d + 1 / d - 5 / 2 = (2 * d - 1) * (d - 2) / (2 * d) := by
    field_simp; ring
  rw [heq]
  apply div_nonneg
  · have h1 : 0 ≤ 2 * d - 1 := by linarith
    have h2 : 0 ≤ d - 2 := by linarith
    exact mul_nonneg h1 h2
  · linarith

-- snip end

/-- The statement. Requires the graph to be a tree (connected and acyclic). -/
problem imc2023_p8 (G : SimpleGraph V) (hT : G.IsTree) [DecidableRel G.Adj] :
    let n : ℕ := Fintype.card V
    let W : ℚ := (∑ e ∈ (Finset.univ.filter fun p : V × V => p.1 ≠ p.2),
                    (G.dist e.1 e.2 : ℚ)) / 2
    let H : ℚ := (∑ e ∈ (Finset.univ.filter fun p : V × V => p.1 ≠ p.2),
                    (1 : ℚ) / (G.dist e.1 e.2)) / 2
    W * H ≥ ((n - 1 : ℚ) ^ 3 * (n + 2)) / 4 := by
  intro n W H
  classical
  -- Abbreviations
  set U : Finset (V × V) := Finset.univ.filter fun p : V × V => p.1 ≠ p.2 with hU_def
  set E : Finset (V × V) := U.filter fun p => G.Adj p.1 p.2 with hE_def
  set S : Finset (V × V) := U.filter fun p => ¬ G.Adj p.1 p.2 with hS_def
  have hn_pos : 0 < n := Fintype.card_pos_iff.mpr hT.connected.nonempty
  -- Basic disjoint union U = E ∪ S
  have hES_disj : Disjoint E S := by
    rw [hE_def, hS_def]
    exact Finset.disjoint_filter.mpr (fun _ _ h hn => hn h)
  have hES_union : E ∪ S = U := by
    rw [hE_def, hS_def, ← Finset.filter_or]
    ext p
    simp [em (G.Adj p.1 p.2)]
  -- Every pair in E has distance 1, every pair in S has distance ≥ 2.
  have hE_dist : ∀ p ∈ E, G.dist p.1 p.2 = 1 := by
    intro p hp
    rw [hE_def, Finset.mem_filter] at hp
    exact SimpleGraph.dist_eq_one_iff_adj.mpr hp.2
  have hS_dist : ∀ p ∈ S, 2 ≤ G.dist p.1 p.2 := by
    intro p hp
    rw [hS_def, Finset.mem_filter, hU_def, Finset.mem_filter] at hp
    obtain ⟨⟨_, hne⟩, hnadj⟩ := hp
    have hpos : 0 < G.dist p.1 p.2 := hT.connected.pos_dist_of_ne hne
    rcases Nat.lt_or_ge (G.dist p.1 p.2) 2 with h | h
    · exfalso
      have hdist1 : G.dist p.1 p.2 = 1 := by omega
      exact hnadj (SimpleGraph.dist_eq_one_iff_adj.mp hdist1)
    · exact h
  -- Cardinalities.
  have hU_card : U.card = n * (n - 1) := by
    have hU_eq_offDiag : U = (Finset.univ : Finset V).offDiag := by
      rw [hU_def]; ext p; simp [Finset.mem_offDiag]
    rw [hU_eq_offDiag, Finset.offDiag_card, Finset.card_univ]
    -- goal: Fintype.card V * Fintype.card V - Fintype.card V = n * (n - 1)
    -- Since n = Fintype.card V, and n ≥ 1:
    show n * n - n = n * (n - 1)
    cases hcase : n with
    | zero => simp
    | succ k => rw [Nat.mul_sub_one]
  -- E is exactly filter over all pairs (including p.1 = p.2 is impossible).
  have hE_eq : E = (Finset.univ : Finset (V × V)).filter fun (x, y) => G.Adj x y := by
    rw [hE_def, hU_def]
    ext ⟨x, y⟩
    simp
    intro hadj
    exact G.ne_of_adj hadj
  have hE_card : E.card = 2 * (n - 1) := by
    have hedge : G.edgeFinset.card + 1 = n := hT.card_edgeFinset
    have : 2 * G.edgeFinset.card =
        (Finset.univ.filter fun (xy : V × V) => G.Adj xy.1 xy.2).card :=
      SimpleGraph.two_mul_card_edgeFinset G
    rw [hE_eq, ← this]
    omega
  have hS_card : S.card = (n - 1) * (n - 2) := by
    have hU_eq : E.card + S.card = U.card := by
      rw [← Finset.card_union_of_disjoint hES_disj, hES_union]
    rw [hU_card, hE_card] at hU_eq
    -- hU_eq : 2 * (n - 1) + S.card = n * (n - 1)
    -- We want: S.card = (n - 1) * (n - 2)
    have key : n * (n - 1) = 2 * (n - 1) + (n - 1) * (n - 2) := by
      rcases hcase : n with _ | _ | k
      · rfl
      · rfl
      · -- n = k + 2
        show (k + 2) * (k + 1) = 2 * (k + 1) + (k + 1) * k
        ring
    omega
  -- Now work on the sums.
  -- Split W and H over E ∪ S.
  have hW_split : 2 * W = ∑ p ∈ E, (G.dist p.1 p.2 : ℚ) +
                            ∑ p ∈ S, (G.dist p.1 p.2 : ℚ) := by
    show 2 * ((∑ e ∈ U, (G.dist e.1 e.2 : ℚ)) / 2) = _
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℚ) ≠ 0)]
    rw [← hES_union, Finset.sum_union hES_disj]
  have hH_split : 2 * H = ∑ p ∈ E, (1 : ℚ) / (G.dist p.1 p.2 : ℚ) +
                            ∑ p ∈ S, (1 : ℚ) / (G.dist p.1 p.2 : ℚ) := by
    show 2 * ((∑ e ∈ U, (1 : ℚ) / (G.dist e.1 e.2 : ℚ)) / 2) = _
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℚ) ≠ 0)]
    rw [← hES_union, Finset.sum_union hES_disj]
  -- (n - 1 : ℕ) cast to ℚ equals (n : ℚ) - 1 since n ≥ 1.
  have hn1_cast : (↑(n - 1) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub hn_pos]; push_cast; ring
  -- Sum over E: distance is 1.
  have hEcard_Q : (E.card : ℚ) = 2 * (n - 1 : ℚ) := by
    rw [hE_card]; push_cast; rw [hn1_cast]
  have hE_sum_d : ∑ p ∈ E, (G.dist p.1 p.2 : ℚ) = 2 * (n - 1 : ℚ) := by
    have : ∀ p ∈ E, (G.dist p.1 p.2 : ℚ) = 1 := fun p hp => by
      rw [hE_dist p hp]; rfl
    rw [Finset.sum_congr rfl this, Finset.sum_const, ← hEcard_Q]
    simp
  have hE_sum_inv : ∑ p ∈ E, (1 : ℚ) / (G.dist p.1 p.2 : ℚ) = 2 * (n - 1 : ℚ) := by
    have heq : ∀ p ∈ E, (1 : ℚ) / (G.dist p.1 p.2 : ℚ) = 1 := fun p hp => by
      rw [hE_dist p hp]; norm_num
    rw [Finset.sum_congr rfl heq, Finset.sum_const, ← hEcard_Q]
    simp
  -- For S, define A = sum of d, B = sum of 1/d.
  set A : ℚ := ∑ p ∈ S, (G.dist p.1 p.2 : ℚ) with hA_def
  set B : ℚ := ∑ p ∈ S, (1 : ℚ) / (G.dist p.1 p.2 : ℚ) with hB_def
  -- d p > 0 for p ∈ S.
  have hS_pos : ∀ p ∈ S, (0 : ℚ) < (G.dist p.1 p.2 : ℚ) := by
    intro p hp
    have := hS_dist p hp
    have : (2 : ℚ) ≤ (G.dist p.1 p.2 : ℚ) := by exact_mod_cast this
    linarith
  -- Cauchy-Schwarz on S.
  have hScard_Q : (S.card : ℚ) = (n - 1 : ℚ) * (n - 2 : ℚ) := by
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- n = 1 (since 0 < n < 2)
      have hn1 : n = 1 := by omega
      rw [hS_card, hn1]
      norm_num
    · rw [hS_card]
      have h2' : (↑(n - 2) : ℚ) = (n : ℚ) - 2 := by
        rw [Nat.cast_sub h2]; push_cast; ring
      rw [Nat.cast_mul, hn1_cast, h2']
  have hCS : ((n - 1 : ℚ) * (n - 2 : ℚ)) ^ 2 ≤ A * B := by
    have h := cs_sum_le S (fun p => (G.dist p.1 p.2 : ℚ)) hS_pos
    rw [hScard_Q] at h
    exact h
  -- A + B ≥ (5/2) * |S|.
  have hAB_sum : (5 / 2 : ℚ) * ((n - 1) * (n - 2)) ≤ A + B := by
    rw [hA_def, hB_def, ← Finset.sum_add_distrib]
    have h1 : ∀ p ∈ S, (5 / 2 : ℚ) ≤ (G.dist p.1 p.2 : ℚ) + 1 / (G.dist p.1 p.2 : ℚ) := by
      intro p hp
      have h2 : (2 : ℚ) ≤ (G.dist p.1 p.2 : ℚ) := by exact_mod_cast hS_dist p hp
      exact add_inv_ge _ h2
    calc (5 / 2 : ℚ) * ((n - 1) * (n - 2))
        = (S.card : ℚ) * (5 / 2) := by
          rw [hScard_Q]; ring
      _ = ∑ _p ∈ S, (5 / 2 : ℚ) := by
          simp [mul_comm]
      _ ≤ ∑ p ∈ S, ((G.dist p.1 p.2 : ℚ) + 1 / (G.dist p.1 p.2 : ℚ)) :=
          Finset.sum_le_sum h1
  -- Now combine: (2W)(2H) = 4 W H.
  have h2W : 2 * W = 2 * (n - 1 : ℚ) + A := by
    rw [hW_split, hE_sum_d]
  have h2H : 2 * H = 2 * (n - 1 : ℚ) + B := by
    rw [hH_split, hE_sum_inv]
  -- Compute (2W)(2H) ≥ (n-1)^3 (n+2).
  have hkey : (2 * W) * (2 * H) ≥ (n - 1 : ℚ) ^ 3 * (n + 2) := by
    rw [h2W, h2H]
    -- (2(n-1) + A)(2(n-1) + B) = 4(n-1)^2 + 2(n-1)(A+B) + A*B
    have hexp : (2 * (n - 1 : ℚ) + A) * (2 * (n - 1) + B) =
        4 * (n - 1) ^ 2 + 2 * (n - 1) * (A + B) + A * B := by ring
    rw [hexp]
    have hn1 : (0 : ℚ) ≤ n - 1 := by
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn_pos
      linarith
    -- bound
    have h_ab_sum_scaled : 2 * (n - 1 : ℚ) * (A + B) ≥
        2 * (n - 1) * ((5 / 2) * ((n - 1) * (n - 2))) := by
      exact mul_le_mul_of_nonneg_left hAB_sum (by linarith)
    have h_ab_prod : A * B ≥ ((n - 1 : ℚ) * (n - 2)) ^ 2 := hCS
    have : 4 * (n - 1 : ℚ) ^ 2 + 2 * (n - 1) * (A + B) + A * B ≥
        4 * (n - 1) ^ 2 + 2 * (n - 1) * ((5 / 2) * ((n - 1) * (n - 2))) +
        ((n - 1) * (n - 2)) ^ 2 := by
      linarith
    apply le_trans _ this
    have hrhs : 4 * (n - 1 : ℚ) ^ 2 + 2 * (n - 1) * ((5 / 2) * ((n - 1) * (n - 2))) +
        ((n - 1) * (n - 2)) ^ 2 = (n - 1) ^ 2 * (n ^ 2 + n - 2) := by ring
    rw [hrhs]
    have hfact : (n - 1 : ℚ) ^ 2 * (n ^ 2 + n - 2) = (n - 1) ^ 3 * (n + 2) := by ring
    rw [hfact]
  -- Finally derive W * H ≥ (n-1)^3 (n+2) / 4.
  have : 4 * (W * H) = (2 * W) * (2 * H) := by ring
  linarith [hkey]

end Imc2023P8
