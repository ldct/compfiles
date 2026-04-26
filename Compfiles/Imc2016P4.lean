/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2016, Problem 4

Let `n ≥ k` be positive integers, and let `F` be a family of finite sets
satisfying:
  (i) `F` contains at least `C(n,k) + 1` distinct sets of size exactly `k`;
  (ii) for any `A, B ∈ F`, the union `A ∪ B` is also in `F`.
Prove that `F` contains at least three sets with at least `n` elements.

The strategy: take `C(n,k)+1` "generator" `k`-sets, let `V` be their union.
Then `|V| > n`. Call `v ∈ V` *appropriate* if at most `C(n-1,k-1)` generators
contain it; then `≥ C(n-1,k)+1` generators avoid it, and their union `U` has
size `≥ n` and excludes `v`. By double counting, the number of non-appropriate
elements is at most `n-1`. Pick appropriate `v_1 ∈ V`, then appropriate
`v_2 ∈ U_1` (where `U_1` is the union avoiding `v_1`); the three sets
`V`, `U_1`, `U_2` are distinct, all in `F`, and all of size `≥ n`.
-/

namespace Imc2016P4

open Finset

snip begin

/-- If `T` is a finset of subsets of `V`, each of cardinality `k`, then
`#T ≤ C(#V, k)`. -/
lemma card_le_choose_of_subsets {α : Type*} [DecidableEq α]
    (T : Finset (Finset α)) (V : Finset α) (k : ℕ)
    (hsub : ∀ S ∈ T, S ⊆ V) (hcard : ∀ S ∈ T, S.card = k) :
    T.card ≤ V.card.choose k := by
  have hT_sub : T ⊆ V.powersetCard k := by
    intro S hS
    rw [mem_powersetCard]
    exact ⟨hsub S hS, hcard S hS⟩
  calc T.card ≤ (V.powersetCard k).card := Finset.card_le_card hT_sub
    _ = V.card.choose k := card_powersetCard _ _

/-- Double counting on `T × V`: for `T : Finset (Finset α)`, the sum over
`v ∈ V` of `#{S ∈ T | v ∈ S}` equals the sum over `S ∈ T` of `|S ∩ V|`. -/
lemma sum_deg_eq_sum_inter {α : Type*} [DecidableEq α]
    (T : Finset (Finset α)) (V : Finset α) :
    ∑ v ∈ V, (T.filter (fun S => v ∈ S)).card =
      ∑ S ∈ T, (S ∩ V).card := by
  -- Both sides count pairs (v, S) with v ∈ V, S ∈ T, v ∈ S.
  have lhs_eq : ∑ v ∈ V, (T.filter (fun S => v ∈ S)).card =
      ∑ v ∈ V, ∑ S ∈ T, if v ∈ S then 1 else 0 := by
    apply sum_congr rfl; intro v _
    rw [Finset.card_filter]
  rw [lhs_eq, Finset.sum_comm]
  apply sum_congr rfl
  intro S _
  rw [Finset.card_eq_sum_ones]
  rw [show (S ∩ V) = V.filter (fun v => v ∈ S) from ?_]
  · rw [Finset.sum_filter]
  · ext v
    simp [Finset.mem_inter, and_comm]

/-- Identity `k * C(n,k) = n * C(n-1, k-1)` for `1 ≤ k ≤ n`. -/
lemma k_mul_choose (n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  simp only [Nat.succ_sub_one]
  -- Want: (k'+1) * C(n'+1, k'+1) = (n'+1) * C(n', k')
  -- Standard: Nat.add_one_mul_choose_eq says (n+1) * C(n, k) = (k+1) * C(n+1, k+1).
  have := Nat.add_one_mul_choose_eq n' k'
  -- this : (n' + 1) * C(n' + 1, k' + 1) = C(n', k') * (k' + 1) -- check
  -- Actually let's just use omega/linarith with the lemma.
  linarith [this]

/-- Pascal's rule rearranged: `C(n,k) = C(n-1,k) + C(n-1,k-1)` for `1 ≤ k ≤ n`. -/
lemma choose_pascal (n k : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    Nat.choose n k = Nat.choose (n - 1) k + Nat.choose (n - 1) (k - 1) := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hk)
  simp only [Nat.succ_sub_one]
  rw [Nat.choose_succ_succ' n' k']
  ring

snip end

/-- The problem statement: a family `F` of finite subsets of `ℕ`, closed under
binary unions, containing at least `C(n,k) + 1` distinct `k`-subsets, must
contain at least three sets of cardinality `≥ n`. -/
problem imc2016_p4 (n k : ℕ) (hk : 0 < k) (hnk : k ≤ n) (F : Set (Finset ℕ))
    (G : Finset (Finset ℕ))
    (hG_sub_F : ∀ S ∈ G, S ∈ F)
    (hG_card : ∀ S ∈ G, S.card = k)
    (hG_size : Nat.choose n k + 1 ≤ G.card)
    (hF_union : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) :
    ∃ S₁ ∈ F, ∃ S₂ ∈ F, ∃ S₃ ∈ F,
      S₁ ≠ S₂ ∧ S₁ ≠ S₃ ∧ S₂ ≠ S₃ ∧
      n ≤ S₁.card ∧ n ≤ S₂.card ∧ n ≤ S₃.card := by
  -- Pick a sub-family G₀ ⊆ G with exactly C(n,k) + 1 generators.
  obtain ⟨G₀, hG₀_sub_G, hG₀_card_eq⟩ :=
    Finset.exists_subset_card_eq (n := Nat.choose n k + 1) hG_size
  have hG₀_card : ∀ S ∈ G₀, S.card = k := fun S hS => hG_card S (hG₀_sub_G hS)
  have hG₀_sub_F : ∀ S ∈ G₀, S ∈ F := fun S hS => hG_sub_F S (hG₀_sub_G hS)
  -- Let V = ⋃ G₀.
  set V : Finset ℕ := G₀.biUnion id with hV_def
  have hgen_sub_V : ∀ S ∈ G₀, S ⊆ V := by
    intro S hS x hx; rw [hV_def, mem_biUnion]; exact ⟨S, hS, hx⟩
  -- |V| > n.
  have hV_gt : n < V.card := by
    by_contra h; push Not at h
    have hbound : G₀.card ≤ V.card.choose k :=
      card_le_choose_of_subsets G₀ V k hgen_sub_V hG₀_card
    have hchoose : V.card.choose k ≤ n.choose k := Nat.choose_le_choose k h
    omega
  have hV_ge : n ≤ V.card := le_of_lt hV_gt
  -- Lemma: any nonempty subfamily of G₀ has its biUnion in F.
  have biUnion_in_F : ∀ (H : Finset (Finset ℕ)), H.Nonempty →
      (∀ S ∈ H, S ∈ F) → H.biUnion id ∈ F := by
    intro H hH_ne hHF
    classical
    induction H using Finset.induction with
    | empty => exact absurd hH_ne (by simp)
    | insert A H' hA ih =>
      by_cases hH' : H'.Nonempty
      · rw [biUnion_insert]
        have hA_F : A ∈ F := hHF A (mem_insert_self _ _)
        have hsub : ∀ S ∈ H', S ∈ F := fun S hS => hHF S (mem_insert_of_mem hS)
        have h_ih : H'.biUnion id ∈ F := ih hH' hsub
        simpa using hF_union A hA_F _ h_ih
      · have hH'_eq : H' = ∅ := not_nonempty_iff_eq_empty.mp hH'
        subst hH'_eq
        simp only [biUnion_insert, biUnion_empty, union_empty]
        exact hHF A (mem_insert_self _ _)
  -- G₀ is nonempty.
  have hG₀_ne : G₀.Nonempty := by
    rw [← card_pos]; omega
  have hV_in_F : V ∈ F := biUnion_in_F G₀ hG₀_ne hG₀_sub_F
  -- Now split on whether n = k or n > k.
  by_cases hnk_eq : n = k
  · -- Case n = k. C(n,n) + 1 = 2. Pick A ≠ B ∈ G₀, both of size k = n.
    -- A ∪ B ∈ F has size > k (distinct k-sets) ≥ n. Three distinct sets.
    have hG₀_two : G₀.card ≥ 2 := by
      have hc : Nat.choose n k = 1 := by rw [hnk_eq]; exact Nat.choose_self k
      omega
    -- Pick two distinct elements.
    obtain ⟨A, hA, T, hAT, hAT_eq⟩ : ∃ A ∈ G₀, ∃ T : Finset (Finset ℕ),
        A ∉ T ∧ insert A T = G₀ := by
      obtain ⟨A, hA⟩ := hG₀_ne
      refine ⟨A, hA, G₀.erase A, ?_, ?_⟩
      · exact Finset.notMem_erase A G₀
      · exact Finset.insert_erase hA
    have hT_card : T.card ≥ 1 := by
      have h := Finset.card_insert_of_notMem hAT
      rw [hAT_eq] at h
      omega
    obtain ⟨B, hB⟩ : T.Nonempty := card_pos.mp (by omega)
    have hB_in : B ∈ G₀ := hAT_eq ▸ mem_insert_of_mem hB
    have hAB : A ≠ B := fun heq => hAT (heq ▸ hB)
    have hA_card : A.card = k := hG₀_card A hA
    have hB_card : B.card = k := hG₀_card B hB_in
    have hA_F : A ∈ F := hG₀_sub_F A hA
    have hB_F : B ∈ F := hG₀_sub_F B hB_in
    have hAB_F : A ∪ B ∈ F := hF_union A hA_F B hB_F
    refine ⟨A, hA_F, B, hB_F, A ∪ B, hAB_F, hAB, ?_, ?_, ?_, ?_, ?_⟩
    · -- A ≠ A ∪ B
      intro heq
      apply hAB
      have hBA : B ⊆ A := by
        intro x hx; rw [heq]; exact mem_union_right _ hx
      have := Finset.eq_of_subset_of_card_le hBA (by rw [hA_card, hB_card])
      exact this.symm
    · -- B ≠ A ∪ B
      intro heq
      apply hAB
      have hAB' : A ⊆ B := by
        intro x hx; rw [heq]; exact mem_union_left _ hx
      exact Finset.eq_of_subset_of_card_le hAB' (by rw [hA_card, hB_card])
    · rw [hA_card]; exact hnk_eq.le
    · rw [hB_card]; exact hnk_eq.le
    · calc n ≤ k := hnk_eq.le
        _ = A.card := hA_card.symm
        _ ≤ (A ∪ B).card := Finset.card_le_card Finset.subset_union_left
  · -- Case n > k.
    have hnk_lt : k < n := lt_of_le_of_ne hnk (fun h => hnk_eq h.symm)
    have hn_pos : 0 < n := lt_of_lt_of_le hk hnk
    -- For each v, deg v = #{S ∈ G₀ | v ∈ S}.
    set deg : ℕ → ℕ := fun v => (G₀.filter (fun S => v ∈ S)).card with hdeg_def
    -- Total: ∑_{v ∈ V} deg v = k · #G₀ = k · (C(n,k) + 1).
    have h_total : ∑ v ∈ V, deg v = k * (Nat.choose n k + 1) := by
      have h1 : ∑ v ∈ V, deg v = ∑ S ∈ G₀, (S ∩ V).card :=
        sum_deg_eq_sum_inter G₀ V
      have h2 : ∀ S ∈ G₀, S ∩ V = S := fun S hS =>
        Finset.inter_eq_left.mpr (hgen_sub_V S hS)
      have h3 : ∑ S ∈ G₀, (S ∩ V).card = ∑ S ∈ G₀, k := by
        apply sum_congr rfl; intro S hS; rw [h2 S hS, hG₀_card S hS]
      rw [h1, h3, sum_const, smul_eq_mul, hG₀_card_eq]; ring
    -- "Good" vertices in V: deg v ≤ C(n-1, k-1).
    set Good : Finset ℕ := V.filter (fun v => deg v ≤ Nat.choose (n - 1) (k - 1))
      with hGood_def
    -- Bad := V \ Good has |Bad| ≤ n - 1.
    set Bad : Finset ℕ := V.filter (fun v => Nat.choose (n - 1) (k - 1) < deg v)
      with hBad_def
    have hBad_eq_sdiff : Bad = V \ Good := by
      ext v
      simp [hBad_def, hGood_def, Finset.mem_sdiff, Finset.mem_filter]
      tauto
    have h_bad_lt_n : Bad.card < n := by
      -- Sum over Bad: each deg v ≥ C(n-1,k-1) + 1.
      have h_sum_bad : Bad.card * (Nat.choose (n - 1) (k - 1) + 1) ≤
          ∑ v ∈ Bad, deg v := by
        have h_const : ∑ _v ∈ Bad, (Nat.choose (n - 1) (k - 1) + 1) =
            Bad.card * (Nat.choose (n - 1) (k - 1) + 1) := by
          rw [sum_const, smul_eq_mul]
        rw [← h_const]
        apply Finset.sum_le_sum
        intro v hv
        rw [hBad_def, Finset.mem_filter] at hv
        omega
      have h_sum_le_total : ∑ v ∈ Bad, deg v ≤ ∑ v ∈ V, deg v :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have h_pascal : k * (Nat.choose n k + 1) =
          n * Nat.choose (n - 1) (k - 1) + k := by
        have := k_mul_choose n k hk (Nat.one_le_iff_ne_zero.mpr (by omega))
        linarith
      have h_combined : Bad.card * (Nat.choose (n - 1) (k - 1) + 1) ≤
          n * Nat.choose (n - 1) (k - 1) + k :=
        h_sum_bad.trans (h_sum_le_total.trans (by rw [h_total, h_pascal]))
      -- Strict: < n*(C(n-1,k-1)+1)
      have h_strict : Bad.card * (Nat.choose (n - 1) (k - 1) + 1) <
          n * (Nat.choose (n - 1) (k - 1) + 1) := by
        calc Bad.card * (Nat.choose (n - 1) (k - 1) + 1)
            ≤ n * Nat.choose (n - 1) (k - 1) + k := h_combined
          _ < n * Nat.choose (n - 1) (k - 1) + n := by linarith
          _ = n * (Nat.choose (n - 1) (k - 1) + 1) := by ring
      exact Nat.lt_of_mul_lt_mul_right h_strict
    -- Pick v₁ ∈ Good ∩ V.
    have hGood_sub_V : Good ⊆ V := Finset.filter_subset _ _
    have hGood_card : V.card = Good.card + Bad.card := by
      rw [hBad_eq_sdiff, add_comm]
      exact (Finset.card_sdiff_add_card_eq_card hGood_sub_V).symm
    have hGood_pos : 0 < Good.card := by
      have : V.card ≥ n + 1 := hV_gt
      omega
    obtain ⟨v₁, hv₁⟩ := Finset.card_pos.mp hGood_pos
    have hv₁_V : v₁ ∈ V := hGood_sub_V hv₁
    have hv₁_deg : deg v₁ ≤ Nat.choose (n - 1) (k - 1) := by
      rw [hGood_def, Finset.mem_filter] at hv₁; exact hv₁.2
    -- G₁ = generators avoiding v₁.
    set G₁ : Finset (Finset ℕ) := G₀.filter (fun S => v₁ ∉ S) with hG₁_def
    have hG₁_sub : G₁ ⊆ G₀ := Finset.filter_subset _ _
    have hG₁_card : G₁.card ≥ Nat.choose (n - 1) k + 1 := by
      have h_split : G₀.card = (G₀.filter (fun S => v₁ ∈ S)).card + G₁.card := by
        rw [hG₁_def]
        exact (Finset.card_filter_add_card_filter_not (s := G₀)
          (p := fun S => v₁ ∈ S)).symm
      have h_deg_eq : deg v₁ = (G₀.filter (fun S => v₁ ∈ S)).card := rfl
      have h_pascal := choose_pascal n k hk
        (Nat.one_le_iff_ne_zero.mpr (by omega))
      omega
    -- U₁ = ⋃ G₁.
    set U₁ : Finset ℕ := G₁.biUnion id with hU₁_def
    have hG₁_card_each : ∀ S ∈ G₁, S.card = k := fun S hS =>
      hG₀_card S (hG₁_sub hS)
    have hgen₁_sub : ∀ S ∈ G₁, S ⊆ U₁ := by
      intro S hS x hx; rw [hU₁_def, mem_biUnion]; exact ⟨S, hS, hx⟩
    have hG₁_ne : G₁.Nonempty := by
      rw [← card_pos]; omega
    have hG₁_sub_F : ∀ S ∈ G₁, S ∈ F := fun S hS =>
      hG₀_sub_F S (hG₁_sub hS)
    have hU₁_in_F : U₁ ∈ F := biUnion_in_F G₁ hG₁_ne hG₁_sub_F
    have hU₁_ge : n ≤ U₁.card := by
      by_contra h; push Not at h
      have h_le : U₁.card ≤ n - 1 := by omega
      have hbound : G₁.card ≤ U₁.card.choose k :=
        card_le_choose_of_subsets G₁ U₁ k hgen₁_sub hG₁_card_each
      have h_choose_le : U₁.card.choose k ≤ (n - 1).choose k :=
        Nat.choose_le_choose k h_le
      omega
    have hv₁_not_U₁ : v₁ ∉ U₁ := by
      intro hin
      rw [hU₁_def, mem_biUnion] at hin
      obtain ⟨S, hSG₁, hvS⟩ := hin
      rw [hG₁_def, Finset.mem_filter] at hSG₁
      exact hSG₁.2 hvS
    have hU₁_sub_V : U₁ ⊆ V := by
      intro x hx
      rw [hU₁_def, mem_biUnion] at hx
      obtain ⟨S, hSG₁, hxS⟩ := hx
      exact hgen_sub_V S (hG₁_sub hSG₁) hxS
    -- Now choose v₂ ∈ Good ∩ U₁. Such v₂ exists since |U₁ ∩ Good| ≥ |U₁| - |Bad| ≥ n - (n-1) ≥ 1.
    have hU₁_inter_Good : (U₁ ∩ Good).Nonempty := by
      rw [← card_pos]
      have heq : U₁ ∩ Bad = U₁ \ Good := by
        rw [hBad_eq_sdiff]
        ext x
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hxU, _, hng⟩; exact ⟨hxU, hng⟩
        · rintro ⟨hxU, hng⟩; exact ⟨hxU, hU₁_sub_V hxU, hng⟩
      have h_split_U : U₁.card = (U₁ ∩ Good).card + (U₁ ∩ Bad).card := by
        rw [heq]
        have := Finset.card_inter_add_card_sdiff U₁ Good
        omega
      have h_inter_bad_le : (U₁ ∩ Bad).card ≤ Bad.card :=
        Finset.card_le_card Finset.inter_subset_right
      have hbad_lt : Bad.card < n := h_bad_lt_n
      omega
    obtain ⟨v₂, hv₂⟩ := hU₁_inter_Good
    rw [Finset.mem_inter] at hv₂
    obtain ⟨hv₂_U₁, hv₂_Good⟩ := hv₂
    have hv₂_V : v₂ ∈ V := hGood_sub_V hv₂_Good
    have hv₂_deg : deg v₂ ≤ Nat.choose (n - 1) (k - 1) := by
      rw [hGood_def, Finset.mem_filter] at hv₂_Good; exact hv₂_Good.2
    -- G₂ = generators avoiding v₂.
    set G₂ : Finset (Finset ℕ) := G₀.filter (fun S => v₂ ∉ S) with hG₂_def
    have hG₂_sub : G₂ ⊆ G₀ := Finset.filter_subset _ _
    have hG₂_card : G₂.card ≥ Nat.choose (n - 1) k + 1 := by
      have h_split : G₀.card = (G₀.filter (fun S => v₂ ∈ S)).card + G₂.card := by
        rw [hG₂_def]
        exact (Finset.card_filter_add_card_filter_not (s := G₀)
          (p := fun S => v₂ ∈ S)).symm
      have h_deg_eq : deg v₂ = (G₀.filter (fun S => v₂ ∈ S)).card := rfl
      have h_pascal := choose_pascal n k hk
        (Nat.one_le_iff_ne_zero.mpr (by omega))
      omega
    set U₂ : Finset ℕ := G₂.biUnion id with hU₂_def
    have hG₂_card_each : ∀ S ∈ G₂, S.card = k := fun S hS =>
      hG₀_card S (hG₂_sub hS)
    have hgen₂_sub : ∀ S ∈ G₂, S ⊆ U₂ := by
      intro S hS x hx; rw [hU₂_def, mem_biUnion]; exact ⟨S, hS, hx⟩
    have hG₂_ne : G₂.Nonempty := by
      rw [← card_pos]; omega
    have hG₂_sub_F : ∀ S ∈ G₂, S ∈ F := fun S hS =>
      hG₀_sub_F S (hG₂_sub hS)
    have hU₂_in_F : U₂ ∈ F := biUnion_in_F G₂ hG₂_ne hG₂_sub_F
    have hU₂_ge : n ≤ U₂.card := by
      by_contra h; push Not at h
      have h_le : U₂.card ≤ n - 1 := by omega
      have hbound : G₂.card ≤ U₂.card.choose k :=
        card_le_choose_of_subsets G₂ U₂ k hgen₂_sub hG₂_card_each
      have h_choose_le : U₂.card.choose k ≤ (n - 1).choose k :=
        Nat.choose_le_choose k h_le
      omega
    have hv₂_not_U₂ : v₂ ∉ U₂ := by
      intro hin
      rw [hU₂_def, mem_biUnion] at hin
      obtain ⟨S, hSG₂, hvS⟩ := hin
      rw [hG₂_def, Finset.mem_filter] at hSG₂
      exact hSG₂.2 hvS
    -- The three sets V, U₁, U₂ are distinct.
    -- V ≠ U₁: v₁ ∈ V (good vertices are in V) and v₁ ∉ U₁.
    have hV_ne_U₁ : V ≠ U₁ := fun heq => hv₁_not_U₁ (heq ▸ hv₁_V)
    -- V ≠ U₂: v₂ ∈ V and v₂ ∉ U₂.
    have hV_ne_U₂ : V ≠ U₂ := fun heq => hv₂_not_U₂ (heq ▸ hv₂_V)
    -- U₁ ≠ U₂: v₂ ∈ U₁ and v₂ ∉ U₂.
    have hU₁_ne_U₂ : U₁ ≠ U₂ := fun heq => hv₂_not_U₂ (heq ▸ hv₂_U₁)
    refine ⟨V, hV_in_F, U₁, hU₁_in_F, U₂, hU₂_in_F, hV_ne_U₁, hV_ne_U₂,
      hU₁_ne_U₂, hV_ge, hU₁_ge, hU₂_ge⟩

end Imc2016P4
