/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 9

Let `p(z)` be a polynomial of degree `n ≥ 1` with complex coefficients.
Prove that there are at least `n + 1` complex numbers `z` for which
`p(z) ∈ {0, 1}`.

The proof counts root multiplicities. Over `ℂ`, both `p` and `p - 1` have
exactly `n` roots (with multiplicity). The derivative `p'` has degree at
most `n - 1`, hence at most `n - 1` roots (with multiplicity). In
characteristic zero, every root `c` of `p` of multiplicity `k ≥ 1` is a
root of `p'` of multiplicity exactly `k - 1` (and similarly for `p - 1`,
whose derivative is also `p'`). Thus, letting `S₀` and `S₁` be the sets
of distinct roots of `p` and `p - 1`,
`|S₀| + |S₁| = (n - ∑_{S₀}(mult p' c)) + (n - ∑_{S₁}(mult p' c))
             = 2n - ∑_{S₀ ⊔ S₁}(mult p' c) ≥ 2n - (n - 1) = n + 1`.
Since `S₀` and `S₁` are disjoint, `|S₀ ∪ S₁| = |S₀| + |S₁| ≥ n + 1`.
-/

namespace Imc2000P9

open Polynomial

problem imc2000_p9 (p : ℂ[X]) (hp : 1 ≤ p.natDegree) :
    p.natDegree + 1 ≤ (p.roots.toFinset ∪ (p - 1).roots.toFinset).card := by
  set n := p.natDegree with hn_def
  have hnpos : 1 ≤ n := hp
  -- `p ≠ 0` since `natDegree p ≥ 1`.
  have hp0 : p ≠ 0 := by
    intro h
    have : p.natDegree = 0 := by rw [h]; exact natDegree_zero
    omega
  -- `p - 1` has the same `natDegree` as `p`.
  have hsub_natDeg : (p - 1).natDegree = n := by
    show (p - C (1 : ℂ)).natDegree = n
    rw [natDegree_sub_C]
  have hp10 : p - 1 ≠ 0 := by
    intro h
    have : (p - 1).natDegree = 0 := by rw [h]; exact natDegree_zero
    rw [hsub_natDeg] at this
    omega
  -- Both `p` and `p - 1` split over ℂ, so root count (with multiplicity) equals `n`.
  have hp_roots_card : p.roots.card = n := IsAlgClosed.card_roots_eq_natDegree
  have hp1_roots_card : (p - 1).roots.card = n := by
    rw [← hsub_natDeg]; exact IsAlgClosed.card_roots_eq_natDegree
  -- The two root sets are disjoint.
  have hdisj : Disjoint p.roots.toFinset (p - 1).roots.toFinset := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [Multiset.mem_toFinset, mem_roots hp0] at hz
    rw [Multiset.mem_toFinset, mem_roots hp10] at hz'
    rw [IsRoot, eval_sub, eval_one, sub_eq_zero] at hz'
    exact zero_ne_one (hz.symm.trans hz')
  set S₀ := p.roots.toFinset with hS₀_def
  set S₁ := (p - 1).roots.toFinset with hS₁_def
  -- `∑_{c ∈ S₀} rootMultiplicity c p = n`.
  have hsum₀ : ∑ c ∈ S₀, p.rootMultiplicity c = n := by
    have : ∑ c ∈ S₀, p.roots.count c = p.roots.card := Multiset.toFinset_sum_count_eq _
    rw [hp_roots_card] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun c _ => (count_roots p).symm)
  have hsum₁ : ∑ c ∈ S₁, (p - 1).rootMultiplicity c = n := by
    have : ∑ c ∈ S₁, (p - 1).roots.count c = (p - 1).roots.card :=
      Multiset.toFinset_sum_count_eq _
    rw [hp1_roots_card] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun c _ => (count_roots (p - 1)).symm)
  -- `(p - 1).derivative = p.derivative`.
  have hderiv_sub : (p - 1).derivative = p.derivative := by
    rw [derivative_sub, derivative_one, sub_zero]
  -- `p'` has `natDegree ≤ n - 1`, hence at most `n - 1` roots with multiplicity.
  have hp'_roots_card : p.derivative.roots.card ≤ n - 1 := by
    calc p.derivative.roots.card
        ≤ p.derivative.natDegree := card_roots' _
      _ ≤ n - 1 := by
          have := natDegree_derivative_lt (R := ℂ) (p := p) (by omega : p.natDegree ≠ 0)
          omega
  -- Key inequality: for each root `c ∈ S₀`, `p.rootMultiplicity c ≤ p'.rootMultiplicity c + 1`.
  have hmult₀ : ∀ c ∈ S₀, p.rootMultiplicity c ≤ p.derivative.rootMultiplicity c + 1 := by
    intro c hc
    rw [hS₀_def, Multiset.mem_toFinset, mem_roots hp0] at hc
    have := derivative_rootMultiplicity_of_root (R := ℂ) hc
    omega
  have hmult₁ : ∀ c ∈ S₁, (p - 1).rootMultiplicity c ≤ p.derivative.rootMultiplicity c + 1 := by
    intro c hc
    rw [hS₁_def, Multiset.mem_toFinset, mem_roots hp10] at hc
    have h := derivative_rootMultiplicity_of_root (R := ℂ) hc
    rw [hderiv_sub] at h
    omega
  -- Hence `n ≤ ∑_{c ∈ S₀} p'.rootMultiplicity c + |S₀|`, similarly for `S₁`.
  have hbound₀ : n ≤ (∑ c ∈ S₀, p.derivative.rootMultiplicity c) + S₀.card := by
    calc n = ∑ c ∈ S₀, p.rootMultiplicity c := hsum₀.symm
      _ ≤ ∑ c ∈ S₀, (p.derivative.rootMultiplicity c + 1) := Finset.sum_le_sum hmult₀
      _ = (∑ c ∈ S₀, p.derivative.rootMultiplicity c) + S₀.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hbound₁ : n ≤ (∑ c ∈ S₁, p.derivative.rootMultiplicity c) + S₁.card := by
    calc n = ∑ c ∈ S₁, (p - 1).rootMultiplicity c := hsum₁.symm
      _ ≤ ∑ c ∈ S₁, (p.derivative.rootMultiplicity c + 1) := Finset.sum_le_sum hmult₁
      _ = (∑ c ∈ S₁, p.derivative.rootMultiplicity c) + S₁.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  -- Sum the two bounds. Use disjointness of `S₀` and `S₁`.
  have hsum_p' : (∑ c ∈ S₀, p.derivative.rootMultiplicity c)
               + (∑ c ∈ S₁, p.derivative.rootMultiplicity c)
               = ∑ c ∈ S₀ ∪ S₁, p.derivative.rootMultiplicity c := by
    rw [← Finset.sum_union hdisj]
  -- Bound the sum over `S₀ ∪ S₁` by `p'.roots.card ≤ n - 1`.
  have hp'_sum_bound :
      ∑ c ∈ S₀ ∪ S₁, p.derivative.rootMultiplicity c ≤ n - 1 := by
    calc ∑ c ∈ S₀ ∪ S₁, p.derivative.rootMultiplicity c
        = ∑ c ∈ S₀ ∪ S₁, p.derivative.roots.count c :=
          Finset.sum_congr rfl (fun c _ => (count_roots _).symm)
      _ ≤ ∑ c ∈ (S₀ ∪ S₁) ∪ p.derivative.roots.toFinset, p.derivative.roots.count c := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.subset_union_left
          · intro _ _ _; exact Nat.zero_le _
      _ = ∑ c ∈ p.derivative.roots.toFinset, p.derivative.roots.count c := by
          symm
          apply Finset.sum_subset Finset.subset_union_right
          intro c _ hc
          rw [Multiset.mem_toFinset] at hc
          exact Multiset.count_eq_zero.mpr hc
      _ = p.derivative.roots.card := Multiset.toFinset_sum_count_eq _
      _ ≤ n - 1 := hp'_roots_card
  -- Combine: `2n ≤ (n - 1) + |S₀| + |S₁|`, so `n + 1 ≤ |S₀| + |S₁|`.
  have hcard_sum : n + 1 ≤ S₀.card + S₁.card := by
    have hsum_combined := add_le_add hbound₀ hbound₁
    -- hsum_combined: n + n ≤ (∑ S₀ p' + |S₀|) + (∑ S₁ p' + |S₁|)
    -- Using hsum_p' and hp'_sum_bound: ∑ S₀ p' + ∑ S₁ p' ≤ n - 1.
    omega
  -- Finally `|S₀ ∪ S₁| = |S₀| + |S₁|` by disjointness.
  rw [Finset.card_union_of_disjoint hdisj]
  exact hcard_sum

end Imc2000P9
