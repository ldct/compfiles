/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory, .Combinatorics] }

/-!
# International Mathematical Competition 2014, Problem 6

For a positive integer `x`, denote its `n`-th decimal digit by
`d_n(x) ∈ {0, 1, …, 9}` (so `x = ∑_{n=1}^∞ d_n(x) · 10^{n-1}`). Suppose
that for some sequence `(a_n)_{n=1}^∞` there are only finitely many zeros
in the sequence `(d_n(a_n))`. Prove that there are infinitely many positive
integers that do not occur in `(a_n)`.

## Solution sketch

Suppose `d_n(a_n) ≠ 0` for all `n ≥ n₀`. The presence of a non-zero
digit at position `n` forces `a_n ≥ 10^{n-1}`. Hence for any `N ≥ n₀`,
all values `a_m` with `m ≥ N` are at least `10^{N-1}`, so positive
integers in `[1, 10^{N-1})` can only be hit by `a_1, …, a_{N-1}`. As
`N → ∞`, the number of missing positive integers below `10^{N-1}` is at
least `10^{N-1} - (N - 1) → ∞`.
-/

namespace Imc2014P6

open Finset

/-- The `n`-th decimal digit of `x` (`n ≥ 1`), defined as
`(x / 10^{n-1}) % 10`. -/
def dn (n x : ℕ) : ℕ := (x / 10 ^ (n - 1)) % 10

snip begin

/-- If the `n`-th decimal digit of `x` is non-zero (and `n ≥ 1`), then
`x ≥ 10^{n-1}`. -/
lemma le_of_dn_ne_zero {n x : ℕ} (h : dn n x ≠ 0) :
    10 ^ (n - 1) ≤ x := by
  unfold dn at h
  -- If x < 10^(n-1), then x / 10^(n-1) = 0, so its mod is 0.
  by_contra hlt
  push_neg at hlt
  have hdiv : x / 10 ^ (n - 1) = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv] at h
  exact h rfl

/-- Pure-arithmetic lower bound: `10 ^ k ≥ 2 * k + 2` for `k ≥ 1`. -/
lemma pow_ten_ge {k : ℕ} (hk : 1 ≤ k) : 2 * k + 2 ≤ 10 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk' : k = 0
      · subst hk'; norm_num
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk'
        have ih' := ih hk1
        have hp : 1 ≤ 10 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
        calc 2 * (k + 1) + 2 = 2 * k + 2 + 2 := by ring
          _ ≤ 10 ^ k + 2 := by omega
          _ ≤ 10 ^ k + 10 ^ k * 9 := by nlinarith
          _ = 10 ^ (k + 1) := by ring

snip end

problem imc2014_p6 (a : ℕ → ℕ)
    (h : ∃ n₀, ∀ n ≥ n₀, 1 ≤ n → dn n (a n) ≠ 0) :
    {m : ℕ | 0 < m ∧ ∀ n, a n ≠ m}.Infinite := by
  obtain ⟨n₀, hn₀⟩ := h
  -- Strategy: show the set of missing positive integers is not finite, by
  -- exhibiting arbitrarily many elements in it.
  rw [Set.infinite_iff_exists_gt]
  intro M
  -- Choose N large enough.
  let N := max (max n₀ 1) (M + 2)
  have hN1 : 1 ≤ N := le_max_of_le_left (le_max_right _ _)
  have hNn₀ : n₀ ≤ N := le_max_of_le_left (le_max_left _ _)
  have hNM : M + 2 ≤ N := le_max_right _ _
  -- The set S of "small" positive integers in [1, 10^(N-1)).
  let S : Finset ℕ := (Finset.range (10 ^ (N - 1))).filter (fun m => 0 < m)
  -- S has size 10^(N-1) - 1.
  have hScard : S.card = 10 ^ (N - 1) - 1 := by
    have h1 : S = (Finset.range (10 ^ (N - 1))).erase 0 := by
      ext x
      simp [S, Finset.mem_erase, Nat.pos_iff_ne_zero]
      tauto
    rw [h1, Finset.card_erase_of_mem]
    · rw [Finset.card_range]
    · exact Finset.mem_range.mpr (by positivity)
  -- The image set: {a 0, a 1, …, a (N-1)}.
  let T : Finset ℕ := (Finset.range N).image a
  -- |T| ≤ N.
  have hTcard : T.card ≤ N := by
    apply (Finset.card_image_le).trans
    rw [Finset.card_range]
  -- Key: every m ∈ S not in T is missing from (a n) entirely.
  -- Because for n ≥ N, a n ≥ 10^(n-1) ≥ 10^(N-1) > m.
  have ha_large : ∀ n ≥ N, 10 ^ (N - 1) ≤ a n := by
    intro n hnN
    have hn1 : 1 ≤ n := le_trans hN1 hnN
    have hnn₀ : n₀ ≤ n := le_trans hNn₀ hnN
    have hnz : dn n (a n) ≠ 0 := hn₀ n hnn₀ hn1
    have hmono : 10 ^ (N - 1) ≤ 10 ^ (n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans hmono (le_of_dn_ne_zero hnz)
  -- The missing set: S \ T.
  let Miss : Finset ℕ := S \ T
  -- Each element of Miss is a positive integer not occurring in (a n).
  have hMiss_subset : ∀ m ∈ Miss,
      0 < m ∧ ∀ n, a n ≠ m := by
    intro m hm
    rw [mem_sdiff] at hm
    obtain ⟨hmS, hmT⟩ := hm
    have hmpos : 0 < m := (mem_filter.mp hmS).2
    have hmlt : m < 10 ^ (N - 1) := mem_range.mp (mem_filter.mp hmS).1
    refine ⟨hmpos, ?_⟩
    intro n hcontra
    by_cases hnN : n < N
    · -- a n ∈ T but m ∉ T, contradiction
      apply hmT
      rw [mem_image]
      exact ⟨n, mem_range.mpr hnN, hcontra⟩
    · push_neg at hnN
      have := ha_large n hnN
      rw [hcontra] at this
      omega
  -- |Miss| ≥ |S| - |T| ≥ 10^(N-1) - 1 - N.
  have hMiss_card : 10 ^ (N - 1) - 1 - N ≤ Miss.card := by
    have h1 : S.card - T.card ≤ Miss.card := by
      have := Finset.le_card_sdiff T S
      omega
    omega
  -- And 10^(N-1) - 1 - N ≥ M + 1.  Since N ≥ M + 2, we have N - 1 ≥ M + 1, so
  -- 2*(N-1) + 1 ≥ 2*M + 3 ≥ N + M + 2 (using N - 1 ≥ M + 1 again).
  have hbound : M + 1 ≤ 10 ^ (N - 1) - 1 - N := by
    have hN1 : 1 ≤ N - 1 := by omega
    have hpow : 2 * (N - 1) + 2 ≤ 10 ^ (N - 1) := pow_ten_ge hN1
    omega
  -- So |Miss| ≥ M + 1, meaning Miss has > M elements.
  have hMcard_gt : M < Miss.card := by omega
  -- Pick `M + 1` distinct elements of Miss; we just need one element greater
  -- than `M` in the missing set.  Actually we want `Set.Infinite`; the form
  -- `infinite_iff_exists_gt` asks for an element > M in the set.
  -- Since |Miss| > M, by pigeonhole some element of Miss is > M (as Miss ⊆ ℕ).
  -- Actually any finset with cardinality > M has an element > M iff the set
  -- isn't contained in {0, …, M}. But Miss ⊆ {1, …, 10^(N-1) - 1}; if
  -- |Miss| > M, there must be an element greater than M (since {1, …, M} has
  -- cardinality M).
  -- Use the fact that Miss \ Finset.Icc 1 M has positive cardinality.
  have hMiss_not_subset : ¬ Miss ⊆ Finset.Icc 1 M := by
    intro hsub
    have : Miss.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  -- ∃ x ∈ Miss, x ∉ Icc 1 M.
  obtain ⟨x, hxMiss, hxNotIcc⟩ := Finset.not_subset.mp hMiss_not_subset
  obtain ⟨hxpos, hxmiss⟩ := hMiss_subset x hxMiss
  -- x ∉ Icc 1 M and 0 < x means M < x.
  have hxgt : M < x := by
    rw [Finset.mem_Icc] at hxNotIcc
    push_neg at hxNotIcc
    by_cases hxM : x ≤ M
    · exact absurd (hxNotIcc hxpos) (by omega)
    · omega
  refine ⟨x, ⟨hxpos, hxmiss⟩, hxgt⟩

end Imc2014P6
