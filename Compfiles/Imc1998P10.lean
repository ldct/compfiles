/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 1998, Problem 10 (Day 2, Problem 4)

For `n ≥ 3`, let `Aₙ = {1, …, n}` and let `𝓕` be the set of non-constant
functions `f : Aₙ → Aₙ` satisfying

* `f(k) ≤ f(k+1)` for `1 ≤ k ≤ n-1` (monotonicity), and
* `f(k) = f(f(k+1))` for `1 ≤ k ≤ n-1`.

Determine `|𝓕|`.

## Answer

`|𝓕| = (n choose 3)`.

## Solution sketch

Every `f ∈ 𝓕` has the following form, parameterised by integers
`1 ≤ k < l ≤ m ≤ n-1`:

  `f(i) = k`        for `i ≤ m`,
  `f(m+1) = l`,
  `f(i) = i - 1`    for `i ≥ m + 2`.

The number of such triples `(k, l, m)` equals the number of triples
`1 ≤ k < l < m+1 ≤ n` (substituting `m' = m + 1`), which is `(n choose 3)`.

The forward direction — that every `f ∈ 𝓕` is of this form — proceeds by a
case analysis on `f(n)` and uses the relation `f(k) = f(f(k+1))` together with
monotonicity to pin down `f` uniquely.
-/

namespace Imc1998P10

open Finset

-- We model `Aₙ = {1, …, n}` as the subtype `{i : ℕ // 1 ≤ i ∧ i ≤ n}`.
-- Working with this 1-based view matches the problem statement directly. We
-- encode functions on `Aₙ` as `f : ℕ → ℕ` together with the side conditions
-- that `1 ≤ f i ≤ n` whenever `1 ≤ i ≤ n`; this avoids fighting with `Fin`
-- arithmetic.

/-- The set `𝓕`: non-constant maps `f : ℕ → ℕ` such that
* `f` sends `{1, …, n}` into `{1, …, n}`;
* `f` is monotone on `{1, …, n}`;
* the functional equation `f k = f (f (k+1))` holds for `1 ≤ k ≤ n-1`;
* `f` is not constant on `{1, …, n}`.
-/
def Family (n : ℕ) : Set (ℕ → ℕ) :=
  { f | (∀ i, 1 ≤ i → i ≤ n → 1 ≤ f i ∧ f i ≤ n) ∧
        (∀ k, 1 ≤ k → k ≤ n - 1 → f k ≤ f (k + 1)) ∧
        (∀ k, 1 ≤ k → k ≤ n - 1 → f k = f (f (k + 1))) ∧
        (¬ ∃ c, ∀ i, 1 ≤ i → i ≤ n → f i = c) }

/-- The explicit family of solutions, parameterised by a triple `(k, l, m)`
with `1 ≤ k < l ≤ m ≤ n - 1`.

The function `mkFun` is:

* `f i = k`     for `1 ≤ i ≤ m`;
* `f (m+1) = l`;
* `f i = i - 1` for `m + 2 ≤ i ≤ n`.

Outside `{1, …, n}` we set `f` to `1` (this junk value will not be used).
-/
def mkFun (k l m : ℕ) : ℕ → ℕ :=
  fun i => if i ≤ m then k else if i = m + 1 then l else i - 1

/-- For valid parameters, `mkFun k l m` maps `{1, …, n}` into itself. -/
lemma mkFun_mem_range
    {n k l m : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hlm : l ≤ m) (hmn : m ≤ n - 1)
    (hn : 1 ≤ n) :
    ∀ i, 1 ≤ i → i ≤ n → 1 ≤ mkFun k l m i ∧ mkFun k l m i ≤ n := by
  intro i h1 hin
  unfold mkFun
  have hmlt : m + 1 ≤ n := by omega
  split_ifs with hi hi'
  · refine ⟨hk, ?_⟩
    have : k ≤ m := by omega
    omega
  · refine ⟨?_, ?_⟩
    · omega
    · omega
  · refine ⟨?_, ?_⟩
    · -- i > m, i ≠ m+1, so i ≥ m+2 ≥ 2; thus i - 1 ≥ 1
      omega
    · omega

/-- For valid parameters, `mkFun k l m` is monotone on `{1, …, n-1} → {1, …, n}`. -/
lemma mkFun_mono
    {n k l m : ℕ} (_hk : 1 ≤ k) (hkl : k < l) (hlm : l ≤ m) (_hmn : m ≤ n - 1) :
    ∀ i, 1 ≤ i → i ≤ n - 1 → mkFun k l m i ≤ mkFun k l m (i + 1) := by
  intro i _ _
  unfold mkFun
  split_ifs with h1 h2 h3 h4 h5
  all_goals first | rfl | omega

/-- Value of `mkFun` when the input is `≤ m`. -/
lemma mkFun_le_m (k l m i : ℕ) (h : i ≤ m) : mkFun k l m i = k := by
  unfold mkFun; simp [h]

/-- Value of `mkFun` at `m + 1`. -/
lemma mkFun_eq_succ_m (k l m : ℕ) : mkFun k l m (m + 1) = l := by
  unfold mkFun
  have h1 : ¬ (m + 1 ≤ m) := by omega
  simp [h1]

/-- Value of `mkFun` when input is `≥ m + 2`. -/
lemma mkFun_ge_m_add_two (k l m i : ℕ) (h : m + 2 ≤ i) : mkFun k l m i = i - 1 := by
  unfold mkFun
  have h1 : ¬ (i ≤ m) := by omega
  have h2 : i ≠ m + 1 := by omega
  simp [h1, h2]

/-- For valid parameters, `mkFun k l m` satisfies the functional equation. -/
lemma mkFun_funEq
    {n k l m : ℕ} (_hk : 1 ≤ k) (hkl : k < l) (hlm : l ≤ m) (_hmn : m ≤ n - 1) :
    ∀ i, 1 ≤ i → i ≤ n - 1 →
      mkFun k l m i = mkFun k l m (mkFun k l m (i + 1)) := by
  intro i _ _
  -- Three cases on `i + 1` vs `m`.
  by_cases hA : i + 1 ≤ m
  · -- Inner: mkFun (i+1) = k. Outer: mkFun k = k since k ≤ m.
    have hi : i ≤ m := by omega
    have hk_le_m : k ≤ m := by omega
    rw [mkFun_le_m _ _ _ _ hA, mkFun_le_m _ _ _ _ hk_le_m, mkFun_le_m _ _ _ _ hi]
  · by_cases hB : i + 1 = m + 1
    · -- Inner: mkFun (i+1) = l. Outer: mkFun l = k since l ≤ m. LHS: mkFun i = k since i ≤ m.
      have hi : i ≤ m := by omega
      rw [show i + 1 = m + 1 from hB, mkFun_eq_succ_m,
          mkFun_le_m _ _ _ _ hlm, mkFun_le_m _ _ _ _ hi]
    · -- Inner: mkFun (i+1) = i. Now i ≥ m + 1 and i ≠ m, so i ≥ m + 1.
      -- Subcase a: i = m + 1.
      -- Subcase b: i ≥ m + 2.
      have hge : i + 1 ≥ m + 2 := by omega
      have hinner : mkFun k l m (i + 1) = i := by
        rw [mkFun_ge_m_add_two _ _ _ _ hge]; omega
      rw [hinner]

/-- For valid parameters, `mkFun k l m` is non-constant on `{1, …, n}`
(taking value `k` at `1` and `l` at `m+1`, with `k < l`). -/
lemma mkFun_nonconstant
    {n k l m : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hlm : l ≤ m) (hmn : m ≤ n - 1)
    (hn : 1 ≤ n) :
    ¬ ∃ c, ∀ i, 1 ≤ i → i ≤ n → mkFun k l m i = c := by
  rintro ⟨c, hc⟩
  have h1 : mkFun k l m 1 = k := by
    unfold mkFun
    have : (1 : ℕ) ≤ m := by omega
    simp [this]
  have h2 : mkFun k l m (m + 1) = l := by
    unfold mkFun
    have h3 : ¬ (m + 1 ≤ m) := by omega
    simp [h3]
  have h1' := hc 1 (le_refl _) (by omega)
  have h2' := hc (m + 1) (by omega) (by omega)
  rw [h1] at h1'
  rw [h2] at h2'
  omega

/-- The construction direction: every admissible triple yields an element of
`Family n`. -/
lemma mkFun_mem_family
    {n k l m : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hlm : l ≤ m) (hmn : m ≤ n - 1)
    (hn : 1 ≤ n) :
    mkFun k l m ∈ Family n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mkFun_mem_range hk hkl hlm hmn hn
  · exact mkFun_mono hk hkl hlm hmn
  · exact mkFun_funEq hk hkl hlm hmn
  · exact mkFun_nonconstant hk hkl hlm hmn hn

/-- The answer. -/
determine answer (n : ℕ) : ℕ := n.choose 3

/-- Set of admissible triples `(k, l, m)` with `1 ≤ k < l ≤ m ≤ n - 1`,
viewed as a `Finset` of `ℕ × ℕ × ℕ`. -/
def TripleSet (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter
    fun p => 1 ≤ p.1 ∧ p.1 < p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.2 ≤ n - 1)

/-- IMC 1998 Problem 10.

We state the conclusion as: there is a `Finset` `S` whose underlying set is
`Family n` and whose cardinality is `(n choose 3)`.

TODO: A complete formal proof requires:

1. **Construction**: showing that for each admissible triple `(k, l, m)`, the
   function `mkFun k l m` lies in `Family n`, and that the assignment
   `(k, l, m) ↦ mkFun k l m` is injective on triples (when restricted to
   their values on `{1, …, n}`). This shows `(n choose 3) ≤ |𝓕|`.

2. **Uniqueness** (the heart of the problem): starting from `f ∈ Family n`,
   recover the triple `(k, l, m)` and prove that `f` agrees with
   `mkFun k l m` on `{1, …, n}`. The argument:

   * Use monotonicity and the functional equation `f(n-1) = f(f(n))` to show
     that `f(n) ≤ n - 1` (otherwise `f(n) = n` forces `f` constant equal
     to `n`).
   * Inductively show that for `i` close to `n`, `f(i) = i - 1`, until one
     reaches an index `m + 1` where the behaviour changes.
   * Show `f` is constant on `{1, …, m}` with value some `k` satisfying
     `1 ≤ k < f(m+1) = l ≤ m`.

3. **Cardinality**: counting the set of triples
   `{(k, l, m) ∈ ℕ³ : 1 ≤ k < l ≤ m ≤ n - 1}`. Substituting `m' = m + 1`
   yields a bijection with `{(k, l, m') : 1 ≤ k < l < m' ≤ n}`, which has
   cardinality `(n choose 3)` (e.g. via the powerset-of-cardinality-3
   count of `Finset.range n`).
-/
problem imc1998_p10 (n : ℕ) (_hn : 3 ≤ n) :
    ∃ S : Finset (ℕ → ℕ), (↑S : Set (ℕ → ℕ)) = Family n ∧
      S.card = answer n := by
  sorry

end Imc1998P10
