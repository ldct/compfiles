/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2004, Problem 5

Let `X` be a set of `Nat.choose (2*k - 4) (k - 2) + 1` real numbers, with `k ≥ 2`.
Prove that there exists a monotone sequence `x_1, …, x_k` in `X` such that
`|x_{i+1} - x_1| ≥ 2|x_i - x_1|` for all `i = 2, …, k-1`.

The proof uses the more general lemma (over pairs `(k, l)`):
if `|X| ≥ C(k+l-4, k-2) + 1` then either there is an increasing sequence of
length `k` or a decreasing sequence of length `l` satisfying the doubling
property. Pascal's identity `C(k+l-4, k-2) = C(k+l-5, k-2) + C(k+l-5, k-3)`
allows the inductive split using the midpoint of the minimum and maximum
of `X`.
-/

namespace Imc2004P5

open scoped BigOperators

snip begin

/-- The doubling property for a sequence indexed `0, …, n-1` (n = length). -/
def DoublingProp {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i : ℕ, ∀ (h1 : 1 ≤ i) (h2 : i + 1 < n),
    |x ⟨i + 1, h2⟩ - x ⟨0, by omega⟩| ≥ 2 * |x ⟨i, by omega⟩ - x ⟨0, by omega⟩|

/-- Increasing sequence with the doubling property in a finset `X`. -/
def HasInc (X : Finset ℝ) (k : ℕ) : Prop :=
  ∃ x : Fin k → ℝ, (∀ i, x i ∈ X) ∧ StrictMono x ∧ DoublingProp x

/-- Decreasing sequence with the doubling property in a finset `X`. -/
def HasDec (X : Finset ℝ) (l : ℕ) : Prop :=
  ∃ x : Fin l → ℝ, (∀ i, x i ∈ X) ∧ StrictAnti x ∧ DoublingProp x

/-- Monotonicity in superset. -/
lemma hasInc_mono {X Y : Finset ℝ} (hXY : X ⊆ Y) {k : ℕ} (h : HasInc X k) : HasInc Y k := by
  obtain ⟨x, hxmem, hmono, hdbl⟩ := h
  exact ⟨x, fun i => hXY (hxmem i), hmono, hdbl⟩

lemma hasDec_mono {X Y : Finset ℝ} (hXY : X ⊆ Y) {l : ℕ} (h : HasDec X l) : HasDec Y l := by
  obtain ⟨x, hxmem, hmono, hdbl⟩ := h
  exact ⟨x, fun i => hXY (hxmem i), hmono, hdbl⟩

/-- For `k = 2`: any two distinct elements of `X` give a length-2 increasing
sequence (doubling vacuous). -/
lemma hasInc_two_of_two_le_card {X : Finset ℝ} (hX : 2 ≤ X.card) : HasInc X 2 := by
  have hX' : 1 < X.card := hX
  rw [Finset.one_lt_card] at hX'
  obtain ⟨a, ha, b, hb, hab⟩ := hX'
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨![a, b], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [ha, hb]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact hlt
    · intro i _ h2; omega
  · refine ⟨![b, a], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [ha, hb]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact hlt
    · intro i _ h2; omega

lemma hasDec_two_of_two_le_card {X : Finset ℝ} (hX : 2 ≤ X.card) : HasDec X 2 := by
  have hX' : 1 < X.card := hX
  rw [Finset.one_lt_card] at hX'
  obtain ⟨a, ha, b, hb, hab⟩ := hX'
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨![b, a], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [ha, hb]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact hlt
    · intro i _ h2; omega
  · refine ⟨![a, b], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [ha, hb]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact hlt
    · intro i _ h2; omega

/-- Pascal's identity for our setup. -/
private lemma pascal_klm4 (k l : ℕ) (hk : 3 ≤ k) (hl : 3 ≤ l) :
    Nat.choose (k + l - 4) (k - 2) =
      Nat.choose (k + l - 5) (k - 2) + Nat.choose (k + l - 5) (k - 3) := by
  set a := k - 3 with ha
  set b := k + l - 5 with hb
  have hb_eq : k + l - 4 = b + 1 := by omega
  have ha_eq : k - 2 = a + 1 := by omega
  rw [hb_eq, ha_eq, Nat.choose_succ_succ']
  ring

/-- Splitting argument: if `X` is split via a predicate, one side has the
appropriate share of the elements.  If both sides are short by at least one,
their sum cannot reach `a + b - 1`. -/
lemma split_card (X : Finset ℝ) (p : ℝ → Prop) [DecidablePred p]
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b - 1 ≤ X.card) :
    a ≤ (X.filter p).card ∨ b ≤ (X.filter (fun x => ¬ p x)).card := by
  by_contra hboth
  rw [not_or] at hboth
  obtain ⟨h1, h2⟩ := hboth
  push Not at h1 h2
  have hsplit : (X.filter p).card + (X.filter (fun x => ¬ p x)).card = X.card :=
    Finset.card_filter_add_card_filter_not _
  omega

/-- Append one element to a `Fin k → ℝ` sequence to get `Fin (k+1) → ℝ`. -/
private def append (k : ℕ) (xs : Fin k → ℝ) (a : ℝ) : Fin (k + 1) → ℝ :=
  fun i => if h : i.val < k then xs ⟨i.val, h⟩ else a

private lemma append_lt {k : ℕ} (xs : Fin k → ℝ) (a : ℝ)
    {n : ℕ} (hn : n < k + 1) (hk : n < k) :
    append k xs a ⟨n, hn⟩ = xs ⟨n, hk⟩ := by
  unfold append; simp [hk]

private lemma append_at_k {k : ℕ} (xs : Fin k → ℝ) (a : ℝ) :
    append k xs a ⟨k, Nat.lt_succ_self k⟩ = a := by
  unfold append; simp

/-- Extension by max: given an increasing sequence of length `k+1` in the lower
half (≤ midpoint), extending by `M` gives a length `k+2` increasing doubling
sequence. -/
lemma extend_inc_with_max
    {k : ℕ} (xs : Fin (k + 1) → ℝ)
    (hmono : StrictMono xs)
    (hdbl : DoublingProp xs)
    (m M : ℝ)
    (hxs0_ge : m ≤ xs ⟨0, Nat.succ_pos _⟩)
    (hxs_le_mid : ∀ i, xs i ≤ (m + M) / 2)
    (hmM : m < M) :
    StrictMono (append (k + 1) xs M) ∧ DoublingProp (append (k + 1) xs M) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val < k + 1
    · by_cases hj : j.val < k + 1
      · rw [append_lt _ _ i.isLt hi, append_lt _ _ j.isLt hj]
        apply hmono
        simp [Fin.lt_def, Fin.lt_def.mp hij]
      · -- j.val = k + 1
        have hj_eq : j.val = k + 1 := by have := j.isLt; omega
        have : j = ⟨k + 1, Nat.lt_succ_self _⟩ := Fin.ext hj_eq
        rw [this, append_at_k, append_lt _ _ i.isLt hi]
        have h1 : xs ⟨i.val, hi⟩ ≤ (m + M) / 2 := hxs_le_mid _
        have h2 : (m + M) / 2 < M := by linarith
        linarith
    · -- i.val = k + 1, but j > i, contradiction
      have hi_eq : i.val = k + 1 := by have := i.isLt; omega
      have : j.val ≤ k + 1 := by have := j.isLt; omega
      have hjlt := Fin.lt_def.mp hij
      omega
  · intro i h1 h2
    -- New length is (k+1)+1 = k+2.
    have h0_eq : append (k + 1) xs M ⟨0, by omega⟩ = xs ⟨0, by omega⟩ :=
      append_lt _ _ (by omega) (by omega)
    by_cases hilast : i + 1 = k + 1
    · -- i + 1 = k + 1, so the index k+1 in the appended sequence ↦ M, and i = k.
      have hi_eq : i = k := by omega
      have hkp1_idx : (⟨i + 1, h2⟩ : Fin (k + 2)) = ⟨k + 1, Nat.lt_succ_self _⟩ := by
        apply Fin.ext; simpa using hi_eq
      rw [hkp1_idx, append_at_k]
      have hk_lt : k < k + 1 := Nat.lt_succ_self _
      have hi_idx : (⟨i, by omega⟩ : Fin (k + 2)) = ⟨k, by omega⟩ := Fin.ext hi_eq
      rw [hi_idx]
      have hk_eq : append (k + 1) xs M ⟨k, by omega⟩ = xs ⟨k, hk_lt⟩ :=
        append_lt _ _ _ hk_lt
      rw [hk_eq, h0_eq]
      have hxk_le : xs ⟨k, hk_lt⟩ ≤ (m + M) / 2 := hxs_le_mid _
      have hx0_ge : m ≤ xs ⟨0, by omega⟩ := hxs0_ge
      have hk_pos : 0 < k := by omega
      have hxk_ge_x0 : xs ⟨0, by omega⟩ ≤ xs ⟨k, hk_lt⟩ := by
        apply le_of_lt
        apply hmono
        show (0 : ℕ) < k
        exact hk_pos
      have hM_ge_x0 : xs ⟨0, by omega⟩ ≤ M := by
        have : xs ⟨0, by omega⟩ ≤ (m + M) / 2 := hxs_le_mid _
        linarith
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ xs ⟨k, hk_lt⟩ - xs ⟨0, by omega⟩),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ M - xs ⟨0, by omega⟩)]
      have h_calc : 2 * xs ⟨k, hk_lt⟩ ≤ m + M := by linarith
      linarith
    · -- i + 1 < k + 1, both indices stay in the original.
      have hi1_lt : i + 1 < k + 1 := by omega
      have hi_lt : i < k + 1 := by omega
      have hi1_eq : append (k + 1) xs M ⟨i + 1, h2⟩ = xs ⟨i + 1, hi1_lt⟩ :=
        append_lt _ _ _ hi1_lt
      have hi_eq : append (k + 1) xs M ⟨i, by omega⟩ = xs ⟨i, hi_lt⟩ :=
        append_lt _ _ _ hi_lt
      rw [hi1_eq, hi_eq, h0_eq]
      exact hdbl i h1 hi1_lt

/-- Extension by min: given a decreasing sequence of length `l+1` in the upper
half (> midpoint), extending by `m` gives a length `l+2` decreasing doubling
sequence. -/
lemma extend_dec_with_min
    {l : ℕ} (xs : Fin (l + 1) → ℝ)
    (hmono : StrictAnti xs)
    (hdbl : DoublingProp xs)
    (m M : ℝ)
    (hxs0_le : xs ⟨0, Nat.succ_pos _⟩ ≤ M)
    (hxs_gt_mid : ∀ i, (m + M) / 2 < xs i)
    (hmM : m < M) :
    StrictAnti (append (l + 1) xs m) ∧ DoublingProp (append (l + 1) xs m) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_cases hi : i.val < l + 1
    · by_cases hj : j.val < l + 1
      · rw [append_lt _ _ i.isLt hi, append_lt _ _ j.isLt hj]
        apply hmono
        simp [Fin.lt_def, Fin.lt_def.mp hij]
      · have hj_eq : j.val = l + 1 := by have := j.isLt; omega
        have : j = ⟨l + 1, Nat.lt_succ_self _⟩ := Fin.ext hj_eq
        rw [this, append_at_k, append_lt _ _ i.isLt hi]
        have h1 : (m + M) / 2 < xs ⟨i.val, hi⟩ := hxs_gt_mid _
        have h2 : m < (m + M) / 2 := by linarith
        linarith
    · have hi_eq : i.val = l + 1 := by have := i.isLt; omega
      have : j.val ≤ l + 1 := by have := j.isLt; omega
      have hjlt := Fin.lt_def.mp hij
      omega
  · intro i h1 h2
    have h0_eq : append (l + 1) xs m ⟨0, by omega⟩ = xs ⟨0, by omega⟩ :=
      append_lt _ _ (by omega) (by omega)
    by_cases hilast : i + 1 = l + 1
    · have hi_eq : i = l := by omega
      have hkp1_idx : (⟨i + 1, h2⟩ : Fin (l + 2)) = ⟨l + 1, Nat.lt_succ_self _⟩ := by
        apply Fin.ext; simpa using hi_eq
      rw [hkp1_idx, append_at_k]
      have hl_lt : l < l + 1 := Nat.lt_succ_self _
      have hi_idx : (⟨i, by omega⟩ : Fin (l + 2)) = ⟨l, by omega⟩ := Fin.ext hi_eq
      rw [hi_idx]
      have hl_eq : append (l + 1) xs m ⟨l, by omega⟩ = xs ⟨l, hl_lt⟩ :=
        append_lt _ _ _ hl_lt
      rw [hl_eq, h0_eq]
      have hxl_gt : (m + M) / 2 < xs ⟨l, hl_lt⟩ := hxs_gt_mid _
      have hx0_le : xs ⟨0, by omega⟩ ≤ M := hxs0_le
      have hl_pos : 0 < l := by omega
      have hxl_le_x0 : xs ⟨l, hl_lt⟩ ≤ xs ⟨0, by omega⟩ := by
        apply le_of_lt
        apply hmono
        show (0 : ℕ) < l
        exact hl_pos
      have hm_le_x0 : m ≤ xs ⟨0, by omega⟩ := by
        have : (m + M) / 2 < xs ⟨0, by omega⟩ := hxs_gt_mid _
        linarith
      rw [abs_of_nonpos (by linarith : xs ⟨l, hl_lt⟩ - xs ⟨0, by omega⟩ ≤ 0),
          abs_of_nonpos (by linarith : m - xs ⟨0, by omega⟩ ≤ 0)]
      -- Want: -(m - xs 0) ≥ 2 * -(xs l - xs 0)
      -- i.e., xs 0 - m ≥ 2 (xs 0 - xs l)
      -- i.e., 2 xs l ≥ xs 0 + m
      -- xs l > (m + M)/2 ≥ (m + xs 0)/2 (since xs 0 ≤ M), so 2 xs l > m + xs 0.
      have h_calc : 2 * xs ⟨l, hl_lt⟩ > m + M := by linarith
      have h_calc2 : 2 * xs ⟨l, hl_lt⟩ ≥ m + xs ⟨0, by omega⟩ := by linarith
      linarith
    · have hi1_lt : i + 1 < l + 1 := by omega
      have hi_lt : i < l + 1 := by omega
      have hi1_eq : append (l + 1) xs m ⟨i + 1, h2⟩ = xs ⟨i + 1, hi1_lt⟩ :=
        append_lt _ _ _ hi1_lt
      have hi_eq : append (l + 1) xs m ⟨i, by omega⟩ = xs ⟨i, hi_lt⟩ :=
        append_lt _ _ _ hi_lt
      rw [hi1_eq, hi_eq, h0_eq]
      exact hdbl i h1 hi1_lt

/-- For a finset of reals with at least one element, the min and max exist. -/
private lemma exists_min_max {X : Finset ℝ} (hX : X.Nonempty) :
    ∃ m M : ℝ, m ∈ X ∧ M ∈ X ∧ (∀ x ∈ X, m ≤ x) ∧ (∀ x ∈ X, x ≤ M) :=
  ⟨X.min' hX, X.max' hX,
    X.min'_mem hX, X.max'_mem hX,
    fun x hx => X.min'_le x hx, fun x hx => X.le_max' x hx⟩

/-- Main lemma. Strong induction on `k + l`. -/
lemma main_lemma_aux : ∀ N : ℕ, ∀ k l : ℕ, 2 ≤ k → 2 ≤ l → k + l ≤ N →
    ∀ X : Finset ℝ, Nat.choose (k + l - 4) (k - 2) + 1 ≤ X.card →
      HasInc X k ∨ HasDec X l := by
  intro N
  induction N with
  | zero =>
    intro k l hk hl hN
    omega
  | succ N ih =>
    intro k l hk hl hN X hX
    -- Base case: k = 2 → directly inc-of-2.
    by_cases hk2 : k = 2
    · subst hk2
      have hXcard : 2 ≤ X.card := by
        have hch : Nat.choose (2 + l - 4) (2 - 2) = 1 := by
          have : 2 - 2 = 0 := rfl
          rw [this, Nat.choose_zero_right]
        omega
      exact Or.inl (hasInc_two_of_two_le_card hXcard)
    -- Base case: l = 2 → directly dec-of-2.
    by_cases hl2 : l = 2
    · subst hl2
      have hXcard : 2 ≤ X.card := by
        have hch : Nat.choose (k + 2 - 4) (k - 2) = 1 := by
          have h1 : k + 2 - 4 = k - 2 := by omega
          rw [h1, Nat.choose_self]
        omega
      exact Or.inr (hasDec_two_of_two_le_card hXcard)
    -- Inductive step: k ≥ 3 and l ≥ 3.
    have hk3 : 3 ≤ k := by omega
    have hl3 : 3 ≤ l := by omega
    -- Let m, M be min/max of X.
    have hX_ne : X.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h] at hX; simp at hX
    obtain ⟨m, M, hm_mem, hM_mem, hm_min, hM_max⟩ := exists_min_max hX_ne
    -- Need m < M for the splitting to work.
    by_cases hmM : m = M
    · -- All elements equal m = M. So X = {m}, but |X| ≥ C(k+l-4,k-2)+1 ≥ 2. Contradiction.
      exfalso
      have hX_sub : X ⊆ {m} := by
        intro x hx
        have h1 : m ≤ x := hm_min x hx
        have h2 : x ≤ M := hM_max x hx
        have : x = m := by rw [hmM]; linarith
        simp [this]
      have hcard : X.card ≤ 1 := by
        calc X.card ≤ ({m} : Finset ℝ).card := Finset.card_le_card hX_sub
          _ = 1 := Finset.card_singleton _
      have hpos : 1 ≤ Nat.choose (k + l - 4) (k - 2) := by
        apply Nat.choose_pos; omega
      omega
    have hmM' : m < M := lt_of_le_of_ne (hm_min M hM_mem) hmM
    -- Split X into Xm and XM.
    set p : ℝ → Prop := fun x => x ≤ (m + M) / 2
    set Xm := X.filter p with hXm_def
    set XM := X.filter (fun x => ¬ p x) with hXM_def
    have hXm_sub : Xm ⊆ X := Finset.filter_subset _ _
    have hXM_sub : XM ⊆ X := Finset.filter_subset _ _
    -- By Pascal: |X| ≥ C(k+l-5, k-2) + C(k+l-5, k-3) + 1.
    have hPascal := pascal_klm4 k l hk3 hl3
    have hX' : Nat.choose (k + l - 5) (k - 2) + Nat.choose (k + l - 5) (k - 3) + 1 ≤ X.card := by
      rw [← hPascal]; exact hX
    -- Split: either |Xm| ≥ C(k+l-5, k-3) + 1 or |XM| ≥ C(k+l-5, k-2) + 1.
    -- (Pascal: C(k+l-4, k-2) = C(k+l-5, k-2) + C(k+l-5, k-3); if neither side
    --  meets its bound, sum is at most C(k+l-4, k-2), contradicting |X| > that.)
    rcases split_card X p (Nat.choose (k + l - 5) (k - 3) + 1)
        (Nat.choose (k + l - 5) (k - 2) + 1)
        (by omega) (by omega) (by omega) with hXm_big | hXM_big
    · -- Case 1: |Xm| ≥ C(k+l-5, k-3) + 1 = C((k-1) + l - 4, (k-1) - 2) + 1.
      -- Apply IH to Xm with parameters (k-1, l).
      have hk1 : 2 ≤ k - 1 := by omega
      have hkl_eq : (k - 1) + l - 4 = k + l - 5 := by omega
      have hk12 : (k - 1) - 2 = k - 3 := by omega
      have hXm_card : Nat.choose ((k - 1) + l - 4) ((k - 1) - 2) + 1 ≤ Xm.card := by
        rw [hkl_eq, hk12]; exact hXm_big
      have hN' : (k - 1) + l ≤ N := by omega
      have h_ih := ih (k - 1) l hk1 hl hN' Xm hXm_card
      rcases h_ih with ⟨xs, hxs_mem, hxs_mono, hxs_dbl⟩ | hdec
      · -- Inc of length k-1 in Xm. Extend with M.
        -- All elements of xs ≤ (m+M)/2 (since they live in Xm).
        -- xs ⟨0, _⟩ ≥ m (since m is min of X).
        -- xs ⟨k-2, _⟩ ≤ (m+M)/2.
        have hk_eq : k = (k - 2) + 2 := by omega
        -- We need to convert k-1 to (k-2)+1.
        have hk1_eq : k - 1 = (k - 2) + 1 := by omega
        -- Cast xs : Fin (k-1) → ℝ to xs : Fin ((k-2) + 1) → ℝ.
        let xs' : Fin ((k - 2) + 1) → ℝ := fun i => xs ⟨i.val, by rw [hk1_eq]; exact i.isLt⟩
        have hxs'_mono : StrictMono xs' := by
          intro i j hij
          show xs ⟨i.val, _⟩ < xs ⟨j.val, _⟩
          apply hxs_mono
          show i.val < j.val
          exact hij
        have hxs'_dbl : DoublingProp xs' := by
          intro i h1 h2
          have h2' : i + 1 < k - 1 := by rw [hk1_eq]; exact h2
          exact hxs_dbl i h1 h2'
        have hxs'_mem : ∀ i, xs' i ∈ X := fun i => hXm_sub (hxs_mem _)
        have hxs'_lemid : ∀ i, xs' i ≤ (m + M) / 2 := by
          intro i
          have := hxs_mem ⟨i.val, by rw [hk1_eq]; exact i.isLt⟩
          rw [hXm_def, Finset.mem_filter] at this
          exact this.2
        have hxs'0_ge : m ≤ xs' ⟨0, Nat.succ_pos _⟩ := hm_min _ (hxs'_mem _)
        obtain ⟨hext_mono, hext_dbl⟩ :=
          extend_inc_with_max xs' hxs'_mono hxs'_dbl m M hxs'0_ge hxs'_lemid hmM'
        -- The extended sequence has length (k-2) + 2 = k.
        have hlen_eq : (k - 2) + 1 + 1 = k := by omega
        let xs'' : Fin k → ℝ := fun i =>
          append ((k - 2) + 1) xs' M ⟨i.val, by have := i.isLt; omega⟩
        refine Or.inl ⟨xs'', ?_, ?_, ?_⟩
        · intro i
          have hi : i.val < (k - 2) + 1 + 1 := by rw [hlen_eq]; exact i.isLt
          by_cases hi' : i.val < (k - 2) + 1
          · show append ((k - 2) + 1) xs' M ⟨i.val, hi⟩ ∈ X
            rw [append_lt _ _ hi hi']
            exact hxs'_mem _
          · have : i.val = (k - 2) + 1 := by omega
            show append ((k - 2) + 1) xs' M ⟨i.val, hi⟩ ∈ X
            have heq : (⟨i.val, hi⟩ : Fin ((k - 2) + 1 + 1))
                = ⟨(k - 2) + 1, Nat.lt_succ_self _⟩ := Fin.ext this
            rw [heq, append_at_k]
            exact hM_mem
        · intro i j hij
          show append ((k - 2) + 1) xs' M ⟨i.val, _⟩ < append ((k - 2) + 1) xs' M ⟨j.val, _⟩
          apply hext_mono
          show i.val < j.val
          exact hij
        · intro i h1 h2
          have h2' : i + 1 < (k - 2) + 1 + 1 := by rw [hlen_eq]; exact h2
          exact hext_dbl i h1 h2'
      · -- Dec of length l in Xm. It's also in X.
        exact Or.inr (hasDec_mono hXm_sub hdec)
    · -- Case 2: |XM| ≥ C(k+l-5, k-2) + 1 = C(k + (l-1) - 4, k - 2) + 1.
      -- Apply IH to XM with parameters (k, l-1).
      have hl1 : 2 ≤ l - 1 := by omega
      have hkl_eq : k + (l - 1) - 4 = k + l - 5 := by omega
      have hXM_card : Nat.choose (k + (l - 1) - 4) (k - 2) + 1 ≤ XM.card := by
        rw [hkl_eq]; exact hXM_big
      have hN' : k + (l - 1) ≤ N := by omega
      have h_ih := ih k (l - 1) hk hl1 hN' XM hXM_card
      rcases h_ih with hinc | ⟨xs, hxs_mem, hxs_anti, hxs_dbl⟩
      · -- Inc of length k in XM. It's also in X.
        exact Or.inl (hasInc_mono hXM_sub hinc)
      · -- Dec of length l-1 in XM. Extend with m.
        have hl_eq : l = (l - 2) + 2 := by omega
        have hl1_eq : l - 1 = (l - 2) + 1 := by omega
        let xs' : Fin ((l - 2) + 1) → ℝ := fun i => xs ⟨i.val, by rw [hl1_eq]; exact i.isLt⟩
        have hxs'_anti : StrictAnti xs' := by
          intro i j hij
          show xs ⟨i.val, _⟩ > xs ⟨j.val, _⟩
          apply hxs_anti
          show i.val < j.val
          exact hij
        have hxs'_dbl : DoublingProp xs' := by
          intro i h1 h2
          have h2' : i + 1 < l - 1 := by rw [hl1_eq]; exact h2
          exact hxs_dbl i h1 h2'
        have hxs'_mem : ∀ i, xs' i ∈ X := fun i => hXM_sub (hxs_mem _)
        have hxs'_gtmid : ∀ i, (m + M) / 2 < xs' i := by
          intro i
          have hh := hxs_mem ⟨i.val, by rw [hl1_eq]; exact i.isLt⟩
          rw [hXM_def, Finset.mem_filter] at hh
          have hnp : ¬ (xs' i ≤ (m + M) / 2) := hh.2
          exact lt_of_not_ge hnp
        have hxs'0_le : xs' ⟨0, Nat.succ_pos _⟩ ≤ M := hM_max _ (hxs'_mem _)
        obtain ⟨hext_anti, hext_dbl⟩ :=
          extend_dec_with_min xs' hxs'_anti hxs'_dbl m M hxs'0_le hxs'_gtmid hmM'
        have hlen_eq : (l - 2) + 1 + 1 = l := by omega
        let xs'' : Fin l → ℝ := fun i =>
          append ((l - 2) + 1) xs' m ⟨i.val, by have := i.isLt; omega⟩
        refine Or.inr ⟨xs'', ?_, ?_, ?_⟩
        · intro i
          have hi : i.val < (l - 2) + 1 + 1 := by rw [hlen_eq]; exact i.isLt
          by_cases hi' : i.val < (l - 2) + 1
          · show append ((l - 2) + 1) xs' m ⟨i.val, hi⟩ ∈ X
            rw [append_lt _ _ hi hi']
            exact hxs'_mem _
          · have : i.val = (l - 2) + 1 := by omega
            show append ((l - 2) + 1) xs' m ⟨i.val, hi⟩ ∈ X
            have heq : (⟨i.val, hi⟩ : Fin ((l - 2) + 1 + 1))
                = ⟨(l - 2) + 1, Nat.lt_succ_self _⟩ := Fin.ext this
            rw [heq, append_at_k]
            exact hm_mem
        · intro i j hij
          show append ((l - 2) + 1) xs' m ⟨i.val, _⟩ > append ((l - 2) + 1) xs' m ⟨j.val, _⟩
          apply hext_anti
          show i.val < j.val
          exact hij
        · intro i h1 h2
          have h2' : i + 1 < (l - 2) + 1 + 1 := by rw [hlen_eq]; exact h2
          exact hext_dbl i h1 h2'

snip end

/-- The main problem. -/
problem imc2004_p5
    (k : ℕ) (hk : 2 ≤ k)
    (X : Finset ℝ)
    (hX : Nat.choose (2 * k - 4) (k - 2) + 1 ≤ X.card) :
    ∃ x : Fin k → ℝ, (∀ i, x i ∈ X) ∧
      (StrictMono x ∨ StrictAnti x) ∧
      (∀ i : ℕ, ∀ (h1 : 1 ≤ i) (h2 : i + 1 < k),
        |x ⟨i + 1, h2⟩ - x ⟨0, by omega⟩| ≥
          2 * |x ⟨i, by omega⟩ - x ⟨0, by omega⟩|) := by
  have h2k4 : 2 * k - 4 = k + k - 4 := by ring_nf
  rw [h2k4] at hX
  have h := main_lemma_aux (k + k) k k hk hk le_rfl X hX
  rcases h with ⟨x, hxmem, hmono, hdbl⟩ | ⟨x, hxmem, hanti, hdbl⟩
  · exact ⟨x, hxmem, Or.inl hmono, hdbl⟩
  · exact ⟨x, hxmem, Or.inr hanti, hdbl⟩

end Imc2004P5
