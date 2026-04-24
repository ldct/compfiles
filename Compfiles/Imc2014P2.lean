/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2014, Problem 2

Consider the sequence
`(a_n)_{n=1}^∞ = (1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3, 4, 5, 1, ...)`.
Find all pairs `(α, β)` of positive real numbers such that
`lim_{n → ∞} (∑_{k=1}^n a_k) / n^α = β`.

Answer: `(α, β) = (3/2, √2 / 3)`.
-/

namespace Imc2014P2

open Filter Topology

/-- The "block index" of `n`: the smallest `m` with `n ≤ m*(m+1)/2`. The value
`a n` lies in block `m`, where the `m`-th block (`m ≥ 1`) consists of the values
`1, 2, …, m` placed at indices `m(m-1)/2 + 1, …, m(m+1)/2`. -/
def blockIdx (n : ℕ) : ℕ := Nat.find (p := fun m => n ≤ m * (m + 1) / 2)
  ⟨n, by
    rcases n.eq_zero_or_pos with h | h
    · simp [h]
    · have h2 : 2 * n ≤ n * (n + 1) := by nlinarith
      omega⟩

/-- The sequence `a_n`, defined for `n ≥ 1`. We extend `a 0 = 0`. -/
def a (n : ℕ) : ℕ := n - (blockIdx n) * (blockIdx n - 1) / 2

/-- Partial sum `S n = ∑_{k=1}^n a k`. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, a (k + 1)

/-- The set of valid `(α, β)` pairs. -/
noncomputable determine answer : Set (ℝ × ℝ) := {(3 / 2, Real.sqrt 2 / 3)}

snip begin

/-- The triangular number `T m = m*(m+1)/2`. -/
def T (m : ℕ) : ℕ := m * (m + 1) / 2

lemma T_zero : T 0 = 0 := rfl
lemma T_one : T 1 = 1 := rfl

lemma two_T (m : ℕ) : 2 * T m = m * (m + 1) := by
  unfold T
  have heven : 2 ∣ m * (m + 1) := by
    rcases Nat.even_or_odd m with hm | hm
    · exact hm.two_dvd.mul_right _
    · have : Even (m + 1) := Odd.add_one hm
      exact this.two_dvd.mul_left _
  omega

lemma T_succ (m : ℕ) : T (m + 1) = T m + (m + 1) := by
  have h1 : 2 * T (m + 1) = (m + 1) * (m + 2) := two_T (m + 1)
  have h2 : 2 * T m = m * (m + 1) := two_T m
  have h3 : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  omega

lemma T_strictMono : StrictMono T := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => rw [T_succ]; omega
  | succ n _ ih => exact ih.trans (by rw [T_succ]; omega)

/-- `blockIdx n` is the smallest `m` with `n ≤ T m`. -/
lemma blockIdx_le (n : ℕ) : n ≤ T (blockIdx n) := by
  unfold blockIdx T
  exact Nat.find_spec (p := fun m => n ≤ m * (m + 1) / 2) _

lemma blockIdx_min (n m : ℕ) (h : n ≤ T m) : blockIdx n ≤ m := by
  unfold blockIdx
  apply Nat.find_le
  exact h

lemma blockIdx_zero : blockIdx 0 = 0 := by
  apply le_antisymm
  · exact blockIdx_min 0 0 (by simp [T_zero])
  · exact Nat.zero_le _

lemma blockIdx_pos (n : ℕ) (hn : 0 < n) : 0 < blockIdx n := by
  by_contra h
  push_neg at h
  have hb : blockIdx n = 0 := by omega
  have hle := blockIdx_le n
  rw [hb] at hle
  simp [T_zero] at hle
  omega

/-- The "not" part of the spec: anything less than blockIdx n doesn't satisfy. -/
lemma blockIdx_not_lt (n m : ℕ) (h : m < blockIdx n) : ¬ n ≤ T m := by
  unfold T
  unfold blockIdx at h
  exact Nat.find_min (p := fun m => n ≤ m * (m + 1) / 2) _ h

/-- For `1 ≤ n`, we have `T (blockIdx n - 1) < n`. -/
lemma T_pred_blockIdx_lt (n : ℕ) (hn : 0 < n) : T (blockIdx n - 1) < n := by
  have hpos := blockIdx_pos n hn
  have hmin := blockIdx_not_lt n (blockIdx n - 1) (by omega)
  push_neg at hmin
  exact hmin

lemma blockIdx_eq (m j : ℕ) (hm : 0 < m) (hj1 : 1 ≤ j) (hj2 : j ≤ m) :
    blockIdx (T (m - 1) + j) = m := by
  have hpos : 0 < T (m - 1) + j := by omega
  have hsucc : T m = T (m - 1) + m := by
    have := T_succ (m - 1)
    rw [Nat.sub_add_cancel hm] at this
    omega
  -- Upper bound: blockIdx (T(m-1)+j) ≤ m, since T(m-1)+j ≤ T m.
  have hle : blockIdx (T (m - 1) + j) ≤ m := blockIdx_min _ _ (by omega)
  -- Lower bound: blockIdx (T(m-1)+j) ≥ m, since T(m-1)+j > T(m-1).
  have hge : m ≤ blockIdx (T (m - 1) + j) := by
    by_contra hlt
    push_neg at hlt
    -- so blockIdx(...) ≤ m-1, so T(m-1)+j ≤ T(m-1).
    have : blockIdx (T (m - 1) + j) ≤ m - 1 := by omega
    have hbi := blockIdx_le (T (m - 1) + j)
    have : T (blockIdx (T (m - 1) + j)) ≤ T (m - 1) := T_strictMono.monotone this
    omega
  omega

/-- `a (T (m-1) + j) = j` for `1 ≤ j ≤ m`. -/
lemma a_eq (m j : ℕ) (hm : 0 < m) (hj1 : 1 ≤ j) (hj2 : j ≤ m) :
    a (T (m - 1) + j) = j := by
  unfold a
  rw [blockIdx_eq m j hm hj1 hj2]
  -- a = (T(m-1) + j) - m(m-1)/2 = (T(m-1) + j) - T(m-1) = j
  -- need: m * (m - 1) / 2 = T (m - 1)
  have hT : T (m - 1) = m * (m - 1) / 2 := by
    unfold T
    have : (m - 1) * (m - 1 + 1) = (m - 1) * m := by
      rw [Nat.sub_add_cancel hm]
    rw [this]
    ring_nf
  rw [← hT]
  omega

/-- Sum of `a` over the `m`-th block: `∑_{j=0}^{m-1} a (T(m-1)+(j+1)) = T m`. -/
lemma sum_block (m : ℕ) (hm : 0 < m) :
    ∑ j ∈ Finset.range m, a (T (m - 1) + (j + 1)) = T m := by
  have heach : ∀ j ∈ Finset.range m, a (T (m - 1) + (j + 1)) = j + 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact a_eq m (j + 1) hm (by omega) (by omega)
  rw [Finset.sum_congr rfl heach]
  -- ∑ j ∈ range m, (j + 1) = m(m+1)/2 = T m
  have h1 : ∑ j ∈ Finset.range m, (j + 1) = T m := by
    have hsum : (∑ j ∈ Finset.range m, (j + 1)) = (∑ j ∈ Finset.range m, j) + m := by
      rw [Finset.sum_add_distrib]; simp
    rw [hsum, Finset.sum_range_id]
    -- Goal: m * (m - 1) / 2 + m = T m
    have h2 := two_T m
    -- 2 * T m = m * (m + 1)
    -- 2 * (m * (m - 1) / 2 + m) = m * (m - 1) + 2*m (when m * (m-1) is even, but not always)
    -- Actually m*(m-1) is always even.
    have heven : 2 ∣ m * (m - 1) := by
      rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        rcases Nat.even_or_odd m with hm | hm
        · exact hm.two_dvd.mul_left _
        · have := Odd.add_one hm
          exact this.two_dvd.mul_right _
    have h3 : m * (m + 1) = m * (m - 1) + 2 * m := by
      rcases m with _ | m
      · simp
      · simp; ring
    omega
  exact h1

/-- `S` is monotone. -/
lemma S_mono : Monotone S := fun m n hmn => by
  unfold S
  exact Finset.sum_le_sum_of_subset (by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega)

/-- `S (T m) = m(m+1)(m+2)/6`, equivalently `6 S(T m) = m(m+1)(m+2)`. -/
lemma six_S_T (m : ℕ) : 6 * S (T m) = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp [S, T_zero]
  | succ m ih =>
    -- S (T (m+1)) = S (T m) + (T(m+1) - T m terms summed)
    -- T(m+1) = T m + (m+1)
    have hsucc : T (m + 1) = T m + (m + 1) := T_succ m
    have hSeq : S (T (m + 1)) = S (T m) + ∑ j ∈ Finset.range (m + 1), a (T m + (j + 1)) := by
      unfold S
      rw [hsucc, Finset.sum_range_add]
      simp only [add_assoc]
    have hblock := sum_block (m + 1) (by omega)
    -- (m + 1) - 1 = m
    simp only [Nat.add_sub_cancel] at hblock
    rw [hblock] at hSeq
    rw [hSeq]
    have hTm1 : 2 * T (m + 1) = (m + 1) * (m + 2) := two_T (m + 1)
    nlinarith [ih, hTm1]

/-- For `1 ≤ n`, with `m = blockIdx n`, we have `S (T (m-1)) ≤ S n ≤ S (T m)`. -/
lemma S_sandwich (n : ℕ) (hn : 0 < n) :
    S (T (blockIdx n - 1)) ≤ S n ∧ S n ≤ S (T (blockIdx n)) := by
  refine ⟨S_mono ?_, S_mono ?_⟩
  · have := T_pred_blockIdx_lt n hn
    omega
  · exact blockIdx_le n

/-- `T m → ∞`. -/
lemma T_atTop : Tendsto T atTop atTop := by
  apply Filter.tendsto_atTop_mono (f := fun m => m)
  · intro m
    induction m with
    | zero => simp [T_zero]
    | succ m ih => rw [T_succ]; omega
  · exact Filter.tendsto_id

/-- `blockIdx n → ∞` as `n → ∞`. -/
lemma blockIdx_atTop : Tendsto blockIdx atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨T M + 1, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 := blockIdx_le n
  have h2 : T (blockIdx n) ≤ T M := T_strictMono.monotone (by omega)
  omega

snip end

problem imc2014_p2 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => (S n : ℝ) / (n : ℝ) ^ α) atTop (𝓝 β) ↔
      (α, β) ∈ answer := by
  -- TODO: full proof from here. Approach:
  -- (←) Sandwich argument: write n = T(m-1)+j with 1 ≤ j ≤ m. Then
  --     S(T(m-1)) ≤ S n ≤ S(T m), and (T(m-1))^{3/2} ≤ n^{3/2} ≤ (T m)^{3/2},
  --     so S n / n^{3/2} is squeezed between S(T(m-1))/(T m)^{3/2} and
  --     S(T m)/(T(m-1))^{3/2}, both → √2/3.
  -- (→) Uniqueness from convergence: along the subsequence N = T m,
  --     S(T m)/(T m)^α = (m(m+1)(m+2)/6) / (m(m+1)/2)^α tends to a positive
  --     finite limit iff α = 3/2, in which case the limit is √2/3.
  sorry

end Imc2014P2
