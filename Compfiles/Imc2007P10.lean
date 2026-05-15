/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2007, Problem 10
(IMC 2007, Day 2, Problem 4)

Let `n > 1` be an odd integer and let `A` be the `n × n` matrix with
  `A i i = 2`,
  `A i j = 1` if `i - j ≡ ±2 (mod n)`,
  `A i j = 0` otherwise.
Find `det A`.

Answer: `det A = 4`.

The matrix is indexed by `ZMod n`.
-/

namespace Imc2007P10

open Matrix Finset

/-- The `n × n` "cycle squared" matrix `A` from the problem, indexed by `ZMod n`. -/
noncomputable def Amat (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of (fun i j : ZMod n => if i = j then (2 : ℝ)
             else if i - j = 2 ∨ i - j = -2 then 1 else 0)

/-- The `n × n` cycle (adjacency of the `n`-cycle) matrix `B`. -/
noncomputable def Bmat (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℝ :=
  Matrix.of (fun i j : ZMod n => if i - j = 1 ∨ i - j = -1 then (1 : ℝ) else 0)

snip begin

/-! ### Preliminaries in `ZMod n` for `n` odd with `n ≥ 3`. -/

/-- For `n ≥ 3`, `(1 : ZMod n) ≠ -1`. -/
lemma one_ne_neg_one (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (1 : ZMod n) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod n) = 0 := by linear_combination h
  have : (n : ℤ) ∣ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 n).mp (by exact_mod_cast h2)
    exact this
  have hn' : (n : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) this
  omega

/-- For `n ≥ 3`, `(2 : ZMod n) ≠ 0`. -/
lemma two_ne_zero_zmod (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (2 : ZMod n) ≠ 0 := by
  intro h
  have : (n : ℤ) ∣ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 n).mp (by exact_mod_cast h)
    exact this
  have hn' : (n : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) this
  omega

/-- For `n` odd with `n ≥ 3`, `(2 : ZMod n) ≠ -2`. -/
lemma two_ne_neg_two (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (2 : ZMod n) ≠ -2 := by
  intro h
  have h4 : (4 : ZMod n) = 0 := by linear_combination h
  have : (n : ℤ) ∣ 4 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd 4 n).mp (by exact_mod_cast h4)
    exact this
  -- n ≥ 3, odd, divides 4. Divisors of 4 are 1, 2, 4. Odd ones: 1. But n ≥ 3.
  have hndvd : n ∣ 4 := by exact_mod_cast this
  have hn4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) hndvd
  interval_cases n
  all_goals (first | (exact absurd hndvd (by decide)) | exact (Nat.not_odd_iff_even.mpr (by decide)).elim hodd)

/-- For `n` odd with `n ≥ 3`, `(3 : ZMod n) ≠ 1`. -/
lemma three_ne_one (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (3 : ZMod n) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod n) = 0 := by linear_combination h
  exact two_ne_zero_zmod n hn h2

/-- For `n` odd with `n ≥ 3`, `(3 : ZMod n) ≠ -1`. -/
lemma three_ne_neg_one (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (3 : ZMod n) ≠ -1 := by
  intro h
  have h4 : (4 : ZMod n) = 0 := by linear_combination h
  have : (n : ℤ) ∣ 4 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd 4 n).mp (by exact_mod_cast h4)
    exact this
  have hndvd : n ∣ 4 := by exact_mod_cast this
  have hn4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) hndvd
  interval_cases n
  all_goals (first | (exact absurd hndvd (by decide)) | exact (Nat.not_odd_iff_even.mpr (by decide)).elim hodd)

/-- For `n` odd with `n ≥ 3`, `(-3 : ZMod n) ≠ 1`. -/
lemma neg_three_ne_one (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (-3 : ZMod n) ≠ 1 := by
  intro h
  have : (3 : ZMod n) = -1 := by linear_combination -h
  exact three_ne_neg_one n hn hodd this

/-- For `n` odd with `n ≥ 3`, `(-3 : ZMod n) ≠ -1`. -/
lemma neg_three_ne_neg_one (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (-3 : ZMod n) ≠ -1 := by
  intro h
  have : (3 : ZMod n) = 1 := by linear_combination -h
  exact three_ne_one n hn hodd this

/-! ### Sum over `B[i][·] * f`. -/

/-- Sum of `B[i][k] * f(k)` over `k` equals `f(i-1) + f(i+1)` for `n ≥ 3`. -/
lemma sum_Bmat_row_mul (n : ℕ) [NeZero n] (hn : 3 ≤ n) (i : ZMod n) (f : ZMod n → ℝ) :
    (∑ k : ZMod n, (if i - k = 1 ∨ i - k = -1 then (1 : ℝ) else 0) * f k)
      = f (i - 1) + f (i + 1) := by
  classical
  have hne : (1 : ZMod n) ≠ -1 := one_ne_neg_one n hn
  -- Simplify (ite 1 0) * f k to ite (f k) 0.
  have h1 : ∀ k : ZMod n, (if i - k = 1 ∨ i - k = -1 then (1 : ℝ) else 0) * f k
            = if i - k = 1 ∨ i - k = -1 then f k else 0 := by
    intro k; split_ifs <;> ring
  simp_rw [h1]
  rw [← Finset.sum_filter]
  -- The filtered set is {i - 1, i + 1}.
  have hfin : (Finset.univ.filter (fun k : ZMod n => i - k = 1 ∨ i - k = -1))
              = ({i - 1, i + 1} : Finset (ZMod n)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination -h
    · rintro (rfl | rfl)
      · left; ring
      · right; ring
  rw [hfin]
  rw [Finset.sum_insert, Finset.sum_singleton]
  simp only [Finset.mem_singleton]
  intro h
  have h2 : (2 : ZMod n) = 0 := by linear_combination -h
  exact two_ne_zero_zmod n hn h2

/-! ### `A = B * B`. -/

lemma Amat_eq_Bmat_sq (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    Amat n = Bmat n * Bmat n := by
  ext i j
  simp only [Amat, Bmat, Matrix.of_apply, Matrix.mul_apply]
  rw [sum_Bmat_row_mul n hn i (fun k => if k - j = 1 ∨ k - j = -1 then (1 : ℝ) else 0)]
  -- Now analyze.
  -- (i - 1) - j = (i - j) - 1 =: d - 1
  -- (i + 1) - j = (i - j) + 1 =: d + 1
  set d : ZMod n := i - j with hd_def
  have heq1 : i - 1 - j = d - 1 := by rw [hd_def]; ring
  have heq2 : i + 1 - j = d + 1 := by rw [hd_def]; ring
  rw [heq1, heq2]
  -- Relate `i = j` to `d = 0`, and `i - j = ±2` to `d = ±2`.
  have heq_ij : (i = j) ↔ (d = 0) := by
    rw [hd_def]; constructor
    · intro h; rw [h]; ring
    · intro h; linear_combination h
  -- Case analysis on d.
  by_cases hd0 : d = 0
  · -- d = 0 → i = j → LHS = 2. RHS: d - 1 = -1 ✓, d + 1 = 1 ✓. Sum = 1 + 1 = 2.
    rw [heq_ij.mpr hd0]
    rw [if_pos rfl]
    have hd1 : (d - 1 : ZMod n) = -1 := by rw [hd0]; ring
    have hd2 : (d + 1 : ZMod n) = 1 := by rw [hd0]; ring
    rw [hd1, hd2]
    have hne : (1 : ZMod n) ≠ -1 := one_ne_neg_one n hn
    -- (if -1 = 1 ∨ -1 = -1 then 1 else 0) + (if 1 = 1 ∨ 1 = -1 then 1 else 0) = 2
    have c1 : (if (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 then (1 : ℝ) else 0) = 1 := by
      rw [if_pos (Or.inr rfl)]
    have c2 : (if (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 then (1 : ℝ) else 0) = 1 := by
      rw [if_pos (Or.inl rfl)]
    rw [c1, c2]; norm_num
  -- i ≠ j since d ≠ 0.
  have hij : i ≠ j := fun h => hd0 (heq_ij.mp h)
  rw [if_neg hij]
  by_cases hd2 : d = 2
  · -- d = 2. RHS: d - 1 = 1 ✓. d + 1 = 3 ✗. Sum = 1. LHS: d = 2 → use second ite true.
    have c1 : (if d = 2 ∨ d = -2 then (1 : ℝ) else 0) = 1 := if_pos (Or.inl hd2)
    rw [c1]
    have hd1 : (d - 1 : ZMod n) = 1 := by rw [hd2]; ring
    have hd3 : (d + 1 : ZMod n) = 3 := by rw [hd2]; ring
    rw [hd1, hd3]
    have hone_ne_neg : (1 : ZMod n) ≠ -1 := one_ne_neg_one n hn
    have : (if (1 : ZMod n) = 1 ∨ (1 : ZMod n) = -1 then (1 : ℝ) else 0) = 1 := by
      rw [if_pos (Or.inl rfl)]
    rw [this]
    have h3_1 : (3 : ZMod n) ≠ 1 := three_ne_one n hn hodd
    have h3_n1 : (3 : ZMod n) ≠ -1 := three_ne_neg_one n hn hodd
    have : (if (3 : ZMod n) = 1 ∨ (3 : ZMod n) = -1 then (1 : ℝ) else 0) = 0 := by
      rw [if_neg]; push Not; exact ⟨h3_1, h3_n1⟩
    rw [this]; ring
  by_cases hdm2 : d = -2
  · -- d = -2. RHS: d - 1 = -3 ✗. d + 1 = -1 ✓. Sum = 1. LHS: second ite second branch.
    have c1 : (if d = 2 ∨ d = -2 then (1 : ℝ) else 0) = 1 := if_pos (Or.inr hdm2)
    rw [c1]
    have hd1 : (d - 1 : ZMod n) = -3 := by rw [hdm2]; ring
    have hd3 : (d + 1 : ZMod n) = -1 := by rw [hdm2]; ring
    rw [hd1, hd3]
    have h_n3_1 : (-3 : ZMod n) ≠ 1 := neg_three_ne_one n hn hodd
    have h_n3_n1 : (-3 : ZMod n) ≠ -1 := neg_three_ne_neg_one n hn hodd
    have : (if (-3 : ZMod n) = 1 ∨ (-3 : ZMod n) = -1 then (1 : ℝ) else 0) = 0 := by
      rw [if_neg]; push Not; exact ⟨h_n3_1, h_n3_n1⟩
    rw [this]
    have : (if (-1 : ZMod n) = 1 ∨ (-1 : ZMod n) = -1 then (1 : ℝ) else 0) = 1 := by
      rw [if_pos (Or.inr rfl)]
    rw [this]; ring
  · -- d ∉ {0, 2, -2}. LHS = 0. RHS: neither d - 1 nor d + 1 is ±1 (else d = 0, 2, or -2).
    have c1 : (if d = 2 ∨ d = -2 then (1 : ℝ) else 0) = 0 := by
      rw [if_neg]; push Not; exact ⟨hd2, hdm2⟩
    rw [c1]
    -- RHS: d - 1 = 1 → d = 2; d - 1 = -1 → d = 0; both excluded. Similarly d + 1.
    have e1 : (if d - 1 = 1 ∨ d - 1 = -1 then (1 : ℝ) else 0) = 0 := by
      rw [if_neg]
      push Not
      refine ⟨?_, ?_⟩
      · intro h; apply hd2; linear_combination h
      · intro h; apply hd0; linear_combination h
    have e2 : (if d + 1 = 1 ∨ d + 1 = -1 then (1 : ℝ) else 0) = 0 := by
      rw [if_neg]
      push Not
      refine ⟨?_, ?_⟩
      · intro h; apply hd0; linear_combination h
      · intro h; apply hdm2; linear_combination h
    rw [e1, e2]; ring

/-! ### `det B = 2` for odd `n ≥ 3`.

We classify the permutations `σ` that contribute to `det B = ∑_σ sign(σ) · ∏_i B[σ(i), i]`.
For the product to be nonzero, we need `σ(i) - i ∈ {±1}` for all `i`. Summing over `i`,
`∑ (σ i - i) = 0` in `ZMod n` (since `σ` is a bijection), so if `a = #{i : σ i - i = 1}`
and `b = #{i : σ i - i = -1}`, then `a + b = n` and `n ∣ a - b` as integers. Since
`|a - b| ≤ n` and `a - b` has the same parity as `a + b = n` (which is odd), `a - b` is odd,
hence nonzero, so `a - b = ±n`, giving `(a, b) = (n, 0)` or `(0, n)`. Thus `σ` is one of the
two cyclic shifts `i ↦ i + 1` or `i ↦ i - 1`.

Each such shift is a full `n`-cycle, with sign `(-1)^(n-1) = 1` for `n` odd. Thus
`det B = 1 + 1 = 2`.

TODO: formalize this permutation classification.
-/

lemma det_Bmat_odd (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (Bmat n).det = 2 := by
  sorry

snip end

/-- The answer: `det A = 4`. -/
determine detAnswer : ℝ := 4

problem imc2007_p10 (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hodd : Odd n) :
    (Amat n).det = detAnswer := by
  show (Amat n).det = 4
  rw [Amat_eq_Bmat_sq n hn hodd, Matrix.det_mul, det_Bmat_odd n hn hodd]
  norm_num

end Imc2007P10
