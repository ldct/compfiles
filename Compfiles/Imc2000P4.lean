/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 4

(a) If `(xᵢ)` is a decreasing positive sequence, then
    `(∑_{i=1}^n xᵢ²)^{1/2} ≤ ∑_{i=1}^n xᵢ/√i`.

(b) There is a constant `C` such that for every decreasing positive sequence
    `(xᵢ)`,
    `∑_{m=1}^∞ (1/√m) (∑_{i=m}^∞ xᵢ²)^{1/2} ≤ C ∑_{i=1}^∞ xᵢ`.
-/

namespace Imc2000P4

open scoped BigOperators

snip begin

/-- Arithmetic fact used in the inductive step: `3n² + 4n ≥ 0`, giving
`2 √(n(n+1)) ≥ n`, i.e. `√n ≥ n / (2 √(n+1))`. -/
lemma sqrt_n_ge_half (n : ℕ) :
    (n : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
  -- Want: n ≤ 2 √(n(n+1)). Both sides nonneg, square.
  -- (2√(n(n+1)))² = 4n(n+1) = 4n² + 4n.  n² ≤ 4n²+4n since 3n²+4n ≥ 0.
  have hsq : (n : ℝ) ^ 2 ≤ (2 * Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h1]
    nlinarith [hn0]
  have h2 : 0 ≤ 2 * Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := by positivity
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hn0, Real.sqrt_sq h2] at this
  exact this

/-- Key algebraic step in the inductive argument:
If `S ≥ 0`, `y ≥ 0`, and `√S ≥ y * n / (2 √(n+1))` (with `n+1 > 0`), then
`√(S + y²) ≤ √S + y / √(n+1)`. -/
lemma sqrt_add_sq_le {S y : ℝ} {n : ℕ} (hS : 0 ≤ S) (hy : 0 ≤ y)
    (hbnd : y * (n : ℝ) ≤ 2 * Real.sqrt S * Real.sqrt ((n : ℝ) + 1)) :
    Real.sqrt (S + y ^ 2) ≤ Real.sqrt S + y / Real.sqrt ((n : ℝ) + 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
  have hsqrt_npos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hnpos
  have hrhs_nn : 0 ≤ Real.sqrt S + y / Real.sqrt ((n : ℝ) + 1) := by
    have := Real.sqrt_nonneg S
    positivity
  -- Square both sides.
  rw [← Real.sqrt_sq hrhs_nn]
  apply Real.sqrt_le_sqrt
  have hsS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have hsqr_n1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt hnpos.le
  -- (√S + y/√(n+1))² = S + 2 √S y/√(n+1) + y²/(n+1).
  -- Want: S + y² ≤ S + 2 √S y/√(n+1) + y²/(n+1)
  -- i.e. y²(1 - 1/(n+1)) ≤ 2 √S y / √(n+1)
  -- i.e. y² n/(n+1) ≤ 2 √S y / √(n+1)
  -- Multiply both sides by (n+1): y² n ≤ 2 √S y √(n+1).
  -- If y = 0, trivial.  Else divide by y.
  by_cases hy0 : y = 0
  · subst hy0; simp; nlinarith [Real.sqrt_nonneg S]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  -- Goal: S + y^2 ≤ (√S + y/√(n+1))^2
  -- Expand directly using nlinarith.
  -- We know: hsS: √S² = S,  hsqr_n1: √(n+1)² = n+1,  hbnd: y·n ≤ 2 √S √(n+1).
  have key : y ^ 2 * (n : ℝ) ≤ 2 * Real.sqrt S * y * Real.sqrt ((n : ℝ) + 1) := by
    nlinarith [hbnd, hsqrtS_nn, hsqrt_npos.le, hy]
  -- Now show (√S + y/√(n+1))² ≥ S + y²  using:  √(n+1) > 0, y ≥ 0.
  -- Multiply through by (n+1): (n+1)(√S + y/√(n+1))² = (n+1)S + 2√S·y·√(n+1) + y²
  -- ≥ (n+1)(S + y²) iff 2√S·y·√(n+1) ≥ n·y², which is `key`.
  -- Expand (√S + y/√(n+1))² · (n+1) directly.
  set t : ℝ := Real.sqrt ((n : ℝ) + 1) with ht
  have ht_pos : 0 < t := hsqrt_npos
  have ht_sq : t ^ 2 = (n : ℝ) + 1 := hsqr_n1
  have ht_ne : t ≠ 0 := ht_pos.ne'
  have hmul : (Real.sqrt S + y / t) ^ 2 * ((n : ℝ) + 1) =
      S * ((n : ℝ) + 1) + 2 * Real.sqrt S * y * t + y ^ 2 := by
    -- Expand: (√S + y/t)² = S + 2√S·y/t + y²/t², then multiply by (n+1) = t².
    have h1 : (Real.sqrt S + y / t) ^ 2 =
        Real.sqrt S ^ 2 + 2 * Real.sqrt S * (y / t) + (y / t) ^ 2 := by ring
    rw [h1, hsS, ← ht_sq]
    field_simp
  -- Compare to (S + y²) * (n+1)
  have hgoal : (S + y ^ 2) * ((n : ℝ) + 1) ≤
      (Real.sqrt S + y / t) ^ 2 * ((n : ℝ) + 1) := by
    rw [hmul]
    nlinarith [key]
  -- Divide by (n+1) > 0.
  exact le_of_mul_le_mul_right (by linarith [hgoal]) hnpos

/-- Lower bound: for a decreasing positive sequence, `∑_{i=1}^n xᵢ² ≥ n · x_{n+1}²`. -/
lemma sum_sq_ge_of_decreasing {n : ℕ} (x : ℕ → ℝ)
    (hpos : ∀ i, 0 ≤ x i) (hdec : ∀ i j, i ≤ j → x j ≤ x i) :
    (n : ℝ) * x (n + 1) ^ 2 ≤ ∑ i ∈ Finset.range n, x (i + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hxn1 : x (n + 1 + 1) ≤ x (n + 1) := hdec (n + 1) (n + 1 + 1) (Nat.le_succ _)
    have hxn1_nn : 0 ≤ x (n + 1 + 1) := hpos _
    have hsq_le : x (n + 1 + 1) ^ 2 ≤ x (n + 1) ^ 2 := by
      have h1 : 0 ≤ x (n + 1) := hpos _
      nlinarith
    -- Also each earlier term x(i+1)² ≥ x(n+1+1)²
    have hall : ∀ i ∈ Finset.range n, x (n + 1 + 1) ^ 2 ≤ x (i + 1) ^ 2 := by
      intro i hi
      have hi_lt : i < n := Finset.mem_range.mp hi
      have hle : x (n + 1 + 1) ≤ x (i + 1) := hdec (i + 1) (n + 1 + 1) (by omega)
      have h1 : 0 ≤ x (i + 1) := hpos _
      nlinarith
    -- (n+1) x_{n+2}² = n x_{n+2}² + x_{n+2}² ≤ (∑... x_{i+1}²) + x_{n+1}²
    -- Bound: n·x_{n+2}² ≤ n·x_{n+1}² ≤ ∑_{i<n} x(i+1)² (need this?). Actually use ih with n but substituting
    -- Simpler: n x_{n+2}² ≤ ∑_{i<n} x(i+1)² because each x(i+1) ≥ x(n+2).
    have hbnd : (n : ℝ) * x (n + 1 + 1) ^ 2 ≤ ∑ i ∈ Finset.range n, x (i + 1) ^ 2 := by
      calc (n : ℝ) * x (n + 1 + 1) ^ 2
          = ∑ _i ∈ Finset.range n, x (n + 1 + 1) ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.range n, x (i + 1) ^ 2 :=
            Finset.sum_le_sum hall
    push_cast
    linarith

snip end

/--
Part (a): If `(xᵢ)` is a decreasing positive sequence (indexed `1, 2, …, n`),
then `(∑_{i=1}^n xᵢ²)^{1/2} ≤ ∑_{i=1}^n xᵢ/√i`.

We encode the sequence as a function `x : ℕ → ℝ` used at indices `1, 2, …, n`.
-/
problem imc2000_p4a (n : ℕ) (x : ℕ → ℝ)
    (hpos : ∀ i, 0 ≤ x i)
    (hdec : ∀ i j, i ≤ j → x j ≤ x i) :
    Real.sqrt (∑ i ∈ Finset.range n, x (i + 1) ^ 2) ≤
      ∑ i ∈ Finset.range n, x (i + 1) / Real.sqrt ((i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set S : ℝ := ∑ i ∈ Finset.range n, x (i + 1) ^ 2 with hS_def
    set T : ℝ := ∑ i ∈ Finset.range n, x (i + 1) / Real.sqrt ((i : ℝ) + 1) with hT_def
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => by positivity)
    have hsqrtS_nn : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
    have hy_nn : 0 ≤ x (n + 1) := hpos _
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    have hsqrt_npos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hnpos
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    change Real.sqrt (S + x (n + 1) ^ 2) ≤ T + x (n + 1) / Real.sqrt ((n : ℝ) + 1)
    -- Need: √(S + y²) ≤ √S + y/√(n+1) ≤ T + y/√(n+1).
    -- First inequality from sqrt_add_sq_le, requires y*n ≤ 2 √S √(n+1).
    -- √S ≥ √(n · x(n+1)²) = x(n+1)·√n, using sum_sq_ge_of_decreasing.
    have hS_lb : (n : ℝ) * x (n + 1) ^ 2 ≤ S := sum_sq_ge_of_decreasing x hpos hdec
    have hsqrtS_ge : x (n + 1) * Real.sqrt (n : ℝ) ≤ Real.sqrt S := by
      have h1 : x (n + 1) * Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) * x (n+1)^2) := by
        rw [show (n : ℝ) * x (n+1)^2 = x (n+1)^2 * (n : ℝ) from by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_sq hy_nn]
      rw [h1]; exact Real.sqrt_le_sqrt hS_lb
    -- bound needed: y * n ≤ 2 √S √(n+1)
    have hbnd : x (n + 1) * (n : ℝ) ≤ 2 * Real.sqrt S * Real.sqrt ((n : ℝ) + 1) := by
      -- It suffices: y·n ≤ 2·(y·√n)·√(n+1) and y·√n ≤ √S.
      -- So y·n ≤ 2·√S·√(n+1) follows from y·n ≤ 2·y·√n·√(n+1).
      have hstep : x (n + 1) * (n : ℝ) ≤ 2 * (x (n + 1) * Real.sqrt (n : ℝ)) *
          Real.sqrt ((n : ℝ) + 1) := by
        -- Equivalent: n ≤ 2 √n √(n+1) = 2 √(n(n+1)), which is sqrt_n_ge_half.
        have hc : (n : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) := sqrt_n_ge_half n
        have hsplit : Real.sqrt ((n : ℝ) * ((n : ℝ) + 1)) =
            Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + 1) :=
          Real.sqrt_mul (by exact_mod_cast Nat.zero_le _) _
        rw [hsplit] at hc
        nlinarith [hy_nn, Real.sqrt_nonneg ((n : ℝ)), hsqrt_npos.le]
      have hmul : 2 * (x (n + 1) * Real.sqrt (n : ℝ)) * Real.sqrt ((n : ℝ) + 1) ≤
          2 * Real.sqrt S * Real.sqrt ((n : ℝ) + 1) := by
        have := hsqrtS_ge
        nlinarith [hsqrt_npos.le]
      linarith
    have h1 : Real.sqrt (S + x (n + 1) ^ 2) ≤ Real.sqrt S + x (n + 1) / Real.sqrt ((n : ℝ) + 1) :=
      sqrt_add_sq_le hS_nn hy_nn hbnd
    have h2 : Real.sqrt S + x (n + 1) / Real.sqrt ((n : ℝ) + 1) ≤
        T + x (n + 1) / Real.sqrt ((n : ℝ) + 1) := by
      linarith [ih]
    linarith

/-- Part (b): There exists a constant `C` such that for every decreasing positive
sequence `(xᵢ)_{i≥1}` of reals, the Hardy-type inequality
`∑_m (1/√m) (∑_{i≥m} xᵢ²)^{1/2} ≤ C ∑_i xᵢ` holds.

We formalize this via summable hypotheses on `fun i => x (i+1)` and on
`fun i => x (i+1) / √(i+1) * ...`, but for simplicity require unconditionally the
`Summable` side conditions on both sides and express the claim as a bound on
partial sums (pointwise over `M, N`).
-/
problem imc2000_p4b :
    ∃ C : ℝ, ∀ (x : ℕ → ℝ),
      (∀ i, 0 < x i) → (∀ i j, i ≤ j → x j ≤ x i) →
      Summable (fun i => x (i + 1)) →
      (∀ m, Summable (fun i => x (i + m + 1) ^ 2)) →
      ∀ M : ℕ,
        ∑ m ∈ Finset.range M, (1 / Real.sqrt ((m : ℝ) + 1)) *
          Real.sqrt (∑' i, x (i + m + 1) ^ 2) ≤
        C * ∑' i, x (i + 1) := by
  -- TODO: prove with C = π using part (a) and the integral bound on the
  -- kernel 1/(√m √(i - m + 1)).
  sorry

end Imc2000P4
