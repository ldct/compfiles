/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 3

Define the sequence `x₁, x₂, …` by `x₁ = √5` and `x_{n+1} = x_n² - 2` for `n ≥ 1`.
Compute
  `lim_{n → ∞} (x₁ · x₂ ⋯ x_n) / x_{n+1}`.

The answer is `1`.
-/

namespace Imc2010P3

/-- The sequence `xₙ` defined by `x₁ = √5` and `x_{n+1} = xₙ² - 2`.
We use 0-indexing, so `x 0 = √5`, `x 1 = 3`, etc. -/
noncomputable def x : ℕ → ℝ
  | 0 => Real.sqrt 5
  | n + 1 => (x n) ^ 2 - 2

snip begin

/-- `x n` squared is at least `5` for every `n`. -/
lemma sq_ge_five (n : ℕ) : 5 ≤ (x n) ^ 2 := by
  induction n with
  | zero =>
    show 5 ≤ (Real.sqrt 5) ^ 2
    rw [Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  | succ k ih =>
    -- (x k)^2 ≥ 5, so x(k+1) = (x k)^2 - 2 ≥ 3, and (x(k+1))^2 ≥ 9 ≥ 5.
    show 5 ≤ (x (k+1)) ^ 2
    have hk : (x k) ^ 2 - 2 ≥ 3 := by linarith
    have : x (k+1) = (x k)^2 - 2 := rfl
    rw [this]
    nlinarith

/-- `x n` is positive for every `n`. -/
lemma x_pos (n : ℕ) : 0 < x n := by
  induction n with
  | zero =>
    show 0 < Real.sqrt 5
    exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  | succ k _ =>
    show 0 < (x k)^2 - 2
    have := sq_ge_five k
    linarith

/-- `x n` is positive (as a nonnegative version). -/
lemma x_ne_zero (n : ℕ) : x n ≠ 0 := (x_pos n).ne'

/-- Define `y n = (x n)^2`. -/
noncomputable def y (n : ℕ) : ℝ := (x n) ^ 2

lemma y_zero : y 0 = 5 := by
  unfold y x
  rw [Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]

lemma y_succ (n : ℕ) : y (n + 1) = (y n - 2) ^ 2 := by
  unfold y
  show (x (n+1))^2 = ((x n)^2 - 2)^2
  have : x (n+1) = (x n)^2 - 2 := rfl
  rw [this]

lemma y_ge_five (n : ℕ) : 5 ≤ y n := sq_ge_five n

lemma y_sub_four_pos (n : ℕ) : 0 < y n - 4 := by
  have := y_ge_five n
  linarith

/-- The key recursive identity: `y_{n+1} - 4 = y_n * (y_n - 4)`. -/
lemma y_succ_sub_four (n : ℕ) : y (n + 1) - 4 = y n * (y n - 4) := by
  rw [y_succ]
  ring

/-- The telescoping product: `∏_{k ≤ n} y k = y (n+1) - 4`. -/
lemma prod_y_eq (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), y k) = y (n + 1) - 4 := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.prod_singleton]
    rw [y_zero, y_succ, y_zero]
    norm_num
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    have h := y_succ_sub_four (m + 1)
    linarith

/-- The square of the partial product ratio. -/
lemma ratio_sq (n : ℕ) :
    ((∏ k ∈ Finset.range (n + 1), x k) / x (n + 1)) ^ 2
      = 1 - 4 / y (n + 1) := by
  have hxn1 : x (n+1) ≠ 0 := x_ne_zero (n+1)
  have hy : y (n+1) ≠ 0 := by
    unfold y; exact pow_ne_zero _ hxn1
  have hsq : (∏ k ∈ Finset.range (n + 1), x k) ^ 2
      = ∏ k ∈ Finset.range (n + 1), y k := by
    rw [← Finset.prod_pow]
    rfl
  rw [div_pow, hsq, prod_y_eq]
  unfold y
  field_simp

/-- The partial product divided by `x_{n+1}` is positive. -/
lemma ratio_pos (n : ℕ) :
    0 < (∏ k ∈ Finset.range (n + 1), x k) / x (n + 1) := by
  apply div_pos
  · exact Finset.prod_pos (fun k _ => x_pos k)
  · exact x_pos _

/-- `y n → ∞`. -/
lemma y_tendsto : Filter.Tendsto y Filter.atTop Filter.atTop := by
  -- y (n+1) - 4 = y n * (y n - 4) ≥ 1 * (y n - 4) = y n - 4 since y n ≥ 5 ≥ 1.
  -- More usefully: y (n+1) = (y n - 2)^2 ≥ (y n - 2) since y n - 2 ≥ 3 ≥ 1.
  -- Actually: y n ≥ y 0 + n = 5 + n by induction since y (n+1) ≥ y n + 1.
  -- In fact y(n+1) - y n = (y n - 2)^2 - y n = y_n^2 - 5 y_n + 4.
  -- With y n ≥ 5: y_n^2 - 5 y_n + 4 = y_n(y_n - 5) + 4 ≥ 4. So y(n+1) ≥ y n + 4.
  have h_incr : ∀ n, y n + 4 ≤ y (n + 1) := by
    intro n
    have hy : 5 ≤ y n := y_ge_five n
    have : y (n + 1) = (y n - 2) ^ 2 := y_succ n
    rw [this]
    nlinarith
  -- So y n ≥ 5 + 4*n.
  have h_lb : ∀ m : ℕ, 5 + 4 * (m : ℝ) ≤ y m := by
    intro m
    induction m with
    | zero => rw [y_zero]; simp
    | succ k ih =>
      calc 5 + 4 * ((k + 1 : ℕ) : ℝ)
          = (5 + 4 * k) + 4 := by push_cast; ring
        _ ≤ y k + 4 := by linarith
        _ ≤ y (k + 1) := h_incr k
  -- Thus y → ∞.
  apply Filter.tendsto_atTop_mono h_lb
  have : Filter.Tendsto (fun n : ℕ => 5 + 4 * (n : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    exact tendsto_natCast_atTop_atTop
  exact this

/-- `4 / y n → 0`. -/
lemma four_div_y_tendsto : Filter.Tendsto (fun n => 4 / y n) Filter.atTop (nhds 0) := by
  have h := Filter.Tendsto.const_div_atTop y_tendsto (4 : ℝ)
  exact h

snip end

problem imc2010_p3 :
    Filter.Tendsto (fun n => (∏ k ∈ Finset.range (n + 1), x k) / x (n + 1))
      Filter.atTop (nhds 1) := by
  -- Let r n = (∏ k ≤ n, x k) / x(n+1). Then r n > 0 and (r n)^2 = 1 - 4/y(n+1) → 1.
  -- So r n → 1 (via sqrt).
  set r : ℕ → ℝ := fun n => (∏ k ∈ Finset.range (n + 1), x k) / x (n + 1) with hr_def
  -- Step 1: (r n)^2 → 1.
  have h_sq_tendsto : Filter.Tendsto (fun n => (r n)^2) Filter.atTop (nhds 1) := by
    have heq : ∀ n, (r n)^2 = 1 - 4 / y (n + 1) := fun n => ratio_sq n
    have hlim : Filter.Tendsto (fun n : ℕ => 1 - 4 / y (n + 1)) Filter.atTop (nhds 1) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (4 : ℝ) / y (n + 1)) Filter.atTop (nhds 0) := by
        have : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
          Filter.tendsto_add_atTop_nat 1
        exact four_div_y_tendsto.comp this
      have : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 4 / y (n + 1)) Filter.atTop
              (nhds (1 - 0)) := Filter.Tendsto.const_sub 1 h1
      simpa using this
    exact Filter.Tendsto.congr (fun n => (heq n).symm) hlim
  -- Step 2: r n > 0.
  have h_pos : ∀ n, 0 < r n := fun n => ratio_pos n
  -- Step 3: |r n - 1| ≤ |r n ^ 2 - 1| / (r n + 1) ≤ |r n ^ 2 - 1| (since r n + 1 ≥ 1).
  -- r n - 1 = (r n ^ 2 - 1) / (r n + 1).
  have h_r1 : ∀ n, r n - 1 = ((r n)^2 - 1) / (r n + 1) := by
    intro n
    have hpos : 0 < r n + 1 := by linarith [h_pos n]
    have hne : r n + 1 ≠ 0 := hpos.ne'
    field_simp
    ring
  have h_abs : ∀ n, |r n - 1| ≤ |(r n)^2 - 1| := by
    intro n
    rw [h_r1 n]
    rw [abs_div]
    have hpos : 0 < r n + 1 := by linarith [h_pos n]
    have h1le : 1 ≤ |r n + 1| := by
      rw [abs_of_pos hpos]; linarith [h_pos n]
    have habs_pos : 0 < |r n + 1| := by linarith
    rw [div_le_iff₀ habs_pos]
    calc |(r n)^2 - 1| = |(r n)^2 - 1| * 1 := (mul_one _).symm
      _ ≤ |(r n)^2 - 1| * |r n + 1| := by
          apply mul_le_mul_of_nonneg_left h1le (abs_nonneg _)
  -- Step 4: (r n ^ 2 - 1) → 0, so |r n ^ 2 - 1| → 0, so |r n - 1| → 0, so r n → 1.
  have h_sq_sub : Filter.Tendsto (fun n => (r n)^2 - 1) Filter.atTop (nhds 0) := by
    have := h_sq_tendsto.sub_const 1
    simpa using this
  have h_abs_sq : Filter.Tendsto (fun n => |(r n)^2 - 1|) Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = |0| from (abs_zero).symm]
    exact h_sq_sub.abs
  have h_abs_r : Filter.Tendsto (fun n => |r n - 1|) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => abs_nonneg _) h_abs h_abs_sq
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at h_abs_r
  obtain ⟨N, hN⟩ := h_abs_r ε hε
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simp only [Real.dist_eq] at this ⊢
  have habs_eq : |(|r n - 1|) - 0| = |r n - 1| := by simp
  rw [habs_eq] at this
  exact this

end Imc2010P3
