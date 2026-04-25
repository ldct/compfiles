/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 8

Define the sequence `x₁, x₂, …` by `x₁ = 2`, `x₂ = 4`, and

  `xₙ₊₂ = 3 xₙ₊₁ − 2 xₙ + 2ⁿ / xₙ`  for `n ≥ 1`.

Prove that `lim xₙ / 2ⁿ` exists and satisfies
`(1 + √3)/2 ≤ lim ≤ 3/2`.
-/

namespace Imc2024P8

/-- The recursive sequence. We use 0-indexed: `x 0` corresponds to the
problem's `x_1 = 2`, `x 1` corresponds to `x_2 = 4`. The paper recurrence
`x_{m+2} = 3 x_{m+1} - 2 x_m + 2^m / x_m` for `m ≥ 1` with our index shift
`m = n + 1` becomes `x (n+2) = 3 x (n+1) - 2 x n + 2^(n+1) / x n`. -/
noncomputable def x : ℕ → ℝ
  | 0 => 2  -- x_1 (1-indexed in the problem; we use 0-indexed)
  | 1 => 4  -- x_2
  | n + 2 => 3 * x (n + 1) - 2 * x n + (2 : ℝ) ^ (n + 1) / x n

snip begin

/-- Combined induction: `x n > 0` and `2 * x n ≤ x (n+1)`. The induction is
on `n`; at step `n+1` we need the bound at `n` (for `x (n+2)`). -/
lemma pos_and_mono : ∀ n : ℕ, 0 < x n ∧ 2 * x n ≤ x (n + 1)
  | 0 => by
      refine ⟨by norm_num [x], ?_⟩
      show 2 * x 0 ≤ x 1
      simp [x]; norm_num
  | n + 1 => by
      have ih := pos_and_mono n
      obtain ⟨hpos_n, h_n⟩ := ih
      -- x(n+1) ≥ 2 x n > 0
      have hpos_n1 : 0 < x (n + 1) := lt_of_lt_of_le (by linarith) h_n
      refine ⟨hpos_n1, ?_⟩
      -- Need: 2 * x (n+1) ≤ x (n+2).
      -- x (n+2) = 2 x(n+1) + (x(n+1) - 2 x n) + 2^(n+1)/x n
      have hx2 : x (n + 2) = 2 * x (n + 1) + (x (n + 1) - 2 * x n) +
          (2 : ℝ) ^ (n + 1) / x n := by
        show 3 * x (n + 1) - 2 * x n + (2 : ℝ) ^ (n + 1) / x n = _
        ring
      have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
      have hdiv : (0 : ℝ) ≤ (2 : ℝ) ^ (n + 1) / x n := le_of_lt (div_pos hpow hpos_n)
      have hsub : 0 ≤ x (n + 1) - 2 * x n := by linarith
      linarith [hx2]

lemma x_pos (n : ℕ) : 0 < x n := (pos_and_mono n).1

lemma two_mul_x_le (n : ℕ) : 2 * x n ≤ x (n + 1) := (pos_and_mono n).2

/-- The normalized sequence `y n = x n / 2^(n+1)`. -/
noncomputable def y (n : ℕ) : ℝ := x n / (2 : ℝ) ^ (n + 1)

lemma y_zero : y 0 = 1 := by simp [y, x]

lemma y_one : y 1 = 1 := by simp [y, x]; norm_num

lemma two_pow_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := by positivity

lemma y_pos (n : ℕ) : 0 < y n :=
  div_pos (x_pos n) (two_pow_pos _)

/-- `y` is monotone: `y n ≤ y (n+1)`. Follows from `2 * x n ≤ x (n+1)`. -/
lemma y_le_succ (n : ℕ) : y n ≤ y (n + 1) := by
  unfold y
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := two_pow_pos _
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (n + 1 + 1) := two_pow_pos _
  rw [div_le_div_iff₀ hpow hpow2]
  have hmul : 2 * x n ≤ x (n + 1) := two_mul_x_le n
  have hpow_eq : (2 : ℝ) ^ (n + 1 + 1) = 2 * (2 : ℝ) ^ (n + 1) := by ring
  rw [hpow_eq]
  nlinarith [hmul, x_pos n, hpow]

lemma y_mono : Monotone y := monotone_nat_of_le_succ y_le_succ

lemma one_le_y (n : ℕ) : 1 ≤ y n := by
  rw [← y_zero]
  exact y_mono (Nat.zero_le n)

/-- The recurrence translated to `y`:
`4 y(n+2) - 2 y(n+1) = 4 y(n+1) - 2 y n + 1/(2^(n+1) * y n)`. -/
lemma y_recurrence (n : ℕ) :
    4 * y (n + 2) - 2 * y (n + 1) =
      4 * y (n + 1) - 2 * y n + 1 / ((2 : ℝ) ^ (n + 1) * y n) := by
  unfold y
  have hxn : 0 < x n := x_pos n
  have hxn1 : 0 < x (n + 1) := x_pos (n + 1)
  have hp1 : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := two_pow_pos _
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (n + 2) := two_pow_pos _
  have hp3 : (0 : ℝ) < (2 : ℝ) ^ (n + 3) := two_pow_pos _
  have hxdef : x (n + 2) = 3 * x (n + 1) - 2 * x n + (2 : ℝ) ^ (n + 1) / x n := rfl
  rw [hxdef]
  have h21 : (2 : ℝ) ^ (n + 2) = 2 * (2 : ℝ) ^ (n + 1) := by ring
  have h32 : (2 : ℝ) ^ (n + 3) = 4 * (2 : ℝ) ^ (n + 1) := by ring
  rw [show (n + 2 + 1) = n + 3 from rfl, h32, h21]
  field_simp
  ring

/-- Sum-form of the telescoped recurrence:
`4 y(n+1) - 2 y n = 2 + Σ_{k=0}^{n-1} 1/(2^(k+1) y k)`. -/
lemma a_sum_eq (n : ℕ) :
    4 * y (n + 1) - 2 * y n =
      2 + ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) * y k) := by
  induction n with
  | zero => simp [y_zero, y_one]; norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      have hr := y_recurrence n
      linarith

/-- Key bound: `4 y(n+1) - 2 y n ≤ 3` for all `n`. -/
lemma a_le_three (n : ℕ) : 4 * y (n + 1) - 2 * y n ≤ 3 := by
  rw [a_sum_eq]
  have hsum : ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) * y k) ≤ 1 := by
    have hbound : ∀ k ∈ Finset.range n,
        1 / ((2 : ℝ) ^ (k + 1) * y k) ≤ (1 / 2) ^ (k + 1) := by
      intro k _
      have hp : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := two_pow_pos _
      have hyk : 0 < y k := y_pos k
      have hyk1 : 1 ≤ y k := one_le_y k
      have h12 : ((1 : ℝ) / 2) ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) := by
        rw [div_pow, one_pow]
      rw [h12]
      apply one_div_le_one_div_of_le hp
      calc (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * 1 := by ring
        _ ≤ (2 : ℝ) ^ (k + 1) * y k :=
            mul_le_mul_of_nonneg_left hyk1 (le_of_lt hp)
    calc ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) * y k)
        ≤ ∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ (k + 1) :=
          Finset.sum_le_sum hbound
      _ = ∑ k ∈ Finset.range n, (1 / 2) * ((1 / 2) ^ k) := by
          congr 1; ext k; ring
      _ = (1 / 2) * ∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k := by
          rw [Finset.mul_sum]
      _ = 1 - ((1:ℝ)/2)^n := by
          rw [geom_sum_eq (by norm_num : (1:ℝ)/2 ≠ 1)]
          field_simp
          ring
      _ ≤ 1 := by
          have hpow : (0 : ℝ) ≤ (1/2 : ℝ) ^ n := by positivity
          linarith
  linarith

/-- Upper bound on `y`: `y n ≤ 3/2`. -/
lemma y_le (n : ℕ) : y n ≤ 3 / 2 := by
  rcases n with _ | n
  · rw [y_zero]; norm_num
  · have h := a_le_three n
    have hmono : y n ≤ y (n + 1) := y_le_succ n
    linarith

snip end

problem imc2024_p8 :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => x n / (2 : ℝ) ^ (n + 1))
        Filter.atTop (nhds L) ∧
      (1 + Real.sqrt 3) / 2 ≤ L ∧ L ≤ 3 / 2 := by
  -- Paper solution: let y_n = x_n / 2^(n+1). Then y is increasing and bounded
  -- above by 3/2. Telescoping the recurrence: 4 y(n+1) - 2 y n = 2 + S_n
  -- where S_n = Σ_{k<n} 1/(2^(k+1) y k). As n→∞, y_n → c, so 2c = 2 + S∞,
  -- with S∞ ≥ 1/c (using y_k ≤ c). Thus 2c^2 - 2c - 1 ≥ 0, giving c ≥ (1+√3)/2.
  set f : ℕ → ℝ := fun n => x n / (2 : ℝ) ^ (n + 1) with hf
  have hf_eq : ∀ n, f n = y n := fun n => rfl
  -- Existence of limit: monotone bounded above.
  have hmono : Monotone f := by
    intro m n hmn
    rw [hf_eq, hf_eq]
    exact y_mono hmn
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨3 / 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [hf_eq]; exact y_le n
  set L : ℝ := ⨆ n, f n with hL
  have htends : Filter.Tendsto f Filter.atTop (nhds L) :=
    tendsto_atTop_ciSup hmono hbdd
  refine ⟨L, htends, ?_, ?_⟩
  · -- Lower bound: c ≥ (1+√3)/2.
    -- We have 4 y(n+1) - 2 y n = 2 + Σ_{k<n} 1/(2^(k+1) y k) ≥ 2 + Σ_{k<n} 1/(2^(k+1) L).
    -- Taking n → ∞: 2L ≥ 2 + 1/L, so 2L^2 - 2L - 1 ≥ 0, hence L ≥ (1+√3)/2.
    -- First, L ≥ 1 from y 0 = 1.
    have hL1 : 1 ≤ L := by
      rw [hL]
      have : f 0 ≤ ⨆ n, f n := le_ciSup hbdd 0
      rw [hf_eq, y_zero] at this
      exact this
    have hL_pos : 0 < L := by linarith
    -- L is the limit of y; y is monotone so y n ≤ L for all n.
    have hyL : ∀ n, y n ≤ L := by
      intro n
      have : f n ≤ L := le_ciSup hbdd n
      rw [hf_eq] at this
      exact this
    -- Show that `4 * L - 2 * L = 2L` is at least `2 + 1/L`. We use the
    -- telescoping equality at `n` and lower-bound the sum by `(1 - (1/2)^n)/L`.
    have hkey : 2 * L ≥ 2 + 1 / L := by
      -- It suffices to show, for every ε > 0, 2L + ε ≥ 2 + 1/L.
      by_contra hcontra
      push Not at hcontra
      -- hcontra : 2 * L < 2 + 1 / L
      set ε : ℝ := (2 + 1 / L - 2 * L) / 2 with hε_def
      have hε_pos : 0 < ε := by
        rw [hε_def]; linarith
      -- Choose n large enough so 1/2^n * (1/L) < ε/2 and y(n+1) close to L.
      -- Actually: a(n) = 4 y(n+1) - 2 y n = 2 + Σ_{k<n} 1/(2^(k+1) y_k) ≤ 2 + Σ 1/(2^(k+1) L) -- WRONG direction.
      -- Reverse: use y_k ≤ L to get 1/(2^(k+1) y_k) ≥ 1/(2^(k+1) L).
      -- So a n ≥ 2 + (1 - (1/2)^n)/L. As y(n+1), y n → L, a n → 2L.
      -- So 2L ≥ 2 + 1/L.
      have hsum_lb : ∀ n, 2 + (1 - ((1:ℝ)/2)^n) / L ≤ 4 * y (n + 1) - 2 * y n := by
        intro n
        rw [a_sum_eq]
        have hsumineq : (1 - ((1:ℝ)/2)^n) / L ≤
            ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) * y k) := by
          have hcalc : (1 - ((1:ℝ)/2)^n) / L =
              ∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) * L) := by
            have hLne : L ≠ 0 := ne_of_gt hL_pos
            have hrw : ∀ k, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) * L) = (1/L) * ((1/2)^(k+1)) := by
              intro k
              rw [div_pow, one_pow]
              field_simp
            rw [show (∑ k ∈ Finset.range n, 1 / ((2 : ℝ) ^ (k + 1) * L))
                = ∑ k ∈ Finset.range n, (1/L) * ((1/2)^(k+1)) from
              Finset.sum_congr rfl (fun k _ => hrw k)]
            rw [← Finset.mul_sum]
            have hgeom : ∑ k ∈ Finset.range n, ((1:ℝ)/2)^(k+1) =
                (1/2) * ∑ k ∈ Finset.range n, ((1:ℝ)/2)^k := by
              rw [Finset.mul_sum]; congr 1; ext k; ring
            rw [hgeom, geom_sum_eq (by norm_num : (1:ℝ)/2 ≠ 1)]
            field_simp
            ring
          rw [hcalc]
          apply Finset.sum_le_sum
          intro k _
          have hyk : 0 < y k := y_pos k
          have hykL : y k ≤ L := hyL k
          have hp : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := two_pow_pos _
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hh : (2 : ℝ) ^ (k + 1) * y k ≤ (2 : ℝ) ^ (k + 1) * L :=
            mul_le_mul_of_nonneg_left hykL (le_of_lt hp)
          linarith
        linarith
      -- Now take n→∞: y(n+1), y n → L, so 4y(n+1) - 2y n → 2L.
      -- And 2 + (1 - (1/2)^n)/L → 2 + 1/L.
      have hy_tend : Filter.Tendsto y Filter.atTop (nhds L) := by
        have : f = y := funext hf_eq
        rw [this] at htends; exact htends
      have hy1_tend : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds L) :=
        hy_tend.comp (Filter.tendsto_add_atTop_nat 1)
      have ha_tend : Filter.Tendsto (fun n => 4 * y (n + 1) - 2 * y n) Filter.atTop
          (nhds (4 * L - 2 * L)) :=
        (hy1_tend.const_mul 4).sub (hy_tend.const_mul 2)
      have hsimp : (4 * L - 2 * L) = 2 * L := by ring
      rw [hsimp] at ha_tend
      have hpow_tend : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (nhds 0) := by
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · norm_num
        · norm_num
      have hsum_tend :
          Filter.Tendsto (fun n => 2 + (1 - ((1:ℝ)/2)^n) / L) Filter.atTop
            (nhds (2 + (1 - 0)/L)) := by
        apply Filter.Tendsto.const_add
        apply Filter.Tendsto.div_const
        exact tendsto_const_nhds.sub hpow_tend
      have hlim_lb : 2 + (1 - 0) / L ≤ 2 * L := by
        apply le_of_tendsto_of_tendsto' hsum_tend ha_tend
        exact hsum_lb
      have : 2 + 1 / L ≤ 2 * L := by
        have : (2 : ℝ) + (1 - 0) / L = 2 + 1 / L := by ring
        linarith [this, hlim_lb]
      linarith
    -- Now use: 2L ≥ 2 + 1/L means 2L^2 - 2L - 1 ≥ 0 (since L > 0).
    have hL_quad : 2 * L^2 - 2 * L - 1 ≥ 0 := by
      have hL_pos' : 0 < L := hL_pos
      have h := hkey
      have h2 : 2 * L * L ≥ (2 + 1 / L) * L := by
        exact mul_le_mul_of_nonneg_right h (le_of_lt hL_pos')
      have h3 : (2 + 1 / L) * L = 2 * L + 1 := by
        field_simp
      nlinarith [h2, h3]
    -- Now: L ≥ (1 + √3)/2 since 2L^2 - 2L - 1 ≥ 0 and L > 0.
    -- The roots are (1 ± √3)/2. Since L > 0 and (1 - √3)/2 < 0, we need L ≥ (1 + √3)/2.
    have hsqrt3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hsqrt3_nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hsqrt3_le : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2^2 by norm_num,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    -- 2L^2 - 2L - 1 = 2(L - (1+√3)/2)(L - (1-√3)/2)
    -- Since L > 0 ≥ (1-√3)/2, L - (1-√3)/2 > 0.
    -- So 2L^2 - 2L - 1 ≥ 0 implies L - (1+√3)/2 ≥ 0.
    have hother : L - (1 - Real.sqrt 3) / 2 > 0 := by
      have : (1 - Real.sqrt 3) / 2 ≤ 0 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        have hsqrt3_pos : 1 ≤ Real.sqrt 3 := by
          rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
          exact Real.sqrt_le_sqrt (by norm_num)
        linarith
      linarith
    have hfactor : 2 * L^2 - 2 * L - 1 =
        2 * (L - (1 + Real.sqrt 3) / 2) * (L - (1 - Real.sqrt 3) / 2) := by
      have : Real.sqrt 3 ^ 2 = 3 := by rw [sq]; exact hsqrt3
      nlinarith [this]
    rw [hfactor] at hL_quad
    -- 2 * (L - (1+√3)/2) * (L - (1-√3)/2) ≥ 0, second factor > 0, so first ≥ 0.
    have hpos2 : 0 < 2 * (L - (1 - Real.sqrt 3) / 2) := by linarith
    have hprod : 0 ≤ (L - (1 + Real.sqrt 3) / 2) * (2 * (L - (1 - Real.sqrt 3) / 2)) := by
      have hrearr : 2 * (L - (1 + Real.sqrt 3) / 2) * (L - (1 - Real.sqrt 3) / 2) =
          (L - (1 + Real.sqrt 3) / 2) * (2 * (L - (1 - Real.sqrt 3) / 2)) := by ring
      linarith [hL_quad, hrearr]
    have hnonneg : 0 ≤ L - (1 + Real.sqrt 3) / 2 := by
      by_contra hneg
      push Not at hneg
      have : (L - (1 + Real.sqrt 3) / 2) * (2 * (L - (1 - Real.sqrt 3) / 2)) < 0 :=
        mul_neg_of_neg_of_pos hneg hpos2
      linarith
    linarith
  · -- Upper bound: L ≤ 3/2.
    rw [hL]
    apply ciSup_le
    intro n
    rw [hf_eq]
    exact y_le n

end Imc2024P8
