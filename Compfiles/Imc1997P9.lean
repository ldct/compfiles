/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 9 (Day 2, Problem 3)

Show that the series

  `∑_{n=1}^∞ (-1)^{n-1} · sin(log n) / n^α`

converges if and only if `α > 0`.

## Solution outline (official)

Let `f(t) = sin(log t) / t^α` for `t ≥ 1`. Then
  `f'(t) = (cos(log t) - α · sin(log t)) / t^{α+1}`,
so `|f'(t)| ≤ (1 + α) / t^{α+1}` on `[1, ∞)`.

**Sufficiency (`α > 0`).** By the mean value theorem,
  `|f(n+1) - f(n)| ≤ (1 + α) / n^{α+1}`,
which is summable for `α > 0`. Pairing
  `(-1)^{2k-1} f(2k) + (-1)^{2k} f(2k+1) = f(2k+1) - f(2k)`,
the series of pairs converges absolutely. Combined with `f(n) → 0`
(since `|sin| ≤ 1` and `n^α → ∞`), the original series converges.

**Necessity (`α ≤ 0`).** It suffices to show divergence at `α = 0`,
i.e. that `sin(log n)` does not tend to zero (so the `n`-th term does
not go to zero, hence the series cannot converge). Suppose
`sin(log n) → 0`. Then `log n / π = k_n + λ_n` with `k_n ∈ ℤ` and
`λ_n → 0`. But `k_{n+1} - k_n = (1/π) log(1 + 1/n) - (λ_{n+1} - λ_n) → 0`,
so eventually `k_n` is constant, contradicting `log n → ∞`.

For `α < 0`, the term `|sin(log n)| / n^α = n^{|α|} · |sin(log n)|`
does not tend to zero either (using the same density argument: there
exist arbitrarily large `n` with `|sin(log n)| ≥ 1/2`).

## Status

`sorry` skeleton with detailed roadmap. The auxiliary formula for the
derivative of `f` is fully proved.
-/

namespace Imc1997P9

open scoped Topology BigOperators
open Filter Real Finset

/-- The summand `f_α(n) = sin(log n) / n^α`. By convention, the term at
`n = 0` is irrelevant (the series starts at `n = 1`); we set it to `0`
since `(0 : ℝ) ^ α = 0` for `α ≠ 0` (and `log 0 = 0`, so `sin(log 0) = 0`). -/
noncomputable def f (α : ℝ) (n : ℕ) : ℝ :=
  Real.sin (Real.log n) / (n : ℝ) ^ α

/-- The signed term `(-1)^{n-1} · f_α(n)` in the alternating series. -/
noncomputable def term (α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - 1) * f α n

snip begin

/-- Derivative of `t ↦ sin(log t) / t^α` for `t > 0`. -/
lemma hasDerivAt_f_real (α : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sin (Real.log s) / s ^ α)
      ((Real.cos (Real.log t) - α * Real.sin (Real.log t)) / t ^ (α + 1)) t := by
  -- d/dt sin(log t) = cos(log t) * (1/t)
  have h1 : HasDerivAt (fun s : ℝ => Real.sin (Real.log s))
      (Real.cos (Real.log t) * (1 / t)) t := by
    have hsin := (Real.hasDerivAt_sin (Real.log t)).comp t (Real.hasDerivAt_log ht.ne')
    simpa [one_div] using hsin
  -- d/dt t^α = α * t^(α-1)
  have h2 : HasDerivAt (fun s : ℝ => s ^ α) (α * t ^ (α - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  -- Quotient rule.
  have hpow : (0 : ℝ) < t ^ α := Real.rpow_pos_of_pos ht _
  have hne : (t : ℝ) ^ α ≠ 0 := hpow.ne'
  have hquot := h1.div h2 hne
  -- Simplify the derivative expression.
  convert hquot using 1
  have hα1 : t ^ (α + 1) = t ^ α * t := by
    rw [Real.rpow_add ht, Real.rpow_one]
  have hα_sub : t ^ (α - 1) = t ^ α / t := by
    rw [Real.rpow_sub ht, Real.rpow_one]
  rw [hα1, hα_sub]
  field_simp

/-- Bound on the derivative for `t ≥ 1` and `α ≥ 0`:
`|f'(t)| ≤ (1 + α) / t^{α+1}`. -/
lemma abs_deriv_f_le (α : ℝ) (hα : 0 ≤ α) {t : ℝ} (ht : 1 ≤ t) :
    |(Real.cos (Real.log t) - α * Real.sin (Real.log t)) / t ^ (α + 1)|
      ≤ (1 + α) / t ^ (α + 1) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hpow : (0 : ℝ) < t ^ (α + 1) := Real.rpow_pos_of_pos htpos _
  rw [abs_div, abs_of_pos hpow]
  apply div_le_div_of_nonneg_right _ hpow.le
  · -- |cos(log t) - α · sin(log t)| ≤ |cos(log t)| + α · |sin(log t)| ≤ 1 + α
    calc |Real.cos (Real.log t) - α * Real.sin (Real.log t)|
        ≤ |Real.cos (Real.log t)| + |α * Real.sin (Real.log t)| := abs_sub _ _
      _ = |Real.cos (Real.log t)| + α * |Real.sin (Real.log t)| := by
            rw [abs_mul, abs_of_nonneg hα]
      _ ≤ 1 + α * 1 := by
            gcongr
            · exact Real.abs_cos_le_one _
            · exact Real.abs_sin_le_one _
      _ = 1 + α := by ring

/-- For `α > 0`, `f α n → 0` as `n → ∞`. -/
lemma tendsto_f_zero {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => f α n) atTop (𝓝 0) := by
  -- We show |f α n| ≤ 1 / n^α (eventually), and 1/n^α → 0.
  have hbd : ∀ n : ℕ, 1 ≤ n → |f α n| ≤ 1 / (n : ℝ) ^ α := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hpos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnpos _
    rw [f, abs_div, Real.abs_rpow_of_nonneg hnpos.le, abs_of_pos hnpos]
    apply div_le_div_of_nonneg_right _ hpos.le
    exact Real.abs_sin_le_one _
  -- 1/n^α → 0 since α > 0.
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ α) atTop (𝓝 0) := by
    have hto : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ) ^ α)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hto
    simpa [one_div] using h0
  -- Combine via squeeze.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simpa [Real.norm_eq_abs] using hbd n hn

/-- **Sufficiency.** For `α > 0`, the alternating series converges. -/
lemma converges_of_pos {α : ℝ} (hα : 0 < α) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N, term α n) atTop (𝓝 L) := by
  -- Roadmap:
  -- 1. By MVT applied to `s ↦ sin(log s)/s^α` on `[n, n+1]` (n ≥ 1),
  --    `|f α (n+1) - f α n| ≤ (1+α) / n^{α+1}`.
  -- 2. The series `∑ (1+α)/n^{α+1}` converges (`Real.summable_one_div_nat_rpow`
  --    or similar, since `α + 1 > 1`).
  -- 3. Hence the series of "pair differences" `f α (2k+1) - f α (2k)` is
  --    absolutely summable.
  -- 4. The partial sums `S_{2N} = ∑_{k=0}^{N-1} (f α (2k+1) - f α (2k+2))`
  --    (after re-indexing) thus converge.
  -- 5. The odd partial sums `S_{2N+1} = S_{2N} + term α (2N+1)` differ from
  --    `S_{2N}` by `f α (2N+1) → 0`.
  -- 6. Combine to get convergence of `(S_N)` to a common limit.
  -- This is a standard application of the alternating-series test
  -- (`Antitone.tendsto_alternating_series_of_tendsto_zero` does not directly
  -- apply since `f α` is not monotone, but a similar Cauchy-pairing argument
  -- works because the variation `∑ |f α (n+1) - f α n|` is finite).
  sorry

/-- **Necessity.** If `α ≤ 0`, the series diverges, because `sin(log n)`
does not tend to zero, so the term `term α n` does not tend to zero. -/
lemma not_tendsto_sin_log : ¬ Tendsto (fun n : ℕ => Real.sin (Real.log n)) atTop (𝓝 0) := by
  -- Roadmap:
  -- Suppose sin(log n) → 0. Then log n / π = k_n + λ_n with k_n = round(log n / π),
  -- |λ_n| ≤ 1/2, and λ_n → 0 (since sin(π λ) ≈ π λ near 0).
  -- Then k_{n+1} - k_n = (1/π) log(1 + 1/n) - (λ_{n+1} - λ_n) → 0,
  -- so being an integer, eventually k_{n+1} = k_n, hence k_n is eventually constant.
  -- But log n → ∞, contradicting boundedness of k_n.
  sorry

lemma diverges_of_nonpos {α : ℝ} (hα : α ≤ 0) :
    ¬ ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N, term α n) atTop (𝓝 L) := by
  -- If the series converges, the n-th term goes to zero: `term α n → 0`.
  -- For α ≤ 0 and n ≥ 1, |term α n| = |sin(log n)| / n^α ≥ |sin(log n)|
  -- (since n^α ≤ 1), so |term α n| → 0 ⇒ sin(log n) → 0, contradicting
  -- `not_tendsto_sin_log`.
  rintro ⟨L, hL⟩
  -- The general term tends to 0.
  have hterm : Tendsto (fun n : ℕ => term α n) atTop (𝓝 0) := by
    -- ∑_{i<N+1} term i - ∑_{i<N} term i = term N, so term N → L - L = 0.
    have hshift : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), term α n) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have hdiff : Tendsto (fun N : ℕ =>
        (∑ n ∈ range (N + 1), term α n) - (∑ n ∈ range N, term α n)) atTop (𝓝 (L - L)) :=
      hshift.sub hL
    rw [sub_self] at hdiff
    have heq : (fun N : ℕ => term α N) =
        fun N : ℕ => (∑ n ∈ range (N + 1), term α n) - (∑ n ∈ range N, term α n) := by
      funext N; rw [Finset.sum_range_succ]; ring
    rw [heq]; exact hdiff
  -- term α n = (-1)^(n-1) * f α n, |term α n| = |f α n|.
  have habs : Tendsto (fun n : ℕ => |term α n|) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = |0| from (abs_zero).symm]
    exact (continuous_abs.tendsto _).comp hterm
  -- |term α n| = |f α n| since (-1)^k has absolute value 1.
  have habs_eq : ∀ n, |term α n| = |f α n| := by
    intro n
    rw [term, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- Hence |f α n| → 0.
  have hf_to_zero : Tendsto (fun n : ℕ => |f α n|) atTop (𝓝 0) := by
    have : (fun n : ℕ => |f α n|) = (fun n : ℕ => |term α n|) := funext (fun n => (habs_eq n).symm)
    rw [this]; exact habs
  -- Now sin(log n) = f α n * n^α. For α ≤ 0, n^α ≤ 1 on n ≥ 1, so
  -- |sin(log n)| = |f α n| * n^α ≤ |f α n|.
  have hsin_abs_to_zero : Tendsto (fun n : ℕ => |Real.sin (Real.log n)|) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => abs_nonneg _) ?_ hf_to_zero
    intro n
    by_cases hn : 1 ≤ n
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      have hnge : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow_le : (n : ℝ) ^ α ≤ 1 := by
        rw [show (1 : ℝ) = (n : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
        exact Real.rpow_le_rpow_of_exponent_le hnge hα
      have hpow_pos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnpos _
      have heq : |Real.sin (Real.log n)| = |f α n| * (n : ℝ) ^ α := by
        rw [f, abs_div, Real.abs_rpow_of_nonneg hnpos.le, abs_of_pos hnpos,
            div_mul_cancel₀ _ hpow_pos.ne']
      rw [heq]
      calc |f α n| * (n : ℝ) ^ α
          ≤ |f α n| * 1 := mul_le_mul_of_nonneg_left hpow_le (abs_nonneg _)
        _ = |f α n| := mul_one _
    · have : n = 0 := by omega
      subst this
      simp [f]
  have hsin_to_zero : Tendsto (fun n : ℕ => Real.sin (Real.log n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact hsin_abs_to_zero
  exact not_tendsto_sin_log hsin_to_zero

snip end

/-- The IMC 1997 Problem 9 statement: the alternating series
`∑ (-1)^{n-1} sin(log n) / n^α` converges (i.e. its sequence of partial sums
has a limit) if and only if `α > 0`. -/
problem imc1997_p9 (α : ℝ) :
    (∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N, term α n) atTop (𝓝 L))
      ↔ 0 < α := by
  constructor
  · intro hconv
    by_contra hα
    exact diverges_of_nonpos (not_lt.mp hα) hconv
  · intro hα
    exact converges_of_pos hα

end Imc1997P9
