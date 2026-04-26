/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 3
(IMC 2001, Day 1, Problem 3)

Find `lim_{t → 1⁻} (1 - t) · Σ_{n=1}^∞ t^n / (1 + t^n)`.

Answer: `log 2`.

## Solution sketch

Substitute `h = -log t`, so `h → 0⁺` as `t → 1⁻`. Then
`(1 - t) / (-log t) → 1` and `t^n = e^{-nh}`, giving
`(1 - t) · Σ t^n / (1 + t^n) = ((1 - t)/(-log t)) · h · Σ 1/(1 + e^{nh})`.
The latter is a right-endpoint Riemann sum for `∫_0^∞ dx/(1 + e^x) = log 2`.
-/

namespace Imc2001P3

open Filter Topology Real

/-- For `t ∈ (0, 1)`, the series `t^n / (1 + t^n)` is summable over `n ≥ 1`.
We use `Finset.range` starting from `0`, where the `n = 0` term is `1/2`, and state
the problem as the limit of the sum from `n = 1` to `∞`. -/
noncomputable def S (t : ℝ) : ℝ := ∑' n : ℕ, t ^ (n + 1) / (1 + t ^ (n + 1))

noncomputable determine answer : ℝ := Real.log 2

snip begin

/-- `t^n / (1 + t^n)` is bounded by `t^n` when `t ∈ [0, 1]`. -/
lemma term_le_pow {t : ℝ} (ht0 : 0 ≤ t) (n : ℕ) :
    t ^ n / (1 + t ^ n) ≤ t ^ n := by
  have htn_nn : 0 ≤ t ^ n := pow_nonneg ht0 n
  have h1_pos : (0 : ℝ) < 1 + t ^ n := by linarith
  rw [div_le_iff₀ h1_pos]
  nlinarith

/-- `Σ t^(n+1)` is summable for `t ∈ [0, 1)`. -/
lemma summable_pow_succ {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => t ^ (n + 1)) := by
  have hsg : Summable (fun n : ℕ => t ^ n) := summable_geometric_of_lt_one ht0 ht1
  have hinj : Function.Injective (fun n : ℕ => n + 1) := fun a b h => by
    have : a + 1 = b + 1 := h
    omega
  exact hsg.comp_injective hinj

/-- Summability of `t^(n+1) / (1 + t^(n+1))` for `t ∈ [0, 1)`. -/
lemma summable_terms {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => t ^ (n + 1) / (1 + t ^ (n + 1))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (summable_pow_succ ht0 ht1)
  · intro n
    have htn_nn : 0 ≤ t ^ (n + 1) := pow_nonneg ht0 _
    have h1_pos : (0 : ℝ) < 1 + t ^ (n + 1) := by linarith
    exact div_nonneg htn_nn h1_pos.le
  · intro n
    exact term_le_pow ht0 (n + 1)

snip end

problem imc2001_p3 :
    Tendsto (fun t : ℝ => (1 - t) * S t) (𝓝[<] 1) (𝓝 answer) := by
  -- TODO: Proof outline:
  --   Substitute `h = -log t`, so `h → 0⁺` as `t → 1⁻`.
  --   Write `(1 - t) · S t = ((1 - t) / (-log t)) · h · Σ_{n ≥ 1} 1/(1 + e^{nh})`.
  --   The factor `(1 - t)/(-log t) → 1` by the standard limit.
  --   The remaining factor `h · Σ_{n ≥ 1} 1/(1 + e^{nh})` is a right-endpoint
  --   Riemann sum for `∫_0^∞ dx/(1 + e^x)`. Since `1/(1 + e^x)` is strictly
  --   decreasing on `[0, ∞)`, monotonicity gives the needed bounds:
  --     `h · Σ_{n=1}^N 1/(1 + e^{nh}) ≤ ∫_0^{Nh} dx/(1+e^x)
  --                                 ≤ h · Σ_{n=0}^{N-1} 1/(1 + e^{nh})`.
  --   Letting `N → ∞` first (with fixed small `h`) gives the Riemann-sum limit,
  --   then `h → 0⁺` converts it to the integral.
  --   The integral `∫_0^∞ dx/(1 + e^x) = log 2` is obtained by the substitution
  --   `u = 1/(1 + e^x)` or directly via the antiderivative
  --   `-log(1 + e^{-x}) + x` (equivalently, `log(e^x/(1+e^x))`).
  sorry

end Imc2001P3
