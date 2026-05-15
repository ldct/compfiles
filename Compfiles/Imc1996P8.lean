/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 8 (Day 2, Problem 2)

Let `θ > 0` and `cosh t = (eᵗ + e⁻ᵗ)/2`. Show: if `k ∈ ℕ` with `k ≥ 1`
and `cosh(k·θ)`, `cosh((k+1)·θ)` are both rational, then `cosh θ` is
rational.

## Proof outline (official solution)

**Step 1.** *If `cosh t ∈ ℚ` and `m ∈ ℕ`, then `cosh(m·t) ∈ ℚ`.* By
strong induction on `m`, using

  `cosh((m+1) t) = 2 · cosh t · cosh(m t) - cosh((m-1) t)`

(which is the addition formula `cosh(a+b) + cosh(a-b) = 2 cosh a · cosh b`
applied with `a = m t`, `b = t`).

**Step 2.** For all real `s`, `t`,

  `cosh(s - t) = cosh s · cosh t - sinh s · sinh t`,

and since `s, t ≥ 0` implies `sinh s, sinh t ≥ 0`,

  `sinh s · sinh t = √(cosh² s - 1) · √(cosh² t - 1)`.

Setting `s = (m+1)θ`, `t = m θ`:

  `cosh θ = cosh((m+1)θ) · cosh(m θ) - √(cosh²((m+1)θ) - 1) · √(cosh²(m θ) - 1)`.

Squaring `cosh((m+1)θ) cosh(m θ) - cosh θ = √… · √…` gives

  `(cosh²((m+1)θ) - 1)(cosh²(m θ) - 1)
       = (cosh((m+1)θ) cosh(m θ) - cosh θ)²
       = cosh²((m+1)θ) cosh²(m θ) - 2 cosh((m+1)θ) cosh(m θ) cosh θ
         + cosh² θ`.                                                  (★)

**Step 3.** Set `a = cosh(k θ)`, `b = cosh((k+1)θ)`. Both are rational by
hypothesis. From (★) with `m = k`:

  `(a² - 1)(b² - 1) = a² b² - 2 a b · cosh θ + cosh² θ`.              (3)

**Step 4.** Set `A = cosh((k²-1)θ)`, `B = cosh(k² θ)`. By Step 1
applied to `t = (k+1)θ` (since `cosh((k+1)θ) = b ∈ ℚ`) and `m = k - 1`,
`A ∈ ℚ`. Similarly with `t = k θ`, `m = k`, `B ∈ ℚ`. Now using (★) with
`m = k² - 1` (so `m+1 = k²`):

  `(A² - 1)(B² - 1) = A² B² - 2 A B · cosh θ + cosh² θ`.              (4)

**Step 5.** For `k ≥ 2`, `k² - 1 > k`, hence `A · B > a · b` (since
`cosh` is strictly increasing on `[0, ∞)` and `θ > 0`). Subtracting (3)
from (4) the `cosh² θ` term cancels and the coefficient of `cosh θ` is
`-2(A B - a b) ≠ 0`. Solving:

  `cosh θ = ((A² - 1)(B² - 1) - (a² - 1)(b² - 1) - A² B² + a² b²)
              / (-2 (A B - a b))`,

a quotient of rationals, hence rational.

The case `k = 1` is the hypothesis itself (`cosh((k+1)θ) = cosh(2θ)
= 2 cosh² θ - 1`, so `cosh² θ = (b + 1)/2 ∈ ℚ`, and from `b ≥ 1` and
`cosh θ ≥ 1` we recover `cosh θ = √((b+1)/2)` — but the simpler route is
that `k = 1` is *not* covered by the same argument and requires a small
separate analysis; the official IMC argument actually assumes `k ≥ 2`,
remarking that `k = 1` is handled directly because `cosh θ ∈ ℚ` would
follow from `cosh θ` being a root of a rational quadratic with the other
root being its reciprocal, and `cosh θ ≥ 1` pins it down — but again
this requires extra rationality arguments. In our formalization we
state the result for `k ≥ 1`.)

## Status

Proof complete (no `sorry`). Auxiliary lemmas:
* `cosh_recurrence` — `cosh((n+2) t) = 2 cosh t · cosh((n+1) t) - cosh(n t)`.
* `cosh_nat_rat_of_cosh_rat` — Step 1 of the official solution.
* `key_identity` — `(cosh² s - 1)(cosh² t - 1) = (cosh s · cosh t - cosh(s-t))²`.
-/

namespace Imc1996P8

open Real

snip begin

/-- Recurrence: `cosh((n+2) t) = 2 cosh t · cosh((n+1) t) - cosh(n t)`. -/
lemma cosh_recurrence (n : ℕ) (t : ℝ) :
    Real.cosh (((n : ℝ) + 2) * t)
      = 2 * Real.cosh t * Real.cosh (((n : ℝ) + 1) * t) - Real.cosh ((n : ℝ) * t) := by
  have h1 : ((n : ℝ) + 2) * t = ((n : ℝ) + 1) * t + t := by ring
  have h2 : ((n : ℝ)) * t = ((n : ℝ) + 1) * t - t := by ring
  rw [h1, h2, Real.cosh_add, Real.cosh_sub]
  ring

/--
**Step 1 of the official solution.** If `cosh t` is rational and
`m : ℕ`, then `cosh (m · t)` is rational. Proved by strong induction
using `cosh_recurrence`.
-/
lemma cosh_nat_rat_of_cosh_rat
    {t : ℝ} (ht : ∃ q : ℚ, (q : ℝ) = Real.cosh t) (m : ℕ) :
    ∃ q : ℚ, (q : ℝ) = Real.cosh (m * t) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact ⟨1, by simp⟩
    | 1, _ => obtain ⟨q, hq⟩ := ht; exact ⟨q, by simpa using hq⟩
    | (n + 2), ih =>
      obtain ⟨q₁, hq₁⟩ := ih (n + 1) (by omega)
      obtain ⟨q₀, hq₀⟩ := ih n (by omega)
      obtain ⟨q, hq⟩ := ht
      refine ⟨2 * q * q₁ - q₀, ?_⟩
      have hrec := cosh_recurrence n t
      have e1 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
      have e2 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [e1]
      push_cast
      rw [hrec, ← hq, ← hq₀]
      have hq₁' : Real.cosh ((↑n + 1) * t) = (q₁ : ℝ) := by rw [← e2]; exact hq₁.symm
      rw [hq₁']

/-- The product-to-sum identity used to derive the key equation:
`(cosh² s - 1)(cosh² t - 1) = (cosh s · cosh t - cosh(s - t))²`. -/
lemma key_identity (s t : ℝ) :
    (Real.cosh s ^ 2 - 1) * (Real.cosh t ^ 2 - 1)
      = (Real.cosh s * Real.cosh t - Real.cosh (s - t)) ^ 2 := by
  -- cosh(s - t) = cosh s cosh t - sinh s sinh t, so
  -- cosh s cosh t - cosh(s - t) = sinh s sinh t.
  -- Squaring: (cosh s cosh t - cosh(s - t))² = sinh² s sinh² t
  --                                          = (cosh² s - 1)(cosh² t - 1).
  have hcs := Real.cosh_sub s t
  have hs : Real.sinh s ^ 2 = Real.cosh s ^ 2 - 1 := Real.sinh_sq s
  have ht : Real.sinh t ^ 2 = Real.cosh t ^ 2 - 1 := Real.sinh_sq t
  have heq : Real.cosh s * Real.cosh t - Real.cosh (s - t) = Real.sinh s * Real.sinh t := by
    rw [hcs]; ring
  rw [heq, mul_pow, ← hs, ← ht]

snip end

/--
**IMC 1996, Problem 8 (Day 2, Problem 2).**

If `θ > 0` and `cosh(k θ)`, `cosh((k+1)θ)` are both rational for some
`k ≥ 1`, then `cosh θ` is rational.
-/
problem imc1996_p8
    (θ : ℝ) (hθ : 0 < θ) (k : ℕ) (hk : 1 ≤ k)
    (h_kθ : ∃ q : ℚ, (q : ℝ) = Real.cosh (k * θ))
    (h_k1θ : ∃ q : ℚ, (q : ℝ) = Real.cosh ((k + 1 : ℕ) * θ)) :
    ∃ q : ℚ, (q : ℝ) = Real.cosh θ := by
  -- Case k = 1: hypothesis cosh(k·θ) = cosh θ is rational, done.
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · obtain ⟨q, hq⟩ := h_kθ
    refine ⟨q, ?_⟩; rw [hq, ← hk1]; norm_num
  -- Case k ≥ 2 (here `hk2 : 1 < k`):
  obtain ⟨a, ha⟩ := h_kθ
  obtain ⟨b, hb⟩ := h_k1θ
  -- A := cosh((k - 1)(k + 1) θ) = cosh((k² - 1) θ): rational by Step 1
  -- applied to t = (k+1) θ.
  have hA : ∃ q : ℚ, (q : ℝ) = Real.cosh ((k - 1 : ℕ) * ((k + 1 : ℕ) * θ)) :=
    cosh_nat_rat_of_cosh_rat ⟨b, hb⟩ (k - 1)
  -- B := cosh(k · k θ) = cosh(k² θ): rational by Step 1 applied to t = k θ.
  have hB : ∃ q : ℚ, (q : ℝ) = Real.cosh ((k : ℕ) * ((k : ℕ) * θ)) :=
    cosh_nat_rat_of_cosh_rat ⟨a, ha⟩ k
  -- Rewrite to cleaner form: cosh((k²-1) θ) and cosh(k² θ).
  have hkk_pos : 1 ≤ k * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hAeq : ((k - 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * θ) = ((k * k - 1 : ℕ) : ℝ) * θ := by
    have : (k - 1) * (k + 1) = k * k - 1 := by
      zify [hk, hkk_pos]; ring
    have hAr : ((k - 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * θ)
        = (((k - 1) * (k + 1) : ℕ) : ℝ) * θ := by push_cast; ring
    rw [hAr, this]
  have hBeq : ((k : ℕ) : ℝ) * (((k : ℕ) : ℝ) * θ) = ((k * k : ℕ) : ℝ) * θ := by
    push_cast; ring
  rw [hAeq] at hA
  rw [hBeq] at hB
  obtain ⟨A, hA⟩ := hA
  obtain ⟨B, hB⟩ := hB
  -- Apply key_identity at (s, t) = ((k+1) θ, k θ).
  have key1 := key_identity (((k + 1 : ℕ) : ℝ) * θ) ((k : ℝ) * θ)
  have hsub1 : ((k + 1 : ℕ) : ℝ) * θ - (k : ℝ) * θ = θ := by push_cast; ring
  rw [hsub1] at key1
  -- Apply key_identity at (s, t) = (k² θ, (k²-1) θ).
  have key2 := key_identity (((k * k : ℕ) : ℝ) * θ) (((k * k - 1 : ℕ) : ℝ) * θ)
  have hsub2 : ((k * k : ℕ) : ℝ) * θ - ((k * k - 1 : ℕ) : ℝ) * θ = θ := by
    push_cast [Nat.cast_sub hkk_pos]; ring
  rw [hsub2] at key2
  -- Substitute rational values.
  have ha' : (a : ℝ) = Real.cosh ((k : ℝ) * θ) := ha
  rw [← ha', ← hb] at key1
  rw [← hA, ← hB] at key2
  set c : ℝ := Real.cosh θ with hc_def
  -- key1: (↑b ^ 2 - 1) * (↑a ^ 2 - 1) = (↑b * ↑a - c) ^ 2
  -- key2: (↑B ^ 2 - 1) * (↑A ^ 2 - 1) = (↑B * ↑A - c) ^ 2
  -- Linear equation in c after subtracting:
  have hlin : 2 * ((A : ℝ) * B - a * b) * c = (A : ℝ)^2 + B^2 - a^2 - b^2 := by
    nlinarith [key1, key2]
  -- Strict monotonicity: cosh is strictly increasing on [0, ∞).
  have hcosh_mono : StrictMonoOn Real.cosh (Set.Ici 0) := Real.cosh_strictMonoOn
  -- Bounds: k ≥ 2.
  have hk2 : 2 ≤ k := hk2
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hθpos : 0 < θ := hθ
  have hkθ_pos : (0 : ℝ) ≤ k * θ := mul_nonneg hk_pos.le hθpos.le
  have hk1θ_pos : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * θ := by positivity
  -- (k² - 1) ≥ k+1 > k, so (k²-1)θ > kθ.
  have hkk1_gt_k : (k : ℝ) < ((k * k - 1 : ℕ) : ℝ) := by
    have hkk_gt : k + 1 < k * k := by nlinarith
    have hkk_lt : k < k * k - 1 := by
      have : 1 ≤ k * k := hkk_pos
      omega
    exact_mod_cast hkk_lt
  have hkkθ_gt : (k : ℝ) * θ < ((k * k - 1 : ℕ) : ℝ) * θ := by
    have := mul_lt_mul_of_pos_right hkk1_gt_k hθpos
    convert this using 1
  have hkk_gt_k1 : ((k + 1 : ℕ) : ℝ) < ((k * k : ℕ) : ℝ) := by
    push_cast; nlinarith
  have hkk2θ_gt : ((k + 1 : ℕ) : ℝ) * θ < ((k * k : ℕ) : ℝ) * θ := by
    exact mul_lt_mul_of_pos_right hkk_gt_k1 hθpos
  have hA_gt_a : (a : ℝ) < A := by
    rw [ha, hA]
    apply hcosh_mono hkθ_pos _ hkkθ_gt
    apply mul_nonneg _ hθpos.le
    exact_mod_cast (Nat.zero_le _)
  have hB_gt_b : (b : ℝ) < B := by
    rw [hb, hB]
    apply hcosh_mono hk1θ_pos _ hkk2θ_gt
    apply mul_nonneg _ hθpos.le
    exact_mod_cast (Nat.zero_le _)
  have ha_ge_1 : 1 ≤ (a : ℝ) := by rw [ha]; exact Real.one_le_cosh _
  have hb_ge_1 : 1 ≤ (b : ℝ) := by rw [hb]; exact Real.one_le_cosh _
  have hA_ge_1 : 1 ≤ (A : ℝ) := le_of_lt (lt_of_le_of_lt ha_ge_1 hA_gt_a)
  -- AB > ab using A > a ≥ 1, B > b ≥ 1.
  have hAB_gt_ab : (a : ℝ) * b < A * B := by
    have h1 : (a : ℝ) * b < A * b := by
      have hbpos : 0 < (b : ℝ) := by linarith
      exact mul_lt_mul_of_pos_right hA_gt_a hbpos
    have h2 : (A : ℝ) * b ≤ A * B := by
      have hApos : 0 < (A : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left hB_gt_b.le hApos.le
    linarith
  have hcoeff_pos : (0 : ℝ) < 2 * ((A : ℝ) * B - a * b) := by linarith
  have hcoeff_ne : 2 * ((A : ℝ) * B - a * b) ≠ 0 := ne_of_gt hcoeff_pos
  refine ⟨(A^2 + B^2 - a^2 - b^2) / (2 * (A * B - a * b)), ?_⟩
  have hcval : c = ((A : ℝ)^2 + B^2 - a^2 - b^2) / (2 * (A * B - a * b)) := by
    rw [eq_div_iff hcoeff_ne]
    linarith [hlin]
  rw [hcval]
  push_cast
  ring

end Imc1996P8
