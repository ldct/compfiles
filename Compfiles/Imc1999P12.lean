/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 1999, Problem 12 (Day 2, Problem 6)

Let `A ⊂ ℤ/nℤ` be a subset with `|A| ≤ (1/100) · ln n`. For each
`r ∈ ℤ/nℤ` define
  `f(r) = ∑_{s ∈ A} exp(2πi · s · r / n)`.
Prove that there exists `r ≠ 0` in `ℤ/nℤ` with `|f(r)| ≥ |A| / 2`.

## Solution sketch (official, via arc-pigeonhole)

Let `A = {a₁, …, a_k}` and consider the `k`-tuples
  `v_t = (e^(2πi a₁ t / n), …, e^(2πi a_k t / n)) ∈ (S¹)^k`,
for `t = 0, 1, …, n − 1`. Partition `S¹` into 6 equal arcs (each of arc
length `π/3`). This induces a partition of `(S¹)^k` into `6^k`
classes. Since `k ≤ (ln n) / 100`, we have `6^k ≤ e^(k · ln 6) ≤
e^((ln 6)/100 · ln n) ≪ n`, so by the pigeonhole principle there exist
`0 ≤ t₁ < t₂ ≤ n − 1` with `v_{t₁}` and `v_{t₂}` in the same class.
Let `r = t₂ − t₁`. For each coordinate `j`, the points
`e^(2πi a_j t₁ / n)` and `e^(2πi a_j t₂ / n)` lie in a common arc of
length `π/3`, so the angle between them is at most `π/3`, i.e.,
  `Re e^(2πi a_j r / n) = cos(2π a_j r / n) ≥ cos(π/3) = 1/2`.
Hence `|f(r)| ≥ Re f(r) ≥ k · (1/2) = |A|/2`, and `r ≠ 0` because
`t₁ < t₂` and we are in `ℤ/nℤ` with `t₁, t₂ ∈ {0, …, n−1}`.

## Status of this formalization

Statement: complete. Proof: `sorry` placeholder. The core ingredients
are routine but combine real-analytic, combinatorial, and complex-arithmetic
reasoning, all of which are available in Mathlib but require careful
plumbing. See the TODO inside the proof for the step-by-step plan.
-/

namespace Imc1999P12

open scoped BigOperators
open Finset Complex

/-- The "Fourier coefficient" of a finite subset `A` of `ZMod n`,
evaluated at `r ∈ ZMod n`. We use `ZMod.val` to lift to `ℕ` and then
form the standard root-of-unity exponential. -/
noncomputable def fourier {n : ℕ} (A : Finset (ZMod n)) (r : ZMod n) : ℂ :=
  ∑ s ∈ A, Complex.exp (2 * Real.pi * Complex.I * (s.val : ℂ) * (r.val : ℂ) / (n : ℂ))

/-- **IMC 1999 Problem 12.** For any `n ≥ 1` and any subset
`A ⊂ ℤ/nℤ` with `|A| ≤ (ln n) / 100`, there exists `r ≠ 0` in
`ℤ/nℤ` such that the Fourier-style exponential sum
`f(r) = ∑_{s ∈ A} e^(2πi s r / n)` has magnitude at least `|A| / 2`. -/
problem imc1999_p12 (n : ℕ) (hn : 2 ≤ n)
    (A : Finset (ZMod n))
    (hA : (A.card : ℝ) ≤ Real.log n / 100) :
    ∃ r : ZMod n, r ≠ 0 ∧ (A.card : ℝ) / 2 ≤ ‖fourier A r‖ := by
  -- TODO: Full proof.
  --
  -- Strategy (official solution, "arc-pigeonhole"):
  --
  -- (1) **Setup.** Let `k := A.card`. Enumerate `A = {a₁, …, a_k}` (as
  --     elements of `ZMod n`, lifted via `ZMod.val` to `Fin n`).
  --     Define, for each `t : Fin n`, the `k`-tuple
  --       `v t : Fin k → S¹`,
  --       `v t j = exp(2πi · (a_j : ℕ) · (t : ℕ) / n)`.
  --     (We can equivalently view `v t` as a function in
  --     `Fin k → ℝ / 2π` via the argument map.)
  --
  -- (2) **Arc decomposition.** Partition the circle `S¹` (or
  --     `ℝ / 2π`) into 6 equal half-open arcs `I_0, …, I_5` of arc
  --     length `2π / 6 = π / 3`:
  --       `I_m = { z : S¹ | (m π / 3) ≤ arg z < ((m+1) π / 3) }`,
  --     using the `arg : ℂ → ℝ` (taking values in `(-π, π]`) and a
  --     suitable shift, or alternatively work directly with
  --     `Fin 6`-classifying functions on `[0, 2π)`. The exact bookkeeping
  --     uses `Real.angle` or `(t : ℝ) % (2π)`.
  --
  -- (3) **Color and pigeonhole.** Define
  --       `c : Fin n → (Fin k → Fin 6)`,
  --       `c t j = (the arc index of `v t j`)`.
  --     The codomain has cardinality `6^k`.
  --
  --     **Key estimate.** From the hypothesis `(k : ℝ) ≤ Real.log n / 100`,
  --     we deduce `(6 : ℝ)^k ≤ Real.exp ((Real.log 6) * Real.log n / 100)`.
  --     Since `Real.log 6 < 2 < 100`, we get `(6 : ℝ)^k < n` (at least
  --     for `n ≥ 2`; the edge case `n = 1` is trivial as `A = ∅`).
  --     Concretely, `6^k = exp(k · log 6) ≤ exp(log n · log 6 / 100) =
  --     n^(log 6 / 100)`, and `log 6 / 100 < 1`, so `6^k ≤ n^(log 6 / 100) < n`.
  --
  --     With `6^k < n`, pigeonhole (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
  --     or `Fintype.exists_ne_map_eq_of_card_lt`) yields distinct
  --     `t₁ ≠ t₂ ∈ Fin n` with `c t₁ = c t₂`. WLOG `t₁ < t₂`.
  --
  -- (4) **Same arc => small angle => cosine bound.** For each `j`,
  --     `v t₁ j` and `v t₂ j` lie in the same arc `I_{c t₁ j}`, hence
  --     the angles differ by at most `π / 3`. Therefore
  --       `arg ((v t₂ j) / (v t₁ j))  ∈ (−π/3, π/3)`
  --     (mod `2π`), which means
  --       `Re ((v t₂ j) · conj (v t₁ j)) = cos(angle) ≥ cos(π/3) = 1/2`.
  --     Setting `r := t₂ - t₁` (in `ZMod n`), and using
  --     `(v t₂ j) · conj (v t₁ j) = exp(2πi · a_j · (t₂ - t₁) / n) =
  --     exp(2πi · a_j · r / n)` (after care with the `ZMod`-vs-`ℕ` lift),
  --     we obtain
  --       `Re exp(2πi · a_j · r / n) ≥ 1/2`,    for each `j ∈ Fin k`.
  --
  -- (5) **Sum the real parts.** Summing over `j`,
  --       `Re (fourier A r) = ∑_j Re exp(2πi · a_j · r / n) ≥ k / 2`.
  --     Since `‖z‖ ≥ Re z` for all `z ∈ ℂ`, this gives
  --       `‖fourier A r‖ ≥ k / 2 = |A| / 2`,    as required.
  --
  -- (6) **Nonzero.** `r = t₂ - t₁` in `ZMod n` is nonzero because
  --     `t₁, t₂ ∈ Fin n` are distinct, so `t₁ ≠ t₂` implies their
  --     `ZMod n`-images differ, i.e., `r ≠ 0`.
  --
  -- **Mathlib ingredients.**
  --
  --   * `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` for the
  --     pigeonhole step.
  --   * `Real.log_lt_log_iff`, `Real.exp_log`, `Real.log_pow`,
  --     `Real.rpow_lt_rpow_iff_left` for the key estimate
  --     `6^k < n`.
  --   * `Complex.exp_add`, `Complex.norm_exp`, `Complex.re_add_im`,
  --     `Complex.re_sum`, `Complex.cos_le_one`, the fact
  --     `Complex.exp (I · θ) = cos θ + I sin θ`, etc., for the
  --     real-part computation.
  --   * `Real.cos_pi_div_three : Real.cos (π / 3) = 1 / 2`.
  --   * Basic `Complex.norm_re_le_norm`/`Complex.re_le_norm` for
  --     `Re z ≤ ‖z‖`.
  --
  -- The proof is conceptually short but its formalization in Lean is
  -- substantial because it weaves together (a) careful index/coercion
  -- bookkeeping among `ZMod n`, `Fin n`, and `ℕ`, (b) a circle-arc
  -- partition with explicit angle bounds, (c) a real-analytic estimate
  -- comparing `6^k` to `n` via `Real.log`, and (d) the standard
  -- `Re ≤ ‖·‖` bound on complex numbers.
  sorry

end Imc1999P12
