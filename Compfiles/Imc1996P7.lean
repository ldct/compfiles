/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1996, Problem 7 (Day 2, Problem 1)

Let `f : [0,1] → [0,1]` be continuous. For `x₀ ∈ [0,1]`, define the orbit
sequence `x : ℕ → [0,1]` by `x 0 = x₀` and `x (n+1) = f (x n)`. Prove that
the iterates `x n` converge if and only if `x (n+1) - x n → 0`.

## Proof outline (official solution)

(⇒) "Only if": If `x n → L`, then `x (n+1) → L` as well (the shifted
sequence has the same limit), so `x (n+1) - x n → L - L = 0`. (Continuity
of `f` is not needed for this direction.)

(⇐) "If": Assume `x (n+1) - x n → 0` and suppose toward contradiction that
`(x n)` does not converge. Since `(x n)` is bounded (in `[0,1]`), by
Bolzano–Weierstrass it has at least one cluster point. If it had only one
cluster point, then by boundedness it would converge to that point. So
there exist two cluster points `K < L` in `[0,1]`.

Sub-claim: For every `y ∈ (K, L)`, the sequence `(x n)` enters every
neighborhood of `y` infinitely often. Indeed, fix `y ∈ (K, L)` and
`η > 0` with `η < min(y - K, L - y)`. For `n` large enough,
`|x (n+1) - x n| < η`. There exist `n₁ < n₂` arbitrarily large with
`x n₁ < K + η < y` and `x n₂ > L - η > y`. Walking from index `n₁` to
`n₂` with step size `< η`, the sequence must enter `(y - η, y + η)` at
some intermediate step.

Now consider two cases:

* Case A: there exists `y ∈ (K, L)` with `f y ≠ y`. Set
  `ε = |f y - y| / 2 > 0`. By continuity of `f` at `y`, there is `δ > 0`
  with `|f y' - y'| > ε` for all `y' ∈ (y - δ, y + δ)`. By the sub-claim,
  `x n` enters `(y - δ, y + δ)` infinitely often. But for `n` large
  enough, `|x (n+1) - x n| = |f (x n) - x n| < ε`, so `x n ∉ (y - δ, y + δ)`
  eventually — contradiction.

* Case B: `f y = y` for every `y ∈ (K, L)`. By the sub-claim with
  `y = (K + L)/2` and `η = (L - K)/4`, there exists `N` with
  `x N ∈ (y - η, y + η) ⊂ (K, L)`. Then by induction `x m = x N` for
  all `m ≥ N` (since `f` fixes every point of `(K, L)`). Hence `(x m)`
  is eventually constant, contradicting the existence of two distinct
  cluster points `K ≠ L`.

In both cases we get a contradiction, so `(x n)` converges.

## Status

The forward direction (`Tendsto → x_{n+1} - x_n → 0`) is proved
completely. The reverse direction is left as `sorry` with the detailed
outline above.
-/

namespace Imc1996P7

open Filter Topology

/-- The orbit sequence `x n` defined by `x 0 = x₀` and `x (n+1) = f (x n)`. -/
def orbit (f : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => f (orbit f x₀ n)

@[simp] lemma orbit_zero (f : ℝ → ℝ) (x₀ : ℝ) : orbit f x₀ 0 = x₀ := rfl

@[simp] lemma orbit_succ (f : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    orbit f x₀ (n + 1) = f (orbit f x₀ n) := rfl

snip begin

/-- The orbit stays in `[0,1]` if `f` maps `[0,1]` to `[0,1]` and `x₀ ∈ [0,1]`. -/
lemma orbit_mem_Icc {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc (0:ℝ) 1, f x ∈ Set.Icc (0:ℝ) 1)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    orbit f x₀ n ∈ Set.Icc (0:ℝ) 1 := by
  induction n with
  | zero => simpa using hx₀
  | succ n ih => simpa [orbit_succ] using hf _ ih

snip end

/--
**IMC 1996, Problem 7 (Day 2, Problem 1).**

For a continuous function `f : [0,1] → [0,1]`, the orbit sequence
`x_{n+1} = f(x_n)` converges if and only if `x_{n+1} - x_n → 0`.
-/
problem imc1996_p7
    (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_maps : ∀ x ∈ Set.Icc (0:ℝ) 1, f x ∈ Set.Icc (0:ℝ) 1)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc (0:ℝ) 1) :
    (∃ L, Tendsto (orbit f x₀) atTop (𝓝 L)) ↔
      Tendsto (fun n => orbit f x₀ (n+1) - orbit f x₀ n) atTop (𝓝 0) := by
  constructor
  · -- (⇒) "Only if": if x_n → L, then x_{n+1} - x_n → L - L = 0.
    rintro ⟨L, hL⟩
    have h_shift : Tendsto (fun n => orbit f x₀ (n + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have := h_shift.sub hL
    simpa using this
  · -- (⇐) "If": if x_{n+1} - x_n → 0, then x_n converges.
    intro hdiff
    -- TODO: full formalization. Detailed outline:
    --
    -- Step 1. The orbit is bounded: `orbit f x₀ n ∈ [0,1]` for all `n`
    --   (by `orbit_mem_Icc` using `hf_maps` and `hx₀`).
    --
    -- Step 2. Suppose for contradiction the orbit does not converge.
    --   By Bolzano–Weierstrass on `[0,1]` (which is compact), the orbit has
    --   a cluster point. If the orbit had a unique cluster point `c`, the
    --   orbit would converge to `c` (a bounded sequence in a metric space
    --   with a unique cluster point converges to that point). So there
    --   exist two distinct cluster points; call them `K < L` (after
    --   swapping if necessary).
    --
    -- Step 3. Sub-claim ("intermediate value for sequences"): for every
    --   `y ∈ (K, L)` and every `η > 0` with `η < min(y - K, L - y)`,
    --   there are infinitely many `n` with `x n ∈ (y - η, y + η)`.
    --
    --   Proof: For `n ≥ N` we have `|x (n+1) - x n| < η` (from `hdiff`).
    --   `K` cluster point ⇒ ∃ `n₁ ≥ N` with `|x n₁ - K| < η`, so
    --   `x n₁ < K + η < y`. `L` cluster point ⇒ ∃ `n₂ > n₁` with
    --   `|x n₂ - L| < η`, so `x n₂ > L - η > y`. The function `n ↦ x n`
    --   on `{n₁, …, n₂}` starts below `y` and ends above `y` with
    --   consecutive jumps of size `< η`; hence at some `n* ∈ [n₁, n₂]`,
    --   `|x n* - y| < η`. Iterating gives infinitely many such `n`.
    --
    -- Step 4. Case A: ∃ `y ∈ (K, L)` with `f y ≠ y`.
    --   Set `ε = |f y - y| / 2 > 0`.
    --   By continuity of `f` at `y`, ∃ `δ ∈ (0, min(y - K, L - y))` with
    --   `|f y' - y'| > ε` for `y' ∈ (y - δ, y + δ) ∩ [0,1]`.
    --   By Step 3 with this `δ` and `y`, there are infinitely many `n`
    --   with `x n ∈ (y - δ, y + δ)`, hence `|x (n+1) - x n| > ε`.
    --   But by `hdiff`, eventually `|x (n+1) - x n| < ε`. Contradiction.
    --
    -- Step 5. Case B: `f y = y` for every `y ∈ (K, L)`.
    --   Take `y = (K + L) / 2` and `η = (L - K) / 4`.
    --   By Step 3, ∃ `N` with `x N ∈ (y - η, y + η) ⊂ (K, L)`.
    --   By induction on `m ≥ N`: `x m = x N`. (Base: trivial. Step: if
    --   `x m = x N ∈ (K, L)`, then `f (x m) = x m`, so
    --   `x (m+1) = f (x m) = x m = x N`.)
    --   Hence `x m → x N`, contradicting `x m` having two distinct
    --   cluster points `K ≠ L`.
    --
    -- Conclude: `(x n)` converges.
    sorry

end Imc1996P7
