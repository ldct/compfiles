/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2008, Problem 12
(IMC 2008, Day 2, Problem 6)

Let `H` be an infinite-dimensional real Hilbert space and let `d > 0`.
Let `S ⊂ H` be a set such that any two distinct points of `S` are at
distance exactly `d`. Show that there exists a point `y ∈ H` such that
the family `{(√2 / d) • (x - y) : x ∈ S}` is an orthonormal family in `H`.

## Proof sketch

Fix any base point `x₀ ∈ S` (if `S` is empty the conclusion is vacuous).
The model example: take an orthonormal family `{eᵢ}` in `H`; the points
`{(d / √2) eᵢ}` are pairwise at distance `d`. So we expect any equidistant
set to be a translate of such a configuration.

**Inner-product computations.** For pairwise-equidistant points, the
parallelogram identity gives, for distinct `x₁, x₂, x₃, x₄ ∈ S`,

  `⟪x₂ - x₁, x₂ - x₁⟫ = d²`,
  `⟪x₂ - x₁, x₃ - x₁⟫ = d² / 2`,
  `⟪x₂ - x₁, x₄ - x₃⟫ = 0`.

More generally, for integer (then rational, then real) coefficients summing
to zero, inner products of linear combinations of points of `S` match those
of the canonical configuration.

**Finite case.** If `S = {x₁, …, xₙ}`, set `x̄ = (1/n) Σᵢ xᵢ`. Pick a unit
vector `z ∈ H` orthogonal to `span{xᵢ - x̄}` (it exists since `H` is
infinite-dimensional). Set `y = x̄ + λ z` with `λ = d / √(2n)`. The above
identities give `⟪xᵢ - y, xⱼ - y⟫ = -d²/(2n) + λ²` (for `i ≠ j`) and
`‖xᵢ - y‖² = d²(n-1)/n + λ²`. Substituting `λ² = d²/(2n)` gives
inner products `0` and norms `d/√2`.

**Infinite case.** Pick a countable sequence `T = {x₁, x₂, …} ⊆ S`. Define
`yₙ = (1/n) (x₁ + ⋯ + xₙ)`. Using the canonical inner products,

  `‖yₘ - yₙ‖² = (d²/2)(1/n − 1/m)  → 0`,

so `yₙ` is Cauchy; let `y = lim yₙ`. One checks that
`‖xₙ − y‖ = d / √2` and `⟪xₙ − y, xₚ − y⟫ = 0` for `n ≠ p`.

For `x', x'' ∈ S \ T`, applying the construction to `T ∪ {x', x''}`
yields the same limit `y`, and the orthonormality of the rescaled family
extends to all of `S`.

This file gives the formal statement; the full Lean 4 proof is left as
a `sorry` (the construction requires choosing a countable subset of `S`,
verifying Cauchy-ness with explicit inner-product identities, and
extending orthonormality from a countable sub-family to all of `S`).
-/

namespace Imc2008P12

open scoped RealInnerProductSpace

snip begin

/-!
The mathematical content of the problem hinges on the following identity,
which we record (without proof) for future use. From pairwise distance
constraints `‖x - y‖ = d` for distinct `x, y ∈ S`, the polarization identity
yields

  `⟪xᵢ - x₁, xⱼ - x₁⟫ = d² / 2`   (for `i, j ≥ 2`, `i ≠ j`),
  `‖xᵢ - x₁‖² = d²`                (for `i ≥ 2`).

These determine all pairwise inner products of differences of points of `S`
once a base point is fixed.
-/

snip end

problem imc2008_p12
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (hInfDim : ¬ FiniteDimensional ℝ H)
    (d : ℝ) (hd : 0 < d) (S : Set H)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ‖x - y‖ = d) :
    ∃ y : H, Orthonormal ℝ (fun x : S => (Real.sqrt 2 / d) • ((x : H) - y)) := by
  -- TODO: formalize the analytic argument outlined in the docstring:
  --
  -- 1. If `S` is empty, take any `y` (the family is vacuous and trivially
  --    orthonormal).
  -- 2. Otherwise fix `x₀ ∈ S` and use polarization to compute
  --    `⟪x - x₀, x' - x₀⟫ = d²/2` for distinct `x, x' ∈ S \ {x₀}`,
  --    and `‖x - x₀‖² = d²` for `x ∈ S \ {x₀}`.
  -- 3. Pick a countable subset `T = {t₀, t₁, t₂, …} ⊆ S` (using axiom of
  --    choice); set `yₙ = (1 / (n+1)) • Σ_{k ≤ n} tₖ`.
  --    Show `(yₙ)` is Cauchy in `H`.
  -- 4. Let `y = lim yₙ`. Verify that for each `tₙ`,
  --      `‖tₙ - y‖ = d / √2` and ⟪tₙ - y, tₚ - y⟫ = 0` for `n ≠ p`.
  -- 5. For any other point `x ∈ S \ T`, repeat the construction with
  --    `T ∪ {x}`: the limit is still `y`, so `‖x - y‖ = d / √2` and
  --    `⟪x - y, t - y⟫ = 0` for all `t ∈ T`. By an analogous argument with
  --    pairs `(x, x') ∈ (S \ T)²`, the inner products vanish there too.
  -- 6. Conclude that the rescaled family is orthonormal.
  sorry


end Imc2008P12
