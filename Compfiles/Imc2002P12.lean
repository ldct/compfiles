/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Function

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 12
(IMC 2002, Day 2, Problem 6)

Let `f : ℝⁿ → ℝ` be a convex, differentiable function whose gradient is
`L`-Lipschitz, i.e. `‖∇f(x) - ∇f(y)‖ ≤ L · ‖x - y‖` for all `x, y`. Prove
that
  `‖∇f(x₁) - ∇f(x₂)‖² ≤ L · ⟨∇f(x₁) - ∇f(x₂), x₁ - x₂⟩`.

This inequality is known as the **co-coercivity** of the gradient (the
Baillon-Haddad theorem in finite dimensions).

## Solution outline

Replace `f` by `g(x) = f(x) - f(x₁) - ⟨∇f(x₁), x - x₁⟩`. Then `g` is convex,
differentiable, with the same `L`-Lipschitz gradient (∇g(x) = ∇f(x) - ∇f(x₁)),
and `g(x₁) = 0`, `∇g(x₁) = 0`, so `x₁` is the global minimum of `g`.

The **smoothness lemma** for `L`-Lipschitz gradients gives, for any `y, z`,
  `g(z) ≤ g(y) + ⟨∇g(y), z - y⟩ + (L/2)·‖z - y‖²`.

Apply this with `y = x₂`, `z = y₀ := x₂ - (1/L)·∇g(x₂)`, getting
  `g(y₀) ≤ g(x₂) + ⟨∇g(x₂), -1/L·∇g(x₂)⟩ + (L/2)·(1/L²)·‖∇g(x₂)‖²
         = g(x₂) - (1/(2L))·‖∇g(x₂)‖²`.

Since `g(y₀) ≥ g(x₁) = 0`, we get
  `g(x₂) ≥ (1/(2L))·‖∇g(x₂)‖²`.

Substituting back the definition of `g` yields
  `‖∇f(x₂) - ∇f(x₁)‖² ≤ 2L·(f(x₂) - f(x₁) + ⟨∇f(x₁), x₁ - x₂⟩).`  (†)

Swapping `x₁ ↔ x₂` gives
  `‖∇f(x₁) - ∇f(x₂)‖² ≤ 2L·(f(x₁) - f(x₂) + ⟨∇f(x₂), x₂ - x₁⟩).`  (‡)

Averaging (†) and (‡) yields the claim.

The deep ingredient is the smoothness lemma which depends on the fundamental
theorem of calculus along line segments. We isolate it as `smoothness_ineq`
below.
-/

namespace Imc2002P12

open scoped Gradient
open Real

variable {n : ℕ}

/-- Local notation: `E n` is `n`-dimensional Euclidean space. -/
local notation "E " n => EuclideanSpace ℝ (Fin n)

snip begin

/-- The smoothness lemma (descent lemma): for a differentiable convex
function `f` with `L`-Lipschitz gradient on a (real) inner product space,
`f(z) ≤ f(y) + ⟨∇f(y), z - y⟩ + (L/2)·‖z - y‖²`.

This is a standard calculus result (FTC along the segment from `y` to `z`,
combined with the Lipschitz bound on the gradient). It does *not* require
convexity.

We state it for `EuclideanSpace ℝ (Fin n)` to keep dependencies light.
-/
lemma smoothness_ineq {n : ℕ} {f : (E n) → ℝ} {f' : (E n) → (E n)}
    (hf : ∀ x, HasGradientAt f (f' x) x) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖) (y z : (E n)) :
    f z ≤ f y + inner ℝ (f' y) (z - y) + (L / 2) * ‖z - y‖ ^ 2 := by
  -- Standard analysis result; see, e.g., Nesterov, "Introductory Lectures on
  -- Convex Optimization", Lemma 1.2.3.
  -- Proof: integrate ⟨∇f(y + t(z-y)), z - y⟩ from t = 0 to 1 to get
  -- f(z) - f(y), then bound the difference using Lipschitz continuity of ∇f.
  sorry

/-- From the smoothness lemma applied at `y = x₂`, `z = x₂ - L⁻¹ • ∇g(x₂)`
where `g(x) = f(x) - f(x₁) - ⟨∇f(x₁), x - x₁⟩`. The minimum of `g` over all
points (which equals `g(x₁) = 0` by convexity and `∇g(x₁) = 0`) lower-bounds
`g(x₂) - (1/(2L))·‖∇g(x₂)‖²`. -/
lemma key_ineq {n : ℕ} {f : (E n) → ℝ} {f' : (E n) → (E n)}
    (hconv : ConvexOn ℝ Set.univ f)
    (hf : ∀ x, HasGradientAt f (f' x) x)
    (L : ℝ) (hL : 0 < L)
    (hlip : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖) (x₁ x₂ : (E n)) :
    ‖f' x₂ - f' x₁‖ ^ 2 ≤
      2 * L * (f x₂ - f x₁ + inner ℝ (f' x₁) (x₁ - x₂)) := by
  -- Set g(x) = f(x) - f(x₁) - ⟨∇f(x₁), x - x₁⟩.
  -- ∇g(x) = ∇f(x) - ∇f(x₁), so ∇g(x₁) = 0 and g has the same Lipschitz constant L.
  -- Convexity of g + ∇g(x₁) = 0 implies x₁ is a global minimum: g(y) ≥ g(x₁) = 0
  -- for all y. Apply smoothness_ineq with y = x₂, z = x₂ - L⁻¹ • ∇g(x₂):
  --   g(z) ≤ g(x₂) + ⟨∇g(x₂), -L⁻¹ • ∇g(x₂)⟩ + (L/2) · L⁻² · ‖∇g(x₂)‖²
  --        = g(x₂) - (1/(2L)) · ‖∇g(x₂)‖².
  -- Since 0 ≤ g(z), this gives g(x₂) ≥ (1/(2L)) · ‖∇g(x₂)‖², i.e.,
  --   ‖∇g(x₂)‖² ≤ 2L · g(x₂)
  --   ‖∇f(x₂) - ∇f(x₁)‖² ≤ 2L · (f(x₂) - f(x₁) - ⟨∇f(x₁), x₂ - x₁⟩)
  -- Note ⟨∇f(x₁), x₁ - x₂⟩ = -⟨∇f(x₁), x₂ - x₁⟩.
  sorry

snip end

problem imc2002_p12 (f : (E n) → ℝ) (f' : (E n) → (E n))
    (hconv : ConvexOn ℝ Set.univ f)
    (hf : ∀ x, HasGradientAt f (f' x) x)
    (L : ℝ) (hL : 0 < L)
    (hlip : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖)
    (x₁ x₂ : (E n)) :
    ‖f' x₁ - f' x₂‖ ^ 2 ≤ L * inner ℝ (f' x₁ - f' x₂) (x₁ - x₂) := by
  -- Apply key_ineq twice (swapping x₁ and x₂) and average.
  have h1 := key_ineq hconv hf L hL hlip x₁ x₂
  have h2 := key_ineq hconv hf L hL hlip x₂ x₁
  -- h1 : ‖f' x₂ - f' x₁‖² ≤ 2L·(f x₂ - f x₁ + ⟨f' x₁, x₁ - x₂⟩)
  -- h2 : ‖f' x₁ - f' x₂‖² ≤ 2L·(f x₁ - f x₂ + ⟨f' x₂, x₂ - x₁⟩)
  -- Note: ‖f' x₁ - f' x₂‖² = ‖f' x₂ - f' x₁‖² (norm of negation).
  have hnorm : ‖f' x₂ - f' x₁‖ ^ 2 = ‖f' x₁ - f' x₂‖ ^ 2 := by
    rw [show f' x₂ - f' x₁ = -(f' x₁ - f' x₂) from (neg_sub _ _).symm]
    rw [norm_neg]
  rw [hnorm] at h1
  -- Adding h1 and h2:
  --   2 · ‖f' x₁ - f' x₂‖² ≤ 2L · (⟨f' x₁, x₁ - x₂⟩ + ⟨f' x₂, x₂ - x₁⟩).
  -- Since ⟨f' x₂, x₂ - x₁⟩ = -⟨f' x₂, x₁ - x₂⟩, the RHS equals
  --   2L · ⟨f' x₁ - f' x₂, x₁ - x₂⟩.
  have hadd : 2 * ‖f' x₁ - f' x₂‖ ^ 2 ≤
      2 * L * ((f x₂ - f x₁ + inner ℝ (f' x₁) (x₁ - x₂)) +
               (f x₁ - f x₂ + inner ℝ (f' x₂) (x₂ - x₁))) := by
    nlinarith [h1, h2]
  -- Simplify the RHS.
  have hsimp : (f x₂ - f x₁ + inner ℝ (f' x₁) (x₁ - x₂)) +
      (f x₁ - f x₂ + inner ℝ (f' x₂) (x₂ - x₁)) =
      inner ℝ (f' x₁ - f' x₂) (x₁ - x₂) := by
    have h3 : (inner ℝ (f' x₂) (x₂ - x₁) : ℝ) = -inner ℝ (f' x₂) (x₁ - x₂) := by
      rw [show (x₂ - x₁ : E n) = -(x₁ - x₂) from (neg_sub _ _).symm, inner_neg_right]
    rw [h3, inner_sub_left]
    ring
  rw [hsimp] at hadd
  linarith

end Imc2002P12
