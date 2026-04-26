/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 6
(IMC 2000, Day 1, Problem 6)

Let `f : ℝ → (0, ∞)` be a strictly increasing, differentiable function with
`f(x) → ∞` as `x → ∞` and with `f'` bounded. Let `F(x) = ∫₀^x f(t) dt`.
Define sequences by
  `a₀ = 1`,     `aₙ₊₁ = aₙ + 1/f(aₙ)`,
and let `bₙ = F⁻¹(n)`, i.e. `F(bₙ) = n`.
Prove that `aₙ - bₙ → 0` as `n → ∞`.

## Outline of the solution

By the Mean Value Theorem applied to `F` on `[aₖ, aₖ₊₁]`, there is
`ξₖ ∈ (aₖ, aₖ₊₁)` with `F(aₖ₊₁) - F(aₖ) = (aₖ₊₁ - aₖ) · f(ξₖ) = f(ξₖ)/f(aₖ)`.
Since `f` is increasing, this quantity lies in
`[1, 1 + (f(aₖ₊₁) - f(aₖ))/f(aₖ)]`. Summing over `k = 0,…,n-1` yields, using
`F(bₙ) = n`,
`F(bₙ) < n + F(a₀) ≤ F(aₙ) ≤ F(bₙ) + F(a₀) + Σₖ (f(aₖ₊₁)-f(aₖ))/f(aₖ)`.
Hence `aₙ > bₙ` and `aₙ → ∞`.

For `ε > 0` choose `K` with `f(a_K) > 2/ε`. Splitting the sum at `K` and
bounding the tail by `ε/2 · (f(aₙ) - f(a_K))`, we obtain `F(aₙ) - F(bₙ) < ε·f(aₙ)`
for large `n`. Again by the MVT, `F(aₙ) - F(bₙ) = f(ζₙ)(aₙ - bₙ)` for some
`ζₙ ∈ (bₙ, aₙ)`, and `f(ζₙ) > f(bₙ)`. If `B` bounds `f'`, then
`f(aₙ) < f(bₙ) + B(aₙ - bₙ)`, giving
`(f(bₙ) - εB)(aₙ - bₙ) < ε · f(bₙ)`, whence `aₙ - bₙ < 2ε` for large `n`.

A full Lean formalization requires a careful use of the Mean Value Theorem
applied to `F` together with the Fundamental Theorem of Calculus
(`F` is an antiderivative of `f`), and is substantial; we record the theorem
statement and a TODO.
-/

namespace Imc2000P6

open Filter Topology

problem imc2000_p6
    (f : ℝ → ℝ)
    (f' : ℝ → ℝ)
    (F : ℝ → ℝ)
    (B : ℝ)
    (hf_pos : ∀ x, 0 < f x)
    (hf_mono : StrictMono f)
    (_hf_deriv : ∀ x, HasDerivAt f (f' x) x)
    (_hf_infty : Tendsto f atTop atTop)
    (_hf'_bdd : ∀ x, |f' x| ≤ B)
    (_hF_deriv : ∀ x, HasDerivAt F (f x) x)
    (_hF_zero : F 0 = 0)
    (a : ℕ → ℝ)
    (_ha0 : a 0 = 1)
    (_ha_rec : ∀ n, a (n + 1) = a n + 1 / f (a n))
    (b : ℕ → ℝ)
    (_hb : ∀ n, F (b n) = n) :
    Tendsto (fun n => a n - b n) atTop (𝓝 0) := by
  -- This is a nontrivial real-analysis limit result.
  -- The proof uses the Mean Value Theorem applied to `F` on successive
  -- intervals `[a_k, a_{k+1}]` to relate `F(a_n) - F(b_n)` to a telescoping
  -- sum of `(f(a_{k+1}) - f(a_k))/f(a_k)`, then uses boundedness of `f'`
  -- together with the MVT applied once more to `F` on `[b_n, a_n]` to
  -- conclude that the difference `a_n - b_n` tends to zero.
  -- Full formalization in Lean is substantial; recorded as TODO.
  sorry

end Imc2000P6
