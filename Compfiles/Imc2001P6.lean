/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2001, Problem 6
(IMC 2001, Day 1, Problem 6)

Suppose that the functions `a, b, f, g : ℝ → ℝ` are differentiable on all of `ℝ`,
and satisfy
  `f ≥ 0`, `f' ≥ 0`, `g > 0`, `g' > 0`,
and
  `f'(x)/g'(x) + a(x) · f(x)/g(x) = b(x)` for all `x`.
Further assume that `a(x) → A`, `b(x) → B` with `A > 0`, that `f(x) → ∞`,
`g(x) → ∞`, as `x → ∞`. Prove that `f(x)/g(x) → B/(A+1)` as `x → ∞`.
-/

namespace Imc2001P6

open Filter Topology

problem imc2001_p6
    (a b f g : ℝ → ℝ)
    (f' g' : ℝ → ℝ)
    (A B : ℝ)
    (hA : 0 < A)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf'_nonneg : ∀ x, 0 ≤ f' x)
    (hg_pos : ∀ x, 0 < g x)
    (hg'_pos : ∀ x, 0 < g' x)
    (_hf_deriv : ∀ x, HasDerivAt f (f' x) x)
    (_hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (_ha_diff : Differentiable ℝ a)
    (_hb_diff : Differentiable ℝ b)
    (ha_lim : Tendsto a atTop (𝓝 A))
    (hb_lim : Tendsto b atTop (𝓝 B))
    (_hf_infty : Tendsto f atTop atTop)
    (_hg_infty : Tendsto g atTop atTop)
    (hrel : ∀ x, f' x / g' x + a x * (f x / g x) = b x) :
    Tendsto (fun x => f x / g x) atTop (𝓝 (B / (A + 1))) := by
  -- This is a nontrivial generalized l'Hopital-type result.
  -- The proof uses the identity
  --   (f * g^A)' / (g^(A+1))' = (f'/g' + A * f/g) / (A + 1),
  -- combined with the given relation f'/g' = b - a * f/g, to bound
  -- (f * g^A)' / (g^(A+1))' between (B-ε)/(A+1) · (something) and its upper analog,
  -- then invokes Stolz–Cesàro / l'Hopital for the ratio (f g^A)/(g^(A+1)) = f/g.
  -- Full formalization in Lean is substantial; recorded as TODO.
  sorry

end Imc2001P6
