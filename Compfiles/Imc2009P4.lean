/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2009, Problem 4

Let `p(z) = ∑_{k=0}^n a_k z^k` be a complex polynomial. Suppose
`1 = c_0 ≥ c_1 ≥ ⋯ ≥ c_n ≥ 0` are real numbers satisfying the convexity
condition `2 c_k ≤ c_{k-1} + c_{k+1}` for `1 ≤ k ≤ n-1`. Define
`q(z) = ∑ c_k a_k z^k`. Prove that
`max_{|z| ≤ 1} |q(z)| ≤ max_{|z| ≤ 1} |p(z)|`.

The proof uses Cauchy's integral formula on the unit circle to write
`q(w) = (1 / 2π) ∫_S K(w/z) p(z) |dz|` where the kernel is
`K(u) = ∑_{j=-n}^n c_{|j|} u^j`. Setting `d_k = c_{k-1} - 2 c_k + c_{k+1} ≥ 0`
(with `c_{n+1} = 0`), one writes `K = ∑ d_k F_k` where `F_k` is the
Fejér kernel `|∑_{j=0}^{k-1} u^j|^2 ≥ 0`. Since `K ≥ 0` on the circle,
`∫ |K| = ∫ K = 2π c_0 = 2π`, and the inequality follows.
-/

namespace Imc2009P4

open Polynomial Complex

/--
The statement: for a complex polynomial `p` of degree ≤ `n` and a finite
sequence of real coefficients `c : Fin (n+1) → ℝ` that is non-negative,
non-increasing, with `c 0 = 1`, and convex (`2 c k ≤ c (k-1) + c (k+1)`
for interior indices), the polynomial `q` whose `k`-th coefficient is
`c k * (p.coeff k)` satisfies the bound

  `sup_{|z| ≤ 1} |q(z)| ≤ sup_{|z| ≤ 1} |p(z)|`.
-/
problem imc2009_p4 (n : ℕ) (p : Polynomial ℂ) (hpdeg : p.natDegree ≤ n)
    (c : ℕ → ℝ)
    (hc0 : c 0 = 1)
    (hcnn : ∀ k, 0 ≤ c k)
    (hcmono : ∀ k, c (k + 1) ≤ c k)
    (hczero : ∀ k, n < k → c k = 0)
    (hconvex : ∀ k, 1 ≤ k → k ≤ n - 1 → 2 * c k ≤ c (k - 1) + c (k + 1))
    (q : Polynomial ℂ)
    (hq : ∀ k, q.coeff k = (c k : ℂ) * p.coeff k)
    (Mp : ℝ) (hMp : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖p.eval z‖ ≤ Mp) :
    ∀ w : ℂ, ‖w‖ ≤ 1 → ‖q.eval w‖ ≤ Mp := by
  -- TODO: full analytic proof.
  -- Outline:
  --   (1) For |z| = 1, write a_j = (1/(2π)) ∫_S p(z) z^{-j} |dz| (Cauchy).
  --   (2) Hence q(w) = (1/(2π)) ∫_S K(w/z) p(z) |dz|, with
  --       K(u) = ∑_{j = -n}^{n} c_{|j|} u^j.
  --   (3) Setting d_k = c_{k-1} - 2 c_k + c_{k+1} ≥ 0 (boundary terms via
  --       hcmono and hczero), and F_k(u) = ∑_{j = -(k-1)}^{k-1} (k - |j|) u^j
  --       (the Fejér kernel), one has K = ∑_k d_k F_k.
  --   (4) On |u| = 1, F_k(u) = |∑_{j=0}^{k-1} u^j|^2 ≥ 0, so K ≥ 0.
  --   (5) Therefore ∫_S |K| |du| = ∫_S K |du| = 2π c_0 = 2π.
  --   (6) Then |q(w)| ≤ (1/(2π)) · M_p · 2π = M_p.
  sorry

end Imc2009P4
