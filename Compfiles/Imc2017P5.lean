/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2017, Problem 5

Let `k` and `n` be positive integers with `n ≥ k² - 3k + 4`, and let
`f(z) = z^{n-1} + c_{n-2} z^{n-2} + … + c_0` be a polynomial with complex
coefficients such that
`c_0 c_{n-2} = c_1 c_{n-3} = … = c_{n-2} c_0 = 0`.
Prove that `f(z)` and `z^n - 1` have at most `n - k` common roots.

## Proof sketch (official solution)

Let `M = {z ∈ ℂ : z^n = 1}` (so `|M| = n`) and let `A = {z ∈ M : f(z) ≠ 0}`.
The set of common roots of `f` and `z^n - 1` is `M ∖ A`, so it suffices to
show `|A| ≥ k`, i.e. `|M ∖ A| ≤ n - k`.

Setting `c_{n-1} = 1`, the key identity (using `∑_{z ∈ M} z^m = n` if `n ∣ m`,
else `0`) is, for every `η ∈ M`,
  `∑_{z ∈ M} z² f(z) f(η z) = n (c_{n-1}² + ∑_{j=0}^{n-2} c_j c_{n-2-j} η^{n-2-j}) = n ≠ 0`,
since each `c_j c_{n-2-j} = 0`. So for every `η ∈ M` there exists `b ∈ M` with
`f(b) ≠ 0` and `f(η b) ≠ 0`; set `a = η b`, so `a, b ∈ A` and `a b^{-1} = η`.

Hence the map `(a, b) ↦ a b^{-1}` from `A × A` to `M` is surjective onto
`M ∖ {1}` only via pairs with `a ≠ b`, giving `|A|(|A| - 1) ≥ |M| - 1 = n - 1`.
Combined with `n ≥ k² - 3k + 4`, this yields `|A|(|A| - 1) ≥ (k-1)(k-2) + 1`,
hence `|A| ≥ k`.
-/

namespace Imc2017P5

open Polynomial Finset BigOperators

/-- The polynomial `f(z) = z^{n-1} + ∑_{i=0}^{n-2} c_i z^i`, where the
coefficients `c_0, …, c_{n-2}` are encoded as `c : Fin (n - 1) → ℂ`. -/
noncomputable def f (n : ℕ) (c : Fin (n - 1) → ℂ) : Polynomial ℂ :=
  X ^ (n - 1) + ∑ i : Fin (n - 1), C (c i) * X ^ (i : ℕ)

/-- The polynomial `z^n - 1`. -/
noncomputable def g (n : ℕ) : Polynomial ℂ := X ^ n - 1

/-- Statement of IMC 2017 Problem 5.

Under the hypotheses `0 < k`, `0 < n`, `n ≥ k² - 3k + 4`, and the pairing
condition `c_i · c_{n-2-i} = 0` for all `i ≤ n - 2`, the polynomials
`f` and `z^n - 1` share at most `n - k` common roots. -/
problem imc2017_p5 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hkn : k ^ 2 + 4 ≤ n + 3 * k)
    (c : Fin (n - 1) → ℂ)
    (hpair : ∀ i j : Fin (n - 1), (i : ℕ) + (j : ℕ) = n - 2 → c i * c j = 0) :
    ((f n c).roots.toFinset ∩ (g n).roots.toFinset).card ≤ n - k := by
  -- See the file-level docstring for the proof outline. The full formalization
  -- (sum over n-th roots of unity and double-counting) is left as future work.
  sorry

end Imc2017P5
