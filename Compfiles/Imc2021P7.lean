/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 7

Let `D ⊆ ℂ` be an open set containing the closed unit disk. Let
`f : D → ℂ` be holomorphic, and let `p(z)` be a monic polynomial. Prove
that

  `|f(0)| ≤ max_{|z|=1} |f(z) p(z)|`.
-/

namespace Imc2021P7

open Complex

/-- Problem statement: for any polynomial `p` that is monic (leading coefficient 1)
and any function `f` holomorphic on an open set `D` containing the closed unit
disk, we have `|f(0)| ≤ max_{|z|=1} |f(z) * p(z)|`.

TODO: The official solution introduces the "reverse" polynomial
`q(z) = z^n * conj(p(1/conj(z)))`. Then on the unit circle `|q(z)| = |p(z)|`,
and `q(0) = 1`. Applying the maximum modulus principle to `f * q` (which is
holomorphic on `D` and continuous on the closed disk) gives

  `|f(0)| = |f(0) * q(0)| ≤ max_{|z|=1} |f(z) * q(z)| = max_{|z|=1} |f(z) * p(z)|`.
-/
problem imc2021_p7 (D : Set ℂ) (hD : IsOpen D) (hD1 : Metric.closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D)
    (p : Polynomial ℂ) (hp : p.Monic) :
    ‖f 0‖ ≤ sSup ((fun z => ‖f z * p.eval z‖) '' Metric.sphere (0 : ℂ) 1) := by
  sorry

end Imc2021P7
