/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2006, Problem 9

(Also listed as Day 2, Problem 3.)

Compare `tan (sin x)` and `sin (tan x)` for `x ∈ (0, π/2)`.

Answer: `tan (sin x) > sin (tan x)`.

## Proof sketch

Let `f(x) = tan (sin x) - sin (tan x)`. Then `f(0) = 0` and
`f'(x) = cos x / cos² (sin x) - cos (tan x) / cos² x`.

* **Case 1: `x ∈ (0, arctan (π/2))`.** Here `tan x < π/2`, so `cos (tan x) > 0`.
  Writing
  `f'(x) = (cos³ x - cos (tan x) · cos² (sin x)) / (cos² x · cos² (tan x))`,
  it suffices to prove `cos (tan x) · cos² (sin x) < cos³ x`.

  By AM-GM on three positive factors:
  `(cos (tan x) · cos² (sin x))^{1/3} ≤ (cos (tan x) + 2 cos (sin x)) / 3`.

  By concavity of `cos` on `[0, π/2]`:
  `(cos (tan x) + 2 cos (sin x)) / 3 ≤ cos ((tan x + 2 sin x) / 3)`.

  Finally one shows `(tan x + 2 sin x) / 3 > x` on `(0, π/2)` via derivative analysis
  (at `x = 0` both sides vanish; the derivative of `tan x + 2 sin x - 3x` is
  `sec² x + 2 cos x - 3 ≥ 0` by AM-GM on `sec² x, cos x, cos x`).
  Combined with monotonicity of `cos` on `[0, π/2]`, we get
  `cos ((tan x + 2 sin x) / 3) < cos x`. Hence `f' > 0` on the interval, so
  `f(x) > f(0) = 0`.

* **Case 2: `x ∈ [arctan (π/2), π/2)`.** Then `tan x ≥ π/2`, and
  `sin x ≥ (π/2) / √(1 + π²/4) > π/4`. Therefore `tan (sin x) > tan (π/4) = 1`,
  and `sin (tan x) ≤ 1`. So `tan (sin x) > sin (tan x)`.
-/

namespace Imc2006P9

open Real

problem imc2006_p9 :
    ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2), sin (tan x) < tan (sin x) := by
  -- The full proof requires:
  --   Case 1 (x ∈ (0, arctan (π/2))): a derivative-of-`tan (sin x) - sin (tan x)`
  --     analysis. The derivative equals
  --     `(cos³ x - cos (tan x) · cos² (sin x)) / (cos² x · cos² (tan x))`
  --     which is positive: by AM-GM on three positive factors,
  --     `(cos (tan x) · cos² (sin x))^{1/3} ≤ (cos (tan x) + 2 cos (sin x)) / 3`;
  --     by concavity of cos on `[0, π/2]`, this is
  --     `≤ cos ((tan x + 2 sin x) / 3)`; and since `(tan x + 2 sin x)/3 > x`
  --     (proved by showing its derivative `(sec² x + 2 cos x - 3)/3 ≥ 0` via AM-GM),
  --     this is strictly less than `cos x`. So `f' > 0`, hence `f > f(0) = 0`.
  --   Case 2 (x ∈ [arctan (π/2), π/2)): `sin x ≥ (π/2) / √(1 + π²/4) > π/4`
  --     (since `π² < 12`), so `tan (sin x) > tan (π/4) = 1 ≥ sin (tan x)`.
  -- Both cases require substantial real-analysis work. See the docstring above.
  sorry

end Imc2006P9
