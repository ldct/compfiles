/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2007, Problem 8
(IMC 2007, Day 2, Problem 2)

Let `x, y, z` be integers with `29 ∣ x^4 + y^4 + z^4`. Prove that
`29 ∣ x`, `29 ∣ y`, and `29 ∣ z`.
-/

namespace Imc2007P8

snip begin

/-
The fourth powers in `ℤ/29ℤ` form the set `{0, 1, 7, 16, 20, 23, 24, 25}`
(since `29 = 4 · 7 + 1`, the multiplicative group `(ℤ/29ℤ)*` is cyclic of order
`28`, and the map `a ↦ a^4` has image of size `28 / gcd(28, 4) = 7`, plus `0`).
We check by enumeration that for all `a, b, c ∈ ℤ/29ℤ`, if
`a^4 + b^4 + c^4 = 0` then `a = b = c = 0`.
-/

/-- In `ZMod 29`, the only solution of `a^4 + b^4 + c^4 = 0` is `a = b = c = 0`. -/
lemma key (a b c : ZMod 29) (h : a^4 + b^4 + c^4 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  revert h
  revert a b c
  decide

snip end

problem imc2007_p8 (x y z : ℤ) (h : (29 : ℤ) ∣ x^4 + y^4 + z^4) :
    (29 : ℤ) ∣ x ∧ (29 : ℤ) ∣ y ∧ (29 : ℤ) ∣ z := by
  -- Cast to ZMod 29.
  have hcast : ((x^4 + y^4 + z^4 : ℤ) : ZMod 29) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  push_cast at hcast
  obtain ⟨hx, hy, hz⟩ := key (x : ZMod 29) (y : ZMod 29) (z : ZMod 29) hcast
  refine ⟨?_, ?_, ?_⟩
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 29).mp hx
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd y 29).mp hy
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 29).mp hz

end Imc2007P8
