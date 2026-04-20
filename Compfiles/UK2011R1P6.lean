/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Inequality] }

/-!
# British Mathematical Olympiad 2011, Round 1, Problem 6

Let a, b and c be the lengths of the sides of a triangle.
Suppose that ab + bc + ca = 1. Show that (a + 1)(b + 1)(c + 1) < 4.
-/

namespace UK2011R1P6

problem uk2011_r1_p6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b)
    (hsum : a * b + b * c + c * a = 1) :
    (a + 1) * (b + 1) * (c + 1) < 4 := by
  -- Let s = a+b+c, p = abc. We expand: (a+1)(b+1)(c+1) = abc + (ab+bc+ca) + (a+b+c) + 1
  --   = p + 1 + s + 1 = p + s + 2. So need p + s < 2.
  -- Triangle: (a+b-c)(b+c-a)(c+a-b) > 0. This expands to -s³ + 4s - 8p.
  -- So 8p < 4s - s³, hence p < (4s-s³)/8.
  -- Then s + p < (12s - s³)/8 = 2 - (s-2)²(s+4)/8 ≤ 2.
  have habc_pos : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have ht1 : 0 < a + b - c := sub_pos.mpr hab
  have ht2 : 0 < b + c - a := sub_pos.mpr hbc
  have ht3 : 0 < c + a - b := sub_pos.mpr hca
  have htri : 0 < (a + b - c) * (b + c - a) * (c + a - b) :=
    mul_pos (mul_pos ht1 ht2) ht3
  nlinarith [htri, habc_pos, sq_nonneg (a + b + c - 2),
             sq_nonneg (a + b + c), ha, hb, hc, hsum,
             mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]

end UK2011R1P6
