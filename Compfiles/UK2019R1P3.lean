/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2019, Round 1, Problem 3

Find all positive integers x, y with x(x + 9) = y(y + 6).

(This is a restatement of BMO 2019 Round 1 Problem 3, where Ares multiplies
two integers which differ by 9 and Grace multiplies two integers which differ
by 6 and they obtain the same product T.)
-/

namespace UK2019R1P3

/-- x(x + 9) = y(y + 6) with x, y ≥ 1. Completing the square gives
    (2y + 6)² − (2x + 9)² = 36 − 81 = −45, i.e.
    (2x + 9 − 2y − 6)(2x + 9 + 2y + 6) = 45. Factorising 45 over positive
    integers yields only x = 2, y = 4 (giving T = 22·? actually T = 40). -/
determine solution_set : Set (ℕ × ℕ) := { (7, 8) }

problem uk2019_r1_p3 :
    { xy : ℕ × ℕ | 0 < xy.1 ∧ 0 < xy.2 ∧
                  xy.1 * (xy.1 + 9) = xy.2 * (xy.2 + 6) } = solution_set := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hy, heq⟩
    -- (2x+9)² - (2y+6)² = 81 - 36 = 45.
    -- (2x+9-2y-6)(2x+9+2y+6) = 45.
    -- i.e. (2x - 2y + 3)(2x + 2y + 15) = 45.
    have heqZ : (x : ℤ) * (x + 9) = y * (y + 6) := by exact_mod_cast heq
    have hfac : (2 * (x : ℤ) - 2 * y + 3) * (2 * x + 2 * y + 15) = 45 := by nlinarith [heqZ]
    -- x, y ≥ 1, so 2x + 2y + 15 ≥ 19. Therefore the second factor is ≥ 19, so it's a positive
    -- divisor of 45 that is ≥ 19. Positive divisors of 45: 1, 3, 5, 9, 15, 45.
    -- Only 45 is ≥ 19. So 2x + 2y + 15 = 45 ⇒ 2x + 2y = 30 ⇒ x + y = 15.
    -- Then 2x - 2y + 3 = 1 ⇒ 2x - 2y = -2 ⇒ y = x + 1. With x + y = 15: 2x + 1 = 15, x = 7, y = 8.
    have hB : 19 ≤ 2 * (x : ℤ) + 2 * y + 15 := by
      have : (1 : ℤ) ≤ x := by exact_mod_cast hx
      have : (1 : ℤ) ≤ y := by exact_mod_cast hy
      linarith
    have hsum_eq : 2 * (x : ℤ) + 2 * y + 15 = 45 := by
      -- second factor divides 45 and is ≥ 19; other factor is 45 / (second) ≥ 1.
      -- The second factor divides 45 in ℤ and is positive.
      have hpos : 0 < 2 * (x : ℤ) + 2 * y + 15 := by linarith
      have hdvd : (2 * (x : ℤ) + 2 * y + 15) ∣ 45 := ⟨2 * x - 2 * y + 3, by linarith [hfac]⟩
      have hle : 2 * (x : ℤ) + 2 * y + 15 ≤ 45 := Int.le_of_dvd (by norm_num) hdvd
      -- Now (2x+2y+15) is a divisor of 45 in [19, 45].
      -- Positive divisors of 45: 1, 3, 5, 9, 15, 45. Only 45 is ≥ 19.
      -- Lift to ℕ:
      set s : ℤ := 2 * (x : ℤ) + 2 * y + 15 with hs_def
      have hs_nn : 0 ≤ s := le_of_lt hpos
      lift s to ℕ using hs_nn with sN hsN
      have hsN_dvd : sN ∣ 45 := by
        have : (sN : ℤ) ∣ (45 : ℤ) := hdvd
        exact_mod_cast this
      have hsN_mem : sN ∈ Nat.divisors 45 := Nat.mem_divisors.mpr ⟨hsN_dvd, by norm_num⟩
      have hsN_le : sN ≤ 45 := by exact_mod_cast hle
      have hsN_ge : 19 ≤ sN := by exact_mod_cast hB
      have : sN = 45 := by
        have : ∀ d ∈ Nat.divisors 45, 19 ≤ d → d = 45 := by decide
        exact this sN hsN_mem hsN_ge
      rw [this]; norm_num
    -- Now compute 2x - 2y + 3 = 45 / (2x+2y+15) = 1 (using hfac).
    have hdiff_eq : 2 * (x : ℤ) - 2 * y + 3 = 1 := by
      have h45 : (2 * (x : ℤ) - 2 * y + 3) * 45 = 45 := by
        have := hfac
        rw [hsum_eq] at this
        exact this
      linarith
    -- Solve: y = x + 1, x + y = 15, so x = 7, y = 8.
    have hx_val : (x : ℤ) = 7 := by linarith
    have hy_val : (y : ℤ) = 8 := by linarith
    have hxn : x = 7 := by exact_mod_cast hx_val
    have hyn : y = 8 := by exact_mod_cast hy_val
    rw [hxn, hyn]
  · rintro h
    rw [Prod.mk.injEq] at h
    obtain ⟨hx, hy⟩ := h
    subst hx; subst hy
    refine ⟨by decide, by decide, by decide⟩

end UK2019R1P3
