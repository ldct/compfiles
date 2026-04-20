/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2007, Round 2, Problem 1

Triangle ABC has integer-length sides, and AC = 2007. The internal bisector
of ∠BAC meets BC at D. Given that AB = CD, determine AB and BC.

By the angle-bisector length/ratio theorem, BD/DC = AB/AC, so if AB = c,
BC = a, AC = b = 2007 and CD = c, then BD = a − c and (a − c)/c = c/2007,
i.e. 2007(a − c) = c², giving a = c + c²/2007. Thus 2007 | c², and using
2007 = 3² · 223, we get 3·223 | c, so c is a multiple of 669. The triangle
inequality then pins down c = 1593 (c must satisfy c < 2 · 2007 = 4014, etc).
-/

namespace UK2007R2P1

/-- The pair (AB, BC) determined by the problem. -/
determine solution_pair : ℕ × ℕ := (1338, 2230)

problem uk2007_r2_p1 :
    ∀ a b c : ℕ,
      0 < a → 0 < b → 0 < c →
      b = 2007 →
      -- triangle inequality (non-degenerate integer triangle)
      a < b + c → b < a + c → c < a + b →
      -- AB = CD, where D is on BC with BD/DC = AB/AC (angle bisector);
      -- CD = c means BD = a - c and (a - c) * b = c * c
      c ≤ a →
      (a - c) * b = c * c →
      (c, a) = solution_pair := by
  intro a b c ha hb hc hb_eq habc hbac hcab hca hprod
  subst hb_eq
  -- hprod : (a - c) * 2007 = c * c (Nat subtraction, but c ≤ a so it's fine)
  -- Move to ℤ for safety.
  have hprodZ : ((a : ℤ) - c) * 2007 = (c : ℤ) * c := by
    have : ((a - c : ℕ) : ℤ) * 2007 = ((c * c : ℕ) : ℤ) := by exact_mod_cast hprod
    rw [Nat.cast_sub hca] at this
    push_cast at this; linarith
  -- 2007 = 3² · 223. Since 2007 | c², we get 3·223 | c.
  -- Let's directly show c = 669·k for some k ∈ {1, 2}.
  -- From hprodZ: c² = 2007(a-c). So 2007 | c². Since 223 is prime and 2007 = 9·223,
  -- 223 | c² ⇒ 223 | c; similarly 3 | c (actually 9 | c² ⇒ 3 | c).
  -- So 669 | c. Let c = 669 k.
  have h223_dvd_c : (223 : ℤ) ∣ c := by
    have h : (223 : ℤ) ∣ c * c := by
      have : (223 : ℤ) ∣ ((a : ℤ) - c) * 2007 := by
        refine Dvd.dvd.mul_left ?_ _
        norm_num
      rw [hprodZ] at this; exact this
    exact (Int.Prime.dvd_mul' (by norm_num) h).elim id id
  have h3_dvd_c : (3 : ℤ) ∣ c := by
    have h : (3 : ℤ) ∣ c * c := by
      have : (3 : ℤ) ∣ ((a : ℤ) - c) * 2007 := by
        refine Dvd.dvd.mul_left ?_ _
        norm_num
      rw [hprodZ] at this; exact this
    exact (Int.Prime.dvd_mul' (by norm_num) h).elim id id
  -- 3 and 223 are coprime, so 669 | c
  have h669_dvd_c : (669 : ℤ) ∣ c := by
    have hcop : IsCoprime (3 : ℤ) 223 := by decide
    have : (3 * 223 : ℤ) ∣ c := hcop.mul_dvd h3_dvd_c h223_dvd_c
    norm_num at this; exact this
  -- Thus c = 669 * k for some k ≥ 1, k : ℕ.
  have hc_pos : (1 : ℤ) ≤ c := by exact_mod_cast hc
  obtain ⟨k, hkeq⟩ := h669_dvd_c
  have hk_pos : 0 < k := by
    by_contra hk0
    rw [not_lt] at hk0
    have : (c : ℤ) ≤ 0 := by
      rw [hkeq]
      have : 669 * k ≤ 669 * 0 := by
        apply mul_le_mul_of_nonneg_left hk0 (by norm_num)
      linarith
    linarith
  -- a = c + c²/2007 = 669k + (669k)²/2007 = 669k + 223 k² (since 669² / 2007 = 447561/2007 = 223).
  have ha_eq : (a : ℤ) = 669 * k + 223 * k^2 := by
    have : ((a : ℤ) - c) * 2007 = c * c := hprodZ
    rw [hkeq] at this
    have : ((a : ℤ) - 669 * k) * 2007 = 223 * 2007 * k^2 := by nlinarith [this]
    have : ((a : ℤ) - 669 * k) = 223 * k^2 := by
      have h2007 : (2007 : ℤ) ≠ 0 := by norm_num
      have := this
      -- Divide both sides by 2007
      have h' : ((a : ℤ) - 669 * k) * 2007 = (223 * k^2) * 2007 := by linarith
      exact mul_right_cancel₀ h2007 h'
    linarith
  -- Triangle inequality: b < a + c ⟺ 2007 < a + c = 669k + 223k² + 669k = 223k² + 1338k.
  have hbac' : (2007 : ℤ) < 223 * k^2 + 1338 * k := by
    have : (a : ℤ) + c > 2007 := by exact_mod_cast hbac
    rw [ha_eq, hkeq] at this
    linarith
  -- Triangle inequality: a < b + c ⟺ 669k + 223k² < 2007 + 669k ⟺ 223k² < 2007 ⟺ k² ≤ 9.
  have habc' : 223 * k^2 < 2007 := by
    have : (a : ℤ) < 2007 + c := by exact_mod_cast habc
    rw [ha_eq, hkeq] at this
    linarith
  -- k² < 9, so k ≤ 2 (in positive integers).
  have hk_sq : k^2 ≤ 8 := by linarith
  have hk_le : k ≤ 2 := by
    by_contra hc'
    rw [not_le] at hc'
    have : k^2 ≥ 9 := by nlinarith
    linarith
  -- hbac: 223 k² + 1338 k > 2007. For k=1: 223 + 1338 = 1561 < 2007. So k ≠ 1.
  have hk_ne1 : k ≠ 1 := by
    intro hk1
    rw [hk1] at hbac'
    norm_num at hbac'
  -- k ∈ {1, 2} and k ≠ 1, so k = 2.
  have hk2 : k = 2 := by
    interval_cases k
    · exact absurd rfl hk_ne1
    · rfl
  rw [hk2] at ha_eq hkeq
  have hcZ : (c : ℤ) = 1338 := by linarith
  have hc_val : c = 1338 := by exact_mod_cast hcZ
  have haZ : (a : ℤ) = 2230 := by linarith
  have ha_val : a = 2230 := by exact_mod_cast haZ
  rw [hc_val, ha_val]

end UK2007R2P1
