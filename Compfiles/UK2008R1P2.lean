/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2008, Round 1, Problem 2

Find all solutions in positive integers x, y, z to the simultaneous equations
x + y − z = 12
x² + y² − z² = 12.
-/

namespace UK2008R1P2

determine solution_set : Set (ℕ × ℕ × ℕ) :=
  { (13, 78, 79), (78, 13, 79),
    (14, 45, 47), (45, 14, 47),
    (15, 34, 37), (34, 15, 37),
    (18, 23, 29), (23, 18, 29) }

problem uk2008_r1_p2 :
    { xyz : ℕ × ℕ × ℕ | 0 < xyz.1 ∧ 0 < xyz.2.1 ∧ 0 < xyz.2.2 ∧
        (xyz.1 : ℤ) + xyz.2.1 - xyz.2.2 = 12 ∧
        (xyz.1 : ℤ)^2 + (xyz.2.1 : ℤ)^2 - (xyz.2.2 : ℤ)^2 = 12 } = solution_set := by
  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨hx, hy, hz, h1, h2⟩
    have hzxy : (z : ℤ) = (x : ℤ) + y - 12 := by linarith
    have hprod : ((x : ℤ) - 12) * ((y : ℤ) - 12) = 66 := by
      have h2' : (x : ℤ)^2 + (y : ℤ)^2 - ((x : ℤ) + y - 12)^2 = 12 := by
        rw [← hzxy]; exact h2
      nlinarith [h2']
    have hx_ge : (1 : ℤ) ≤ x := by exact_mod_cast hx
    have hy_ge : (1 : ℤ) ≤ y := by exact_mod_cast hy
    have hz_ge : (1 : ℤ) ≤ z := by exact_mod_cast hz
    -- Key claim: x ≥ 13 and y ≥ 13.
    -- Proof: (x-12)(y-12) = 66 > 0, so same sign. x+y = z+12 ≥ 13 so (x-12)+(y-12) ≥ -11.
    -- Can't both be ≤ 0 while summing to ≥ -11 and having product 66:
    --   since then -11 ≤ u ≤ 0, -11 ≤ v ≤ 0 (x,y ≥ 1), uv ≤ 121 and ≥ 0 (but = 66 needs both ≠ 0)
    --   then |u|·|v| = 66, but |u|+|v| = -(u+v) ≤ 11. By AM-GM, 66 ≤ (|u|+|v|)²/4 ≤ 30.25.
    --   Actually 2·sqrt(66) ≈ 16.2 ≤ |u|+|v|, contradicting ≤ 11.
    have hx_ge13 : 13 ≤ x := by
      have hub : (x : ℤ) - 12 > 0 := by
        by_contra hc
        rw [not_lt] at hc
        -- (x-12) ≤ 0 ⇒ (y-12) ≤ 0 (else product ≤ 0)
        have hv_le : (y : ℤ) - 12 ≤ 0 := by
          by_contra hv; rw [not_le] at hv
          have : ((x : ℤ) - 12) * ((y : ℤ) - 12) ≤ 0 := by
            apply mul_nonpos_of_nonpos_of_nonneg hc (le_of_lt hv)
          linarith
        -- -11 ≤ x - 12 ≤ 0 and -11 ≤ y - 12 ≤ 0
        have hxl : -11 ≤ (x : ℤ) - 12 := by linarith
        have hyl : -11 ≤ (y : ℤ) - 12 := by linarith
        -- x + y ≥ 13 (since z ≥ 1)
        have hsum : (x : ℤ) + y ≥ 13 := by linarith
        -- Both ≤ 0 and ≥ -11, so (x-12)(y-12) ≥ 0.
        -- Also |x-12|+|y-12| = -(x-12)-(y-12) ≤ 11.
        -- Product (x-12)(y-12) ≤ ((|x-12|+|y-12|)/2)² ≤ (11/2)² = 30.25 < 66.
        have hau : -(((x : ℤ) - 12)) ≥ 0 := by linarith
        have hav : -(((y : ℤ) - 12)) ≥ 0 := by linarith
        have hsumabs : -((x : ℤ) - 12) + -(((y : ℤ) - 12)) ≤ 11 := by linarith
        have hprod_pos : (-((x : ℤ) - 12)) * (-((y : ℤ) - 12)) = 66 := by
          have := hprod; ring_nf; linarith [hprod]
        nlinarith [sq_nonneg (-((x : ℤ) - 12) - -((y : ℤ) - 12)), hprod_pos, hsumabs, hau, hav]
      have : (13 : ℤ) ≤ x := by linarith
      exact_mod_cast this
    have hy_ge13 : 13 ≤ y := by
      have hub : (y : ℤ) - 12 > 0 := by
        by_contra hc
        rw [not_lt] at hc
        have hu_le : (x : ℤ) - 12 ≤ 0 := by
          by_contra hu; rw [not_le] at hu
          have : ((x : ℤ) - 12) * ((y : ℤ) - 12) ≤ 0 := by
            apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hu) hc
          linarith
        have hxl : -11 ≤ (x : ℤ) - 12 := by linarith
        have hyl : -11 ≤ (y : ℤ) - 12 := by linarith
        have hsum : (x : ℤ) + y ≥ 13 := by linarith
        have hau : -(((x : ℤ) - 12)) ≥ 0 := by linarith
        have hav : -(((y : ℤ) - 12)) ≥ 0 := by linarith
        have hsumabs : -((x : ℤ) - 12) + -(((y : ℤ) - 12)) ≤ 11 := by linarith
        have hprod_pos : (-((x : ℤ) - 12)) * (-((y : ℤ) - 12)) = 66 := by
          have := hprod; ring_nf; linarith [hprod]
        nlinarith [sq_nonneg (-((x : ℤ) - 12) - -((y : ℤ) - 12)), hprod_pos, hsumabs, hau, hav]
      have : (13 : ℤ) ≤ y := by linarith
      exact_mod_cast this
    -- Now x, y ≥ 13, so (x-12) ≥ 1, (y-12) ≥ 1 in ℕ.
    have ha_pos : 1 ≤ x - 12 := by omega
    have hb_pos : 1 ≤ y - 12 := by omega
    have hprodN : (x - 12) * (y - 12) = 66 := by
      have : ((x - 12 : ℕ) : ℤ) * ((y - 12 : ℕ) : ℤ) = 66 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; exact hprod
      exact_mod_cast this
    -- a = x - 12, b = y - 12, a*b = 66, a ≤ 66, b ≤ 66
    have ha_le : x - 12 ≤ 66 := by
      by_contra hc; rw [not_le] at hc
      have : (x - 12) * (y - 12) ≥ 67 := by
        calc (x - 12) * (y - 12) ≥ 67 * 1 := by
                exact Nat.mul_le_mul (by omega) hb_pos
          _ = 67 := by ring
      omega
    have hb_le : y - 12 ≤ 66 := by
      by_contra hc; rw [not_le] at hc
      have : (x - 12) * (y - 12) ≥ 67 := by
        calc (x - 12) * (y - 12) ≥ 1 * 67 := by
                exact Nat.mul_le_mul ha_pos (by omega)
          _ = 67 := by ring
      omega
    have hzeq : z = x + y - 12 := by
      have hc : (z : ℤ) = ((x + y - 12 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith
      exact_mod_cast hc
    subst hzeq
    -- Now do case analysis on x - 12 ∈ [1, 66].
    have hxeq : x = (x - 12) + 12 := by omega
    have hyeq : y = (y - 12) + 12 := by omega
    set a := x - 12 with ha_def
    set b := y - 12 with hb_def
    have ha_le66 : a ≤ 66 := ha_le
    have ha_ge1 : 1 ≤ a := ha_pos
    -- Replace (a*b = 66) in ℕ and a ∈ [1,66]:
    have hdisj : (a = 1 ∧ b = 66) ∨ (a = 2 ∧ b = 33) ∨ (a = 3 ∧ b = 22) ∨ (a = 6 ∧ b = 11) ∨
                 (a = 11 ∧ b = 6) ∨ (a = 22 ∧ b = 3) ∨ (a = 33 ∧ b = 2) ∨ (a = 66 ∧ b = 1) := by
      interval_cases a <;> omega
    have hxrw : x = a + 12 := hxeq
    have hyrw : y = b + 12 := hyeq
    rcases hdisj with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      (rw [ha] at hxrw; rw [hb] at hyrw;
       rw [hxrw, hyrw])
    · left; decide
    · right; right; left; decide
    · right; right; right; right; left; decide
    · right; right; right; right; right; right; left; decide
    · right; right; right; right; right; right; right; decide
    · right; right; right; right; right; left; decide
    · right; right; right; left; decide
    · right; left; decide
  · rintro (h | h | h | h | h | h | h | h) <;>
    · rw [Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨hx, hy, hz⟩ := h
      subst hx; subst hy; subst hz
      refine ⟨by decide, by decide, by decide, by norm_num, by norm_num⟩

end UK2008R1P2
