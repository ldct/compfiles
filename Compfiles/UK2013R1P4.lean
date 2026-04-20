/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# British Mathematical Olympiad 2013, Round 1, Problem 4

Find all positive integers n such that 12n − 119 and 75n − 539 are both
perfect squares.
-/

namespace UK2013R1P4

determine solution_set : Set ℕ := { 12, 20 }

problem uk2013_r1_p4 :
    { n : ℕ | 0 < n ∧ (∃ a : ℕ, 12 * n = a^2 + 119) ∧
                     (∃ b : ℕ, 75 * n = b^2 + 539) } = solution_set := by
  ext n
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, ⟨a, ha⟩, ⟨b, hb⟩⟩
    -- From 12n = a²+119 and 75n = b²+539, eliminate n: 75·(a²+119) = 12·(b²+539).
    -- ⇒ 75a² + 8925 = 12b² + 6468 ⇒ 12b² - 75a² = 2457 ⇒ 4b² - 25a² = 819.
    -- ⇒ (2b - 5a)(2b + 5a) = 819.
    have hkey : (2 * (b : ℤ) - 5 * a) * (2 * b + 5 * a) = 819 := by
      have hn_eq : 75 * (12 * n) = 75 * (a^2 + 119) := by rw [ha]
      have hn_eq' : 12 * (75 * n) = 12 * (b^2 + 539) := by rw [hb]
      have : 75 * (a^2 + 119) = 12 * (b^2 + 539) := by
        have h1 : (75 * 12) * n = 75 * (a^2 + 119) := by
          rw [← hn_eq]; ring
        have h2 : (12 * 75) * n = 12 * (b^2 + 539) := by
          rw [← hn_eq']; ring
        have heq : (75 * 12 : ℕ) = 12 * 75 := by norm_num
        rw [heq] at h1
        linarith [h1, h2]
      -- Cast to ℤ and manipulate.
      have : (75 : ℤ) * ((a : ℤ)^2 + 119) = 12 * ((b : ℤ)^2 + 539) := by exact_mod_cast this
      nlinarith [this]
    -- Bound a and b.
    have hb_sq : (b : ℤ) ^ 2 = 75 * (n : ℤ) - 539 := by
      have : (75 * n : ℕ) = b^2 + 539 := hb
      have : ((75 * n : ℕ) : ℤ) = ((b^2 + 539 : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at this
      linarith
    have ha_sq : (a : ℤ) ^ 2 = 12 * (n : ℤ) - 119 := by
      have : (12 * n : ℕ) = a^2 + 119 := ha
      have : ((12 * n : ℕ) : ℤ) = ((a^2 + 119 : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at this
      linarith
    -- (2b - 5a), (2b + 5a) are divisors of 819 (in ℤ) with (2b+5a) ≥ 0.
    -- Since b ≥ 0 and a ≥ 0, 2b + 5a ≥ 0.
    -- The product is 819. Case split on divisor pairs.
    set u : ℤ := 2 * (b : ℤ) - 5 * a with hu
    set v : ℤ := 2 * (b : ℤ) + 5 * a with hv
    have huv : u * v = 819 := hkey
    have hv_nn : 0 ≤ v := by positivity
    have hv_pos : 0 < v := by
      by_contra h
      rw [not_lt] at h
      have : v = 0 := le_antisymm h hv_nn
      rw [this] at huv; simp at huv
    have hu_pos : 0 < u := by
      by_contra h; rw [not_lt] at h
      rcases lt_or_eq_of_le h with hlt | heq
      · have : u * v < 0 := mul_neg_of_neg_of_pos hlt hv_pos
        linarith
      · rw [heq] at huv; simp at huv
    have hvle : v ≤ 819 := by
      have hu_ge1 : 1 ≤ u := hu_pos
      nlinarith [huv]
    have hule : u ≤ 819 := by
      have hv_ge1 : 1 ≤ v := hv_pos
      nlinarith [huv]
    -- Also u ≤ v since u + v = 4b ≥ 0 and v - u = 10a ≥ 0.
    have huv_order : u ≤ v := by
      have : v - u = 10 * (a : ℤ) := by simp [hu, hv]; ring
      have ha_nn : 0 ≤ (a : ℤ) := by positivity
      linarith
    -- Enumerate u × v with uv = 819 and u, v ∈ [1, 819].
    -- Divisors of 819 = 3²·7·13: 1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273, 819.
    -- Pairs (u, v) with u ≤ v, uv = 819, both positive:
    --   (1, 819), (3, 273), (7, 117), (9, 91), (13, 63), (21, 39).
    -- For each, we recover a, b: a = (v - u)/10, b = (u + v)/4.
    -- Only (7, 117) → a=11, b=31, n=20 and (13, 63) → a=5, b=19, n=12 give valid n.
    have hu_le_v : u ≤ v := huv_order
    -- Reduce to a decidable statement about (u, v) integers in range.
    have key : ∀ u v : ℤ, 0 < u → 0 < v → u ≤ v → u ≤ 819 → v ≤ 819 → u * v = 819 →
        ((u = 1 ∧ v = 819) ∨ (u = 3 ∧ v = 273) ∨ (u = 7 ∧ v = 117) ∨
         (u = 9 ∧ v = 91) ∨ (u = 13 ∧ v = 63) ∨ (u = 21 ∧ v = 39)) := by
      intro u v hu hv huv' huB hvB hp
      have hu_nn : 0 ≤ u := le_of_lt hu
      have hv_nn : 0 ≤ v := le_of_lt hv
      lift u to ℕ using hu_nn with uN
      lift v to ℕ using hv_nn with vN
      have hpN : uN * vN = 819 := by exact_mod_cast hp
      have hu0 : 0 < uN := by exact_mod_cast hu
      have hv0 : 0 < vN := by exact_mod_cast hv
      have hle : uN ≤ vN := by exact_mod_cast huv'
      -- Find uN among divisors.
      have huDiv : uN ∣ 819 := ⟨vN, hpN.symm⟩
      have hvDiv : vN ∣ 819 := ⟨uN, by linarith [hpN, Nat.mul_comm uN vN]⟩
      -- Decidable check: if uN ∣ 819 ∧ vN ∣ 819 ∧ uN * vN = 819 ∧ uN ≤ vN,
      -- then (uN, vN) is one of six pairs.
      have hfin : ∀ un ∈ Nat.divisors 819, ∀ vn ∈ Nat.divisors 819,
          un * vn = 819 → un ≤ vn →
          (un = 1 ∧ vn = 819) ∨ (un = 3 ∧ vn = 273) ∨ (un = 7 ∧ vn = 117) ∨
          (un = 9 ∧ vn = 91) ∨ (un = 13 ∧ vn = 63) ∨ (un = 21 ∧ vn = 39) := by
        native_decide
      have huMem : uN ∈ Nat.divisors 819 := by
        rw [Nat.mem_divisors]; exact ⟨huDiv, by norm_num⟩
      have hvMem : vN ∈ Nat.divisors 819 := by
        rw [Nat.mem_divisors]; exact ⟨hvDiv, by norm_num⟩
      rcases hfin uN huMem vN hvMem hpN hle with
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · right; left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · right; right; left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · right; right; right; left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · right; right; right; right; left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · right; right; right; right; right; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    rcases key u v hu_pos hv_pos hu_le_v hule hvle huv with
      ⟨hua, hva⟩ | ⟨hua, hva⟩ | ⟨hua, hva⟩ | ⟨hua, hva⟩ | ⟨hua, hva⟩ | ⟨hua, hva⟩
    all_goals (
      -- From u and v, determine a and b.
      have hsum : u + v = 4 * (b : ℤ) := by simp [hu, hv]; ring
      have hdiff : v - u = 10 * (a : ℤ) := by simp [hu, hv]; ring
      rw [hua, hva] at hsum hdiff
    )
    -- (1, 819): a = 81.8 not integer → contradiction
    -- (3, 273): 10a = 270, a = 27. 4b = 276, b = 69. n·12 = 27² + 119 = 848. 848/12 not integer.
    -- (7, 117): 10a = 110, a = 11. n·12 = 121+119 = 240, n = 20.
    -- (9, 91): 10a = 82 not divisible.
    -- (13, 63): 10a = 50, a = 5. n·12 = 25+119 = 144, n = 12.
    -- (21, 39): 10a = 18 not divisible.
    · -- u=1, v=819: 10a = 818, a not integer
      exfalso
      have : (10 : ℤ) ∣ 818 := ⟨a, by linarith⟩
      norm_num at this
    · -- u=3, v=273: a = 27, b = 69
      have ha_val : (a : ℤ) = 27 := by linarith
      have hb_val : (b : ℤ) = 69 := by linarith
      have hcast : (a : ℤ)^2 + 119 = 12 * n := by
        have hcast' : ((a^2 + 119 : ℕ) : ℤ) = ((12 * n : ℕ) : ℤ) := by exact_mod_cast ha.symm
        push_cast at hcast'; linarith
      have hne : (12 * n : ℤ) = 848 := by
        rw [← hcast, ha_val]; norm_num
      exfalso; omega
    · -- u=7, v=117: a = 11, b = 31; n = 20
      have ha_val : (a : ℤ) = 11 := by linarith
      have hb_val : (b : ℤ) = 31 := by linarith
      have hcast : (a : ℤ)^2 + 119 = 12 * n := by
        have hcast' : ((a^2 + 119 : ℕ) : ℤ) = ((12 * n : ℕ) : ℤ) := by exact_mod_cast ha.symm
        push_cast at hcast'; linarith
      have h12n : (12 * n : ℤ) = 240 := by rw [← hcast, ha_val]; norm_num
      right
      have : (n : ℤ) = 20 := by linarith
      exact_mod_cast this
    · -- u=9, v=91: 10a = 82, not divisible by 10
      exfalso
      have : (10 : ℤ) ∣ 82 := ⟨a, by linarith⟩
      norm_num at this
    · -- u=13, v=63: a = 5, b = 19; n = 12
      have ha_val : (a : ℤ) = 5 := by linarith
      have hb_val : (b : ℤ) = 19 := by linarith
      have hcast : (a : ℤ)^2 + 119 = 12 * n := by
        have hcast' : ((a^2 + 119 : ℕ) : ℤ) = ((12 * n : ℕ) : ℤ) := by exact_mod_cast ha.symm
        push_cast at hcast'; linarith
      have h12n : (12 * n : ℤ) = 144 := by rw [← hcast, ha_val]; norm_num
      left
      have : (n : ℤ) = 12 := by linarith
      exact_mod_cast this
    · -- u=21, v=39: 10a = 18, not divisible
      exfalso
      have : (10 : ℤ) ∣ 18 := ⟨a, by linarith⟩
      norm_num at this
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, ⟨5, by norm_num⟩, ⟨19, by norm_num⟩⟩
    · exact ⟨by norm_num, ⟨11, by norm_num⟩, ⟨31, by norm_num⟩⟩

end UK2013R1P4
