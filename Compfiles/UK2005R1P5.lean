/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2005, Round 1, Problem 5

Let S be a set of rational numbers with the following properties:
i) 1/2 ∈ S;
ii) If x ∈ S, then both 1/(x+1) ∈ S and x/(x+1) ∈ S.
Prove that S contains all rational numbers in the interval 0 < x < 1.
-/

namespace UK2005R1P5

problem uk2005_r1_p5 (S : Set ℚ)
    (h1 : (1 / 2 : ℚ) ∈ S)
    (h2 : ∀ x ∈ S, 1 / (x + 1) ∈ S ∧ x / (x + 1) ∈ S) :
    ∀ q : ℚ, 0 < q → q < 1 → q ∈ S := by
  -- Strong induction on p + q for coprime p, q with 0 < p < q.
  suffices h : ∀ N : ℕ, ∀ p q : ℕ, 0 < p → p < q → p + q ≤ N →
                Nat.Coprime p q → ((p : ℚ) / q) ∈ S by
    intro r hr_pos hr_lt
    have hr_num_pos : 0 < r.num := Rat.num_pos.mpr hr_pos
    have hr_den_pos : 0 < r.den := r.pos
    set p := r.num.toNat with hp_def
    have hp_pos : 0 < p := by
      rw [hp_def]; omega
    have hp_eq : (p : ℤ) = r.num := Int.toNat_of_nonneg (le_of_lt hr_num_pos)
    have hpq_lt : p < r.den := by
      have h3 : r.num < (r.den : ℤ) := by
        have : (r.num : ℚ) / r.den < 1 := by rw [Rat.num_div_den]; exact hr_lt
        have hden_pos : (0 : ℚ) < r.den := by exact_mod_cast hr_den_pos
        rw [div_lt_one hden_pos] at this
        exact_mod_cast this
      have : (p : ℤ) < r.den := by rw [hp_eq]; exact h3
      exact_mod_cast this
    have hnat_abs : r.num.natAbs = p := by
      rw [hp_def]
      exact Int.natAbs_of_nonneg (le_of_lt hr_num_pos) |>.symm ▸ rfl
    have hcoprime : Nat.Coprime p r.den := by
      rw [← hnat_abs]
      exact r.reduced
    have : ((p : ℚ) / r.den) = r := by
      rw [show ((p : ℚ) = (r.num : ℚ)) from by exact_mod_cast hp_eq]
      exact Rat.num_div_den r
    rw [← this]
    exact h (p + r.den) p r.den hp_pos hpq_lt (le_refl _) hcoprime
  -- Now prove the strong induction.
  intro N
  induction N with
  | zero =>
    intro p q hp hpq hsum _
    omega
  | succ N ih =>
    intro p q hp hpq hsum hcop
    -- Case p = q - p: then p/q = 1/2 (by coprimality).
    rcases lt_trichotomy (2 * p) q with h2p | h2p | h2p
    · -- p < q - p: came from x/(x+1) with x = p/(q - 2p).
      -- x/(x+1) = (p/(q-2p))/(p/(q-2p) + 1) = (p/(q-2p))/((q - p)/(q - 2p)) = p/(q-p).
      -- Wait that gives p/(q - p), not p/q. Let me redo.
      -- Actually: x ↦ x/(x+1) maps a/b (with a,b coprime) to a/(a+b). So if a/(a+b) = p/q,
      -- then a = p, a + b = q, b = q - p. So x = p/(q - p).
      -- Need p < q - p for this to be in (0,1) — yes when 2p < q.
      have h3 : p < q - p := by omega
      have hcop' : Nat.Coprime p (q - p) := by
        have hle : p ≤ q := le_of_lt hpq
        have hq_eq : q = p + (q - p) := (Nat.add_sub_cancel' hle).symm
        have := (Nat.coprime_self_add_right (m := p) (n := q - p)).mpr
        rw [hq_eq] at hcop
        exact (Nat.coprime_self_add_right).mp hcop
      have hx_in : ((p : ℚ) / ((q - p : ℕ) : ℚ)) ∈ S := by
        apply ih p (q - p) hp h3 _ hcop'
        omega
      have hstep := (h2 _ hx_in).2
      have hqp_nat : 0 < q - p := by omega
      have hqp : (0 : ℚ) < ((q - p : ℕ) : ℚ) := by exact_mod_cast hqp_nat
      have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q from by omega)
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
      have hqp_eq : ((q - p : ℕ) : ℚ) = (q : ℚ) - p := by
        have hle : p ≤ q := le_of_lt hpq
        rw [Nat.cast_sub hle]
      have h_qp_ne : ((q - p : ℕ) : ℚ) ≠ 0 := ne_of_gt hqp
      have hq_ne : (q : ℚ) ≠ 0 := ne_of_gt hq_pos
      have hp_ne : (p : ℚ) ≠ 0 := by
        have : (0 : ℚ) < p := by exact_mod_cast hp
        exact ne_of_gt this
      have hsubeq : ((p : ℚ) / ((q - p : ℕ) : ℚ)) / ((p : ℚ) / ((q - p : ℕ) : ℚ) + 1) = (p : ℚ) / q := by
        set A := ((q - p : ℕ) : ℚ)
        have hA_ne : A ≠ 0 := h_qp_ne
        have key : ((p : ℚ) / A) / ((p : ℚ) / A + 1) = (p : ℚ) / ((p : ℚ) + A) := by
          rw [div_add_one hA_ne]
          exact div_div_div_cancel_right₀ hA_ne _ _
        rw [key]
        congr 1
        rw [hqp_eq]; ring
      rw [← hsubeq]
      exact hstep
    · -- 2p = q: then by coprimality, p = 1, q = 2.
      have hpq1 : p = 1 := by
        have hd : p ∣ q := ⟨2, by omega⟩
        have hd' : Nat.gcd p q = p := Nat.gcd_eq_left hd
        rw [Nat.Coprime] at hcop
        omega
      have hq2 : q = 2 := by omega
      rw [hpq1, hq2]
      simpa using h1
    · -- 2p > q: came from 1/(x+1) with x = (q-p)/p.
      -- 1/(x+1) = 1/((q-p)/p + 1) = 1/(q/p) = p/q. ✓
      have h3 : 0 < q - p := by omega
      have h4 : q - p < p := by omega
      have hcop' : Nat.Coprime (q - p) p := by
        have hpq_le : p ≤ q := le_of_lt hpq
        have hq_eq : q = (q - p) + p := (Nat.sub_add_cancel hpq_le).symm
        rw [hq_eq] at hcop
        have hcop2 : Nat.Coprime (q - p + p) p := hcop.symm
        exact (Nat.coprime_add_self_left).mp hcop2
      have hx_in : (((q - p : ℕ) : ℚ) / p) ∈ S := by
        apply ih (q - p) p h3 h4 _ hcop'
        omega
      have hstep := (h2 _ hx_in).1
      -- 1 / (((q-p)/p) + 1) = p/q.
      have hp_pos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
      have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q from by omega)
      have hqp_eq : ((q - p : ℕ) : ℚ) = (q : ℚ) - p := by
        have hpq_le : p ≤ q := le_of_lt hpq
        rw [Nat.cast_sub hpq_le]
      have hsubeq : (1 : ℚ) / (((q - p : ℕ) : ℚ) / p + 1) = (p : ℚ) / q := by
        have hp_ne : (p : ℚ) ≠ 0 := ne_of_gt hp_pos
        rw [div_add_one hp_ne]
        rw [one_div_div]
        congr 1
        rw [hqp_eq]; ring
      rw [← hsubeq]
      exact hstep

end UK2005R1P5
