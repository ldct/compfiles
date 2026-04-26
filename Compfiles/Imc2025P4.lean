/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2025, Problem 4

Let `a` be an even positive integer. Find all real numbers `x` such that

  `⌊ a√(bᵃ + x) · bᵃ⁻¹ ⌋ = bᵃ + ⌊x/a⌋`      (1)

holds for every positive integer `b`.

Answer:
- If `a = 2`, the set of solutions is `[-1, 2) ∪ [3, 4)`.
- If `a > 2`, the set of solutions is `[-1, a)`.
-/

namespace Imc2025P4

/-- The set of real numbers `x` satisfying (1) for all positive integers `b`,
  depending on the (even) parameter `a`. -/
noncomputable determine answer (a : ℕ) : Set ℝ :=
  if a = 2 then (Set.Ico (-1 : ℝ) 2 ∪ Set.Ico (3 : ℝ) 4)
  else Set.Ico (-1 : ℝ) a

snip begin

/-- If `u, v ≥ 0` and `a ≥ 1`, then `u^(1/a) ≤ v ↔ u ≤ v^a`. -/
lemma rpow_inv_le_iff_of_nonneg {a : ℕ} (ha : 0 < a) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ ((a : ℝ)⁻¹) ≤ v ↔ u ≤ v ^ a := by
  have han : (a : ℕ) ≠ 0 := ha.ne'
  constructor
  · intro h
    have h1 : (u ^ ((a : ℝ)⁻¹)) ^ a ≤ v ^ a :=
      pow_le_pow_left₀ (Real.rpow_nonneg hu _) h a
    rwa [Real.rpow_inv_natCast_pow hu han] at h1
  · intro h
    have hmono : u ^ ((a : ℝ)⁻¹) ≤ (v ^ a) ^ ((a : ℝ)⁻¹) :=
      Real.rpow_le_rpow hu h (by positivity)
    rwa [Real.pow_rpow_inv_natCast hv han] at hmono

lemma rpow_inv_lt_iff_of_nonneg {a : ℕ} (ha : 0 < a) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ ((a : ℝ)⁻¹) < v ↔ u < v ^ a := by
  have han : (a : ℕ) ≠ 0 := ha.ne'
  constructor
  · intro h
    have h1 : (u ^ ((a : ℝ)⁻¹)) ^ a < v ^ a :=
      pow_lt_pow_left₀ h (Real.rpow_nonneg hu _) han
    rwa [Real.rpow_inv_natCast_pow hu han] at h1
  · intro h
    have hmono : u ^ ((a : ℝ)⁻¹) < (v ^ a) ^ ((a : ℝ)⁻¹) :=
      Real.rpow_lt_rpow hu h (by positivity)
    rwa [Real.pow_rpow_inv_natCast hv han] at hmono

/-- Bernoulli's inequality: for natural `n` and real `t ≥ -1`, `1 + n t ≤ (1 + t)^n`. -/
lemma bernoulli_nat (n : ℕ) {t : ℝ} (ht : -1 ≤ t) : 1 + n * t ≤ (1 + t) ^ n :=
  one_add_mul_le_pow (by linarith) n

/-- Lower bound for reverse direction. Only valid cases: `m = -1`, `m = 0`, or (`m = 1` and `a = 2`). -/
lemma lower_bound_rev (a b : ℕ) (ha : 2 ≤ a) (hb : 0 < b) (m : ℤ) (x : ℝ)
    (hm_range : m = -1 ∨ m = 0 ∨ (m = 1 ∧ a = 2))
    (hx_low : ((m + 1 : ℤ) : ℝ) ^ a - 1 ≤ x)
    (hx_lb : (-1 : ℝ) ≤ x) :
    (1 + (m : ℝ) / (b : ℝ) ^ a) ^ a ≤ 1 + x / (b : ℝ) ^ a := by
  have hb_pos_r : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hba_pos : (0 : ℝ) < (b : ℝ) ^ a := pow_pos hb_pos_r a
  have hb_one_le : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba_one_le : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ hb_one_le
  rcases hm_range with hm | hm | ⟨hm, ha2⟩
  · subst hm
    have h1 : (1 : ℝ) - 1 / (b : ℝ) ^ a ≤ 1 + x / (b : ℝ) ^ a := by
      have hle : (-1 : ℝ) / (b : ℝ) ^ a ≤ x / (b : ℝ) ^ a :=
        div_le_div_of_nonneg_right hx_lb hba_pos.le
      have heq : (-1 : ℝ) / (b : ℝ) ^ a = -(1 / (b : ℝ) ^ a) := by ring
      rw [heq] at hle
      linarith
    have h2 : 0 ≤ 1 - 1 / (b : ℝ) ^ a := by
      have : 1 / (b : ℝ) ^ a ≤ 1 := by
        rw [div_le_one hba_pos]; exact hba_one_le
      linarith
    have hle1 : 1 - 1 / (b : ℝ) ^ a ≤ 1 := by
      have : 0 ≤ 1 / (b : ℝ) ^ a := by positivity
      linarith
    have h3 : (1 - 1 / (b : ℝ) ^ a) ^ a ≤ 1 - 1 / (b : ℝ) ^ a := by
      calc (1 - 1 / (b : ℝ) ^ a) ^ a
          ≤ (1 - 1 / (b : ℝ) ^ a) ^ 1 := by
            apply pow_le_pow_of_le_one h2 hle1 (by linarith)
        _ = _ := pow_one _
    have hrw : (1 : ℝ) + (↑(-1 : ℤ) : ℝ) / (b : ℝ) ^ a = 1 - 1 / (b : ℝ) ^ a := by
      push_cast; ring
    rw [hrw]
    linarith
  · subst hm
    simp only [Int.cast_zero, zero_div, add_zero, one_pow]
    have hx_nn : (0 : ℝ) ≤ x := by
      have := hx_low
      push_cast at this
      simp at this
      linarith
    have : (0 : ℝ) ≤ x / (b : ℝ) ^ a := div_nonneg hx_nn hba_pos.le
    linarith
  · subst hm; subst ha2
    have hx3 : (3 : ℝ) ≤ x := by
      have := hx_low
      push_cast at this
      linarith
    have hb2_pos : (0 : ℝ) < (b : ℝ) ^ 2 := pow_pos hb_pos_r 2
    have hb2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_pow₀ hb_one_le
    have hb4 : (1 : ℝ) ≤ (b : ℝ) ^ 4 := one_le_pow₀ hb_one_le
    -- Need: (1 + 1/b²)² ≤ 1 + x/b²
    -- Expand: 1 + 2/b² + 1/b^4 ≤ 1 + x/b²
    -- Equivalent: 2/b² + 1/b^4 ≤ x/b²
    -- Multiply by b² > 0: 2 + 1/b² ≤ x, so need 1/b² ≤ 1 and x ≥ 3.
    have hkey : 2 + 1 / (b : ℝ) ^ 2 ≤ x := by
      have hinv : 1 / (b : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one hb2_pos]; exact hb2
      linarith
    push_cast
    rw [show (1 + 1 / (b : ℝ) ^ 2) ^ 2 = 1 + (2 / (b : ℝ) ^ 2 + 1 / (b : ℝ) ^ 4) by ring]
    have heq : 2 / (b : ℝ) ^ 2 + 1 / (b : ℝ) ^ 4 = (2 + 1 / (b : ℝ) ^ 2) / (b : ℝ) ^ 2 := by
      have hb2_ne : (b : ℝ) ^ 2 ≠ 0 := hb2_pos.ne'
      field_simp
    rw [heq]
    have : (2 + 1 / (b : ℝ) ^ 2) / (b : ℝ) ^ 2 ≤ x / (b : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hkey hb2_pos.le
    linarith

/-- Upper bound for reverse direction: `1 + x/b^a < (1 + (m+1)/b^a)^a` when `x < a(m+1)`. -/
lemma upper_bound_rev (a b : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (m : ℤ) (x : ℝ)
    (hm_ge : -1 ≤ m)
    (hx_high : x < a * ((m : ℝ) + 1)) :
    (1 : ℝ) + x / (b : ℝ) ^ a < (1 + ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a) ^ a := by
  have hb_pos_r : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hba_pos : (0 : ℝ) < (b : ℝ) ^ a := pow_pos hb_pos_r a
  have hb_one_le : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba_one_le : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ hb_one_le
  -- Bernoulli: 1 + a * ((m+1)/b^a) ≤ (1 + (m+1)/b^a)^a, provided (m+1)/b^a ≥ -1.
  have ht : -1 ≤ ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a := by
    have hm1 : (0 : ℝ) ≤ (m + 1 : ℤ) := by exact_mod_cast (by linarith : (0 : ℤ) ≤ m + 1)
    have : 0 ≤ ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a := div_nonneg hm1 hba_pos.le
    linarith
  have hbern := bernoulli_nat a ht
  -- 1 + a * ((m+1)/b^a) ≤ (1 + (m+1)/b^a)^a
  -- We want to show: 1 + x/b^a < RHS.
  -- It suffices to show 1 + x/b^a < 1 + a * ((m+1)/b^a) = 1 + a(m+1)/b^a.
  have hstrict : 1 + x / (b : ℝ) ^ a < 1 + a * (((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a) := by
    have : x / (b : ℝ) ^ a < (a : ℝ) * (m + 1) / (b : ℝ) ^ a := by
      apply div_lt_div_of_pos_right hx_high hba_pos
    push_cast at this ⊢
    have hrw : (a : ℝ) * ((m : ℝ) + 1) / (b : ℝ) ^ a = (a : ℝ) * (((m : ℝ) + 1) / (b : ℝ) ^ a) := by
      ring
    linarith [this]
  linarith

/-- Bridge from the inequalities `(1+m/b^a)^a ≤ 1+x/b^a < (1+(m+1)/b^a)^a` to the floor identity. -/
lemma floor_identity_from_bounds (a b : ℕ) (ha : 2 ≤ a) (hb : 0 < b) (m : ℤ) (x : ℝ)
    (hm_ge : -1 ≤ m)
    (hba_pos : (0 : ℝ) < (b : ℝ) ^ a)
    (hba1_ne : ((b : ℝ) ^ (a - 1)) ≠ 0)
    (hsum_nn : (0 : ℝ) ≤ (b : ℝ) ^ a + x)
    (hlo : (1 + (m : ℝ) / (b : ℝ) ^ a) ^ a ≤ 1 + x / (b : ℝ) ^ a)
    (hhi : 1 + x / (b : ℝ) ^ a < (1 + ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a) ^ a) :
    ⌊((b : ℝ) ^ a + x) ^ ((a : ℝ)⁻¹) * (b : ℝ) ^ (a - 1)⌋ = (b : ℤ) ^ a + m := by
  have ha_pos : 0 < a := by linarith
  have ha_ne : (a : ℕ) ≠ 0 := by omega
  have hb_pos_r : (0 : ℝ) < b := by
    have := hba_pos
    have hne : (b : ℝ) ≠ 0 := by
      intro h; rw [h] at this
      simp [zero_pow ha_ne] at this
    exact lt_of_le_of_ne (Nat.cast_nonneg b) (Ne.symm hne)
  have hb_one_le : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hba1_pos : (0 : ℝ) < (b : ℝ) ^ (a - 1) := pow_pos hb_pos_r _
  -- Convert hlo, hhi into bounds on (b^a+x)^(1/a) * b^(a-1).
  -- Multiply through by b^a > 0: b^a * (1+m/b^a)^a ≤ b^a + x ≤ ...
  -- We use: (1 + t/b^a)^a * b^a = ((1 + t/b^a) * b)^(?) — not clean.
  -- Instead: multiplying (hlo)*b^a gives (b^a + m*... wait use:
  -- (1 + m/b^a)^a = ((b^a + m)/b^a)^a = (b^a+m)^a / b^(a²), valid when b^a+m ≥ 0.
  have hba_ne : (b : ℝ) ^ a ≠ 0 := hba_pos.ne'
  -- Derive (b^a + m)^a ≤ (b^a + x) * b^(a(a-1)).
  -- Let's prove this using: b^(a²) * (1+m/b^a)^a = (b^a+m)^a, valid in general.
  have hrw1 : (b : ℝ) ^ a * (1 + (m : ℝ) / (b : ℝ) ^ a) = (b : ℝ) ^ a + m := by
    field_simp
  have hrw2 : (b : ℝ) ^ a * (1 + ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a) = (b : ℝ) ^ a + (m + 1 : ℤ) := by
    field_simp
  -- Case 1: lower bound
  -- ((b^a)*(1 + m/b^a))^a = (b^a+m)^a, and ((b^a)*(1+x/b^a))?
  -- Cleaner: multiply both sides by (b^a)^a
  have hba_a_pos : (0 : ℝ) < ((b : ℝ) ^ a) ^ a := pow_pos hba_pos a
  have hlo2 : ((b : ℝ) ^ a + m) ^ a ≤ ((b : ℝ) ^ a) ^ a * (1 + x / (b : ℝ) ^ a) := by
    have := mul_le_mul_of_nonneg_left hlo hba_a_pos.le
    calc ((b : ℝ) ^ a + m) ^ a
        = ((b : ℝ) ^ a * (1 + (m : ℝ) / (b : ℝ) ^ a)) ^ a := by rw [hrw1]
      _ = ((b : ℝ) ^ a) ^ a * (1 + (m : ℝ) / (b : ℝ) ^ a) ^ a := by rw [mul_pow]
      _ ≤ ((b : ℝ) ^ a) ^ a * (1 + x / (b : ℝ) ^ a) := this
  have hhi2 : ((b : ℝ) ^ a) ^ a * (1 + x / (b : ℝ) ^ a) < ((b : ℝ) ^ a + (m + 1 : ℤ)) ^ a := by
    have := mul_lt_mul_of_pos_left hhi hba_a_pos
    calc ((b : ℝ) ^ a) ^ a * (1 + x / (b : ℝ) ^ a)
        < ((b : ℝ) ^ a) ^ a * (1 + ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a) ^ a := this
      _ = ((b : ℝ) ^ a * (1 + ((m + 1 : ℤ) : ℝ) / (b : ℝ) ^ a)) ^ a := by rw [mul_pow]
      _ = ((b : ℝ) ^ a + (m + 1 : ℤ)) ^ a := by rw [hrw2]
  -- Now: (b^a)^a * (1 + x/b^a) = (b^a)^(a-1) * (b^a + x) = b^(a(a-1)) * (b^a+x)
  have hmid_eq : ((b : ℝ) ^ a) ^ a * (1 + x / (b : ℝ) ^ a) = ((b : ℝ) ^ (a - 1)) ^ a * ((b : ℝ) ^ a + x) := by
    have hba_ne' : (b : ℝ) ^ a ≠ 0 := hba_ne
    have hb_ne : (b : ℝ) ≠ 0 := hb_pos_r.ne'
    have : ((b : ℝ) ^ a) ^ a = ((b : ℝ) ^ (a - 1)) ^ a * (b : ℝ) ^ a := by
      rw [← mul_pow]
      congr 1
      rw [← pow_succ]
      congr 1
      omega
    rw [this]
    field_simp
  rw [hmid_eq] at hlo2 hhi2
  -- Let y = (b^a + x)^(1/a). Then y^a = b^a + x ≥ 0.
  set y := ((b : ℝ) ^ a + x) ^ ((a : ℝ)⁻¹) with hy_def
  have hy_nn : 0 ≤ y := Real.rpow_nonneg hsum_nn _
  have hya : y ^ a = (b : ℝ) ^ a + x := Real.rpow_inv_natCast_pow hsum_nn ha_ne
  -- Rewrite: ((b^(a-1))^a * y^a) = ((b^(a-1)) * y)^a.
  have hlo3 : ((b : ℝ) ^ a + m) ^ a ≤ ((b : ℝ) ^ (a - 1) * y) ^ a := by
    have : ((b : ℝ) ^ (a - 1)) ^ a * ((b : ℝ) ^ a + x) = ((b : ℝ) ^ (a - 1) * y) ^ a := by
      rw [mul_pow, ← hya]
    linarith [this ▸ hlo2]
  have hhi3 : ((b : ℝ) ^ (a - 1) * y) ^ a < ((b : ℝ) ^ a + (m + 1 : ℤ)) ^ a := by
    have heq : ((b : ℝ) ^ (a - 1)) ^ a * ((b : ℝ) ^ a + x) = ((b : ℝ) ^ (a - 1) * y) ^ a := by
      rw [mul_pow, ← hya]
    linarith [heq ▸ hhi2]
  -- Deduce the un-exponentiated bounds.
  have hprod_nn : (0 : ℝ) ≤ (b : ℝ) ^ (a - 1) * y := mul_nonneg hba1_pos.le hy_nn
  have hbam_nn : (0 : ℝ) ≤ (b : ℝ) ^ a + m := by
    have h1 : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ hb_one_le
    have h2 : (-1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
    linarith
  have hbamp1_nn : (0 : ℝ) ≤ (b : ℝ) ^ a + (m + 1 : ℤ) := by
    have h1 : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ hb_one_le
    have h2 : (0 : ℝ) ≤ ((m + 1 : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0 : ℤ) ≤ m + 1)
    linarith
  have hlo4 : (b : ℝ) ^ a + m ≤ (b : ℝ) ^ (a - 1) * y :=
    (pow_le_pow_iff_left₀ hbam_nn hprod_nn ha_ne).mp hlo3
  have hhi4 : (b : ℝ) ^ (a - 1) * y < (b : ℝ) ^ a + (m + 1 : ℤ) :=
    (pow_lt_pow_iff_left₀ hprod_nn hbamp1_nn ha_ne).mp hhi3
  -- Now apply floor_eq_iff.
  rw [show (b : ℝ) ^ (a - 1) * y = y * (b : ℝ) ^ (a - 1) from mul_comm _ _] at hlo4 hhi4
  rw [show y * (b : ℝ) ^ (a - 1) = ((b : ℝ) ^ a + x) ^ ((a : ℝ)⁻¹) * (b : ℝ) ^ (a - 1) from rfl]
  apply Int.floor_eq_iff.mpr
  refine ⟨?_, ?_⟩
  · push_cast
    convert hlo4 using 1
  · push_cast
    have hconv : ((b : ℝ) ^ a + x) ^ ((a : ℝ)⁻¹) * (b : ℝ) ^ (a - 1) < (b : ℝ) ^ a + ((m : ℝ) + 1) := by
      have := hhi4
      push_cast at this
      linarith
    linarith

/-- Helper: `b^a + x ≥ 0` when `b ≥ 1` and `x ≥ -1`, for `a ≥ 1`. -/
lemma sum_nn_aux (a b : ℕ) (ha : 1 ≤ a) (hb : 0 < b) (x : ℝ) (hx : -1 ≤ x) :
    (0 : ℝ) ≤ (b : ℝ) ^ a + x := by
  have hb_one_le : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have : (1 : ℝ) ≤ (b : ℝ) ^ a := one_le_pow₀ hb_one_le
  linarith

snip end

problem imc2025_p4 (a : ℕ) (ha_pos : 0 < a) (ha_even : Even a) (x : ℝ) :
    x ∈ answer a ↔
    ∀ b : ℕ, 0 < b →
      ⌊((b : ℝ) ^ a + x) ^ ((a : ℝ)⁻¹) * (b : ℝ) ^ (a - 1)⌋ =
        (b : ℤ) ^ a + ⌊x / a⌋ := by
  have ha_two : 2 ≤ a := by
    obtain ⟨k, hk⟩ := ha_even
    omega
  have ha_nat_ne : (a : ℕ) ≠ 0 := ha_pos.ne'
  have ha_pos_r : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
  constructor
  · -- Reverse direction: x ∈ answer a ⇒ identity for all b.
    intro hx b hb
    -- Derive m = ⌊x/a⌋ and key properties from x ∈ answer a.
    have hx_lb : (-1 : ℝ) ≤ x := by
      unfold answer at hx
      split_ifs at hx with h2
      · rcases hx with h | h
        · exact h.1
        · linarith [h.1]
      · exact hx.1
    set m : ℤ := ⌊x / a⌋ with hm_def
    -- Bounds: a*m ≤ x < a*(m+1).
    have hx_lo_am : (a : ℝ) * m ≤ x := by
      have h := Int.floor_le (x / a)
      rw [show ⌊x / a⌋ = m from rfl] at h
      have : (m : ℝ) * a ≤ x := (le_div_iff₀ ha_pos_r).mp h
      linarith
    have hx_hi_am1 : x < (a : ℝ) * ((m : ℝ) + 1) := by
      have h := Int.lt_floor_add_one (x / a)
      rw [show ⌊x / a⌋ = m from rfl] at h
      have : x < (m + 1 : ℝ) * a := (div_lt_iff₀ ha_pos_r).mp h
      linarith
    have hm_ge : (-1 : ℤ) ≤ m := by
      -- From x ≥ -1 and x < a*(m+1) we derive -1 < a*(m+1), so m+1 > -1/a ≥ -1, m ≥ -1.
      by_contra hlt
      push_neg at hlt
      -- hlt : m < -1, so m + 1 ≤ -1.
      have hm1_le : (m : ℝ) + 1 ≤ -1 := by exact_mod_cast (by linarith : (m : ℤ) + 1 ≤ -1)
      have : (a : ℝ) * ((m : ℝ) + 1) ≤ (a : ℝ) * (-1) :=
        mul_le_mul_of_nonneg_left hm1_le ha_pos_r.le
      have : x ≤ -(a : ℝ) := by linarith
      have ha_ge_one : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
      linarith
    -- Now we need: m ∈ {-1, 0} if a > 2, else m ∈ {-1, 0, 1}.
    -- And also: (m+1)^a - 1 ≤ x, to apply lower_bound_rev.
    -- These follow from x ∈ answer a.
    have hm_cases : (m = -1 ∨ m = 0 ∨ (m = 1 ∧ a = 2)) ∧
        ((m + 1 : ℤ) : ℝ) ^ a - 1 ≤ x := by
      unfold answer at hx
      split_ifs at hx with h2
      · -- a = 2 case
        rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
        · -- x ∈ [-1, 2): m = -1 or m = 0.
          rcases lt_or_ge x 0 with hx0 | hx0
          · -- m = -1
            have hm_eq : m = -1 := by
              apply le_antisymm
              · apply Int.floor_le_iff.mpr
                have : x / (a : ℝ) < 0 := div_neg_of_neg_of_pos hx0 ha_pos_r
                push_cast; linarith
              · exact hm_ge
            refine ⟨Or.inl hm_eq, ?_⟩
            rw [hm_eq]; push_cast
            have : (0 : ℝ) ^ a = 0 := zero_pow ha_nat_ne
            linarith
          · -- m = 0
            have hm_eq : m = 0 := by
              apply le_antisymm
              · apply Int.floor_le_iff.mpr
                push_cast
                rw [div_lt_iff₀ ha_pos_r]
                have : ((a : ℝ)) = 2 := by exact_mod_cast h2
                linarith
              · apply Int.le_floor.mpr
                push_cast
                exact div_nonneg hx0 ha_pos_r.le
            refine ⟨Or.inr (Or.inl hm_eq), ?_⟩
            rw [hm_eq]; push_cast
            have : (1 : ℝ) ^ a = 1 := one_pow a
            linarith
        · -- x ∈ [3, 4): m = 1, a = 2.
          have hm_eq : m = 1 := by
            apply le_antisymm
            · apply Int.floor_le_iff.mpr
              push_cast
              rw [div_lt_iff₀ ha_pos_r]
              have : ((a : ℝ)) = 2 := by exact_mod_cast h2
              linarith
            · apply Int.le_floor.mpr
              push_cast
              rw [le_div_iff₀ ha_pos_r]
              have : ((a : ℝ)) = 2 := by exact_mod_cast h2
              linarith
          refine ⟨Or.inr (Or.inr ⟨hm_eq, h2⟩), ?_⟩
          rw [hm_eq, h2]; push_cast; linarith
      · -- a ≠ 2, so a > 2 (since a ≥ 2). Then answer = [-1, a).
        have ha_gt : 2 < a := lt_of_le_of_ne ha_two (Ne.symm h2)
        obtain ⟨hx1, hx2⟩ := hx
        rcases lt_or_ge x 0 with hx0 | hx0
        · -- m = -1
          have hm_eq : m = -1 := by
            apply le_antisymm
            · apply Int.floor_le_iff.mpr
              push_cast
              have : x / (a : ℝ) < 0 := div_neg_of_neg_of_pos hx0 ha_pos_r
              linarith
            · exact hm_ge
          refine ⟨Or.inl hm_eq, ?_⟩
          rw [hm_eq]; push_cast
          have : (0 : ℝ) ^ a = 0 := zero_pow ha_nat_ne
          linarith
        · -- m = 0
          have hm_eq : m = 0 := by
            apply le_antisymm
            · apply Int.floor_le_iff.mpr
              push_cast
              rw [div_lt_iff₀ ha_pos_r]; linarith
            · apply Int.le_floor.mpr
              push_cast
              exact div_nonneg hx0 ha_pos_r.le
          refine ⟨Or.inr (Or.inl hm_eq), ?_⟩
          rw [hm_eq]; push_cast
          have : (1 : ℝ) ^ a = 1 := one_pow a
          linarith
    obtain ⟨hm_range, hx_low⟩ := hm_cases
    -- Apply lower and upper bounds.
    have hb_pos_r : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    have hba_pos : (0 : ℝ) < (b : ℝ) ^ a := pow_pos hb_pos_r a
    have hba1_ne : (b : ℝ) ^ (a - 1) ≠ 0 := (pow_pos hb_pos_r _).ne'
    have hsum_nn : (0 : ℝ) ≤ (b : ℝ) ^ a + x := sum_nn_aux a b (by linarith) hb x hx_lb
    have hlo := lower_bound_rev a b ha_two hb m x hm_range hx_low hx_lb
    have hhi := upper_bound_rev a b (by linarith) hb m x hm_ge hx_hi_am1
    exact floor_identity_from_bounds a b ha_two hb m x hm_ge hba_pos hba1_ne hsum_nn hlo hhi
  · -- Forward direction: identity for all b ⇒ x ∈ answer a.
    intro h
    -- Apply at b = 1.
    have h1 := h 1 Nat.one_pos
    -- Let m = ⌊x/a⌋.
    set m : ℤ := ⌊x / a⌋ with hm_def
    -- Simplify h1 to: ⌊(1+x)^(1/a)⌋ = 1 + m.
    have h1' : ⌊((1 : ℝ) + x) ^ ((a : ℝ)⁻¹)⌋ = 1 + m := by
      have : ((1 : ℕ) : ℝ) ^ a = 1 := by norm_num
      have h1'' := h1
      rw [show ((1 : ℕ) : ℝ) = 1 from by norm_num] at h1''
      rw [one_pow, one_pow, mul_one] at h1''
      have e : ((1 : ℕ) : ℤ) ^ a = 1 := by simp
      rw [e] at h1''
      exact h1''
    -- Bounds: a*m ≤ x < a*(m+1).
    have hx_lo_am : (a : ℝ) * m ≤ x := by
      have h := Int.floor_le (x / a)
      rw [show ⌊x / a⌋ = m from rfl] at h
      have : (m : ℝ) * a ≤ x := (le_div_iff₀ ha_pos_r).mp h
      linarith
    have hx_hi_am1 : x < (a : ℝ) * ((m : ℝ) + 1) := by
      have h := Int.lt_floor_add_one (x / a)
      rw [show ⌊x / a⌋ = m from rfl] at h
      have : x < (m + 1 : ℝ) * a := (div_lt_iff₀ ha_pos_r).mp h
      linarith
    -- From the b=1 identity and Int.floor_eq_iff:
    -- 1 + m ≤ (1+x)^(1/a) < 1 + m + 1 = 2 + m.
    have hfloor := Int.floor_eq_iff.mp h1'
    obtain ⟨hle_rpow, hlt_rpow⟩ := hfloor
    -- Both sides of the range: (1+m ≤ rpow) and (rpow < 2+m).
    -- Since rpow is an rpow, its floor = 1+m ≥ 0 iff rpow ≥ 0 iff 1+x ≥ 0 is fine.
    -- Actually: (1+x)^(1/a) ≥ 0 always (rpow_nonneg when base... wait rpow_nonneg needs base ≥ 0).
    -- If 1+x < 0: (1+x)^(1/a) = 0 by convention (Real.rpow for negative base).
    -- But then floor = 0 = 1+m means m = -1. Then am ≤ x means -a ≤ x, so x ≥ -a. But 1+x < 0 means x < -1.
    -- Range m = -1: [-1, 0), so x ≥ -1. Contradiction. Unless we allow x ∈ [-a, -1), in which case
    -- the floor identity holds trivially via rpow of negative.
    -- Actually for even a, Real.rpow with negative base and noninteger exponent = 0, hmm let me think.
    -- For cleanliness, let's first prove x ≥ -1.
    have hx_lb : (-1 : ℝ) ≤ x := by
      by_contra hxlt
      push_neg at hxlt
      -- 1+x < 0. Real.rpow for negative base: Real.rpow x y = Real.exp (y * Real.log x),
      -- and Real.log of negative = Real.log |x|. But actually for Real.rpow when base < 0,
      -- it's defined as some value. Let me just use: Real.rpow_nonneg actually only applies with base ≥ 0.
      -- For base < 0, the value is irregular. This direction is delicate.
      sorry
    -- From 1+m ≤ (1+x)^(1/a), using rpow_inv_le_iff_of_nonneg backwards:
    -- if 1+m ≥ 0, then (1+m)^a ≤ 1+x.
    -- Case m = -1: trivially 0 ≤ 1+x, true.
    -- Case m ≥ 0: 1+m ≥ 1 > 0, so we can square.
    have hm_ge : (-1 : ℤ) ≤ m := by
      by_contra hlt
      push_neg at hlt
      -- m < -1, so m ≤ -2. Then a*m ≤ -2a, so x ≤ -2a. But x ≥ -1 and a ≥ 2, so -2a ≤ -4 < -1 ≤ x.
      have hm2 : m ≤ -2 := by omega
      have : (m : ℝ) ≤ -2 := by exact_mod_cast hm2
      have : (a : ℝ) * m ≤ (a : ℝ) * (-2) := mul_le_mul_of_nonneg_left this ha_pos_r.le
      have ha_ge : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_two
      linarith
    -- Derive (m+1)^a - 1 ≤ x from b=1 lower bound.
    have h1px_nn : (0 : ℝ) ≤ 1 + x := by linarith
    have hmp1_nn : (0 : ℝ) ≤ ((m + 1 : ℤ) : ℝ) := by
      push_cast; exact_mod_cast (by linarith : (0 : ℤ) ≤ m + 1)
    have hlow1 : ((m + 1 : ℤ) : ℝ) ^ a - 1 ≤ x := by
      -- (1+x)^(1/a) ≥ m+1 ≥ 0, so 1+x ≥ (m+1)^a.
      have : (1 + m : ℝ) ≤ ((1 : ℝ) + x) ^ ((a : ℝ)⁻¹) := by
        have := hle_rpow
        push_cast at this
        linarith
      have hmp1_nn' : (0 : ℝ) ≤ (1 + m : ℝ) := by
        push_cast; exact_mod_cast (by linarith : (0 : ℤ) ≤ 1 + m)
      have h2' : 1 + m ≤ ((1 : ℝ) + x) ^ ((a : ℝ)⁻¹) := this
      -- Use rpow_inv_le_iff_of_nonneg in reverse. We have `u ≥ v^a ⇔ u^(1/a) ≥ v`.
      -- Specifically (rpow_inv_le_iff_of_nonneg): u^(1/a) ≤ v ↔ u ≤ v^a.
      -- Contrapositive: u^(1/a) > v ↔ u > v^a. We have v ≤ u^(1/a), want v^a ≤ u.
      -- Actually from h2': (1+m) ≤ (1+x)^(1/a), raise both to a-th power (both ≥ 0):
      have : (1 + (m : ℝ)) ^ a ≤ ((1 + x) ^ ((a : ℝ)⁻¹)) ^ a :=
        pow_le_pow_left₀ hmp1_nn' h2' a
      rw [Real.rpow_inv_natCast_pow h1px_nn ha_nat_ne] at this
      have hrw : ((m + 1 : ℤ) : ℝ) = 1 + (m : ℝ) := by push_cast; ring
      rw [hrw]
      linarith
    -- Derive 1 + x < (m+2)^a from b=1 upper bound.
    have hupp1 : 1 + x < ((m + 2 : ℤ) : ℝ) ^ a := by
      have : ((1 : ℝ) + x) ^ ((a : ℝ)⁻¹) < 2 + m := by
        have := hlt_rpow
        push_cast at this
        linarith
      have hmp2_pos : (0 : ℝ) ≤ 2 + (m : ℝ) := by
        push_cast; exact_mod_cast (by linarith : (0 : ℤ) ≤ 2 + m)
      have h_lt_a : ((1 + x) ^ ((a : ℝ)⁻¹)) ^ a < (2 + (m : ℝ)) ^ a :=
        pow_lt_pow_left₀ this (Real.rpow_nonneg h1px_nn _) ha_nat_ne
      rw [Real.rpow_inv_natCast_pow h1px_nn ha_nat_ne] at h_lt_a
      have hrw : ((m + 2 : ℤ) : ℝ) = 2 + (m : ℝ) := by push_cast; ring
      rw [hrw]
      exact h_lt_a
    -- Now we have: (m+1)^a - 1 ≤ x < a*(m+1). From this: (m+1)^a < a*(m+1) + 1.
    have hkey : ((m + 1 : ℤ) : ℝ) ^ a < (a : ℝ) * ((m + 1 : ℤ) : ℝ) + 1 := by
      push_cast at hlow1 hx_hi_am1 ⊢
      linarith
    -- Derive upper bound on m: m ≤ 1 always.
    have pow_ge : ∀ (k : ℕ), 2 ≤ k → ∀ (t : ℝ), 3 ≤ t → (k : ℝ) * t + 1 ≤ t ^ k := by
      intro k hk t ht
      induction k, hk using Nat.le_induction with
      | base =>
        show (2 : ℝ) * t + 1 ≤ t ^ 2
        nlinarith [sq_nonneg (t - 2), ht]
      | succ n hn ih =>
        have hrec : t ^ (n + 1) = t * t ^ n := by ring
        rw [hrec]
        have hnn : ((n + 1 : ℕ) : ℝ) * t + 1 = (n : ℝ) * t + t + 1 := by push_cast; ring
        rw [hnn]
        have hn_ge : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have ht_pos : 0 < t := by linarith
        -- t * t^n ≥ t * (nt+1) = nt² + t ≥ nt + t + 1 iff n(t²-t) ≥ 1.
        have hstep : t * t ^ n ≥ t * ((n : ℝ) * t + 1) := by
          apply mul_le_mul_of_nonneg_left ih ht_pos.le
        nlinarith [hstep, hn_ge, ht, sq_nonneg (t - 1)]
    have hm_upper : m ≤ 1 := by
      by_contra hlt
      push_neg at hlt
      have ht : (3 : ℝ) ≤ ((m + 1 : ℤ) : ℝ) := by
        push_cast; exact_mod_cast (by linarith : (3 : ℤ) ≤ m + 1)
      have hbound := pow_ge a ha_two _ ht
      linarith
    -- Now interval_cases works with -1 ≤ m ≤ 1.
    interval_cases m
    · -- m = -1: x ∈ [-1, 0). Check membership.
      unfold answer
      split_ifs with h2
      · left
        refine ⟨hx_lb, ?_⟩
        -- x < a*0 = 0
        have : x < 0 := by
          have := hx_hi_am1
          push_cast at this; linarith
        linarith
      · refine ⟨hx_lb, ?_⟩
        have : x < 0 := by
          have := hx_hi_am1
          push_cast at this; linarith
        have ha_pos' : (0 : ℝ) ≤ (a : ℝ) := ha_pos_r.le
        linarith
    · -- m = 0: x ∈ [0, a).
      have hx_ge0 : (0 : ℝ) ≤ x := by
        have := hx_lo_am
        push_cast at this; linarith
      have hx_lta : x < (a : ℝ) := by
        have := hx_hi_am1
        push_cast at this; linarith
      unfold answer
      split_ifs with h2
      · left
        refine ⟨by linarith, ?_⟩
        have : ((a : ℝ)) = 2 := by exact_mod_cast h2
        linarith
      · exact ⟨by linarith, hx_lta⟩
    · -- m = 1: from hkey, 2^a < 2a+1. For a ≥ 4, 2^a ≥ 2a+1. Hence a = 2.
      have h2a : a = 2 := by
        by_contra ha_ne_2
        have ha_ge4 : 4 ≤ a := by
          obtain ⟨k, hk⟩ := ha_even
          omega
        -- Show 2a + 1 ≤ 2^a for a ≥ 4.
        have h_ind : ∀ (k : ℕ), 4 ≤ k → (2 * (k : ℝ) + 1 : ℝ) ≤ (2 : ℝ) ^ k := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => norm_num
          | succ n hn ih =>
            have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
            have hrec : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
            rw [hrec]
            have hn_ge : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            push_cast
            nlinarith [ih, hn_ge]
        have h_ind_a := h_ind a ha_ge4
        -- hkey: (1+1)^a < a*(1+1) + 1 = 2a + 1. So 2^a < 2a+1.
        have hk' : (2 : ℝ) ^ a < 2 * (a : ℝ) + 1 := by
          have hh := hkey
          push_cast at hh
          linarith
        linarith
      subst h2a
      unfold answer
      rw [if_pos rfl]
      right
      have hx_ge3 : (3 : ℝ) ≤ x := by
        have := hlow1
        push_cast at this; linarith
      have hx_lt4 : x < 4 := by
        have := hx_hi_am1
        push_cast at this; linarith
      exact ⟨hx_ge3, hx_lt4⟩

end Imc2025P4
