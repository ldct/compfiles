/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2019, Problem 7

Let `C = {4, 6, 8, 9, 10, …}` be the set of composite positive integers.
For `n ∈ C`, let `a n` be the smallest `k` such that `n ∣ k!`. Determine
whether the series `∑_{n ∈ C} (a n / n)^n` converges.

Answer: Yes, it converges.

We show that `a n / n ≤ 2/3` for every composite `n ≥ 5`. The single
term at `n = 4` (where `a 4 / 4 = 1`) is finite, so the series is
dominated by a geometric series.
-/

namespace Imc2019P7

/-- A composite positive integer: at least `4` and not prime. -/
def IsComposite (n : ℕ) : Prop := 4 ≤ n ∧ ¬ n.Prime

instance (n : ℕ) : Decidable (IsComposite n) := by
  unfold IsComposite; infer_instance

/-- For `n ≥ 1`, `n ∣ n!`, so the set of `k` with `n ∣ k!` is nonempty. -/
private lemma dvd_factorial_self {n : ℕ} (hn : 1 ≤ n) : n ∣ n.factorial :=
  Nat.dvd_factorial hn le_rfl

/-- `a n` is the smallest `k : ℕ` such that `n ∣ k!`, defined for any
`n ≥ 1` via `Nat.find`. For `n = 0` we set it to `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : 1 ≤ n then
    Nat.find (p := fun k => n ∣ k.factorial) ⟨n, dvd_factorial_self h⟩
  else 0

/-- For `n ≥ 1`, `a n` satisfies `n ∣ (a n)!`. -/
private lemma n_dvd_factorial_a {n : ℕ} (hn : 1 ≤ n) : n ∣ (a n).factorial := by
  unfold a
  rw [dif_pos hn]
  exact Nat.find_spec (p := fun k => n ∣ k.factorial) ⟨n, dvd_factorial_self hn⟩

/-- For `n ≥ 1`, `a n` is the minimum: if `n ∣ k!` then `a n ≤ k`. -/
private lemma a_le_of_dvd {n k : ℕ} (hn : 1 ≤ n) (hk : n ∣ k.factorial) : a n ≤ k := by
  unfold a
  rw [dif_pos hn]
  exact Nat.find_le hk

/-- The terms of the series, indexed over all natural numbers, with
non-composite indices contributing `0`. -/
noncomputable def term (n : ℕ) : ℝ :=
  if IsComposite n then ((a n : ℝ) / n) ^ n else 0

determine answer : Prop := Summable term

-- snip begin

/-- The terms are nonneg. -/
private lemma term_nonneg (n : ℕ) : 0 ≤ term n := by
  unfold term
  split_ifs with hn
  · apply pow_nonneg
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact_mod_cast Nat.zero_le _
  · exact le_refl 0

/-- For composite `n`, the smallest prime factor `p = minFac n` divides
`n`, and `p ≤ n / p`. -/
private lemma minFac_le_div_of_composite {n : ℕ} (h : IsComposite n) :
    n.minFac ≤ n / n.minFac := by
  apply Nat.minFac_le_div
  · linarith [h.1]
  · exact h.2

/-- The key bound: for composite `n ≥ 5`, `3 * a n ≤ 2 * n`. -/
private lemma a_bound {n : ℕ} (h : IsComposite n) (h5 : 5 ≤ n) :
    3 * a n ≤ 2 * n := by
  set p := n.minFac with hp_def
  have hn1 : 1 ≤ n := by linarith [h.1]
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hn_ne_one : n ≠ 1 := by linarith
  have hp_prime : p.Prime := Nat.minFac_prime hn_ne_one
  have hp_pos : 0 < p := hp_prime.pos
  have hp_two : 2 ≤ p := hp_prime.two_le
  set m := n / p with hm_def
  have hpm : p * m = n := Nat.mul_div_cancel' hp_dvd
  have hp_le_m : p ≤ m := minFac_le_div_of_composite h
  rcases lt_or_eq_of_le hp_le_m with hp_lt_m | hp_eq_m
  · -- p < m. Then n = p * m ∣ m! since p, m are distinct in [1, m].
    have hm_pos : 0 < m := lt_of_lt_of_le hp_pos hp_le_m
    have hp_le_m_pred : p ≤ m - 1 := by omega
    have h_p_dvd_pred_fact : p ∣ (m - 1).factorial :=
      Nat.dvd_factorial hp_pos hp_le_m_pred
    have h_m_fact_eq : m.factorial = m * (m - 1).factorial := by
      have hms : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hms]
      rw [Nat.factorial_succ]
      congr 1
      omega
    have hn_dvd : n ∣ m.factorial := by
      rw [h_m_fact_eq, ← hpm]
      have : m * p ∣ m * (m - 1).factorial :=
        mul_dvd_mul (dvd_refl m) h_p_dvd_pred_fact
      rw [mul_comm p m]
      exact this
    have ha_le_m : a n ≤ m := a_le_of_dvd hn1 hn_dvd
    have h2n : 2 * n = 2 * p * m := by rw [← hpm]; ring
    calc 3 * a n ≤ 3 * m := by linarith
      _ ≤ 2 * p * m := by nlinarith
      _ = 2 * n := h2n.symm
  · -- p = m, so n = p^2.
    have hn_eq : n = p * p := by rw [← hpm, ← hp_eq_m]
    have hp3 : 3 ≤ p := by
      by_contra hp_lt
      have hp_lt' : p < 3 := Nat.lt_of_not_le hp_lt
      have hp_eq_two : p = 2 := by omega
      rw [hp_eq_two] at hn_eq
      omega
    have h_n_dvd_2p_fact : n ∣ (2 * p).factorial := by
      have h2p_eq : 2 * p = (2 * p - 1) + 1 := by omega
      rw [h2p_eq, Nat.factorial_succ]
      have h_p_dvd_factor : p ∣ ((2 * p - 1) + 1) := by
        rw [show (2 * p - 1) + 1 = 2 * p from by omega]
        exact ⟨2, by ring⟩
      have hp_le_2p_minus_one : p ≤ 2 * p - 1 := by omega
      have h_p_dvd_other : p ∣ (2 * p - 1).factorial :=
        Nat.dvd_factorial hp_pos hp_le_2p_minus_one
      rw [hn_eq]
      exact mul_dvd_mul h_p_dvd_factor h_p_dvd_other
    have ha_le_2p : a n ≤ 2 * p := a_le_of_dvd hn1 h_n_dvd_2p_fact
    calc 3 * a n ≤ 3 * (2 * p) := by linarith
      _ = 6 * p := by ring
      _ ≤ 2 * p * p := by nlinarith
      _ = 2 * n := by rw [hn_eq]; ring

/-- For composite `n ≥ 5`, the term is bounded by `(2/3)^n`. -/
private lemma term_le {n : ℕ} (h : IsComposite n) (h5 : 5 ≤ n) :
    term n ≤ (2 / 3 : ℝ) ^ n := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by linarith : 0 < n)
  have hbound : 3 * a n ≤ 2 * n := a_bound h h5
  have hratio : ((a n : ℝ) / n) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 3)]
    have hbound' : (3 * a n : ℝ) ≤ 2 * n := by exact_mod_cast hbound
    linarith
  have h_nonneg : (0 : ℝ) ≤ (a n : ℝ) / n :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (by exact_mod_cast Nat.zero_le _)
  have hpow : ((a n : ℝ) / n) ^ n ≤ (2 / 3 : ℝ) ^ n :=
    pow_le_pow_left₀ h_nonneg hratio n
  show (if IsComposite n then ((a n : ℝ) / n) ^ n else 0) ≤ (2 / 3 : ℝ) ^ n
  rw [if_pos h]
  exact hpow

/-- The series is summable. -/
private lemma summable_term : Summable term := by
  -- Dominate by g n = (2/3)^n + (if n = 4 then term 4 else 0).
  set g : ℕ → ℝ := fun n => (2 / 3 : ℝ)^n + (if n = 4 then term 4 else 0) with hg_def
  have hgeo : Summable (fun n : ℕ => (2/3 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsingle : Summable (fun n : ℕ => if n = 4 then term 4 else (0 : ℝ)) :=
    summable_of_ne_finset_zero (s := {4}) (by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      simp [hx])
  have hg_sum : Summable g := hgeo.add hsingle
  apply Summable.of_nonneg_of_le term_nonneg ?_ hg_sum
  intro n
  by_cases hn4 : n = 4
  · subst hn4
    have hpos : (0 : ℝ) ≤ (2/3 : ℝ)^4 := by positivity
    show term 4 ≤ (2/3)^4 + (if (4 : ℕ) = 4 then term 4 else 0)
    rw [if_pos rfl]
    linarith
  · show term n ≤ (2/3)^n + (if n = 4 then term 4 else 0)
    rw [if_neg hn4, add_zero]
    by_cases hcomp : IsComposite n
    · have hn5 : 5 ≤ n := by
        rcases hcomp with ⟨h4, _⟩
        omega
      exact term_le hcomp hn5
    · unfold term
      rw [if_neg hcomp]
      positivity

problem imc2019_p7 : answer := summable_term

-- snip end

end Imc2019P7
