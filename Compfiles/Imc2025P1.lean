/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 1

Let `P ∈ ℝ[x]` be a polynomial with real coefficients, and suppose `deg(P) ≥ 2`.
For every `x ∈ ℝ`, let `ℓ_x ⊆ ℝ²` denote the line tangent to the graph of `P`
at the point `(x, P(x))`.

(a) Suppose that the degree of `P` is odd. Show that `⋃_{x ∈ ℝ} ℓ_x = ℝ²`.

(b) Does there exist a polynomial of even degree for which the above equality
    still holds?

Answer to (b): No.
-/

namespace Imc2025P1

open Polynomial

/-- The tangent line to the graph of `P` at the point `(x, P(x))`. -/
def tangentLine (P : ℝ[X]) (x : ℝ) : Set (ℝ × ℝ) :=
  {q | q.2 = (P.derivative.eval x) * (q.1 - x) + P.eval x}

snip begin

/-- A real polynomial of positive degree has values of both signs at ±∞ iff it has odd natDegree.
In particular, odd-degree polynomials over the reals have a root. -/
lemma exists_root_of_odd_natDegree {Q : ℝ[X]} (hodd : Odd Q.natDegree) :
    ∃ r : ℝ, Q.eval r = 0 := by
  have hdeg_pos : 0 < Q.natDegree := by rcases hodd with ⟨k, hk⟩; omega
  have hQ_ne_zero : Q ≠ 0 := fun h => by simp [h] at hdeg_pos
  have hdegree_pos : 0 < Q.degree := natDegree_pos_iff_degree_pos.mp hdeg_pos
  have hlc_ne : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ_ne_zero
  have hcont : Continuous (fun x => Q.eval x) := Q.continuous
  -- We show there exist a, b with Q.eval a < 0 < Q.eval b, then apply IVT.
  suffices h : ∃ a b : ℝ, Q.eval a < 0 ∧ 0 < Q.eval b by
    obtain ⟨a, b, ha, hb⟩ := h
    rcases lt_or_ge a b with hlt | hle
    · obtain ⟨r, _, hr⟩ := intermediate_value_Ioo hlt.le hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (Q.eval a) (Q.eval b) from ⟨ha, hb⟩)
      exact ⟨r, hr⟩
    · have hlt' : b < a := by
        rcases lt_or_eq_of_le hle with h' | h'
        · exact h'
        · exfalso; subst h'; linarith
      obtain ⟨r, _, hr⟩ := intermediate_value_Ioo' hlt'.le hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (Q.eval a) (Q.eval b) from ⟨ha, hb⟩)
      exact ⟨r, hr⟩
  -- Consider Q' := Q.comp (-X), whose evaluation at x equals Q.eval (-x).
  -- Its natDegree is the same, but its leadingCoeff is negated since natDegree is odd.
  set Q' : ℝ[X] := Q.comp (-X) with hQ'
  have hQ'_natDeg : Q'.natDegree = Q.natDegree := by simp [Q', natDegree_comp]
  have hQ'_degree_pos : 0 < Q'.degree := by
    rw [← natDegree_pos_iff_degree_pos, hQ'_natDeg]; exact hdeg_pos
  have hQ'_lc : Q'.leadingCoeff = -Q.leadingCoeff := by
    rw [hQ', comp_neg_X_leadingCoeff_eq, Odd.neg_one_pow hodd]
    ring
  have hQ'_eval : ∀ x, Q'.eval x = Q.eval (-x) := by
    intro x; simp [Q', eval_comp]
  -- Case on sign of leading coefficient.
  rcases lt_or_gt_of_ne hlc_ne with hneg | hpos
  · -- leadingCoeff Q < 0: so leadingCoeff Q' > 0
    have hTop : Filter.Tendsto (fun x => Q.eval x) Filter.atTop Filter.atBot :=
      Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hdegree_pos hneg.le
    have hQ'_lc_nonneg : 0 ≤ Q'.leadingCoeff := by rw [hQ'_lc]; linarith
    have hTop' : Filter.Tendsto (fun x => Q'.eval x) Filter.atTop Filter.atTop :=
      Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Q' hQ'_degree_pos hQ'_lc_nonneg
    -- Turn Q' behavior into Q on atBot.
    have hBot : Filter.Tendsto (fun x => Q.eval x) Filter.atBot Filter.atTop := by
      have hh : Filter.Tendsto (fun x => Q.eval (-x)) Filter.atTop Filter.atTop := by
        convert hTop' using 1; ext x; exact (hQ'_eval x).symm
      have hneg_tendsto : Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop :=
        Filter.tendsto_neg_atBot_atTop
      have := hh.comp hneg_tendsto
      refine this.congr ?_
      intro x; simp
    rcases (hTop.eventually (Filter.eventually_lt_atBot (0 : ℝ))).exists with ⟨a, ha⟩
    rcases (hBot.eventually (Filter.eventually_gt_atTop (0 : ℝ))).exists with ⟨b, hb⟩
    exact ⟨a, b, ha, hb⟩
  · -- leadingCoeff Q > 0: so leadingCoeff Q' < 0
    have hTop : Filter.Tendsto (fun x => Q.eval x) Filter.atTop Filter.atTop :=
      Polynomial.tendsto_atTop_of_leadingCoeff_nonneg Q hdegree_pos hpos.le
    have hQ'_lc_nonpos : Q'.leadingCoeff ≤ 0 := by rw [hQ'_lc]; linarith
    have hTop' : Filter.Tendsto (fun x => Q'.eval x) Filter.atTop Filter.atBot :=
      Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q' hQ'_degree_pos hQ'_lc_nonpos
    have hBot : Filter.Tendsto (fun x => Q.eval x) Filter.atBot Filter.atBot := by
      have hh : Filter.Tendsto (fun x => Q.eval (-x)) Filter.atTop Filter.atBot := by
        convert hTop' using 1; ext x; exact (hQ'_eval x).symm
      have hneg_tendsto : Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop :=
        Filter.tendsto_neg_atBot_atTop
      have := hh.comp hneg_tendsto
      refine this.congr ?_
      intro x; simp
    rcases (hBot.eventually (Filter.eventually_lt_atBot (0 : ℝ))).exists with ⟨a, ha⟩
    rcases (hTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))).exists with ⟨b, hb⟩
    exact ⟨a, b, ha, hb⟩

/-- For odd-degree real polynomials, evaluation is surjective. -/
lemma eval_surjective_of_odd_natDegree {Q : ℝ[X]} (hodd : Odd Q.natDegree) :
    ∀ y : ℝ, ∃ r : ℝ, Q.eval r = y := by
  intro y
  have hdeg_pos : 0 < Q.natDegree := by rcases hodd with ⟨k, hk⟩; omega
  have hQy_natDeg : (Q - C y).natDegree = Q.natDegree := by
    apply natDegree_sub_eq_left_of_natDegree_lt
    rw [natDegree_C]
    exact hdeg_pos
  have hQy_odd : Odd (Q - C y).natDegree := hQy_natDeg ▸ hodd
  obtain ⟨r, hr⟩ := exists_root_of_odd_natDegree hQy_odd
  refine ⟨r, ?_⟩
  have hsub : (Q - C y).eval r = Q.eval r - y := by simp
  linarith [hsub ▸ hr]

/-- The key polynomial used to encode the tangency condition:
    `Qpoly P a = a * P' + P - X * P'`.
The point `(a, b)` is on some tangent line iff `b` is in the image of `Qpoly P a`. -/
noncomputable def Qpoly (P : ℝ[X]) (a : ℝ) : ℝ[X] :=
  C a * P.derivative + P - X * P.derivative

lemma tangent_through_iff (P : ℝ[X]) (a b : ℝ) :
    (a, b) ∈ ⋃ x, tangentLine P x ↔ ∃ r, (Qpoly P a).eval r = b := by
  simp only [Set.mem_iUnion, tangentLine, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simp only [Qpoly, eval_add, eval_sub, eval_mul, eval_C, eval_X]
    linarith
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    simp only [Qpoly, eval_add, eval_sub, eval_mul, eval_C, eval_X] at hr
    linarith

/-- For `P` with `2 ≤ natDegree P`, `X * P.derivative` has natDegree equal to `P.natDegree`. -/
lemma natDegree_X_mul_derivative {P : ℝ[X]} (hdeg : 2 ≤ P.natDegree) :
    (X * P.derivative).natDegree = P.natDegree := by
  have hP_ne : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  -- P.derivative is not zero since natDegree P ≥ 2 ≥ 1.
  have hderiv_ne : P.derivative ≠ 0 := by
    intro h
    have := natDegree_eq_zero_of_derivative_eq_zero (f := P) h
    omega
  -- Compute natDegree (X * P') = 1 + natDegree P'.
  rw [natDegree_mul X_ne_zero hderiv_ne, natDegree_X]
  -- natDegree of P' and of P differ by exactly 1 for CharZero / rings like ℝ.
  -- Use: P' coefficient at n-1 equals n * (coeff P n) ≠ 0
  have h_pos_nat : 0 < P.natDegree := by omega
  have hcoeff : P.derivative.coeff (P.natDegree - 1) = P.natDegree * P.coeff P.natDegree := by
    rw [coeff_derivative, Nat.sub_add_cancel h_pos_nat]
    have hc : ((P.natDegree - 1 : ℕ) : ℝ) + 1 = (P.natDegree : ℝ) := by
      have : ((P.natDegree - 1 : ℕ) + 1 : ℕ) = P.natDegree := Nat.sub_add_cancel h_pos_nat
      exact_mod_cast this
    rw [hc]
    ring
  have hcoeff_ne : P.derivative.coeff (P.natDegree - 1) ≠ 0 := by
    rw [hcoeff]
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (by omega : P.natDegree ≠ 0)
    · exact leadingCoeff_ne_zero.mpr hP_ne
  have hderiv_le : P.derivative.natDegree ≤ P.natDegree - 1 := natDegree_derivative_le P
  have hderiv_ge : P.natDegree - 1 ≤ P.derivative.natDegree :=
    le_natDegree_of_ne_zero hcoeff_ne
  have hderiv_eq : P.derivative.natDegree = P.natDegree - 1 := le_antisymm hderiv_le hderiv_ge
  rw [hderiv_eq]
  omega

/-- The leading coeff of `X * P.derivative` is `n * P.leadingCoeff` when natDegree P = n ≥ 1. -/
lemma leadingCoeff_X_mul_derivative {P : ℝ[X]} (hdeg : 2 ≤ P.natDegree) :
    (X * P.derivative).leadingCoeff = P.natDegree * P.leadingCoeff := by
  have h_pos_nat : 0 < P.natDegree := by omega
  have hP_ne : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hnd : (X * P.derivative).natDegree = P.natDegree := natDegree_X_mul_derivative hdeg
  have hnd_eq : P.natDegree = (P.natDegree - 1) + 1 := (Nat.sub_add_cancel h_pos_nat).symm
  rw [leadingCoeff, hnd]
  conv_lhs => rw [hnd_eq]
  rw [coeff_X_mul, coeff_derivative, Nat.sub_add_cancel h_pos_nat]
  rw [leadingCoeff]
  have hc : ((P.natDegree - 1 : ℕ) : ℝ) + 1 = (P.natDegree : ℝ) := by
    have : ((P.natDegree - 1 : ℕ) + 1 : ℕ) = P.natDegree := Nat.sub_add_cancel h_pos_nat
    exact_mod_cast this
  rw [hc]
  ring

/-- For `P` with `2 ≤ natDegree P`, `P - X * P.derivative` has natDegree equal to `P.natDegree`,
because the leading coefficients don't cancel: the difference is `(1 - n) * P.leadingCoeff ≠ 0`. -/
lemma natDegree_P_sub_X_deriv {P : ℝ[X]} (hdeg : 2 ≤ P.natDegree) :
    (P - X * P.derivative).natDegree = P.natDegree := by
  have hP_ne : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hlc_ne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP_ne
  have hXd_nd : (X * P.derivative).natDegree = P.natDegree := natDegree_X_mul_derivative hdeg
  have hXd_lc : (X * P.derivative).leadingCoeff = P.natDegree * P.leadingCoeff :=
    leadingCoeff_X_mul_derivative hdeg
  -- The leading coefficients of P and X * P' at degree P.natDegree are
  -- P.leadingCoeff and n * P.leadingCoeff respectively. Their difference is (1 - n) * P.leadingCoeff.
  -- Since n ≥ 2, this is nonzero, so the subtraction keeps the natDegree.
  set n := P.natDegree with hn
  have hn_ne : (1 - (n : ℝ)) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hdeg
    linarith
  -- Use that leadingCoeff (P - X*P') is nonzero and equals P.lc - n * P.lc.
  have h_coeff_at_n : (P - X * P.derivative).coeff n = (1 - n) * P.leadingCoeff := by
    rw [coeff_sub]
    have h1 : P.coeff n = P.leadingCoeff := rfl
    have h2 : (X * P.derivative).coeff n = n * P.leadingCoeff := by
      have : (X * P.derivative).coeff n = (X * P.derivative).leadingCoeff := by
        rw [leadingCoeff, hXd_nd]
      rw [this, hXd_lc]
    rw [h1, h2]
    ring
  have h_coeff_ne : (P - X * P.derivative).coeff n ≠ 0 := by
    rw [h_coeff_at_n]
    exact mul_ne_zero hn_ne hlc_ne
  -- natDegree is at least n.
  have h_ge : n ≤ (P - X * P.derivative).natDegree := le_natDegree_of_ne_zero h_coeff_ne
  -- natDegree is at most n: both P and X*P' have natDegree ≤ n.
  have h_le : (P - X * P.derivative).natDegree ≤ n := by
    have hmax : (P - X * P.derivative).natDegree ≤ max P.natDegree (X * P.derivative).natDegree :=
      natDegree_sub_le P (X * P.derivative)
    rw [hXd_nd, max_self] at hmax
    exact hmax
  exact le_antisymm h_le h_ge

/-- `Qpoly P a` has natDegree equal to `P.natDegree`. -/
lemma Qpoly_natDegree {P : ℝ[X]} (hdeg : 2 ≤ P.natDegree) (a : ℝ) :
    (Qpoly P a).natDegree = P.natDegree := by
  -- Qpoly P a = C a * P' + (P - X * P'). The second summand has natDegree P.natDegree,
  -- and C a * P' has natDegree ≤ P.natDegree - 1.
  have hbase : (P - X * P.derivative).natDegree = P.natDegree := natDegree_P_sub_X_deriv hdeg
  have hPa_le : (C a * P.derivative).natDegree ≤ P.natDegree - 1 := by
    calc (C a * P.derivative).natDegree
        ≤ (C a).natDegree + P.derivative.natDegree := natDegree_mul_le
      _ ≤ 0 + P.derivative.natDegree := by rw [natDegree_C]
      _ = P.derivative.natDegree := by ring
      _ ≤ P.natDegree - 1 := natDegree_derivative_le P
  have hPa_lt : (C a * P.derivative).natDegree < P.natDegree := by
    have h_pos_nat : 0 < P.natDegree := by omega
    omega
  -- Now: Qpoly P a = C a * P' + P - X * P' = C a * P' + (P - X * P').
  have hQeq : Qpoly P a = C a * P.derivative + (P - X * P.derivative) := by
    rw [Qpoly]; ring
  rw [hQeq]
  rw [natDegree_add_eq_right_of_natDegree_lt ?_]
  · exact hbase
  · rw [hbase]; exact hPa_lt

snip end

/-- The answer to part (b): No such even-degree polynomial exists. -/
determine answerB : Prop := False

problem imc2025_p1 :
    (∀ (P : ℝ[X]), 2 ≤ P.natDegree → Odd P.natDegree →
      ⋃ x, tangentLine P x = (Set.univ : Set (ℝ × ℝ))) ∧
    (answerB ↔
      ∃ (P : ℝ[X]), 2 ≤ P.natDegree ∧ Even P.natDegree ∧
        ⋃ x, tangentLine P x = (Set.univ : Set (ℝ × ℝ))) := by
  refine ⟨?_, ?_⟩
  · -- Part (a).
    intro P hdeg hodd
    apply Set.eq_univ_of_forall
    rintro ⟨a, b⟩
    rw [tangent_through_iff]
    -- Qpoly P a has odd natDegree equal to P.natDegree.
    have hQnatDeg : (Qpoly P a).natDegree = P.natDegree := Qpoly_natDegree hdeg a
    have hQodd : Odd (Qpoly P a).natDegree := hQnatDeg ▸ hodd
    exact eval_surjective_of_odd_natDegree hQodd b
  · -- Part (b): answer is False, i.e., no such even-degree polynomial exists.
    show False ↔ _
    refine ⟨False.elim, ?_⟩
    -- For even natDegree, Qpoly P 0 is a polynomial of even natDegree n ≥ 2
    -- with leading coefficient (1 - n) * P.leadingCoeff.
    -- Since 1 - n ≤ -1 < 0, this leading coefficient has sign opposite to P.leadingCoeff.
    -- An even-degree polynomial tends to the same infinity at ±∞ (determined by sign of lc),
    -- hence its image is bounded on one side, missing infinitely many reals.
    rintro ⟨P, hdeg, heven, hcover⟩
    have hQnd : (Qpoly P 0).natDegree = P.natDegree := Qpoly_natDegree hdeg 0
    have hP_ne : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
    have hQ_ne : Qpoly P 0 ≠ 0 := by
      intro h
      have : (Qpoly P 0).natDegree = 0 := by rw [h, natDegree_zero]
      rw [hQnd] at this; omega
    -- Sign of leading coefficient of Qpoly P 0.
    -- Qpoly P 0 = C 0 * P' + P - X * P' = 0 + P - X * P' = P - X * P'.
    have hQ0 : Qpoly P 0 = P - X * P.derivative := by
      simp [Qpoly]
    have hQ_natDeg' : (P - X * P.derivative).natDegree = P.natDegree :=
      natDegree_P_sub_X_deriv hdeg
    have hQ_lc : (Qpoly P 0).leadingCoeff = (1 - P.natDegree) * P.leadingCoeff := by
      rw [hQ0]
      -- Compute leading coeff of P - X*P' directly.
      set n := P.natDegree
      have h_coeff_at_n : (P - X * P.derivative).coeff n = (1 - (n : ℝ)) * P.leadingCoeff := by
        rw [coeff_sub]
        have h1 : P.coeff n = P.leadingCoeff := rfl
        have h2 : (X * P.derivative).coeff n = n * P.leadingCoeff := by
          have hXd_nd : (X * P.derivative).natDegree = P.natDegree :=
            natDegree_X_mul_derivative hdeg
          have hXd_lc : (X * P.derivative).leadingCoeff = P.natDegree * P.leadingCoeff :=
            leadingCoeff_X_mul_derivative hdeg
          have : (X * P.derivative).coeff n = (X * P.derivative).leadingCoeff := by
            rw [leadingCoeff, hXd_nd]
          rw [this, hXd_lc]
        rw [h1, h2]
        ring
      rw [leadingCoeff, hQ_natDeg']
      exact h_coeff_at_n
    have hP_lc_ne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP_ne
    have h_1_sub_n_ne : (1 - (P.natDegree : ℝ)) ≠ 0 := by
      have : (2 : ℝ) ≤ P.natDegree := by exact_mod_cast hdeg
      linarith
    -- Also need Qpoly's natDegree is even.
    have hQ_even : Even (Qpoly P 0).natDegree := hQnd ▸ heven
    have hQ_degree_pos : 0 < (Qpoly P 0).degree := by
      rw [← natDegree_pos_iff_degree_pos, hQnd]; omega
    -- Two cases on sign of Qpoly's leading coefficient.
    rcases lt_or_gt_of_ne (show (Qpoly P 0).leadingCoeff ≠ 0 from
        leadingCoeff_ne_zero.mpr hQ_ne) with hneg | hpos
    · -- Qpoly lc < 0. Both ±∞ go to -∞. So image is bounded above.
      have hTop : Filter.Tendsto (fun x => (Qpoly P 0).eval x) Filter.atTop Filter.atBot :=
        Polynomial.tendsto_atBot_of_leadingCoeff_nonpos _ hQ_degree_pos hneg.le
      -- Use Q.comp (-X): has the same leading coeff since natDegree is even.
      set Q' : ℝ[X] := (Qpoly P 0).comp (-X) with hQ'_def
      have hQ'_lc : Q'.leadingCoeff = (Qpoly P 0).leadingCoeff := by
        rw [hQ'_def, comp_neg_X_leadingCoeff_eq, Even.neg_one_pow hQ_even]; ring
      have hQ'_natDeg : Q'.natDegree = (Qpoly P 0).natDegree := by simp [Q', natDegree_comp]
      have hQ'_degree_pos : 0 < Q'.degree := by
        rw [← natDegree_pos_iff_degree_pos, hQ'_natDeg]
        exact natDegree_pos_iff_degree_pos.mpr hQ_degree_pos
      have hQ'_lc_nonpos : Q'.leadingCoeff ≤ 0 := by rw [hQ'_lc]; linarith
      have hTop' : Filter.Tendsto (fun x => Q'.eval x) Filter.atTop Filter.atBot :=
        Polynomial.tendsto_atBot_of_leadingCoeff_nonpos _ hQ'_degree_pos hQ'_lc_nonpos
      have hBot : Filter.Tendsto (fun x => (Qpoly P 0).eval x) Filter.atBot Filter.atBot := by
        have hh : Filter.Tendsto (fun x => (Qpoly P 0).eval (-x)) Filter.atTop Filter.atBot := by
          convert hTop' using 1
          ext x
          simp [Q', eval_comp]
        have := hh.comp Filter.tendsto_neg_atBot_atTop
        refine this.congr ?_; intro x; simp
      -- Now find b such that (0, b) is not attained.
      -- The set of attained values is bounded above. Show by contradiction with hcover.
      have hUniv := hcover
      have : ((0 : ℝ), ((0 : ℝ), ((0 : ℝ), (0 : ℝ)))) ∈ (Set.univ : Set (ℝ × ℝ × ℝ × ℝ)) :=
        trivial
      -- For each real y, (0, y) should be in the union.
      -- Choose y very large. Then there's r with Qpoly P 0 evaluated at r equals y.
      -- But (Qpoly P 0).eval → -∞ at ±∞, so it's bounded above. Contradiction.
      obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ r, (Qpoly P 0).eval r ≤ M := by
        -- Qpoly P 0 tends to -∞ at ±∞, so it's bounded above.
        have hEv1 : ∀ᶠ x in Filter.atTop, (Qpoly P 0).eval x ≤ 0 :=
          hTop.eventually (Filter.eventually_le_atBot (0 : ℝ))
        have hEv2 : ∀ᶠ x in Filter.atBot, (Qpoly P 0).eval x ≤ 0 :=
          hBot.eventually (Filter.eventually_le_atBot (0 : ℝ))
        obtain ⟨x₀, hx₀⟩ := hEv1.exists_forall_of_atTop
        obtain ⟨x₁, hx₁⟩ := hEv2.exists_forall_of_atBot
        let a := min x₁ x₀
        let b := max x₁ x₀
        have hab : a ≤ b := min_le_max
        have hcont : ContinuousOn (fun x => (Qpoly P 0).eval x) (Set.Icc a b) :=
          (Qpoly P 0).continuous.continuousOn
        have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
        obtain ⟨M₁, hM₁⟩ := hcompact.bddAbove_image hcont
        use max M₁ 0
        intro r
        by_cases hr1 : r ≤ x₁
        · calc (Qpoly P 0).eval r ≤ 0 := hx₁ r hr1
            _ ≤ max M₁ 0 := le_max_right _ _
        by_cases hr2 : x₀ ≤ r
        · calc (Qpoly P 0).eval r ≤ 0 := hx₀ r hr2
            _ ≤ max M₁ 0 := le_max_right _ _
        simp only [not_le] at hr1 hr2
        have h_in : r ∈ Set.Icc a b := by
          constructor
          · exact le_trans (min_le_left _ _) hr1.le
          · exact le_trans hr2.le (le_max_right _ _)
        have : (Qpoly P 0).eval r ∈ ((fun x => (Qpoly P 0).eval x) '' Set.Icc a b) :=
          ⟨r, h_in, rfl⟩
        calc (Qpoly P 0).eval r ≤ M₁ := hM₁ this
          _ ≤ max M₁ 0 := le_max_left _ _
      -- Now derive contradiction: (0, M+1) should be in the tangent cover.
      have h := Set.eq_univ_iff_forall.mp hcover (0, M + 1)
      rw [tangent_through_iff] at h
      obtain ⟨r, hr⟩ := h
      have := hM r
      linarith
    · -- Qpoly lc > 0. Both ±∞ go to +∞. So image is bounded below. Symmetric.
      have hTop : Filter.Tendsto (fun x => (Qpoly P 0).eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ hQ_degree_pos hpos.le
      set Q' : ℝ[X] := (Qpoly P 0).comp (-X) with hQ'_def
      have hQ'_lc : Q'.leadingCoeff = (Qpoly P 0).leadingCoeff := by
        rw [hQ'_def, comp_neg_X_leadingCoeff_eq, Even.neg_one_pow hQ_even]; ring
      have hQ'_natDeg : Q'.natDegree = (Qpoly P 0).natDegree := by simp [Q', natDegree_comp]
      have hQ'_degree_pos : 0 < Q'.degree := by
        rw [← natDegree_pos_iff_degree_pos, hQ'_natDeg]
        exact natDegree_pos_iff_degree_pos.mpr hQ_degree_pos
      have hQ'_lc_nonneg : 0 ≤ Q'.leadingCoeff := by rw [hQ'_lc]; linarith
      have hTop' : Filter.Tendsto (fun x => Q'.eval x) Filter.atTop Filter.atTop :=
        Polynomial.tendsto_atTop_of_leadingCoeff_nonneg _ hQ'_degree_pos hQ'_lc_nonneg
      have hBot : Filter.Tendsto (fun x => (Qpoly P 0).eval x) Filter.atBot Filter.atTop := by
        have hh : Filter.Tendsto (fun x => (Qpoly P 0).eval (-x)) Filter.atTop Filter.atTop := by
          convert hTop' using 1
          ext x
          simp [Q', eval_comp]
        have := hh.comp Filter.tendsto_neg_atBot_atTop
        refine this.congr ?_; intro x; simp
      obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ r, M ≤ (Qpoly P 0).eval r := by
        have hEv1 : ∀ᶠ x in Filter.atTop, 0 ≤ (Qpoly P 0).eval x :=
          hTop.eventually (Filter.eventually_ge_atTop (0 : ℝ))
        have hEv2 : ∀ᶠ x in Filter.atBot, 0 ≤ (Qpoly P 0).eval x :=
          hBot.eventually (Filter.eventually_ge_atTop (0 : ℝ))
        obtain ⟨x₀, hx₀⟩ := hEv1.exists_forall_of_atTop
        obtain ⟨x₁, hx₁⟩ := hEv2.exists_forall_of_atBot
        -- Use a = min x₁ x₀ and b = max x₁ x₀ so that [a, b] covers the middle region.
        let a := min x₁ x₀
        let b := max x₁ x₀
        have hab : a ≤ b := min_le_max
        have hcont : ContinuousOn (fun x => (Qpoly P 0).eval x) (Set.Icc a b) :=
          (Qpoly P 0).continuous.continuousOn
        have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
        obtain ⟨M₁, hM₁⟩ := hcompact.bddBelow_image hcont
        use min M₁ 0
        intro r
        by_cases hr1 : r ≤ x₁
        · calc min M₁ 0 ≤ 0 := min_le_right _ _
            _ ≤ (Qpoly P 0).eval r := hx₁ r hr1
        by_cases hr2 : x₀ ≤ r
        · calc min M₁ 0 ≤ 0 := min_le_right _ _
            _ ≤ (Qpoly P 0).eval r := hx₀ r hr2
        simp only [not_le] at hr1 hr2
        have h_in : r ∈ Set.Icc a b := by
          constructor
          · exact le_trans (min_le_left _ _) hr1.le
          · exact le_trans hr2.le (le_max_right _ _)
        have : (Qpoly P 0).eval r ∈ ((fun x => (Qpoly P 0).eval x) '' Set.Icc a b) :=
          ⟨r, h_in, rfl⟩
        calc min M₁ 0 ≤ M₁ := min_le_left _ _
          _ ≤ (Qpoly P 0).eval r := hM₁ this
      -- Derive contradiction: (0, M-1) should be in the tangent cover.
      have h := Set.eq_univ_iff_forall.mp hcover (0, M - 1)
      rw [tangent_through_iff] at h
      obtain ⟨r, hr⟩ := h
      have := hM r
      linarith

end Imc2025P1
