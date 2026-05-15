/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1995, Problem 9 (Day 2 Problem 3)

Let `P` be a polynomial of degree `n ≥ 1` over `ℂ`, all of whose roots lie on
the unit circle. Prove that all roots of `Q(z) = 2 z P'(z) - n P(z)` also lie
on the unit circle.

## Proof outline

The key Mathlib lemma `Splits.eval_derivative_div_eval_of_ne_zero` gives, for
`P(z) ≠ 0`,

  `P'(z) / P(z) = ∑_{α ∈ roots} 1/(z - α)`.

So when `Q(z) = 0`, multiplying through gives

  `0 = 2 z · ∑_α 1/(z - α) - n = ∑_α (2z - (z - α))/(z - α) = ∑_α (z + α)/(z - α)`,

(using that there are `n = card roots` terms in the sum). Now if `|α| = 1` and
`z ≠ α`, the real part of `(z + α)/(z - α)` is `(|z|² - 1) / |z - α|²`. So

  `0 = Re(0) = (|z|² - 1) · ∑_α 1/|z - α|²`,

and the sum is strictly positive (`n ≥ 1` and each term positive), forcing
`|z|² = 1`. The remaining case `P(z) = 0` is immediate: then `z ∈ roots`,
hence `|z| = 1`.
-/

namespace Imc1995P9

open Polynomial

/-- Real part identity: for `|α| = 1` and `z ≠ α`,
`Re((z + α)/(z - α)) = (|z|² - 1) / |z - α|²`. -/
private lemma re_frac_unit (z α : ℂ) (hα : ‖α‖ = 1) (hzα : z ≠ α) :
    ((z + α) / (z - α)).re = (‖z‖ ^ 2 - 1) / ‖z - α‖ ^ 2 := by
  have hzα' : z - α ≠ 0 := sub_ne_zero.mpr hzα
  have hns_pos : (0 : ℝ) < Complex.normSq (z - α) :=
    Complex.normSq_pos.mpr hzα'
  have hns_ne : Complex.normSq (z - α) ≠ 0 := ne_of_gt hns_pos
  have hns_C_ne : (Complex.normSq (z - α) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hns_ne
  -- (z+α)/(z-α) = ((z+α) * conj(z-α)) / normSq(z-α).
  have hconj_ne : starRingEnd ℂ (z - α) ≠ 0 :=
    (_root_.map_ne_zero (starRingEnd ℂ)).mpr hzα'
  have hkey_eq : (z + α) / (z - α) =
      ((z + α) * starRingEnd ℂ (z - α)) / (Complex.normSq (z - α) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    rw [show ((z + α) * starRingEnd ℂ (z - α)) / (starRingEnd ℂ (z - α) * (z - α))
          = (z + α) / (z - α) by
            rw [mul_comm (starRingEnd ℂ (z - α)) (z - α)]
            rw [mul_div_mul_right _ _ hconj_ne]]
  rw [hkey_eq, Complex.div_ofReal_re]
  have hns_eq : Complex.normSq (z - α) = ‖z - α‖ ^ 2 :=
    (Complex.sq_norm _).symm
  rw [hns_eq]
  congr 1
  -- Compute Re((z+α) · conj(z-α)).
  have hα2 : α.re ^ 2 + α.im ^ 2 = 1 := by
    have hns_α : Complex.normSq α = ‖α‖ ^ 2 := (Complex.sq_norm _).symm
    rw [Complex.normSq_apply] at hns_α
    rw [hα] at hns_α
    nlinarith [hns_α]
  have hzz_re : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have : ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z
    rw [this, Complex.normSq_apply]; ring
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, map_sub, Complex.conj_re, Complex.conj_im,
    sub_neg_eq_add]
  rw [hzz_re]
  ring_nf
  nlinarith [hα2]

/-- The summation identity: when `P(z) ≠ 0` and `Q(z) = 2z P'(z) - n P(z) = 0`
(with `n = natDegree P`), the sum `∑_{α ∈ roots} (z + α)/(z - α)` equals `0`. -/
private lemma sum_quotient_eq_zero
    (P : ℂ[X]) (n : ℕ) (hn : P.natDegree = n)
    (z : ℂ) (hPz : P.eval z ≠ 0)
    (hQz : (2 * X * P.derivative - C (n : ℂ) * P).eval z = 0) :
    (P.roots.map fun α => (z + α) / (z - α)).sum = 0 := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : (P.roots.card : ℂ) = (n : ℂ) := by
    have h := Polynomial.splits_iff_card_roots.mp hsplit
    rw [show P.roots.card = P.natDegree from by omega, hn]
  -- P'(z) / P(z) = ∑ 1/(z - α).
  have hderiv := hsplit.eval_derivative_div_eval_of_ne_zero hPz
  -- Unfold hQz: 2 z P'(z) - n P(z) = 0.
  have hQz' : 2 * z * P.derivative.eval z = (n : ℂ) * P.eval z := by
    have heval : (2 * X * P.derivative - C (n : ℂ) * P).eval z =
        2 * z * P.derivative.eval z - (n : ℂ) * P.eval z := by
      simp [eval_sub, eval_mul, eval_X]
    rw [heval] at hQz
    linear_combination hQz
  -- So P'(z)/P(z) = n / (2z) (when 2z ≠ 0; n ≥ 1 so we won't actually need this special case).
  -- But we manipulate sum directly.
  -- Goal: ∑ (z + α)/(z - α) = 0.
  -- We have: ∑ 1/(z - α) = P'(z)/P(z), and 2z P'(z) = n P(z).
  -- So: 2z · ∑ 1/(z - α) = 2z · P'(z)/P(z) = (2z · P'(z))/P(z) = (n · P(z))/P(z) = n.
  -- And: ∑ (z + α)/(z - α) = ∑ (2z/(z-α) - 1) = 2z · ∑ 1/(z-α) - card = n - n = 0.
  -- Translate (z + α)/(z - α) = 2z/(z - α) - 1.
  have hroots_zα : ∀ α ∈ P.roots, z - α ≠ 0 := by
    intro α hα hzeq
    apply hPz
    have hroot : P.IsRoot α := (mem_roots'.mp hα).2
    rw [show z = α from sub_eq_zero.mp hzeq]
    exact hroot
  have hsplit_term : (P.roots.map fun α => (z + α) / (z - α)) =
      (P.roots.map fun α => (2 * z) * (1 / (z - α)) - 1) := by
    apply Multiset.map_congr rfl
    intro α hα
    have hzα_ne := hroots_zα α hα
    field_simp
    ring
  rw [hsplit_term]
  rw [Multiset.sum_map_sub]
  -- Sum splits: ∑(2z * (1/(z-α))) - ∑ 1 = 2z·∑1/(z-α) - card.
  rw [Multiset.sum_map_mul_left]
  rw [Multiset.map_const', Multiset.sum_replicate]
  -- 2 z · (∑ 1/(z - α)) - card • 1 = 0.
  rw [← hderiv]
  -- Goal: 2 * z * (P'(z)/P(z)) - card • 1 = 0.
  have h2zP : 2 * z * (P.derivative.eval z / P.eval z) = (n : ℂ) := by
    rw [show 2 * z * (P.derivative.eval z / P.eval z)
          = (2 * z * P.derivative.eval z) / P.eval z by ring]
    rw [hQz']
    rw [mul_div_assoc, div_self hPz, mul_one]
  rw [h2zP]
  -- Goal: (n : ℂ) - card • 1 = 0.
  rw [show ((P.roots.card : ℕ) • (1 : ℂ)) = (P.roots.card : ℂ) by
        rw [nsmul_eq_mul, mul_one]]
  rw [hcard]
  ring

/-- Sum of real parts of `(z+α)/(z-α)` is nonzero when `‖z‖ ≠ 1` and roots
nonempty all on unit circle. -/
private lemma sum_quotient_re_ne_zero (z : ℂ)
    (s : Multiset ℂ) (hs : s ≠ 0) (hroots : ∀ α ∈ s, ‖α‖ = 1)
    (hzα : ∀ α ∈ s, z ≠ α) (hzn : ‖z‖ ≠ 1) :
    ((s.map fun α => (z + α) / (z - α)).sum).re ≠ 0 := by
  -- Re of a multiset sum = multiset sum of Res.
  have hre_sum : ((s.map fun α => (z + α) / (z - α)).sum).re =
      (s.map fun α => ((z + α) / (z - α)).re).sum := by
    rw [show ((s.map fun α => (z + α) / (z - α)).sum).re
          = Complex.reAddGroupHom (s.map fun α => (z + α) / (z - α)).sum from rfl]
    rw [map_multiset_sum]
    rw [Multiset.map_map]
    rfl
  rw [hre_sum]
  -- Substitute Re via re_frac_unit.
  have hexpand : (s.map fun α => ((z + α) / (z - α)).re) =
      (s.map fun α => (‖z‖ ^ 2 - 1) * (1 / ‖z - α‖ ^ 2)) := by
    apply Multiset.map_congr rfl
    intro α hα
    rw [re_frac_unit z α (hroots α hα) (hzα α hα)]
    field_simp
  rw [hexpand, Multiset.sum_map_mul_left]
  apply mul_ne_zero
  · intro heq
    apply hzn
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg (‖z‖ + 1), heq]
  · -- ∑ 1/‖z-α‖² > 0.
    have hpos : ∀ a ∈ (s.map fun α => 1 / ‖z - α‖ ^ 2), 0 < a := by
      intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨α, hα, rfl⟩ := ha
      have hp : (0:ℝ) < ‖z - α‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hzα α hα))
      positivity
    have hexists : ∃ α ∈ s, True := by
      obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero hs
      exact ⟨α, hα, trivial⟩
    obtain ⟨α, hα, _⟩ := hexists
    have hp : (0:ℝ) < 1 / ‖z - α‖ ^ 2 := by
      have : (0:ℝ) < ‖z - α‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hzα α hα))
      positivity
    have hge : 0 < (s.map fun α => 1 / ‖z - α‖ ^ 2).sum := by
      have hge' : 1 / ‖z - α‖ ^ 2 ≤ (s.map fun α => 1 / ‖z - α‖ ^ 2).sum :=
        Multiset.single_le_sum (fun b hb => (hpos b hb).le)
          (1 / ‖z - α‖ ^ 2)
          (by rw [Multiset.mem_map]; exact ⟨α, hα, rfl⟩)
      linarith
    exact ne_of_gt hge

/-- Main theorem: For any polynomial `P` of degree `n ≥ 1` over `ℂ` with all
roots on the unit circle, every root of `2 X P' - n P` lies on the unit circle. -/
problem imc1995_p9 (P : ℂ[X]) (n : ℕ) (hn : P.natDegree = n) (hn1 : 1 ≤ n)
    (hroots : ∀ α ∈ P.roots, ‖α‖ = 1)
    (z : ℂ) (hQz : (2 * X * P.derivative - C (n : ℂ) * P).eval z = 0) :
    ‖z‖ = 1 := by
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hP_ne : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hn
    omega
  by_cases hPz : P.eval z = 0
  · -- z is a root of P, so ‖z‖ = 1.
    have hz_mem : z ∈ P.roots := (Polynomial.mem_roots hP_ne).mpr hPz
    exact hroots z hz_mem
  · have hsumeq := sum_quotient_eq_zero P n hn z hPz hQz
    by_contra hne
    have hzα : ∀ α ∈ P.roots, z ≠ α := by
      intro α hα hzeq
      apply hPz
      rw [hzeq]
      exact (Polynomial.mem_roots hP_ne).mp hα
    have hcard : P.roots.card = P.natDegree := by
      have h := Polynomial.splits_iff_card_roots.mp hsplit
      omega
    have hs_ne : P.roots ≠ 0 := by
      intro h
      have : P.roots.card = 0 := by rw [h]; rfl
      rw [hcard, hn] at this
      omega
    have hcontra := sum_quotient_re_ne_zero z P.roots hs_ne hroots hzα hne
    apply hcontra
    rw [hsumeq]
    simp

end Imc1995P9
