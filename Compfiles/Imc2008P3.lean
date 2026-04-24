/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2008, Problem 3
(IMC 2008, Day 1, Problem 3)

Let `p ∈ ℤ[X]`, and let `a₁ < a₂ < ... < aₖ` be integers. Prove that there
exists an integer `a` such that `p(aᵢ) ∣ p(a)` for every `i`.
-/

namespace Imc2008P3

open Polynomial

snip begin

/-- Coprime factorization of two nonzero natural numbers. Given `u, v`, construct
`s, t` with `s ∣ u`, `t ∣ v`, `s` and `t` coprime, and `u * v ∣ (s * t) ^ 2`
(equivalently, `u ∣ s * t` and `v ∣ s * t`). -/
lemma exists_coprime_factorization_nat (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ s t : ℕ, s ∣ u ∧ t ∣ v ∧ Nat.Coprime s t ∧ u ∣ s * t ∧ v ∣ s * t := by
  -- For each prime p, we put p^{v_p(u)} into s if v_p(u) ≥ v_p(v), else put p^{v_p(v)} into t.
  classical
  let fu := u.factorization
  let fv := v.factorization
  -- sF: Finsupp for s, tF: Finsupp for t.
  let sF : ℕ →₀ ℕ := fu.filter (fun p => fv p ≤ fu p)
  let tF : ℕ →₀ ℕ := fv.filter (fun p => fu p < fv p)
  set s : ℕ := sF.prod (· ^ ·) with hs_def
  set t : ℕ := tF.prod (· ^ ·) with ht_def
  have hsF_le : sF ≤ fu := by
    intro p
    show sF p ≤ fu p
    by_cases h : fv p ≤ fu p
    · rw [show sF p = fu p from Finsupp.filter_apply_pos _ _ h]
    · rw [show sF p = 0 from Finsupp.filter_apply_neg _ _ h]; exact Nat.zero_le _
  have htF_le : tF ≤ fv := by
    intro p
    show tF p ≤ fv p
    by_cases h : fu p < fv p
    · rw [show tF p = fv p from Finsupp.filter_apply_pos _ _ h]
    · rw [show tF p = 0 from Finsupp.filter_apply_neg _ _ h]; exact Nat.zero_le _
  have hs_dvd_u : s ∣ u := Nat.prod_pow_dvd_of_le_factorization hsF_le
  have ht_dvd_v : t ∣ v := Nat.prod_pow_dvd_of_le_factorization htF_le
  -- s and t coprime: their supports are disjoint.
  have hdisj : Disjoint sF.support tF.support := by
    rw [Finset.disjoint_left]
    intro p hps hpt
    have h1 : fv p ≤ fu p := by
      rw [Finsupp.mem_support_iff] at hps
      by_contra h
      exact hps (Finsupp.filter_apply_neg _ _ h)
    have h2 : fu p < fv p := by
      rw [Finsupp.mem_support_iff] at hpt
      by_contra h
      exact hpt (Finsupp.filter_apply_neg _ _ h)
    omega
  have hprime_sF : ∀ p ∈ sF.support, p.Prime := by
    intro p hp
    have : p ∈ fu.support := by
      have : sF.support ⊆ fu.support := Finsupp.support_mono hsF_le
      exact this hp
    exact Nat.prime_of_mem_primeFactors this
  have hprime_tF : ∀ p ∈ tF.support, p.Prime := by
    intro p hp
    have : p ∈ fv.support := Finsupp.support_mono htF_le hp
    exact Nat.prime_of_mem_primeFactors this
  have hs_pos : 0 < s := by
    rw [hs_def]
    apply Nat.pos_of_ne_zero
    rw [Finsupp.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (hprime_sF p hp).ne_zero
  have ht_pos : 0 < t := by
    rw [ht_def]
    apply Nat.pos_of_ne_zero
    rw [Finsupp.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (hprime_tF p hp).ne_zero
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have ht_ne : t ≠ 0 := ht_pos.ne'
  -- Factorization of s equals sF.
  have hfact_s : s.factorization = sF := by
    rw [hs_def]
    exact Nat.factorization_prod_pow_eq_self_of_le_factorization hsF_le
  have hfact_t : t.factorization = tF := by
    rw [ht_def]
    exact Nat.factorization_prod_pow_eq_self_of_le_factorization htF_le
  -- Coprime: gcd(s, t) = 1.
  have hcop : Nat.Coprime s t := by
    rw [Nat.coprime_iff_gcd_eq_one]
    -- Show s and t share no prime factors.
    by_contra h
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h
    have hp_dvd_s : p ∣ s := dvd_trans hp_dvd (Nat.gcd_dvd_left s t)
    have hp_dvd_t : p ∣ t := dvd_trans hp_dvd (Nat.gcd_dvd_right s t)
    have hps : p ∈ s.factorization.support := by
      rw [Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨hp_prime, hp_dvd_s, hs_ne⟩
    have hpt : p ∈ t.factorization.support := by
      rw [Nat.support_factorization, Nat.mem_primeFactors]
      exact ⟨hp_prime, hp_dvd_t, ht_ne⟩
    rw [hfact_s] at hps
    rw [hfact_t] at hpt
    exact (Finset.disjoint_left.mp hdisj) hps hpt
  -- u | s * t: for each prime p, v_p(u) ≤ v_p(s*t) = v_p(s) + v_p(t).
  -- v_p(s) = fu p if fv p ≤ fu p, else 0. v_p(t) = fv p if fu p < fv p, else 0.
  -- If fv p ≤ fu p: v_p(s) = fu p. v_p(t) = 0 (since fu p ≥ fv p). Sum = fu p. ≥ fu p ✓.
  -- If fu p < fv p: v_p(s) = 0. v_p(t) = fv p. Sum = fv p > fu p. ✓.
  have hst_ne : s * t ≠ 0 := mul_ne_zero hs_ne ht_ne
  have hu_dvd_st : u ∣ s * t := by
    rw [← Nat.factorization_le_iff_dvd hu hst_ne]
    rw [Nat.factorization_mul hs_ne ht_ne]
    rw [hfact_s, hfact_t]
    intro p
    show fu p ≤ (sF + tF) p
    simp only [Finsupp.add_apply]
    by_cases h : fv p ≤ fu p
    · have hsp : sF p = fu p := Finsupp.filter_apply_pos _ _ h
      have htp : tF p = 0 := Finsupp.filter_apply_neg _ _ (not_lt.mpr h)
      rw [hsp, htp]; exact Nat.le_add_right _ _
    · push Not at h
      have hsp : sF p = 0 := Finsupp.filter_apply_neg _ _ (not_le.mpr h)
      have htp : tF p = fv p := Finsupp.filter_apply_pos _ _ h
      rw [hsp, htp]; omega
  have hv_dvd_st : v ∣ s * t := by
    rw [← Nat.factorization_le_iff_dvd hv hst_ne]
    rw [Nat.factorization_mul hs_ne ht_ne]
    rw [hfact_s, hfact_t]
    intro p
    show fv p ≤ (sF + tF) p
    simp only [Finsupp.add_apply]
    by_cases h : fu p < fv p
    · have htp : tF p = fv p := Finsupp.filter_apply_pos _ _ h
      have hsp : sF p = 0 := Finsupp.filter_apply_neg _ _ (not_le.mpr h)
      rw [hsp, htp]; exact Nat.le_add_left _ _
    · push Not at h
      have hsp : sF p = fu p := Finsupp.filter_apply_pos _ _ h
      have htp : tF p = 0 := Finsupp.filter_apply_neg _ _ (not_lt.mpr h)
      rw [hsp, htp]; omega
  exact ⟨s, t, hs_dvd_u, ht_dvd_v, hcop, hu_dvd_st, hv_dvd_st⟩

/-- Coprime factorization of two nonzero integers: we can find `s ∣ u` and
`t ∣ v` with `s, t` coprime and such that both `u` and `v` divide `s * t`. -/
lemma exists_coprime_factorization (u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ s t : ℤ, s ∣ u ∧ t ∣ v ∧ IsCoprime s t ∧ u ∣ s * t ∧ v ∣ s * t := by
  -- Apply the Nat version to u.natAbs and v.natAbs, then lift.
  have hu' : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu
  have hv' : v.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hv
  obtain ⟨s, t, hs_dvd_u, ht_dvd_v, hcop, hu_dvd_st, hv_dvd_st⟩ :=
    exists_coprime_factorization_nat u.natAbs v.natAbs hu' hv'
  refine ⟨(s : ℤ), (t : ℤ), ?_, ?_, ?_, ?_, ?_⟩
  · -- (s : ℤ) | u. We have s | u.natAbs. Use Int.natCast_dvd_natCast and natAbs.
    have h1 : (s : ℤ) ∣ (u.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hs_dvd_u
    have h2 : ((u.natAbs : ℤ)) ∣ u := Int.natAbs_dvd.mpr dvd_rfl
    exact dvd_trans h1 h2
  · have h1 : (t : ℤ) ∣ (v.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr ht_dvd_v
    have h2 : ((v.natAbs : ℤ)) ∣ v := Int.natAbs_dvd.mpr dvd_rfl
    exact dvd_trans h1 h2
  · rw [Int.isCoprime_iff_gcd_eq_one]
    -- gcd((s : ℤ), (t : ℤ)) = Nat.gcd s t = 1.
    simp [Int.gcd_natCast_natCast, hcop]
  · -- u ∣ s * t. We have u.natAbs ∣ s * t (in ℕ).
    have h1 : (u.natAbs : ℤ) ∣ ((s * t : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hu_dvd_st
    have h2 : u ∣ (u.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have h3 : u ∣ ((s * t : ℕ) : ℤ) := dvd_trans h2 h1
    have h4 : ((s * t : ℕ) : ℤ) = (s : ℤ) * (t : ℤ) := by push_cast; ring
    rw [h4] at h3; exact h3
  · have h1 : (v.natAbs : ℤ) ∣ ((s * t : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hv_dvd_st
    have h2 : v ∣ (v.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have h3 : v ∣ ((s * t : ℕ) : ℤ) := dvd_trans h2 h1
    have h4 : ((s * t : ℕ) : ℤ) = (s : ℤ) * (t : ℤ) := by push_cast; ring
    rw [h4] at h3; exact h3

/-- Bezout: if `s` and `t` are coprime in ℤ, there exists `a` with
`s ∣ (a - b)` and `t ∣ (a - c)` for any `b, c`. -/
lemma exists_crt (s t b c : ℤ) (hst : IsCoprime s t) :
    ∃ a : ℤ, s ∣ (a - b) ∧ t ∣ (a - c) := by
  obtain ⟨x, y, hxy⟩ := hst
  -- x*s + y*t = 1
  -- Take a = b * (y * t) + c * (x * s) = b * y * t + c * x * s.
  -- a - b = b*y*t + c*x*s - b = b*(y*t - 1) + c*x*s = -b*x*s + c*x*s = (c - b)*x*s = s*(c-b)*x.
  -- a - c = b*y*t + c*x*s - c = b*y*t + c*(x*s - 1) = b*y*t - c*y*t = (b - c)*y*t = t*(b-c)*y.
  refine ⟨b * y * t + c * x * s, ?_, ?_⟩
  · refine ⟨(c - b) * x, ?_⟩
    linear_combination b * hxy
  · refine ⟨(b - c) * y, ?_⟩
    linear_combination c * hxy

/-- Given `m | p(b)` with `m ≠ 0`, and any integer `a₀`, we can find `a` with
both `m | p(a)` and `p(a₀) | p(a)`. -/
lemma extend_divisibility (poly : ℤ[X]) (b a₀ : ℤ) (m : ℤ) (hm : m ≠ 0)
    (hmb : m ∣ poly.eval b) :
    ∃ a : ℤ, m ∣ poly.eval a ∧ poly.eval a₀ ∣ poly.eval a := by
  by_cases hpa₀ : poly.eval a₀ = 0
  · -- p(a₀) = 0. Take a = a₀. Then m ∣ p(a) = 0 trivially, p(a₀) ∣ p(a₀).
    refine ⟨a₀, ?_, dvd_refl _⟩
    rw [hpa₀]
    exact dvd_zero m
  · obtain ⟨s, t, hs_m, ht_a₀, hst, hm_st, ha₀_st⟩ :=
      exists_coprime_factorization m (poly.eval a₀) hm hpa₀
    obtain ⟨a, hsa, hta⟩ := exists_crt s t b a₀ hst
    have hsp : s ∣ poly.eval a := by
      have h1 : (a - b) ∣ poly.eval a - poly.eval b := sub_dvd_eval_sub a b poly
      have h2 : s ∣ poly.eval a - poly.eval b := dvd_trans hsa h1
      have h3 : s ∣ poly.eval b := dvd_trans hs_m hmb
      have : s ∣ (poly.eval a - poly.eval b) + poly.eval b := dvd_add h2 h3
      simpa using this
    have htp : t ∣ poly.eval a := by
      have h1 : (a - a₀) ∣ poly.eval a - poly.eval a₀ := sub_dvd_eval_sub a a₀ poly
      have h2 : t ∣ poly.eval a - poly.eval a₀ := dvd_trans hta h1
      have h3 : t ∣ poly.eval a₀ := ht_a₀
      have : t ∣ (poly.eval a - poly.eval a₀) + poly.eval a₀ := dvd_add h2 h3
      simpa using this
    have hstp : (s * t : ℤ) ∣ poly.eval a := hst.mul_dvd hsp htp
    exact ⟨a, dvd_trans hm_st hstp, dvd_trans ha₀_st hstp⟩

snip end

/-- The main problem: given `p ∈ ℤ[X]` and a nonempty finite set `S` of
integers, there exists `a ∈ ℤ` with `p(s) ∣ p(a)` for every `s ∈ S`. -/
problem imc2008_p3 (p : ℤ[X]) (S : Finset ℤ) (hS : S.Nonempty) :
    ∃ a : ℤ, ∀ s ∈ S, p.eval s ∣ p.eval a := by
  -- Induction on S.
  induction S using Finset.induction with
  | empty => exact absurd hS Finset.not_nonempty_empty
  | insert s₀ T hs₀ ih =>
    by_cases hT : T.Nonempty
    · obtain ⟨a', ha'⟩ := ih hT
      -- Use extend_divisibility with m = p(a') if p(a') ≠ 0.
      by_cases hpa' : p.eval a' = 0
      · -- p(a') = 0, so every p(s) | p(a') = 0. We can just take a = a'.
        refine ⟨a', ?_⟩
        intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · rw [hpa']; exact dvd_zero _
        · exact ha' s hs
      · obtain ⟨a, hma, hs₀a⟩ := extend_divisibility p a' s₀ (p.eval a') hpa' dvd_rfl
        refine ⟨a, ?_⟩
        intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hs₀a
        · exact dvd_trans (ha' s hs) hma
    · rw [Finset.not_nonempty_iff_eq_empty] at hT
      subst hT
      refine ⟨s₀, ?_⟩
      intro s hs
      rw [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · exact dvd_refl _
      · exact absurd hs (Finset.notMem_empty _)

end Imc2008P3
