/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 7

Let `D ⊆ ℂ` be an open set containing the closed unit disk. Let
`f : D → ℂ` be holomorphic, and let `p(z)` be a monic polynomial. Prove
that

  `|f(0)| ≤ max_{|z|=1} |f(z) p(z)|`.
-/

namespace Imc2021P7

open Complex Finset

/-- The "reverse" polynomial of `p`: `q(z) = z^d · conj(p(1/conj(z)))` for
`d = p.natDegree`. Defined directly as a sum so we can work with it as a
function `ℂ → ℂ`. If `p(z) = Σ a_k z^k`, then `q(z) = Σ conj(a_k) z^(d-k)`. -/
private noncomputable def reversePoly (p : Polynomial ℂ) : ℂ → ℂ :=
  fun z => ∑ k ∈ range (p.natDegree + 1), (starRingEnd ℂ) (p.coeff k) * z ^ (p.natDegree - k)

private lemma reversePoly_zero_of_monic {p : Polynomial ℂ} (hp : p.Monic) :
    reversePoly p 0 = 1 := by
  unfold reversePoly
  rw [Finset.sum_eq_single p.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree, map_one]
  · intro k hk hkd
    rw [mem_range] at hk
    have : 0 < p.natDegree - k := Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkd)
    rw [zero_pow this.ne', mul_zero]
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_self _)) h

private lemma reversePoly_differentiable (p : Polynomial ℂ) :
    Differentiable ℂ (reversePoly p) := by
  unfold reversePoly
  exact Differentiable.fun_sum (fun k _ => (differentiable_pow _).const_mul _)

private lemma norm_reversePoly_eq_of_norm_one {p : Polynomial ℂ} {z : ℂ} (hz : ‖z‖ = 1) :
    ‖reversePoly p z‖ = ‖p.eval z‖ := by
  -- On the unit circle, z * conj(z) = 1, so conj(z) = 1/z.
  -- reversePoly p z = z^d * Σ conj(a_k) / z^k (formally),
  -- but we'll just prove ‖·‖ directly.
  unfold reversePoly
  -- Key identity: for |z|=1, conj(z) = z⁻¹.
  have hz' : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
  -- Compute z * conj(z) = |z|^2 = 1.
  have hconj : (starRingEnd ℂ) z = z⁻¹ := by
    have h1 : z * (starRingEnd ℂ) z = 1 := by
      have hns : Complex.normSq z = 1 := by
        rw [Complex.normSq_eq_norm_sq, hz]; norm_num
      have := Complex.mul_conj z
      rw [hns] at this
      exact_mod_cast this
    field_simp
    linear_combination h1
  -- We have reversePoly p z = z^d * conj(p.eval z).
  have hkey : (∑ k ∈ range (p.natDegree + 1),
      (starRingEnd ℂ) (p.coeff k) * z ^ (p.natDegree - k))
      = z ^ p.natDegree * (starRingEnd ℂ) (p.eval z) := by
    rw [p.eval_eq_sum_range, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [map_mul, map_pow, hconj]
    have hle : k ≤ p.natDegree := Nat.lt_succ_iff.mp hk
    rw [inv_pow]
    have hzk : z ^ k ≠ 0 := pow_ne_zero _ hz'
    rw [show z ^ p.natDegree = z ^ (p.natDegree - k) * z ^ k from
        by rw [← pow_add, Nat.sub_add_cancel hle]]
    field_simp
  rw [hkey, norm_mul, norm_pow, hz, one_pow, one_mul]
  rw [Complex.norm_conj]

/-- Problem statement: for any polynomial `p` that is monic (leading coefficient 1)
and any function `f` holomorphic on an open set `D` containing the closed unit
disk, we have `|f(0)| ≤ max_{|z|=1} |f(z) * p(z)|`.

Proof: introduce the "reverse" polynomial `q(z) = z^d * conj(p(1/conj(z)))`.
On the unit circle `|q(z)| = |p(z)|`, and `q(0) = 1`. Applying the maximum
modulus principle to `f * q` on the closed disk gives
`|f(0)| = |f(0) * q(0)| ≤ max_{|z|=1} |f(z) * q(z)| = max_{|z|=1} |f(z) * p(z)|`.
-/
problem imc2021_p7 (D : Set ℂ) (hD : IsOpen D) (hD1 : Metric.closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D)
    (p : Polynomial ℂ) (hp : p.Monic) :
    ‖f 0‖ ≤ sSup ((fun z => ‖f z * p.eval z‖) '' Metric.sphere (0 : ℂ) 1) := by
  set q : ℂ → ℂ := reversePoly p with hq_def
  have hq_diff : Differentiable ℂ q := reversePoly_differentiable p
  have hq_zero : q 0 = 1 := reversePoly_zero_of_monic hp
  have hq_norm : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖q z‖ = ‖p.eval z‖ := by
    intro z hz
    apply norm_reversePoly_eq_of_norm_one
    rw [Metric.mem_sphere] at hz
    simpa [dist_zero_right] using hz
  -- The set S is nonempty and bounded, since sphere is compact and fq is continuous.
  set S := (fun z => ‖f z * q z‖) '' Metric.sphere (0 : ℂ) 1 with hS_def
  have hsphere_compact : IsCompact (Metric.sphere (0 : ℂ) 1) :=
    isCompact_sphere 0 1
  have hsphere_ne : (Metric.sphere (0 : ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hsphere_sub : Metric.sphere (0 : ℂ) 1 ⊆ D := by
    intro z hz
    apply hD1
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_closedBall]
    exact le_of_eq hz
  have hfq_cont : ContinuousOn (fun z => f z * q z) (Metric.sphere (0 : ℂ) 1) := by
    apply ContinuousOn.mul
    · exact (hf.mono hsphere_sub).continuousOn
    · exact hq_diff.continuous.continuousOn
  have hS_compact : IsCompact S := hsphere_compact.image_of_continuousOn hfq_cont.norm
  have hS_bdd : BddAbove S := hS_compact.bddAbove
  have hS_ne : S.Nonempty := hsphere_ne.image _
  -- M := sSup S, the right-hand side of the goal (up to f*q vs f*p identification).
  set M := sSup S with hM_def
  -- Replace M with the target expression at the end.
  have hM_eq : sSup ((fun z => ‖f z * p.eval z‖) '' Metric.sphere (0 : ℂ) 1) = M := by
    rw [hM_def, hS_def]
    congr 1
    apply Set.image_congr
    intro z hz
    rw [norm_mul, norm_mul, hq_norm z hz]
  rw [hM_eq]
  -- Now apply maximum modulus principle to f * q on ball 0 1.
  have hball_bdd : Bornology.IsBounded (Metric.ball (0 : ℂ) 1) := Metric.isBounded_ball
  have hclosed_sub : Metric.closedBall (0 : ℂ) 1 ⊆ D := hD1
  have hf_diffcont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1) := by
    have hfd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) 1) := hf.mono hD1
    exact hfd.diffContOnCl_ball (by rfl)
  have hq_diffcont : DiffContOnCl ℂ q (Metric.ball (0 : ℂ) 1) := hq_diff.diffContOnCl
  have hfq_diffcont : DiffContOnCl ℂ (fun z => f z * q z) (Metric.ball (0 : ℂ) 1) := by
    have := hf_diffcont.smul (𝕜' := ℂ) hq_diffcont
    simpa [smul_eq_mul] using this
  have h0mem : (0 : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    simp
  have hbound : ∀ z ∈ frontier (Metric.ball (0 : ℂ) 1), ‖f z * q z‖ ≤ M := by
    intro z hz
    rw [frontier_ball (0 : ℂ) one_ne_zero] at hz
    exact le_csSup hS_bdd ⟨z, hz, rfl⟩
  have hmain := Complex.norm_le_of_forall_mem_frontier_norm_le hball_bdd hfq_diffcont hbound h0mem
  -- At z = 0: f(0) * q(0) = f(0) * 1 = f(0).
  simp only [hq_zero, mul_one] at hmain
  exact hmain

end Imc2021P7
