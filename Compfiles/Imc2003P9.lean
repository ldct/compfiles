/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 9
(IMC 2003, Day 2, Problem 3)

Let `A` be a closed nonempty subset of `ℝⁿ`. Let
`B = { b : ∃! a₀ ∈ A, ‖a₀ - b‖ = dist(b, A) }`. Show that `B` is dense in `ℝⁿ`.
-/

namespace Imc2003P9

open Metric RealInnerProductSpace

snip begin

/-
Sketch. Take `b₀ ∈ ℝⁿ`. If `b₀ ∈ A` then `b₀` itself is its unique nearest
point, so `b₀ ∈ B`. Otherwise let `ρ = dist(b₀, A) > 0`. Compactness of
closed-bounded sets in `ℝⁿ` gives some `a₀ ∈ A` with `‖a₀ - b₀‖ = ρ`. For
`s ∈ (0, 1)`, set `aₛ = b₀ + s • (a₀ - b₀)`. Then `aₛ` lies within distance
`s ρ` of `b₀`, and `a₀` is the unique nearest point of `A` to `aₛ`. The reverse
triangle inequality gives `‖b - aₛ‖ ≥ ‖b - b₀‖ - ‖b₀ - aₛ‖ ≥ (1 - s) ρ` for
all `b ∈ A`. If equality holds then `‖b - b₀‖ = ρ`, and an inner-product
computation shows `⟨b - b₀, a₀ - b₀⟩ = ρ²`, i.e. equality in Cauchy–Schwarz,
which forces `b - b₀ = a₀ - b₀`. Hence `aₛ ∈ B`, and taking `s` small shows
`b₀` is arbitrarily close to a point of `B`.
-/

snip end

/-- The set of points with a unique nearest neighbour in `A`. -/
def B {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  { b | ∃! a₀ : EuclideanSpace ℝ (Fin n), a₀ ∈ A ∧ ‖a₀ - b‖ = infDist b A }

problem imc2003_p9 {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA_closed : IsClosed A) (hA_ne : A.Nonempty) :
    Dense (B A) := by
  classical
  intro b₀
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Case 1: b₀ ∈ A. Then b₀ itself works.
  by_cases hb₀A : b₀ ∈ A
  · refine ⟨b₀, ?_, ?_⟩
    · refine ⟨b₀, ⟨hb₀A, ?_⟩, ?_⟩
      · simp [Metric.infDist_zero_of_mem hb₀A]
      · rintro a ⟨haA, ha_eq⟩
        have h0 : Metric.infDist b₀ A = 0 := Metric.infDist_zero_of_mem hb₀A
        have h1 : ‖a - b₀‖ = 0 := by rw [ha_eq, h0]
        have h2 : a - b₀ = 0 := by rwa [norm_eq_zero] at h1
        exact sub_eq_zero.mp h2
    · simpa using hε
  -- Case 2: b₀ ∉ A.
  · set ρ : ℝ := Metric.infDist b₀ A with hρ_def
    have hρ_pos : 0 < ρ :=
      (hA_closed.notMem_iff_infDist_pos hA_ne).mp hb₀A
    obtain ⟨a₀, ha₀A, ha₀_dist⟩ :=
      hA_closed.exists_infDist_eq_dist hA_ne b₀
    have ha₀_norm : ‖a₀ - b₀‖ = ρ := by
      rw [← dist_eq_norm, dist_comm, ← ha₀_dist]
    -- Pick s.
    set s : ℝ := min (ε / (2 * ρ)) (1 / 2) with hs_def
    have hs_pos : 0 < s := by
      apply lt_min
      · positivity
      · norm_num
    have hs_le_half : s ≤ 1 / 2 := min_le_right _ _
    have hs_lt_one : s < 1 := by linarith
    have h1ms_pos : 0 < 1 - s := by linarith
    have hs_le_eps : s * ρ ≤ ε / 2 := by
      have h1 : s ≤ ε / (2 * ρ) := min_le_left _ _
      have h2 : s * ρ ≤ (ε / (2 * ρ)) * ρ := by nlinarith [hρ_pos]
      have heq : (ε / (2 * ρ)) * ρ = ε / 2 := by field_simp
      linarith
    -- Define aₛ.
    set as : EuclideanSpace ℝ (Fin n) := b₀ + s • (a₀ - b₀) with has_def
    have h_as_sub_b₀ : as - b₀ = s • (a₀ - b₀) := by
      rw [has_def]; abel
    have h_dist_as_b₀ : ‖as - b₀‖ = s * ρ := by
      rw [h_as_sub_b₀, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, ha₀_norm]
    have h_a₀_sub_as : a₀ - as = (1 - s) • (a₀ - b₀) := by
      rw [has_def, sub_smul, one_smul]
      have : a₀ - (b₀ + s • (a₀ - b₀)) = (a₀ - b₀) - s • (a₀ - b₀) := by abel
      rw [this]
    have h_dist_a₀_as : ‖a₀ - as‖ = (1 - s) * ρ := by
      rw [h_a₀_sub_as, norm_smul, Real.norm_eq_abs, abs_of_pos h1ms_pos, ha₀_norm]
    -- ‖as - b₀‖ = ‖b₀ - as‖
    have h_dist_b₀_as : ‖b₀ - as‖ = s * ρ := by
      rw [norm_sub_rev]; exact h_dist_as_b₀
    -- Key lemma: for b ∈ A, ‖a₀ - as‖ ≤ ‖b - as‖.
    have h_key : ∀ b ∈ A, ‖a₀ - as‖ ≤ ‖b - as‖ := by
      intro b hbA
      have hb_dist : ρ ≤ ‖b - b₀‖ := by
        have h1 := Metric.infDist_le_dist_of_mem hbA (x := b₀)
        rw [dist_comm, dist_eq_norm] at h1
        exact h1
      have htri : ‖b - b₀‖ ≤ ‖b - as‖ + ‖as - b₀‖ := by
        have h1 := norm_sub_le (b - as) (b₀ - as)
        have heq : b - as - (b₀ - as) = b - b₀ := by abel
        rw [heq] at h1
        have h2 : ‖b₀ - as‖ = ‖as - b₀‖ := norm_sub_rev _ _
        linarith
      rw [h_dist_a₀_as]
      rw [h_dist_as_b₀] at htri
      have : (1 - s) * ρ = ρ - s * ρ := by ring
      linarith
    refine ⟨as, ?_, ?_⟩
    · -- aₛ ∈ B A.
      have h_infDist_ge : (1 - s) * ρ ≤ Metric.infDist as A := by
        rw [← h_dist_a₀_as]
        rw [Metric.le_infDist hA_ne]
        intro b hbA
        rw [dist_comm, dist_eq_norm]
        exact h_key b hbA
      have h_infDist_le : Metric.infDist as A ≤ (1 - s) * ρ := by
        have h1 := Metric.infDist_le_dist_of_mem ha₀A (x := as)
        rw [dist_comm, dist_eq_norm, h_dist_a₀_as] at h1
        exact h1
      have h_infDist_eq : Metric.infDist as A = (1 - s) * ρ :=
        le_antisymm h_infDist_le h_infDist_ge
      refine ⟨a₀, ⟨ha₀A, ?_⟩, ?_⟩
      · rw [h_dist_a₀_as, h_infDist_eq]
      · rintro b ⟨hbA, hb_eq⟩
        have hb_eq2 : ‖b - as‖ = (1 - s) * ρ := by
          rw [hb_eq, h_infDist_eq]
        have hb_dist : ρ ≤ ‖b - b₀‖ := by
          have h1 := Metric.infDist_le_dist_of_mem hbA (x := b₀)
          rw [dist_comm, dist_eq_norm] at h1
          exact h1
        have h_b_b₀_le : ‖b - b₀‖ ≤ ρ := by
          have h1 := norm_sub_le (b - as) (b₀ - as)
          have heq : b - as - (b₀ - as) = b - b₀ := by abel
          rw [heq] at h1
          rw [hb_eq2, h_dist_b₀_as] at h1
          linarith
        have h_b_b₀ : ‖b - b₀‖ = ρ := le_antisymm h_b_b₀_le hb_dist
        -- Inner product computation.
        have hsq : ‖b - as‖^2 =
            ‖b - b₀‖^2 - 2 * @inner ℝ _ _ (b - b₀) (as - b₀) + ‖as - b₀‖^2 := by
          have heq : b - as = (b - b₀) - (as - b₀) := by abel
          rw [heq, @norm_sub_sq_real _ _ _ (b - b₀) (as - b₀)]
        rw [hb_eq2, h_b_b₀, h_dist_as_b₀] at hsq
        rw [h_as_sub_b₀, inner_smul_right] at hsq
        -- hsq : ((1-s)*ρ)^2 = ρ^2 - 2*(s*⟨b-b₀, a₀-b₀⟩) + (s*ρ)^2
        have hs_ne : s ≠ 0 := ne_of_gt hs_pos
        have hI : @inner ℝ _ _ (b - b₀) (a₀ - b₀) = ρ^2 := by
          have hexp : ρ^2 - 2 * (s * @inner ℝ _ _ (b - b₀) (a₀ - b₀)) + (s * ρ)^2
              = ((1 - s) * ρ)^2 := hsq.symm
          -- ((1-s)ρ)² = ρ² - 2sρ² + s²ρ² = ρ² - 2sρ² + (sρ)²
          have h1 : 2 * (s * @inner ℝ _ _ (b - b₀) (a₀ - b₀)) = 2 * s * ρ^2 := by
            nlinarith [hexp]
          have h2 : s * @inner ℝ _ _ (b - b₀) (a₀ - b₀) = s * ρ^2 := by linarith
          exact mul_left_cancel₀ hs_ne h2
        have h_cs : @inner ℝ _ _ (b - b₀) (a₀ - b₀) = ‖b - b₀‖ * ‖a₀ - b₀‖ := by
          rw [hI, h_b_b₀, ha₀_norm]; ring
        have h_par : ‖a₀ - b₀‖ • (b - b₀) = ‖b - b₀‖ • (a₀ - b₀) :=
          inner_eq_norm_mul_iff_real.mp h_cs
        rw [h_b_b₀, ha₀_norm] at h_par
        have hρne : ρ ≠ 0 := ne_of_gt hρ_pos
        have h_eq : b - b₀ = a₀ - b₀ :=
          smul_right_injective _ hρne h_par
        have : b = a₀ := by
          have h1 : b - b₀ + b₀ = a₀ - b₀ + b₀ := by rw [h_eq]
          simpa using h1
        exact this
    · rw [dist_eq_norm, h_dist_b₀_as]
      linarith

end Imc2003P9
