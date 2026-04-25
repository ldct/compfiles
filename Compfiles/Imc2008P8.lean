/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2008, Problem 8
(IMC 2008, Day 2, Problem 2)

Two different ellipses in the plane share a common focus.
Prove that they have at most two common points.

## Proof sketch

We use the two-foci definition of an ellipse: an ellipse with foci `F, G`
and major-axis sum `c` is `{X : dist X F + dist X G = c}`. Non-degeneracy
requires `dist F G < c`.

For `X` on both ellipses sharing focus `F`, squaring the relations
`‖X-Gᵢ‖ = cᵢ - ‖X-F‖` and combining yields a linear equation
`2 ⟪X, v⟫_ℝ = K` in `X` with `v = c₂ • (G₁-F) - c₁ • (G₂-F)`.

For three pairwise-distinct common points `X, Y, Z`, this forces
`⟪Y-X, v⟫ = ⟪Z-X, v⟫ = 0`. If `v ≠ 0`, the orthogonal complement of
`v` in `ℝ²` is one-dimensional, so the three points are collinear. A
direct algebraic squaring argument shows that a non-degenerate ellipse
meets any line in at most two points (the leading coefficient
`4c²‖n‖² - 4⟪n, F-G⟫²` of the resulting quadratic is positive because
`‖F-G‖ < c`). So two of the three points must coincide.

If `v = 0`, then `c₂ • (G₁-F) = c₁ • (G₂-F)` and combined with the
existence of a common point an algebraic computation forces `c₁ = c₂`
and `G₁ = G₂`, so the two ellipses are equal — contradicting "different
ellipses".
-/

namespace Imc2008P8

open scoped InnerProductSpace

abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- An ellipse with foci `F, G` and major-axis sum `c`. -/
def Ellipse (F G : Pt) (c : ℝ) : Set Pt :=
  {X | dist X F + dist X G = c}

/-- Non-degeneracy: `dist F G < c`. -/
def IsEllipse (F G : Pt) (c : ℝ) : Prop := dist F G < c

snip begin

/-- Inner product on `Pt = EuclideanSpace ℝ (Fin 2)` is the dot product. -/
lemma inner_def (u v : Pt) : ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  have h0 : (inner ℝ (u 0) (v 0) : ℝ) = u 0 * v 0 := by
    show v 0 * (starRingEnd ℝ (u 0)) = u 0 * v 0
    simp [mul_comm]
  have h1 : (inner ℝ (u 1) (v 1) : ℝ) = u 1 * v 1 := by
    show v 1 * (starRingEnd ℝ (u 1)) = u 1 * v 1
    simp [mul_comm]
  show inner ℝ (u 0) (v 0) + inner ℝ (u 1) (v 1) = u 0 * v 0 + u 1 * v 1
  rw [h0, h1]

/-- The constant `K` on the right-hand side of the linear equation. -/
private noncomputable def Kconst (F G₁ G₂ : Pt) (c₁ c₂ : ℝ) : ℝ :=
  c₂ * ‖G₁‖ ^ 2 - c₁ * ‖G₂‖ ^ 2 + (c₁ - c₂) * ‖F‖ ^ 2 - c₁ * c₂ * (c₁ - c₂)

/-- Key linear identity: for any X ∈ E₁ ∩ E₂ where the two ellipses
share focus F, `2 * ⟪X, v⟫_ℝ` equals the constant `K`, where
`v = c₂ • (G₁ - F) - c₁ • (G₂ - F)`. -/
lemma linear_eqn_of_mem_inter
    {F G₁ G₂ : Pt} {c₁ c₂ : ℝ} {X : Pt}
    (h₁ : X ∈ Ellipse F G₁ c₁) (h₂ : X ∈ Ellipse F G₂ c₂) :
    2 * ⟪X, c₂ • (G₁ - F) - c₁ • (G₂ - F)⟫_ℝ = Kconst F G₁ G₂ c₁ c₂ := by
  have e₁ : dist X F + dist X G₁ = c₁ := h₁
  have e₂ : dist X F + dist X G₂ = c₂ := h₂
  have sq₁ : ‖X - G₁‖ ^ 2 = (c₁ - ‖X - F‖) ^ 2 := by
    have hh : ‖X - G₁‖ = c₁ - ‖X - F‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]; linarith
    rw [hh]
  have sq₂ : ‖X - G₂‖ ^ 2 = (c₂ - ‖X - F‖) ^ 2 := by
    have hh : ‖X - G₂‖ = c₂ - ‖X - F‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]; linarith
    rw [hh]
  have ex₁ : ‖X - G₁‖ ^ 2 = ‖X‖ ^ 2 - 2 * ⟪X, G₁⟫_ℝ + ‖G₁‖ ^ 2 := norm_sub_sq_real X G₁
  have ex₂ : ‖X - G₂‖ ^ 2 = ‖X‖ ^ 2 - 2 * ⟪X, G₂⟫_ℝ + ‖G₂‖ ^ 2 := norm_sub_sq_real X G₂
  have exF : ‖X - F‖ ^ 2 = ‖X‖ ^ 2 - 2 * ⟪X, F⟫_ℝ + ‖F‖ ^ 2 := norm_sub_sq_real X F
  set a : ℝ := ⟪X, F⟫_ℝ
  set b : ℝ := ⟪X, G₁⟫_ℝ
  set d : ℝ := ⟪X, G₂⟫_ℝ
  set N : ℝ := ‖X‖ ^ 2
  have hv : ⟪X, c₂ • (G₁ - F) - c₁ • (G₂ - F)⟫_ℝ
      = c₂ * (b - a) - c₁ * (d - a) := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right,
        inner_sub_right, inner_sub_right]
  rw [hv]
  have eq1 : 2 * c₁ * ‖X - F‖ = c₁ ^ 2 + 2 * b - 2 * a + ‖F‖ ^ 2 - ‖G₁‖ ^ 2 := by
    have h1 : ‖X - G₁‖ ^ 2 = c₁ ^ 2 - 2 * c₁ * ‖X - F‖ + ‖X - F‖ ^ 2 := by
      rw [sq₁]; ring
    linarith [h1, ex₁, exF]
  have eq2 : 2 * c₂ * ‖X - F‖ = c₂ ^ 2 + 2 * d - 2 * a + ‖F‖ ^ 2 - ‖G₂‖ ^ 2 := by
    have h1 : ‖X - G₂‖ ^ 2 = c₂ ^ 2 - 2 * c₂ * ‖X - F‖ + ‖X - F‖ ^ 2 := by
      rw [sq₂]; ring
    linarith [h1, ex₂, exF]
  have e3 : c₂ * (2 * c₁ * ‖X - F‖) = c₂ * (c₁ ^ 2 + 2 * b - 2 * a + ‖F‖ ^ 2 - ‖G₁‖ ^ 2) := by
    rw [eq1]
  have e4 : c₁ * (2 * c₂ * ‖X - F‖) = c₁ * (c₂ ^ 2 + 2 * d - 2 * a + ‖F‖ ^ 2 - ‖G₂‖ ^ 2) := by
    rw [eq2]
  have h_eq : c₂ * (c₁ ^ 2 + 2 * b - 2 * a + ‖F‖ ^ 2 - ‖G₁‖ ^ 2)
      = c₁ * (c₂ ^ 2 + 2 * d - 2 * a + ‖F‖ ^ 2 - ‖G₂‖ ^ 2) := by linarith [e3, e4]
  show 2 * (c₂ * (b - a) - c₁ * (d - a)) = Kconst F G₁ G₂ c₁ c₂
  unfold Kconst
  linarith [h_eq]

/-- For two vectors `u, w` perpendicular to a non-zero vector `v` in
`Pt = EuclideanSpace ℝ (Fin 2)`, with `u ≠ 0`, there exists `t : ℝ`
with `w = t • u`. -/
lemma collinear_of_perp_in_2d
    {v u w : Pt} (hv : v ≠ 0)
    (hu : ⟪u, v⟫_ℝ = 0) (hw : ⟪w, v⟫_ℝ = 0)
    (hu_ne : u ≠ 0) :
    ∃ t : ℝ, w = t • u := by
  have hu_inner : u 0 * v 0 + u 1 * v 1 = 0 := by rw [← inner_def]; exact hu
  have hw_inner : w 0 * v 0 + w 1 * v 1 = 0 := by rw [← inner_def]; exact hw
  have hv_ne : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext i
    fin_cases i <;> simp [h.1, h.2]
  have hu_neq : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu_ne
    ext i
    fin_cases i <;> simp [h.1, h.2]
  -- Cross product u 0 * w 1 = u 1 * w 0.
  have hcross : u 0 * w 1 = u 1 * w 0 := by
    rcases hv_ne with hv0 | hv1
    · have h1 : u 0 * v 0 = -(u 1 * v 1) := by linarith
      have h2 : w 0 * v 0 = -(w 1 * v 1) := by linarith
      have h3 : (u 0 * w 1 - u 1 * w 0) * v 0 = 0 := by
        have hh : u 0 * v 0 * w 1 = u 1 * w 0 * v 0 := by
          rw [h1]
          have : -(u 1 * v 1) * w 1 = u 1 * (-(w 1 * v 1)) := by ring
          rw [this, ← h2]; ring
        linarith
      have : u 0 * w 1 - u 1 * w 0 = 0 :=
        (mul_eq_zero.mp h3).resolve_right hv0
      linarith
    · have h1 : u 1 * v 1 = -(u 0 * v 0) := by linarith
      have h2 : w 1 * v 1 = -(w 0 * v 0) := by linarith
      have h3 : (u 1 * w 0 - u 0 * w 1) * v 1 = 0 := by
        have hh : u 1 * v 1 * w 0 = u 0 * w 1 * v 1 := by
          rw [h1]
          have : -(u 0 * v 0) * w 0 = u 0 * (-(w 0 * v 0)) := by ring
          rw [this, ← h2]; ring
        linarith
      have : u 1 * w 0 - u 0 * w 1 = 0 :=
        (mul_eq_zero.mp h3).resolve_right hv1
      linarith
  -- Construct t.
  rcases hu_neq with hu0 | hu1
  · refine ⟨w 0 / u 0, ?_⟩
    ext i
    fin_cases i
    · show w 0 = ((w 0 / u 0) • u) 0
      rw [PiLp.smul_apply]
      show w 0 = (w 0 / u 0) * u 0
      field_simp
    · show w 1 = ((w 0 / u 0) • u) 1
      rw [PiLp.smul_apply]
      show w 1 = (w 0 / u 0) * u 1
      have h_w1 : w 1 * u 0 = w 0 * u 1 := by linarith
      field_simp
      linarith
  · refine ⟨w 1 / u 1, ?_⟩
    ext i
    fin_cases i
    · show w 0 = ((w 1 / u 1) • u) 0
      rw [PiLp.smul_apply]
      show w 0 = (w 1 / u 1) * u 0
      have h_w0 : w 0 * u 1 = w 1 * u 0 := by linarith
      field_simp
      linarith
    · show w 1 = ((w 1 / u 1) • u) 1
      rw [PiLp.smul_apply]
      show w 1 = (w 1 / u 1) * u 1
      field_simp

/-- Three distinct values of `s` cannot all give a point `X + s • n` on
a non-degenerate ellipse `Ellipse F G c` (with `n ≠ 0`). -/
lemma at_most_two_on_line
    (X F G n : Pt) (c : ℝ)
    (hE : IsEllipse F G c) (hn : n ≠ 0) :
    ∀ s₁ s₂ s₃ : ℝ,
      X + s₁ • n ∈ Ellipse F G c →
      X + s₂ • n ∈ Ellipse F G c →
      X + s₃ • n ∈ Ellipse F G c →
      s₁ = s₂ ∨ s₁ = s₃ ∨ s₂ = s₃ := by
  intro s₁ s₂ s₃ h1 h2 h3
  set A := ⟪n, X - F⟫_ℝ with hA
  set B := ⟪n, X - G⟫_ℝ with hB
  set N := ‖n‖ ^ 2 with hN
  set DF := ‖X - F‖ ^ 2 with hDF
  set DG := ‖X - G‖ ^ 2 with hDG
  set q := ⟪n, F - G⟫_ℝ with hq
  set α := 4 * c ^ 2 * N - 4 * q ^ 2 with hα_def
  set β := 8 * c ^ 2 * B - 4 * (c ^ 2 + DG - DF) * q with hβ_def
  set γ := 4 * c ^ 2 * DG - (c ^ 2 + DG - DF) ^ 2 with hγ_def
  have key : ∀ s : ℝ, X + s • n ∈ Ellipse F G c → α * s ^ 2 + β * s + γ = 0 := by
    intro s hs
    have hd : dist (X + s • n) F + dist (X + s • n) G = c := hs
    have hF_norm : ‖X + s • n - F‖ = dist (X + s • n) F := by rw [dist_eq_norm]
    have hG_norm : ‖X + s • n - G‖ = dist (X + s • n) G := by rw [dist_eq_norm]
    have hsub : ‖X + s • n - G‖ = c - ‖X + s • n - F‖ := by
      rw [hG_norm, hF_norm]; linarith
    have e_F : ‖X + s • n - F‖ ^ 2 = DF + 2 * s * A + s ^ 2 * N := by
      have heq : X + s • n - F = (X - F) + s • n := by abel
      rw [heq, norm_add_sq_real]
      have hsn : ‖(s • n : Pt)‖ ^ 2 = s ^ 2 * N := by
        rw [hN, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [hsn]
      have hAA : ⟪(X - F : Pt), s • n⟫_ℝ = s * A := by
        rw [inner_smul_right, hA, real_inner_comm]
      linarith [hAA]
    have e_G : ‖X + s • n - G‖ ^ 2 = DG + 2 * s * B + s ^ 2 * N := by
      have heq : X + s • n - G = (X - G) + s • n := by abel
      rw [heq, norm_add_sq_real]
      have hsn : ‖(s • n : Pt)‖ ^ 2 = s ^ 2 * N := by
        rw [hN, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [hsn]
      have hBB : ⟪(X - G : Pt), s • n⟫_ℝ = s * B := by
        rw [inner_smul_right, hB, real_inner_comm]
      linarith [hBB]
    have h_lin' : 2 * c * ‖X + s • n - G‖ = c ^ 2 + DG - DF + 2 * s * (B - A) := by
      have hsub' : ‖X + s • n - F‖ = c - ‖X + s • n - G‖ := by linarith
      have hsq' : ‖X + s • n - F‖ ^ 2 =
          c ^ 2 - 2 * c * ‖X + s • n - G‖ + ‖X + s • n - G‖ ^ 2 := by
        rw [hsub']; ring
      linarith [hsq', e_F, e_G]
    have h_sq2 : (2 * c * ‖X + s • n - G‖) ^ 2 =
        (c ^ 2 + DG - DF + 2 * s * (B - A)) ^ 2 := by rw [h_lin']
    have lhs_eq : (2 * c * ‖X + s • n - G‖) ^ 2 = 4 * c ^ 2 * (DG + 2 * s * B + s ^ 2 * N) := by
      have : (2 * c * ‖X + s • n - G‖) ^ 2 = 4 * c ^ 2 * ‖X + s • n - G‖ ^ 2 := by ring
      rw [this, e_G]
    have hBA : B - A = q := by
      rw [hA, hB, hq, ← inner_sub_right]; congr 1; abel
    have hh : 4 * c ^ 2 * (DG + 2 * s * B + s ^ 2 * N) =
        (c ^ 2 + DG - DF + 2 * s * q) ^ 2 := by
      rw [← lhs_eq, h_sq2, hBA]
    show α * s ^ 2 + β * s + γ = 0
    rw [hα_def, hβ_def, hγ_def]
    nlinarith [hh]
  have hc_pos : 0 < c := lt_of_le_of_lt dist_nonneg hE
  have hN_pos : 0 < N := by
    rw [hN]; have hn_pos : 0 < ‖n‖ := norm_pos_iff.mpr hn; positivity
  have h_FG : ‖F - G‖ ^ 2 < c ^ 2 := by
    have hd : dist F G = ‖F - G‖ := dist_eq_norm F G
    have hE' : ‖F - G‖ < c := hd ▸ hE
    have hnn : 0 ≤ ‖F - G‖ := norm_nonneg _
    nlinarith
  have h_cs : q ^ 2 ≤ ‖n‖ ^ 2 * ‖F - G‖ ^ 2 := by
    have h_cs0 : |q| ≤ ‖n‖ * ‖F - G‖ := abs_real_inner_le_norm n (F - G)
    have hq_sq : |q| ^ 2 = q ^ 2 := sq_abs q
    have habs_nn : 0 ≤ |q| := abs_nonneg _
    have h_pow : |q| ^ 2 ≤ (‖n‖ * ‖F - G‖) ^ 2 :=
      pow_le_pow_left₀ habs_nn h_cs0 2
    have hp_sq : (‖n‖ * ‖F - G‖) ^ 2 = ‖n‖ ^ 2 * ‖F - G‖ ^ 2 := by ring
    linarith [h_pow, hq_sq, hp_sq]
  have lead_pos : 0 < α := by
    rw [hα_def]
    have h1 : q ^ 2 < ‖n‖ ^ 2 * c ^ 2 := by
      have hN_pos' : 0 < ‖n‖ ^ 2 := by rw [hN] at hN_pos; exact hN_pos
      have hh1 : ‖n‖ ^ 2 * ‖F - G‖ ^ 2 < ‖n‖ ^ 2 * c ^ 2 :=
        (mul_lt_mul_iff_of_pos_left hN_pos').mpr h_FG
      linarith [h_cs, hh1]
    have h2 : 4 * (‖n‖ ^ 2 * c ^ 2) = 4 * c ^ 2 * N := by rw [hN]; ring
    linarith
  have h1' : α * s₁ ^ 2 + β * s₁ + γ = 0 := key s₁ h1
  have h2' : α * s₂ ^ 2 + β * s₂ + γ = 0 := key s₂ h2
  have h3' : α * s₃ ^ 2 + β * s₃ + γ = 0 := key s₃ h3
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have d12 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : s₁ - s₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : s₂ - s₃ ≠ 0 := sub_ne_zero.mpr h23
  have eq12 : α * (s₁ + s₂) + β = 0 := by
    have h_diff : α * (s₁ ^ 2 - s₂ ^ 2) + β * (s₁ - s₂) = 0 := by linarith
    have h_fact : α * (s₁ ^ 2 - s₂ ^ 2) + β * (s₁ - s₂)
        = (s₁ - s₂) * (α * (s₁ + s₂) + β) := by ring
    rw [h_fact] at h_diff
    exact (mul_eq_zero.mp h_diff).resolve_left d12
  have eq13 : α * (s₁ + s₃) + β = 0 := by
    have h_diff : α * (s₁ ^ 2 - s₃ ^ 2) + β * (s₁ - s₃) = 0 := by linarith
    have h_fact : α * (s₁ ^ 2 - s₃ ^ 2) + β * (s₁ - s₃)
        = (s₁ - s₃) * (α * (s₁ + s₃) + β) := by ring
    rw [h_fact] at h_diff
    exact (mul_eq_zero.mp h_diff).resolve_left d13
  have h_a : α * (s₂ - s₃) = 0 := by linarith
  have hα_ne : α ≠ 0 := ne_of_gt lead_pos
  have : s₂ - s₃ = 0 := (mul_eq_zero.mp h_a).resolve_left hα_ne
  exact d23 this

/-- If `v = 0` (where `v = c₂ • (G₁-F) - c₁ • (G₂-F)`) and the two
ellipses share a common point, then they are equal. -/
lemma ellipses_eq_of_v_zero_and_common
    {F G₁ G₂ : Pt} {c₁ c₂ : ℝ}
    (h₁ : IsEllipse F G₁ c₁) (h₂ : IsEllipse F G₂ c₂)
    (hv : c₂ • (G₁ - F) - c₁ • (G₂ - F) = 0)
    {X : Pt} (hX1 : X ∈ Ellipse F G₁ c₁) (hX2 : X ∈ Ellipse F G₂ c₂) :
    Ellipse F G₁ c₁ = Ellipse F G₂ c₂ := by
  have hc₁_pos : 0 < c₁ := lt_of_le_of_lt dist_nonneg h₁
  have hc₂_pos : 0 < c₂ := lt_of_le_of_lt dist_nonneg h₂
  have hd1 : ‖G₁ - F‖ < c₁ := by
    have h : dist F G₁ < c₁ := h₁
    have heq : dist F G₁ = ‖G₁ - F‖ := by rw [dist_comm, dist_eq_norm]
    rw [heq] at h; exact h
  have hd2 : ‖G₂ - F‖ < c₂ := by
    have h : dist F G₂ < c₂ := h₂
    have heq : dist F G₂ = ‖G₂ - F‖ := by rw [dist_comm, dist_eq_norm]
    rw [heq] at h; exact h
  -- From hv: c₂ • (G₁ - F) = c₁ • (G₂ - F).
  have hv1 : c₂ • (G₁ - F) = c₁ • (G₂ - F) := by
    have hh : c₂ • (G₁ - F) - c₁ • (G₂ - F) + c₁ • (G₂ - F) = 0 + c₁ • (G₂ - F) := by
      rw [hv]
    rw [sub_add_cancel, zero_add] at hh
    exact hh
  -- The common point X gives K = 0.
  have hK : Kconst F G₁ G₂ c₁ c₂ = 0 := by
    have h := linear_eqn_of_mem_inter hX1 hX2
    rw [hv] at h
    simp at h
    linarith
  -- Unfold Kconst.
  have hK' : c₂ * ‖G₁‖ ^ 2 - c₁ * ‖G₂‖ ^ 2 + (c₁ - c₂) * ‖F‖ ^ 2 - c₁ * c₂ * (c₁ - c₂) = 0 := by
    unfold Kconst at hK; exact hK
  -- Substitute G_i = F + h_i where h_i = G_i - F.
  set h₁v := G₁ - F with hh₁v
  set h₂v := G₂ - F with hh₂v
  have hG₁ : G₁ = F + h₁v := by rw [hh₁v]; abel
  have hG₂ : G₂ = F + h₂v := by rw [hh₂v]; abel
  -- v = 0 gives c₂ h₁v = c₁ h₂v.
  have hh : c₂ • h₁v = c₁ • h₂v := hv1
  -- ‖G_i‖² = ‖F + h_iv‖² = ‖F‖² + 2 ⟪F, h_iv⟫ + ‖h_iv‖².
  have eF1 : ‖G₁‖ ^ 2 = ‖F‖ ^ 2 + 2 * ⟪F, h₁v⟫_ℝ + ‖h₁v‖ ^ 2 := by
    rw [hG₁]; exact norm_add_sq_real F h₁v
  have eF2 : ‖G₂‖ ^ 2 = ‖F‖ ^ 2 + 2 * ⟪F, h₂v⟫_ℝ + ‖h₂v‖ ^ 2 := by
    rw [hG₂]; exact norm_add_sq_real F h₂v
  -- 2⟪F, c₂ h₁v⟫ = 2⟪F, c₁ h₂v⟫.
  have hFh : c₂ * ⟪F, h₁v⟫_ℝ = c₁ * ⟪F, h₂v⟫_ℝ := by
    have : ⟪F, c₂ • h₁v⟫_ℝ = ⟪F, c₁ • h₂v⟫_ℝ := by rw [hh]
    rw [inner_smul_right, inner_smul_right] at this
    exact this
  -- K' simplifies to: c₂ ‖h₁v‖² - c₁ ‖h₂v‖² - c₁ c₂(c₁ - c₂) = 0
  have hK'' : c₂ * ‖h₁v‖ ^ 2 - c₁ * ‖h₂v‖ ^ 2 - c₁ * c₂ * (c₁ - c₂) = 0 := by
    have := hK'
    rw [eF1, eF2] at this
    linarith [hFh]
  -- Take norms: c₂² ‖h₁v‖² = c₁² ‖h₂v‖².
  have hnorms : c₂ ^ 2 * ‖h₁v‖ ^ 2 = c₁ ^ 2 * ‖h₂v‖ ^ 2 := by
    have hsmul : ‖c₂ • h₁v‖ ^ 2 = ‖c₁ • h₂v‖ ^ 2 := by rw [hh]
    rw [norm_smul, norm_smul] at hsmul
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hsmul
    rw [abs_of_pos hc₁_pos, abs_of_pos hc₂_pos] at hsmul
    have : (c₂ * ‖h₁v‖) ^ 2 = c₂ ^ 2 * ‖h₁v‖ ^ 2 := by ring
    rw [this] at hsmul
    have : (c₁ * ‖h₂v‖) ^ 2 = c₁ ^ 2 * ‖h₂v‖ ^ 2 := by ring
    rw [this] at hsmul
    exact hsmul
  -- ‖h₁v‖² < c₁², ‖h₂v‖² < c₂².
  have hh1_lt : ‖h₁v‖ ^ 2 < c₁ ^ 2 := by
    have hnn : 0 ≤ ‖h₁v‖ := norm_nonneg _
    nlinarith
  have hh2_lt : ‖h₂v‖ ^ 2 < c₂ ^ 2 := by
    have hnn : 0 ≤ ‖h₂v‖ := norm_nonneg _
    nlinarith
  have hc₁_ne : c₁ ≠ 0 := ne_of_gt hc₁_pos
  have hc₂_ne : c₂ ≠ 0 := ne_of_gt hc₂_pos
  -- Multiply hK'' by c₁: c₁ * (c₂ ‖h₁v‖² - c₁ ‖h₂v‖² - c₁c₂(c₁-c₂)) = 0
  -- Use hnorms to substitute c₁² ‖h₂v‖² = c₂² ‖h₁v‖²:
  -- c₁ * c₂ * ‖h₁v‖² - c₂² * ‖h₁v‖² - c₁² c₂ (c₁-c₂) = 0
  -- c₂ * (c₁ - c₂) * ‖h₁v‖² = c₁² c₂ (c₁-c₂)
  -- c₂ * (c₁ - c₂) * (‖h₁v‖² - c₁²) = 0
  have key_eq : c₂ * (c₁ - c₂) * (‖h₁v‖ ^ 2 - c₁ ^ 2) = 0 := by
    -- From hK'': c₂ ‖h₁v‖² - c₁ ‖h₂v‖² = c₁ c₂ (c₁ - c₂)
    -- Multiply by c₁: c₁ c₂ ‖h₁v‖² - c₁² ‖h₂v‖² = c₁² c₂ (c₁ - c₂)
    -- Use hnorms (c₁² ‖h₂v‖² = c₂² ‖h₁v‖²): c₁ c₂ ‖h₁v‖² - c₂² ‖h₁v‖² = c₁² c₂ (c₁ - c₂)
    -- Factor: c₂(c₁ - c₂) ‖h₁v‖² - c₁² c₂ (c₁ - c₂) = 0
    -- i.e., c₂ (c₁ - c₂) (‖h₁v‖² - c₁²) = 0.
    linear_combination c₁ * hK'' - hnorms
  have hh1_ne : ‖h₁v‖ ^ 2 - c₁ ^ 2 ≠ 0 := by
    have : ‖h₁v‖ ^ 2 - c₁ ^ 2 < 0 := by nlinarith [norm_nonneg h₁v, hd1]
    linarith
  have h2 : c₂ * (c₁ - c₂) = 0 := by
    rcases mul_eq_zero.mp key_eq with h | h
    · exact h
    · exact absurd h hh1_ne
  have hc1_eq_c2 : c₁ = c₂ := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hc₂_ne
    · linarith
  -- And then h₂v = h₁v.
  have hh_eq : h₁v = h₂v := by
    have hc : c₁ • h₁v = c₁ • h₂v := by
      have := hh
      rw [← hc1_eq_c2] at this
      exact this
    exact smul_right_injective Pt hc₁_ne hc
  -- So G₂ = G₁.
  have hG_eq : G₁ = G₂ := by
    rw [hG₁, hG₂, hh_eq]
  -- Conclude Ellipse F G₁ c₁ = Ellipse F G₂ c₂.
  rw [hG_eq, hc1_eq_c2]

snip end

problem imc2008_p8
    (F G₁ G₂ : Pt) (c₁ c₂ : ℝ)
    (h₁ : IsEllipse F G₁ c₁) (h₂ : IsEllipse F G₂ c₂)
    (hne : Ellipse F G₁ c₁ ≠ Ellipse F G₂ c₂) :
    ∀ (X Y Z : Pt), X ∈ Ellipse F G₁ c₁ ∩ Ellipse F G₂ c₂ →
      Y ∈ Ellipse F G₁ c₁ ∩ Ellipse F G₂ c₂ →
      Z ∈ Ellipse F G₁ c₁ ∩ Ellipse F G₂ c₂ →
      X = Y ∨ X = Z ∨ Y = Z := by
  intro X Y Z ⟨hX1, hX2⟩ ⟨hY1, hY2⟩ ⟨hZ1, hZ2⟩
  set v : Pt := c₂ • (G₁ - F) - c₁ • (G₂ - F) with hv_def
  have hKX := linear_eqn_of_mem_inter hX1 hX2
  have hKY := linear_eqn_of_mem_inter hY1 hY2
  have hKZ := linear_eqn_of_mem_inter hZ1 hZ2
  -- ⟪Y-X, v⟫ = 0 and ⟪Z-X, v⟫ = 0.
  have hYX_perp : ⟪Y - X, v⟫_ℝ = 0 := by
    rw [inner_sub_left]
    have h1 : 2 * ⟪X, v⟫_ℝ = 2 * ⟪Y, v⟫_ℝ := by rw [hv_def]; rw [hKX, hKY]
    linarith
  have hZX_perp : ⟪Z - X, v⟫_ℝ = 0 := by
    rw [inner_sub_left]
    have h1 : 2 * ⟪X, v⟫_ℝ = 2 * ⟪Z, v⟫_ℝ := by rw [hv_def]; rw [hKX, hKZ]
    linarith
  -- Case 1: v = 0 ⇒ ellipses are equal, contradiction.
  by_cases hv0 : v = 0
  · exfalso; apply hne
    exact ellipses_eq_of_v_zero_and_common h₁ h₂ hv0 hX1 hX2
  · -- v ≠ 0.
    by_cases hYX : Y = X
    · left; exact hYX.symm
    by_cases hZX : Z = X
    · right; left; exact hZX.symm
    have hYX_ne : Y - X ≠ 0 := sub_ne_zero.mpr (fun h => hYX h)
    have hZX_ne : Z - X ≠ 0 := sub_ne_zero.mpr (fun h => hZX h)
    obtain ⟨t, ht⟩ := collinear_of_perp_in_2d hv0 hYX_perp hZX_perp hYX_ne
    set n := Y - X with hn_def
    have hX_repr : X = X + (0 : ℝ) • n := by simp
    have hY_repr : Y = X + (1 : ℝ) • n := by simp [hn_def]
    have hZ_repr : Z = X + t • n := by
      have : Z = X + (Z - X) := by abel
      rw [this, ht, hn_def]
    have h_atm := at_most_two_on_line X F G₁ n c₁ h₁ hYX_ne 0 1 t
      (by rw [← hX_repr]; exact hX1)
      (by rw [← hY_repr]; exact hY1)
      (by rw [← hZ_repr]; exact hZ1)
    rcases h_atm with h01 | h0t | h1t
    · exfalso; exact zero_ne_one h01
    · exfalso; apply hZX
      rw [hZ_repr, ← h0t]; simp
    · right; right
      rw [hZ_repr, ← h1t]; simp [hn_def]

end Imc2008P8
