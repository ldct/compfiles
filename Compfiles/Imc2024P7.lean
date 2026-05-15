/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2024, Problem 7

Let `n` be a positive integer. Suppose that `A` and `B` are invertible `n × n`
matrices with complex entries such that `A + B = I` and
`(A^2 + B^2)(A^4 + B^4) = A^5 + B^5`.
Find all possible values of `det(A*B)` for the given `n`.

Answer: the set `{(1/4)^k | 0 ≤ k ≤ n}`.
-/

namespace Imc2024P7

open Matrix Polynomial

/-- The set of possible values of `det(A*B)`. -/
determine answer (n : ℕ) : Set ℂ :=
  { z | ∃ k : ℕ, k ≤ n ∧ z = (1 / 4 : ℂ) ^ k }

snip begin

/-- If `A + B = 1`, then `A * B = B * A`. -/
lemma comm_of_add_eq_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) : A * B = B * A := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  rw [hB]; noncomm_ring

/-- `A^2 + B^2 = 1 - 2*(A*B)` when `A + B = 1`. -/
lemma pow2_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) :
    A ^ 2 + B ^ 2 = 1 - 2 • (A * B) := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  subst hB
  noncomm_ring

/-- `A^4 + B^4 = 1 - 4*(A*B) + 2*(A*B)^2` when `A + B = 1`. -/
lemma pow4_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) :
    A ^ 4 + B ^ 4 = 1 - 4 • (A * B) + 2 • (A * B) ^ 2 := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  subst hB
  noncomm_ring

/-- `A^5 + B^5 = 1 - 5*(A*B) + 5*(A*B)^2` when `A + B = 1`. -/
lemma pow5_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1) :
    A ^ 5 + B ^ 5 = 1 - 5 • (A * B) + 5 • (A * B) ^ 2 := by
  have hB : B = 1 - A := by
    have : A + B - A = 1 - A := by rw [hAB]
    rw [add_sub_cancel_left] at this
    exact this
  subst hB
  noncomm_ring

/-- The main polynomial identity: under the hypotheses,
`4 (A*B)^3 - 5 (A*B)^2 + (A*B) = 0`. -/
lemma poly_identity {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A + B = 1)
    (hyp : (A ^ 2 + B ^ 2) * (A ^ 4 + B ^ 4) = A ^ 5 + B ^ 5) :
    4 • (A * B) ^ 3 - 5 • (A * B) ^ 2 + (A * B) = 0 := by
  have h2 := pow2_sum A B hAB
  have h4 := pow4_sum A B hAB
  have h5 := pow5_sum A B hAB
  rw [h2, h4, h5] at hyp
  -- hyp: (1 - 2C)(1 - 4C + 2C^2) = 1 - 5C + 5C^2
  set C := A * B with hC_def
  have hexpand : ((1 : Matrix (Fin n) (Fin n) ℂ) - 2 • C) * (1 - 4 • C + 2 • C ^ 2) =
      1 - 6 • C + 10 • C ^ 2 - 4 • C ^ 3 := by
    noncomm_ring
  rw [hexpand] at hyp
  -- hyp: 1 - 6C + 10C^2 - 4C^3 = 1 - 5C + 5C^2
  -- Subtract: 4C^3 - 5C^2 + C = 0, i.e. -(1 - 6C + 10C^2 - 4C^3) + (1 - 5C + 5C^2) = ...
  -- Direct: rearrange hyp.
  have := hyp
  -- 1 - 6C + 10C^2 - 4C^3 - (1 - 5C + 5C^2) = 0
  -- = -C + 5C^2 - 4C^3 = -(4C^3 - 5C^2 + C)
  have heq : (1 : Matrix (Fin n) (Fin n) ℂ) - 6 • C + 10 • C ^ 2 - 4 • C ^ 3
             - (1 - 5 • C + 5 • C ^ 2) = -(4 • C ^ 3 - 5 • C ^ 2 + C) := by
    noncomm_ring
  have hsub : (1 : Matrix (Fin n) (Fin n) ℂ) - 6 • C + 10 • C ^ 2 - 4 • C ^ 3
             - (1 - 5 • C + 5 • C ^ 2) = 0 := by
    rw [this]; abel
  rw [heq] at hsub
  exact neg_eq_zero.mp hsub

/-- If `C` is a matrix with `4 C^3 - 5 C^2 + C = 0` and `C` is invertible,
then `(C - 1)(C - (1/4)•1) = 0`. -/
lemma factor_poly {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (hC_unit : IsUnit C)
    (hpoly : 4 • C ^ 3 - 5 • C ^ 2 + C = 0) :
    (C - 1) * (C - (1 / 4 : ℂ) • 1) = 0 := by
  -- 4 C^3 - 5 C^2 + C = C (4 C^2 - 5 C + 1)
  have hfact : C * (4 • C ^ 2 - 5 • C + 1) = 0 := by
    have : C * (4 • C ^ 2 - 5 • C + 1) = 4 • C ^ 3 - 5 • C ^ 2 + C := by noncomm_ring
    rw [this, hpoly]
  -- Cancel C on the left.
  have hcancel : 4 • C ^ 2 - 5 • C + 1 = 0 := by
    obtain ⟨u, hu⟩ := hC_unit
    have key : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (C * (4 • C ^ 2 - 5 • C + 1)) =
        (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * 0 := by rw [hfact]
    rw [mul_zero, ← mul_assoc] at key
    have hinv : (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) * C = 1 := by
      rw [← hu]; exact Units.inv_mul u
    rw [hinv, one_mul] at key
    exact key
  -- Now (C - 1)(C - (1/4)•1) expanded: C*C - (1/4)•C - C + (1/4)•1
  -- 4•((C - 1)(C - (1/4)•1)) = 4•C^2 - C - 4C + 1 = 4C^2 - 5C + 1 = 0
  have h4 : (4 : ℂ) • ((C - 1) * (C - (1 / 4 : ℂ) • 1)) = 0 := by
    have exp1 : (C - 1) * (C - (1 / 4 : ℂ) • 1) =
        C * C - (1 / 4 : ℂ) • C - C + (1 / 4 : ℂ) • 1 := by
      rw [sub_mul, mul_sub, mul_sub, one_mul]
      rw [show C * ((1/4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = (1/4 : ℂ) • C from by
        rw [Matrix.mul_smul, mul_one]]
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) * ((1/4 : ℂ) • 1) = (1/4 : ℂ) • 1 from by
        rw [one_mul]]
      abel
    rw [exp1]
    rw [smul_add, smul_sub, smul_sub]
    -- 4 • (C * C) - 4 • ((1/4) • C) - 4 • C + 4 • ((1/4) • 1) = 0
    -- = 4 • (C*C) - C - 4•C + 1 = 4•C^2 - 5•C + 1
    rw [show (4 : ℂ) • (C * C) = 4 • C ^ 2 from by
      rw [show C * C = C ^ 2 from (sq C).symm]
      rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) from by norm_num, Nat.cast_smul_eq_nsmul]]
    rw [show (4 : ℂ) • ((1/4 : ℂ) • C) = C from by rw [smul_smul]; norm_num]
    rw [show (4 : ℂ) • C = (4 : ℕ) • C from by
      rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) from by norm_num, Nat.cast_smul_eq_nsmul]]
    rw [show (4 : ℂ) • ((1/4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = 1 from by
      rw [smul_smul]; norm_num]
    -- Now goal: 4•C^2 - C - 4•C + 1 = 0
    -- From hcancel: 4•C^2 - 5•C + 1 = 0
    have : (4 : ℕ) • C ^ 2 - C - (4 : ℕ) • C + 1 = 4 • C ^ 2 - 5 • C + 1 := by
      show (4 : ℕ) • C ^ 2 - C - (4 : ℕ) • C + 1 = (4 : ℕ) • C ^ 2 - (5 : ℕ) • C + 1
      rw [show (5 : ℕ) • C = (4 : ℕ) • C + C from by
        rw [show (5 : ℕ) = 4 + 1 from rfl, add_nsmul, one_nsmul]]
      abel
    rw [this, hcancel]
  -- From 4•(_) = 0 and 4 ≠ 0, conclude _ = 0.
  have h4ne : (4 : ℂ) ≠ 0 := by norm_num
  have hgoal : (4 : ℂ) • ((C - 1) * (C - (1/4 : ℂ) • 1)) = (4 : ℂ) • 0 := by
    rw [smul_zero]; exact h4
  exact smul_right_injective _ h4ne hgoal

snip end

problem imc2024_p7 (n : ℕ) (z : ℂ) :
    z ∈ answer n ↔
      ∃ (A B : Matrix (Fin n) (Fin n) ℂ),
        IsUnit A ∧ IsUnit B ∧ A + B = 1 ∧
        (A ^ 2 + B ^ 2) * (A ^ 4 + B ^ 4) = A ^ 5 + B ^ 5 ∧
        (A * B).det = z := by
  constructor
  · -- Forward direction: for each k ≤ n, construct A, B with det(A*B) = (1/4)^k.
    rintro ⟨k, hk, hz⟩
    -- Let ω = (1 + i√3)/2 and ω̄ = (1 - i√3)/2. Then ω + ω̄ = 1 and ω·ω̄ = 1.
    set ω : ℂ := (1 + Complex.I * Real.sqrt 3) / 2 with hω_def
    set ω' : ℂ := (1 - Complex.I * Real.sqrt 3) / 2 with hω'_def
    have hω_add : ω + ω' = 1 := by
      simp [hω_def, hω'_def]; ring
    have hω_mul : ω * ω' = 1 := by
      simp [hω_def, hω'_def]
      have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
      have hsq : (Real.sqrt 3 : ℂ) * Real.sqrt 3 = 3 := by
        have : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) =
            ((Real.sqrt 3 * Real.sqrt 3 : ℝ) : ℂ) := by push_cast; ring
        rw [this]
        rw [Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)]
        norm_cast
      ring_nf
      rw [show (Complex.I)^2 = -1 from Complex.I_sq]
      have : (Real.sqrt 3 : ℂ)^2 = 3 := by
        rw [sq, hsq]
      rw [this]
      ring
    -- Diagonal entries for A and B
    let α : Fin n → ℂ := fun i => if (i : ℕ) < k then (1 / 2 : ℂ) else ω
    let β : Fin n → ℂ := fun i => if (i : ℕ) < k then (1 / 2 : ℂ) else ω'
    refine ⟨Matrix.diagonal α, Matrix.diagonal β, ?_, ?_, ?_, ?_, ?_⟩
    · -- IsUnit (diagonal α)
      rw [Matrix.isUnit_diagonal]
      rw [isUnit_iff_exists]
      refine ⟨fun i => if (i : ℕ) < k then (2 : ℂ) else ω', ?_, ?_⟩ <;>
      · funext i
        simp only [α, Pi.mul_apply, Pi.one_apply]
        split_ifs with hi
        · norm_num
        · first | exact hω_mul | rw [mul_comm]; exact hω_mul
    · rw [Matrix.isUnit_diagonal]
      rw [isUnit_iff_exists]
      refine ⟨fun i => if (i : ℕ) < k then (2 : ℂ) else ω, ?_, ?_⟩ <;>
      · funext i
        simp only [β, Pi.mul_apply, Pi.one_apply]
        split_ifs with hi
        · norm_num
        · first | (rw [mul_comm]; exact hω_mul) | exact hω_mul
    · -- A + B = 1
      rw [Matrix.diagonal_add]
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => (1:ℂ)) from
        Matrix.diagonal_one.symm]
      congr 1
      funext i
      simp only [α, β]
      split_ifs with hi
      · norm_num
      · exact hω_add
    · -- polynomial identity
      rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_add,
          Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_add,
          Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_add,
          Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.pow_apply, α, β]
      split_ifs with hi
      · norm_num
      · -- (ω² + ω'²)(ω⁴ + ω'⁴) = ω⁵ + ω'⁵ when ω + ω' = 1 and ωω' = 1
        -- Using s = ω+ω' = 1, p = ωω' = 1:
        -- ω²+ω'² = s²-2p = -1
        -- ω³+ω'³ = s³-3sp = 1-3 = -2
        -- ω⁴+ω'⁴ = (ω²+ω'²)² - 2p² = 1 - 2 = -1
        -- ω⁵+ω'⁵ = (ω⁴+ω'⁴)(ω+ω') - p(ω³+ω'³) = -1 - (-2) = 1
        -- (ω²+ω'²)(ω⁴+ω'⁴) = (-1)(-1) = 1 ✓
        have h1 : ω ^ 2 + ω' ^ 2 = -1 := by
          have : ω ^ 2 + ω' ^ 2 = (ω + ω')^2 - 2 * (ω * ω') := by ring
          rw [this, hω_add, hω_mul]; ring
        have h2 : ω ^ 4 + ω' ^ 4 = -1 := by
          have : ω ^ 4 + ω' ^ 4 = (ω^2 + ω'^2)^2 - 2 * (ω*ω')^2 := by ring
          rw [this, h1, hω_mul]; ring
        have h3 : ω ^ 5 + ω' ^ 5 = 1 := by
          have : ω ^ 5 + ω' ^ 5 = (ω^2 + ω'^2) * (ω^3 + ω'^3) - (ω*ω')^2 * (ω + ω') := by ring
          have h3' : ω ^ 3 + ω' ^ 3 = -2 := by
            have : ω ^ 3 + ω' ^ 3 = (ω + ω')^3 - 3 * (ω*ω') * (ω + ω') := by ring
            rw [this, hω_add, hω_mul]; ring
          rw [this, h1, h3', hω_mul, hω_add]; ring
        rw [h1, h2, h3]; ring
    · -- det(A*B) = z = (1/4)^k
      rw [Matrix.diagonal_mul_diagonal, Matrix.det_diagonal]
      rw [hz]
      -- Product over Fin n of (if i<k then 1/4 else 1) = (1/4)^k
      have hprod : ∀ i : Fin n, α i * β i = if (i : ℕ) < k then (1/4 : ℂ) else 1 := by
        intro i
        simp only [α, β]
        split_ifs with hi
        · norm_num
        · exact hω_mul
      simp_rw [hprod]
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, mul_one]
      rw [Finset.prod_const]
      congr 1
      -- card {i : Fin n | i < k} = k, given k ≤ n
      have hcard : (Finset.univ.filter fun i : Fin n => (i : ℕ) < k).card = k := by
        -- Use bijection Fin k ≃ filter
        have himage : (Finset.univ.filter fun i : Fin n => (i : ℕ) < k) =
            (Finset.univ : Finset (Fin k)).image
              (fun j : Fin k => (⟨j.1, lt_of_lt_of_le j.2 hk⟩ : Fin n)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          refine ⟨fun hi => ⟨⟨i.1, hi⟩, ?_⟩, ?_⟩
          · apply Fin.ext; rfl
          · rintro ⟨j, hji⟩
            rw [← hji]
            exact j.2
        rw [himage]
        rw [Finset.card_image_of_injective _ (by
          intro a b hab
          apply Fin.ext
          have := Fin.mk.inj_iff.mp hab
          exact this)]
        exact Finset.card_univ.trans (Fintype.card_fin k)
      exact hcard
  · -- Backward direction
    rintro ⟨A, B, hA, hB, hAB, hyp, hdet⟩
    set M := A * B with hM_def
    -- M satisfies (M-1)(M-(1/4)•1) = 0
    have hMunit : IsUnit M := hA.mul hB
    have hpoly := poly_identity A B hAB hyp
    have hfact := factor_poly M hMunit hpoly
    -- The polynomial q = (X - 1)(X - 1/4) annihilates M, so its evaluation is 0.
    let q : ℂ[X] := (Polynomial.X - Polynomial.C (1 : ℂ)) *
        (Polynomial.X - Polynomial.C (1/4 : ℂ))
    have haeval : (Polynomial.aeval M) q = 0 := by
      show (Polynomial.aeval M) ((Polynomial.X - Polynomial.C (1 : ℂ)) *
        (Polynomial.X - Polynomial.C (1/4 : ℂ))) = 0
      rw [map_mul, map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
          Polynomial.aeval_C]
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp only [one_smul]
      exact hfact
    -- Case on n = 0
    by_cases hn : n = 0
    · subst hn
      refine ⟨0, le_refl _, ?_⟩
      rw [← hdet, hM_def]
      simp [Matrix.det_fin_zero]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := by
      haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
      infer_instance
    -- Every eigenvalue (root of charpoly) of M is a root of q.
    have hroots_mem : ∀ r ∈ M.charpoly.roots, r = 1 ∨ r = 1/4 := by
      intro r hr
      -- r ∈ spectrum ℂ M
      have hr_spec : r ∈ spectrum ℂ M := by
        rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
        exact (Polynomial.isRoot_of_mem_roots hr)
      -- q(r) ∈ spectrum ℂ (q(M)) = spectrum 0 = {0}
      have hqr_spec : (Polynomial.eval r q) ∈ spectrum ℂ (Polynomial.aeval M q) :=
        spectrum.subset_polynomial_aeval M q ⟨r, hr_spec, rfl⟩
      rw [haeval, spectrum.zero_eq, Set.mem_singleton_iff] at hqr_spec
      show r = 1 ∨ r = 1/4
      have : (r - 1) * (r - 1/4) = 0 := by
        have := hqr_spec
        simp only [q, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
                   Polynomial.eval_C] at this
        exact this
      rcases mul_eq_zero.mp this with h1 | h2
      · left; exact sub_eq_zero.mp h1
      · right; exact sub_eq_zero.mp h2
    -- det M = product of roots of charpoly
    have hdet_prod : M.det = M.charpoly.roots.prod :=
      Matrix.det_eq_prod_roots_charpoly M
    -- Split roots: every root is either 1 or 1/4, so
    -- roots = filter(=1) + filter(¬=1), and filter(¬=1) = filter(=1/4) (over roots)
    have hroots_eq : M.charpoly.roots =
        (M.charpoly.roots.filter (· = (1 : ℂ))) +
        (M.charpoly.roots.filter (· = (1/4 : ℂ))) := by
      conv_lhs => rw [← Multiset.filter_add_not (fun x : ℂ => x = 1) M.charpoly.roots]
      congr 1
      apply Multiset.filter_congr
      intro r hr
      constructor
      · intro hne
        rcases hroots_mem r hr with h1 | h2
        · exact absurd h1 hne
        · exact h2
      · rintro rfl; norm_num
    rw [← hdet, hM_def]
    show (A * B).det ∈ answer n
    rw [show (A * B).det = M.det from rfl, hdet_prod, hroots_eq]
    rw [Multiset.prod_add]
    have hprod1 : (M.charpoly.roots.filter (· = (1 : ℂ))).prod = 1 := by
      have hrepl : (M.charpoly.roots.filter (· = (1 : ℂ))) =
          Multiset.replicate (M.charpoly.roots.filter (· = (1 : ℂ))).card (1 : ℂ) := by
        apply Multiset.eq_replicate_card.mpr
        intro x hx
        exact (Multiset.mem_filter.mp hx).2
      rw [hrepl, Multiset.prod_replicate, one_pow]
    set k := (M.charpoly.roots.filter (· = (1/4 : ℂ))).card with hk_def
    have hprod2 : (M.charpoly.roots.filter (· = (1/4 : ℂ))).prod = (1/4 : ℂ) ^ k := by
      have hall : ∀ x ∈ (M.charpoly.roots.filter (· = (1/4 : ℂ))), x = (1/4 : ℂ) :=
        fun x hx => (Multiset.mem_filter.mp hx).2
      -- The filtered multiset equals replicate k (1/4)
      have hrepl : (M.charpoly.roots.filter (· = (1/4 : ℂ))) = Multiset.replicate k (1/4 : ℂ) := by
        apply Multiset.eq_replicate_card.mpr
        exact hall
      rw [hrepl, Multiset.prod_replicate]
    rw [hprod1, hprod2, one_mul]
    refine ⟨k, ?_, rfl⟩
    have hle1 : k ≤ M.charpoly.roots.card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    have hle2 : M.charpoly.roots.card ≤ M.charpoly.natDegree := M.charpoly.card_roots'
    rw [M.charpoly_natDegree_eq_dim, Fintype.card_fin] at hle2
    exact hle1.trans hle2

end Imc2024P7
