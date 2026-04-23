/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2022, Problem 2

Let `n` be a positive integer. Find all `n × n` real matrices `A` with only
real eigenvalues satisfying
  `A + A^k = A^T`
for some integer `k ≥ n`.

Answer: `A = 0`.
-/

namespace Imc2022P2

open Matrix

/-- The answer: the only such matrix is the zero matrix. -/
determine answer {n : ℕ} : Matrix (Fin n) (Fin n) ℝ := 0

snip begin

/-- For real `x` and integer `k ≥ 2`, the value `1 + (1 + x^(k-1))^k` is positive.
This is the key inequality behind the minimal polynomial argument. -/
lemma one_add_pow_pos {k : ℕ} (hk : 2 ≤ k) (x : ℝ) :
    0 < 1 + (1 + x ^ (k - 1)) ^ k := by
  -- Case split on parity of k.
  rcases Nat.even_or_odd k with hke | hko
  · -- k even: (1 + x^(k-1))^k ≥ 0 since k is even.
    have h1 : 0 ≤ (1 + x ^ (k - 1)) ^ k := Even.pow_nonneg hke _
    linarith
  · -- k odd: k-1 is even, so x^(k-1) ≥ 0. Thus 1 + x^(k-1) ≥ 1 > 0,
    -- so (1 + x^(k-1))^k > 0.
    have hk1even : Even (k - 1) := by
      rcases hko with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      omega
    have hxpow : 0 ≤ x ^ (k - 1) := Even.pow_nonneg hk1even x
    have h1 : 0 < 1 + x ^ (k - 1) := by linarith
    have h2 : 0 < (1 + x ^ (k - 1)) ^ k := pow_pos h1 k
    linarith

/-- From `A + A^k = Aᵀ`, transposing and substituting gives the annihilating
identity `A^k * (1 + (1 + A^(k-1))^k) = 0`. That is,
`p(x) = x^k * (1 + (1 + x^(k-1))^k)` annihilates `A`. -/
lemma annihilating_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hEq : A + A ^ k = A.transpose) :
    A ^ k * (1 + (1 + A ^ (k - 1)) ^ k) = 0 := by
  -- Take transpose of hEq: Aᵀ + (Aᵀ)^k = A.
  have hT : A.transpose + (A.transpose) ^ k = A := by
    have ht := congrArg Matrix.transpose hEq
    simpa [Matrix.transpose_add, Matrix.transpose_pow] using ht
  -- Substitute Aᵀ = A + A^k. Then (A + A^k) + (A + A^k)^k = A.
  have h2 : (A + A ^ k) + (A + A ^ k) ^ k = A := by
    conv_lhs => rw [hEq]
    exact hT
  -- So (A + A^k)^k = -A^k.
  have h3 : (A + A ^ k) ^ k = - A ^ k := by
    have : (A + A ^ k) + (A + A ^ k) ^ k - (A + A ^ k) = A - (A + A ^ k) := by
      rw [h2]
    simpa using this
  -- Factor A + A^k = A * (1 + A^(k-1)) since k ≥ 1.
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hfac : A + A ^ k = A * (1 + A ^ (k - 1)) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← pow_succ', hk']
  -- Substitute and compute: (A * (1 + A^(k-1)))^k = -A^k.
  -- Since powers of A and (1 + A^(k-1)) commute (both are polynomials in A),
  -- (A * (1 + A^(k-1)))^k = A^k * (1 + A^(k-1))^k.
  have hcomm : Commute A (1 + A ^ (k - 1)) := by
    refine (Commute.one_right A).add_right ?_
    exact (Commute.refl A).pow_right (k - 1)
  have hexp : (A * (1 + A ^ (k - 1))) ^ k = A ^ k * (1 + A ^ (k - 1)) ^ k :=
    hcomm.mul_pow k
  rw [hfac, hexp] at h3
  -- h3 : A^k * (1 + A^(k-1))^k = -A^k.
  -- So A^k * (1 + (1 + A^(k-1))^k) = A^k * 1 + A^k * (1 + A^(k-1))^k
  --                                = A^k + (-A^k) = 0.
  rw [Matrix.mul_add, Matrix.mul_one, h3]
  exact add_neg_cancel (A ^ k)

snip end

problem imc2022_p2 {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (hk : n ≤ k)
    (hreal : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' (A.map ((algebraMap ℝ ℂ)))) μ → μ.im = 0)
    (hEq : A + A ^ k = A.transpose) :
    A = answer := by
  show A = 0
  -- Notation.
  set ι : ℝ →+* ℂ := algebraMap ℝ ℂ with hι
  set A_C : Matrix (Fin n) (Fin n) ℂ := A.map ι with hA_C
  -- `k ≥ n ≥ 1` so `k ≥ 1`, hence `k ≥ 2` is used only in the helper; we extract
  -- `1 ≤ k` now.
  have hk1 : 1 ≤ k := hn.trans_le hk
  -- Step 1: the annihilating polynomial over ℝ.
  have hann_R : A ^ k * (1 + (1 + A ^ (k - 1)) ^ k) = 0 :=
    annihilating_identity A k hk1 hEq
  -- Step 2: same identity over ℂ (after applying the ring hom `ι.mapMatrix`).
  have hann_C : A_C ^ k * (1 + (1 + A_C ^ (k - 1)) ^ k) = 0 := by
    have := congrArg ι.mapMatrix hann_R
    simp only [map_mul, map_pow, map_add, map_one, RingHom.mapMatrix_apply] at this
    simpa [A_C] using this
  -- Step 3: the same polynomial (in `ℂ[X]`) annihilates the linear map `A_C.toLin'`.
  let φ : Module.End ℂ (Fin n → ℂ) := A_C.toLin'
  -- Define the annihilating polynomial over ℂ.
  let p : Polynomial ℂ :=
    (Polynomial.X : Polynomial ℂ) ^ k *
      (1 + (1 + (Polynomial.X : Polynomial ℂ) ^ (k - 1)) ^ k)
  -- `aeval A_C p = A_C^k * (1 + (1 + A_C^(k-1))^k) = 0`.
  have hp_A_C : (Polynomial.aeval A_C) p = 0 := by
    simp only [p, map_mul, map_pow, map_add, map_one, Polynomial.aeval_X]
    exact hann_C
  -- Transport to φ via the algebra hom `Matrix.toLinAlgEquiv'`.
  have hp_phi : (Polynomial.aeval φ) p = 0 := by
    let f : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Module.End ℂ (Fin n → ℂ) :=
      Matrix.toLinAlgEquiv'.toAlgHom
    have hφ : f A_C = φ := by
      apply LinearMap.ext
      intro v
      simp [f, φ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
    calc (Polynomial.aeval φ) p = (Polynomial.aeval (f A_C)) p := by rw [hφ]
      _ = f ((Polynomial.aeval A_C) p) := Polynomial.aeval_algHom_apply f A_C p
      _ = f 0 := by rw [hp_A_C]
      _ = 0 := map_zero _
  -- Step 4: every complex eigenvalue of φ is 0.
  have heig_zero : ∀ μ : ℂ, φ.HasEigenvalue μ → μ = 0 := by
    intro μ hμ
    -- μ is a root of p by `aeval_apply_of_hasEigenvector`.
    obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
    have hpμ : p.eval μ = 0 := by
      have : (Polynomial.aeval φ p) x = p.eval μ • x :=
        Module.End.aeval_apply_of_hasEigenvector ⟨hx_mem, hx_ne⟩
      rw [hp_phi, LinearMap.zero_apply] at this
      exact (smul_eq_zero.mp this.symm).resolve_right hx_ne
    -- μ is real.
    have hμ_im : μ.im = 0 := hreal μ hμ
    -- Write μ = ι r with r = μ.re.
    set r : ℝ := μ.re with hr_def
    have hμ_eq : μ = ι r := by
      apply Complex.ext
      · simp [hι, r]
      · simp [hι, hμ_im]
    -- Substitute into `p.eval μ = 0`.
    have hp_eval_r : r ^ k * (1 + (1 + r ^ (k - 1)) ^ k) = 0 := by
      have h1 : p.eval μ = μ ^ k * (1 + (1 + μ ^ (k - 1)) ^ k) := by
        simp [p]
      rw [h1, hμ_eq] at hpμ
      have hstep : (ι r) ^ k * (1 + (1 + (ι r) ^ (k - 1)) ^ k) =
             ι (r ^ k * (1 + (1 + r ^ (k - 1)) ^ k)) := by
        simp [hι, map_pow, map_add, map_one, map_mul]
      rw [hstep] at hpμ
      have hinj : Function.Injective ι := (algebraMap ℝ ℂ).injective
      have : ι (r ^ k * (1 + (1 + r ^ (k - 1)) ^ k)) = ι 0 := by
        rw [hpμ]; simp [hι]
      exact hinj this
    -- Use `one_add_pow_pos` to conclude r = 0, hence μ = 0.
    -- Need k ≥ 2 for `one_add_pow_pos`. Handle k = 1 case separately.
    rcases Nat.lt_or_ge k 2 with hk_lt | hk_ge
    · -- k = 1 case. Combined with hk1 : 1 ≤ k, k = 1.
      interval_cases k
      · -- k = 1: polynomial is x * (1 + (1+x^0)^1) = x * 3 = 3x. So r = 0.
        have : r * 3 = 0 := by
          have : r ^ 1 * (1 + (1 + r ^ (1 - 1)) ^ 1) = r * 3 := by ring
          linarith [hp_eval_r, this]
        have hrr : r = 0 := by linarith
        rw [hμ_eq, hrr]; simp [hι]
    · -- k ≥ 2.
      have hpos : 0 < 1 + (1 + r ^ (k - 1)) ^ k := one_add_pow_pos hk_ge r
      have hrk : r ^ k = 0 := by
        rcases mul_eq_zero.mp hp_eval_r with h | h
        · exact h
        · linarith
      have hr : r = 0 := by
        have hk_ne : k ≠ 0 := by omega
        exact (pow_eq_zero_iff hk_ne).mp hrk
      rw [hμ_eq, hr]; simp [hι]
  -- Step 5: charpoly of `A_C` has only 0 as root over ℂ. Since ℂ is algebraically
  -- closed, charpoly = X^n.
  have hcharpoly_C : A_C.charpoly = Polynomial.X ^ n := by
    -- `A_C.charpoly` is monic of degree n, splits over ℂ, has only root 0.
    have hmon : A_C.charpoly.Monic := A_C.charpoly_monic
    have hdeg : A_C.charpoly.natDegree = n := by
      rw [A_C.charpoly_natDegree_eq_dim]; exact Fintype.card_fin n
    -- Every root of charpoly is an eigenvalue, hence 0.
    have hroots : ∀ μ ∈ A_C.charpoly.roots, μ = 0 := by
      intro μ hμ
      have hroot : A_C.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
      -- Root of charpoly ↔ eigenvalue.
      have : φ.HasEigenvalue μ := by
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        rwa [show φ.charpoly = A_C.charpoly from A_C.charpoly_toLin']
      exact heig_zero μ this
    -- Monic polynomial of degree n with all roots = 0 over ℂ (alg closed) is X^n.
    have hsplits : A_C.charpoly.Splits := IsAlgClosed.splits _
    -- roots has multiset replicate structure.
    have hcard : A_C.charpoly.roots.card = n :=
      (Polynomial.splits_iff_card_roots.mp hsplits).trans hdeg
    have hroots_repl : A_C.charpoly.roots = Multiset.replicate n 0 :=
      Multiset.eq_replicate.mpr ⟨hcard, hroots⟩
    -- Use splits to factor.
    have hfact := hsplits.eq_prod_roots_of_monic hmon
    rw [hroots_repl] at hfact
    rw [hfact]
    -- Now simplify the product.
    rw [Multiset.map_replicate]
    simp [Polynomial.C_0]
  -- Step 6: charpoly of A (over ℝ) is X^n.
  have hcharpoly_R : A.charpoly = Polynomial.X ^ n := by
    have : A.charpoly.map ι = Polynomial.X ^ n := by
      rw [← Matrix.charpoly_map, ← hA_C]; exact hcharpoly_C
    -- ι is injective, so A.charpoly = X^n over ℝ.
    have hinj : Function.Injective ι := (algebraMap ℝ ℂ).injective
    apply Polynomial.map_injective ι hinj
    rw [this]; simp
  -- Step 7: A^n = 0 by Cayley-Hamilton.
  have hAn : A ^ n = 0 := by
    have := A.aeval_self_charpoly
    rw [hcharpoly_R] at this
    simpa using this
  -- Step 8: A^k = 0 since k ≥ n.
  have hAk : A ^ k = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, hAn, zero_mul]
  -- Step 9: A = Aᵀ.
  have hsymm : A = A.transpose := by
    have : A + 0 = A.transpose := by rw [← hAk]; exact hEq
    simpa using this
  -- Step 10: tr(A²) = 0 from A nilpotent.
  have hA_nil : IsNilpotent A := ⟨n, hAn⟩
  have hA2_nil : IsNilpotent (A * A) := by
    obtain ⟨m, hm⟩ := hA_nil
    refine ⟨m, ?_⟩
    have : (A * A) ^ m = A ^ m * A ^ m := (Commute.refl A).mul_pow m
    rw [this, hm, zero_mul]
  have htr : (A * A).trace = 0 := by
    have hnil_tr : IsNilpotent (A * A).trace := Matrix.isNilpotent_trace_of_isNilpotent hA2_nil
    -- Over ℝ (reduced), nilpotent ⟹ 0.
    exact hnil_tr.eq_zero
  -- Step 11: tr(Aᴴ · A) = 0 gives A = 0 (over ℝ, Aᴴ = Aᵀ = A).
  have hconj : A.conjTranspose = A.transpose :=
    Matrix.conjTranspose_eq_transpose_of_trivial A
  rw [← Matrix.trace_conjTranspose_mul_self_eq_zero_iff, hconj, ← hsymm]
  exact htr

end Imc2022P2
