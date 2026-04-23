/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 2

Let `A` and `B` be `n × n` real matrices such that `rank(AB - BA + I) = 1`.
Prove that
  `trace(ABAB) - trace(A^2 B^2) = (1/2) * n * (n-1)`.
-/

namespace Imc2020P2

open Matrix

snip begin

/-- A matrix `M : Matrix (Fin n) (Fin n) ℝ` with rank equal to 1 can be written
as the outer product `vecMulVec v w` for some vectors `v, w : Fin n → ℝ`. -/
lemma exists_vecMulVec_of_rank_eq_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hrank : M.rank = 1) :
    ∃ v w : Fin n → ℝ, M = vecMulVec v w := by
  -- The column space of M has finrank 1.
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range M.col)) = 1 := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact hrank
  -- So there's a nonzero vector v such that every vector in the span is a multiple of v.
  -- In particular every column is a multiple of v.
  rw [finrank_eq_one_iff' (K := ℝ)] at hspan
  obtain ⟨v, hv_ne, hv_span⟩ := hspan
  -- v : span ℝ (range M.col). Get the underlying vector.
  set v₀ : Fin n → ℝ := v.1 with hv₀
  -- Each column of M lies in the span.
  have hcol : ∀ j, M.col j ∈ Submodule.span ℝ (Set.range M.col) := fun j =>
    Submodule.subset_span ⟨j, rfl⟩
  -- For each column j, there is c_j such that c_j • v = M.col j.
  choose c hc using
    (fun j => hv_span ⟨M.col j, hcol j⟩)
  -- Extract the underlying vector equality.
  have hc' : ∀ j i, c j * v₀ i = M i j := by
    intro j i
    have h := hc j
    have h2 : ((c j • v : Submodule.span ℝ (Set.range M.col)) : Fin n → ℝ) =
              M.col j := by
      rw [h]
    simp only [SetLike.val_smul] at h2
    have := congrFun h2 i
    simp only [Matrix.col_apply] at this
    rw [← this]
    rfl
  refine ⟨v₀, c, ?_⟩
  ext i j
  rw [vecMulVec_apply, ← hc' j i]
  ring

snip end

problem imc2020_p2 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hrank : (A * B - B * A + 1).rank = 1) :
    trace (A * B * A * B) - trace (A ^ 2 * B ^ 2) = (1 / 2 : ℝ) * n * (n - 1) := by
  -- Let X = A*B - B*A. Then X + 1 has rank 1.
  set X : Matrix (Fin n) (Fin n) ℝ := A * B - B * A with hX_def
  -- trace X = 0 by cyclicity.
  have htrX : trace X = 0 := by
    simp only [X, Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]
  -- Decompose X + 1 = vecMulVec v w.
  obtain ⟨v, w, hvw⟩ := exists_vecMulVec_of_rank_eq_one (X + 1) hrank
  -- From trace X = 0: trace(X + 1) = n, so vecMulVec trace is v ⬝ᵥ w = n.
  have htr_sum : trace (X + 1) = (n : ℝ) := by
    rw [Matrix.trace_add, htrX, Matrix.trace_one, zero_add, Fintype.card_fin]
  have hvw_dot : v ⬝ᵥ w = (n : ℝ) := by
    have htr_eq := congrArg trace hvw
    rw [Matrix.trace_vecMulVec] at htr_eq
    rw [← htr_eq, htr_sum]
  -- X = vecMulVec v w - 1.
  have hX_eq : X = vecMulVec v w - 1 := by
    rw [← hvw]; abel
  -- Compute X^2.
  -- X^2 = (vecMulVec v w - 1)^2 = (vecMulVec v w)^2 - 2 * vecMulVec v w + 1.
  -- And (vecMulVec v w) * (vecMulVec v w) = (v ⬝ᵥ w) • vecMulVec v w = n • vecMulVec v w.
  have hvv_mul : vecMulVec v w * vecMulVec v w = (v ⬝ᵥ w) • vecMulVec v w := by
    ext i j
    simp only [Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hvv_mul' : vecMulVec v w * vecMulVec v w = (n : ℝ) • vecMulVec v w := by
    rw [hvv_mul, hvw_dot]
  have hX_sq : X * X = ((n : ℝ) - 2) • vecMulVec v w + 1 := by
    rw [hX_eq]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hvv_mul']
    rw [Matrix.mul_one, Matrix.one_mul, Matrix.one_mul]
    -- n • vecMulVec - vecMulVec - (vecMulVec - 1) = n • vecMulVec - 2 • vecMulVec + 1
    have h2 : (2 : ℕ) • vecMulVec v w = vecMulVec v w + vecMulVec v w := by
      rw [two_nsmul]
    rw [show ((n : ℝ) - 2) • vecMulVec v w =
      (n : ℝ) • vecMulVec v w - (2 : ℝ) • vecMulVec v w from sub_smul _ _ _]
    rw [show (2 : ℝ) • vecMulVec v w = vecMulVec v w + vecMulVec v w from by
      rw [show (2 : ℝ) = (1 : ℝ) + 1 from by norm_num, add_smul, one_smul]]
    abel
  -- trace X^2 = (n-2) * n + n = n^2 - 2n + n = n^2 - n = n(n-1).
  have htr_Xsq : trace (X * X) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [hX_sq, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_vecMulVec,
        Matrix.trace_one, Fintype.card_fin, hvw_dot]
    ring
  -- Now: X^2 = (AB - BA)(AB - BA) = ABAB - AB*BA - BA*AB + BA*BA
  -- trace X^2 = trace(ABAB) - trace(AB*BA) - trace(BA*AB) + trace(BABA).
  -- By cyclicity: trace(BABA) = trace(ABAB), trace(AB*BA) = trace(A*B*B*A) = trace(A^2*B^2)... hmm
  -- Wait, trace(AB*BA) = trace(ABBA) = trace(A^2 B^2)? No, AB*BA = A(BB)A = AB^2 A
  -- trace(AB^2 A) = trace(A^2 B^2) by cyclicity. Yes.
  -- Similarly trace(BA*AB) = trace(BA^2 B) = trace(A^2 B^2).
  -- So trace X^2 = trace(ABAB) - trace(A^2 B^2) - trace(A^2 B^2) + trace(ABAB)
  --             = 2 trace(ABAB) - 2 trace(A^2 B^2).
  have hXX_expand : X * X = A * B * A * B - A * B * (B * A) - B * A * (A * B) + B * A * (B * A) := by
    show (A * B - B * A) * (A * B - B * A) = _
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc (A*B) A B]
    abel
  -- Each trace of the 4 terms.
  have tr1 : trace (A * B * A * B) = trace (A * B * A * B) := rfl
  have tr2 : trace (A * B * (B * A)) = trace (A ^ 2 * B ^ 2) := by
    -- A * B * (B * A) = A * B^2 * A; cyclic trace gives A^2 B^2.
    rw [show A * B * (B * A) = A * (B * B) * A from by rw [Matrix.mul_assoc A B (B*A),
       ← Matrix.mul_assoc B B A, ← Matrix.mul_assoc A _ A]]
    rw [Matrix.trace_mul_cycle, show A * A = A ^ 2 from (sq A).symm,
        show B * B = B ^ 2 from (sq B).symm]
  have tr3 : trace (B * A * (A * B)) = trace (A ^ 2 * B ^ 2) := by
    -- B * A * (A * B) = B * A^2 * B; cyclic trace gives A^2 * B^2.
    rw [show B * A * (A * B) = B * (A * A) * B from by rw [Matrix.mul_assoc B A (A*B),
       ← Matrix.mul_assoc A A B, ← Matrix.mul_assoc B _ B]]
    rw [show A * A = A ^ 2 from (sq A).symm]
    rw [Matrix.trace_mul_comm (B * A^2) B, ← Matrix.mul_assoc,
        show B * B = B ^ 2 from (sq B).symm,
        Matrix.trace_mul_comm (B^2) (A^2)]
  have tr4 : trace (B * A * (B * A)) = trace (A * B * A * B) := by
    -- trace(BABA) = trace(ABAB) by cyclicity.
    rw [show B * A * (B * A) = B * (A * B * A) from by
          rw [Matrix.mul_assoc B A (B*A), ← Matrix.mul_assoc A B A]]
    rw [Matrix.trace_mul_comm B (A * B * A)]
  -- Combine.
  have h_trXX : trace (X * X) = 2 * trace (A * B * A * B) - 2 * trace (A ^ 2 * B ^ 2) := by
    rw [hXX_expand]
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
    rw [tr2, tr3, tr4]
    ring
  rw [h_trXX] at htr_Xsq
  linarith
end Imc2020P2
