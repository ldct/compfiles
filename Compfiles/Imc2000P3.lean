/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2000, Problem 3

Let `A` and `B` be square complex matrices such that `rank (AB - BA) = 1`.
Show that `(AB - BA)^2 = 0`.
-/

namespace Imc2000P3

open Matrix

snip begin

/-- A key identity: any square matrix `C` over a field with rank at most `1`
satisfies `C * C = (trace C) • C`. -/
lemma mul_self_eq_trace_smul {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K]
    (C : Matrix n n K) (hrank : C.rank ≤ 1) :
    C * C = (trace C) • C := by
  -- The column span of C has finrank ≤ 1.
  have hspan : Module.finrank K (Submodule.span K (Set.range C.col)) ≤ 1 := by
    rw [← rank_eq_finrank_span_cols]; exact hrank
  -- Hence there is a vector `u` in that submodule whose span contains every column.
  set W : Submodule K (n → K) := Submodule.span K (Set.range C.col) with hW
  have hWprinc : W.IsPrincipal := by
    rw [← Submodule.finrank_le_one_iff_isPrincipal]
    exact hspan
  obtain ⟨u, hu⟩ := hWprinc
  -- Each column of C lies in `span {u}`, so there's a scalar `v j` with C.col j = (v j) • u.
  have hcol_in : ∀ j, C.col j ∈ (K ∙ u) := by
    intro j
    rw [← hu]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose v hv using fun j => Submodule.mem_span_singleton.mp (hcol_in j)
  -- So `C i j = v j * u i`.
  have hCij : ∀ i j, C i j = v j * u i := by
    intro i j
    have := congrArg (fun f : n → K => f i) (hv j)
    simp only [col_apply] at this
    rw [← this]
    rfl
  -- Compute C * C.
  ext i k
  simp only [Matrix.mul_apply]
  calc ∑ j, C i j * C j k
      = ∑ j, (v j * u i) * (v k * u j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hCij i j, hCij j k]
    _ = (∑ j, u j * v j) * (v k * u i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = trace C * C i k := by
        rw [hCij i k]
        congr 1
        unfold Matrix.trace
        apply Finset.sum_congr rfl
        intro j _
        have : C j j = v j * u j := hCij j j
        rw [show C.diag j = C j j from rfl, this]
        ring

snip end

problem imc2000_p3 {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hrank : (A * B - B * A).rank = 1) :
    (A * B - B * A) * (A * B - B * A) = 0 := by
  set C := A * B - B * A with hC
  have hrank_le : C.rank ≤ 1 := by rw [hrank]
  have hmul : C * C = trace C • C := mul_self_eq_trace_smul C hrank_le
  have htrace : trace C = 0 := by
    show trace (A * B - B * A) = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [hmul, htrace, zero_smul]

end Imc2000P3
