/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1998, Problem 7 (Day 2, Problem 1)

Let `V` be a real vector space and `f, f₁, …, fₖ : V → ℝ` linear functionals.
Suppose that for every `x ∈ V` with `f₁ x = ⋯ = fₖ x = 0` we have `f x = 0`.
Prove that `f` is a linear combination of `f₁, …, fₖ`.

## Solution sketch

The hypothesis says `⋂ᵢ ker fᵢ ⊆ ker f`. The conclusion that `f` lies in the
linear span of the `fᵢ` is a standard consequence of duality, formalized in
Mathlib as `mem_span_of_iInf_ker_le_ker` (which only requires the index set
to be finite).
-/

namespace Imc1998P7

open Submodule

/-- If `f, f₁, …, fₖ : V → ℝ` are linear functionals on a real vector space and
the joint kernel of `f₁, …, fₖ` is contained in the kernel of `f`, then `f`
is a linear combination of `f₁, …, fₖ`. -/
problem imc1998_p7
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (f : V →ₗ[ℝ] ℝ) (fs : Fin k → V →ₗ[ℝ] ℝ)
    (h : ∀ x : V, (∀ i, fs i x = 0) → f x = 0) :
    ∃ c : Fin k → ℝ, f = ∑ i, c i • fs i := by
  -- Translate the hypothesis into the inclusion of kernels.
  have hker : ⨅ i, LinearMap.ker (fs i) ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine h x ?_
    intro i
    have : x ∈ LinearMap.ker (fs i) := (Submodule.mem_iInf _).mp hx i
    exact (LinearMap.mem_ker.mp this)
  -- Apply the Mathlib lemma.
  have hmem : f ∈ Submodule.span ℝ (Set.range fs) :=
    mem_span_of_iInf_ker_le_ker hker
  -- Convert the membership to an explicit linear combination indexed by `Fin k`.
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℝ).1 hmem
  exact ⟨c, hc.symm⟩

end Imc1998P7
