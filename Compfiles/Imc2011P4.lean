/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2011, Problem 4

Let `A₁, A₂, …, Aₙ` be finite, nonempty sets. Define the function
`f(t) = Σ_{k=1}^n Σ_{i₁<…<iₖ} (-1)^{k-1} t^{|Aᵢ₁ ∪ … ∪ Aᵢₖ|}`.
Prove that `f` is nondecreasing on `[0, 1]`.

## Solution sketch

Let `Ω = ⋃ Aᵢ`. For a random subset `X ⊆ Ω` where each element of `Ω` is
included independently with probability `t`, the probability that
`Aᵢ ⊆ X` is `t^{|Aᵢ|}`. By inclusion–exclusion, `f(t)` equals the
probability that some `Aᵢ` is contained in `X`. Since the family of
`X ⊆ Ω` containing some `Aᵢ` is upward-closed, sampling `X` at a higher
rate `t' > t` only increases this probability, so `f` is monotone.

Algebraically, this gives the Bernstein expansion
`f(t) = Σ_{S ⊆ Ω, S winning} t^{|S|}(1-t)^{|Ω|-|S|}`,
where `S` is *winning* if some `Aᵢ ⊆ S`. Monotonicity then follows from
upward-closedness of the winning family.
-/

namespace Imc2011P4

open Finset BigOperators

variable {α : Type*} [DecidableEq α]

/-- The function `f(t)` from the problem. -/
noncomputable def f (n : ℕ) (A : Fin n → Finset α) (t : ℝ) : ℝ :=
  ∑ J ∈ (univ : Finset (Finset (Fin n))) \ {∅}, (-1 : ℝ) ^ (J.card - 1) *
    t ^ (J.biUnion A).card

problem imc2011_p4 (n : ℕ) (A : Fin n → Finset α) (_hA : ∀ i, (A i).Nonempty) :
    MonotoneOn (f n A) (Set.Icc (0 : ℝ) 1) := by
  -- The proof proceeds by rewriting `f(t)` as a sum over subsets `S` of
  -- `Ω = ⋃ Aᵢ` of `t^|S|(1-t)^{|Ω|-|S|}` indexed by upward-closed sets,
  -- then using monotonicity of this Bernstein-like polynomial.
  sorry

end Imc2011P4
