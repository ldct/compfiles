/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2020, Problem 7

Let `G` be a group and `n ≥ 2` an integer. Let `H₁, H₂` be subgroups of `G`
satisfying `[G : H₁] = [G : H₂] = n` and `[G : H₁ ∩ H₂] = n(n − 1)`.
Prove that `H₁` and `H₂` are conjugate in `G`.
-/

namespace Imc2020P7

problem imc2020_p7 {G : Type*} [Group G] (n : ℕ) (hn : 2 ≤ n)
    (H₁ H₂ : Subgroup G)
    (hH₁ : H₁.index = n) (hH₂ : H₂.index = n)
    (hinter : (H₁ ⊓ H₂).index = n * (n - 1)) :
    ∃ g : G, H₂ = (H₁.map (MulEquiv.toMonoidHom (MulAut.conj g))) := by
  -- TODO: coset counting; show G ∖ H₁ H₂ is simultaneously a left coset of H₂
  -- and a right coset of H₁, then conjugate.
  sorry

end Imc2020P7
