/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2008, Problem 5

Does there exist a finite group `G` and a normal subgroup `H ≤ G` such
that `|Aut H| > |Aut G|`?

Answer: Yes.

The classical example: take `H = (ℤ/2ℤ)³`, so `Aut H ≅ GL₃(𝔽₂)` has order
`168`. Let `G = H ⋊ ℤ/3ℤ` where `ℤ/3ℤ` acts on `H` by cyclic permutation
of the coordinates. Then `|G| = 24` and a counting argument shows
`|Aut G| ≤ 56 < 168`.
-/

namespace Imc2008P5

/-- The answer: yes, there exist a finite group `G` with a normal subgroup
`H` such that the automorphism group of `H` is strictly larger than that of
`G`. -/
determine answer : Prop := True

problem imc2008_p5 :
    answer ↔
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (H : Subgroup G),
      H.Normal ∧ Nat.card (MulAut H) > Nat.card (MulAut G) := by
  show True ↔ _
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  -- TODO: exhibit `H = (ZMod 2)^3` inside `G = (ZMod 2)^3 ⋊ ZMod 3`.
  -- Then `Nat.card (MulAut H) = |GL₃(𝔽₂)| = 168` and `Nat.card (MulAut G) ≤ 56`.
  sorry

end Imc2008P5
