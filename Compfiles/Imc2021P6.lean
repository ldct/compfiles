/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2021, Problem 6

For a prime `p`, let `GL₂(ℤ/pℤ)` be the group of invertible `2 × 2` matrices
mod `p`, and let `S_p` be the symmetric group on `p` elements. Show that there
is no injective group homomorphism `φ : GL₂(ℤ/pℤ) → S_p`.
-/

namespace Imc2021P6

open Matrix

problem imc2021_p6 (p : ℕ) [Fact p.Prime] :
    ¬ ∃ φ : (GL (Fin 2) (ZMod p)) →* Equiv.Perm (Fin p),
      Function.Injective φ := by
  -- TODO: Full proof plan.
  --
  -- Case p = 2: |GL_2(ℤ/2)| = 6 > 2 = |S_2|. An injection between finite groups
  -- requires |GL_2(ℤ/2)| ≤ |S_2|, contradiction.
  --
  -- Case odd prime p: Construct elements
  --   A = !![1, 1; 0, 1] of order p (unipotent),
  --   B = !![-1, 0; 0, -1] = -I of order 2,
  -- which commute. Then A * B has order lcm(p, 2) = 2p. But in S_p, no element
  -- has order 2p: any σ ∈ S_p with p | ord(σ) must be a p-cycle (since a
  -- p-cycle needs p distinct elements, and we only have p to work with), hence
  -- has order exactly p. Contradiction via injective homomorphism preserving
  -- orders.
  sorry

end Imc2021P6
