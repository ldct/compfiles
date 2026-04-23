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
  -- TODO: exhibit an element of GL₂(F_p) of order 2p; show S_p has no such element.
  sorry

end Imc2021P6
