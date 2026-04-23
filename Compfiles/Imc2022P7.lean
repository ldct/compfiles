/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2022, Problem 7

Let `A_1, …, A_k` be `n × n` idempotent complex matrices such that
`A_i A_j = -A_j A_i` for all `i ≠ j`. Prove that at least one of them
has rank at most `n / k`.
-/

namespace Imc2022P7

open Matrix

/-- The problem: among pairwise anti-commuting idempotent complex
matrices, at least one has rank ≤ n/k.

The official proof: since idempotent complex matrices have trace equal to
rank, and since `(∑ A_i)² = ∑ A_i² + ∑_{i≠j}(A_i A_j + A_j A_i) = ∑ A_i`,
the sum `∑ A_i` is also idempotent. Then

  `∑ rank(A_i) = ∑ trace(A_i) = trace(∑ A_i) = rank(∑ A_i) ≤ n`.

So some `rank(A_i) ≤ n/k`.

TODO: formalize. Mathlib gap: idempotent matrices having
`trace = rank` over fields of characteristic zero.
-/
problem imc2022_p7 {n k : ℕ} (hk : 0 < k) (A : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hidem : ∀ i, A i * A i = A i)
    (hanticomm : ∀ i j, i ≠ j → A i * A j = - (A j * A i)) :
    ∃ i, (A i).rank * k ≤ n := by
  sorry

end Imc2022P7
