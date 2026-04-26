/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2013, Problem 5

Does there exist a sequence `(a_n)` of complex numbers such that for every
positive integer `p`, `∑_{n=1}^∞ a_n^p` converges if and only if `p` is not
a prime?

Answer: Yes.

The construction uses a more general lemma: for any partition `ℕ = C ∪ D` of
the positive integers, there exists a sequence `(a_n)` with `∑ a_n^p`
convergent for `p ∈ C` and divergent for `p ∈ D`. We then take `C` to be the
set of non-primes and `D` the set of primes.

The construction proceeds in blocks. For each `k`, by Newton's identities one
can choose complex numbers `z_1, ..., z_k` with `∑_j z_j^p = 0` for non-primes
`p ≤ k` and `∑_j z_j^p = 1` for primes `p ≤ k`. By scaling and repetition we
build a finite block whose `p`-th power sum is `0` for non-primes `p ≤ k`
(with bounded partial sums of magnitude `≤ 1/k`) and has magnitude `≥ 1` for
primes `p ≤ k`. Concatenating the blocks yields the desired sequence.
-/

namespace Imc2013P5

/-- Answer: yes, such a sequence exists. -/
determine answer : Prop := True

snip begin

-- TODO: Full proof of existence.
--
-- The proof requires:
--   1. A lemma producing, for each `k`, complex numbers `z_1, ..., z_k`
--      with prescribed power sums `∑ z_j^p` for `1 ≤ p ≤ k`. This follows
--      from the surjectivity of the Newton map between power sums and
--      elementary symmetric polynomials, equivalently the existence of
--      a polynomial with given roots and leading coefficients.
--   2. A scaling/repetition step packaging block `k` into a finite tuple
--      `(x_{k,1}, ..., x_{k,N_k})` with the required estimates.
--   3. A concatenation lemma showing that the resulting sequence satisfies
--      the convergence dichotomy for `p` prime vs. non-prime.
--
-- These are all standard but technical; we leave the construction as a
-- placeholder and focus on the high-level statement.

snip end

problem imc2013_p5 :
    answer ↔
      ∃ (a : ℕ → ℂ),
        ∀ p : ℕ, 0 < p →
          (Summable (fun n => (a n) ^ p) ↔ ¬ p.Prime) := by
  -- The answer is `True`, so we must produce such a sequence.
  show True ↔ _
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  sorry

end Imc2013P5
