/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2023, Problem 4

Let `p` be a prime number and let `k` be a positive integer. Suppose that the
numbers `aᵢ = iᵏ + i` for `i = 0, 1, …, p − 1` form a complete residue system
modulo `p`. What is the set of possible remainders of `a₂` upon division by `p`?

Answer: `{4}` for `p > 3`, `{1}` for `p = 3`.
-/

namespace Imc2023P4

/-- The set of possible residues of `a₂ = 2^k + 2` mod `p`, given that
`a_i = i^k + i` forms a complete residue system mod p. -/
determine answer (p : ℕ) : Set ℕ :=
  if p = 3 then {1} else {4}

problem imc2023_p4 (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k)
    (hres : Function.Surjective (fun i : Fin p => ((i.val ^ k + i.val : ℕ) : ZMod p))) :
    ((2 ^ k + 2 : ℕ) % p) ∈ answer p := by
  -- TODO: Formalize the cyclotomic/lemma argument:
  -- For p > 2, show 2^{k-1} ≡ 1 (mod p), hence 2^k + 2 ≡ 4 (mod p).
  -- For p = 3, direct check gives 2^k + 2 ≡ 1 (mod 3).
  sorry

end Imc2023P4
