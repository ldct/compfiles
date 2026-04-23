/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Competition 2022, Problem 3

Let `p` be a prime. A flea sits at `0 ∈ ℝ`. Each minute it may stay, move left
by `1`, or move right by `1`. After `p − 1` minutes it wants to be at `0`
again. Let `f(p)` be the number of such strategies. Find `f(p) mod p`.

Answer:
- `f(3) ≡ 0 (mod 3)`;
- if `p ≡ 1 (mod 3)`, then `f(p) ≡ 1 (mod p)`;
- if `p ≡ 2 (mod 3)`, then `f(p) ≡ −1 (mod p)`.
-/

namespace Imc2022P3

/-- The number of strategies: count functions s : Fin (p-1) → {-1, 0, 1} with
`∑ i, s i = 0`. Represented as count of tuples in `Fin (p-1) → ({-1,0,1} ⊆ ℤ)`. -/
noncomputable def f (p : ℕ) : ℕ :=
  (Finset.univ.filter fun s : Fin (p - 1) → Fin 3 =>
    (∑ i, ((s i).val : ℤ) - (p - 1 : ℤ)) = 0).card
  -- Note: encoding s i = 0 as "left (-1)", 1 as "stay (0)", 2 as "right (+1)",
  -- so the flea moves (s i).val - 1 each minute; sum = ∑(s i).val - (p-1) = 0.

/-- The residue class of `f(p)` mod `p`. -/
determine answer (p : ℕ) : ZMod p :=
  if p = 3 then 0
  else if p % 3 = 1 then 1
  else -1

problem imc2022_p3 (p : ℕ) (hp : p.Prime) :
    (f p : ZMod p) = answer p := by
  -- TODO: generating-function argument modulo p.
  sorry

end Imc2022P3
