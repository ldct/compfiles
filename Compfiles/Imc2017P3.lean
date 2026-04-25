/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2017, Problem 3

For any positive integer `m`, let `P(m)` denote the product of positive divisors
of `m` (e.g. `P(6) = 36`). For every positive integer `n` define the sequence
`a₁(n) = n`, `a_{k+1}(n) = P(a_k(n))` for `k = 1, …, 2016`.

Determine whether for every set `S ⊆ {1, 2, …, 2017}` there exists a positive
integer `n` such that for every `k` with `1 ≤ k ≤ 2017`, `a_k(n)` is a perfect
square if and only if `k ∈ S`.

Answer: YES.

Proof sketch (from the official solution): take `n = 2 ^ w₁`. Then
`a_k(n) = 2 ^ w_k`, where `w_{k+1} = w_k (w_k + 1) / 2`. Hence `a_k(n)` is a
perfect square iff `w_k` is even. The lemma below shows that any 2017-bit parity
pattern of `(w_k)_{k = 1}^{2017}` is realisable by an appropriate choice of
`w₁`. Specifically, replacing `w₁` by `w₁ + 2 ^ m` flips the parity of
`w_{m+1}` while preserving the parities of `w₁, …, w_m`. Iterating this for
`m = 1, …, 2017` yields any desired parity pattern, hence any desired set `S`.
-/

namespace Imc2017P3

/-- `P m` is the product of the positive divisors of `m`. -/
def P (m : ℕ) : ℕ := (Nat.divisors m).prod id

/-- The iterated sequence `a_k(n)` from the problem (indexed by `Nat`):
`a 0 n = n` and `a (k+1) n = P (a k n)`. So `a (k-1) n` corresponds to
`a_k(n)` in the problem. -/
def a : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => P (a k n)

/-- The answer: yes, every parity pattern is realisable. -/
determine answer : Prop := True

problem imc2017_p3 :
    answer ↔
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 2017 →
      ∃ n : ℕ, 0 < n ∧ ∀ k, 1 ≤ k → k ≤ 2017 →
        (IsSquare (a (k - 1) n) ↔ k ∈ S) := by
  show True ↔ _
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  -- TODO: proof following the official solution.
  -- Take `n = 2 ^ w₁`. Then `a (k-1) n = 2 ^ w_k` where `w_{k+1} = w_k(w_k+1)/2`.
  -- So `a_k(n)` is a perfect square iff `w_k` is even.
  -- Key lemma: if `c₁ = b₁ + 2^m` then for `k = 1, …, m`,
  --   `c_k ≡ b_k + 2^{m-k+1} (mod 2^{m-k+2})`,
  -- so the parities of `b_k` and `c_k` agree for `k ≤ m` but disagree at
  -- `k = m+1`. Iterating, any 2017-bit parity sequence is realisable.
  sorry

end Imc2017P3
