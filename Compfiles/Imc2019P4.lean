/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2019, Problem 4
(IMC 2019, Day 1, Problem 4)

Define `a 0 = 1`, `a 1 = 2`, and `(n+3) * a (n+2) = (6n+9) * a (n+1) - n * a n`
for `n ≥ 0`. Prove that every `a n` is an integer.

## Solution outline

Let `f(x) = ∑ a_n x^n` be the generating function.  The recurrence shows that
`f` satisfies the quadratic relation `x f(x)^2 - (1 - x) f(x) + 1 = 0`, i.e.
`f = 1 + x f + x f^2`.  Comparing coefficients gives

  `a_{n+1} = a_n + ∑_{k=0}^{n} a_k a_{n-k}`,

which is a recurrence with integer coefficients and integer initial data
`a_0 = 1`.  Hence every `a_n ∈ ℤ`.

(The sequence is the sequence of large Schröder numbers
`1, 2, 6, 22, 90, 394, 1806, …`.)
-/

namespace Imc2019P4

/-- The sequence `a` defined by the division recurrence, working in `ℚ`. -/
noncomputable def a : ℕ → ℚ
  | 0 => 1
  | 1 => 2
  | (n + 2) => ((6 * n + 9) * a (n + 1) - n * a n) / (n + 3)

snip begin

/-- An auxiliary `ℤ`-valued sequence defined by the convolution recurrence
`b (n+1) = b n + ∑_{k ≤ n} b k * b (n-k)`, `b 0 = 1`.

This recurrence has manifestly integer values. -/
noncomputable def b : ℕ → ℤ
  | 0 => 1
  | (n + 1) =>
      b n + ((Finset.range (n + 1)).attach.sum fun ⟨k, hk⟩ =>
        have : k < n + 1 := Finset.mem_range.mp hk
        b k * b (n - k))
termination_by n => n

lemma b_zero : b 0 = 1 := by
  show b 0 = 1
  rw [b]

lemma b_succ (n : ℕ) : b (n + 1) = b n + ∑ k ∈ Finset.range (n + 1), b k * b (n - k) := by
  rw [b]
  rw [← Finset.sum_attach (Finset.range (n + 1)) (fun k => b k * b (n - k))]

lemma b_one : b 1 = 2 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, b_succ, Finset.sum_range_one]
  simp [b_zero]

/-- `b` satisfies the original division recurrence when interpreted in `ℚ`.
The proof is a nontrivial identity on convolutions, traditionally shown via the
generating function identity `x f^2 - (1-x) f + 1 = 0` together with its
derivative.

TODO: provide a formal proof.  The mathematical content is:

  `(n+3) * b (n+2) = (6n+9) * b (n+1) - n * b n`

equivalently (using the convolution recurrence to eliminate `b (n+2)`),
`(n+3) * ∑_{k≤n+1} b k * b (n+1-k) = (5n+6) * ∑_{k≤n} b k * b (n-k) + (4n+6) * b n`.

This identity is a consequence of the generating-function relation. -/
lemma b_recurrence (n : ℕ) :
    ((n : ℚ) + 3) * b (n + 2) = (6 * n + 9) * b (n + 1) - n * b n := by
  sorry

/-- `a n = b n` as rationals, by strong induction. -/
lemma a_eq_b (n : ℕ) : a n = (b n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [a, b_zero]
    | 1 => simp [a, b_one]
    | (k + 2) =>
      rw [a]
      have hk1 : a (k + 1) = (b (k + 1) : ℚ) := ih (k + 1) (by omega)
      have hk0 : a k = (b k : ℚ) := ih k (by omega)
      rw [hk1, hk0]
      have hne : ((k : ℚ) + 3) ≠ 0 := by
        have : (0 : ℚ) < (k : ℚ) + 3 := by positivity
        exact this.ne'
      rw [div_eq_iff hne]
      have := b_recurrence k
      push_cast at this ⊢
      linarith

snip end

problem imc2019_p4 (n : ℕ) : ∃ z : ℤ, a n = z :=
  ⟨b n, a_eq_b n⟩

end Imc2019P4
