/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2024, Problem 9

A matrix `A = (aᵢⱼ)` of size `m × n` is called *nice* if:

(i)   the set of all entries of `A` equals `{1, 2, …, 2t}` for some
      positive integer `t`;
(ii)  `aᵢⱼ ≤ aᵢ,ⱼ₊₁` and `aᵢⱼ ≤ aᵢ₊₁,ⱼ`;
(iii) if `aᵢⱼ = aₖₗ` then `i = k` or `j = ℓ`;
(iv)  for each `s = 1, …, 2t - 1`, there exist `i ≠ k` and `j ≠ ℓ`
      with `aᵢⱼ = s` and `aₖₗ = s + 1`.

Prove that the number of nice `m × n` matrices is even.
-/

namespace Imc2024P9

/-- `A : Fin m → Fin n → ℕ` is a nice matrix. -/
def IsNice {m n : ℕ} (A : Fin m → Fin n → ℕ) : Prop :=
  ∃ t : ℕ, 0 < t ∧
    -- (i) entries form {1, …, 2t}
    (∀ v, v ∈ Finset.Icc 1 (2 * t) ↔ ∃ i j, A i j = v) ∧
    -- (ii) row/column monotonicity
    (∀ i, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
        A i j ≤ A i ⟨j.val + 1, hj⟩) ∧
    (∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ j,
        A i j ≤ A ⟨i.val + 1, hi⟩ j) ∧
    -- (iii) each value in at most one row and one column
    (∀ i j k l, A i j = A k l → i = k ∨ j = l) ∧
    -- (iv) consecutive values in distinct row and distinct column
    (∀ s ∈ Finset.Icc 1 (2 * t - 1),
        ∃ i j k l, i ≠ k ∧ j ≠ l ∧ A i j = s ∧ A k l = s + 1)

/-- The (finite) set of nice `m × n` matrices, represented as functions
`Fin m → Fin n → ℕ` bounded by some large value. We use `Fintype` over
matrices with entries bounded by `2 * m * n` (which suffices since any
nice matrix uses entries `≤ 2t ≤ 2 · m · n`). -/
noncomputable def niceCount (m n : ℕ) : ℕ :=
  Nat.card {A : Fin m → Fin n → ℕ // IsNice A}

/-! ### Scaffolding for the official solution

The proof proceeds via the friendship graph on standard Young tableaux of
shape `m × n`. The plan, following Petrov's solution:

1. Define `IsSYT Y` = `Y : Fin m → Fin n → ℕ` is a standard Young tableau
   of shape `m × n` (entries are exactly `{1, …, m·n}`, strictly increasing
   along rows and columns).
2. Two SYTs `Y₁`, `Y₂` are *friends* iff they differ by swapping a pair of
   consecutive integers `x, x+1` whose positions are non-adjacent
   (so the swap preserves monotonicity).
3. Each nice matrix `A` with multiplicities `n₁, …, n_{2t}` of values
   `1, …, 2t` is canonically expanded to an SYT `Y_A` by replacing the `nᵢ`
   copies of `i` (which form an antichain — distinct rows and columns) with
   the integers `Σⱼ<ᵢ nⱼ + 1, …, Σⱼ≤ᵢ nⱼ` in the unique monotone order.
4. The number of friends of `Y_A` equals `2t - 1` (odd) — one swap per
   consecutive-value boundary `s ∈ {1, …, 2t-1}` of `A`. Conversely every
   SYT with an odd number of friends arises this way from a unique nice
   matrix.
5. By the handshaking lemma applied to the friendship graph on SYTs, the
   number of vertices of odd degree is even. This is exactly `niceCount m n`.
-/

/-- Standard Young tableau of rectangular shape `m × n`: entries are a
permutation of `{1, …, m·n}`, strictly increasing along rows and columns. -/
def IsSYT {m n : ℕ} (Y : Fin m → Fin n → ℕ) : Prop :=
  (∀ v, v ∈ Finset.Icc 1 (m * n) ↔ ∃ i j, Y i j = v) ∧
  (∀ i j k l, Y i j = Y k l → i = k ∧ j = l) ∧
  (∀ i, ∀ j : Fin n, ∀ hj : j.val + 1 < n,
      Y i j < Y i ⟨j.val + 1, hj⟩) ∧
  (∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ j,
      Y i j < Y ⟨i.val + 1, hi⟩ j)

/-- Two `m × n` arrays are friends if they coincide except they swap
consecutive integers `x` and `x + 1`. -/
def AreFriends {m n : ℕ} (Y₁ Y₂ : Fin m → Fin n → ℕ) : Prop :=
  ∃ x : ℕ,
    (∀ i j, Y₁ i j = x → Y₂ i j = x + 1) ∧
    (∀ i j, Y₁ i j = x + 1 → Y₂ i j = x) ∧
    (∀ i j, Y₁ i j ≠ x → Y₁ i j ≠ x + 1 → Y₂ i j = Y₁ i j)

/-- Count of friends of an SYT `Y` among SYTs of shape `m × n`. -/
noncomputable def friendCount {m n : ℕ} (Y : Fin m → Fin n → ℕ) : ℕ :=
  Nat.card {Y' : Fin m → Fin n → ℕ // IsSYT Y' ∧ AreFriends Y Y'}

/-- Sum of friend counts over all SYTs equals twice the number of friend
pairs (handshaking on the friendship graph). -/
lemma sum_friendCount_even (m n : ℕ) :
    Even (∑ᶠ Y : {Y : Fin m → Fin n → ℕ // IsSYT Y}, friendCount Y.1) := by
  -- Standard handshaking lemma for the (symmetric, irreflexive) friendship
  -- relation on the finite set of SYTs.
  sorry

/-- Key bijection: nice matrices correspond to SYTs with an odd number of
friends. -/
lemma niceCount_eq_oddDegree_count (m n : ℕ) :
    niceCount m n =
      Nat.card {Y : {Y : Fin m → Fin n → ℕ // IsSYT Y} // Odd (friendCount Y.1)} := by
  -- The map A ↦ Y_A defined in step 3 of the plan above is a bijection
  -- between nice matrices and SYTs Y with friendCount Y odd. Forward:
  -- expand multiplicities; the friend swaps correspond to the 2t - 1
  -- value-boundaries of A. Backward: collapse runs of consecutive integers
  -- whose positions form antichains.
  sorry

problem imc2024_p9 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Even (niceCount m n) := by
  -- Apply the bijection then handshaking. Once `niceCount m n` is the
  -- number of odd-degree vertices in the friendship graph, evenness is
  -- the standard corollary of `sum_friendCount_even`.
  -- TODO: assemble `niceCount_eq_oddDegree_count` + `sum_friendCount_even`
  -- via the standard "odd-degree vertices form an even-sized set" argument.
  sorry

end Imc2024P9
