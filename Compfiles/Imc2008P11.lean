/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2008, Problem 11
(IMC 2008, Day 2, Problem 5)

Let `n` be a positive integer, and consider the matrix `A = (a_{ij})_{1 ≤ i,j ≤ n}`,
where `a_{ij} = 1` if `i + j` is a prime number and `0` otherwise.
Prove that `|det A| = k^2` for some integer `k`.

## Proof sketch

Because the only even prime is `2`, a nonzero entry `a_{ij}` (with `i + j ≥ 2`
prime) has `i + j` odd — except for the single entry `a_{1,1} = 1`
(since `1 + 1 = 2` is prime). So `A` has an almost-"checkerboard" structure.

By multilinearity in the first row,
`det A = det X' + det Y`
where `X'` is `A` with first row replaced by `(1, 0, …, 0)` and `Y` is `A` with
entry `a_{1,1}` replaced by `0`. Cofactor expansion gives `det X' = det X`,
where `X` is the `(n−1) × (n−1)` submatrix obtained from `A` by deleting
row 1 and column 1.

Both `X` and `Y` are symmetric, and both have the property that entry `(i, j)`
is zero whenever `i + j` is even (for `Y` this uses that the only excluded
entry `a_{1,1}` is accounted for).

*Key lemma* (`parityOff_det_sq_natAbs`). For any symmetric
`M : Matrix (Fin m) (Fin m) ℤ` with `M i j = 0` whenever `i.val + j.val` is
even: `M.det.natAbs` is a perfect square. Moreover, when `m` is odd,
`det M = 0`.

*Reduction*. When `n` is odd, `Y` has odd size `n`, so `det Y = 0`,
and `|det A| = |det X|` is a square (size `n − 1` is even). When `n` is even,
`X` has odd size `n − 1`, so `det X = 0`, and `|det A| = |det Y|` is a square.
-/

namespace Imc2008P11

open Matrix

/-- The IMC 2008 P11 matrix: entry `(i, j)` is `1` if `(i + 1) + (j + 1)`
is a prime number (`Fin n` is `0`-indexed), otherwise `0`. -/
def primeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if Nat.Prime (i.val + j.val + 2) then 1 else 0

snip begin

/-- `primeMatrix` is symmetric. -/
lemma primeMatrix_symm (n : ℕ) : (primeMatrix n).IsSymm := by
  ext i j
  simp only [primeMatrix, Matrix.transpose_apply]
  rw [show i.val + j.val = j.val + i.val from Nat.add_comm _ _]

/-- For entries `(i, j)` with `i + j ≥ 1`, if `primeMatrix n i j ≠ 0` then
`i.val + j.val` is odd. (Primes other than `2` are odd.) -/
lemma primeMatrix_nonzero_odd_of_pos {n : ℕ} {i j : Fin n}
    (hpos : 0 < i.val + j.val)
    (hne : primeMatrix n i j ≠ 0) : Odd (i.val + j.val) := by
  simp only [primeMatrix, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] at hne
  rcases hne.eq_two_or_odd' with h2 | hOdd
  · omega
  · obtain ⟨k, hk⟩ := hOdd
    refine ⟨k - 1, ?_⟩
    omega

/-- Key lemma: a symmetric integer matrix whose entries vanish outside the
"odd-parity" positions has a determinant whose absolute value is a perfect
square. Furthermore, when the size is odd, the determinant is zero.

The idea of the proof:
- If `m` is odd: partition the index set by parity of `i.val`. Rows with even
  parity have support only in columns of odd parity, and vice versa. The
  number of even-parity indices is `⌈m/2⌉` and of odd-parity is `⌊m/2⌋`; one
  strictly exceeds the other, forcing linear dependence among rows.
- If `m` is even (`m = 2k`): reorder rows and columns to put even-parity
  indices first. The matrix becomes block anti-diagonal `[[0, B], [Bᵀ, 0]]`
  (the `Bᵀ` coming from symmetry), whose determinant is
  `(-1)^k · (det B)^2`. Taking absolute values gives `(det B)^2`, a square.

TODO: formalize this argument. -/
lemma parityOff_det_sq_natAbs {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ)
    (_hSymm : M.IsSymm) (_hOff : ∀ i j : Fin m, Even (i.val + j.val) → M i j = 0) :
    IsSquare M.det.natAbs := by
  sorry

/-- Variant: for odd size, the determinant itself is zero.

*Proof.* For every permutation `σ`, either `M (σ i) i = 0` for some `i`
(making the product term `0`), or else `σ i + i` is odd for every `i`. The
latter means `σ` bijects the even-parity indices with the odd-parity ones,
which is impossible when `m` is odd since the two sets have different
cardinalities. -/
lemma parityOff_det_eq_zero_of_odd {m : ℕ} (hOdd : Odd m)
    (M : Matrix (Fin m) (Fin m) ℤ)
    (hOff : ∀ i j : Fin m, Even (i.val + j.val) → M i j = 0) :
    M.det = 0 := by
  rw [Matrix.det_apply]
  -- Each term in the sum is zero.
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  -- Suppose the product term is nonzero; derive a contradiction.
  by_contra hne
  have hprod_ne : (∏ i, M (σ i) i) ≠ 0 := by
    intro h; rw [h, smul_zero] at hne; exact hne rfl
  -- Every factor is nonzero.
  have hfac : ∀ i : Fin m, M (σ i) i ≠ 0 := fun i => by
    intro h0
    exact hprod_ne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  -- Hence `(σ i).val + i.val` is odd for every `i`.
  have hOddSum : ∀ i : Fin m, Odd ((σ i).val + i.val) := by
    intro i
    rcases Nat.even_or_odd ((σ i).val + i.val) with hE | hO
    · exact absurd (hOff (σ i) i hE) (hfac i)
    · exact hO
  -- Define the parity function φ : Fin m → Bool (true for odd parity).
  -- Since `Odd (σ i).val + i.val`, σ flips parity, giving a parity-flipping
  -- bijection. We derive that the number of even and odd parity indices
  -- in `Fin m` are equal, contradicting `Odd m`.
  -- Concretely: σ restricts to a bijection from `{i | Even i.val}` to
  -- `{i | Odd i.val}` (since a flipping bijection pairs them up).
  let E : Finset (Fin m) := Finset.univ.filter (fun i => Even i.val)
  let O : Finset (Fin m) := Finset.univ.filter (fun i => Odd i.val)
  -- σ maps E into O (sending i with Even i.val to j with Odd j.val).
  have hMapE : ∀ i ∈ E, σ i ∈ O := by
    intro i hi
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hodd := hOddSum i
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
    -- (σ i).val + i.val odd, i.val even → (σ i).val odd
    rcases hi with ⟨k, hk⟩
    rcases hodd with ⟨ℓ, hℓ⟩
    exact ⟨ℓ - k, by omega⟩
  -- σ is injective, so |E| ≤ |O|.
  have hEcard_le : E.card ≤ O.card := by
    exact Finset.card_le_card_of_injOn σ hMapE
      (fun a _ b _ h => σ.injective h)
  -- By symmetry (applying the same to σ⁻¹), |O| ≤ |E|.
  have hOddSum' : ∀ i : Fin m, Odd ((σ.symm i).val + i.val) := by
    intro i
    have := hOddSum (σ.symm i)
    simpa [Equiv.apply_symm_apply, Nat.add_comm] using this
  have hMapO : ∀ i ∈ O, σ.symm i ∈ E := by
    intro i hi
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hodd := hOddSum' i
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with ⟨k, hk⟩
    rcases hodd with ⟨ℓ, hℓ⟩
    exact ⟨ℓ - k, by omega⟩
  have hOcard_le : O.card ≤ E.card := by
    exact Finset.card_le_card_of_injOn σ.symm hMapO
      (fun a _ b _ h => σ.symm.injective h)
  have hEO : E.card = O.card := le_antisymm hEcard_le hOcard_le
  -- But E ∪ O = univ and E, O are disjoint, so |E| + |O| = m. With |E| = |O|,
  -- we get m = 2|E|, so m is even. Contradiction with Odd m.
  have hDisj : Disjoint E O := by
    rw [Finset.disjoint_filter]
    rintro x - ⟨k, hk⟩ ⟨ℓ, hℓ⟩
    omega
  have hUnion : E ∪ O = Finset.univ := by
    ext x
    simp only [E, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Nat.even_or_odd x.val with h | h
    · exact ⟨fun _ => trivial, fun _ => Or.inl h⟩
    · exact ⟨fun _ => trivial, fun _ => Or.inr h⟩
  have hCardSum : E.card + O.card = m := by
    have : (E ∪ O).card = m := by
      rw [hUnion]; exact Finset.card_univ.trans (Fintype.card_fin m)
    rw [Finset.card_union_of_disjoint hDisj] at this
    exact this
  -- m = 2 |E|, contradicting Odd m.
  rw [hEO] at hCardSum
  have : Even m := ⟨O.card, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hOdd) this

snip end

problem imc2008_p11 (n : ℕ) (hn : 0 < n) :
    ∃ k : ℤ, |(primeMatrix n).det| = k ^ 2 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Reduce to `IsSquare (primeMatrix (m + 1)).det.natAbs` and then recover an
  -- integer `k`.
  suffices h : IsSquare (primeMatrix (m + 1)).det.natAbs by
    obtain ⟨k, hk⟩ := h
    refine ⟨(k : ℤ), ?_⟩
    have : ((primeMatrix (m + 1)).det.natAbs : ℤ) = ((k : ℤ)) ^ 2 := by
      rw [hk]; push_cast; ring
    rw [Int.abs_eq_natAbs, this]
  -- Set A = primeMatrix (m + 1).
  set A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := primeMatrix (m + 1) with hA_def
  -- Define e0 (first standard basis vector) and w (row 0 of A with (0,0) zeroed).
  let e0 : Fin (m + 1) → ℤ := fun j => if j.val = 0 then 1 else 0
  let w  : Fin (m + 1) → ℤ := fun j => if j.val = 0 then 0 else A 0 j
  -- Row 0 of A splits as e0 + w:
  have hRow0 : A 0 = e0 + w := by
    funext j
    simp only [e0, w, Pi.add_apply]
    by_cases hj : j.val = 0
    · -- j = 0: A 0 0 = 1 since 0 + 0 + 2 = 2 is prime
      have hj0 : j = (0 : Fin (m + 1)) := by
        apply Fin.ext; rw [hj]; rfl
      have hprime : Nat.Prime 2 := by decide
      have : A 0 j = 1 := by
        rw [hj0, hA_def]
        show (if Nat.Prime ((0 : Fin (m + 1)).val + (0 : Fin (m + 1)).val + 2) then (1 : ℤ) else 0) = 1
        have h02 : (0 : Fin (m + 1)).val + (0 : Fin (m + 1)).val + 2 = 2 := by
          show 0 + 0 + 2 = 2; rfl
        rw [h02, if_pos hprime]
      simp [hj, this]
    · simp [hj]
  -- Define X' = updateRow A 0 e0 and Y = updateRow A 0 w.
  set X' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := A.updateRow 0 e0 with hX'_def
  set Y  : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := A.updateRow 0 w  with hY_def
  -- Key decomposition: det A = det X' + det Y.
  have hDecomp : A.det = X'.det + Y.det := by
    have hA_eq : A = A.updateRow 0 (e0 + w) := by
      ext i j
      rw [Matrix.updateRow_apply]
      split_ifs with hi
      · subst hi; exact congrFun hRow0 j
      · rfl
    conv_lhs => rw [hA_eq]
    rw [Matrix.det_updateRow_add]
  -- Key fact about A: if A i j ≠ 0 and (i, j) ≠ (0, 0), then i.val + j.val is odd.
  have hA_parity : ∀ (i j : Fin (m + 1)), (i.val ≠ 0 ∨ j.val ≠ 0) →
      Even (i.val + j.val) → A i j = 0 := by
    intro i j hne hEven
    simp only [hA_def, primeMatrix]
    by_contra hne'
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hne'
    -- hne' : Nat.Prime (i.val + j.val + 2)
    -- hEven : Even (i.val + j.val)
    -- so i.val + j.val + 2 is even; since it's prime, it equals 2, so i+j = 0
    have : i.val + j.val + 2 = 2 := by
      rcases hne'.eq_two_or_odd' with h2 | hOdd
      · exact h2
      · exfalso
        obtain ⟨k, hk⟩ := hEven
        obtain ⟨ℓ, hℓ⟩ := hOdd
        omega
    rcases hne with hi | hj <;> omega
  -- Y has the parity-off-diagonal property.
  have hY_parityOff : ∀ i j : Fin (m + 1), Even (i.val + j.val) → Y i j = 0 := by
    intro i j hEven
    simp only [Y, Matrix.updateRow_apply]
    by_cases hi : i = 0
    · -- i = 0 branch
      subst hi
      simp only [↓reduceIte]
      show w j = 0
      simp only [w]
      by_cases hj : j.val = 0
      · simp [hj]
      · simp only [hj, if_false]
        -- need A 0 j = 0; j.val ≠ 0 and 0 + j.val = j.val even
        exact hA_parity 0 j (Or.inr hj) hEven
    · simp only [hi, ↓reduceIte]
      -- i ≠ 0 so i.val ≠ 0; apply hA_parity
      have hi_val : i.val ≠ 0 := fun h => hi (Fin.ext h)
      exact hA_parity i j (Or.inl hi_val) hEven
  -- Y is symmetric.
  have hA_symm_eq : ∀ a b : Fin (m + 1), A a b = A b a := by
    intro a b
    exact ((primeMatrix_symm (m + 1)).apply a b).symm
  have hY_symm : Y.IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    -- target: Y j i = Y i j
    simp only [Y, Matrix.updateRow_apply]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi; subst hj; rfl
    · subst hi
      -- target : Y j 0 = Y 0 j : (if j = 0 then w 0 else A j 0) = w j
      -- j ≠ 0, so LHS = A j 0
      simp only [hj, ↓reduceIte]
      -- target : A j 0 = w j
      simp only [w]
      have hj_val : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp only [hj_val, if_false]
      exact (hA_symm_eq j 0)
    · subst hj
      -- target : Y 0 i = Y i 0, i ≠ 0
      simp only [hi, ↓reduceIte]
      -- target : w i = A i 0
      simp only [w]
      have hi_val : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp only [hi_val, if_false]
      exact hA_symm_eq 0 i
    · simp only [hi, hj, ↓reduceIte]
      exact hA_symm_eq j i
  -- X' determinant: Laplace expansion along row 0 gives det X' = det X
  -- where X is the submatrix removing row 0 and column 0 (of size m × m).
  let X : Matrix (Fin m) (Fin m) ℤ :=
    A.submatrix Fin.succ Fin.succ
  have hX'_det : X'.det = X.det := by
    rw [Matrix.det_succ_row_zero X']
    -- X' 0 j = e0 j, so only j = 0 contributes.
    have hOnly : ∀ j : Fin (m + 1), j ≠ 0 →
        (-1 : ℤ) ^ (j : ℕ) * X' 0 j * (X'.submatrix Fin.succ j.succAbove).det = 0 := by
      intro j hj
      have : X' 0 j = 0 := by
        simp only [X', Matrix.updateRow_self, e0]
        have : j.val ≠ 0 := fun h => hj (Fin.ext h)
        simp [this]
      rw [this]; ring
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · -- only contribution: j = 0
      have h00 : X' 0 0 = 1 := by
        simp only [X', Matrix.updateRow_self, e0]
        rfl
      have hsub : X'.submatrix Fin.succ (0 : Fin (m + 1)).succAbove = X := by
        ext i j
        simp only [Matrix.submatrix_apply, X', Matrix.updateRow_apply]
        have hne : (Fin.succ i : Fin (m + 1)) ≠ 0 := Fin.succ_ne_zero _
        simp only [hne, ↓reduceIte]
        congr 1
      rw [hsub, h00]; simp
    · intros b _ hb; exact hOnly b hb
    · intro h; exact absurd (Finset.mem_univ _) h
  -- X is symmetric (as submatrix of symmetric A indexed by same injection).
  have hX_symm : X.IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    simp only [X, Matrix.submatrix_apply]
    exact hA_symm_eq (Fin.succ j) (Fin.succ i)
  -- X has the parity-off-diagonal property.
  have hX_parityOff : ∀ i j : Fin m, Even (i.val + j.val) → X i j = 0 := by
    intro i j hEven
    simp only [X, Matrix.submatrix_apply]
    -- X i j = A (i.succ) (j.succ)
    -- (i.succ).val + (j.succ).val = i.val + j.val + 2 (even iff i.val+j.val even)
    have hEven' : Even ((Fin.succ i).val + (Fin.succ j).val) := by
      rcases hEven with ⟨k, hk⟩
      exact ⟨k + 1, by simp [Fin.val_succ]; omega⟩
    apply hA_parity
    · left
      simp [Fin.val_succ]
    · exact hEven'
  -- Now split by parity of (m + 1).
  rw [hDecomp, hX'_det]
  rcases Nat.even_or_odd (m + 1) with hEven | hOdd
  · -- m + 1 even: det Y has square natAbs; det X = 0 (since m odd).
    have hmOdd : Odd m := by
      rcases hEven with ⟨k, hk⟩
      exact ⟨k - 1, by omega⟩
    have hX_zero : X.det = 0 := parityOff_det_eq_zero_of_odd hmOdd X hX_parityOff
    rw [hX_zero, zero_add]
    have := parityOff_det_sq_natAbs Y hY_symm hY_parityOff
    exact this
  · -- m + 1 odd: det X has square natAbs; det Y = 0.
    have hY_zero : Y.det = 0 :=
      parityOff_det_eq_zero_of_odd hOdd Y hY_parityOff
    rw [hY_zero, add_zero]
    exact parityOff_det_sq_natAbs X hX_symm hX_parityOff

end Imc2008P11
