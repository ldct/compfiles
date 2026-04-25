/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Dist

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2008, Problem 6
(IMC 2008, Day 1, Problem 6)

For a permutation `σ = (i₁, …, iₙ)` of `(1, …, n)`, define
`D(σ) = ∑ |iₖ - k|`. Let
`Q(n, d) = #{σ ∈ Sₙ : D(σ) = d}`.
Prove that `Q(n, d)` is even for `d ≥ 2n`.

## Proof sketch

Consider the matrix `M ∈ ℤ[X]^{n×n}` with `M_{i,j} = X^{|i-j|}`. Its
determinant equals
`det M = ∑_{σ ∈ Sₙ} sgn(σ) · X^{D(σ)}`.

Working modulo `2` (i.e. over `ZMod 2 [X]`), the signs disappear and
`det M ≡ ∑_{σ ∈ Sₙ} X^{D(σ)} (mod 2)`,
so the coefficient of `X^d` in `det M (mod 2)` equals `Q(n,d) (mod 2)`.

A direct row-reduction (subtract `X` times each row from the next)
shows that
`det M = (1 - X²)^{n-1}`,
which has degree `2(n-1) = 2n - 2`. So for `d ≥ 2n`, the coefficient
of `X^d` in `det M` is `0`, hence `Q(n, d)` is even.
-/

namespace Imc2008P6

open Polynomial Equiv Finset

/-- The displacement of a permutation `σ` of `Fin n`:
`D(σ) = ∑ᵢ |σ(i) - i|`. -/
noncomputable def displacement {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, (σ i).val.dist i.val

/-- The number of permutations `σ` of `Fin n` with displacement `d`. -/
noncomputable def Q (n d : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Perm (Fin n) => displacement σ = d)).card

snip begin

/-- The polynomial `X^|i-j|` over a commutative ring `R`. -/
noncomputable def displacementMatrix (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R[X] :=
  fun i j => X ^ (i.val.dist j.val)

/-- The lower-triangular elementary matrix `L` over `R[X]` whose row `i`
implements "subtract `X` times row `i-1`": `L_{i,i} = 1`, `L_{i,i-1} = -X`,
all other entries `0`. The determinant of `L` is `1`. -/
noncomputable def rowOpMatrix (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R[X] := fun i j =>
  if i = j then 1
  else if (j : ℕ) + 1 = i then -X
  else 0

lemma rowOpMatrix_blockTriangular_toDual (R : Type*) [CommRing R] (n : ℕ) :
    (rowOpMatrix R n).BlockTriangular OrderDual.toDual := by
  intro i j hij
  -- hij : OrderDual.toDual j < OrderDual.toDual i, i.e., i < j
  unfold rowOpMatrix
  have hij' : (i : ℕ) < j := hij
  have hne : i ≠ j := ne_of_lt hij'
  have hne2 : (j : ℕ) + 1 ≠ i := by omega
  simp [hne, hne2]

lemma det_rowOpMatrix (R : Type*) [CommRing R] (n : ℕ) :
    (rowOpMatrix R n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (rowOpMatrix_blockTriangular_toDual R n)]
  apply Finset.prod_eq_one
  intro i _
  unfold rowOpMatrix
  simp

/-- The "two-term" form of `(L * M)_{ij}`: the sum over `k` of
`L_{ik} * M_{kj}` reduces to `M_{ij} - X * M_{i-1, j}` (where the second
term is absent for `i = 0`). -/
lemma rowOp_mul_displacement_aux (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    (rowOpMatrix R n * displacementMatrix R n) i j =
      (X : R[X]) ^ (i : ℕ).dist (j : ℕ)
        - if (i : ℕ) = 0 then 0
          else X * X ^ (((i : ℕ) - 1).dist (j : ℕ)) := by
  rw [Matrix.mul_apply]
  unfold rowOpMatrix displacementMatrix
  -- Split the sum using Finset.sum_ite for the diagonal term, plus the rest.
  have key : ∀ k : Fin n, (if i = k then (1 : R[X])
        else if (k : ℕ) + 1 = (i : ℕ) then -X else 0) * X ^ (k : ℕ).dist (j : ℕ) =
      (if i = k then X ^ (k : ℕ).dist (j : ℕ) else 0)
        + (if (k : ℕ) + 1 = (i : ℕ) then -X * X ^ (k : ℕ).dist (j : ℕ) else 0) := by
    intro k
    by_cases hik : i = k
    · simp [hik]
    · by_cases hk : (k : ℕ) + 1 = (i : ℕ)
      · simp only [if_neg hik, if_pos hk]
        ring
      · simp only [if_neg hik, if_neg hk, zero_mul, add_zero]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq Finset.univ i (fun k => X ^ (k : ℕ).dist (j : ℕ))]
  rw [if_pos (Finset.mem_univ i)]
  -- Remaining: ∑ if k+1=i then -X * X^|k-j| = - if i=0 then 0 else X * X^|(i-1)-j|
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi]
    have hzero : ∑ k : Fin n, (if (k : ℕ) + 1 = (i : ℕ) then -X * X ^ (k : ℕ).dist (j : ℕ) else (0 : R[X])) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have : (k : ℕ) + 1 ≠ (i : ℕ) := by rw [hi]; omega
      simp [this]
    rw [hzero]; ring
  · rw [if_neg hi]
    have hi_lt : (i : ℕ) - 1 < n := by have := i.isLt; omega
    have h_unique : ∀ k : Fin n, (k : ℕ) + 1 = (i : ℕ) ↔ (k : ℕ) = (i : ℕ) - 1 := by
      intro k
      omega
    have : ∑ k : Fin n, (if (k : ℕ) + 1 = (i : ℕ) then -X * X ^ (k : ℕ).dist (j : ℕ) else (0 : R[X]))
        = -X * X ^ ((i : ℕ) - 1).dist (j : ℕ) := by
      have heq : ∑ k : Fin n, (if (k : ℕ) + 1 = (i : ℕ) then
            -X * X ^ (k : ℕ).dist (j : ℕ) else (0 : R[X]))
          = ∑ k : Fin n, (if k = (⟨(i : ℕ) - 1, hi_lt⟩ : Fin n) then
              (-X * X ^ ((i : ℕ) - 1).dist (j : ℕ) : R[X]) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = (⟨(i : ℕ) - 1, hi_lt⟩ : Fin n)
        · have : (k : ℕ) + 1 = (i : ℕ) := by
            rw [hk]
            show ((i : ℕ) - 1) + 1 = (i : ℕ); omega
          rw [if_pos this, if_pos hk]
          congr 1
          rw [hk]
        · have : (k : ℕ) + 1 ≠ (i : ℕ) := by
            intro h
            apply hk
            apply Fin.ext
            show (k : ℕ) = (i : ℕ) - 1
            omega
          rw [if_neg this, if_neg hk]
      rw [heq]
      rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) (⟨(i : ℕ) - 1, hi_lt⟩ : Fin n)
            (fun _ => (-X * X ^ ((i : ℕ) - 1).dist (j : ℕ) : R[X]))]
      simp
    rw [this]; ring

/-- The product `L * M` is upper triangular. -/
lemma rowOp_mul_displacement_apply (R : Type*) [CommRing R] (n : ℕ) (i j : Fin n) :
    (rowOpMatrix R n * displacementMatrix R n) i j =
      if (i : ℕ) = 0 then (X : R[X]) ^ (j : ℕ)
      else if (j : ℕ) < (i : ℕ) then 0
      else if (j : ℕ) = (i : ℕ) then 1 - X^2
      else X ^ ((j : ℕ) - (i : ℕ)) * (1 - X^2) := by
  rw [rowOp_mul_displacement_aux]
  by_cases hi : (i : ℕ) = 0
  · simp [hi, Nat.dist]
  · simp only [hi, if_false]
    have hi_pos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi
    by_cases hji_lt : (j : ℕ) < (i : ℕ)
    · simp only [hji_lt, if_true]
      have hdi : (i : ℕ).dist (j : ℕ) = (i : ℕ) - (j : ℕ) :=
        Nat.dist_eq_sub_of_le_right (le_of_lt hji_lt)
      have hdi' : ((i : ℕ) - 1).dist (j : ℕ) = (i : ℕ) - 1 - (j : ℕ) := by
        apply Nat.dist_eq_sub_of_le_right; omega
      rw [hdi, hdi']
      have h1 : (i : ℕ) - (j : ℕ) = ((i : ℕ) - 1 - (j : ℕ)) + 1 := by omega
      rw [h1, pow_add, pow_one]
      ring
    · push Not at hji_lt
      by_cases hji_eq : (j : ℕ) = (i : ℕ)
      · -- j = i.
        rw [if_neg (not_lt.mpr hji_lt), if_pos hji_eq]
        have hdi : (i : ℕ).dist (j : ℕ) = 0 := by
          rw [hji_eq, Nat.dist_self]
        have hdi' : ((i : ℕ) - 1).dist (j : ℕ) = 1 := by
          rw [hji_eq, Nat.dist_comm]
          rw [Nat.dist_eq_sub_of_le_right (by omega : (i : ℕ) - 1 ≤ (i : ℕ))]
          omega
        rw [hdi, hdi', pow_zero, pow_one]
        ring
      · -- j > i, so j > i-1.
        have hji_gt : (i : ℕ) < (j : ℕ) := lt_of_le_of_ne hji_lt (Ne.symm hji_eq)
        simp only [not_lt.mpr hji_lt, hji_eq, if_false]
        have hdi : (i : ℕ).dist (j : ℕ) = (j : ℕ) - (i : ℕ) :=
          Nat.dist_eq_sub_of_le (le_of_lt hji_gt)
        have hdi' : ((i : ℕ) - 1).dist (j : ℕ) = (j : ℕ) - ((i : ℕ) - 1) := by
          apply Nat.dist_eq_sub_of_le; omega
        rw [hdi, hdi']
        have h1 : (j : ℕ) - ((i : ℕ) - 1) = (j : ℕ) - (i : ℕ) + 1 := by omega
        rw [h1, pow_add, pow_one]
        ring

/-- The product `L * M` is upper triangular. -/
lemma rowOp_mul_displacement_blockTriangular (R : Type*) [CommRing R] (n : ℕ) :
    (rowOpMatrix R n * displacementMatrix R n).BlockTriangular id := by
  intro i j hij
  -- hij : (j : Fin n) < (i : Fin n), i.e. j < i.
  rw [rowOp_mul_displacement_apply]
  have hij' : (j : ℕ) < (i : ℕ) := hij
  have hi_pos : 0 < (i : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hij'
  rw [if_neg (by omega : (i : ℕ) ≠ 0)]
  rw [if_pos hij']

/-- The diagonal of `L * M` is `(1, 1-X², 1-X², …, 1-X²)`. -/
lemma rowOp_mul_displacement_diag (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    (rowOpMatrix R n * displacementMatrix R n) i i =
      if (i : ℕ) = 0 then (1 : R[X]) else 1 - X^2 := by
  rw [rowOp_mul_displacement_apply]
  by_cases hi : (i : ℕ) = 0
  · simp [hi]
  · simp [hi]

/-- The determinant of `displacementMatrix` is `(1 - X²)^{n-1}`. -/
lemma det_displacementMatrix (R : Type*) [CommRing R] (n : ℕ) (hn : 0 < n) :
    (displacementMatrix R n).det = (1 - X^2) ^ (n - 1) := by
  -- det L = 1, so det M = det (L * M).
  have hL : (rowOpMatrix R n).det = 1 := det_rowOpMatrix R n
  have hLM : (rowOpMatrix R n * displacementMatrix R n).det =
             (displacementMatrix R n).det := by
    rw [Matrix.det_mul, hL, one_mul]
  rw [← hLM]
  rw [Matrix.det_of_upperTriangular (rowOp_mul_displacement_blockTriangular R n)]
  -- Now product over diagonal.
  have hprod : ∀ i : Fin n, (rowOpMatrix R n * displacementMatrix R n) i i =
               if (i : ℕ) = 0 then (1 : R[X]) else 1 - X^2 := rowOp_mul_displacement_diag R n
  simp_rw [hprod]
  -- product of (if i=0 then 1 else 1-X²) over i : Fin n = (1-X²)^(n-1).
  have hcard : ((Finset.univ : Finset (Fin n)).filter
                  (fun i : Fin n => ¬ (i : ℕ) = 0)).card = n - 1 := by
    have heq : (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => ¬ (i : ℕ) = 0) =
           (Finset.univ : Finset (Fin n)).erase ⟨0, hn⟩ := by
      ext i
      simp [Finset.mem_erase, Fin.ext_iff]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hcard]

/-- Expressing the determinant as a signed sum over permutations. -/
lemma det_displacementMatrix_apply (R : Type*) [CommRing R] (n : ℕ) :
    (displacementMatrix R n).det =
      ∑ σ : Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (X : R[X]) ^ (σ i).val.dist i.val := by
  rw [Matrix.det_apply]
  rfl

/-- Working over `ZMod 2`, signs of permutations are all `1`, so
`det M = ∑_σ X^{D(σ)}`. -/
lemma det_displacementMatrix_zmod2 (n : ℕ) :
    (displacementMatrix (ZMod 2) n).det =
      ∑ σ : Perm (Fin n), (X : (ZMod 2)[X]) ^ displacement σ := by
  rw [det_displacementMatrix_apply]
  apply Finset.sum_congr rfl
  intro σ _
  -- Convert smul to scalar mult, then use that signs are 1 mod 2.
  have hsmul : (Equiv.Perm.sign σ) • (∏ i : Fin n, (X : (ZMod 2)[X]) ^ (σ i).val.dist i.val) =
      ((Equiv.Perm.sign σ : ℤ) : (ZMod 2)[X]) *
        (∏ i : Fin n, (X : (ZMod 2)[X]) ^ (σ i).val.dist i.val) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [hsmul]
  have hchar2 : (2 : (ZMod 2)[X]) = 0 := by
    have h := CharP.cast_eq_zero (R := (ZMod 2)[X]) 2
    exact_mod_cast h
  have hsgnX : ((Equiv.Perm.sign σ : ℤ) : (ZMod 2)[X]) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]; simp
    · rw [h]
      show ((-1 : ℤ) : (ZMod 2)[X]) = 1
      have hneg : ((-1 : ℤ) : (ZMod 2)[X]) = -1 := by push_cast; ring
      rw [hneg]
      linear_combination -hchar2
  rw [hsgnX, one_mul]
  -- Now match the product ∏ X^|σ(i)-i| with X^∑|σ(i)-i|.
  show ∏ i : Fin n, (X : (ZMod 2)[X]) ^ (σ i).val.dist i.val =
       (X : (ZMod 2)[X]) ^ displacement σ
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- The natDegree of `(1 - X²)^(n-1)` over `ZMod 2` is `2(n-1)`. -/
lemma natDegree_one_sub_X_sq_pow (n : ℕ) :
    ((1 - X^2 : (ZMod 2)[X]) ^ n).natDegree ≤ 2 * n := by
  calc ((1 - X^2 : (ZMod 2)[X]) ^ n).natDegree
      ≤ n * (1 - X^2 : (ZMod 2)[X]).natDegree := natDegree_pow_le
    _ ≤ n * 2 := by
        gcongr
        calc (1 - X^2 : (ZMod 2)[X]).natDegree
            ≤ max (1 : (ZMod 2)[X]).natDegree (X^2 : (ZMod 2)[X]).natDegree :=
              natDegree_sub_le _ _
          _ ≤ 2 := by
              simp [natDegree_pow, natDegree_X]
    _ = 2 * n := by ring

/-- The coefficient of `X^d` in `(1 - X²)^{n-1}` is `0` for `d ≥ 2n`. -/
lemma coeff_one_sub_X_sq_pow_high (n d : ℕ) (hn : 0 < n) (hd : 2 * n ≤ d) :
    ((1 - X^2 : (ZMod 2)[X]) ^ (n - 1)).coeff d = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc ((1 - X^2 : (ZMod 2)[X]) ^ (n - 1)).natDegree
      ≤ 2 * (n - 1) := natDegree_one_sub_X_sq_pow (n - 1)
    _ < 2 * n := by omega
    _ ≤ d := hd

/-- The coefficient of `X^d` in `∑_σ X^{D(σ)}` is the number (mod 2) of permutations
with `D(σ) = d`. -/
lemma coeff_sum_displacement (n d : ℕ) :
    (∑ σ : Perm (Fin n), (X : (ZMod 2)[X]) ^ displacement σ).coeff d =
      ((Finset.univ.filter (fun σ : Perm (Fin n) => displacement σ = d)).card : ZMod 2) := by
  rw [finset_sum_coeff]
  -- Each summand: coeff of X^d in X^{D(σ)} is 1 if D(σ)=d, else 0.
  have hstep : (∑ σ ∈ (Finset.univ : Finset (Perm (Fin n))),
        ((X : (ZMod 2)[X]) ^ displacement σ).coeff d) =
        ∑ σ ∈ (Finset.univ : Finset (Perm (Fin n))),
          (if displacement σ = d then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [Polynomial.coeff_X_pow]
    by_cases h : displacement σ = d
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hstep]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one]

/-- Main computation: `Q(n, d) ≡ 0 (mod 2)` for `d ≥ 2n`. -/
lemma Q_even (n d : ℕ) (hn : 0 < n) (hd : 2 * n ≤ d) : 2 ∣ Q n d := by
  -- Equate the two expressions for det M_{ZMod 2}.
  have heq : (∑ σ : Perm (Fin n), (X : (ZMod 2)[X]) ^ displacement σ) =
             (1 - X^2) ^ (n - 1) := by
    rw [← det_displacementMatrix_zmod2, det_displacementMatrix (ZMod 2) n hn]
  -- Compare coefficient of X^d.
  have hcoeff : (∑ σ : Perm (Fin n), (X : (ZMod 2)[X]) ^ displacement σ).coeff d = 0 := by
    rw [heq]; exact coeff_one_sub_X_sq_pow_high n d hn hd
  rw [coeff_sum_displacement] at hcoeff
  -- (Q n d : ZMod 2) = 0 means 2 ∣ Q n d.
  show 2 ∣ Q n d
  unfold Q
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcoeff

snip end

problem imc2008_p6 (n d : ℕ) (hn : 0 < n) (hd : 2 * n ≤ d) :
    2 ∣ Q n d := Q_even n d hn hd

end Imc2008P6
