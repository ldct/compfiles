/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 9

Let `A` be a symmetric `m × m` matrix over `𝔽₂` with all diagonal entries
zero. Prove that for every positive integer `n`, each column of `Aⁿ` has a
zero entry.

The proof, following the official solution, considers the bilinear form
`(x,y) := xᵀ y` and uses two facts in characteristic 2:
* `(x,x) = (x,1)` since `x² = x`,
* `(w, A w) = 0` for symmetric zero-diagonal `A` (off-diagonal terms pair
  up via swapping coordinates).

These give the lemma: if `Aⁿ v = 1` then `(v,v) = 0`. Applied to
`v = e_k`, the standard basis vector for column `k`, we get
`1 = (e_k, e_k) = 0`, contradiction.
-/

namespace Imc2010P9

open Matrix

snip begin

/-- In `ZMod 2`, every element squares to itself. -/
lemma sq_eq_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> decide

/-- In `ZMod 2`, `v ⬝ v = ∑ vᵢ`, since each entry equals its square. -/
lemma dotProduct_self {m : ℕ} (v : Fin m → ZMod 2) :
    v ⬝ᵥ v = ∑ i, v i := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  exact sq_eq_self _

/-- `v ⬝ 1 = ∑ vᵢ`. -/
lemma dotProduct_one_vec {m : ℕ} (v : Fin m → ZMod 2) :
    v ⬝ᵥ (fun _ => (1 : ZMod 2)) = ∑ i, v i := by
  unfold dotProduct
  simp

/-- Combining the two: `v ⬝ v = v ⬝ 1`. -/
lemma dotProduct_self_eq_dotProduct_one {m : ℕ} (v : Fin m → ZMod 2) :
    v ⬝ᵥ v = v ⬝ᵥ (fun _ => (1 : ZMod 2)) := by
  rw [dotProduct_self, dotProduct_one_vec]

/-- Symmetric `(A^k)` satisfies `v ᵥ* A^k = A^k *ᵥ v`. -/
lemma vecMul_eq_mulVec_of_symm {m : ℕ}
    (B : Matrix (Fin m) (Fin m) (ZMod 2)) (hB : B.IsSymm) (v : Fin m → ZMod 2) :
    v ᵥ* B = B *ᵥ v := by
  rw [show B = Bᵀ from hB.eq.symm, Matrix.vecMul_transpose]
  rw [hB.eq]

/-- For a symmetric matrix `A` over `ZMod 2` with zero diagonal, the
quadratic form `wᵀ A w = w ⬝ A *ᵥ w` vanishes. -/
lemma quad_form_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (hsymm : A.IsSymm) (hdiag : ∀ i, A i i = 0)
    (w : Fin m → ZMod 2) :
    w ⬝ᵥ A *ᵥ w = 0 := by
  -- Expand as a double sum over (i, j).
  have expand : w ⬝ᵥ A *ᵥ w =
      ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)),
        w p.1 * A p.1 p.2 * w p.2 := by
    simp_rw [dotProduct, mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [← Finset.sum_product']
    rw [Finset.univ_product_univ]
  rw [expand]
  -- Apply the involution `(i,j) ↦ (j,i)` on `univ ×ˢ univ`.
  apply Finset.sum_involution
    (fun (p : Fin m × Fin m) _ => (p.2, p.1))
  · intro p _
    rcases p with ⟨i, j⟩
    have hA : A j i = A i j := hsymm.apply i j
    rw [hA]
    have h2 : (2 : ZMod 2) = 0 := by decide
    have h : w i * A i j * w j + w j * A i j * w i =
           2 * (w i * A i j * w j) := by ring
    rw [h, h2, zero_mul]
  · intro p _ hne hpeq
    apply hne
    -- hpeq : (p.2, p.1) = (p.1, p.2), so p.1 = p.2.
    have hij : p.1 = p.2 := by
      have h1 : p.2 = p.1 := (Prod.mk.inj hpeq).1
      exact h1.symm
    rw [hij, hdiag p.2]
    ring
  · intro p _; exact Finset.mem_univ _
  · intro p _; rfl

/-- Lemma: if `Aⁿ *ᵥ v = 1`, then `v ⬝ᵥ v = 0`, for `n > 0`.

(For `n = 0`, the conclusion need not hold: `A⁰ *ᵥ v = v`, hence `v = 1`,
and then `v ⬝ᵥ v = m mod 2`.) -/
lemma dot_self_zero_of_pow_apply_eq_one {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (hsymm : A.IsSymm) (hdiag : ∀ i, A i i = 0) :
    ∀ n, 0 < n → ∀ v : Fin m → ZMod 2,
      A ^ n *ᵥ v = (fun _ => 1) → v ⬝ᵥ v = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn v hv
    -- v ⬝ v = v ⬝ 1 = v ⬝ (A^n v) = vᵀ A^n v.
    have key : v ⬝ᵥ v = v ⬝ᵥ A ^ n *ᵥ v := by
      rw [dotProduct_self_eq_dotProduct_one, hv]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- n = k + k. n > 0 so k > 0, and k < n.
      have hk_pos : 0 < k := by omega
      have hk_lt : k < n := by omega
      have hpow : A ^ n = A ^ k * A ^ k := by rw [← pow_add, ← hk]
      set w := A ^ k *ᵥ v with hw_def
      have hAk_w : A ^ k *ᵥ w = (fun _ => 1) := by
        rw [hw_def, Matrix.mulVec_mulVec, ← hpow]
        exact hv
      have hw_dot : w ⬝ᵥ w = 0 := ih k hk_lt hk_pos w hAk_w
      -- v ⬝ v = vᵀ A^n v = (A^k v) ⬝ (A^k v) = w ⬝ w = 0
      rw [key, hpow]
      rw [show v ⬝ᵥ (A ^ k * A ^ k) *ᵥ v = w ⬝ᵥ w from ?_]
      · exact hw_dot
      · rw [← Matrix.mulVec_mulVec]
        rw [Matrix.dotProduct_mulVec]
        rw [vecMul_eq_mulVec_of_symm _ (hsymm.pow k)]
    · -- n = 2k + 1. A^n = A^k * A * A^k.
      have hpow : A ^ n = A ^ k * A * A ^ k := by
        rw [hk]
        rw [show 2 * k + 1 = k + 1 + k from by ring]
        rw [pow_add, pow_add, pow_one]
      rw [key, hpow]
      set w := A ^ k *ᵥ v with hw_def
      have step1 : v ⬝ᵥ (A ^ k * A * A ^ k) *ᵥ v = w ⬝ᵥ A *ᵥ w := by
        -- v ⬝ ((A^k * A) * A^k) v = v ⬝ A^k * (A * (A^k v))
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rw [Matrix.dotProduct_mulVec]
        rw [vecMul_eq_mulVec_of_symm _ (hsymm.pow k)]
      rw [step1]
      exact quad_form_zero A hsymm hdiag w

snip end

problem imc2010_p9 (m : ℕ) (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (hsymm : A.IsSymm) (hdiag : ∀ i, A i i = 0) (n : ℕ) (hn : 0 < n)
    (k : Fin m) :
    ∃ i, (A ^ n) i k = 0 := by
  by_contra hcontra
  push Not at hcontra
  -- For all i, (A^n) i k ≠ 0, hence = 1 in ZMod 2.
  have hcol_one : ∀ i, (A ^ n) i k = 1 := by
    intro i
    have h := hcontra i
    -- ZMod 2 has only 0 and 1
    have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
      intro x hx
      fin_cases x
      · exact (hx rfl).elim
      · rfl
    exact this _ h
  -- A^n *ᵥ Pi.single k 1 = 1.
  have hmulVec : A ^ n *ᵥ (Pi.single k (1 : ZMod 2)) = (fun _ => (1 : ZMod 2)) := by
    funext i
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
      rw [hcol_one i, mul_one]
    · intro j _ hjk
      rw [Pi.single_apply, if_neg hjk, mul_zero]
    · intro hk; exact (hk (Finset.mem_univ k)).elim
  have hzero : (Pi.single k (1 : ZMod 2)) ⬝ᵥ (Pi.single k (1 : ZMod 2)) = 0 :=
    dot_self_zero_of_pow_apply_eq_one A hsymm hdiag n hn _ hmulVec
  have hone : (Pi.single k (1 : ZMod 2)) ⬝ᵥ (Pi.single k (1 : ZMod 2)) = 1 := by
    rw [single_dotProduct, Pi.single_eq_same, mul_one]
  rw [hone] at hzero
  exact one_ne_zero hzero

end Imc2010P9
