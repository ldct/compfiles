/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2025, Problem 3

Denote by `S` the set of all real symmetric `2025 × 2025` matrices of rank 1
whose entries take values `-1` or `+1`. Let `A, B ∈ S` be matrices chosen
independently uniformly at random. Find the probability that `A` and `B`
commute, i.e. `AB = BA`.

Answer: `1 / 2^2024`.
-/

namespace Imc2025P3

open Matrix

/-- `n = 2025`. -/
abbrev n : ℕ := 2025

/-- The set `S` of real symmetric `n × n` matrices of rank 1
with entries in `{-1, +1}`. -/
def S : Set (Matrix (Fin n) (Fin n) ℝ) :=
  { A | A.IsSymm ∧ A.rank = 1 ∧ ∀ i j, A i j = 1 ∨ A i j = -1 }

/-- The answer: `1 / 2^(n-1) = 1/2^2024`. -/
noncomputable determine answer : ℝ := 1 / 2 ^ (n - 1)

snip begin

/-- The parameter type: a vector `u : Fin n → ℝ` with `u 0 = 1` and all entries `±1`
is uniquely specified by an element of `Fin (n-1) → Bool` (for the remaining entries),
together with a sign bit in `Bool` for `±A`. -/
abbrev T : Type := Bool × (Fin (n - 1) → Bool)

/-- Convert a Bool to a sign `±1 : ℝ`. -/
@[simp] def bsign (b : Bool) : ℝ := if b then 1 else -1

lemma bsign_ne_zero (b : Bool) : bsign b ≠ 0 := by
  cases b <;> norm_num

lemma bsign_sq (b : Bool) : bsign b * bsign b = 1 := by
  cases b <;> norm_num

lemma bsign_injective : Function.Injective bsign := by
  intro a b h
  cases a <;> cases b <;> simp [bsign] at h ⊢ <;> linarith

/-- The vector associated to `u : Fin (n-1) → Bool`: first coord 1, rest `bsign (u i)`. -/
def vecOf (u : Fin (n - 1) → Bool) : Fin n → ℝ :=
  fun i => if h : i.val = 0 then 1 else bsign (u ⟨i.val - 1, by
    rcases i with ⟨i, hi⟩
    simp at h
    omega⟩)

lemma vecOf_zero (u : Fin (n - 1) → Bool) : vecOf u ⟨0, by norm_num⟩ = 1 := by
  simp [vecOf]

lemma vecOf_entry (u : Fin (n - 1) → Bool) (i : Fin n) :
    vecOf u i = 1 ∨ vecOf u i = -1 := by
  unfold vecOf
  split
  · left; rfl
  · rcases (u _) with _ | _ <;> simp

lemma vecOf_ne_zero_entry (u : Fin (n - 1) → Bool) (i : Fin n) : vecOf u i ≠ 0 := by
  rcases vecOf_entry u i with h | h <;> rw [h] <;> norm_num

/-- The scaled vector. -/
def scaledVec (t : T) : Fin n → ℝ := bsign t.1 • vecOf t.2

/-- The matrix associated to `t : T = Bool × (Fin (n-1) → Bool)`:
    `vecMulVec (bsign t.1 • vecOf t.2) (vecOf t.2)`. -/
def matOf (t : T) : Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec (scaledVec t) (vecOf t.2)

lemma matOf_apply (t : T) (i j : Fin n) :
    matOf t i j = bsign t.1 * (vecOf t.2 i * vecOf t.2 j) := by
  simp only [matOf, scaledVec, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma matOf_isSymm (t : T) : (matOf t).IsSymm := by
  ext i j
  simp [matOf_apply, transpose_apply, mul_comm]

lemma matOf_entries (t : T) (i j : Fin n) :
    matOf t i j = 1 ∨ matOf t i j = -1 := by
  rw [matOf_apply]
  rcases vecOf_entry t.2 i with hi | hi <;>
    rcases vecOf_entry t.2 j with hj | hj <;>
    rw [hi, hj] <;>
    cases t.1 <;> simp

lemma scaledVec_ne_zero (t : T) : scaledVec t ≠ 0 := by
  intro h
  have := congr_fun h ⟨0, by norm_num⟩
  simp [scaledVec] at this
  exact bsign_ne_zero t.1 this

lemma vecOf_ne_zero (u : Fin (n - 1) → Bool) : vecOf u ≠ 0 := by
  intro h
  have := congr_fun h ⟨0, by norm_num⟩
  rw [vecOf_zero] at this
  norm_num at this

/-- If a matrix is nonzero then its rank is positive. -/
lemma rank_pos_of_ne_zero {m k : Type*} [Fintype k] [DecidableEq k] [Fintype m]
    {M : Matrix m k ℝ} (hM : M ≠ 0) : 0 < M.rank := by
  by_contra h
  apply hM
  push Not at h
  have hzero : M.rank = 0 := Nat.le_zero.mp h
  have hrange : LinearMap.range M.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  ext i j
  let e : k → ℝ := fun l => if l = j then 1 else 0
  have hmem : M.mulVec e ∈ LinearMap.range M.mulVecLin := LinearMap.mem_range_self _ _
  rw [hrange, Submodule.mem_bot] at hmem
  have hi : M.mulVec e i = 0 := by rw [hmem]; rfl
  have hsum : ∑ l : k, M i l * e l = 0 := by
    rwa [mulVec, dotProduct] at hi
  have hj : M i j = ∑ l : k, M i l * e l := by
    rw [Finset.sum_eq_single j]
    · simp [e]
    · intros b _ hb
      simp [e, hb]
    · intro hj; exfalso; exact hj (Finset.mem_univ _)
  rw [zero_apply]
  linarith [hj, hsum]

lemma matOf_rank (t : T) : (matOf t).rank = 1 := by
  have hrle : (matOf t).rank ≤ 1 := rank_vecMulVec_le _ _
  have hne : matOf t ≠ 0 :=
    vecMulVec_ne_zero (scaledVec_ne_zero t) (vecOf_ne_zero t.2)
  have hpos : 0 < (matOf t).rank := rank_pos_of_ne_zero hne
  omega

lemma matOf_mem_S (t : T) : matOf t ∈ S := by
  refine ⟨matOf_isSymm t, matOf_rank t, ?_⟩
  intro i j
  exact matOf_entries t i j

/-- The inverse map: extract the Bool sign from A 0 0 and Bool entries from A 0 (i+1) * A 0 0. -/
noncomputable def tOf (A : Matrix (Fin n) (Fin n) ℝ) : T :=
  ( decide (A ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 1),
    fun i => decide (A ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ *
                     A ⟨0, by norm_num⟩ ⟨i.val + 1, by
                       rcases i with ⟨i, hi⟩; omega⟩ = 1) )

/-- Key lemma: for rank-1 matrices with ±1 entries, any 2×2 minor has determinant 0. -/
lemma entry_prod_eq_of_rank_one {A : Matrix (Fin n) (Fin n) ℝ}
    (hrk : A.rank = 1) (i j k l : Fin n) :
    A i k * A j l = A i l * A j k := by
  -- The 2x2 submatrix has rank ≤ 1, so its determinant is 0.
  -- Extract the submatrix B : Matrix (Fin 2) (Fin 2) ℝ.
  set rows : Fin 2 → Fin n := ![i, j] with hrows
  set cols : Fin 2 → Fin n := ![k, l] with hcols
  set B : Matrix (Fin 2) (Fin 2) ℝ := A.submatrix rows cols with hB
  have hBrk : B.rank ≤ 1 := by
    have h1 : (A.submatrix rows cols).rank ≤ A.rank := rank_submatrix_le A rows cols
    rw [hrk] at h1
    rw [hB]; exact h1
  -- det B = A i k * A j l - A i l * A j k.
  -- If det B ≠ 0, then B is invertible, so rank B = 2, contradiction.
  have hdet : B.det = 0 := by
    by_contra hne
    have hUnit : IsUnit B := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hne
    have hrk2 : B.rank = Fintype.card (Fin 2) := rank_of_isUnit _ hUnit
    simp at hrk2
    omega
  rw [Matrix.det_fin_two] at hdet
  have hB00 : B 0 0 = A i k := by simp [B, rows, cols]
  have hB01 : B 0 1 = A i l := by simp [B, rows, cols]
  have hB10 : B 1 0 = A j k := by simp [B, rows, cols]
  have hB11 : B 1 1 = A j l := by simp [B, rows, cols]
  rw [hB00, hB01, hB10, hB11] at hdet
  linarith

lemma entry_sq_one {A : Matrix (Fin n) (Fin n) ℝ}
    (hentry : ∀ i j, A i j = 1 ∨ A i j = -1) (i j : Fin n) :
    A i j * A i j = 1 := by
  rcases hentry i j with h | h <;> rw [h] <;> norm_num

lemma entry_ne_zero {A : Matrix (Fin n) (Fin n) ℝ}
    (hentry : ∀ i j, A i j = 1 ∨ A i j = -1) (i j : Fin n) :
    A i j ≠ 0 := by
  rcases hentry i j with h | h <;> rw [h] <;> norm_num

/-- Helper: if `r = 1` or `r = -1`, then `bsign (decide (r = 1)) = r`. -/
lemma bsign_decide_eq (r : ℝ) (h : r = 1 ∨ r = -1) :
    bsign (decide (r = 1)) = r := by
  rcases h with h | h
  · rw [h]; simp [bsign]
  · rw [h]; simp [bsign]; norm_num

lemma matOf_tOf {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ S) :
    matOf (tOf A) = A := by
  obtain ⟨hsymm, hrk, hentry⟩ := hA
  -- Shorthand for 0 : Fin n.
  set z : Fin n := ⟨0, by norm_num⟩ with hz
  have h00entry : A z z = 1 ∨ A z z = -1 := hentry _ _
  have hsignA : bsign (tOf A).1 = A z z := by
    show bsign (decide (A z z = 1)) = A z z
    exact bsign_decide_eq _ h00entry
  -- The key entry-level equality: A i j = A 0 0 * A 0 i * A 0 j.
  have h00sq : A z z * A z z = 1 := entry_sq_one hentry _ _
  have hAij : ∀ i j : Fin n, A i j = A z z * A z i * A z j := by
    intro i j
    have hcomm := entry_prod_eq_of_rank_one hrk z i z j
    have hsymm' : A i z = A z i := by
      have := congr_fun (congr_fun hsymm i) z
      simp only [transpose_apply] at this
      exact this.symm
    rw [hsymm'] at hcomm
    have heq1 : A z z * (A z z * A i j) = A z z * (A z j * A z i) := by rw [hcomm]
    rw [← mul_assoc, h00sq, one_mul] at heq1
    rw [heq1]; ring
  -- Now compute vecOf (tOf A).2 at i.
  have hv : ∀ i : Fin n, vecOf (tOf A).2 i = A z z * A z i := by
    intro i
    unfold vecOf
    by_cases hi : i.val = 0
    · rw [dif_pos hi]
      have hiz : i = z := Fin.ext hi
      rw [hiz]
      -- Need: 1 = A z z * A z z. Since A z z * A z z = 1.
      rw [h00sq]
    · rw [dif_neg hi]
      -- Need: bsign ((tOf A).2 ⟨i.val - 1, _⟩) = A z z * A z i.
      have hi' : 0 < i.val := Nat.pos_of_ne_zero hi
      -- Look up (tOf A).2 at that index.
      show bsign (decide (A z z *
          A z ⟨((⟨i.val - 1, _⟩ : Fin (n-1)) : Fin (n-1)).val + 1, _⟩ = 1)) = A z z * A z i
      -- The Fin index is i:
      have hidx_eq : (⟨i.val - 1 + 1, by have := i.isLt; omega⟩ : Fin n) = i := by
        apply Fin.ext; dsimp; omega
      have hentry_prod : A z z * A z i = 1 ∨ A z z * A z i = -1 := by
        rcases h00entry with h' | h' <;>
          rcases hentry z i with h'' | h'' <;>
          rw [h', h''] <;> norm_num
      -- Replace the index using hidx_eq by rewriting the goal.
      have heq : A z ⟨i.val - 1 + 1, by have := i.isLt; omega⟩ = A z i := by
        congr 1
      -- Rewrite using heq.
      have heq2 : A z z * A z ⟨i.val - 1 + 1, by have := i.isLt; omega⟩ = A z z * A z i := by
        rw [heq]
      conv_lhs => rw [heq2]
      exact bsign_decide_eq _ hentry_prod
  ext i j
  rw [matOf_apply, hsignA, hv i, hv j]
  -- Goal: A z z * (A z z * A z i * (A z z * A z j)) = A i j
  rw [hAij i j]
  -- Goal: A z z * (A z z * A z i * (A z z * A z j)) = A z z * A z i * A z j
  have h_expand : A z z * (A z z * A z i * (A z z * A z j)) =
                  (A z z * A z z) * (A z z * A z i * A z j) := by ring
  rw [h_expand, h00sq, one_mul]

lemma decide_bsign_eq (b : Bool) : decide (bsign b = 1) = b := by
  cases b
  · simp [bsign]; norm_num
  · simp [bsign]

lemma tOf_matOf (t : T) : tOf (matOf t) = t := by
  set z : Fin n := ⟨0, by norm_num⟩ with hz
  have h1 : (tOf (matOf t)).1 = t.1 := by
    show decide (matOf t z z = 1) = t.1
    rw [matOf_apply, vecOf_zero]
    simp only [mul_one]
    exact decide_bsign_eq t.1
  have h2 : (tOf (matOf t)).2 = t.2 := by
    funext i
    show decide (matOf t z z *
        matOf t z ⟨i.val + 1, by rcases i with ⟨iv, hi⟩; simp; omega⟩ = 1) = t.2 i
    rw [matOf_apply, matOf_apply, vecOf_zero]
    have hvi : vecOf t.2 ⟨i.val + 1, by rcases i with ⟨iv, hi⟩; simp; omega⟩ = bsign (t.2 i) := by
      unfold vecOf
      rw [dif_neg (by simp : ¬(i.val + 1) = 0)]
      congr
    rw [hvi]
    -- Goal: decide (bsign t.1 * (1 * 1) * (bsign t.1 * (1 * bsign (t.2 i))) = 1) = t.2 i
    have hsq := bsign_sq t.1
    have heq : bsign t.1 * (1 * 1) * (bsign t.1 * (1 * bsign (t.2 i))) = bsign (t.2 i) := by
      have : bsign t.1 * (1 * 1) * (bsign t.1 * (1 * bsign (t.2 i))) =
             (bsign t.1 * bsign t.1) * bsign (t.2 i) := by ring
      rw [this, hsq, one_mul]
    rw [heq]
    exact decide_bsign_eq (t.2 i)
  exact Prod.ext h1 h2

/-- The equiv between `T` and `S`. -/
noncomputable def tEquiv [Fintype S] : T ≃ S where
  toFun t := ⟨matOf t, matOf_mem_S t⟩
  invFun A := tOf A.1
  left_inv := tOf_matOf
  right_inv := fun A => Subtype.ext (matOf_tOf A.2)

lemma card_T : Fintype.card T = 2 ^ n := by
  show Fintype.card (Bool × (Fin (n - 1) → Bool)) = 2 ^ n
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- 2 * 2 ^ (n-1) = 2 ^ n
  show 2 * 2 ^ (n - 1) = 2 ^ n
  have hn : n = (n - 1) + 1 := by rfl
  rw [hn]
  rw [pow_succ]
  ring

lemma card_S [Fintype S] : Fintype.card S = 2 ^ n := by
  have heq : Fintype.card S = Fintype.card T := Fintype.card_congr tEquiv.symm
  rw [heq, card_T]

/-- `n = 2025` is odd. -/
lemma n_odd : Odd n := ⟨1012, by decide⟩

/-- Sum of products of ±1 values, over an odd-cardinality set, is nonzero.
More specifically: `∑ f i = 2*k - |I|` where `k = |{i : f i = 1}|`. -/
lemma sum_pm_one_ne_zero_of_odd {I : Type*} [Fintype I] [DecidableEq I]
    (hodd : Odd (Fintype.card I)) (f : I → ℝ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    ∑ i, f i ≠ 0 := by
  classical
  set pos := (Finset.univ : Finset I).filter (fun i => f i = 1) with hpos_def
  set k := pos.card with hk_def
  have hk_le : k ≤ Fintype.card I := by
    rw [hk_def, hpos_def]
    exact Finset.card_filter_le _ _
  have hsum : ∑ i, f i = (2 * k : ℝ) - Fintype.card I := by
    have : (∑ i, f i) =
           ∑ i ∈ pos, f i + ∑ i ∈ (Finset.univ : Finset I).filter (fun i => ¬(f i = 1)), f i :=
      (Finset.sum_filter_add_sum_filter_not _ (fun i => f i = 1) _).symm
    rw [this]
    have h_pos : ∑ i ∈ pos, f i = (k : ℝ) := by
      rw [hk_def]
      rw [show (↑pos.card : ℝ) = ∑ _ ∈ pos, (1 : ℝ) by simp]
      apply Finset.sum_congr rfl
      intros i hi
      simp [pos] at hi
      exact hi
    have h_neg : ∑ i ∈ (Finset.univ : Finset I).filter (fun i => ¬(f i = 1)), f i =
                 -((Fintype.card I : ℝ) - k) := by
      have hcard :
          ((Finset.univ : Finset I).filter (fun i => ¬(f i = 1))).card = Fintype.card I - k := by
        have hh : ((Finset.univ : Finset I).filter (fun i => f i = 1)).card +
                  ((Finset.univ : Finset I).filter (fun i => ¬(f i = 1))).card =
                  (Finset.univ : Finset I).card :=
          Finset.card_filter_add_card_filter_not _
        rw [Finset.card_univ] at hh
        show ((Finset.univ : Finset I).filter (fun i => ¬(f i = 1))).card = Fintype.card I - k
        have hk_eq : k = ((Finset.univ : Finset I).filter (fun i => f i = 1)).card := hk_def
        omega
      have hstep : ∑ _ ∈ (Finset.univ : Finset I).filter (fun i => ¬(f i = 1)), (-1 : ℝ)
                 = -((Fintype.card I : ℝ) - k) := by
        rw [Finset.sum_const, hcard]
        -- Goal: (Fintype.card I - k) • -1 = -(↑(Fintype.card I) - ↑k).
        -- Convert ℕ smul to ℝ mul.
        rw [nsmul_eq_mul, Nat.cast_sub hk_le]
        ring
      rw [← hstep]
      apply Finset.sum_congr rfl
      intros i hi
      simp at hi
      rcases hf i with h' | h'
      · exact absurd h' hi
      · exact h'
    rw [h_pos, h_neg]
    ring
  rw [hsum]
  intro heq
  have : (2 * k : ℝ) = Fintype.card I := by linarith
  have hn : (Fintype.card I : ℤ) = 2 * k := by exact_mod_cast this.symm
  rcases hodd with ⟨m, hm⟩
  rw [hm] at hn
  omega

lemma sum_vecOf_ne_zero (uA uB : Fin (n - 1) → Bool) :
    ∑ i, vecOf uA i * vecOf uB i ≠ 0 := by
  apply sum_pm_one_ne_zero_of_odd
  · rw [Fintype.card_fin]; exact n_odd
  · intro i
    rcases vecOf_entry uA i with hA | hA <;>
      rcases vecOf_entry uB i with hB | hB <;>
      rw [hA, hB] <;> norm_num

/-- AB = BA iff after projecting to T, the u vectors match.
Given A = matOf (εA, uA) and B = matOf (εB, uB), AB = BA iff uA = uB. -/
lemma matOf_commute_iff (tA tB : T) :
    matOf tA * matOf tB = matOf tB * matOf tA ↔ tA.2 = tB.2 := by
  constructor
  · intro h
    set z : Fin n := ⟨0, by norm_num⟩ with hz
    have key : ∀ i, (matOf tA * matOf tB) i z = (matOf tB * matOf tA) i z := by
      intro i; rw [h]
    have hAB : ∀ i, (matOf tA * matOf tB) i z =
        bsign tA.1 * bsign tB.1 * (∑ k, vecOf tA.2 k * vecOf tB.2 k) * vecOf tA.2 i := by
      intro i
      simp only [Matrix.mul_apply, matOf_apply]
      have hvz : vecOf tB.2 z = 1 := vecOf_zero tB.2
      have : ∀ x, bsign tA.1 * (vecOf tA.2 i * vecOf tA.2 x) *
                  (bsign tB.1 * (vecOf tB.2 x * vecOf tB.2 z)) =
            (bsign tA.1 * bsign tB.1 * vecOf tA.2 i) *
                  (vecOf tA.2 x * vecOf tB.2 x) := by
        intro x; rw [hvz]; ring
      rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum]
      ring
    have hBA : ∀ i, (matOf tB * matOf tA) i z =
        bsign tA.1 * bsign tB.1 * (∑ k, vecOf tA.2 k * vecOf tB.2 k) * vecOf tB.2 i := by
      intro i
      simp only [Matrix.mul_apply, matOf_apply]
      have hvz : vecOf tA.2 z = 1 := vecOf_zero tA.2
      have : ∀ x, bsign tB.1 * (vecOf tB.2 i * vecOf tB.2 x) *
                  (bsign tA.1 * (vecOf tA.2 x * vecOf tA.2 z)) =
            (bsign tA.1 * bsign tB.1 * vecOf tB.2 i) *
                  (vecOf tA.2 x * vecOf tB.2 x) := by
        intro x; rw [hvz]; ring
      rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum]
      ring
    have hs_ne : bsign tA.1 * bsign tB.1 * (∑ k, vecOf tA.2 k * vecOf tB.2 k) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (bsign_ne_zero _) (bsign_ne_zero _))
        (sum_vecOf_ne_zero _ _)
    have hv : ∀ i, vecOf tA.2 i = vecOf tB.2 i := by
      intro i
      have := key i
      rw [hAB, hBA] at this
      exact mul_left_cancel₀ hs_ne this
    funext i
    have hi_lt : i.val + 1 < n := by rcases i with ⟨iv, hi⟩; simp at hi; omega
    have hi1 : vecOf tA.2 ⟨i.val + 1, hi_lt⟩ = vecOf tB.2 ⟨i.val + 1, hi_lt⟩ := hv _
    unfold vecOf at hi1
    rw [dif_neg (by simp : ¬(i.val + 1) = 0), dif_neg (by simp : ¬(i.val + 1) = 0)] at hi1
    have hAi : (⟨(⟨i.val + 1, hi_lt⟩ : Fin n).val - 1, by
                rcases i with ⟨iv, hi⟩; simp at hi; simp; omega⟩ : Fin (n - 1)) = i := by
      apply Fin.ext
      show i.val + 1 - 1 = i.val
      omega
    rw [hAi] at hi1
    exact bsign_injective hi1
  · rintro h
    -- tA.2 = tB.2 so vecOf tA.2 = vecOf tB.2.
    -- Then matOf tA * matOf tB and matOf tB * matOf tA both equal
    -- bsign tA.1 * bsign tB.1 * ⟨v,v⟩ * vecMulVec v v.
    ext i j
    simp only [Matrix.mul_apply, matOf_apply]
    rw [h]
    -- Both sides: ∑ k, (bsign tA.1 * (vecOf tB.2 i * vecOf tB.2 k)) * (bsign tB.1 * (vecOf tB.2 k * vecOf tB.2 j))
    -- vs the same. They are equal.
    apply Finset.sum_congr rfl
    intros k _; ring

/-- Equivalence between commuting S-pairs and T-pairs with equal u-components. -/
noncomputable def commuteEquiv [Fintype S] :
    {p : T × T // p.1.2 = p.2.2} ≃
    {p : S × S // (p.1.1 : Matrix (Fin n) (Fin n) ℝ) * p.2.1 = p.2.1 * p.1.1} where
  toFun p := ⟨(tEquiv p.1.1, tEquiv p.1.2), by
    have hp := p.2
    show (tEquiv p.1.1).1 * (tEquiv p.1.2).1 = (tEquiv p.1.2).1 * (tEquiv p.1.1).1
    show matOf p.1.1 * matOf p.1.2 = matOf p.1.2 * matOf p.1.1
    rw [matOf_commute_iff]; exact hp⟩
  invFun p := ⟨(tEquiv.symm p.1.1, tEquiv.symm p.1.2), by
    have hp := p.2
    have hmA : matOf (tEquiv.symm p.1.1) = p.1.1.1 := by
      exact congr_arg Subtype.val (Equiv.apply_symm_apply tEquiv _)
    have hmB : matOf (tEquiv.symm p.1.2) = p.1.2.1 := by
      exact congr_arg Subtype.val (Equiv.apply_symm_apply tEquiv _)
    rw [← matOf_commute_iff, hmA, hmB]; exact hp⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, _⟩
    ext : 2
    · exact Equiv.symm_apply_apply _ _
    · exact Equiv.symm_apply_apply _ _
  right_inv := by
    rintro ⟨⟨A, B⟩, _⟩
    ext : 2
    · exact Equiv.apply_symm_apply _ _
    · exact Equiv.apply_symm_apply _ _

lemma count_commute_eq_count_T [Fintype S] :
    (Finset.univ.filter (fun p : S × S =>
        (p.1.1 : Matrix (Fin n) (Fin n) ℝ) * p.2.1 = p.2.1 * p.1.1)).card =
    (Finset.univ.filter (fun p : T × T => p.1.2 = p.2.2)).card := by
  classical
  have h1 : (Finset.univ.filter (fun p : S × S =>
      (p.1.1 : Matrix (Fin n) (Fin n) ℝ) * p.2.1 = p.2.1 * p.1.1)).card =
      Fintype.card {p : S × S // (p.1.1 : Matrix (Fin n) (Fin n) ℝ) * p.2.1 = p.2.1 * p.1.1} := by
    rw [Fintype.card_subtype]
  have h2 : (Finset.univ.filter (fun p : T × T => p.1.2 = p.2.2)).card =
      Fintype.card {p : T × T // p.1.2 = p.2.2} := by
    rw [Fintype.card_subtype]
  rw [h1, h2]
  exact (Fintype.card_congr commuteEquiv).symm

/-- Equivalence between pairs (tA, tB) with tA.2 = tB.2 and triples (εA, εB, v). -/
def tPairEquiv :
    {p : T × T // p.1.2 = p.2.2} ≃ (Bool × Bool × (Fin (n - 1) → Bool)) where
  toFun p := (p.1.1.1, p.1.2.1, p.1.1.2)
  invFun q := ⟨((q.1, q.2.2), (q.2.1, q.2.2)), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨εA, vA⟩, εB, vB⟩, hp⟩
    simp only at hp
    subst hp
    rfl
  right_inv := by
    rintro ⟨εA, εB, v⟩; rfl

lemma count_T_pairs : (Finset.univ.filter (fun p : T × T => p.1.2 = p.2.2)).card = 2 ^ (n + 1) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr tPairEquiv]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  show 2 * (2 * 2 ^ (n - 1)) = 2 ^ (n + 1)
  have hrw : n + 1 = (n - 1) + 2 := by decide
  rw [hrw, pow_add]
  ring

snip end

/-- The problem statement: the probability that two independently uniformly random
matrices from `S` commute equals `answer`.

We express the problem as: the ratio of (number of commuting pairs) to
`|S|^2` equals `answer`, assuming `S` is finite (which we encode in the
hypothesis using `Fintype`).
-/
problem imc2025_p3
    [Fintype S] (hSne : Nonempty S) :
    ((Finset.univ.filter (fun p : S × S =>
        (p.1.1 : Matrix (Fin n) (Fin n) ℝ) * p.2.1 = p.2.1 * p.1.1)).card : ℝ) /
      ((Fintype.card S : ℝ) ^ 2) = answer := by
  classical
  rw [count_commute_eq_count_T, count_T_pairs, card_S]
  -- Goal: ((2^(n+1) : ℕ) : ℝ) / ((2^n : ℕ) : ℝ)^2 = answer = 1 / 2^(n-1).
  unfold answer
  -- Use: 2^(n+1) = 2 * 2^n and 2^n = 2 * 2^(n-1).
  have h2 : ((2 ^ n : ℕ) : ℝ) = 2 * 2 ^ (n - 1) := by
    push_cast
    have heq : n = (n - 1) + 1 := rfl
    rw [show (2 : ℝ) ^ n = 2 ^ ((n - 1) + 1) by rw [← heq]]
    rw [pow_succ]; ring
  have h1 : ((2 ^ (n + 1) : ℕ) : ℝ) = 4 * 2 ^ (n - 1) := by
    push_cast
    have h_np1 : n + 1 = (n - 1) + 2 := by decide
    rw [show (2 : ℝ) ^ (n + 1) = 2 ^ ((n - 1) + 2) by rw [← h_np1]]
    rw [pow_add]; ring
  rw [h1, h2]
  have hpow_ne : (2 : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

end Imc2025P3
