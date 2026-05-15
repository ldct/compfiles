/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra, .Combinatorics] }

/-!
# International Mathematical Competition 2021, Problem 8

Let `n` be a positive integer. At most how many distinct unit vectors can be
selected in `ℝⁿ` such that from any three of them, at least two are orthogonal?

Answer: `2n`.
-/

namespace Imc2021P8

/-- The maximum number of unit vectors in ℝⁿ such that every 3 contain
an orthogonal pair. Answer: `2n`. -/
determine answer (n : ℕ) : ℕ := 2 * n

/-- The collection of `2n` unit vectors: the standard basis and its negation.
Indexed by `Fin (2 * n)`: the first `n` indices give `e_i`, the last `n` give `-e_i`. -/
noncomputable def example_vec (n : ℕ) : Fin (2 * n) → EuclideanSpace ℝ (Fin n) := fun k =>
  if h : k.val < n then
    EuclideanSpace.single ⟨k.val, h⟩ (1 : ℝ)
  else
    -EuclideanSpace.single ⟨k.val - n, by
      have hkn : n ≤ k.val := Nat.le_of_not_lt h
      have hk2 : k.val < 2 * n := k.isLt
      omega⟩ (1 : ℝ)

snip begin

/-- Inner product of `EuclideanSpace.single i 1` with `EuclideanSpace.single j 1`
is `1` if `i = j` and `0` otherwise. -/
lemma inner_single_single {n : ℕ} (i j : Fin n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      if i = j then (1 : ℝ) else 0 := by
  have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ)
    (EuclideanSpace.single j (1 : ℝ))
  simp [PiLp.single_apply] at h
  exact h

/-- Norm of `EuclideanSpace.single i 1` is `1`. -/
lemma norm_single_one {n : ℕ} (i : Fin n) :
    ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  simp

/-- For indices in `Fin (2 * n)`, a map `k ↦ if k.val < n then k.val else k.val - n`
takes at most two values equal to any given `m : Fin n`. -/
lemma three_indices_pigeonhole {n : ℕ} (a b c : Fin (2 * n))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ (x y : Fin (2 * n)), x ≠ y ∧
      (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧
      (if x.val < n then x.val else x.val - n) ≠
        (if y.val < n then y.val else y.val - n) := by
  -- Map each index to its "coordinate class"
  set fa := if a.val < n then a.val else a.val - n with hfa
  set fb := if b.val < n then b.val else b.val - n with hfb
  set fc := if c.val < n then c.val else c.val - n with hfc
  -- Among three values, at least two must be distinct (else all three indices
  -- would share a coordinate class, but each class has only 2 indices).
  by_cases h1 : fa = fb
  · by_cases h2 : fb = fc
    · -- fa = fb = fc. Then a, b, c are three distinct indices mapping to the
      -- same coordinate class. But each class has at most 2 preimages.
      exfalso
      -- Show that for each coordinate class m < n, there are exactly two indices
      -- in Fin (2n): m and m+n.
      have ha_in : a.val = fa ∨ a.val = fa + n := by
        by_cases hh : a.val < n
        · left; simp [hfa, hh]
        · right
          have hkn : n ≤ a.val := Nat.le_of_not_lt hh
          have : fa = a.val - n := by simp [hfa, hh]
          omega
      have hb_in : b.val = fb ∨ b.val = fb + n := by
        by_cases hh : b.val < n
        · left; simp [hfb, hh]
        · right
          have hkn : n ≤ b.val := Nat.le_of_not_lt hh
          have : fb = b.val - n := by simp [hfb, hh]
          omega
      have hc_in : c.val = fc ∨ c.val = fc + n := by
        by_cases hh : c.val < n
        · left; simp [hfc, hh]
        · right
          have hkn : n ≤ c.val := Nat.le_of_not_lt hh
          have : fc = c.val - n := by simp [hfc, hh]
          omega
      -- fa = fb = fc, so each of a.val, b.val, c.val ∈ {fa, fa+n}.
      rw [← h1] at hb_in
      rw [← h2, ← h1] at hc_in
      -- Three distinct natural numbers in {fa, fa+n}: impossible.
      have hab_val : a.val ≠ b.val := fun h => hab (Fin.ext h)
      have hbc_val : b.val ≠ c.val := fun h => hbc (Fin.ext h)
      have hac_val : a.val ≠ c.val := fun h => hac (Fin.ext h)
      rcases ha_in with ha | ha <;> rcases hb_in with hb | hb <;>
        rcases hc_in with hc | hc <;> omega
    · -- fb ≠ fc, use b and c
      refine ⟨b, c, hbc, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), ?_⟩
      exact h2
  · -- fa ≠ fb, use a and b
    exact ⟨a, b, hab, Or.inl rfl, Or.inr (Or.inl rfl), h1⟩

/-- For the `example_vec` construction, indices with different coordinate
classes give orthogonal vectors. -/
lemma example_vec_orthogonal_of_ne_class {n : ℕ} (a b : Fin (2 * n))
    (h : (if a.val < n then a.val else a.val - n) ≠
         (if b.val < n then b.val else b.val - n)) :
    inner ℝ (example_vec n a) (example_vec n b) = (0 : ℝ) := by
  unfold example_vec
  -- Case split on a.val < n and b.val < n
  split_ifs with ha hb hb
  · -- e_{a.val} · e_{b.val} where the classes differ, so indices differ.
    rw [inner_single_single]
    split_ifs with hab
    · exfalso; apply h
      simp [ha, hb]
      exact Fin.mk.inj_iff.mp hab
    · rfl
  · -- e_a · (-e_{b-n})
    rw [inner_neg_right, inner_single_single]
    split_ifs with hab
    · exfalso; apply h
      simp [ha, hb]
      have := Fin.mk.inj_iff.mp hab
      omega
    · simp
  · -- (-e_{a-n}) · e_b
    rw [inner_neg_left, inner_single_single]
    split_ifs with hab
    · exfalso; apply h
      simp [ha, hb]
      have := Fin.mk.inj_iff.mp hab
      omega
    · simp
  · -- (-e_{a-n}) · (-e_{b-n})
    rw [inner_neg_left, inner_neg_right, inner_single_single]
    split_ifs with hab
    · exfalso; apply h
      simp [ha, hb]
      have := Fin.mk.inj_iff.mp hab
      omega
    · simp

/-- The example_vec construction gives unit vectors. -/
lemma example_vec_norm_one {n : ℕ} (k : Fin (2 * n)) :
    ‖example_vec n k‖ = 1 := by
  unfold example_vec
  split_ifs <;> simp

/-- The example_vec construction is injective. -/
lemma example_vec_injective {n : ℕ} :
    Function.Injective (example_vec n) := by
  intro a b hab
  unfold example_vec at hab
  -- Case split on a.val < n and b.val < n
  split_ifs at hab with ha hb hb
  · -- Both single_i = single_j ⇒ i = j
    have heq : (EuclideanSpace.single (⟨a.val, ha⟩ : Fin n) (1 : ℝ)) (⟨a.val, ha⟩) =
           (EuclideanSpace.single (⟨b.val, hb⟩ : Fin n) (1 : ℝ)) (⟨a.val, ha⟩) := by
      rw [hab]
    simp [PiLp.single_apply] at heq
    apply Fin.ext
    omega
  · -- single_i = -single_j ⇒ 1 = -something at some index: contradiction
    exfalso
    have : (EuclideanSpace.single (⟨a.val, ha⟩ : Fin n) (1 : ℝ)) (⟨a.val, ha⟩) =
           (-EuclideanSpace.single (⟨b.val - n, by
              have hkn : n ≤ b.val := Nat.le_of_not_lt hb
              have hk2 : b.val < 2 * n := b.isLt
              omega⟩ : Fin n) (1 : ℝ)) (⟨a.val, ha⟩) := by
      rw [hab]
    simp [PiLp.single_apply] at this
    split_ifs at this
    · linarith
    · linarith
  · exfalso
    have : (-EuclideanSpace.single (⟨a.val - n, by
              have hkn : n ≤ a.val := Nat.le_of_not_lt ha
              have hk2 : a.val < 2 * n := a.isLt
              omega⟩ : Fin n) (1 : ℝ)) (⟨a.val - n, by
              have hkn : n ≤ a.val := Nat.le_of_not_lt ha
              have hk2 : a.val < 2 * n := a.isLt
              omega⟩) =
           (EuclideanSpace.single (⟨b.val, hb⟩ : Fin n) (1 : ℝ)) (⟨a.val - n, by
              have hkn : n ≤ a.val := Nat.le_of_not_lt ha
              have hk2 : a.val < 2 * n := a.isLt
              omega⟩) := by
      rw [hab]
    simp [PiLp.single_apply] at this
    split_ifs at this
    · linarith
    · linarith
  · -- Both negatives: -single_i = -single_j ⇒ i = j
    have hkn_a : n ≤ a.val := Nat.le_of_not_lt ha
    have hkn_b : n ≤ b.val := Nat.le_of_not_lt hb
    have hk2_a : a.val < 2 * n := a.isLt
    have hk2_b : b.val < 2 * n := b.isLt
    have hab' : EuclideanSpace.single (⟨a.val - n, by omega⟩ : Fin n) (1 : ℝ) =
                EuclideanSpace.single (⟨b.val - n, by omega⟩ : Fin n) (1 : ℝ) := by
      have := neg_injective hab
      exact this
    have heq : (EuclideanSpace.single (⟨a.val - n, by omega⟩ : Fin n) (1 : ℝ)) (⟨a.val - n, by omega⟩) =
           (EuclideanSpace.single (⟨b.val - n, by omega⟩ : Fin n) (1 : ℝ)) (⟨a.val - n, by omega⟩) := by
      rw [hab']
    simp [PiLp.single_apply] at heq
    apply Fin.ext
    omega

/-- Inner product of two real numbers. -/
private lemma real_inner_real_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  simp [inner, mul_comm]

/-- Real inner product on `EuclideanSpace ℝ (Fin n)` as a sum of products. -/
lemma real_inner_eq_sum {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, x k * y k := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact real_inner_real_eq_mul _ _

/-- Squared norm in `EuclideanSpace ℝ (Fin n)` equals self inner-product. -/
lemma real_inner_self_eq_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x x = ‖x‖ ^ 2 := by
  rw [real_inner_eq_sum, EuclideanSpace.real_norm_sq_eq]
  congr 1; ext k; ring

/-- The upper bound: if `v : Fin N → EuclideanSpace ℝ (Fin n)` are unit vectors
satisfying that any three contain an orthogonal pair, then `N ≤ 2n`. -/
theorem imc2021_p8_upper_bound (n : ℕ) (_hn : 0 < n) (N : ℕ)
    (v : Fin N → EuclideanSpace ℝ (Fin n))
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hortho : ∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
        inner ℝ (v i) (v j) = (0 : ℝ) ∨
        inner ℝ (v j) (v k) = (0 : ℝ) ∨
        inner ℝ (v i) (v k) = (0 : ℝ)) :
    N ≤ 2 * n := by
  -- Define A i j = ⟨v i, v j⟩.
  let A : Fin N → Fin N → ℝ := fun i j => inner ℝ (v i) (v j)
  have hA_diag : ∀ i, A i i = 1 := by
    intro i
    show inner ℝ (v i) (v i) = 1
    rw [real_inner_self_eq_norm_sq, hnorm]; ring
  have hA_symm : ∀ i j, A i j = A j i := fun i j => real_inner_comm _ _
  have hA_triple : ∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
      A i j * A j k * A k i = 0 := by
    intro i j k hij hjk hik
    rcases hortho i j k hij hjk hik with h | h | h
    · show inner ℝ (v i) (v j) * _ * _ = 0
      rw [h]; ring
    · show _ * inner ℝ (v j) (v k) * _ = 0
      rw [h]; ring
    · show _ * _ * inner ℝ (v k) (v i) = 0
      rw [show inner ℝ (v k) (v i) = inner ℝ (v i) (v k) from real_inner_comm _ _, h]
      ring
  -- T2 = ∑_{i,j} A i j ^ 2
  let T2 := ∑ i, ∑ j, (A i j)^2
  -- T3 = ∑_{i,j,k} A i j * A j k * A k i
  let T3 := ∑ i, ∑ j, ∑ k, A i j * A j k * A k i
  -- Step 1: T3 = 3 T2 - 2 N.
  have hT3_eq : T3 = 3 * T2 - 2 * N := by
    -- Express T3 by splitting on equality patterns.
    have key : T3 =
        N + 3 * ∑ i, ∑ k, (if i ≠ k then (A i k)^2 else 0) := by
      show (∑ i, ∑ j, ∑ k, A i j * A j k * A k i) = _
      -- Rewrite the inner sum-over-k by splitting cases.
      rw [show (∑ i : Fin N, ∑ j, ∑ k, A i j * A j k * A k i) =
          ∑ i, ∑ j, ((if i = j then ∑ k, A i j * A j k * A k i else 0) +
                     (if i ≠ j then ∑ k, A i j * A j k * A k i else 0)) by
        congr 1; ext i; congr 1; ext j
        by_cases h : i = j <;> simp [h]]
      simp_rw [Finset.sum_add_distrib]
      -- The first piece: when i = j we have A i i * A i k * A k i = (A i k)^2.
      have piece1 : ∀ i : Fin N,
          (∑ j, if i = j then ∑ k, A i j * A j k * A k i else 0) =
          ∑ k, (A i k)^2 := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp [hA_diag]
          apply Finset.sum_congr rfl
          intro k _
          have : A k i = A i k := hA_symm k i
          rw [this]; ring
        · intro j _ hij; simp [Ne.symm hij]
        · intro h; exact absurd (Finset.mem_univ _) h
      -- The second piece: when i ≠ j, the sum over k is what we need.
      -- Most terms in ∑ k, A i j * A j k * A k i are zero (when k ≠ i, k ≠ j by hA_triple).
      -- Only k = i and k = j contribute.
      have piece2_k : ∀ i j : Fin N, i ≠ j →
          (∑ k, A i j * A j k * A k i) = 2 * (A i j)^2 := by
        intro i j hij
        have hsplit : ∀ k : Fin N,
            A i j * A j k * A k i =
              (if k = i then A i j * A j i * A i i else 0) +
              (if k = j then A i j * A j j * A j i else 0) +
              (if k ≠ i ∧ k ≠ j then A i j * A j k * A k i else 0) := by
          intro k
          by_cases h1 : k = i
          · subst h1
            have hkj : k ≠ j := hij
            simp [hkj]
          · by_cases h2 : k = j
            · subst h2
              have hki : k ≠ i := Ne.symm hij
              simp [hki]
            · simp [h1, h2]
        rw [Finset.sum_congr rfl (fun k _ => hsplit k)]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j]
        simp [hA_diag]
        have hzero : (∑ k, if k ≠ i ∧ k ≠ j then A i j * A j k * A k i else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          split_ifs with hcond
          · exact hA_triple i j k hij hcond.2.symm hcond.1.symm
          · rfl
        rw [hzero]
        have hji : A j i = A i j := hA_symm j i
        rw [hji]; ring
      have piece2 : ∀ i : Fin N,
          (∑ j, if i ≠ j then ∑ k, A i j * A j k * A k i else 0) =
          ∑ j, if i ≠ j then 2 * (A i j)^2 else 0 := by
        intro i
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · simp [hij]
        · simp [hij, piece2_k i j hij]
      simp_rw [piece1, piece2]
      -- Now: ∑ i, ∑ k, (A i k)^2 + ∑ i, ∑ j, (if i ≠ j then 2 (A i j)^2 else 0) = N + 3 ∑ i ∑ k (if i ≠ k then ...)
      have hp2 : ∀ i : Fin N, (∑ j, if i ≠ j then 2 * (A i j)^2 else 0) =
          2 * ∑ j, if i ≠ j then (A i j)^2 else 0 := by
        intro i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      simp_rw [hp2]
      rw [show (∑ i : Fin N, ∑ k, (A i k)^2) =
            ∑ i, ((A i i)^2 + ∑ k, if i ≠ k then (A i k)^2 else 0) by
          congr 1; ext i
          rw [show (∑ k : Fin N, (A i k)^2) =
            ∑ k, ((if i = k then (A i k)^2 else 0) + (if i ≠ k then (A i k)^2 else 0)) by
            congr 1; ext k; by_cases h : i = k <;> simp [h]]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp]
      simp_rw [hA_diag]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, one_pow]
      rw [← Finset.mul_sum]
      ring
    rw [key]
    show N + 3 * ∑ i, ∑ k, (if i ≠ k then (A i k)^2 else 0) = 3 * T2 - 2 * (N : ℝ)
    -- Need: ∑ i ∑ k (if i ≠ k then (A i k)^2 else 0) = T2 - N.
    have hT2_split : T2 = N + ∑ i, ∑ k, (if i ≠ k then (A i k)^2 else 0) := by
      show (∑ i, ∑ j, (A i j)^2) = _
      rw [show (∑ i : Fin N, ∑ j, (A i j)^2) =
            ∑ i, ((A i i)^2 + ∑ k, if i ≠ k then (A i k)^2 else 0) by
          congr 1; ext i
          rw [show (∑ k : Fin N, (A i k)^2) =
            ∑ k, ((if i = k then (A i k)^2 else 0) + (if i ≠ k then (A i k)^2 else 0)) by
            congr 1; ext k; by_cases h : i = k <;> simp [h]]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp]
      simp_rw [hA_diag]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, one_pow]
    linarith [hT2_split]
  -- Step 2: T3 ≥ 4 T2 - 4 N (from sum of squared norms).
  -- Define w_i = ∑ j, A i j • v j.
  let w : Fin N → EuclideanSpace ℝ (Fin n) := fun i => ∑ j, A i j • v j
  -- Compute ‖w i‖² = ∑_{j,k} A i j A i k A j k.
  have hwi_sq : ∀ i, ‖w i‖^2 = ∑ j, ∑ k, A i j * A i k * A j k := by
    intro i
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (∑ j, A i j • v j) (∑ j, A i j • v j) = _
    rw [sum_inner]
    apply Finset.sum_congr rfl; intro j _
    rw [inner_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [real_inner_smul_left, real_inner_smul_right]
    show A i j * (A i k * inner ℝ (v j) (v k)) = A i j * A i k * A j k
    show A i j * (A i k * (A j k)) = _
    ring
  -- Compute ⟨v i, w i⟩ = ∑ j, (A i j)^2.
  have hvi_wi : ∀ i, inner ℝ (v i) (w i) = ∑ j, (A i j)^2 := by
    intro i
    show inner ℝ (v i) (∑ j, A i j • v j) = _
    rw [inner_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [real_inner_smul_right]
    show A i j * inner ℝ (v i) (v j) = (A i j)^2
    show A i j * A i j = _
    ring
  -- Sum identity: ∑ i, ‖w i - 2 • v i‖² = ∑ i ‖w i‖² - 4 ∑ i ⟨v i, w i⟩ + 4 N
  have hexpand : ∀ i, ‖w i - (2 : ℝ) • v i‖^2 =
      ‖w i‖^2 - 4 * inner ℝ (v i) (w i) + 4 * ‖v i‖^2 := by
    intro i
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_right]
    have hcomm : inner ℝ (v i) (w i) = inner ℝ (w i) (v i) := real_inner_comm _ _
    linarith [hcomm]
  -- ∑ i ‖w i‖² = T3.
  have hsum_w_sq : ∑ i, ‖w i‖^2 = T3 := by
    simp_rw [hwi_sq]
    show (∑ i, ∑ j, ∑ k, A i j * A i k * A j k) = ∑ i, ∑ j, ∑ k, A i j * A j k * A k i
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    have : A k i = A i k := hA_symm k i
    rw [this]; ring
  -- ∑ i ⟨v i, w i⟩ = T2.
  have hsum_vi_wi : ∑ i, inner ℝ (v i) (w i) = T2 := by
    simp_rw [hvi_wi]
    rfl
  -- ∑ i ‖v i‖² = N.
  have hsum_vi_sq : ∑ i : Fin N, ‖v i‖^2 = N := by
    simp_rw [hnorm]; simp
  have hsum_eq : ∑ i, ‖w i - (2 : ℝ) • v i‖^2 = T3 - 4 * T2 + 4 * N := by
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsum_w_sq]
    rw [show (∑ i : Fin N, 4 * inner ℝ (v i) (w i)) = 4 * ∑ i, inner ℝ (v i) (w i) by
      rw [Finset.mul_sum]]
    rw [hsum_vi_wi]
    rw [show (∑ i : Fin N, 4 * ‖v i‖^2) = 4 * ∑ i, ‖v i‖^2 by rw [Finset.mul_sum]]
    rw [hsum_vi_sq]
  have hineq : (0 : ℝ) ≤ T3 - 4 * T2 + 4 * N := by
    rw [← hsum_eq]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- Combine: T3 = 3 T2 - 2N and T3 - 4 T2 + 4N ≥ 0 gives -T2 + 2N ≥ 0, i.e. T2 ≤ 2N.
  have hT2_bound : T2 ≤ 2 * N := by linarith [hT3_eq, hineq]
  -- Step 3: Cauchy-Schwarz N² ≤ n T2.
  -- Express T2 in terms of coordinates: define Q k l = ∑ i, v i k * v i l.
  -- Then ∑_{k,l} (Q k l)^2 = T2 and ∑_k Q k k = N.
  let Q : Fin n → Fin n → ℝ := fun k l => ∑ i : Fin N, v i k * v i l
  have hQ_diag_sum : ∑ k, Q k k = N := by
    show (∑ k, ∑ i, v i k * v i k) = N
    rw [Finset.sum_comm]
    have : ∀ i : Fin N, (∑ k, v i k * v i k) = 1 := by
      intro i
      have := hnorm i
      have h2 : ‖v i‖^2 = 1 := by rw [this]; ring
      rw [EuclideanSpace.real_norm_sq_eq] at h2
      rw [show (∑ k, v i k * v i k) = ∑ k, (v i k)^2 by
        congr 1; ext k; ring] at *
      exact h2
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  have hT2_eq_Q : T2 = ∑ k, ∑ l, (Q k l)^2 := by
    show (∑ i, ∑ j, (A i j)^2) = ∑ k, ∑ l, (Q k l)^2
    -- A i j = ⟨v i, v j⟩ = ∑ k, v i k * v j k
    -- (A i j)^2 = (∑ k, v i k * v j k)^2 = ∑ k ∑ l, v i k v j k v i l v j l
    -- Sum over i,j: ∑ i ∑ j ∑ k ∑ l, v i k v j k v i l v j l
    --           = ∑ k ∑ l, (∑ i, v i k v i l)(∑ j, v j k v j l) = ∑ k ∑ l, (Q k l)^2.
    have hAij : ∀ i j : Fin N, A i j = ∑ k, v i k * v j k := by
      intro i j
      show inner ℝ (v i) (v j) = _
      rw [real_inner_eq_sum]
    have hAij_sq : ∀ i j : Fin N, (A i j)^2 = ∑ k, ∑ l, v i k * v j k * (v i l * v j l) := by
      intro i j
      rw [hAij i j, sq]
      rw [Finset.sum_mul_sum]
    simp_rw [hAij_sq]
    -- ∑ i ∑ j ∑ k ∑ l, ... → ∑ k ∑ l ∑ i ∑ j, ...
    -- We do this in steps using Finset.sum_comm.
    -- Step 1: swap j↔k at depth 2: ∑i ∑j ∑k = ∑i ∑k ∑j
    rw [show (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin n, ∑ l : Fin n,
              v i k * v j k * (v i l * v j l)) =
            ∑ i : Fin N, ∑ k : Fin n, ∑ j : Fin N, ∑ l : Fin n,
              v i k * v j k * (v i l * v j l) by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]]
    -- Step 2: swap i↔k at depth 1: ∑i ∑k = ∑k ∑i
    rw [Finset.sum_comm]
    -- Step 3: swap j↔l at depth 3: ∑j ∑l = ∑l ∑j
    rw [show (∑ k : Fin n, ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin n,
              v i k * v j k * (v i l * v j l)) =
            ∑ k : Fin n, ∑ i : Fin N, ∑ l : Fin n, ∑ j : Fin N,
              v i k * v j k * (v i l * v j l) by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]]
    -- Step 4: swap i↔l at depth 2: ∑i ∑l = ∑l ∑i
    rw [show (∑ k : Fin n, ∑ i : Fin N, ∑ l : Fin n, ∑ j : Fin N,
              v i k * v j k * (v i l * v j l)) =
            ∑ k : Fin n, ∑ l : Fin n, ∑ i : Fin N, ∑ j : Fin N,
              v i k * v j k * (v i l * v j l) by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    show (∑ i, ∑ j, v i k * v j k * (v i l * v j l)) = (Q k l)^2
    have hQsq : (Q k l)^2 = (∑ i, v i k * v i l) * (∑ j, v j k * v j l) := by
      show (∑ i : Fin N, v i k * v i l) ^ 2 = _
      rw [sq]
    rw [hQsq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  -- Cauchy-Schwarz: (∑ k, Q k k)^2 ≤ n * ∑ k (Q k k)^2.
  have hCS : (∑ k, Q k k)^2 ≤ n * ∑ k, (Q k k)^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun k => Q k k)
    simp at h
    exact h
  have hQ_sum_bound : ∑ k, (Q k k)^2 ≤ ∑ k, ∑ l, (Q k l)^2 := by
    apply Finset.sum_le_sum
    intro k _
    have hpos : ∀ l, 0 ≤ (Q k l)^2 := fun l => sq_nonneg _
    have hkk : (Q k k)^2 = (Q k k)^2 := rfl
    calc (Q k k)^2 = ∑ l ∈ ({k} : Finset (Fin n)), (Q k l)^2 := by simp
      _ ≤ ∑ l, (Q k l)^2 := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun l _ _ => hpos l)
  -- Combine: N² = (∑ k Q k k)² ≤ n ∑ k (Q k k)² ≤ n ∑ k ∑ l (Q k l)² = n T2 ≤ 2 n N.
  have hN_sq : (N : ℝ)^2 ≤ n * T2 := by
    rw [← hQ_diag_sum] at *
    rw [hT2_eq_Q]
    calc (∑ k, Q k k)^2 ≤ n * ∑ k, (Q k k)^2 := hCS
      _ ≤ n * ∑ k, ∑ l, (Q k l)^2 := by
          have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left hQ_sum_bound hn_nn
  -- Final: N² ≤ n * T2 ≤ n * 2 N = 2 n N. So N ≤ 2 n.
  have hfinal : (N : ℝ)^2 ≤ 2 * n * N := by
    calc (N : ℝ)^2 ≤ n * T2 := hN_sq
      _ ≤ n * (2 * N) := by
          have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left hT2_bound hn_nn
      _ = 2 * n * N := by ring
  -- Conclude N ≤ 2n from N² ≤ 2 n N.
  by_cases hN0 : N = 0
  · simp [hN0]
  · have hN_pos : (0 : ℝ) < N := by
      have : 0 < N := Nat.pos_of_ne_zero hN0
      exact_mod_cast this
    have hfinal' : (N : ℝ) ≤ 2 * n := by
      have h2 : (N : ℝ) * N ≤ 2 * n * N := by
        have hsq : (N : ℝ)^2 = (N : ℝ) * N := sq (N : ℝ)
        linarith
      exact le_of_mul_le_mul_right (by linarith) hN_pos
    exact_mod_cast hfinal'

snip end

problem imc2021_p8 (n : ℕ) (hn : 0 < n) :
    IsGreatest
      { N | ∃ v : Fin N → EuclideanSpace ℝ (Fin n),
        Function.Injective v ∧
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
          inner ℝ (v i) (v j) = (0 : ℝ) ∨
          inner ℝ (v j) (v k) = (0 : ℝ) ∨
          inner ℝ (v i) (v k) = (0 : ℝ)) }
      (answer n) := by
  refine ⟨?_, ?_⟩
  · -- Membership: 2n is achievable via example_vec.
    refine ⟨example_vec n, example_vec_injective, example_vec_norm_one, ?_⟩
    intro i j k hij hjk hik
    -- By pigeonhole, two of i,j,k have different coordinate classes.
    obtain ⟨x, y, hxy, hx, hy, hclass⟩ :=
      three_indices_pigeonhole i j k hij hjk hik
    have horth : inner ℝ (example_vec n x) (example_vec n y) = (0 : ℝ) :=
      example_vec_orthogonal_of_ne_class x y hclass
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | (exact absurd rfl hxy)
      | (left; exact horth)
      | (right; left; exact horth)
      | (right; right; exact horth)
      | (left; rw [real_inner_comm]; exact horth)
      | (right; left; rw [real_inner_comm]; exact horth)
      | (right; right; rw [real_inner_comm]; exact horth)
  · -- Upper bound: N ≤ 2n. Apply the helper lemma.
    rintro N ⟨v, _, hnorm, hortho⟩
    exact imc2021_p8_upper_bound n hn N v hnorm hortho

end Imc2021P8
