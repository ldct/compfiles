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
  · -- Upper bound: N ≤ 2n.
    -- Projector-trace argument. For each unit vector v_i define the rank-1
    -- projection P_i = v_i v_i^T. The hypothesis gives tr(P_i P_j P_k) = 0
    -- for distinct i,j,k. Let Q = Σ P_i with eigenvalues t_i ≥ 0 and
    -- Σ t_i = tr(Q) = N. Then
    --   Σ t_i^3 = tr(Q^3) = N + 6 Σ_{i<j} tr(P_i P_j) = 3 Σ t_i^2 - 2N.
    -- Since (t-2)^2(t+1) ≥ 0 gives t^3 - 3t^2 + 4 ≥ 0,
    --   -2N = Σ(t_i^3 - 3 t_i^2) ≥ -4n, i.e., N ≤ 2n.
    sorry

end Imc2021P8
