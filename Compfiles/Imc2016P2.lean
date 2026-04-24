/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2016, Problem 2

Let `k` and `n` be positive integers. A sequence `(A_1, …, A_k)` of `n × n`
real matrices is called *preferred* if `A_i² ≠ 0` for `1 ≤ i ≤ k` and
`A_i * A_j = 0` for `i ≠ j`.

Show that `k ≤ n` for every preferred sequence, and exhibit a preferred
sequence with `k = n`.
-/

namespace Imc2016P2

open Matrix

/-- A sequence of matrices is *preferred* iff each `A_i² ≠ 0` and `A_i * A_j = 0`
for `i ≠ j`. -/
def IsPreferred {k n : ℕ} (A : Fin k → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, A i * A i ≠ 0) ∧ (∀ i j, i ≠ j → A i * A j = 0)

snip begin

/-- For each `i`, since `A_i² ≠ 0`, we can find a vector `v` with `A_i.mulVec v ≠ 0`,
namely a column of `A_i` whose image under `A_i` is nonzero. -/
lemma exists_mulVec_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : M * M ≠ 0) : ∃ b : Fin n, M.mulVec (fun c => M c b) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  ext a b
  have := congrArg (· a) (hcon b)
  simp only [mulVec, dotProduct, Pi.zero_apply] at this
  rw [Matrix.mul_apply]
  simpa using this

/-- The vectors `v_i := column b_i of A_i` are linearly independent. -/
lemma linearIndependent_of_preferred {k n : ℕ}
    (A : Fin k → Matrix (Fin n) (Fin n) ℝ) (hpref : IsPreferred A)
    (b : Fin k → Fin n)
    (hb : ∀ i, (A i).mulVec (fun c => A i c (b i)) ≠ 0) :
    LinearIndependent ℝ (fun i : Fin k => fun c : Fin n => A i c (b i)) := by
  obtain ⟨_hne_zero, hortho⟩ := hpref
  rw [linearIndependent_iff']
  intro s g hsum i hi
  -- Apply A_i.mulVec to both sides; only the i-th term survives.
  have key : (A i).mulVec (∑ j ∈ s, g j • fun c => A j c (b j)) = 0 := by
    rw [hsum]; ext; simp [mulVec]
  rw [Matrix.mulVec_sum] at key
  have hsingle : ∀ j ∈ s, j ≠ i →
      (A i).mulVec (g j • fun c => A j c (b j)) = 0 := by
    intro j _hj hji
    rw [Matrix.mulVec_smul]
    have hAA : A i * A j = 0 := hortho i j (Ne.symm hji)
    have : (A i).mulVec (fun c => A j c (b j)) = 0 := by
      ext a
      have := congrArg (fun M => M a (b j)) hAA
      simp only [mul_apply, zero_apply] at this
      simpa [mulVec, dotProduct] using this
    rw [this, smul_zero]
  -- Sum reduces to the j = i term.
  have hsum_eq : ∑ j ∈ s, (A i).mulVec (g j • fun c => A j c (b j)) =
      (A i).mulVec (g i • fun c => A i c (b i)) := by
    rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr hi)]
    · simp
    · intro j hjs hjs'
      simp only [Finset.mem_singleton] at hjs'
      exact hsingle j hjs hjs'
  rw [hsum_eq] at key
  rw [Matrix.mulVec_smul] at key
  -- key : g i • (A i).mulVec (col b_i of A_i) = 0, with that vector ≠ 0.
  have := hb i
  have hgi : g i = 0 := by
    by_contra hne
    apply this
    have h2 : g i • (A i).mulVec (fun c => A i c (b i)) = 0 := key
    rcases (smul_eq_zero.mp h2) with h | h
    · exact (hne h).elim
    · exact h
  exact hgi

/-- The "diagonal" example: `A_i = single i i 1` is a preferred sequence with `k = n`. -/
lemma example_preferred (n : ℕ) :
    IsPreferred (fun i : Fin n => (Matrix.single i i (1 : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro i
    show Matrix.single i i (1 : ℝ) * Matrix.single i i 1 ≠ 0
    rw [Matrix.single_mul_single_same, mul_one]
    intro h
    have := congrArg (fun M => M i i) h
    simp at this
  · intro i j hij
    show Matrix.single i i (1 : ℝ) * Matrix.single j j 1 = 0
    exact Matrix.single_mul_single_of_ne (c := (1 : ℝ)) i i j hij (d := (1 : ℝ))

snip end

problem imc2016_p2 :
    (∀ k n : ℕ, ∀ A : Fin k → Matrix (Fin n) (Fin n) ℝ, IsPreferred A → k ≤ n) ∧
    (∀ n : ℕ, 0 < n →
      ∃ A : Fin n → Matrix (Fin n) (Fin n) ℝ, IsPreferred A) := by
  refine ⟨?_, ?_⟩
  · -- The bound k ≤ n.
    intro k n A hpref
    -- For each i, find a column b_i of A_i with A_i.mulVec ≠ 0.
    have hcol : ∀ i, ∃ b : Fin n, (A i).mulVec (fun c => A i c b) ≠ 0 :=
      fun i => exists_mulVec_ne_zero (A i) (hpref.1 i)
    choose b hb using hcol
    -- The vectors v_i are linearly independent.
    have hLI := linearIndependent_of_preferred A hpref b hb
    -- So k ≤ finrank ℝ (Fin n → ℝ) = n.
    have h := hLI.fintype_card_le_finrank
    simpa using h
  · -- The example.
    intro n _hn
    exact ⟨_, example_preferred n⟩

end Imc2016P2
