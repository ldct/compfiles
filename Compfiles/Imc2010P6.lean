/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 6

(a) A sequence `x₁, x₂, …` of reals satisfies `x_{n+1} = x_n cos x_n` for all
    `n ≥ 1`. Does it follow that this sequence converges for all initial
    values `x₁`?

(b) A sequence `y₁, y₂, …` of reals satisfies `y_{n+1} = y_n sin y_n` for all
    `n ≥ 1`. Does it follow that this sequence converges for all initial
    values `y₁`?

Answers: (a) No. (b) Yes.
-/

namespace Imc2010P6

/-- Answer to part (a): not every sequence of the form `x_{n+1} = x_n cos x_n`
converges. Counterexample: `x₁ = π`. -/
determine answerA : Prop := False

/-- Answer to part (b): every sequence of the form `y_{n+1} = y_n sin y_n`
converges. -/
determine answerB : Prop := True

snip begin

/-- Key identity: `t * sin t = |t| * sin |t|` for all real `t`. Both sides are
even functions of `t` that agree for `t ≥ 0`. -/
lemma mul_sin_eq_abs_mul_sin_abs (t : ℝ) :
    t * Real.sin t = |t| * Real.sin |t| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht, Real.sin_neg]; ring

/-- If a sequence tends to a limit `L`, then any subsequence also tends to `L`.
Applied here to the constant subsequences that pick out alternating terms. -/
lemma not_tendsto_of_two_values {a : ℕ → ℝ} {p q : ℝ} (hpq : p ≠ q)
    (hp : ∀ k, a (2 * k) = p) (hq : ∀ k, a (2 * k + 1) = q) :
    ¬ ∃ L, Filter.Tendsto a Filter.atTop (nhds L) := by
  rintro ⟨L, hL⟩
  -- Subsequence along even indices converges to L, but is constantly p.
  have hp_tend : Filter.Tendsto (fun k : ℕ => a (2 * k)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
  have hp_const : Filter.Tendsto (fun k : ℕ => a (2 * k)) Filter.atTop (nhds p) := by
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall (fun k => (hp k).symm)
  have hLp : L = p := tendsto_nhds_unique hp_tend hp_const
  -- Subsequence along odd indices converges to L, but is constantly q.
  have hq_tend : Filter.Tendsto (fun k : ℕ => a (2 * k + 1)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩))
  have hq_const : Filter.Tendsto (fun k : ℕ => a (2 * k + 1)) Filter.atTop (nhds q) := by
    refine tendsto_const_nhds.congr' ?_
    exact Filter.Eventually.of_forall (fun k => (hq k).symm)
  have hLq : L = q := tendsto_nhds_unique hq_tend hq_const
  exact hpq (hLp.symm.trans hLq)

snip end

problem imc2010_p6 :
    (answerA ↔
      ∀ (x : ℕ → ℝ), (∀ n, x (n + 1) = x n * Real.cos (x n)) →
        ∃ L : ℝ, Filter.Tendsto x Filter.atTop (nhds L)) ∧
    (answerB ↔
      ∀ (y : ℕ → ℝ), (∀ n, y (n + 1) = y n * Real.sin (y n)) →
        ∃ L : ℝ, Filter.Tendsto y Filter.atTop (nhds L)) := by
  refine ⟨?_, ?_⟩
  · -- Part (a): answer is False, i.e., the claim is not true in general.
    show False ↔ _
    refine ⟨False.elim, ?_⟩
    -- Counterexample: x₀ = π, then x_n = π for even n and -π for odd n.
    intro H
    -- Construct the sequence x n = (-1)^n * π.
    set x : ℕ → ℝ := fun n => (-1) ^ n * Real.pi with hx_def
    -- Verify the recursion: x(n+1) = x n * cos(x n).
    have hrec : ∀ n, x (n + 1) = x n * Real.cos (x n) := by
      intro n
      -- cos(x n) = cos((-1)^n * π) = cos(±π) = -1.
      have hcos : Real.cos (x n) = -1 := by
        simp only [hx_def]
        rcases Nat.even_or_odd n with heven | hodd
        · rw [heven.neg_one_pow]
          simp [Real.cos_pi]
        · rw [hodd.neg_one_pow]
          simp [Real.cos_neg, Real.cos_pi]
      rw [hcos]
      simp only [hx_def]
      rw [pow_succ]
      ring
    -- The sequence doesn't converge: x(2k) = π, x(2k+1) = -π.
    have hne : ¬ ∃ L : ℝ, Filter.Tendsto x Filter.atTop (nhds L) := by
      apply not_tendsto_of_two_values (p := Real.pi) (q := -Real.pi)
      · intro h
        have : Real.pi > 0 := Real.pi_pos
        linarith
      · intro k
        simp only [hx_def]
        have : Even (2 * k) := ⟨k, by ring⟩
        rw [this.neg_one_pow]; ring
      · intro k
        simp only [hx_def]
        have : Odd (2 * k + 1) := ⟨k, rfl⟩
        rw [this.neg_one_pow]; ring
    exact hne (H x hrec)
  · -- Part (b): answer is True. Every sequence converges.
    show True ↔ _
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    intro y hy
    -- Step 1: |y n| is nonincreasing and bounded below by 0, so converges.
    -- Let a n = |y n|. Then a(n+1) = |y(n+1)| = |y n sin(y n)| = |y n| * |sin(y n)|
    -- = a n * |sin(a n)| ≤ a n.
    set a : ℕ → ℝ := fun n => |y n| with ha_def
    have ha_nonneg : ∀ n, 0 ≤ a n := fun n => abs_nonneg _
    have ha_rec : ∀ n, a (n + 1) = a n * |Real.sin (a n)| := by
      intro n
      simp only [ha_def]
      rw [hy n, abs_mul]
      congr 1
      -- |sin(y n)| = |sin(|y n|)|
      rcases le_or_gt 0 (y n) with hy_pos | hy_neg
      · rw [abs_of_nonneg hy_pos]
      · rw [abs_of_neg hy_neg, Real.sin_neg, abs_neg]
    have ha_le : ∀ n, a (n + 1) ≤ a n := by
      intro n
      rw [ha_rec n]
      have h1 : |Real.sin (a n)| ≤ 1 := Real.abs_sin_le_one _
      nlinarith [ha_nonneg n]
    -- a is antitone (nonincreasing).
    have ha_anti : Antitone a := antitone_nat_of_succ_le ha_le
    -- a is bounded below by 0.
    have ha_bdd : BddBelow (Set.range a) :=
      ⟨0, fun x ⟨n, hn⟩ => hn ▸ ha_nonneg n⟩
    -- So a converges to its infimum.
    obtain ⟨L_a, hL_a⟩ : ∃ L, Filter.Tendsto a Filter.atTop (nhds L) :=
      ⟨_, tendsto_atTop_ciInf ha_anti ha_bdd⟩
    -- Step 2: For n ≥ 1, y n = a(n-1) * sin(a(n-1)).
    -- So y(n+1) = a n * sin(a n) → L_a * sin L_a by continuity.
    -- We show y → L_a * sin L_a.
    use L_a * Real.sin L_a
    -- It suffices to show that y ∘ (Nat.succ) tends to the limit (since cofinite).
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    -- For all n, y (n + 1) = a n * sin (a n).
    have hy_eq : ∀ n, y (n + 1) = a n * Real.sin (a n) := by
      intro n
      rw [hy n]
      simp only [ha_def]
      exact mul_sin_eq_abs_mul_sin_abs (y n)
    have : Filter.Tendsto (fun n => a n * Real.sin (a n)) Filter.atTop
        (nhds (L_a * Real.sin L_a)) := by
      exact hL_a.mul (Real.continuous_sin.tendsto _ |>.comp hL_a)
    refine this.congr ?_
    intro n
    exact (hy_eq n).symm

end Imc2010P6
