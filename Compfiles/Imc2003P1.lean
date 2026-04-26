/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 1
(IMC 2003, Day 1, Problem 1)

Let `a : ℕ → ℝ` be a sequence of real numbers with `a 0 = 1` and
`a (n+1) > (3/2) * a n` for every `n`.

(a) Prove that the sequence `b n = a n / (3/2)^n` either has a finite
    limit, or tends to `+∞`.

(b) For every `α > 1`, there exists such a sequence with
    `lim b n = α`.
-/

namespace Imc2003P1

open Filter Topology

snip begin

/-- The auxiliary sequence `b n = a n / (3/2)^n` is strictly increasing
when `a (n+1) > (3/2) * a n`. -/
lemma b_strictMono (a : ℕ → ℝ)
    (h : ∀ n, a (n + 1) > (3 / 2 : ℝ) * a n) :
    StrictMono (fun n => a n / (3 / 2 : ℝ) ^ n) := by
  have hpos : (0 : ℝ) < 3 / 2 := by norm_num
  apply strictMono_nat_of_lt_succ
  intro n
  have hpow_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ n := pow_pos hpos n
  have hpow_succ_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ (n + 1) := pow_pos hpos (n + 1)
  rw [div_lt_div_iff₀ hpow_pos hpow_succ_pos]
  have hn := h n
  have : a (n + 1) * (3 / 2 : ℝ) ^ n > (3 / 2 : ℝ) * a n * (3 / 2 : ℝ) ^ n := by
    exact mul_lt_mul_of_pos_right hn hpow_pos
  have eq1 : (3 / 2 : ℝ) * a n * (3 / 2 : ℝ) ^ n = a n * (3 / 2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]; ring
  linarith [this, eq1]

/-- Construction for part (b): given `α > 1`, the sequence
`c n = α - (α - 1) * (1/2)^n` is strictly increasing, with `c 0 = 1`
and limit `α`. -/
noncomputable def cSeq (α : ℝ) (n : ℕ) : ℝ :=
  α - (α - 1) * (1 / 2 : ℝ) ^ n

lemma cSeq_zero (α : ℝ) : cSeq α 0 = 1 := by
  simp [cSeq]

lemma cSeq_strictMono (α : ℝ) (hα : 1 < α) : StrictMono (cSeq α) := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold cSeq
  have h1 : (0 : ℝ) < α - 1 := by linarith
  have h2 : ((1 / 2 : ℝ) ^ (n + 1)) < (1 / 2 : ℝ) ^ n :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self n)
  nlinarith [mul_lt_mul_of_pos_left h2 h1]

lemma cSeq_tendsto (α : ℝ) : Tendsto (cSeq α) atTop (𝓝 α) := by
  unfold cSeq
  have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have h1 : Tendsto (fun n : ℕ => (α - 1) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have := h0.const_mul (α - 1)
    simpa using this
  have h2 : Tendsto (fun n : ℕ => α - (α - 1) * (1 / 2 : ℝ) ^ n) atTop (𝓝 (α - 0)) :=
    tendsto_const_nhds.sub h1
  simpa using h2

/-- The sequence `a n = (3/2)^n * cSeq α n` used for the construction in (b). -/
noncomputable def aSeq (α : ℝ) (n : ℕ) : ℝ :=
  (3 / 2 : ℝ) ^ n * cSeq α n

lemma aSeq_zero (α : ℝ) : aSeq α 0 = 1 := by
  simp [aSeq, cSeq_zero]

lemma aSeq_growth (α : ℝ) (hα : 1 < α) (n : ℕ) :
    aSeq α (n + 1) > (3 / 2 : ℝ) * aSeq α n := by
  unfold aSeq
  have hpos : (0 : ℝ) < (3 / 2 : ℝ) ^ n := by positivity
  have hsm : cSeq α n < cSeq α (n + 1) := cSeq_strictMono α hα (Nat.lt_succ_self n)
  have key : (3 / 2 : ℝ) ^ (n + 1) * cSeq α (n + 1) >
      (3 / 2 : ℝ) * ((3 / 2 : ℝ) ^ n * cSeq α n) := by
    have e1 : (3 / 2 : ℝ) ^ (n + 1) = (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ n := by
      rw [pow_succ]; ring
    rw [e1]
    have hmulpos : (0 : ℝ) < (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ n := by
      have : (0 : ℝ) < 3 / 2 := by norm_num
      exact mul_pos this hpos
    calc (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ n * cSeq α (n + 1)
        > (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ n * cSeq α n :=
          mul_lt_mul_of_pos_left hsm hmulpos
      _ = (3 / 2 : ℝ) * ((3 / 2 : ℝ) ^ n * cSeq α n) := by ring
  exact key

lemma aSeq_ratio_tendsto (α : ℝ) :
    Tendsto (fun n => aSeq α n / (3 / 2 : ℝ) ^ n) atTop (𝓝 α) := by
  have h : (fun n => aSeq α n / (3 / 2 : ℝ) ^ n) = cSeq α := by
    funext n
    unfold aSeq
    have hne : ((3 / 2 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [h]
  exact cSeq_tendsto α

snip end

problem imc2003_p1 :
    -- Part (a):
    (∀ (a : ℕ → ℝ), a 0 = 1 → (∀ n, a (n + 1) > (3 / 2 : ℝ) * a n) →
      (∃ L : ℝ, Tendsto (fun n => a n / (3 / 2 : ℝ) ^ n) atTop (𝓝 L)) ∨
      Tendsto (fun n => a n / (3 / 2 : ℝ) ^ n) atTop atTop) ∧
    -- Part (b):
    (∀ α : ℝ, 1 < α →
      ∃ (a : ℕ → ℝ), a 0 = 1 ∧ (∀ n, a (n + 1) > (3 / 2 : ℝ) * a n) ∧
        Tendsto (fun n => a n / (3 / 2 : ℝ) ^ n) atTop (𝓝 α)) := by
  refine ⟨?_, ?_⟩
  · -- Part (a)
    intro a _ h
    set b : ℕ → ℝ := fun n => a n / (3 / 2 : ℝ) ^ n with hbdef
    have hmono : StrictMono b := b_strictMono a h
    by_cases hbdd : BddAbove (Set.range b)
    · left
      refine ⟨⨆ i, b i, ?_⟩
      exact tendsto_atTop_ciSup hmono.monotone hbdd
    · right
      -- b is monotone and not bounded above, so b → ∞
      rw [tendsto_atTop_atTop]
      intro M
      -- Since b is not bounded above, there is some index N with b N > M.
      by_contra hcon
      push Not at hcon
      apply hbdd
      refine ⟨M, ?_⟩
      rintro _ ⟨N, rfl⟩
      obtain ⟨n, hn, hlt⟩ := hcon N
      have : b N ≤ b n := hmono.monotone hn
      linarith
  · -- Part (b)
    intro α hα
    refine ⟨aSeq α, aSeq_zero α, aSeq_growth α hα, aSeq_ratio_tendsto α⟩

end Imc2003P1
