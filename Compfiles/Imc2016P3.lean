/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2016, Problem 3

Let `n` be a positive integer and let `a₁, …, aₙ` and `b₁, …, bₙ` be real
numbers with `aᵢ + bᵢ > 0` for all `i`. Prove that

  ∑ᵢ (aᵢ * bᵢ - bᵢ²) / (aᵢ + bᵢ) ≤
    ((∑ᵢ aᵢ) * (∑ᵢ bᵢ) - (∑ᵢ bᵢ)²) / ∑ᵢ (aᵢ + bᵢ).
-/

namespace Imc2016P3

open Finset

problem imc2016_p3 (n : ℕ) (a b : Fin n → ℝ)
    (hab : ∀ i, 0 < a i + b i) :
    ∑ i, (a i * b i - (b i)^2) / (a i + b i) ≤
      ((∑ i, a i) * (∑ i, b i) - (∑ i, b i)^2) / (∑ i, (a i + b i)) := by
  -- Key identity: (X*Y - Y²)/(X+Y) = Y - 2*Y²/(X+Y).
  -- Apply both sides and reduce to Cauchy-Schwarz / Sedrakyan's lemma:
  --   ∑ bᵢ²/(aᵢ+bᵢ) ≥ (∑ bᵢ)² / ∑ (aᵢ+bᵢ).
  by_cases hn : n = 0
  · subst hn
    simp
  -- Since n ≠ 0, univ is nonempty, so ∑(aᵢ+bᵢ) > 0.
  have hne : (univ : Finset (Fin n)).Nonempty := by
    rw [univ_nonempty_iff]; exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hSpos : 0 < ∑ i, (a i + b i) :=
    sum_pos (fun i _ => hab i) hne
  -- Sedrakyan's lemma applied to f = b, g = a + b:
  have hsed : (∑ i, b i)^2 / (∑ i, (a i + b i)) ≤
      ∑ i, (b i)^2 / (a i + b i) :=
    sq_sum_div_le_sum_sq_div (univ : Finset (Fin n)) b (fun i _ => hab i)
  -- Rewrite each side using the identity (a*b - b²)/(a+b) = b - 2*b²/(a+b).
  have lhs_eq : ∑ i, (a i * b i - (b i)^2) / (a i + b i) =
      (∑ i, b i) - 2 * ∑ i, (b i)^2 / (a i + b i) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    have hne : a i + b i ≠ 0 := ne_of_gt (hab i)
    field_simp
    ring
  -- Rewrite RHS: ((∑a)(∑b) - (∑b)²)/∑(a+b) = ∑b - 2*(∑b)²/∑(a+b).
  have rhs_eq : ((∑ i, a i) * (∑ i, b i) - (∑ i, b i)^2) / (∑ i, (a i + b i)) =
      (∑ i, b i) - 2 * ((∑ i, b i)^2 / (∑ i, (a i + b i))) := by
    have hS : ∑ i, (a i + b i) = (∑ i, a i) + (∑ i, b i) := sum_add_distrib
    have hSne : (∑ i, (a i + b i)) ≠ 0 := ne_of_gt hSpos
    rw [hS] at hSne ⊢
    field_simp
    ring
  rw [lhs_eq, rhs_eq]
  linarith [hsed]

end Imc2016P3
