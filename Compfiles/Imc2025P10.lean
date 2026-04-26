/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2025, Problem 10

For any positive integer `N`, let `S_N` be the number of pairs of integers
`1 ≤ a, b ≤ N` such that the number `(a² + a)(b² + b)` is a perfect square.
Prove that the limit

  `lim_{N → ∞} S_N / N`

exists and find its value.

Answer: the limit equals `1`.
-/

namespace Imc2025P10

/-- The count `S_N` of pairs `(a, b) ∈ [1, N]²` with `(a² + a)(b² + b)` a
perfect square. -/
def S (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
    (fun p : ℕ × ℕ => IsSquare ((p.1 ^ 2 + p.1) * (p.2 ^ 2 + p.2))) |>.card

/-- The answer: the limit equals `1`. -/
determine answer : ℝ := 1

/-- The diagonal `(a, a)` always satisfies `(a² + a)² = ((a² + a))²` is a square,
hence `S N ≥ N`. -/
lemma N_le_S (N : ℕ) : N ≤ S N := by
  classical
  -- The injection `a ↦ (a, a)` lands in the filtered set.
  let f : ℕ → ℕ × ℕ := fun a => (a, a)
  have hf_inj : Function.Injective f := fun a b h => (Prod.mk.injEq _ _ _ _).mp h |>.1
  have h_image : (Finset.Icc 1 N).image f ⊆
      ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
        (fun p : ℕ × ℕ => IsSquare ((p.1 ^ 2 + p.1) * (p.2 ^ 2 + p.2))) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, ha⟩, ?_⟩
    exact ⟨a^2 + a, by ring⟩
  calc N = (Finset.Icc 1 N).card := by rw [Nat.card_Icc]; omega
    _ = ((Finset.Icc 1 N).image f).card :=
          (Finset.card_image_of_injective _ hf_inj).symm
    _ ≤ S N := Finset.card_le_card h_image

problem imc2025_p10 :
    Filter.Tendsto (fun N : ℕ => (S N : ℝ) / N) Filter.atTop (nhds answer) := by
  -- TODO: Following the official solution.
  -- (a² + a)(b² + b) is a perfect square iff there is a square-free d and
  -- positive integers z₁, z₂ with a² + a = d z₁² and b² + b = d z₂².
  -- Multiplying by 4 and setting yᵢ = 2zᵢ gives the Pell-type equation
  --   (2k+1)² - d y² = 1.
  -- The "trivial" diagonal a = b contributes N pairs (giving S_N/N ≥ 1, see
  -- `N_le_S` above). The "error" coming from d ≪ N is bounded using the
  -- divisor-function estimate g(n) ≤ τ(n) ≪ n^ε and exponential growth of
  -- Pell solutions, and is o(N). Hence S_N / N → 1.
  sorry

end Imc2025P10
