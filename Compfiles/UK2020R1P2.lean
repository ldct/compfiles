/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2020, Round 1, Problem 2

A sequence of integers a₁, a₂, a₃, … satisfies the relation
4 a_{n+1}² − 4 aₙ a_{n+1} + aₙ² − 1 = 0 for all positive integers n.
What are the possible values of a₁?
-/

namespace UK2020R1P2

/-- The relation rewrites as (2 a_{n+1} − aₙ)² = 1, i.e.
    2 a_{n+1} = aₙ ± 1. For a_{n+1} to be an integer, aₙ must be odd.
    Hence every aₙ is odd, and in particular a₁ can be any odd integer. -/
determine solution_set : Set ℤ := { a | Odd a }

problem uk2020_r1_p2 :
    { a₁ : ℤ | ∃ a : ℕ → ℤ, a 1 = a₁ ∧
      ∀ n ≥ 1, 4 * (a (n + 1))^2 - 4 * a n * a (n + 1) + (a n)^2 - 1 = 0 }
    = solution_set := by
  ext a₁
  simp only [Set.mem_setOf_eq, solution_set]
  constructor
  · rintro ⟨a, ha1, hrec⟩
    -- Use the relation at n=1 to show a 1 is odd.
    have h := hrec 1 (le_refl 1)
    -- 4 a(2)² - 4 a(1) a(2) + a(1)² - 1 = 0
    -- So (2 a(2) - a(1))² = 1, so 2 a(2) - a(1) = ±1, so a(1) = 2 a(2) ∓ 1.
    have hsq : (2 * a 2 - a 1)^2 = 1 := by linarith [h]
    have habs : 2 * a 2 - a 1 = 1 ∨ 2 * a 2 - a 1 = -1 := by
      have h2 : (2 * a 2 - a 1 - 1) * (2 * a 2 - a 1 + 1) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp h2 with h1 | h1
      · left; linarith
      · right; linarith
    rw [← ha1]
    rcases habs with h1 | h1
    · -- a 1 = 2 a 2 - 1
      refine ⟨a 2 - 1, ?_⟩
      omega
    · -- a 1 = 2 a 2 + 1
      refine ⟨a 2, ?_⟩
      omega
  · rintro ⟨k, hk⟩
    -- Construct a sequence starting at a₁ odd. At each step, pick the "odd" branch.
    -- a_{n+1} = (a_n - 1)/2 if (a_n - 1)/2 is odd, else (a_n + 1)/2.
    -- Equivalently: if a_n ≡ 1 (mod 4), a_{n+1} = (a_n - 1)/2 is even, so we pick (a_n + 1)/2.
    -- if a_n ≡ 3 (mod 4), (a_n - 1)/2 is odd.
    -- For a simpler construction: define a recursively so a n is always odd.
    let step : ℤ → ℤ := fun x => if (x - 1) % 4 = 0 then (x + 1) / 2 else (x - 1) / 2
    let seq : ℕ → ℤ := fun n => Nat.rec a₁ (fun _ prev => step prev) n
    have hseq0 : seq 0 = a₁ := rfl
    have hseqS : ∀ n, seq (n + 1) = step (seq n) := fun _ => rfl
    let a : ℕ → ℤ := fun n => Nat.casesOn n 0 seq
    -- Actually simpler: we want any valid extension. We can use (a_n+1)/2 always, but
    -- that fails as noted. Let's try: a_{n+1} = a_n if the relation holds trivially?
    -- No: relation: 4x² - 4 a x + a² - 1 = 0 with x = a gives 4a² - 4a² + a² - 1 = a² - 1 = 0,
    -- requiring a = ±1.
    -- We'll use: a_{n+1} s.t. a_{n+1} is always odd. Start with a₁ = 2k+1.
    -- Define by: if a_n = 2m+1, then pick the odd one among m, m+1.
    -- m = (a_n - 1)/2, m+1 = (a_n + 1)/2. Exactly one is odd.
    -- The odd one equals m if m is odd, else m+1.
    -- m is odd iff a_n ≡ 3 (mod 4).
    refine ⟨a, rfl, ?_⟩
    -- Invariant: for n ≥ 1, Odd (a n) and relation at n.
    suffices h : ∀ n : ℕ, 1 ≤ n → Odd (a n) ∧
        4 * (a (n + 1))^2 - 4 * a n * a (n + 1) + (a n)^2 - 1 = 0 by
      intro n hn
      exact (h n hn).2
    -- Helper: for any odd x, the step gives odd output and satisfies the relation.
    have step_odd : ∀ x : ℤ, Odd x → Odd (step x) := by
      intro x ⟨m, hm⟩
      simp only [step]
      by_cases hc : (x - 1) % 4 = 0
      · simp [hc]
        have : ∃ t, x = 4 * t + 1 := ⟨(x - 1)/4, by omega⟩
        obtain ⟨t, ht⟩ := this
        refine ⟨t, ?_⟩; omega
      · simp [hc]
        have hmod : x % 4 = 3 := by omega
        have : ∃ t, x = 4 * t + 3 := ⟨x / 4, by omega⟩
        obtain ⟨t, ht⟩ := this
        refine ⟨t, ?_⟩; omega
    have step_rel : ∀ x : ℤ, Odd x →
        4 * (step x)^2 - 4 * x * (step x) + x^2 - 1 = 0 := by
      intro x ⟨m, hm⟩
      simp only [step]
      by_cases hc : (x - 1) % 4 = 0
      · simp [hc]
        have : ∃ t, x = 4 * t + 1 := ⟨(x - 1)/4, by omega⟩
        obtain ⟨t, ht⟩ := this
        have hdiv : (x + 1) / 2 = 2 * t + 1 := by rw [ht]; omega
        rw [hdiv]; nlinarith [ht]
      · simp [hc]
        have hmod : x % 4 = 3 := by omega
        have : ∃ t, x = 4 * t + 3 := ⟨x / 4, by omega⟩
        obtain ⟨t, ht⟩ := this
        have hdiv : (x - 1) / 2 = 2 * t + 1 := by rw [ht]; omega
        rw [hdiv]; nlinarith [ht]
    -- a (m+1) = seq m, a (m+2) = seq (m+1) = step (seq m) = step (a (m+1))
    have ha_eq : ∀ m : ℕ, a (m + 1) = seq m := fun m => rfl
    suffices hinv : ∀ m : ℕ, Odd (seq m) ∧
        4 * (seq (m + 1))^2 - 4 * seq m * seq (m + 1) + (seq m)^2 - 1 = 0 by
      intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      -- Goal: Odd (a (1 + m)) ∧ ...(a (1 + m + 1))...(a (1 + m))...
      -- 1 + m = m + 1 definitionally? Yes by Nat.add_comm but not def. Use rewrite.
      have h1 : 1 + m = m + 1 := Nat.add_comm 1 m
      rw [h1]
      rw [ha_eq m, ha_eq (m + 1)]
      exact hinv m
    intro m
    induction m with
    | zero =>
      refine ⟨⟨k, by show a₁ = 2 * k + 1; omega⟩, ?_⟩
      show 4 * (step a₁)^2 - 4 * a₁ * (step a₁) + a₁^2 - 1 = 0
      exact step_rel a₁ ⟨k, by omega⟩
    | succ m ih =>
      obtain ⟨hodd, _⟩ := ih
      have hs1 : seq (m + 1) = step (seq m) := rfl
      have hs2 : seq (m + 1 + 1) = step (step (seq m)) := rfl
      rw [hs1, hs2]
      exact ⟨step_odd _ hodd, step_rel _ (step_odd _ hodd)⟩

end UK2020R1P2
