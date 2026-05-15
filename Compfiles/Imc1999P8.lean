/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 1999, Problem 8 (Day 2, Problem 2)

A standard six-sided die is thrown `n` times. Determine the probability
that the sum of the rolls is divisible by `5`.

## Answer (official)

  `P(5 ∣ sum) = 1/5 + 4/(5 · 6^n)` if `5 ∣ n`,
  `P(5 ∣ sum) = 1/5 - 1/(5 · 6^n)` otherwise.

## Solution sketch (official, via roots of unity)

Let `ε = e^(2πi/5)`. The generating function for one die roll is
`(x + x² + ⋯ + x⁶)/6`. The probability that the sum of `n` rolls is
divisible by `5` equals
  `(1/5) ∑_{j=0}^{4} f(ε^j)`,
where `f(x) = ((x+x²+⋯+x⁶)/6)^n`. For `j = 0` we get `f(1) = 1`. For
`j ≠ 0`, since `1 + ε^j + ε^(2j) + ε^(3j) + ε^(4j) = 0`, the inner
factor simplifies to `ε^j / 6`, hence `f(ε^j) = ε^(jn) / 6^n`. Summing
`∑_{j=1}^{4} ε^(jn) = 4` if `5 ∣ n` and `-1` otherwise yields the
formula.

## Formalization approach (real-arithmetic induction)

We avoid complex roots of unity entirely. Set `rollCount n k` := number
of `n`-tuples in `(Fin 6)^n` (encoding faces `1..6` via `i.val + 1`)
whose sum is `≡ k (mod 5)`. Then we claim the closed form
  `5 · rollCount n k = 6^n + δ(n, k)`,
where `δ(n, k) = 4` if `(n : ZMod 5) = k` and `δ(n, k) = -1` otherwise.

This is established by induction on `n`. The inductive step rests on
the multiplicities of die-face residues mod 5: the residues of
`1,2,3,4,5,6` are `1,2,3,4,0,1`, i.e., residue `1` appears twice and
residues `0, 2, 3, 4` each appear once. Hence
  `∑_{j ∈ Fin 6} δ(n, k - (j+1)) = δ(n, k) + 2·δ(n, k-1) + δ(n, k-2) + δ(n, k-3) + δ(n, k-4)`.
Exactly one of the five summands `δ(n, k - r)` (for `r ∈ ZMod 5`)
equals `4`; the rest equal `-1`. Case analysis on the residue
`r* = (k - n) mod 5` then yields the claim
  `∑_{j ∈ Fin 6} δ(n, k - (j+1)) = δ(n+1, k)`.

Specializing to `k = 0` gives the answer for the original problem.

## Status

Statement: complete. Proof: complete (induction on `n`, with the
inductive step decided on the residue `(k - n) mod 5`).
-/

namespace Imc1999P8

open scoped BigOperators
open Finset

/-- The set of `n`-tuples of die rolls. Each component `r i : Fin 6`
encodes the face `r i + 1 ∈ {1, …, 6}`. -/
def rolls (n : ℕ) : Finset (Fin n → Fin 6) := Finset.univ

/-- The sum of an `n`-tuple of rolls (face value of `r i` is `r i + 1`),
viewed in `ZMod 5`. -/
def rollSum {n : ℕ} (r : Fin n → Fin 6) : ZMod 5 :=
  ∑ i, ((r i).val + 1 : ZMod 5)

/-- The number of `n`-tuples of rolls whose sum is `≡ k (mod 5)`. -/
noncomputable def rollCount (n : ℕ) (k : ZMod 5) : ℕ :=
  ((rolls n).filter (fun r => rollSum r = k)).card

snip begin

/-- The "indicator" `δ(n, k) = 4` if `(n : ZMod 5) = k`, else `-1`. -/
def deltaSign (n : ℕ) (k : ZMod 5) : ℤ :=
  if (n : ZMod 5) = k then (4 : ℤ) else -1

/-- Sum of an `(n+1)`-tuple via `snoc`. -/
lemma rollSum_snoc (n : ℕ) (r' : Fin n → Fin 6) (j : Fin 6) :
    rollSum (Fin.snoc r' j : Fin (n + 1) → Fin 6) =
    rollSum r' + (((j.val : ℕ) + 1 : ℕ) : ZMod 5) := by
  unfold rollSum
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin n, ((Fin.snoc r' j : Fin (n+1) → Fin 6) i.castSucc) = r' i := by
    intro i; rw [Fin.snoc_castSucc]
  have h2 : (Fin.snoc r' j : Fin (n+1) → Fin 6) (Fin.last n) = j := Fin.snoc_last _ _
  simp_rw [h1, h2]
  push_cast
  ring

/-- Recurrence: an `(n+1)`-tuple = an `n`-tuple followed by a final face. -/
lemma rollCount_succ_eq (n : ℕ) (k : ZMod 5) :
    rollCount (n + 1) k =
      ∑ j : Fin 6, rollCount n (k - (((j.val : ℕ) + 1 : ℕ) : ZMod 5)) := by
  classical
  unfold rollCount rolls
  -- Apply fiberwise on the last coordinate.
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun r : Fin (n+1) → Fin 6 => r (Fin.last n))
    (s := (Finset.univ : Finset (Fin (n+1) → Fin 6)).filter (fun r => rollSum r = k))
    (t := (Finset.univ : Finset (Fin 6))) (fun _ _ => Finset.mem_univ _)
  rw [hfiber]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- card {r ∈ {r | sum r = k} | r last = j} = card {r' | sum r' = k - (j+1)}.
  apply Finset.card_bij' (fun (r : Fin (n+1) → Fin 6) _ => Fin.init r)
                         (fun (r' : Fin n → Fin 6) _ => Fin.snoc r' j)
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    obtain ⟨hsum, hlast⟩ := hr
    have heq : Fin.snoc (Fin.init r) j = r := by
      rw [← hlast]; exact Fin.snoc_init_self r
    have hsum' : rollSum (Fin.snoc (Fin.init r) j : Fin (n+1) → Fin 6) = k := by
      rw [heq]; exact hsum
    rw [rollSum_snoc] at hsum'
    rw [eq_sub_iff_add_eq]; exact hsum'
  · intro r' hr'
    simp only [mem_filter, mem_univ, true_and] at hr' ⊢
    refine ⟨?_, ?_⟩
    · rw [rollSum_snoc, hr']; ring
    · exact Fin.snoc_last _ _
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    obtain ⟨_, hlast⟩ := hr
    rw [← hlast]; exact Fin.snoc_init_self r
  · intro r' _
    exact Fin.init_snoc _ _

/-- Sum of `deltaSign` over the six die-face residues equals `deltaSign (n+1) k`. -/
lemma sum_delta_succ (n : ℕ) (k : ZMod 5) :
    ∑ j : Fin 6, deltaSign n (k - (((j.val : ℕ) + 1 : ℕ) : ZMod 5)) =
      deltaSign (n + 1) k := by
  -- Fin 6 is a finite enumeration; just expand and decide.
  have : (Finset.univ : Finset (Fin 6)) =
      {(0 : Fin 6), 1, 2, 3, 4, 5} := by decide
  rw [this]
  rw [show ({(0 : Fin 6), 1, 2, 3, 4, 5} : Finset (Fin 6)) =
        insert (0 : Fin 6) (insert 1 (insert 2 (insert 3 (insert 4 {5})))) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  -- Each (j.val + 1) for j = 0,1,2,3,4,5: face values 1,2,3,4,5,6.
  -- Their residues mod 5: 1, 2, 3, 4, 0, 1.
  unfold deltaSign
  -- Now everything is decidable on `ZMod 5`. Case split on `(n : ZMod 5)` and `k`.
  -- We reduce by case-splitting on the residue r = k - (n : ZMod 5).
  have hcases : ∀ x : ZMod 5, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  set N : ZMod 5 := (n : ZMod 5)
  set N1 : ZMod 5 := ((n + 1 : ℕ) : ZMod 5)
  have hN1 : N1 = N + 1 := by
    simp [N, N1, Nat.cast_add, Nat.cast_one]
  rcases hcases N with hN | hN | hN | hN | hN <;>
    rcases hcases k with hK | hK | hK | hK | hK <;>
    · simp only [hN, hK, hN1]
      decide

/-- Closed-form count of die-roll `n`-tuples with sum in residue class `k`.

  `5 · rollCount n k = 6^n + δ(n, k)`, where `δ(n, k) = 4` if
  `(n : ZMod 5) = k` and `-1` otherwise. -/
lemma rollCount_formula_aux (n : ℕ) (k : ZMod 5) :
    (5 : ℤ) * rollCount n k = (6 : ℤ) ^ n + deltaSign n k := by
  induction n generalizing k with
  | zero =>
    -- For n=0, the only tuple is the empty tuple, with sum 0.
    unfold deltaSign
    have hn0 : ((0 : ℕ) : ZMod 5) = (0 : ZMod 5) := by simp
    by_cases hk : k = 0
    · subst hk
      have h0 : rollCount 0 0 = 1 := by
        unfold rollCount rolls rollSum
        rw [show ((Finset.univ : Finset (Fin 0 → Fin 6)).filter
            (fun r => ∑ i : Fin 0, ((r i).val + 1 : ZMod 5) = 0)) =
            (Finset.univ : Finset (Fin 0 → Fin 6)) from ?_]
        · simp
        · ext r; simp
      rw [h0]
      simp [hn0]
    · have hzero : rollCount 0 k = 0 := by
        unfold rollCount rolls rollSum
        rw [show ((Finset.univ : Finset (Fin 0 → Fin 6)).filter
            (fun r => ∑ i : Fin 0, ((r i).val + 1 : ZMod 5) = k)) =
            ∅ from ?_]
        · exact Finset.card_empty
        · ext r
          simp only [mem_filter, mem_univ, true_and,
                     Finset.notMem_empty, iff_false]
          intro h0; exact hk (Eq.symm h0)
      rw [hzero]
      rw [hn0]
      rw [if_neg (Ne.symm hk)]
      simp
  | succ n ih =>
    -- The recurrence gives card (n+1) = sum of cards of length n.
    have hrec := rollCount_succ_eq n k
    rw [hrec]
    push_cast
    rw [Finset.mul_sum]
    -- Apply IH term-by-term. After push_cast, the argument of `rollCount n`
    -- becomes `k - (↑↑j + 1)` (with the +1 inside ZMod 5).
    have step : ∀ j ∈ (Finset.univ : Finset (Fin 6)),
        (5 : ℤ) * ((rollCount n (k - ((((j : Fin 6).val : ZMod 5) + 1))) : ℕ) : ℤ) =
        (6 : ℤ) ^ n + deltaSign n (k - (((j.val : ZMod 5) + 1))) := by
      intro j _
      have := ih (k - (((j.val : ZMod 5) + 1)))
      exact_mod_cast this
    rw [Finset.sum_congr rfl step]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    -- Now apply sum_delta_succ.
    have hsum : ∑ j : Fin 6, deltaSign n (k - (((j.val : ZMod 5) + 1))) =
                deltaSign (n + 1) k := by
      have := sum_delta_succ n k
      convert this using 2 with j _
      push_cast; ring
    rw [hsum]
    ring

snip end

/-- Closed-form count of die-roll `n`-tuples with sum in residue class `k`. -/
theorem rollCount_formula (n : ℕ) (k : ZMod 5) :
    (5 : ℤ) * rollCount n k =
      (6 : ℤ) ^ n + (if (n : ZMod 5) = k then (4 : ℤ) else -1) := by
  rw [rollCount_formula_aux n k]
  rfl

/-- **IMC 1999 Problem 8.**

The number of `n`-tuples of die rolls whose sum is divisible by `5`,
multiplied by `5`, satisfies:

* `5 · rollCount n 0 = 6^n + 4` if `5 ∣ n`,
* `5 · rollCount n 0 = 6^n - 1` otherwise.

Equivalently, after dividing by `6^n`, the probability of a sum
divisible by `5` equals `1/5 + 4/(5 · 6^n)` in the first case and
`1/5 - 1/(5 · 6^n)` in the second. -/
problem imc1999_p8 (n : ℕ) :
    (5 : ℤ) * rollCount n 0 =
      if 5 ∣ n then (6 : ℤ) ^ n + 4 else (6 : ℤ) ^ n - 1 := by
  have h := rollCount_formula n 0
  rw [h]
  by_cases hd : (5 : ℕ) ∣ n
  · rw [if_pos hd]
    have hzero : (n : ZMod 5) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact_mod_cast hd
    rw [if_pos hzero]
  · rw [if_neg hd]
    have hnz : ¬ ((n : ZMod 5) = 0) := by
      rw [ZMod.natCast_eq_zero_iff]
      exact_mod_cast hd
    rw [if_neg hnz]
    ring

end Imc1999P8
