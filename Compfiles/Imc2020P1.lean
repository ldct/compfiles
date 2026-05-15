/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2020, Problem 1

Let `n` be a positive integer. Compute the number of words `w`
(finite sequences of letters) satisfying:
  (1) `w` consists of `n` letters from `{a, b, c, d}`;
  (2) `w` contains an even number of letters `a`;
  (3) `w` contains an even number of letters `b`.

Answer: `4^(n-1) + 2^(n-1)`.

We encode the four letters `{a, b, c, d}` as `Fin 4` with `0 ↦ a`,
`1 ↦ b`, `2 ↦ c`, `3 ↦ d`.
-/

namespace Imc2020P1

open Finset

/-- The set of words of length `n` over `{a, b, c, d}` with even counts
of `a` and `b`. Here `0` represents `a` and `1` represents `b`. -/
noncomputable def goodWords (n : ℕ) : Finset (Fin n → Fin 4) :=
  (Finset.univ : Finset (Fin n → Fin 4)).filter fun w =>
    Even ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 0)).card ∧
    Even ((Finset.univ : Finset (Fin n)).filter (fun i => w i = 1)).card

/-- The answer: `4^(n-1) + 2^(n-1)`. -/
determine answer (n : ℕ) : ℕ := 4 ^ (n - 1) + 2 ^ (n - 1)

/-- The count of letter `k` appearing in word `w`. -/
noncomputable def letterCount (n : ℕ) (w : Fin n → Fin 4) (k : Fin 4) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => w i = k)).card

/-- Count of words of length `n` with specified parities of `a` and `b` counts.
`pa` is the desired parity of `#a` (true = odd, false = even), `pb` for `#b`. -/
noncomputable def parityCount (n : ℕ) (pa pb : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 4)).filter fun w =>
    decide (Odd (letterCount n w 0)) = pa ∧ decide (Odd (letterCount n w 1)) = pb).card

lemma goodWords_card_eq (n : ℕ) : (goodWords n).card = parityCount n false false := by
  unfold goodWords parityCount letterCount
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not,
    Nat.not_odd_iff_even]

lemma letterCount_cons (n : ℕ) (c : Fin 4) (w : Fin n → Fin 4) (k : Fin 4) :
    letterCount (n + 1) (Fin.cons c w) k =
      (if c = k then 1 else 0) + letterCount n w k := by
  unfold letterCount
  set emb : Fin n ↪ Fin (n+1) := ⟨Fin.succ, Fin.succ_injective _⟩ with hemb
  have map_eq : ((Finset.univ : Finset (Fin n)).map emb).filter
      (fun i => (Fin.cons c w : Fin (n+1) → Fin 4) i = k) =
    ((Finset.univ : Finset (Fin n)).filter (fun i => w i = k)).map emb := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, hemb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      refine ⟨j, ?_, rfl⟩
      simpa [Fin.cons_succ] using hj
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j, rfl⟩, ?_⟩
      simpa [Fin.cons_succ] using hj
  rw [Fin.univ_succ]
  show (((Finset.cons 0 (Finset.univ.map emb) (by simp [hemb, Finset.map_eq_image])).filter
      fun i => (Fin.cons c w : Fin (n+1) → Fin 4) i = k).card : ℕ) = _
  rw [Finset.filter_cons]
  simp only [Fin.cons_zero]
  split_ifs with hck
  · rw [Finset.card_cons, map_eq, Finset.card_map, add_comm]
  · rw [map_eq, Finset.card_map, zero_add]

/-- Parity of `letterCount (n+1) (Fin.cons c w) k`. -/
lemma odd_letterCount_cons (n : ℕ) (c : Fin 4) (w : Fin n → Fin 4) (k : Fin 4) :
    (decide (Odd (letterCount (n + 1) (Fin.cons c w) k)) : Bool) =
      xor (decide (c = k)) (decide (Odd (letterCount n w k))) := by
  rw [letterCount_cons]
  by_cases hck : c = k
  · simp only [hck, if_true, decide_true, Bool.true_xor]
    have : (1 + letterCount n w k) % 2 = (letterCount n w k + 1) % 2 := by ring_nf
    rcases Nat.even_or_odd (letterCount n w k) with he | ho
    · have hne : ¬ Odd (letterCount n w k) := Nat.not_odd_iff_even.mpr he
      have h1 : Odd (1 + letterCount n w k) := by
        obtain ⟨m, hm⟩ := he; exact ⟨m, by omega⟩
      simp [h1, hne]
    · have h1 : ¬ Odd (1 + letterCount n w k) := by
        obtain ⟨m, hm⟩ := ho
        rw [Nat.not_odd_iff_even]; exact ⟨m+1, by omega⟩
      simp [h1, ho]
  · simp only [hck, if_false, decide_false, Bool.false_xor, zero_add]

/-- Key recurrence: `parityCount` on words of length `n+1` decomposes by first letter.
A word w of length n+1 is (first letter c, rest w') where c ∈ Fin 4.
  - c=0 flips parity of #a
  - c=1 flips parity of #b
  - c=2,3 flip nothing -/
lemma parityCount_succ (n : ℕ) (pa pb : Bool) :
    parityCount (n + 1) pa pb =
      parityCount n (!pa) pb + parityCount n pa (!pb) +
        2 * parityCount n pa pb := by
  unfold parityCount
  -- Bijection (Fin (n+1) → Fin 4) ≃ (Fin 4) × (Fin n → Fin 4)
  let e : (Fin 4 × (Fin n → Fin 4)) ≃ (Fin (n+1) → Fin 4) :=
    Fin.consEquiv (fun _ : Fin (n+1) => Fin 4)
  have count_eq : ((Finset.univ : Finset (Fin (n+1) → Fin 4)).filter fun w =>
      decide (Odd (letterCount (n+1) w 0)) = pa ∧
      decide (Odd (letterCount (n+1) w 1)) = pb).card =
    ((Finset.univ : Finset (Fin 4 × (Fin n → Fin 4))).filter fun p =>
      decide (Odd (letterCount (n+1) (Fin.cons p.1 p.2) 0)) = pa ∧
      decide (Odd (letterCount (n+1) (Fin.cons p.1 p.2) 1)) = pb).card := by
    rw [← Finset.card_map e.toEmbedding]
    apply congrArg
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(w 0, fun i => w i.succ), ⟨?_, ?_⟩, ?_⟩
      · have : Fin.cons (w 0) (fun i => w i.succ) = w := Fin.cons_self_tail w
        rw [this]; exact h1
      · have : Fin.cons (w 0) (fun i => w i.succ) = w := Fin.cons_self_tail w
        rw [this]; exact h2
      · exact Fin.cons_self_tail w
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, h2⟩
  rw [count_eq]
  -- Now split sum over Fin 4
  rw [show (Finset.univ : Finset (Fin 4 × (Fin n → Fin 4))) =
      (Finset.univ : Finset (Fin 4)).biUnion
        (fun c => (Finset.univ : Finset (Fin n → Fin 4)).map
          ⟨fun w => (c, w), fun w1 w2 h => (Prod.mk.injEq _ _ _ _).mp h |>.2⟩) from ?_]
  · rw [Finset.filter_biUnion]
    rw [Finset.card_biUnion]
    · simp_rw [Finset.filter_map, Finset.card_map]
      rw [Fin.sum_univ_four]
      simp only [Function.Embedding.coeFn_mk, odd_letterCount_cons]
      -- Specialize the xor expressions for c=0,1,2,3
      have e0 : decide ((0 : Fin 4) = (0 : Fin 4)) = true := by decide
      have e1 : decide ((1 : Fin 4) = (0 : Fin 4)) = false := by decide
      have e2 : decide ((2 : Fin 4) = (0 : Fin 4)) = false := by decide
      have e3 : decide ((3 : Fin 4) = (0 : Fin 4)) = false := by decide
      have f0 : decide ((0 : Fin 4) = (1 : Fin 4)) = false := by decide
      have f1 : decide ((1 : Fin 4) = (1 : Fin 4)) = true := by decide
      have f2 : decide ((2 : Fin 4) = (1 : Fin 4)) = false := by decide
      have f3 : decide ((3 : Fin 4) = (1 : Fin 4)) = false := by decide
      simp only [Function.comp_def]
      -- Normalize all decide of numeric Fin 4 equalities. After Lean's unification,
      -- 0 = 0 becomes True, others become False-like.
      norm_num [show ((1 : Fin 4) = 0) ↔ False from by decide,
        show ((0 : Fin 4) = 1) ↔ False from by decide,
        show ((2 : Fin 4) = 0) ↔ False from by decide,
        show ((2 : Fin 4) = 1) ↔ False from by decide,
        show ((3 : Fin 4) = 0) ↔ False from by decide,
        show ((3 : Fin 4) = 1) ↔ False from by decide]
      ring
    · intro c1 _ c2 _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk] at hx1 hx2
      obtain ⟨⟨w1, _, hw1⟩, _⟩ := hx1
      obtain ⟨⟨w2, _, hw2⟩, _⟩ := hx2
      apply hne
      rw [← hw1] at hw2
      exact ((Prod.mk.injEq _ _ _ _).mp hw2 |>.1).symm
  · ext ⟨c, w⟩
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk,
      true_and, true_iff]
    exact ⟨c, w, rfl⟩

/-- Base case: `parityCount 1 pa pb` values. For n=1:
  - words "c"(2), "d"(3) have both counts even → class (false,false), count = 2
  - word "a"(0) has #a odd, #b even → class (true, false), count = 1
  - word "b"(1) has #a even, #b odd → class (false, true), count = 1
  - no word has both odd (need ≥ 2 letters) → class (true, true), count = 0 -/
lemma parityCount_one : parityCount 1 false false = 2 ∧
    parityCount 1 true false = 1 ∧ parityCount 1 false true = 1 ∧
    parityCount 1 true true = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold parityCount letterCount
    decide

/-- Base case: `parityCount 0 pa pb`. Only the all-even class contains the empty word. -/
lemma parityCount_zero : parityCount 0 false false = 1 ∧
    parityCount 0 true false = 0 ∧ parityCount 0 false true = 0 ∧
    parityCount 0 true true = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · unfold parityCount letterCount
    decide

/-- Closed-form values of `parityCount n pa pb` for `n ≥ 1`.
  - E = parityCount n false false = 4^(n-1) + 2^(n-1)
  - A = parityCount n true false = 4^(n-1)
  - B = parityCount n false true = 4^(n-1)
  - D = parityCount n true true = 4^(n-1) - 2^(n-1)  (subtraction OK in ℕ since 4^k ≥ 2^k) -/
lemma parityCount_closed_form (n : ℕ) (hn : 0 < n) :
    parityCount n false false = 4 ^ (n - 1) + 2 ^ (n - 1) ∧
    parityCount n true false = 4 ^ (n - 1) ∧
    parityCount n false true = 4 ^ (n - 1) ∧
    parityCount n true true + 2 ^ (n - 1) = 4 ^ (n - 1) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · -- m = 0, so m+1 = 1
      subst hm0
      have h1 := parityCount_one
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp; exact h1.1
      · simp; exact h1.2.1
      · simp; exact h1.2.2.1
      · simp; omega
    · -- m > 0
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      obtain ⟨hE, hA, hB, hD⟩ := ih hmpos
      have hpow2 : 2 ^ (m - 1) ≤ 4 ^ (m - 1) :=
        Nat.pow_le_pow_left (by norm_num) (m - 1)
      -- recurrences
      have rec_E := parityCount_succ m false false
      have rec_A := parityCount_succ m true false
      have rec_B := parityCount_succ m false true
      have rec_D := parityCount_succ m true true
      simp only [Bool.not_false, Bool.not_true] at rec_E rec_A rec_B rec_D
      have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
      have hsucc : m + 1 - 1 = m := rfl
      rw [hsucc]
      -- Key: hD says D(m) + 2^(m-1) = 4^(m-1), so D(m) = 4^(m-1) - 2^(m-1)
      -- and 4^(m-1) = D(m) + 2^(m-1).
      have pow4_m : (4 : ℕ) ^ m = 4 * 4 ^ (m - 1) := by
        conv_lhs => rw [← hm1]
        rw [pow_succ]; ring
      have pow2_m : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
        conv_lhs => rw [← hm1]
        rw [pow_succ]; ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- E(m+1) = A(m) + B(m) + 2E(m)
        rw [rec_E, hA, hB, hE, pow4_m, pow2_m]; ring
      · -- A(m+1) = E(m) + D(m) + 2A(m); use D(m) = 4^(m-1) - 2^(m-1)
        rw [rec_A, hE, hA]
        have hDeq : parityCount m true true = 4 ^ (m - 1) - 2 ^ (m - 1) := by omega
        rw [hDeq, pow4_m]
        omega
      · -- B(m+1) = E(m) + D(m) + 2B(m)
        rw [rec_B, hE, hB]
        have hDeq : parityCount m true true = 4 ^ (m - 1) - 2 ^ (m - 1) := by omega
        rw [hDeq, pow4_m]
        omega
      · -- D(m+1) = A(m) + B(m) + 2D(m); need D(m+1) + 2^m = 4^m
        rw [rec_D, hA, hB]
        have hDeq : parityCount m true true = 4 ^ (m - 1) - 2 ^ (m - 1) := by omega
        rw [hDeq, pow4_m, pow2_m]
        omega

problem imc2020_p1 (n : ℕ) (hn : 0 < n) :
    (goodWords n).card = answer n := by
  rw [goodWords_card_eq, answer]
  exact (parityCount_closed_form n hn).1

end Imc2020P1
