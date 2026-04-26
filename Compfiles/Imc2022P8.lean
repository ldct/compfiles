/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2022, Problem 8

Let `n, k ≥ 3` be integers, and let `S` be a circle. Let `n` blue and
`k` red points be chosen uniformly and independently at random on `S`.
Let `F` be the intersection of the convex hulls of the red and blue
points, and `m` the number of vertices of `F` (`m = 0` if `F` is empty).
Find the expected value of `m`.

Answer: `E(m) = 2kn/(n+k-1) - 2·k!·n!/(k+n-1)!`.

NOTE: We phrase the expected value as a combinatorial sum over
equally-likely cyclic color patterns, which for points in generic
position on a circle equals the measure-theoretic expectation.
-/

namespace Imc2022P8

/-- The cyclic successor in `Fin (n + k)` (well-defined when `n + k > 0`). -/
def succ (n k : ℕ) (i : Fin (n + k)) : Fin (n + k) :=
  ⟨(i.val + 1) % (n + k), Nat.mod_lt _ i.pos⟩

/-- Number of color changes in a cyclic colouring. -/
def changes (n k : ℕ) (c : Fin (n + k) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + k) => c i ≠ c (succ n k i))).card

/-- For a pair `(n, k)` and a cyclic colouring `c : Fin (n + k) → Bool`
(`true` = blue, `false` = red) with exactly `n` blue points, let
`mVal n k c` be the number of "color changes" in the cyclic sequence,
minus 2 if the colors form two contiguous arcs (giving the number of
vertices of the convex-hull intersection). -/
def mVal (n k : ℕ) (c : Fin (n + k) → Bool) : ℕ :=
  if changes n k c = 2 then 0 else changes n k c

/-- The set of valid colourings with exactly `n` trues (blue points). -/
def validCols (n k : ℕ) : Finset (Fin (n + k) → Bool) :=
  Finset.univ.filter
    (fun c => (Finset.univ.filter (fun i => c i = true)).card = n)

/-- The set of "two-arc" valid colourings: those with exactly 2 color changes. -/
def twoArcCols (n k : ℕ) : Finset (Fin (n + k) → Bool) :=
  (validCols n k).filter (fun c => changes n k c = 2)

/-- The determined expected value (rational). -/
determine answer (n k : ℕ) : ℚ :=
  (2 * k * n : ℚ) / (n + k - 1) -
    (2 * Nat.factorial k * Nat.factorial n : ℚ) / Nat.factorial (k + n - 1)

/-- Helper: cardinality of `validCols` is the binomial coefficient `C(n+k, n)`.
Proved via bijection with `Finset.powersetCard n Finset.univ`. -/
lemma validCols_card (n k : ℕ) :
    (validCols n k).card = Nat.choose (n + k) n := by
  -- Bijection: c ↦ {i | c i = true}.
  rw [show Nat.choose (n + k) n =
      ((Finset.univ : Finset (Fin (n + k))).powersetCard n).card by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]]
  refine Finset.card_bij (fun c _ => Finset.univ.filter (fun i => c i = true))
    ?_ ?_ ?_
  · intro c hc
    simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hc⟩
  · intro c1 hc1 c2 hc2 heq
    funext i
    have h1 : i ∈ Finset.univ.filter (fun i => c1 i = true) ↔
              i ∈ Finset.univ.filter (fun i => c2 i = true) := by
      simp only [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
    cases h1c : c1 i <;> cases h2c : c2 i
    · rfl
    · exact absurd (h1.mpr h2c) (by simp [h1c])
    · exact absurd (h1.mp h1c) (by simp [h2c])
    · rfl
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
    · simp only [validCols, Finset.mem_filter, Finset.mem_univ, true_and]
      convert hs.2 using 2
      ext i
      simp
    · ext i
      simp

/-- Helper: total color-changes summed over `validCols`.
By double counting (linearity of expectation): each adjacent pair `(i, succ i)`
contributes `2 · C(n+k-2, n-1)` colourings where the two positions differ,
and there are `n+k` such pairs.

TODO: Full proof requires:
- Swap the sums: ∑_c |{i : c i ≠ c (succ i)}| = ∑_i |{c ∈ valid : c i ≠ c (succ i)}|.
- Per i: count valid `c` differing at positions `i, succ i`. By bijection with
  subsets of size n-1 of the n+k-2 remaining positions (twice, for the two
  ordered pairs (true,false), (false,true)), this is `2 · C(n+k-2, n-1)`.
- Sum over n+k positions gives the result. -/
lemma sum_changes (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∑ c ∈ validCols n k, (changes n k c : ℚ) =
      (n + k) * 2 * Nat.choose (n + k - 2) (n - 1) := by
  sorry

/-- Helper: there are exactly `n + k` two-arc colourings (rotations of the
"first n blue, then k red" pattern).

TODO: Bijection between `twoArcCols n k` and `Fin (n+k)`: send `c` to its
unique "first true after a false" position (the start of the blue arc).
The inverse is `j ↦ (fun i => decide ((i.val - j.val) % (n+k) < n))`.
Verifying both directions and the cardinality involves careful arithmetic
modulo `n+k`. -/
lemma twoArcCols_card (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (twoArcCols n k).card = n + k := by
  sorry

/-- The sum of `mVal` over valid colorings equals total color changes minus
twice the number of two-arc colorings. -/
lemma sum_mVal_eq (n k : ℕ) :
    ∑ c ∈ validCols n k, (mVal n k c : ℚ) =
      (∑ c ∈ validCols n k, (changes n k c : ℚ))
        - 2 * (twoArcCols n k).card := by
  -- Split valid cols into those with `changes = 2` and others.
  classical
  have h := Finset.sum_filter_add_sum_filter_not (validCols n k)
    (fun c => changes n k c = 2) (fun c => (mVal n k c : ℚ))
  have h2 := Finset.sum_filter_add_sum_filter_not (validCols n k)
    (fun c => changes n k c = 2) (fun c => (changes n k c : ℚ))
  -- On the `changes = 2` part: mVal = 0; on the rest: mVal = changes.
  have e1 : ∑ c ∈ (validCols n k).filter (fun c => changes n k c = 2),
              (mVal n k c : ℚ) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter] at hc
    simp [mVal, hc.2]
  have e2 : ∑ c ∈ (validCols n k).filter (fun c => ¬ changes n k c = 2),
              (mVal n k c : ℚ) =
            ∑ c ∈ (validCols n k).filter (fun c => ¬ changes n k c = 2),
              (changes n k c : ℚ) := by
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_filter] at hc
    simp [mVal, hc.2]
  -- changes on the `=2` part sums to 2 · #twoArcCols.
  have e3 : ∑ c ∈ (validCols n k).filter (fun c => changes n k c = 2),
              (changes n k c : ℚ) =
            2 * (twoArcCols n k).card := by
    rw [twoArcCols]
    rw [show (2 : ℚ) * ((validCols n k).filter (fun c => changes n k c = 2)).card =
        ∑ _ ∈ (validCols n k).filter (fun c => changes n k c = 2), (2 : ℚ) by
        rw [Finset.sum_const]; ring]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [Finset.mem_filter] at hc
    rw [hc.2]; norm_num
  linarith [h, h2, e1, e2, e3]

problem imc2022_p8 (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    (∑ c ∈ validCols n k, (mVal n k c : ℚ)) / (validCols n k).card =
      answer n k := by
  -- Combine the helper lemmas:
  --   ∑ mVal = (n+k)·2·C(n+k-2,n-1) − 2·(n+k)
  --   |validCols| = C(n+k, n)
  -- Dividing and simplifying yields
  --   2nk/(n+k-1) − 2·n!·k!/(n+k-1)!.
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  rw [sum_mVal_eq, sum_changes n k hn1 hk1, twoArcCols_card n k hn1 hk1,
      validCols_card]
  -- Substitute n = n' + 1, k = k' + 1 to handle natural subtraction cleanly.
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hn' : 2 ≤ n' := by omega
  have hk' : 2 ≤ k' := by omega
  unfold answer
  -- After substitution: n+k = n'+k'+2, n+k-1 = n'+k'+1, n+k-2 = n'+k', n-1 = n', k-1 = k'.
  have e1 : n' + 1 + (k' + 1) - 2 = n' + k' := by omega
  have e3 : n' + 1 - 1 = n' := by omega
  have e4 : (k' + 1 + (n' + 1) - 1) = n' + k' + 1 := by omega
  rw [e1, e3, e4]
  -- Convert C(n'+k'+2, n'+1) and C(n'+k', n') to factorial form.
  have e_choose1 : (Nat.choose (n' + 1 + (k' + 1)) (n' + 1) : ℚ) =
      Nat.factorial (n' + k' + 2) /
        (Nat.factorial (n' + 1) * Nat.factorial (k' + 1)) := by
    have hle : n' + 1 ≤ n' + 1 + (k' + 1) := by omega
    have := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : n' + 1 + (k' + 1) - (n' + 1) = k' + 1 := by omega
    rw [hsub] at this
    have hadd : n' + 1 + (k' + 1) = n' + k' + 2 := by ring
    rw [hadd] at this
    have h1 : (Nat.choose (n' + k' + 2) (n' + 1) * Nat.factorial (n' + 1) *
                Nat.factorial (k' + 1) : ℚ)
              = (Nat.factorial (n' + k' + 2) : ℚ) := by exact_mod_cast this
    have hfn : (Nat.factorial (n' + 1) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_pos _ |>.ne'
    have hfk : (Nat.factorial (k' + 1) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_pos _ |>.ne'
    rw [show n' + 1 + (k' + 1) = n' + k' + 2 from by ring]
    field_simp
    linarith
  have e_choose2 : (Nat.choose (n' + k') n' : ℚ) =
      Nat.factorial (n' + k') /
        (Nat.factorial n' * Nat.factorial k') := by
    have hle : n' ≤ n' + k' := by omega
    have := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : n' + k' - n' = k' := by omega
    rw [hsub] at this
    have h1 : (Nat.choose (n' + k') n' * Nat.factorial n' *
                Nat.factorial k' : ℚ)
              = (Nat.factorial (n' + k') : ℚ) := by exact_mod_cast this
    have hfn : (Nat.factorial n' : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_pos _ |>.ne'
    have hfk : (Nat.factorial k' : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_pos _ |>.ne'
    field_simp
    linarith
  rw [e_choose1, e_choose2]
  -- Factorial identities.
  have hf1 : (Nat.factorial (n' + k' + 2) : ℚ) =
      ((n' : ℚ) + k' + 2) * ((n' : ℚ) + k' + 1) * Nat.factorial (n' + k') := by
    rw [show n' + k' + 2 = (n' + k' + 1) + 1 from rfl, Nat.factorial_succ,
        show n' + k' + 1 = (n' + k') + 1 from rfl, Nat.factorial_succ]
    push_cast; ring
  have hf2 : (Nat.factorial (n' + k' + 1) : ℚ) =
      ((n' : ℚ) + k' + 1) * Nat.factorial (n' + k') := by
    rw [show n' + k' + 1 = (n' + k') + 1 from rfl, Nat.factorial_succ]
    push_cast; ring
  have hf_n : (Nat.factorial (n' + 1) : ℚ) = ((n' : ℚ) + 1) * Nat.factorial n' := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf_k : (Nat.factorial (k' + 1) : ℚ) = ((k' : ℚ) + 1) * Nat.factorial k' := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf1, hf2, hf_n, hf_k]
  -- Positivity facts.
  have hfn_ne : (Nat.factorial n' : ℚ) ≠ 0 :=
    by exact_mod_cast Nat.factorial_pos _ |>.ne'
  have hfk_ne : (Nat.factorial k' : ℚ) ≠ 0 :=
    by exact_mod_cast Nat.factorial_pos _ |>.ne'
  have hfnk_ne : (Nat.factorial (n' + k') : ℚ) ≠ 0 :=
    by exact_mod_cast Nat.factorial_pos _ |>.ne'
  have hn'1 : ((n' : ℚ) + 1) ≠ 0 := by positivity
  have hk'1 : ((k' : ℚ) + 1) ≠ 0 := by positivity
  have hnk_pos : (1 + (n' : ℚ) + k') > 0 := by positivity
  have hnk_ne : (1 + (n' : ℚ) + k') ≠ 0 := ne_of_gt hnk_pos
  have hnk2_pos : ((n' : ℚ) + k' + 2) > 0 := by positivity
  have hnk2_ne : ((n' : ℚ) + k' + 2) ≠ 0 := ne_of_gt hnk2_pos
  -- Push casts everywhere.
  push_cast
  ring_nf
  -- Now everything is in ℚ. Algebra.
  field_simp
  ring

end Imc2022P8
