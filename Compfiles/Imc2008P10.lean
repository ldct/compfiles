/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.Pigeonhole

import ProblemExtraction

problem_file { tags := [.Algebra, .NumberTheory] }

/-!
# International Mathematical Competition 2008, Problem 10
(IMC 2008, Day 2, Problem 4)

Let `f, g ∈ ℤ[x]` be nonconstant polynomials such that `g` divides `f` in `ℤ[x]`.
Prove that if the polynomial `f(x) - 2008` has at least `81` distinct integer
roots, then the degree of `g(x)` is greater than `5`.
-/

namespace Imc2008P10

open Polynomial

snip begin

/-- The finite set of integer divisors of `2008`; it has exactly `16` elements. -/
def divs2008 : Finset ℤ :=
  {1, -1, 2, -2, 4, -4, 8, -8, 251, -251, 502, -502, 1004, -1004, 2008, -2008}

lemma card_divs2008 : divs2008.card = 16 := by
  rfl

lemma mem_divs2008_of_dvd {d : ℤ} (hd : d ∣ 2008) : d ∈ divs2008 := by
  -- `d ∣ 2008` implies `d.natAbs ∣ 2008`.
  have habs_dvd : d.natAbs ∣ (2008 : ℕ) := by
    have h1 : d.natAbs ∣ (2008 : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr hd
    exact h1
  -- Enumerate the positive divisors of 2008.
  have hdivs : ∀ n : ℕ, n ∣ 2008 →
      n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 251 ∨ n = 502 ∨ n = 1004 ∨ n = 2008 := by
    intro n hn
    have hn_mem : n ∈ Nat.divisors 2008 := Nat.mem_divisors.mpr ⟨hn, by norm_num⟩
    have : Nat.divisors 2008 = {1, 2, 4, 8, 251, 502, 1004, 2008} := by native_decide
    rw [this] at hn_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn_mem
    exact hn_mem
  -- Case on `d.natAbs`, and on the sign of `d`.
  obtain h | h | h | h | h | h | h | h := hdivs _ habs_dvd
  all_goals
    · rcases Int.natAbs_eq d with heq | heq
      all_goals
        · rw [heq, h]
          decide

snip end

problem imc2008_p10 (f g : ℤ[X]) (hf : 1 ≤ f.natDegree) (hg : 1 ≤ g.natDegree)
    (hdvd : g ∣ f) (S : Finset ℤ) (hScard : 81 ≤ S.card)
    (hSroots : ∀ a ∈ S, f.eval a = 2008) :
    5 < g.natDegree := by
  -- Step 1: for each a ∈ S, `g.eval a` divides `2008`, hence lies in `divs2008`.
  have hg_vals_mem : ∀ a ∈ S, g.eval a ∈ divs2008 := by
    intro a ha
    obtain ⟨h, rfl⟩ := hdvd
    have heval : g.eval a * h.eval a = 2008 := by
      have := hSroots a ha
      simpa [Polynomial.eval_mul] using this
    have : g.eval a ∣ 2008 := ⟨h.eval a, heval.symm⟩
    exact mem_divs2008_of_dvd this
  -- Step 2: define the map S → divs2008 by evaluating g, and apply pigeonhole.
  -- 16 * 5 = 80 < 81 ≤ #S, so some fiber has > 5 elements.
  have hpigeon :
      ∃ c ∈ divs2008, 5 < (S.filter (fun a => g.eval a = c)).card := by
    have h := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := fun a : ℤ => g.eval a) (s := S) (t := divs2008) hg_vals_mem
      (n := 5) (by
        calc divs2008.card * 5 = 16 * 5 := by rw [card_divs2008]
          _ = 80 := by norm_num
          _ < 81 := by norm_num
          _ ≤ S.card := hScard)
    exact h
  obtain ⟨c, _, hc⟩ := hpigeon
  -- Let T be the fiber: a ∈ S with g.eval a = c. #T ≥ 6.
  set T : Finset ℤ := S.filter (fun a => g.eval a = c) with hT_def
  have hT_card : 6 ≤ T.card := hc
  -- Step 3: every element of T is a root of `g - C c`.
  have hroots : ∀ a ∈ T, (g - C c).eval a = 0 := by
    intro a ha
    rw [hT_def, Finset.mem_filter] at ha
    simp [ha.2]
  -- Step 4: if natDegree (g - C c) < 6, then g - C c = 0 via the "polynomial
  -- with more roots than degree is zero" lemma.
  by_contra hlt
  have hgdeg : g.natDegree ≤ 5 := by omega
  -- Bound natDegree (g - C c) ≤ natDegree g ≤ 5.
  have hgmc_nat_le : (g - C c).natDegree ≤ 5 := by
    have h1 : (g - C c).natDegree ≤ max g.natDegree (C c).natDegree :=
      Polynomial.natDegree_sub_le g (C c)
    have h2 : (C c).natDegree = 0 := natDegree_C c
    rw [h2, max_eq_left (Nat.zero_le _)] at h1
    exact le_trans h1 hgdeg
  have hgmc_zero : g - C c = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (g - C c) T hroots
    exact lt_of_le_of_lt hgmc_nat_le hT_card
  -- Step 5: g = C c is constant, contradicting `1 ≤ g.natDegree`.
  have hgeq : g = C c := by
    have := sub_eq_zero.mp hgmc_zero
    exact this
  have : g.natDegree = 0 := by rw [hgeq]; exact natDegree_C c
  omega

end Imc2008P10
