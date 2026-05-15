/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2024, Problem 6

Prove that for any function `f : ℚ → ℤ`, there exist `a, b, c ∈ ℚ` such that
`a < b < c`, `f(b) ≥ f(a)`, and `f(b) ≥ f(c)`.
-/

namespace Imc2024P6

/-- Key lemma: if `f(0) ≤ f(1)`, then there exist `a < b < c` with `f a ≤ f b`
and `f c ≤ f b`. -/
lemma aux (f : ℚ → ℤ) (hf : f 0 ≤ f 1) :
    ∃ a b c : ℚ, a < b ∧ b < c ∧ f a ≤ f b ∧ f c ≤ f b := by
  by_cases h2 : f 2 ≤ f 1
  · exact ⟨0, 1, 2, by norm_num, by norm_num, hf, h2⟩
  push_neg at h2
  by_cases hA : ∃ x : ℚ, 1 < x ∧ x < 2 ∧ f 2 ≤ f x
  · obtain ⟨x, hx1, hx2, hfx⟩ := hA
    exact ⟨1, x, 2, hx1, hx2, h2.le.trans hfx, hfx⟩
  push_neg at hA
  by_cases hB : ∃ x : ℚ, 1 < x ∧ x < 2 ∧ f x ≤ f 1
  · obtain ⟨x, hx1, hx2, hfx⟩ := hB
    exact ⟨0, 1, x, by norm_num, hx1, hf, hfx⟩
  push_neg at hB
  -- For every x ∈ (1,2), f 1 < f x < f 2, so f x ∈ {f 1 + 1, ..., f 2 - 1}
  -- The rationals 1 + 1/(n+2), n ∈ ℕ, are in (1,2). f takes a value v at
  -- infinitely many of them.
  set r : ℕ → ℚ := fun n => 1 + 1 / (n + 2 : ℚ) with hr_def
  have hr_mem : ∀ n, 1 < r n ∧ r n < 2 := by
    intro n
    refine ⟨?_, ?_⟩
    · show (1 : ℚ) < 1 + 1 / (n + 2 : ℚ)
      have : (0 : ℚ) < 1 / (n + 2 : ℚ) := by positivity
      linarith
    · show (1 + 1 / (n + 2 : ℚ) : ℚ) < 2
      have hn : (0 : ℚ) < n + 2 := by positivity
      have : 1 / (n + 2 : ℚ) < 1 := by
        rw [div_lt_one hn]
        have : (0 : ℚ) ≤ n := by exact_mod_cast Nat.zero_le n
        linarith
      linarith
  have hr_anti : StrictAnti r := by
    intro m n hmn
    show (1 + 1 / (n + 2 : ℚ) : ℚ) < 1 + 1 / (m + 2 : ℚ)
    have hm : (0 : ℚ) < m + 2 := by positivity
    have : (1 : ℚ) / (n + 2) < 1 / (m + 2) :=
      one_div_lt_one_div_of_lt hm (by exact_mod_cast Nat.add_lt_add_right hmn 2)
    linarith
  set g : ℕ → ℤ := fun n => f (r n) with hg_def
  have hg_range : ∀ n, g n ∈ Set.Ioo (f 1) (f 2) := by
    intro n
    exact ⟨hB _ (hr_mem n).1 (hr_mem n).2, hA _ (hr_mem n).1 (hr_mem n).2⟩
  have hg_finite : (Set.range g).Finite :=
    Set.Finite.subset (Set.Ioo (f 1) (f 2)).toFinite (by
      rintro _ ⟨n, rfl⟩; exact hg_range n)
  -- By pigeonhole, some value v is attained by g at infinitely many n.
  have hfiber : ∃ v, (g ⁻¹' {v}).Infinite := by
    by_contra hcon
    push_neg at hcon
    have hcov : (Set.univ : Set ℕ) = ⋃ v ∈ Set.range g, g ⁻¹' {v} := by
      ext n; simp
    apply Set.infinite_univ (α := ℕ)
    rw [hcov]
    exact Set.Finite.biUnion hg_finite (fun v _ => hcon v)
  obtain ⟨v, hv⟩ := hfiber
  -- Pick three distinct naturals in the fiber.
  have hv' : (g ⁻¹' {v}).Infinite := hv
  -- Take the smallest, then smallest greater, then smallest greater than that.
  obtain ⟨n1, hn1⟩ := hv'.nonempty
  set S1 := g ⁻¹' {v} \ {n1}
  have hS1_inf : S1.Infinite := hv'.diff (Set.finite_singleton _)
  obtain ⟨n2, hn2, hn2_ne_n1⟩ := hS1_inf.nonempty
  set S2 := g ⁻¹' {v} \ {n1, n2}
  have hS2_inf : S2.Infinite :=
    hv'.diff ((Set.finite_singleton _).union (Set.finite_singleton _))
  obtain ⟨n3, hn3, hn3_ne⟩ := hS2_inf.nonempty
  -- Now n1, n2, n3 are pairwise distinct and all map to v under g.
  have hgn1 : g n1 = v := hn1
  have hgn2 : g n2 = v := hn2
  have hgn3 : g n3 = v := hn3
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn3_ne
  have hne12 : n1 ≠ n2 := fun h => hn2_ne_n1 h.symm
  have hne13 : n1 ≠ n3 := fun h => hn3_ne (Or.inl h.symm)
  have hne23 : n2 ≠ n3 := fun h => hn3_ne (Or.inr h.symm)
  -- Sort them
  -- Let (m1, m2, m3) be n1, n2, n3 sorted ascending.
  -- Note r is strictly antitone, so r(m3) < r(m2) < r(m1).
  -- We want a < b < c with f a ≤ f b, f c ≤ f b. Since all three f-values equal v,
  -- take a = r(m1) smallest rational, wait r is antitone so largest n gives smallest r.
  -- Let's pick three n's, sort, get three r values (reverse sorted), and use them.
  -- Use max/min.
  set M := max n1 (max n2 n3)
  set m := min n1 (min n2 n3)
  -- Middle is the remaining one.
  -- Actually, easier: just produce three rationals directly.
  -- Since r is strictly antitone, if we pick a = r(max), b = r(mid), c = r(min)
  -- we get a < b < c.
  -- Let's implement: find p, q, s in {n1, n2, n3} with p > q > s.
  -- By a case split on which is largest.
  have hex : ∃ p q s : ℕ, s < q ∧ q < p ∧ g p = v ∧ g q = v ∧ g s = v := by
    rcases lt_trichotomy n1 n2 with h12 | h12 | h12
    · rcases lt_trichotomy n2 n3 with h23 | h23 | h23
      · exact ⟨n3, n2, n1, h12, h23, hgn3, hgn2, hgn1⟩
      · exact absurd h23 hne23
      · rcases lt_trichotomy n1 n3 with h13 | h13 | h13
        · exact ⟨n2, n3, n1, h13, h23, hgn2, hgn3, hgn1⟩
        · exact absurd h13 hne13
        · exact ⟨n2, n1, n3, h13, h12, hgn2, hgn1, hgn3⟩
    · exact absurd h12 hne12
    · rcases lt_trichotomy n1 n3 with h13 | h13 | h13
      · exact ⟨n3, n1, n2, h12, h13, hgn3, hgn1, hgn2⟩
      · exact absurd h13 hne13
      · rcases lt_trichotomy n2 n3 with h23 | h23 | h23
        · exact ⟨n1, n3, n2, h23, h13, hgn1, hgn3, hgn2⟩
        · exact absurd h23 hne23
        · exact ⟨n1, n2, n3, h23, h12, hgn1, hgn2, hgn3⟩
  obtain ⟨p, q, s, hsq, hqp, hgp, hgq, hgs⟩ := hex
  -- Since r is strictly antitone: r p < r q < r s
  have h1 : r p < r q := hr_anti hqp
  have h2' : r q < r s := hr_anti hsq
  -- f (r p) = v = f (r q) = f (r s)
  refine ⟨r p, r q, r s, h1, h2', ?_, ?_⟩
  · show f (r p) ≤ f (r q)
    have := hgp; have := hgq
    simp [g] at hgp hgq
    rw [hgp, hgq]
  · show f (r s) ≤ f (r q)
    simp [g] at hgs hgq
    rw [hgs, hgq]

/-- Main theorem: every function `f : ℚ → ℤ` has `a < b < c` with
`f a ≤ f b` and `f c ≤ f b`. -/
problem imc2024_p6 (f : ℚ → ℤ) :
    ∃ a b c : ℚ, a < b ∧ b < c ∧ f a ≤ f b ∧ f c ≤ f b := by
  by_cases h : f 0 ≤ f 1
  · exact aux f h
  push_neg at h
  -- Apply aux to g(x) = f(1-x)
  have hg : (fun x : ℚ => f (1 - x)) 0 ≤ (fun x : ℚ => f (1 - x)) 1 := by
    simp
    exact h.le
  obtain ⟨a, b, c, hab, hbc, hab', hcb'⟩ := aux (fun x => f (1 - x)) hg
  refine ⟨1 - c, 1 - b, 1 - a, by linarith, by linarith, hcb', hab'⟩

end Imc2024P6
