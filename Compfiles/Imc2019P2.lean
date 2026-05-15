/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2019, Problem 2
(IMC 2019, Day 1, Problem 2)

A four-digit number `YEAR` (with digits `Y`, `E`, `A`, `R`) is called *very good*
if the system
```
  Y x + E y + A z + R w = Y
  R x + Y y + E z + A w = E
  A x + R y + Y z + E w = A
  E x + A y + R z + Y w = R
```
has at least two solutions in `ℝ⁴`. Find all very good years in the 21st century.

The answer is the set
`{2002, 2013, 2020, 2024, 2035, 2046, 2057, 2068, 2079}`.

## Solution outline

The system has at least two solutions iff there exists a solution `(x,y,z,w)`
and a non-zero homogeneous kernel vector `(a,b,c,d)`. Adding equations 1 and 3
(resp. 2 and 4) gives, with `u = a + c`, `v = b + d`:
* `(Y + A) u + (E + R) v = 0`
* `(E + R) u + (Y + A) v = 0`,

while subtracting them, with `p = a - c`, `q = b - d`:
* `(A - Y) p + (R - E) q = 0`
* `(E - R) p + (A - Y) q = 0`.

The first 2×2 system is singular iff `(Y + A)² = (E + R)²`; the second iff
`(A - Y)² + (R - E)² = 0`, i.e. `A = Y` and `E = R`.

For 21st-century years `n ∈ [2001, 2100]`, we always have `Y = 2`, and
`E = 0` whenever `n ≤ 2099`. The case `n = 2100` (where `E = 1`) is handled
separately and is not very good. For `Y = 2`, `E = 0`, the singular condition
becomes `R = A + 2` (giving years `2002, 2013, ..., 2079`) or
`A = 2 ∧ R = 0` (giving year `2020`). In each case we exhibit two distinct
explicit solutions.
-/

namespace Imc2019P2

/-- The system of equations as a single conjunction of four real equalities. -/
def isSolution (Y E A R : ℝ) (x y z w : ℝ) : Prop :=
  Y * x + E * y + A * z + R * w = Y ∧
  R * x + Y * y + E * z + A * w = E ∧
  A * x + R * y + Y * z + E * w = A ∧
  E * x + A * y + R * z + Y * w = R

/-- A four-digit number with digits `Y E A R` is *very good* if the associated
linear system has at least two solutions. -/
def VeryGood (Y E A R : ℝ) : Prop :=
  ∃ x₁ y₁ z₁ w₁ x₂ y₂ z₂ w₂ : ℝ,
    isSolution Y E A R x₁ y₁ z₁ w₁ ∧
    isSolution Y E A R x₂ y₂ z₂ w₂ ∧
    (x₁, y₁, z₁, w₁) ≠ (x₂, y₂, z₂, w₂)

/-- Reading off the four decimal digits of `n` (in order Y E A R). -/
def digitY (n : ℕ) : ℕ := n / 1000
def digitE (n : ℕ) : ℕ := (n / 100) % 10
def digitA (n : ℕ) : ℕ := (n / 10) % 10
def digitR (n : ℕ) : ℕ := n % 10

snip begin

/-- Forward direction: if there are 2 distinct solutions, there is a nontrivial
homogeneous kernel solution. -/
lemma kernel_of_veryGood {Y E A R : ℝ} (h : VeryGood Y E A R) :
    ∃ a b c d : ℝ, ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∧
      Y * a + E * b + A * c + R * d = 0 ∧
      R * a + Y * b + E * c + A * d = 0 ∧
      A * a + R * b + Y * c + E * d = 0 ∧
      E * a + A * b + R * c + Y * d = 0 := by
  obtain ⟨x₁, y₁, z₁, w₁, x₂, y₂, z₂, w₂, hs1, hs2, hne⟩ := h
  obtain ⟨a1, b1, c1, d1⟩ := hs1
  obtain ⟨a2, b2, c2, d2⟩ := hs2
  refine ⟨x₁ - x₂, y₁ - y₂, z₁ - z₂, w₁ - w₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hx, hy, hz, hw⟩
    apply hne
    rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- For digits `Y = 2`, `E = 0`, `0 ≤ A`, `0 ≤ R`, if the system has at least
two solutions then `R = A + 2` or (`A = 2` and `R = 0`). -/
lemma cond_of_veryGood (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (h : VeryGood 2 0 A R) :
    R = A + 2 ∨ (A = 2 ∧ R = 0) := by
  obtain ⟨a, b, c, d, hne, h1, h2, h3, h4⟩ := kernel_of_veryGood h
  -- Set u = a+c, v = b+d, p = a-c, q = b-d.
  set u := a + c with hu_def
  set v := b + d with hv_def
  set p := a - c with hp_def
  set q := b - d with hq_def
  -- Derive the four 2x2 system equations.
  have huv1 : (2 + A) * u + R * v = 0 := by
    show (2 + A) * (a + c) + R * (b + d) = 0
    nlinarith [h1, h3]
  have huv2 : R * u + (2 + A) * v = 0 := by
    show R * (a + c) + (2 + A) * (b + d) = 0
    nlinarith [h2, h4]
  have hpq1 : (A - 2) * p + R * q = 0 := by
    show (A - 2) * (a - c) + R * (b - d) = 0
    nlinarith [h1, h3]
  have hpq2 : -R * p + (A - 2) * q = 0 := by
    show -R * (a - c) + (A - 2) * (b - d) = 0
    nlinarith [h2, h4]
  by_cases huv0 : u = 0 ∧ v = 0
  · -- (u, v) = 0. Then a = -c and b = -d, so (p, q) = (2a, 2b).
    obtain ⟨hu0, hv0⟩ := huv0
    have hac : a = -c := by show a = -c; linarith [hu0]
    have hbd : b = -d := by show b = -d; linarith [hv0]
    have hp_eq : p = 2 * a := by show a - c = 2 * a; linarith
    have hq_eq : q = 2 * b := by show b - d = 2 * b; linarith
    have hcd_ne : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨ha0, hb0⟩
      apply hne
      refine ⟨ha0, hb0, ?_, ?_⟩ <;> linarith
    have hpq_ne : ¬ (p = 0 ∧ q = 0) := by
      rintro ⟨hp0, hq0⟩
      apply hcd_ne
      refine ⟨?_, ?_⟩
      · have : 2 * a = 0 := hp_eq ▸ hp0
        linarith
      · have : 2 * b = 0 := hq_eq ▸ hq0
        linarith
    -- From hpq1, hpq2: ((A-2)^2 + R^2) p = 0 and ((A-2)^2 + R^2) q = 0.
    have hPp : ((A - 2)^2 + R^2) * p = 0 := by
      have e1 : (A - 2) * ((A - 2) * p + R * q) = 0 := by rw [hpq1]; ring
      have e2 : R * (-R * p + (A - 2) * q) = 0 := by rw [hpq2]; ring
      nlinarith [e1, e2]
    have hPq : ((A - 2)^2 + R^2) * q = 0 := by
      have e1 : R * ((A - 2) * p + R * q) = 0 := by rw [hpq1]; ring
      have e2 : (A - 2) * (-R * p + (A - 2) * q) = 0 := by rw [hpq2]; ring
      nlinarith [e1, e2]
    by_cases hP0 : (A - 2)^2 + R^2 = 0
    · right
      have hAm2 : (A - 2)^2 = 0 := by
        nlinarith [sq_nonneg (A - 2), sq_nonneg R]
      have hR2 : R^2 = 0 := by
        nlinarith [sq_nonneg (A - 2), sq_nonneg R]
      refine ⟨?_, ?_⟩
      · have := sq_eq_zero_iff.mp hAm2
        linarith
      · exact sq_eq_zero_iff.mp hR2
    · exfalso
      apply hpq_ne
      refine ⟨?_, ?_⟩
      · rcases mul_eq_zero.mp hPp with h | h
        · exact absurd h hP0
        · exact h
      · rcases mul_eq_zero.mp hPq with h | h
        · exact absurd h hP0
        · exact h
  · -- (u, v) ≠ 0.
    have hQu : ((2 + A)^2 - R^2) * u = 0 := by
      have e1 : (2 + A) * ((2 + A) * u + R * v) = 0 := by rw [huv1]; ring
      have e2 : R * (R * u + (2 + A) * v) = 0 := by rw [huv2]; ring
      nlinarith [e1, e2]
    have hQv : ((2 + A)^2 - R^2) * v = 0 := by
      have e1 : (2 + A) * (R * u + (2 + A) * v) = 0 := by rw [huv2]; ring
      have e2 : R * ((2 + A) * u + R * v) = 0 := by rw [huv1]; ring
      nlinarith [e1, e2]
    by_cases hQ0 : (2 + A)^2 - R^2 = 0
    · -- (2+A)^2 = R^2, A,R ≥ 0, so 2 + A = R.
      left
      have h_pos : 0 ≤ 2 + A := by linarith
      have hsq : (2 + A)^2 = R^2 := by linarith
      -- Use that x, y ≥ 0 and x^2 = y^2 implies x = y.
      have h_factor : (2 + A - R) * (2 + A + R) = 0 := by ring_nf; linarith
      have hsum_pos : 2 + A + R > 0 := by linarith
      have hsum_ne : 2 + A + R ≠ 0 := ne_of_gt hsum_pos
      rcases mul_eq_zero.mp h_factor with h | h
      · linarith
      · exact absurd h hsum_ne
    · -- u = 0 and v = 0, contradicts huv0.
      exfalso
      have hu0 : u = 0 := by
        rcases mul_eq_zero.mp hQu with h | h
        · exact absurd h hQ0
        · exact h
      have hv0 : v = 0 := by
        rcases mul_eq_zero.mp hQv with h | h
        · exact absurd h hQ0
        · exact h
      exact huv0 ⟨hu0, hv0⟩

/-- For year 2100 (digits Y=2, E=1, A=0, R=0), the system has only the trivial
kernel; hence it is not very good. -/
lemma not_veryGood_2100 : ¬ VeryGood 2 1 0 0 := by
  intro h
  obtain ⟨a, b, c, d, hne, h1, h2, h3, h4⟩ := kernel_of_veryGood h
  -- Equations:
  -- h1: 2a + b = 0
  -- h2: 2b + c = 0
  -- h3: 2c + d = 0
  -- h4: a + 2d = 0
  -- Chain: b = -2a, c = -2b = 4a, d = -2c = -8a, a = -2d = 16a → 15a = 0 → a = 0.
  have hb : b = -2 * a := by linarith
  have hc : c = 4 * a := by linarith
  have hd : d = -8 * a := by linarith
  have ha : a = 0 := by linarith
  apply hne
  refine ⟨ha, ?_, ?_, ?_⟩
  · rw [hb, ha]; ring
  · rw [hc, ha]; ring
  · rw [hd, ha]; ring

/-- For `Y = 2, E = 0, R = A + 2`, the system has two distinct solutions. The
particular solution `s = (1/(4(A²+4))) · (A²-8A+4, 3A²-4, A²+8A+4, -A²+12)` and
`s + (1,-1,1,-1)` are both solutions. -/
lemma veryGood_case1 (A : ℝ) (_hA : 0 ≤ A) :
    VeryGood 2 0 A (A + 2) := by
  -- Particular solution: s = (1/(4(A²+4))) * (A²-8A+4, 3A²-4, A²+8A+4, -A²+12)
  set D : ℝ := 4 * (A^2 + 4) with hD_def
  have hD_pos : D > 0 := by rw [hD_def]; positivity
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  refine ⟨(A^2 - 8*A + 4) / D, (3*A^2 - 4) / D, (A^2 + 8*A + 4) / D,
          (-A^2 + 12) / D,
          (A^2 - 8*A + 4) / D + 1, (3*A^2 - 4) / D - 1,
          (A^2 + 8*A + 4) / D + 1, (-A^2 + 12) / D - 1, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [hD_def]; field_simp; ring)
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [hD_def]; field_simp; ring)
  · intro heq
    rw [Prod.mk.injEq] at heq
    have h1 : (A^2 - 8*A + 4) / D = (A^2 - 8*A + 4) / D + 1 := heq.1
    linarith

/-- For `Y = 2, E = 0, A = 2, R = 0`, the system has two distinct solutions.
The particular solution `(1, 0, 0, 0)` and `(1, 0, 0, 0) + (1, 0, -1, 0)` =
`(2, 0, -1, 0)` are both solutions. -/
lemma veryGood_case2 : VeryGood 2 0 2 0 := by
  refine ⟨1, 0, 0, 0, 2, 0, -1, 0, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  · intro heq
    rw [Prod.mk.injEq] at heq
    have : (1 : ℝ) = 2 := heq.1
    linarith

snip end

/-- The set of very good years in the 21st century. -/
determine answer : Finset ℕ :=
  {2002, 2013, 2020, 2024, 2035, 2046, 2057, 2068, 2079}

/-- A four-digit number `n` (interpreted with digits `Y E A R` according to its
decimal expansion) in the 21st century is very good iff `n ∈ answer`. -/
problem imc2019_p2 (n : ℕ) (hn1 : 2001 ≤ n) (hn2 : n ≤ 2100) :
    VeryGood (digitY n) (digitE n) (digitA n) (digitR n) ↔ n ∈ answer := by
  -- digitY n = 2.
  have hY : digitY n = 2 := by unfold digitY; omega
  by_cases h2100 : n = 2100
  · subst h2100
    have hD2 : (digitY 2100 : ℝ) = 2 := by unfold digitY; norm_num
    have hD1 : (digitE 2100 : ℝ) = 1 := by unfold digitE; norm_num
    have hD0a : (digitA 2100 : ℝ) = 0 := by unfold digitA; norm_num
    have hD0r : (digitR 2100 : ℝ) = 0 := by unfold digitR; norm_num
    constructor
    · intro h
      rw [hD2, hD1, hD0a, hD0r] at h
      exact absurd h not_veryGood_2100
    · intro hmem
      exfalso
      simp [answer] at hmem
  · -- n ∈ [2001, 2099]. digitE n = 0.
    have hE : digitE n = 0 := by unfold digitE; omega
    have hA_lt : digitA n < 10 := by unfold digitA; omega
    have hR_lt : digitR n < 10 := by unfold digitR; omega
    have hYR : (digitY n : ℝ) = 2 := by rw [hY]; norm_num
    have hER : (digitE n : ℝ) = 0 := by rw [hE]; norm_num
    rw [hYR, hER]
    have hA_nn : (0 : ℝ) ≤ (digitA n : ℝ) := by positivity
    have hR_nn : (0 : ℝ) ≤ (digitR n : ℝ) := by positivity
    have hAR : n = 2000 + 10 * digitA n + digitR n := by
      unfold digitA digitR; omega
    constructor
    · intro h
      have hcond := cond_of_veryGood _ _ hA_nn hR_nn h
      rcases hcond with hRA | ⟨hAv, hRv⟩
      · -- (R : ℝ) = A + 2.
        have hR_nat : digitR n = digitA n + 2 := by
          have h1 : (digitR n : ℝ) = (digitA n : ℝ) + 2 := hRA
          have h2 : (digitR n : ℝ) = ((digitA n + 2 : ℕ) : ℝ) := by
            push_cast; linarith
          exact_mod_cast h2
        have hA_le : digitA n ≤ 7 := by omega
        have heq : n = 2002 + 11 * digitA n := by omega
        interval_cases (digitA n) <;> (rw [heq]; decide)
      · -- A = 2, R = 0.
        have hAnat : digitA n = 2 := by exact_mod_cast hAv
        have hRnat : digitR n = 0 := by exact_mod_cast hRv
        have hn : n = 2020 := by omega
        rw [hn]; decide
    · intro hmem
      simp only [answer, Finset.mem_insert, Finset.mem_singleton] at hmem
      -- For each year in answer, exhibit two solutions.
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      -- 2002: digitA=0, digitR=2; case 1 with A=0.
      · have hA0 : (digitA 2002 : ℝ) = 0 := by unfold digitA; norm_num
        have hR2 : (digitR 2002 : ℝ) = 2 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 0 2
        have h := veryGood_case1 0 (by norm_num)
        norm_num at h
        exact h
      -- 2013: A=1, R=3
      · have hA0 : (digitA 2013 : ℝ) = 1 := by unfold digitA; norm_num
        have hR2 : (digitR 2013 : ℝ) = 3 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 1 3
        have h := veryGood_case1 1 (by norm_num)
        norm_num at h
        exact h
      -- 2020: A=2, R=0
      · have hA0 : (digitA 2020 : ℝ) = 2 := by unfold digitA; norm_num
        have hR2 : (digitR 2020 : ℝ) = 0 := by unfold digitR; norm_num
        rw [hA0, hR2]
        exact veryGood_case2
      -- 2024: A=2, R=4
      · have hA0 : (digitA 2024 : ℝ) = 2 := by unfold digitA; norm_num
        have hR2 : (digitR 2024 : ℝ) = 4 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 2 4
        have h := veryGood_case1 2 (by norm_num)
        norm_num at h
        exact h
      -- 2035: A=3, R=5
      · have hA0 : (digitA 2035 : ℝ) = 3 := by unfold digitA; norm_num
        have hR2 : (digitR 2035 : ℝ) = 5 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 3 5
        have h := veryGood_case1 3 (by norm_num)
        norm_num at h
        exact h
      -- 2046: A=4, R=6
      · have hA0 : (digitA 2046 : ℝ) = 4 := by unfold digitA; norm_num
        have hR2 : (digitR 2046 : ℝ) = 6 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 4 6
        have h := veryGood_case1 4 (by norm_num)
        norm_num at h
        exact h
      -- 2057: A=5, R=7
      · have hA0 : (digitA 2057 : ℝ) = 5 := by unfold digitA; norm_num
        have hR2 : (digitR 2057 : ℝ) = 7 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 5 7
        have h := veryGood_case1 5 (by norm_num)
        norm_num at h
        exact h
      -- 2068: A=6, R=8
      · have hA0 : (digitA 2068 : ℝ) = 6 := by unfold digitA; norm_num
        have hR2 : (digitR 2068 : ℝ) = 8 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 6 8
        have h := veryGood_case1 6 (by norm_num)
        norm_num at h
        exact h
      -- 2079: A=7, R=9
      · have hA0 : (digitA 2079 : ℝ) = 7 := by unfold digitA; norm_num
        have hR2 : (digitR 2079 : ℝ) = 9 := by unfold digitR; norm_num
        rw [hA0, hR2]
        show VeryGood 2 0 7 9
        have h := veryGood_case1 7 (by norm_num)
        norm_num at h
        exact h

end Imc2019P2
