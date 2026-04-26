/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib
import Mathlib.NumberTheory.FrobeniusNumber

import ProblemExtraction

problem_file { tags := [.Combinatorics, .NumberTheory] }

/-!
# International Mathematical Competition 2000, Problem 7 (Day 2, Problem 1)

For every integer `d ≥ 2`, there exists an integer `N(d)` such that for every
`n ≥ N(d)`, the unit `d`-cube can be partitioned into `n` smaller `d`-cubes.

We formalize this combinatorially. A dissection of the `d`-cube into `k` smaller
cubes can be *refined* into a dissection into `k + (a^d - 1)` smaller cubes by
splitting one of the cubes into `a^d` sub-cubes of equal side (for any `a ≥ 2`).
Starting from the trivial dissection into `1` cube, this means that the set of
achievable cube counts contains `1` and is closed under `n ↦ n + (a^d - 1)` for
all `a ≥ 2`.

The key step: for `d ≥ 2`, both `2^d - 1` and `(2^d - 1)^d - 1` are available as
increments, and they are coprime (since the latter is `≡ -1 (mod 2^d - 1)`).
Hence by the Chicken McNugget / Frobenius theorem, every sufficiently large
integer is expressible as a nonnegative integer combination of these two, which
means every sufficiently large `n` is in the closure.
-/

namespace Imc2000P7

/-- The set of natural numbers `n` such that the unit `d`-cube can be dissected
into `n` smaller cubes. We model this inductively: `1` is dissectable, and if
`n` is dissectable and `a ≥ 2` is an integer, then `n + (a^d - 1)` is
dissectable (obtained by splitting one of the cubes into `a^d` equal pieces). -/
inductive Dissectable (d : ℕ) : ℕ → Prop
  | one : Dissectable d 1
  | refine' {n a : ℕ} (h : Dissectable d n) (ha : 2 ≤ a) :
      Dissectable d (n + (a ^ d - 1))

snip begin

open Nat

/-- For `d ≥ 2` and `m = 2^d - 1`, we have `gcd(m, m^d - 1) = 1`. -/
lemma coprime_pow_sub_one_of_pow {d : ℕ} (hd : 2 ≤ d) :
    Nat.Coprime (2 ^ d - 1) ((2 ^ d - 1) ^ d - 1) := by
  set m := 2 ^ d - 1 with hm
  -- m ≥ 3 since 2^d ≥ 4 for d ≥ 2
  have hm_ge : 3 ≤ m := by
    have h2d : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hm_pos : 0 < m := by omega
  -- m^d ≥ m ≥ 3, so m^d - 1 ≥ 2
  have hmd_ge : m ≤ m ^ d := by
    conv_lhs => rw [show m = m ^ 1 from (pow_one m).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hmd_ge1 : 1 ≤ m ^ d - 1 := by omega
  -- Key: m divides m^d, so gcd(m, m^d - 1) = gcd(m, -1) = 1
  have h_dvd : m ∣ m ^ d := dvd_pow_self m (by omega)
  -- Direct: any common divisor k of m and m^d - 1 divides m^d (since k ∣ m ∣ m^d)
  -- and k ∣ m^d - 1, so k ∣ (m^d) - (m^d - 1) = 1.
  have key : ∀ k : ℕ, k ∣ m → k ∣ (m ^ d - 1) → k ∣ 1 := by
    intro k hk1 hk2
    have hk3 : k ∣ m ^ d := hk1.trans h_dvd
    have : k ∣ (m ^ d - (m ^ d - 1)) := Nat.dvd_sub hk3 hk2
    have heq : m ^ d - (m ^ d - 1) = 1 := by omega
    rwa [heq] at this
  have hgcd : Nat.gcd m (m ^ d - 1) ∣ 1 :=
    key _ (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  exact Nat.dvd_one.mp hgcd

/-- If `Dissectable d n`, then `Dissectable d (n + a^d - 1)` for `a ≥ 2`. -/
lemma Dissectable.refine_pow {d n a : ℕ} (h : Dissectable d n) (ha : 2 ≤ a) :
    Dissectable d (n + (a ^ d - 1)) :=
  Dissectable.refine' h ha

/-- Adding multiples of `m = a^d - 1` (for `a ≥ 2`) to a dissectable count yields a dissectable count. -/
lemma Dissectable.add_mul {d n a : ℕ} (h : Dissectable d n) (ha : 2 ≤ a) (k : ℕ) :
    Dissectable d (n + k * (a ^ d - 1)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have : n + (k + 1) * (a ^ d - 1) = (n + k * (a ^ d - 1)) + (a ^ d - 1) := by ring
    rw [this]
    exact Dissectable.refine' ih ha

/-- If `Dissectable d n` and `k₁ * (a₁^d - 1) + k₂ * (a₂^d - 1)` with `a₁, a₂ ≥ 2`,
then adding that sum yields dissectable. -/
lemma Dissectable.add_two_mul {d n a b k₁ k₂ : ℕ}
    (h : Dissectable d n) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Dissectable d (n + k₁ * (a ^ d - 1) + k₂ * (b ^ d - 1)) := by
  have h1 := Dissectable.add_mul h ha k₁
  exact Dissectable.add_mul h1 hb k₂

/-- From the Chicken McNugget theorem applied to coprime `2^d - 1` and `(2^d - 1)^d - 1`,
every sufficiently large natural number is in the additive submonoid they generate. -/
lemma exists_in_closure {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ k₁ k₂ : ℕ, n = k₁ * (2 ^ d - 1) + k₂ * ((2 ^ d - 1) ^ d - 1) := by
  set m := 2 ^ d - 1 with hm
  set M := m ^ d - 1 with hM
  have hm_ge : 3 ≤ m := by
    have h2d : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hm_gt1 : 1 < m := by omega
  have hM_ge : m ≤ m ^ d := by
    conv_lhs => rw [show m = m ^ 1 from (pow_one m).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hM_gt1 : 1 < M := by
    have : m ^ d ≥ m := hM_ge
    omega
  have hcop : Nat.Coprime m M := coprime_pow_sub_one_of_pow hd
  -- By frobeniusNumber_pair, F = m*M - m - M is not in closure, but everything greater is.
  have hfro := frobeniusNumber_pair hcop hm_gt1 hM_gt1
  rw [frobeniusNumber_iff] at hfro
  -- For k ≥ m*M - m - M + 1, k ∈ closure{m, M}, i.e. k = a*m + b*M
  refine ⟨m * M - m - M + 1, fun n hn => ?_⟩
  have hmem : n ∈ AddSubmonoid.closure ({m, M} : Set ℕ) := by
    apply hfro.2
    omega
  rw [AddSubmonoid.mem_closure_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  simp only [smul_eq_mul] at hab
  exact ⟨a, b, hab.symm⟩

/-- The key lemma: for `d ≥ 2`, all sufficiently large `n` are dissectable. -/
lemma exists_dissectable_ge {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, ∀ n ≥ N, Dissectable d n := by
  obtain ⟨N, hN⟩ := exists_in_closure hd
  refine ⟨N + 1, fun n hn => ?_⟩
  -- n ≥ N + 1, so n - 1 ≥ N, and n - 1 = k₁ * m + k₂ * M
  have hn1 : n - 1 ≥ N := by omega
  have hn_pos : 1 ≤ n := by omega
  obtain ⟨k₁, k₂, heq⟩ := hN (n - 1) hn1
  -- Now n = 1 + k₁ * (2^d - 1) + k₂ * ((2^d - 1)^d - 1)
  -- 1 is dissectable, 2 ≥ 2, and (2^d - 1) ≥ 2 since d ≥ 2
  have h_pow_ge : 2 ≤ 2 ^ d - 1 := by
    have : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  have hdiss : Dissectable d (1 + k₁ * (2 ^ d - 1) + k₂ * ((2 ^ d - 1) ^ d - 1)) :=
    Dissectable.add_two_mul Dissectable.one (a := 2) (by norm_num) h_pow_ge
  have hn_eq : n = 1 + k₁ * (2 ^ d - 1) + k₂ * ((2 ^ d - 1) ^ d - 1) := by
    have : n = 1 + (n - 1) := by omega
    rw [this, heq]; ring
  rw [hn_eq]
  exact hdiss

snip end

/-- The IMC 2000 Problem 7 statement: for every `d ≥ 2`, there exists `N`
such that for all `n ≥ N`, the unit `d`-cube can be partitioned into `n`
smaller cubes (captured combinatorially via `Dissectable`). -/
problem imc2000_p7 :
    ∀ d : ℕ, 2 ≤ d → ∃ N : ℕ, ∀ n ≥ N, Dissectable d n := by
  intro d hd
  exact exists_dissectable_ge hd

end Imc2000P7
