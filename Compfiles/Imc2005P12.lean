/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2005, Problem 12
(Second day, Problem 6)

For `p, q ∈ ℚ` and `r = p + q * √7`, prove there exists a matrix
`![![a, b], ![c, d]] ∈ SL_2(ℤ)` with `![![a,b],![c,d]] ≠ ±I` such that
`(a * r + b) / (c * r + d) = r`.

## Proof outline

* If `q = 0`, then `r = p` is rational. Let `t` be the square of a denominator
  of `p`, so `p * t ∈ ℤ` and `p^2 * t ∈ ℤ`. Take
  `![![1 + p*t, -p^2*t], ![t, 1 - p*t]]`. The determinant is
  `(1 + p*t)(1 - p*t) - (-p^2*t)*t = 1 - p^2*t^2 + p^2*t^2 = 1`, and the
  Möbius image is `((1 + p*t)*p - p^2*t)/(t*p + 1 - p*t) = p / 1 = p = r`.
  This is `± I` only if `t = 0`, which we avoid by taking the denominator
  squared (≥ 1).

* If `q ≠ 0`, let `u*x^2 + v*x + w` be the minimal polynomial of `r` in `ℤ[x]`,
  whose discriminant is `7 * (2*u*q)^2`. Write `Δ := 2*u*q ∈ ℤ`. Setting
  `(a*r+b)/(c*r+d) = r` rearranges to `c*r^2 + (d-a)*r - b = 0`, an integer
  multiple of the minimal polynomial: `c = u*t`, `d - a = v*t`, `b = -w*t`.
  Combined with `a*d - b*c = 1` we get `(a + d)^2 = 4 + 7 * Δ^2 * t^2`. So we
  need an integer Pell solution `s^2 - 7 * Δ^2 * t^2 = 4` with `t ≠ 0`.

  From `(8 + 3*√7)^n = k_n + l_n*√7`, the integer pair `(k_n, l_n)` satisfies
  `k_n^2 - 7 * l_n^2 = 1`. Since `(k_n mod Δ, l_n mod Δ) ∈ (ℤ/Δ)^2` is a
  pigeonhole-finite sequence and `(k_n, l_n)` are determined by recursion
  `(k_{n+1}, l_{n+1}) = (8*k_n + 21*l_n, 3*k_n + 8*l_n)`, the sequence is
  eventually periodic. Since the recursion is invertible mod Δ (its
  determinant is `8^2 - 7*3^2 = 1`), the sequence is purely periodic, and
  some `n ≥ 1` has `l_n ≡ 0 (mod Δ)`. Then `s = 2*k_n`, `t = 2*l_n / Δ` is
  the desired Pell solution; `s, t` are even so `a = (s + v*t) / 2` and
  `d = (s - v*t) / 2` are integers.
-/

namespace Imc2005P12

open Real

-- snip begin

/-- Möbius action: this is the equation we want to satisfy when `c*r + d ≠ 0`. -/
lemma moebius_eq_iff {a b c d : ℤ} {r : ℝ} (hcd : (c : ℝ) * r + d ≠ 0) :
    ((a : ℝ) * r + b) / (c * r + d) = r ↔
      (c : ℝ) * r ^ 2 + (d - a) * r - b = 0 := by
  rw [div_eq_iff hcd]
  constructor
  · intro h; ring_nf; linarith [h]
  · intro h; ring_nf; ring_nf at h; linarith [h]

/-- Rational case: explicit matrix with `c = t` where `t` clears the denominator
of `p`. We choose `t = (denom p)^2 ≥ 1`. -/
lemma exists_matrix_rational (p : ℚ) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∧
      ¬ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) ∧
      ((a : ℝ) * (p : ℝ) + b) / ((c : ℝ) * (p : ℝ) + d) = (p : ℝ) := by
  -- t = (denom p)^2 as integer
  set D : ℤ := (p.den : ℤ) ^ 2 with hD
  -- p * D ∈ ℤ
  have hpD_int : ∃ k : ℤ, (p : ℝ) * (D : ℝ) = (k : ℝ) := by
    refine ⟨p.num * (p.den : ℤ), ?_⟩
    have hden : (p.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.pos.ne'
    have hp : (p : ℝ) = (p.num : ℝ) / (p.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den p).symm
    rw [hp, hD]; push_cast; field_simp
  obtain ⟨P, hP⟩ := hpD_int
  -- p^2 * D ∈ ℤ; in fact p^2 * D = P * (P / D)... use p^2 * D = (p*D) * p? not integer.
  -- Use: p^2 * D = (p*D)^2 / D = P^2 / D where D | P^2 since p.den | P.
  -- Better: p^2 * D = p^2 * (p.den)^2 = (p.num)^2 / 1 since p = p.num / p.den.
  have hPD : ∃ k : ℤ, (p : ℝ)^2 * (D : ℝ) = (k : ℝ) := by
    refine ⟨p.num ^ 2, ?_⟩
    have hden : (p.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.pos.ne'
    have hp : (p : ℝ) = (p.num : ℝ) / (p.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den p).symm
    rw [hp, hD]; push_cast; field_simp
  obtain ⟨P2, hP2⟩ := hPD
  refine ⟨1 + P, -P2, D, 1 - P, ?_, ?_, ?_, ?_⟩
  · -- (1 + P)(1 - P) - (-P2)*D = 1 - P^2 + P2*D
    -- Need P^2 = P2 * D as integers: since (p*D)^2 = P^2 and p^2*D * D = P2*D, both equal p^2*D^2.
    have hcast : ((1 + P : ℤ) : ℝ) * ((1 - P : ℤ) : ℝ) - ((-P2 : ℤ) : ℝ) * ((D : ℤ) : ℝ) = 1 := by
      push_cast
      have : ((P : ℝ))^2 = (P2 : ℝ) * (D : ℝ) := by
        have h1 : ((P : ℝ))^2 = ((p : ℝ) * (D : ℝ))^2 := by rw [hP]
        have h2 : (P2 : ℝ) * (D : ℝ) = (p : ℝ)^2 * (D : ℝ) * (D : ℝ) := by rw [← hP2]
        rw [h1, h2]; ring
      linarith [this]
    exact_mod_cast hcast
  · -- ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1): we have c = D = (p.den)^2 ≥ 1, so c ≠ 0.
    rintro ⟨_, _, hc, _⟩
    have hDpos : 0 < D := by
      rw [hD]; positivity
    omega
  · rintro ⟨_, _, hc, _⟩
    have hDpos : 0 < D := by rw [hD]; positivity
    omega
  · -- Möbius: ((1+P)*p - P2) / (D*p + 1 - P) = p
    -- Numerator = p + P*p - P2. We have P = p*D so P*p = p^2 * D = P2, so num = p.
    -- Denom = D*p + 1 - P = D*p + 1 - D*p = 1.
    have h1 : (D : ℝ) * (p : ℝ) = (P : ℝ) := by linarith [hP]
    have h2 : (P : ℝ) * (p : ℝ) = (P2 : ℝ) := by
      have : ((P : ℝ)) * (p : ℝ) = (p : ℝ) * (D : ℝ) * (p : ℝ) := by rw [hP]
      rw [this]
      have : (p : ℝ) * (D : ℝ) * (p : ℝ) = (p : ℝ)^2 * (D : ℝ) := by ring
      rw [this, hP2]
    have hdenom : ((D : ℤ) : ℝ) * (p : ℝ) + ((1 - P : ℤ) : ℝ) = 1 := by
      push_cast; linarith [h1]
    have hnum : ((1 + P : ℤ) : ℝ) * (p : ℝ) + ((-P2 : ℤ) : ℝ) = (p : ℝ) := by
      push_cast; linarith [h2]
    rw [show ((D : ℤ) : ℝ) * (p : ℝ) + ((1 - P : ℤ) : ℝ) =
          ((D : ℤ) : ℝ) * (p : ℝ) + ((1 - P : ℤ) : ℝ) from rfl,
        hdenom, hnum]
    simp

/-! ## The Pell equation `x^2 - 7 y^2 = 1`

We use the recursion `(k_{n+1}, l_{n+1}) = (8*k_n + 21*l_n, 3*k_n + 8*l_n)`
with seed `(k_0, l_0) = (1, 0)`. -/

/-- The Pell sequence for `x^2 - 7 y^2 = 1`, seeded at `(1, 0)`. -/
def pellSeq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let p := pellSeq n
    (8 * p.1 + 21 * p.2, 3 * p.1 + 8 * p.2)

@[simp] lemma pellSeq_zero : pellSeq 0 = (1, 0) := rfl

@[simp] lemma pellSeq_succ (n : ℕ) :
    pellSeq (n + 1) =
      (8 * (pellSeq n).1 + 21 * (pellSeq n).2,
       3 * (pellSeq n).1 + 8 * (pellSeq n).2) := rfl

lemma pellSeq_pos (n : ℕ) : 0 < (pellSeq n).1 ∧ 0 ≤ (pellSeq n).2 := by
  induction n with
  | zero => simp [pellSeq]
  | succ n ih =>
    simp only [pellSeq_succ]
    refine ⟨?_, ?_⟩
    · linarith [ih.1, ih.2]
    · linarith [ih.1, ih.2]

lemma pellSeq_l_pos (n : ℕ) (hn : 1 ≤ n) : 0 < (pellSeq n).2 := by
  match n, hn with
  | n + 1, _ =>
    simp only [pellSeq_succ]
    have ih := pellSeq_pos n
    linarith [ih.1, ih.2]

lemma pellSeq_norm (n : ℕ) : (pellSeq n).1 ^ 2 - 7 * (pellSeq n).2 ^ 2 = 1 := by
  induction n with
  | zero => simp [pellSeq]
  | succ n ih =>
    simp only [pellSeq_succ]
    ring_nf
    ring_nf at ih
    linarith [ih]

/-- The forward step on (k, l) coordinates. -/
def pellStep (p : ℤ × ℤ) : ℤ × ℤ := (8 * p.1 + 21 * p.2, 3 * p.1 + 8 * p.2)

/-- The inverse step (recall det = 8*8 - 21*3 = 1). -/
def pellStepInv (p : ℤ × ℤ) : ℤ × ℤ := (8 * p.1 - 21 * p.2, -3 * p.1 + 8 * p.2)

@[simp] lemma pellStep_inv_step (p : ℤ × ℤ) : pellStepInv (pellStep p) = p := by
  unfold pellStep pellStepInv
  ext <;> ring

@[simp] lemma pellStep_step_inv (p : ℤ × ℤ) : pellStep (pellStepInv p) = p := by
  unfold pellStep pellStepInv
  ext <;> ring

lemma pellSeq_succ_step (n : ℕ) : pellSeq (n + 1) = pellStep (pellSeq n) := rfl

/-- The Pell sequence reduced mod Δ becomes periodic, hence returns to (1, 0).
For positive Δ, there exists n ≥ 1 with `Δ ∣ l_n` and `(k_n - 1) ≡ 0 mod Δ`. -/
lemma exists_period (Δ : ℤ) (hΔ : Δ ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ Δ ∣ (pellSeq n).2 ∧ Δ ∣ ((pellSeq n).1 - 1) := by
  -- Reduce mod |Δ|: the map pellStep mod Δ is a bijection on
  -- (ℤ/|Δ|)² (det = 64 - 63 = 1, invertible). The sequence on a finite set
  -- under a bijection starting at (1,0) eventually returns to (1,0).
  set m : ℕ := Δ.natAbs with hm
  have hm_pos : 0 < m := Int.natAbs_pos.mpr hΔ
  -- The reduced sequence in ZMod m × ZMod m.
  let red : ℕ → ZMod m × ZMod m := fun n =>
    (((pellSeq n).1 : ZMod m), ((pellSeq n).2 : ZMod m))
  -- ZMod m is finite, so by pigeonhole two values coincide.
  haveI : NeZero m := ⟨hm_pos.ne'⟩
  haveI : Finite (ZMod m × ZMod m) := Finite.instProd
  have hpigeon : ∃ i j : ℕ, i < j ∧ red i = red j := by
    obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite red
    rcases hne.lt_or_gt with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hpigeon
  -- Then red i = red j and i < j. By invertibility, red 0 = red (j - i).
  -- Specifically: for any k ≤ i, applying `pellStepInv` k times to both
  -- pellSeq i and pellSeq j yields pellSeq (i - k) and pellSeq (j - k); after
  -- i steps, we have red 0 = red (j - i).
  have key : ∀ k : ℕ, k ≤ i →
      (((pellSeq (i - k)).1 : ZMod m), ((pellSeq (i - k)).2 : ZMod m)) =
      (((pellSeq (j - k)).1 : ZMod m), ((pellSeq (j - k)).2 : ZMod m)) := by
    intro k hk
    induction k with
    | zero => simpa [red] using heq
    | succ k ih =>
      have hk' : k ≤ i := Nat.le_of_succ_le hk
      have hki : k < i := hk
      have hkj : k < j := lt_of_lt_of_le hki hij.le
      have ih' := ih hk'
      -- (pellSeq (i - k)) = pellStep (pellSeq (i - (k+1)))
      have e1 : pellSeq (i - k) = pellStep (pellSeq (i - (k + 1))) := by
        have : i - k = (i - (k + 1)) + 1 := by omega
        rw [this, pellSeq_succ_step]
      have e2 : pellSeq (j - k) = pellStep (pellSeq (j - (k + 1))) := by
        have : j - k = (j - (k + 1)) + 1 := by omega
        rw [this, pellSeq_succ_step]
      -- Apply pellStepInv: (pellSeq (i-(k+1))) and (pellSeq (j-(k+1))) reduced are equal.
      -- ih' says pellSeq (i-k) ≡ pellSeq (j-k) mod m. By e1, e2, that's
      -- pellStep (pellSeq (i-(k+1))) ≡ pellStep (pellSeq (j-(k+1))) mod m.
      -- pellStep is a polynomial map; the inverse mod m gives equality.
      have h1 : ((pellSeq (i - k)).1 : ZMod m) = ((pellSeq (j - k)).1 : ZMod m) :=
        (Prod.ext_iff.mp ih').1
      have h2 : ((pellSeq (i - k)).2 : ZMod m) = ((pellSeq (j - k)).2 : ZMod m) :=
        (Prod.ext_iff.mp ih').2
      rw [e1, e2] at h1 h2
      -- pellStep (a) = (8a.1 + 21a.2, 3a.1 + 8a.2)
      -- so we have:
      --   8 * X.1 + 21 * X.2 ≡ 8 * Y.1 + 21 * Y.2  mod m
      --   3 * X.1 + 8 * X.2 ≡ 3 * Y.1 + 8 * Y.2  mod m
      -- where X = pellSeq (i-(k+1)), Y = pellSeq (j-(k+1)).
      -- Apply 8 * eq1 - 21 * eq2 to get 64*X.1 + ... - 63*X.1 - ... = X.1 ≡ Y.1.
      -- Apply -3 * eq1 + 8 * eq2 to get X.2 ≡ Y.2.
      have e1' : (8 : ZMod m) * (pellSeq (i - (k+1))).1 + 21 * (pellSeq (i - (k+1))).2 =
                 8 * (pellSeq (j - (k+1))).1 + 21 * (pellSeq (j - (k+1))).2 := by
        have h1' := h1
        unfold pellStep at h1'
        simpa using h1'
      have e2' : (3 : ZMod m) * (pellSeq (i - (k+1))).1 + 8 * (pellSeq (i - (k+1))).2 =
                 3 * (pellSeq (j - (k+1))).1 + 8 * (pellSeq (j - (k+1))).2 := by
        have h2' := h2
        unfold pellStep at h2'
        simpa using h2'
      have h_first :
          (((pellSeq (i - (k+1))).1 : ZMod m)) = (((pellSeq (j - (k+1))).1 : ZMod m)) := by
        have step : (8 : ZMod m) * (8 * (pellSeq (i - (k+1))).1 + 21 * (pellSeq (i - (k+1))).2)
                  - 21 * (3 * (pellSeq (i - (k+1))).1 + 8 * (pellSeq (i - (k+1))).2)
                  = ((pellSeq (i - (k+1))).1 : ZMod m) := by ring
        have step' : (8 : ZMod m) * (8 * (pellSeq (j - (k+1))).1 + 21 * (pellSeq (j - (k+1))).2)
                   - 21 * (3 * (pellSeq (j - (k+1))).1 + 8 * (pellSeq (j - (k+1))).2)
                   = ((pellSeq (j - (k+1))).1 : ZMod m) := by ring
        linear_combination 8 * e1' - 21 * e2' + step - step'
      have h_second :
          (((pellSeq (i - (k+1))).2 : ZMod m)) = (((pellSeq (j - (k+1))).2 : ZMod m)) := by
        have step : -(3 : ZMod m) * (8 * (pellSeq (i - (k+1))).1 + 21 * (pellSeq (i - (k+1))).2)
                  + 8 * (3 * (pellSeq (i - (k+1))).1 + 8 * (pellSeq (i - (k+1))).2)
                  = ((pellSeq (i - (k+1))).2 : ZMod m) := by ring
        have step' : -(3 : ZMod m) * (8 * (pellSeq (j - (k+1))).1 + 21 * (pellSeq (j - (k+1))).2)
                   + 8 * (3 * (pellSeq (j - (k+1))).1 + 8 * (pellSeq (j - (k+1))).2)
                   = ((pellSeq (j - (k+1))).2 : ZMod m) := by ring
        linear_combination -3 * e1' + 8 * e2' + step - step'
      exact Prod.ext h_first h_second
  -- Apply key with k = i: get red 0 = red (j - i)
  have h0 := key i (le_refl i)
  simp only [Nat.sub_self] at h0
  set N := j - i with hN_def
  have hN : 1 ≤ N := by omega
  -- pellSeq 0 = (1, 0); so red N = (1, 0) mod m.
  rw [pellSeq_zero] at h0
  refine ⟨N, hN, ?_, ?_⟩
  · -- Δ ∣ (pellSeq N).2: from red N = (1, 0), so (pellSeq N).2 ≡ 0 mod m.
    have h2 := (Prod.ext_iff.mp h0).2
    simp at h2
    -- h2 : ((pellSeq N).2 : ZMod m) = 0
    have hmod : (m : ℤ) ∣ (pellSeq N).2 := by
      have : ((pellSeq N).2 : ZMod m) = 0 := h2.symm
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
      exact_mod_cast this
    have : Δ ∣ (pellSeq N).2 := by
      rw [hm] at hmod
      exact (Int.natAbs_dvd).mp hmod
    exact this
  · have h1 := (Prod.ext_iff.mp h0).1
    simp at h1
    -- h1 : 1 = ((pellSeq N).1 : ZMod m), so (pellSeq N).1 - 1 ≡ 0 mod m.
    have hmod : (m : ℤ) ∣ ((pellSeq N).1 - 1) := by
      have : (((pellSeq N).1 - 1 : ℤ) : ZMod m) = 0 := by
        push_cast; rw [← h1]; ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    rw [hm] at hmod
    exact (Int.natAbs_dvd).mp hmod

/-- Existence of a nontrivial Pell solution `s^2 - 7 (Δ t)^2 = 4` with `t ≠ 0`,
where moreover `s` and `Δ t` are even and `s ≡ 2 mod Δ`. -/
lemma exists_pell_mod (Δ : ℤ) (hΔ : Δ ≠ 0) :
    ∃ s t : ℤ, t ≠ 0 ∧ s ^ 2 - 7 * (Δ * t) ^ 2 = 4 ∧
      Even s ∧ Even (Δ * t) := by
  obtain ⟨n, hn1, hdvd, hdvd_k⟩ := exists_period Δ hΔ
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨2 * (pellSeq n).1, 2 * t, ?_, ?_, ⟨(pellSeq n).1, by ring⟩, ⟨Δ * t, by ring⟩⟩
  · -- 2 * t ≠ 0: l_n > 0 for n ≥ 1, so Δ * t = l_n ≠ 0, hence t ≠ 0.
    intro ht_zero
    have hl_pos : 0 < (pellSeq n).2 := pellSeq_l_pos n hn1
    have ht0 : t = 0 := by linarith [ht_zero]
    rw [ht0, mul_zero] at ht
    omega
  · -- s^2 - 7(Δ * (2t))^2 = 4 k_n^2 - 4*7*(Δ * t)^2 = 4(k_n^2 - 7 l_n^2) = 4
    have hnorm := pellSeq_norm n
    have hl : (pellSeq n).2 = Δ * t := ht
    have h := pellSeq_norm n
    have hgoal :
        (2 * (pellSeq n).1)^2 - 7 * (Δ * (2 * t))^2
          = 4 * ((pellSeq n).1^2 - 7 * (pellSeq n).2^2) := by
      rw [hl]; ring
    rw [hgoal, hnorm]; ring

-- snip end

/-- The Möbius action on a real number, returning false when `c*r + d = 0`. -/
def Moebius (a b c d : ℤ) (r : ℝ) : Prop :=
  ((a : ℝ) * r + b) / ((c : ℝ) * r + d) = r

problem imc2005_p12 (p q : ℚ) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∧
      ¬ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) ∧
      Moebius a b c d ((p : ℝ) + (q : ℝ) * Real.sqrt 7) := by
  by_cases hq : q = 0
  · -- r = p is rational.
    subst hq
    obtain ⟨a, b, c, d, hdet, hI, hnI, hmoeb⟩ := exists_matrix_rational p
    refine ⟨a, b, c, d, hdet, hI, hnI, ?_⟩
    unfold Moebius
    simp only [Rat.cast_zero, zero_mul, add_zero]
    exact hmoeb
  · -- r = p + q√7 with q ≠ 0.
    -- Set up minimal polynomial: u r² + v r + w = 0 with
    --   u = p₂² q₂², v = -2 p₁ p₂ q₂², w = p₁² q₂² - 7 q₁² p₂²
    -- where p = p₁/p₂, q = q₁/q₂. The discriminant v² - 4uw = 7 Δ² with
    -- Δ = 2 p₂² q₁ q₂.
    set p1 : ℤ := p.num with hp1_def
    set p2 : ℤ := (p.den : ℤ) with hp2_def
    set q1 : ℤ := q.num with hq1_def
    set q2 : ℤ := (q.den : ℤ) with hq2_def
    set u : ℤ := p2 ^ 2 * q2 ^ 2 with hu_def
    set v : ℤ := -2 * p1 * p2 * q2 ^ 2 with hv_def
    set w : ℤ := p1 ^ 2 * q2 ^ 2 - 7 * q1 ^ 2 * p2 ^ 2 with hw_def
    set Δ : ℤ := 2 * p2 ^ 2 * q1 * q2 with hΔ_def
    have hp2_pos : (0 : ℤ) < p2 := by simp [hp2_def]; exact p.pos
    have hq2_pos : (0 : ℤ) < q2 := by simp [hq2_def]; exact q.pos
    have hq1_ne : q1 ≠ 0 := by
      simp only [hq1_def]
      intro hq1
      apply hq
      have hQ : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      rw [hq1] at hQ; simp at hQ; exact hQ
    have hΔ_ne : Δ ≠ 0 := by
      simp only [hΔ_def]
      intro h
      have hp2_ne : p2 ≠ 0 := hp2_pos.ne'
      have hq2_ne : q2 ≠ 0 := hq2_pos.ne'
      have : (2 : ℤ) ≠ 0 := by norm_num
      have : p2^2 ≠ 0 := pow_ne_zero _ hp2_ne
      -- 2 * p2² * q1 * q2 = 0 with all factors nonzero is contradiction.
      have h1 : 2 * p2^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hp2_ne)
      have h2 : 2 * p2^2 * q1 ≠ 0 := mul_ne_zero h1 hq1_ne
      have h3 : 2 * p2^2 * q1 * q2 ≠ 0 := mul_ne_zero h2 hq2_ne
      exact h3 h
    -- The casts: p = p1/p2, q = q1/q2.
    have hp_cast : (p : ℝ) = (p1 : ℝ) / (p2 : ℝ) := by
      simp only [hp1_def, hp2_def]; push_cast
      exact_mod_cast (Rat.num_div_den p).symm
    have hq_cast : (q : ℝ) = (q1 : ℝ) / (q2 : ℝ) := by
      simp only [hq1_def, hq2_def]; push_cast
      exact_mod_cast (Rat.num_div_den q).symm
    set r : ℝ := (p : ℝ) + (q : ℝ) * Real.sqrt 7 with hr_def
    -- Key fact: u * r² + v * r + w = 0.
    have hr_min : (u : ℝ) * r ^ 2 + v * r + w = 0 := by
      rw [hr_def, hp_cast, hq_cast]
      have hp2r : (p2 : ℝ) ≠ 0 := by exact_mod_cast hp2_pos.ne'
      have hq2r : (q2 : ℝ) ≠ 0 := by exact_mod_cast hq2_pos.ne'
      have hsqrt7 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num : (7 : ℝ) ≥ 0)
      simp only [hu_def, hv_def, hw_def]
      push_cast
      field_simp
      ring_nf
      rw [show (Real.sqrt 7) ^ 2 = 7 from hsqrt7]
      ring
    -- Get the Pell solution.
    obtain ⟨s, t, ht_ne, hpell, hs_even, hΔt_even⟩ := exists_pell_mod Δ hΔ_ne
    -- From s,Δt even, we want a + d = s (even) and d - a = vt.
    -- v t even? v = -2*p1*p2*q2² is even. So vt is even, hence s ± vt is even.
    have hv_even : Even v := by
      simp only [hv_def]
      exact ⟨-(p1 * p2 * q2^2), by ring⟩
    obtain ⟨s', hs'⟩ := hs_even -- s = s' + s'
    obtain ⟨v', hv'⟩ := hv_even -- v = v' + v'
    -- a = s' - v' * t, d = s' + v' * t (i.e., a + d = 2s' = s, d - a = 2 v' t = v t).
    set a : ℤ := s' - v' * t with ha_def
    set b : ℤ := -(w * t) with hb_def
    set c : ℤ := u * t with hc_def
    set d : ℤ := s' + v' * t with hd_def
    refine ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩
    · -- ad - bc = (s' - v' t)(s' + v' t) - (-(wt))(ut)
      --        = s'^2 - v'^2 t^2 + uw t^2
      -- Goal: = 1.  We have s = 2s', v = 2v'. So s² - v²t² = 4(s'^2 - v'^2 t^2).
      -- Pell: s² - 7 Δ² t² = 4. And v² - 4uw = 7 Δ² (the discriminant).
      -- Hence s² - v² t² + 4uw t² = s² - (v² - 4uw)t² = s² - 7 Δ² t² = 4.
      -- So s'² - v'² t² + uw t² = 1.
      have hdisc : v ^ 2 - 4 * u * w = 7 * Δ ^ 2 := by
        simp only [hu_def, hv_def, hw_def, hΔ_def]; ring
      have hkey : s ^ 2 - v ^ 2 * t ^ 2 + 4 * u * w * t ^ 2 = 4 := by
        have : s ^ 2 - v ^ 2 * t ^ 2 + 4 * u * w * t ^ 2 = s ^ 2 - (v^2 - 4*u*w) * t ^ 2 := by ring
        rw [this, hdisc]; linarith [hpell]
      have hs'_sq : s ^ 2 = 4 * s' ^ 2 := by rw [hs']; ring
      have hv'_sq : v ^ 2 = 4 * v' ^ 2 := by rw [hv']; ring
      have hkey' : 4 * s' ^ 2 - 4 * v' ^ 2 * t ^ 2 + 4 * u * w * t ^ 2 = 4 := by
        rw [hs'_sq, hv'_sq] at hkey
        linarith [hkey]
      have h4 : 4 * (a * d - b * c) = 4 := by
        simp only [ha_def, hb_def, hc_def, hd_def]
        have : 4 * ((s' - v' * t) * (s' + v' * t) - -(w * t) * (u * t))
             = 4 * s'^2 - 4 * v'^2 * t^2 + 4 * u * w * t^2 := by ring
        linarith [hkey', this]
      linarith [h4]
    · -- ¬ (a=1 ∧ b=0 ∧ c=0 ∧ d=1): c = u*t with u > 0, t ≠ 0, so c ≠ 0.
      rintro ⟨_, _, hc, _⟩
      simp only [hc_def] at hc
      have hu_pos : 0 < u := by
        simp only [hu_def]
        positivity
      have : u * t = 0 := hc
      have : t = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hu_pos.ne'
        · exact h
      exact ht_ne this
    · rintro ⟨_, _, hc, _⟩
      simp only [hc_def] at hc
      have hu_pos : 0 < u := by simp only [hu_def]; positivity
      have : u * t = 0 := hc
      have : t = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hu_pos.ne'
        · exact h
      exact ht_ne this
    · -- Möbius equation: (ar+b)/(cr+d) = r.
      -- We have c r + d ≠ 0 because r is irrational and c,d are rational.
      -- Specifically c*r + d = 0 would mean r = -d/c, but r is irrational (q ≠ 0).
      show ((a : ℝ) * r + b) / ((c : ℝ) * r + d) = r
      have hu_pos : (0 : ℤ) < u := by simp only [hu_def]; positivity
      have hr_irrat : Irrational r := by
        rw [hr_def]
        have h7 : Irrational (Real.sqrt 7) := Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 7)
        -- q * √7 with q ≠ 0 rational and √7 irrational is irrational.
        have hmul : Irrational ((q : ℝ) * Real.sqrt 7) := by
          rw [mul_comm]; exact h7.mul_ratCast hq
        -- p + q*√7 with p rational and q*√7 irrational is irrational.
        exact hmul.ratCast_add p
      have hc_ne : (c : ℝ) ≠ 0 := by
        intro hc0
        have hc_int : c = 0 := by exact_mod_cast hc0
        simp only [hc_def] at hc_int
        rcases mul_eq_zero.mp hc_int with h | h
        · exact hu_pos.ne' h
        · exact ht_ne h
      have hcdr_ne : (c : ℝ) * r + d ≠ 0 := by
        intro hcdr
        -- If c*r + d = 0 with c ≠ 0, then r = -d/c is rational. But r is irrational.
        have hreq : r = -((d : ℝ) / (c : ℝ)) := by
          have : (c : ℝ) * r = -(d : ℝ) := by linarith [hcdr]
          field_simp
          linarith [this]
        apply hr_irrat
        rw [hreq]
        exact ⟨-((d : ℚ) / (c : ℚ)), by push_cast; rfl⟩
      rw [div_eq_iff hcdr_ne]
      -- Goal: a*r + b = r * (c*r + d).
      -- LHS = ar + b. RHS = c r² + d r.
      -- Difference: ar + b - cr² - dr = -(cr² + (d-a)r - b) = -(t * (u r² + v r + w)) = 0.
      -- a = s' - v' * t, d = s' + v' * t. So a + d = 2 s' and d - a = 2 v' t.
      -- Then a r + b - (c r² + d r) = - (c r² + (d-a) r - b)
      --   = - (u t r² + 2 v' t r - (-w t)) ... hmm, but v = 2v', so 2 v' t = v t. Good.
      --   = - t * (u r² + v r + w) = 0 by hr_min.
      have hv_real : (v : ℝ) = 2 * (v' : ℝ) := by
        have : v = v' + v' := hv'
        push_cast [this]; ring
      have heq : (a : ℝ) * r + b - ((c : ℝ) * r ^ 2 + d * r) = -((t : ℝ) * ((u : ℝ) * r^2 + v * r + w)) := by
        simp only [ha_def, hb_def, hc_def, hd_def]
        push_cast
        rw [hv_real]
        ring
      have hgoal : (a : ℝ) * r + b = r * ((c : ℝ) * r + d) := by
        have := heq
        rw [hr_min] at this
        linarith [this]
      linarith [hgoal]

end Imc2005P12
