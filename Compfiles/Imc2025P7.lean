/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 2025, Problem 7

Let `ℤ>0` be the set of positive integers. Find all nonempty subsets
`M ⊆ ℤ>0` satisfying both of the following properties:

  (a) if `x ∈ M`, then `2x ∈ M`,
  (b) if `x, y ∈ M` and `x + y` is even, then `(x + y)/2 ∈ M`.

Answer: `M` is of the form `{(m + k) * d | k ∈ ℕ}` for some positive integer
`m` and positive *odd* integer `d`.
-/

namespace Imc2025P7

/-- The set of "nice" subsets — those of the form `{(m + k) * d | k ∈ ℕ}`
for some positive integer `m` and positive odd integer `d`. -/
determine answer : Set (Set ℕ) :=
  { M | ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ Odd d ∧
    M = { x | ∃ k : ℕ, x = (m + k) * d } }

problem imc2025_p7 (M : Set ℕ) (hMsub : M ⊆ Set.Ioi 0) (hMne : M.Nonempty) :
    M ∈ answer ↔
    ((∀ x ∈ M, 2 * x ∈ M) ∧
     (∀ x ∈ M, ∀ y ∈ M, Even (x + y) → (x + y) / 2 ∈ M)) := by
  constructor
  · -- Forward direction: straightforward computation.
    rintro ⟨m, d, hm, hd, hdOdd, rfl⟩
    refine ⟨?_, ?_⟩
    · -- 2x ∈ M when x ∈ M.
      rintro x ⟨k, rfl⟩
      refine ⟨m + 2 * k, ?_⟩
      ring
    · -- (x + y) / 2 ∈ M when x, y ∈ M and x + y even.
      rintro x ⟨k, rfl⟩ y ⟨l, rfl⟩ heven
      obtain ⟨c, hc⟩ := hdOdd
      subst hc
      -- Now d = 2*c + 1.
      have hkl : Even (k + l) := by
        rcases Nat.even_or_odd (k + l) with he | ho
        · exact he
        · exfalso
          -- (m+k)(2c+1) + (m+l)(2c+1) = (2m+k+l)(2c+1)
          -- 2m+k+l is odd since 2m even and k+l odd; product of odd*odd is odd.
          have h2mkl_odd : Odd (2 * m + (k + l)) := by
            have h2m_even : Even (2 * m) := ⟨m, by ring⟩
            exact Even.add_odd h2m_even ho
          have hd_odd : Odd (2 * c + 1) := ⟨c, rfl⟩
          have hprod_odd : Odd ((2 * m + (k + l)) * (2 * c + 1)) := h2mkl_odd.mul hd_odd
          have heq : (m + k) * (2 * c + 1) + (m + l) * (2 * c + 1)
                   = (2 * m + (k + l)) * (2 * c + 1) := by ring
          rw [heq] at heven
          exact (Nat.not_even_iff_odd.mpr hprod_odd) heven
      obtain ⟨c', hc'⟩ := hkl
      refine ⟨c', ?_⟩
      show ((m + k) * (2 * c + 1) + (m + l) * (2 * c + 1)) / 2 = (m + c') * (2 * c + 1)
      rw [show (m + k) * (2 * c + 1) + (m + l) * (2 * c + 1)
           = (2 * m + (k + l)) * (2 * c + 1) from by ring]
      rw [show k + l = c' + c' from hc']
      rw [show 2 * m + (c' + c') = 2 * (m + c') from by ring]
      rw [show 2 * (m + c') * (2 * c + 1) = 2 * ((m + c') * (2 * c + 1)) from by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)
  · -- Reverse direction: the official solution's argument.
    rintro ⟨hdouble, hhalf⟩
    -- Step 1: closure under addition. x + y = (2x + 2y)/2 ∈ M.
    have hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M := by
      intro x hx y hy
      have h2x : 2 * x ∈ M := hdouble x hx
      have h2y : 2 * y ∈ M := hdouble y hy
      have heven : Even (2 * x + 2 * y) := ⟨x + y, by ring⟩
      have := hhalf _ h2x _ h2y heven
      convert this using 1
      omega
    -- Step 2: closure under multiplication by positive naturals.
    have hmul : ∀ n : ℕ, 0 < n → ∀ x ∈ M, n * x ∈ M := by
      intro n hn x hx
      induction n with
      | zero => exact absurd hn (by omega)
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simpa using hx
        · have : k * x ∈ M := ih hk
          have := hadd _ this _ hx
          convert this using 1; ring
    -- Step 3: M contains an odd number.
    -- Key lemma: if x ∈ M is even, then 3x/2 ∈ M (via (x + 2x)/2 = 3x/2).
    have hhalf3 : ∀ x ∈ M, Even x → 3 * x / 2 ∈ M := by
      intro x hx hxe
      have h2x : 2 * x ∈ M := hdouble x hx
      have hsum_even : Even (x + 2 * x) := by
        obtain ⟨k, hk⟩ := hxe
        exact ⟨k + x, by omega⟩
      have h := hhalf x hx (2 * x) h2x hsum_even
      -- (x + 2x) / 2 = 3x/2
      have : (x + 2 * x) / 2 = 3 * x / 2 := by congr 1; ring
      rwa [this] at h
    -- Iteration: using strong induction on the 2-adic valuation, from any x ∈ M
    -- we derive an odd element in M.
    -- Key: if x ∈ M and x = 2^a * b with b odd, then 3^a * b ∈ M (odd).
    have hstrip : ∀ a b : ℕ, Odd b → 0 < b → 2^a * b ∈ M → 3^a * b ∈ M := by
      intro a
      induction a with
      | zero => intro b _ _ h; simpa using h
      | succ n ih =>
        intro b hb hbpos hx
        -- 2^(n+1) * b = 2 * (2^n * b); apply hhalf3 to get 3 * (2^n * b) / 2 ∈ M
        -- but 2^(n+1) * b is even, so hhalf3 gives 3 * (2^(n+1) * b) / 2 = 3 * 2^n * b ∈ M
        have hxe : Even (2^(n+1) * b) := ⟨2^n * b, by ring⟩
        have h1 : 3 * (2^(n+1) * b) / 2 ∈ M := hhalf3 _ hx hxe
        have heq : 3 * (2^(n+1) * b) / 2 = 2^n * (3 * b) := by
          have : 3 * (2^(n+1) * b) = 2 * (2^n * (3 * b)) := by ring
          rw [this, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
        rw [heq] at h1
        -- Now apply ih to (3*b): 3*b is odd (odd*odd), positive.
        have h3b_odd : Odd (3 * b) := (by decide : Odd 3).mul hb
        have h3b_pos : 0 < 3 * b := by positivity
        have h2 : 3^n * (3 * b) ∈ M := ih _ h3b_odd h3b_pos h1
        have : 3^n * (3 * b) = 3^(n+1) * b := by ring
        rwa [this] at h2
    have hodd_exists : ∃ x ∈ M, Odd x := by
      obtain ⟨x₀, hx₀⟩ := hMne
      have hx₀_pos : 0 < x₀ := hMsub hx₀
      -- Write x₀ = 2^a * b with b odd, b > 0.
      obtain ⟨a, b, hb_odd, hx0_eq⟩ : ∃ a b : ℕ, Odd b ∧ x₀ = 2^a * b := by
        clear hx₀
        -- Strong induction on the positive integer x₀.
        have : ∀ n : ℕ, 0 < n → ∃ a b : ℕ, Odd b ∧ n = 2^a * b := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
            intro hnpos
            rcases Nat.even_or_odd n with he | ho
            · obtain ⟨m, hm⟩ := he
              have hmpos : 0 < m := by omega
              have hm_lt : m < n := by omega
              obtain ⟨a, b, hb, heq⟩ := ih m hm_lt hmpos
              refine ⟨a + 1, b, hb, ?_⟩
              rw [hm, heq]; ring
            · exact ⟨0, n, ho, by simp⟩
        exact this x₀ hx₀_pos
      have hb_pos : 0 < b := by
        rcases Nat.eq_zero_or_pos b with hb0 | hbp
        · subst hb0; simp at hb_odd
        · exact hbp
      have hx_in : 2^a * b ∈ M := hx0_eq ▸ hx₀
      have h3ab : 3^a * b ∈ M := hstrip a b hb_odd hb_pos hx_in
      exact ⟨3^a * b, h3ab, ((by decide : Odd 3).pow).mul hb_odd⟩
    -- Obtain an odd element m₀ of M.
    obtain ⟨m₀, hm₀M, hm₀_odd⟩ := hodd_exists
    have hm₀_pos : 0 < m₀ := hMsub hm₀M
    -- Step 4: Define DSet := positive differences in M, and d := its minimum.
    set DSet : Set ℕ := {n | 0 < n ∧ ∃ a ∈ M, a + n ∈ M} with hDSet
    have hDSet_ne : DSet.Nonempty := by
      refine ⟨m₀, hm₀_pos, m₀, hm₀M, ?_⟩
      rw [show m₀ + m₀ = 2 * m₀ from by ring]; exact hdouble m₀ hm₀M
    set d := sInf DSet with hd_def
    have hd_mem' : d ∈ DSet := Nat.sInf_mem hDSet_ne
    obtain ⟨hd_pos, a₀, ha₀M, ha₀d⟩ := hd_mem'
    have hd_mem : d ∈ DSet := ⟨hd_pos, a₀, ha₀M, ha₀d⟩
    have hd_min : ∀ n ∈ DSet, d ≤ n := fun n hn => Nat.sInf_le hn
    -- Step 5: Closure of DSet under gcd-with-M-element. For n ∈ DSet, m ∈ M, gcd n m ∈ DSet.
    have hgcd_DSet : ∀ n ∈ DSet, ∀ m ∈ M, Nat.gcd n m ∈ DSet := by
      rintro n ⟨hn_pos, b, hbM, hbnM⟩ m hmM
      -- n = (b + n) - b. We use Bezout to write gcd(n, m) = un - vm for suitable u, v ≥ 1.
      -- Equivalently gcd(n, m) = u(b+n) - ub - vm = u(b+n) - (ub + vm). Both u(b+n) ∈ M and ub + vm ∈ M.
      -- Pick u, v ≥ 1 with un = vm + gcd(n, m). Such exist: u = (m / g) + k * (m / g) for suitable shift…
      -- Actually: let g = gcd(n, m). Write n = g * n', m = g * m' with gcd(n', m') = 1.
      -- We want un - vm = g, u, v ≥ 1.
      -- u n' - v m' = 1, with u, v ≥ 1.
      -- Since gcd(n', m') = 1, ∃ u₀ ∈ ℕ with u₀ * n' ≡ 1 (mod m'). So u = u₀ + k m' works for any k.
      -- Then v = (u n' - 1) / m'. For u₀ ≥ 1 and k = 0: u = u₀, v = (u₀ n' - 1)/m'.
      -- We need u ≥ 1: take u = u₀ + m' (so u ≥ m' + 1 ≥ 1). Then u n' = u₀ n' + m' n' ≡ 1 mod m',
      -- so v = (u n' - 1)/m' = (u₀ n' - 1)/m' + n' ≥ n' ≥ 1.
      set g := Nat.gcd n m with hg_def
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hn_pos
      have hg_dvd_n : g ∣ n := Nat.gcd_dvd_left _ _
      have hg_dvd_m : g ∣ m := Nat.gcd_dvd_right _ _
      obtain ⟨n', hn'⟩ := hg_dvd_n
      obtain ⟨m', hm'⟩ := hg_dvd_m
      have hm_pos : 0 < m := hMsub hmM
      have hn'_pos : 0 < n' := by rcases Nat.eq_zero_or_pos n' with h0 | hp
                                  · subst h0; simp at hn'; omega
                                  · exact hp
      have hm'_pos : 0 < m' := by rcases Nat.eq_zero_or_pos m' with h0 | hp
                                  · subst h0; simp at hm'; omega
                                  · exact hp
      have hcop : Nat.Coprime n' m' := by
        unfold Nat.Coprime
        have : Nat.gcd (g * n') (g * m') = g * Nat.gcd n' m' := Nat.gcd_mul_left g n' m'
        rw [← hn', ← hm'] at this
        rw [← hg_def] at this
        have : g = g * Nat.gcd n' m' := this
        have hmul : g * 1 = g * Nat.gcd n' m' := by linarith
        exact (Nat.eq_of_mul_eq_mul_left hg_pos hmul).symm
      -- Bezout: ∃ u₀ ∈ ℕ with u₀ * n' ≡ 1 (mod m'), specifically u₀ = (n')⁻¹ mod m'.
      -- Use Nat.Coprime.gcd_mul_right_cancel or chineseRemainder. Simplest: gcd_eq_gcd_ab gives ZMod approach.
      -- Use ZMod: since gcd n' m' = 1, n' is a unit mod m'.
      -- Concrete: by induction or use Nat.xgcd.
      -- Mathlib has: `Nat.Coprime.exists_pow_eq_one`... hmm. Let's use Int Bezout.
      have hbezout : ∃ u v : ℤ, u * (n' : ℤ) + v * (m' : ℤ) = 1 := by
        have hg1 : Int.gcd (n' : ℤ) (m' : ℤ) = 1 := by
          rw [Int.gcd_natCast_natCast]; exact hcop
        refine ⟨(n' : ℤ).gcdA m', (n' : ℤ).gcdB m', ?_⟩
        have h := Int.gcd_eq_gcd_ab (n' : ℤ) (m' : ℤ)
        rw [hg1] at h
        push_cast at h
        linarith
      obtain ⟨u₁, v₁, huv⟩ := hbezout
      have hm'_one : (1 : ℤ) ≤ m' := by exact_mod_cast hm'_pos
      have hn'_one : (1 : ℤ) ≤ n' := by exact_mod_cast hn'_pos
      let K : ℤ := |u₁| + |v₁| + 2
      have hKpos : (0 : ℤ) ≤ K := by positivity
      have hKge : (2 : ℤ) ≤ K := by
        have h1 : (0 : ℤ) ≤ |u₁| := abs_nonneg _
        have h2 : (0 : ℤ) ≤ |v₁| := abs_nonneg _
        show (2 : ℤ) ≤ |u₁| + |v₁| + 2; linarith
      have hu_new_pos : (1 : ℤ) ≤ u₁ + K * m' := by
        have h1 : -|u₁| ≤ u₁ := neg_abs_le u₁
        have hKm : K ≤ K * m' := by nlinarith
        have : (|u₁| + 1 : ℤ) ≤ K := by
          show (|u₁| + 1 : ℤ) ≤ |u₁| + |v₁| + 2
          have h2 : (0 : ℤ) ≤ |v₁| := abs_nonneg _; linarith
        linarith
      have hv_new_neg : v₁ - K * n' ≤ -1 := by
        have h1 : v₁ ≤ |v₁| := le_abs_self v₁
        have hKn : K ≤ K * n' := by nlinarith
        have : (|v₁| + 1 : ℤ) ≤ K := by
          show (|v₁| + 1 : ℤ) ≤ |u₁| + |v₁| + 2
          have h2 : (0 : ℤ) ≤ |u₁| := abs_nonneg _; linarith
        linarith
      let U := u₁ + K * m'
      let V := -(v₁ - K * n')
      have hU_pos : 1 ≤ U := hu_new_pos
      have hV_pos : 1 ≤ V := by show (1 : ℤ) ≤ -(v₁ - K * n'); linarith
      have hUV_eq : U * (n' : ℤ) - V * (m' : ℤ) = 1 := by
        show (u₁ + K * m') * (n' : ℤ) - (-(v₁ - K * n')) * (m' : ℤ) = 1
        have : (u₁ + K * m') * (n' : ℤ) - (-(v₁ - K * n')) * (m' : ℤ)
             = u₁ * n' + v₁ * m' := by ring
        rw [this, huv]
      -- Now to ℕ: U n' = V m' + 1. So U n' g = V m' g + g. So U * n = V * m + g.
      have hU_nat : ∃ Un : ℕ, (Un : ℤ) = U := ⟨U.toNat, by rw [Int.toNat_of_nonneg]; linarith⟩
      have hV_nat : ∃ Vn : ℕ, (Vn : ℤ) = V := ⟨V.toNat, by rw [Int.toNat_of_nonneg]; linarith⟩
      obtain ⟨Un, hUn⟩ := hU_nat
      obtain ⟨Vn, hVn⟩ := hV_nat
      have hUn_pos : 0 < Un := by have : (1 : ℤ) ≤ Un := hUn ▸ hU_pos; exact_mod_cast this
      have hVn_pos : 0 < Vn := by have : (1 : ℤ) ≤ Vn := hVn ▸ hV_pos; exact_mod_cast this
      have hUVnat : Un * n' = Vn * m' + 1 := by
        have h₁ : (Un : ℤ) * n' = Vn * m' + 1 := by
          rw [hUn, hVn]; linarith [hUV_eq]
        have h₂ : ((Un * n' : ℕ) : ℤ) = ((Vn * m' + 1 : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast h₂
      -- Multiply by g: Un * n = Vn * m + g.
      have hUVg : Un * n = Vn * m + g := by
        have h1 : Un * n = Un * (g * n') := by rw [hn']
        have h2 : Vn * m = Vn * (g * m') := by rw [hm']
        rw [h1, h2]
        have : Un * (g * n') = g * (Un * n') := by ring
        rw [this, hUVnat]
        ring
      -- Now: a := Vn * m + Un * b ∈ M (closure), and a + g = Un * b + Un * n = Un * (b + n) ∈ M.
      -- Difference is g. Wait: we want g = (something in M) - (something in M).
      -- We have Un * (b + n) - (Un * b + Vn * m) = Un * n - Vn * m = g. So
      -- Un * (b + n) ∈ M (closure under multiplication of b+n), and Un * b + Vn * m ∈ M (closure under +).
      have hUbn_M : Un * (b + n) ∈ M := hmul Un hUn_pos _ hbnM
      have hUb_M : Un * b ∈ M := hmul Un hUn_pos _ hbM
      have hVm_M : Vn * m ∈ M := hmul Vn hVn_pos _ hmM
      have hsum_M : Un * b + Vn * m ∈ M := hadd _ hUb_M _ hVm_M
      refine ⟨hg_pos, Un * b + Vn * m, hsum_M, ?_⟩
      -- (Un * b + Vn * m) + g = Un * (b + n).
      have : Un * b + Vn * m + g = Un * (b + n) := by
        have := hUVg; ring_nf; linarith
      rw [this]; exact hUbn_M
    -- Step 6: M ⊆ d·ℕ.
    have hd_dvd : ∀ m ∈ M, d ∣ m := by
      intro m hmM
      have hgmem := hgcd_DSet d hd_mem m hmM
      -- d ≤ gcd d m ≤ d, and gcd d m ∣ d.
      have h_le : d ≤ Nat.gcd d m := hd_min _ hgmem
      have h_dvd : Nat.gcd d m ∣ d := Nat.gcd_dvd_left _ _
      have h_le2 : Nat.gcd d m ≤ d := Nat.le_of_dvd hd_pos h_dvd
      have heq : Nat.gcd d m = d := le_antisymm h_le2 h_le
      rw [← heq]; exact Nat.gcd_dvd_right _ _
    -- Step 7: d is odd.
    have hd_odd : Odd d := by
      have := hd_dvd m₀ hm₀M
      exact Odd.of_dvd_nat hm₀_odd this
    -- Step 8: c := sInf M.
    set c := sInf M with hc_def
    have hc_mem : c ∈ M := Nat.sInf_mem hMne
    have hc_pos : 0 < c := hMsub hc_mem
    have hc_min : ∀ x ∈ M, c ≤ x := fun x hx => Nat.sInf_le hx
    -- Descent: a, a+d ∈ M, c < a ⇒ a - d ∈ M.
    have hdescent : ∀ a ∈ M, a + d ∈ M → c < a → a - d ∈ M := by
      intro a haM hadM hca
      -- Largest x ∈ M with x < a, found by Nat.findGreatest.
      classical
      let x := Nat.findGreatest (fun n => n ∈ M) (a - 1)
      have hx_le : x ≤ a - 1 := Nat.findGreatest_le _
      have hx_lt_a : x < a := by omega
      have hx_M : x ∈ M := by
        apply Nat.findGreatest_spec (P := fun n => n ∈ M) (n := a - 1) (m := c)
        · omega
        · exact hc_mem
      have hx_max : ∀ y, y ≤ a - 1 → y ∈ M → y ≤ x :=
        fun y hy hyM => Nat.le_findGreatest hy hyM
      have hx_max' : ∀ y ∈ M, y < a → y ≤ x := fun y hyM hy => hx_max y (by omega) hyM
      -- x + a is odd: else (x+a)/2 ∈ M and x < (x+a)/2 < a.
      have hx_a_odd : Odd (x + a) := by
        by_contra hne
        rw [Nat.not_odd_iff_even] at hne
        have hmid : (x + a) / 2 ∈ M := hhalf x hx_M a haM hne
        obtain ⟨k, hk⟩ := hne
        have h2k : 2 * k = x + a := by omega
        have hmid_lt : (x + a) / 2 < a := by rw [hk]; omega
        have hmid_gt : x < (x + a) / 2 := by rw [hk]; omega
        have := hx_max' _ hmid hmid_lt
        omega
      -- Hence x + a + d is even (odd + odd).
      have hxad_even : Even (x + a + d) := by
        rcases hd_odd with ⟨q, hq⟩
        rcases hx_a_odd with ⟨p, hp⟩
        refine ⟨p + q + 1, ?_⟩
        omega
      -- M-element midpoint = (x + a + d) / 2.
      have hmid : (x + a + d) / 2 ∈ M := by
        have h1 : x + (a + d) = x + a + d := by ring
        have heven' : Even (x + (a + d)) := h1 ▸ hxad_even
        have := hhalf x hx_M (a + d) hadM heven'
        rwa [h1] at this
      -- Strict bounds: x < (x+a+d)/2 < a + d (since x < a + d).
      have hx_lt_ad : x < a + d := by have := hca; have := hd_pos; omega
      obtain ⟨t, ht⟩ := hxad_even
      have h2t : 2 * t = x + a + d := by omega
      have hmid_eq : (x + a + d) / 2 = t := by rw [ht]; omega
      have ht_M : t ∈ M := by rw [← hmid_eq]; exact hmid
      have hmid_gt : x < t := by have := hd_pos; have := hca; omega
      have hmid_lt : t < a + d := by have := hd_pos; have := hca; omega
      have hd_a : d ∣ a := hd_dvd a haM
      have hd_x : d ∣ x := hd_dvd x hx_M
      have hd_t : d ∣ t := hd_dvd t ht_M
      -- We have x ≤ a - d (strict): x < a, both multiples of d, so x ≤ a - d.
      have hx_le_ad : x ≤ a - d := by
        obtain ⟨xk, hxk⟩ := hd_x
        obtain ⟨ak, hak⟩ := hd_a
        rw [hxk, hak] at hx_lt_a ⊢
        have hxa : xk < ak := Nat.lt_of_mul_lt_mul_left (by linarith : d * xk < d * ak)
        have hxa1 : xk + 1 ≤ ak := hxa
        have h1 : d * (xk + 1) ≤ d * ak := Nat.mul_le_mul_left d hxa1
        have h2 : d * xk + d = d * (xk + 1) := by ring
        omega
      -- t is a multiple of d in [x+1, a+d-1], with d | t, d | a, d | a+d, d | x.
      -- The multiples of d in this range that are also ≤ a + d - 1 and ≥ x + 1:
      -- Since x ≤ a - d, multiples include a - d, a, but a - d ≤ x in fact.
      -- Wait, x ≤ a - d. So x + 1 ≤ a - d + 1. The next multiple of d ≥ x + 1 is at most ?
      -- Actually we have x ≤ a - d (as shown). The multiples of d in (x, a+d) are exactly:
      -- {k * d : x < k * d < a + d}. Since x ≤ a - d, multiples include a - d (if x = a - d-? no, x ≤ a - d
      -- means a - d ≥ x so a - d might equal x or be > x. So a - d is in [x, a+d-1].
      -- If x = a - d, then multiples in (x, a+d) start at a, then a + d. But a + d not strict.
      -- So just {a}.
      -- If x < a - d: multiples in (x, a+d) include {a - d, a} (since a - d > x, a - d < a + d).
      -- Wait but x is the LARGEST M-element < a. We have a - d ∈ ?: is a-d ∈ M? Not necessarily.
      -- a - d need not be in M (yet — we're proving it is!). But it's a multiple of d.
      -- Hmm, x being maximal in M ∩ [0, a-1] doesn't restrict where multiples of d sit.
      -- We need: t (in M, hence in dℕ) lies strictly between x and a+d.
      -- And t is a multiple of d with x < t < a + d. We need t = a.
      -- Actually we DON'T necessarily get t = a from this. We could have t = a - d.
      -- But t ∈ M and t < a, so t ≤ x by maximality. But x < t. Contradiction unless t ≥ a.
      -- t < a + d, so t ∈ [a, a+d-1]. Multiple of d in this range: only a (next is a+d which is excluded).
      -- So t = a.
      have ht_ge_a : a ≤ t := by
        by_contra hlt
        push Not at hlt
        have := hx_max' t ht_M hlt
        omega
      have ht_lt_ad : t < a + d := hmid_lt
      -- t is a multiple of d in [a, a+d-1]. Only a.
      have ht_eq_a : t = a := by
        obtain ⟨tk, htk⟩ := hd_t
        obtain ⟨ak, hak⟩ := hd_a
        rw [htk, hak] at ht_ge_a ht_lt_ad ⊢
        have hdp : 0 < d := hd_pos
        have h1 : ak ≤ tk := Nat.le_of_mul_le_mul_left ht_ge_a hdp
        have h2 : d * tk < d * ak + d := by linarith
        have h3 : tk < ak + 1 := by
          by_contra hlt
          push Not at hlt
          have hh : d * (ak + 1) ≤ d * tk := Nat.mul_le_mul_left d hlt
          have : d * (ak + 1) = d * ak + d := by ring
          omega
        have : tk = ak := by omega
        rw [this]
      -- So x + a + d = 2a, so x = a - d.
      have : x = a - d := by
        have heqab : x + a + d = 2 * a := by rw [← h2t, ht_eq_a]
        omega
      rw [← this]; exact hx_M
    -- Ascent: a - d, a ∈ M ⇒ a + d ∈ M (provided a ≥ d, which is automatic since a ∈ M and d | a).
    have hascent : ∀ a ∈ M, d ≤ a → a - d ∈ M → a + d ∈ M := by
      intro a haM hda hadm
      -- Smallest y ∈ M with y > a. Exists since 2a ∈ M and 2a > a.
      -- We use Nat.find on n ↦ a < n ∧ n ∈ M, with bound n ≤ 2a.
      have h2a_M : 2 * a ∈ M := hdouble a haM
      have ha_pos : 0 < a := hMsub haM
      -- Use Nat.find.
      let Q : ℕ → Prop := fun n => a < n ∧ n ∈ M
      have hQ_dec : DecidablePred Q := Classical.decPred _
      have hQ_ex : ∃ n, Q n := ⟨2 * a, by omega, h2a_M⟩
      let y := @Nat.find Q hQ_dec hQ_ex
      have hy_spec : Q y := @Nat.find_spec Q hQ_dec hQ_ex
      have hy_min : ∀ k, Q k → y ≤ k := fun k hk => @Nat.find_min' Q hQ_dec hQ_ex k hk
      have hy_lt : a < y := hy_spec.1
      have hy_M : y ∈ M := hy_spec.2
      have hy_min' : ∀ k ∈ M, a < k → y ≤ k := fun k hkM hk => hy_min k ⟨hk, hkM⟩
      -- a + y odd (else (a+y)/2 ∈ M, a < (a+y)/2 < y, contradicting minimality).
      have hay_odd : Odd (a + y) := by
        by_contra hne
        rw [Nat.not_odd_iff_even] at hne
        have hmid : (a + y) / 2 ∈ M := hhalf a haM y hy_M hne
        obtain ⟨k, hk⟩ := hne
        have h2k : 2 * k = a + y := by omega
        have hmid_lt : (a + y) / 2 < y := by rw [hk]; omega
        have hmid_gt : a < (a + y) / 2 := by rw [hk]; omega
        have := hy_min' _ hmid hmid_gt
        omega
      -- (a - d + y) is even (= a + y - d, odd - odd = even).
      have hady_even : Even (a - d + y) := by
        rcases hd_odd with ⟨q, hq⟩
        rcases hay_odd with ⟨p, hp⟩
        refine ⟨p - q, ?_⟩
        have : a + y = 2 * p + 1 := hp
        have hd : d = 2 * q + 1 := hq
        -- a - d + y = (a + y) - d = (2p+1) - (2q+1) = 2(p-q). Need p ≥ q, i.e., d ≤ a + y.
        -- d ≤ a, so d ≤ a + y trivially.
        have hpq : q ≤ p := by omega
        omega
      -- Midpoint t' = (a - d + y) / 2 ∈ M.
      have hmid : (a - d + y) / 2 ∈ M := hhalf (a - d) hadm y hy_M hady_even
      obtain ⟨t', ht'⟩ := hady_even
      have h2t' : 2 * t' = a - d + y := by omega
      have hmid_eq : (a - d + y) / 2 = t' := by rw [ht']; omega
      rw [hmid_eq] at hmid
      -- Bounds: a - d < t' < y. (Since a - d < y and 2t' = a-d+y so t' = (a-d+y)/2 strictly.)
      have hmid_gt : a - d < t' := by
        have : a - d < y := by omega
        omega
      have hmid_lt : t' < y := by
        have : a - d < y := by omega
        omega
      -- t' ∈ M, t' > a - d and t' < y. Since y is min above a, t' ≤ a (else t' > a contradicts).
      -- Combined with t' > a - d, and d | t', d | (a-d), d | a: multiples of d in (a-d, a]: just a.
      have hd_t' : d ∣ t' := hd_dvd t' hmid
      have hd_a : d ∣ a := hd_dvd a haM
      have hd_ad : d ∣ (a - d) := by
        obtain ⟨ak, hak⟩ := hd_a
        refine ⟨ak - 1, ?_⟩
        have hdp : 0 < d := hd_pos
        have hak_pos : 0 < ak := by
          rcases Nat.eq_zero_or_pos ak with h | h
          · exfalso; subst h; rw [Nat.mul_zero] at hak; omega
          · exact h
        rw [hak]
        cases ak with
        | zero => omega
        | succ n => simp [Nat.mul_succ]
      have ht'_le_a : t' ≤ a := by
        by_contra hlt
        push Not at hlt
        have := hy_min' t' hmid hlt
        omega
      have ht'_eq_a : t' = a := by
        obtain ⟨tk, htk⟩ := hd_t'
        obtain ⟨ak, hak⟩ := hd_a
        have hdp : 0 < d := hd_pos
        have hak_pos : 0 < ak := by
          rcases Nat.eq_zero_or_pos ak with h | h
          · exfalso; subst h; rw [Nat.mul_zero] at hak; omega
          · exact h
        -- hmid_gt : a - d < t', want to extract: d * ak - d < d * tk.
        rw [htk] at hmid_gt
        -- hmid_gt : a - d < d * tk
        have h_amd : a - d = d * (ak - 1) := by
          rw [hak]
          cases ak with
          | zero => omega
          | succ n => simp [Nat.mul_succ]
        rw [h_amd] at hmid_gt
        -- now hmid_gt : d * (ak - 1) < d * tk
        rw [hak] at ht'_le_a
        rw [htk] at ht'_le_a
        -- ht'_le_a : d * tk ≤ d * ak
        rw [htk, hak]
        have h1 : ak - 1 < tk := Nat.lt_of_mul_lt_mul_left hmid_gt
        have h2 : tk ≤ ak := Nat.le_of_mul_le_mul_left ht'_le_a hdp
        have : tk = ak := by omega
        rw [this]
      -- So 2a = a - d + y, hence y = a + d.
      have hy_eq : y = a + d := by
        have : 2 * a = a - d + y := by rw [← h2t', ht'_eq_a]
        omega
      rw [← hy_eq]; exact hy_M
    -- Step 9: c + d ∈ M (descent from a₀ down to c).
    have hcd_M : c + d ∈ M := by
      have ha₀_ge_c : c ≤ a₀ := hc_min _ ha₀M
      have hd_dvd_a₀c : d ∣ (a₀ - c) := by
        have hd_a₀ := hd_dvd a₀ ha₀M
        have hd_c := hd_dvd c hc_mem
        obtain ⟨p, hp⟩ := hd_a₀
        obtain ⟨q, hq⟩ := hd_c
        refine ⟨p - q, ?_⟩
        have hdp : 0 < d := hd_pos
        have hqp : q ≤ p :=
          Nat.le_of_mul_le_mul_left (by rw [← hp, ← hq]; exact ha₀_ge_c) hdp
        rw [hp, hq]
        rw [Nat.mul_sub]
      obtain ⟨K, hK⟩ := hd_dvd_a₀c
      have ha₀_eq : a₀ = c + K * d := by
        have h1 : a₀ - c = d * K := hK
        have h2 : a₀ = c + d * K := by omega
        rw [h2]; ring
      -- Descend by induction on K.
      have hDes : ∀ k : ℕ, ∀ a ∈ M, a + d ∈ M → c + k * d = a → c + d ∈ M := by
        intro k
        induction k with
        | zero => intro a haM hadM heq
                  simp at heq
                  rw [heq]; exact hadM
        | succ j ih =>
            intro a haM hadM heq
            have ha_gt_c : c < a := by rw [← heq]; have := hd_pos; nlinarith
            have hadM' : (a - d) ∈ M := hdescent a haM hadM ha_gt_c
            have hd_le_a : d ≤ a := by
              have ha_pos : 0 < a := hMsub haM
              have hd_a : d ∣ a := hd_dvd a haM
              exact Nat.le_of_dvd ha_pos hd_a
            have hadd_M : (a - d) + d ∈ M := by
              have hada : (a - d) + d = a := by omega
              rw [hada]; exact haM
            apply ih (a - d) hadM' hadd_M
            have hcj : c + j * d + d = a := by
              have : c + (j + 1) * d = c + j * d + d := by ring
              linarith
            omega
      exact hDes K a₀ ha₀M ha₀d ha₀_eq.symm
    -- Step 10: c + k*d ∈ M for all k by induction (using ascent).
    -- Need to track c + k*d ∈ M and c + (k+1)*d ∈ M jointly.
    have hc_kd_aux : ∀ k : ℕ, c + k * d ∈ M ∧ c + (k + 1) * d ∈ M := by
      intro k
      induction k with
      | zero =>
        refine ⟨?_, ?_⟩
        · simpa using hc_mem
        · simpa using hcd_M
      | succ n ih =>
        obtain ⟨h0, h1⟩ := ih
        refine ⟨h1, ?_⟩
        -- ascent at a = c + (n+1)*d, a - d = c + n*d.
        have ha_sub_eq : c + (n + 1) * d - d = c + n * d := by
          have : c + (n + 1) * d = c + n * d + d := by ring
          omega
        have hd_le_a : d ≤ c + (n + 1) * d := by have := hc_pos; nlinarith
        have h_asc := hascent (c + (n + 1) * d) h1 hd_le_a (ha_sub_eq ▸ h0)
        have heq : c + (n + 1) * d + d = c + (n + 1 + 1) * d := by ring
        rw [heq] at h_asc
        exact h_asc
    have hc_kd : ∀ k : ℕ, c + k * d ∈ M := fun k => (hc_kd_aux k).1
    -- Step 11: M ⊆ {c + k*d : k ∈ ℕ}.
    have hM_sub : ∀ x ∈ M, ∃ k : ℕ, x = c + k * d := by
      intro x hxM
      have hd_x : d ∣ x := hd_dvd x hxM
      have hd_c : d ∣ c := hd_dvd c hc_mem
      have hcx : c ≤ x := hc_min x hxM
      obtain ⟨xk, hxk⟩ := hd_x
      obtain ⟨ck, hck⟩ := hd_c
      have hck_le : ck ≤ xk := by
        have hdp : 0 < d := hd_pos
        exact Nat.le_of_mul_le_mul_left (by rw [← hxk, ← hck]; exact hcx) hdp
      refine ⟨xk - ck, ?_⟩
      -- x = d * xk = d * ck + (xk - ck) * d.
      have h1 : d * xk = d * ck + d * (xk - ck) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      rw [hxk, hck]
      rw [h1]
      ring
    -- Step 12: Conclude with the determine answer.
    -- Need: M = {x | ∃ k : ℕ, x = (m + k) * d } for some m > 0 odd d > 0.
    -- Take m = c / d (so c = m * d), d = d. Need c / d > 0, d odd, d > 0.
    have hd_c : d ∣ c := hd_dvd c hc_mem
    obtain ⟨ck, hck⟩ := hd_c
    have hck_pos : 0 < ck := by
      rcases Nat.eq_zero_or_pos ck with h | h
      · subst h; simp at hck; omega
      · exact h
    refine ⟨ck, d, hck_pos, hd_pos, hd_odd, ?_⟩
    ext x
    constructor
    · intro hxM
      obtain ⟨k, hk⟩ := hM_sub x hxM
      refine ⟨k, ?_⟩
      rw [hk, hck]; ring
    · rintro ⟨k, rfl⟩
      -- x = (ck + k) * d = c + k * d ∈ M.
      have : (ck + k) * d = c + k * d := by rw [hck]; ring
      rw [this]
      exact hc_kd k

end Imc2025P7
