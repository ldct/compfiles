/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 5

(a) Let `f ∈ C[0,b]` and let `g ∈ C(ℝ)` be periodic with period `b > 0`.
Prove that

  `lim_{n → ∞} ∫₀ᵇ f(x) g(nx) dx = (1/b) (∫₀ᵇ f(x) dx) (∫₀ᵇ g(x) dx)`.

## Proof outline (official solution)

Let `‖g‖₁ = ∫₀ᵇ |g|` and `ω(f, t) = sup{|f(x) - f(y)| : |x - y| ≤ t}`. By
uniform continuity of `f` on the compact interval `[0,b]`, `ω(f, t) → 0` as
`t → 0⁺`.

Split `[0, b]` into `n` equal subintervals `[b(k-1)/n, bk/n]`, `k = 1, …, n`.
On each such subinterval, replace `f(x)` by `f(bk/n)`; the error is at most
`ω(f, b/n) · ∫₀ᵇ |g|`. Using periodicity of `g` (period `b`), a substitution
`u = nx` gives

  `∫_{b(k-1)/n}^{bk/n} g(nx) dx = (1/n) ∫₀ᵇ g(u) du`.

Therefore

  `∫₀ᵇ f(x) g(nx) dx = (1/n) (∑_{k=1}^n f(bk/n)) (∫₀ᵇ g) + O(ω(f, b/n) ‖g‖₁)`.

The first term is a Riemann sum, converging to `(1/b) (∫₀ᵇ f) (∫₀ᵇ g)`, while
the error term tends to `0`.
-/

namespace Imc1994P5

open Filter Topology MeasureTheory intervalIntegral

snip begin

/-- Key substitution lemma: if `g : ℝ → ℝ` is continuous and periodic with
period `b`, and `n : ℕ` is positive, and `k : ℕ`, then
`∫_{kb/n}^{(k+1)b/n} g(n x) dx = (1/n) ∫₀ᵇ g(u) du`. -/
lemma sub_integral_eq (b : ℝ) (g : ℝ → ℝ)
    (hper : Function.Periodic g b)
    (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ∫ x in (k * b / n)..((k + 1) * b / n), g (n * x)
      = (1 / n) * ∫ u in (0:ℝ)..b, g u := by
  -- Substitution u = n x: dx = du/n, x: kb/n → (k+1)b/n  ⇔  u: kb → (k+1)b.
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  -- Use intervalIntegral.integral_comp_mul_left:
  --   ∫ x in a..b, f(c x) dx = c⁻¹ ∫ y in c a..c b, f y dy
  have hcomp := intervalIntegral.integral_comp_mul_left
      (f := g) (a := k * b / n) (b := (k + 1) * b / n) (c := (n : ℝ)) hnR
  -- hcomp : ∫ x in (kb/n)..((k+1)b/n), g (n * x) = n⁻¹ • ∫ y in n*(kb/n)..n*((k+1)b/n), g y
  have hkb : (n : ℝ) * (k * b / n) = k * b := by field_simp
  have hk1b : (n : ℝ) * ((k + 1) * b / n) = (k + 1) * b := by field_simp
  rw [hcomp, hkb, hk1b]
  -- now need: n⁻¹ • ∫ y in (k*b)..((k+1)*b), g y = (1/n) * ∫ y in 0..b, g y
  -- Use periodicity: ∫ over [kb, kb + b] equals ∫ over [0, b].
  have hkb' : ((k : ℝ) + 1) * b = k * b + b := by ring
  rw [hkb']
  have hper_int := hper.intervalIntegral_add_eq (t := (k : ℝ) * b) (s := 0)
  -- hper_int : ∫ x in (k*b)..(k*b + b), g x = ∫ x in 0..(0 + b), g x
  rw [hper_int, zero_add]
  -- now: n⁻¹ • ∫ y in 0..b, g y = (1/n) * ∫ y in 0..b, g y
  rw [smul_eq_mul, one_div]

snip end

problem imc1994_p5
    (b : ℝ) (hb : 0 < b)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 b))
    (hg : Continuous g)
    (hper : ∀ x, g (x + b) = g x) :
    Tendsto (fun n : ℕ => ∫ x in (0:ℝ)..b, f x * g (n * x)) atTop
      (𝓝 ((1 / b) * (∫ x in (0:ℝ)..b, f x) * (∫ x in (0:ℝ)..b, g x))) := by
  -- TODO: full formalization of the official argument:
  --   1. Use compactness of [0,b] + continuity of f to obtain uniform continuity:
  --        for every ε > 0 there is δ > 0 with |f x - f y| < ε whenever
  --        x, y ∈ [0,b], |x - y| < δ.
  --   2. For n large enough that b/n < δ, partition [0, b] into n equal
  --      subintervals I_k = [b(k-1)/n, bk/n].
  --   3. On each I_k use periodicity to compute
  --        ∫_{I_k} g (n x) dx = (1/n) ∫₀ᵇ g(u) du
  --      (substitution u = n x − b (k−1), then periodicity of g with period b
  --       gives g(u + b(k-1)) = g u for the integer shift k-1).
  --   4. Bound |f(x) - f(b k / n)| ≤ ε on I_k, and combine with
  --      ∫₀ᵇ |g(n x)| dx = ∫₀ᵇ |g| (again by periodicity) to control the error.
  --   5. The main term is (1/n) ∑_{k=1}^n f(b k / n) · ∫₀ᵇ g, a Riemann sum
  --      for the continuous function f, converging to
  --      (1/b)(∫₀ᵇ f)(∫₀ᵇ g) as n → ∞.
  --   6. Conclude the limit by ε-δ.
  sorry

end Imc1994P5
