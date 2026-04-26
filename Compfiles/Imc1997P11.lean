/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1997, Problem 11 (Day 2, Problem 5)

Let `X` be a set and let `f : X → X` be a bijection. Show that `f` can be
written as a composition `f = g₁ ∘ g₂` of two involutions `g₁, g₂ : X → X`,
i.e. functions satisfying `g₁ ∘ g₁ = id` and `g₂ ∘ g₂ = id`.

## Solution outline (official)

The orbits of `f` partition `X`; it suffices to handle each orbit separately.

* **Finite orbit of size `n`:** model the orbit as `ZMod n` with `f` acting as
  `k ↦ k + 1`. Take `g₂(k) = -k` and `g₁(k) = 1 - k`. Both are involutions, and
  `g₁(g₂(k)) = 1 - (-k) = 1 + k = f(k)`.

* **Infinite (i.e. `ℤ`-)orbit:** model the orbit as `ℤ` with `f(m) = m + 1`.
  The same formulas `g₂(m) = -m`, `g₁(m) = 1 - m` work.

## Lean formalization

We work directly with `f : Equiv.Perm X`. The key construction is an involution
`τ` ("flip") satisfying `τ ∘ f = f⁻¹ ∘ τ`. Once we have `τ`, the decomposition
is `f = (f ∘ τ) ∘ τ`, with both factors involutions:

* `τ * τ = 1` by construction;
* `(f * τ) * (f * τ) = f * (τ * f) * τ = f * (f⁻¹ * τ) * τ = (f * f⁻¹) * τ * τ = 1`.

To build `τ`, we use the orbit decomposition. We define an equivalence relation
`orbitRel : x ~ y ↔ ∃ n : ℤ, y = f^[n] x`. Choose, via `Quotient.out`, a
representative `r [x]` from each orbit. For each `x`, choose an integer
`idx x ∈ ℤ` with `f^[idx x] (r [x]) = x` (this exists since `x` and `r [x]`
are in the same orbit). Define

  `τ x = f^[-(idx x)] (r [x])`.

Then `τ ∘ τ = id` because the equation holds with `idx (τ x) = -(idx x)`
(modulo the orbit's period in the finite case), and `τ ∘ f = f⁻¹ ∘ τ` because
applying `f` to `x` shifts `idx` by `+1`.

The well-definedness of `τ` modulo finite-orbit period is the technically
delicate point. Concretely, if `f^[a] r = f^[b] r`, we need `f^[-a] r = f^[-b] r`;
this holds because `f^[a-b] r = r` implies `f^[b-a] r = r`.

## Status

Fully proved.
-/

namespace Imc1997P11

open Function

/-- **Reduction lemma.** If there is an involution `τ` on `X` that conjugates
`f` to its inverse, i.e. `τ ∘ f = f⁻¹ ∘ τ`, then `f` is a product of two
involutions, namely `g₁ = f ∘ τ` and `g₂ = τ`. -/
lemma decomposition_from_flip {X : Type*} (f : Equiv.Perm X) (τ : Equiv.Perm X)
    (hτ : τ * τ = 1) (hflip : τ * f = f⁻¹ * τ) :
    ∃ g₁ g₂ : Equiv.Perm X, g₁ * g₁ = 1 ∧ g₂ * g₂ = 1 ∧ f = g₁ * g₂ := by
  refine ⟨f * τ, τ, ?_, hτ, ?_⟩
  · -- (f * τ) * (f * τ) = f * (τ * f) * τ = f * (f⁻¹ * τ) * τ
    --                  = (f * f⁻¹) * (τ * τ) = 1 * 1 = 1
    calc (f * τ) * (f * τ)
        = f * (τ * f) * τ := by group
      _ = f * (f⁻¹ * τ) * τ := by rw [hflip]
      _ = (f * f⁻¹) * (τ * τ) := by group
      _ = 1 * 1 := by rw [mul_inv_cancel, hτ]
      _ = 1 := by group
  · -- f = (f * τ) * τ since τ * τ = 1.
    calc f = f * (τ * τ) := by rw [hτ, mul_one]
      _ = (f * τ) * τ := by group

/-- The orbit equivalence relation for `f`: `x ~ y ↔ ∃ n : ℤ, y = (f^n) x`. -/
def orbitRel {X : Type*} (f : Equiv.Perm X) : Setoid X where
  r x y := ∃ n : ℤ, (f ^ n) x = y
  iseqv := {
    refl := fun x => ⟨0, by simp⟩
    symm := fun ⟨n, hn⟩ => ⟨-n, by rw [zpow_neg, ← hn]; simp⟩
    trans := fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨m + n, by rw [zpow_add]; simp [Equiv.Perm.mul_apply, hn, hm]⟩
  }

/-!
## Existence of the flip involution `τ`

The construction proceeds as follows. Let `Q = Quotient (orbitRel f)`. Choose a
representative `r : Q → X` (e.g. `Quotient.out`), with `r ⟦x⟧ ~ x` for all `x`.

For each `x : X`, choose an integer `idx x` such that `(f ^ idx x) (r ⟦x⟧) = x`.
Define `τ x = (f ^ (-(idx x))) (r ⟦x⟧)`.

Proof of `τ ∘ τ = id`: since `τ x` and `x` lie in the same orbit, `r ⟦τ x⟧ = r ⟦x⟧`.
Now `(f ^ (-(idx x))) (r ⟦x⟧) = τ x`, so `idx (τ x)` and `-(idx x)` differ by
the period of the orbit (`0` for infinite orbits, the orbit size `N` for finite
ones). In either case, `f^[idx (τ x)] r = f^[-(idx x)] r` and consequently
`f^[-(idx (τ x))] r = f^[idx x] r = x`, giving `τ (τ x) = x`.

Proof of `τ ∘ f = f⁻¹ ∘ τ`: `f x` is in the same orbit as `x`, so
`r ⟦f x⟧ = r ⟦x⟧`, and `idx (f x) = idx x + 1` (modulo period). Hence
`τ (f x) = f^[-(idx x + 1)] r = f⁻¹ (f^[-(idx x)] r) = f⁻¹ (τ x)`.

The "modulo period" reasoning is the delicate part; one packages it as: for any
`a, b : ℤ` with `f^[a] (r ⟦x⟧) = f^[b] (r ⟦x⟧)`, also `f^[-a] (r ⟦x⟧) = f^[-b] (r ⟦x⟧)`.
This holds because `f^[a-b] (r ⟦x⟧) = r ⟦x⟧` iff `f^[b-a] (r ⟦x⟧) = r ⟦x⟧`
(invert the equation by applying `f^[-(a-b)]`).
-/

section Flip
variable {X : Type*} (f : Equiv.Perm X)

/-- The "period preservation" lemma: if `f^n` fixes `y`, then so does `f^(-n)`. -/
private lemma fix_neg_of_fix {y : X} {n : ℤ} (h : (f ^ n) y = y) :
    (f ^ (-n)) y = y := by
  have : (f ^ (-n)) ((f ^ n) y) = (f ^ (-n)) y := congrArg _ h
  rw [← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero] at this
  exact this.symm

/-- More generally: if `f^a y = f^b y`, then `f^(-a) y = f^(-b) y`. -/
private lemma neg_eq_of_eq {y : X} {a b : ℤ} (h : (f ^ a) y = (f ^ b) y) :
    (f ^ (-a)) y = (f ^ (-b)) y := by
  -- (f^(b-a)) y = y, so (f^(a-b)) y = y, then translate.
  have h1 : (f ^ (b - a)) y = y := by
    have := congrArg ((f ^ (-a)) ·) h
    simp only at this
    rw [← Equiv.Perm.mul_apply, ← zpow_add, ← Equiv.Perm.mul_apply (f ^ (-a)) (f ^ b),
      ← zpow_add] at this
    rw [show -a + a = 0 from by ring, zpow_zero, Equiv.Perm.one_apply,
      show -a + b = b - a from by ring] at this
    exact this.symm
  have h2 : (f ^ (a - b)) y = y := by
    have := fix_neg_of_fix f h1
    rw [show -(b - a) = a - b from by ring] at this
    exact this
  -- Now compute f^(-a) y = f^(-a) (f^(a-b) y) = f^(-b) y.
  have := congrArg ((f ^ (-a)) ·) h2
  simp only at this
  rw [← Equiv.Perm.mul_apply, ← zpow_add] at this
  rw [show -a + (a - b) = -b from by ring] at this
  exact this.symm

/-- Choice of orbit representative as a function `X → X`. We pick
`r x = Quotient.out ⟦x⟧`. -/
private noncomputable def rep (x : X) : X :=
  Quotient.out (s := orbitRel f) (Quotient.mk (orbitRel f) x)

private lemma rep_orbit (x : X) : ∃ n : ℤ, (f ^ n) (rep f x) = x := by
  have : (Quotient.mk (orbitRel f) (rep f x)) = Quotient.mk (orbitRel f) x := by
    unfold rep
    exact Quotient.out_eq _
  exact Quotient.exact this

private lemma rep_eq_of_orbit {x y : X} (h : ∃ n : ℤ, (f ^ n) x = y) :
    rep f x = rep f y := by
  unfold rep
  congr 1
  exact Quotient.sound h

/-- A choice of integer `idx x` such that `f^(idx x) (rep x) = x`. -/
private noncomputable def idx (x : X) : ℤ :=
  (rep_orbit f x).choose

private lemma idx_spec (x : X) : (f ^ (idx f x)) (rep f x) = x :=
  (rep_orbit f x).choose_spec

/-- The flip function. -/
private noncomputable def tauFun (x : X) : X :=
  (f ^ (-(idx f x))) (rep f x)

private lemma rep_tauFun (x : X) : rep f (tauFun f x) = rep f x := by
  -- tauFun f x = f^(-idx x) (rep x), and (f^(idx x)) (rep x) = x.
  -- So (f^(idx x)) (tauFun f x) = (f^(idx x + -idx x)) (rep x) = rep x.
  -- That gives: rep f x ~ rep f x is reflexive; we want rep ~ tauFun f x.
  -- Use rep_eq_of_orbit with x = tauFun f x, y = x, n = idx x + idx x:
  -- (f^(2 idx x)) (tauFun f x) = (f^(2 idx x - idx x)) (rep x) = (f^(idx x))(rep x) = x.
  have h : (f ^ (2 * idx f x)) (tauFun f x) = x := by
    unfold tauFun
    rw [← Equiv.Perm.mul_apply, ← zpow_add]
    rw [show 2 * idx f x + -(idx f x) = idx f x from by ring]
    exact idx_spec f x
  exact rep_eq_of_orbit f ⟨2 * idx f x, h⟩

/-- Key periodicity: if both `(f^a) r₀ = x` and `(f^b) r₀ = x`, then
`(f^(-a)) r₀ = (f^(-b)) r₀`. -/
private lemma tauFun_well_def (x : X) {a : ℤ}
    (ha : (f ^ a) (rep f x) = x) :
    (f ^ (-a)) (rep f x) = tauFun f x := by
  unfold tauFun
  apply neg_eq_of_eq
  rw [ha, idx_spec]

private lemma tauFun_involutive : Involutive (tauFun f) := by
  intro x
  have hτx : (f ^ (-(idx f x))) (rep f x) = tauFun f x := rfl
  -- We have rep (τ x) = rep x. So idx (τ x) is some integer with
  -- f^(idx (τ x)) (rep x) = τ x. We use tauFun_well_def with a = -(idx x):
  -- (f^(-(-(idx x)))) (rep x) = tauFun (τ x), i.e., (f^(idx x)) (rep x) = tauFun (τ x).
  -- And (f^(idx x)) (rep x) = x. So tauFun (τ x) = x.
  have hrep : rep f (tauFun f x) = rep f x := rep_tauFun f x
  have key : (f ^ (-(-(idx f x)))) (rep f (tauFun f x)) = tauFun f (tauFun f x) := by
    apply tauFun_well_def
    rw [hrep]
    exact hτx
  rw [neg_neg, hrep, idx_spec] at key
  exact key.symm

/-- The flip permutation. -/
private noncomputable def tauPerm : Equiv.Perm X :=
  ⟨tauFun f, tauFun f, tauFun_involutive f, tauFun_involutive f⟩

private lemma tauPerm_apply (x : X) : tauPerm f x = tauFun f x := rfl

private lemma tauPerm_sq : tauPerm f * tauPerm f = 1 := by
  ext x
  simp only [Equiv.Perm.mul_apply, tauPerm_apply, Equiv.Perm.one_apply]
  exact tauFun_involutive f x

/-- The flip property: `τ ∘ f = f⁻¹ ∘ τ`. -/
private lemma tauPerm_flip : tauPerm f * f = f⁻¹ * tauPerm f := by
  ext x
  simp only [Equiv.Perm.mul_apply, tauPerm_apply]
  -- Goal: tauFun f (f x) = f⁻¹ (tauFun f x).
  -- tauFun (f x) = f^(-(idx (f x))) (rep (f x)). rep (f x) = rep x.
  -- We have f^(idx x) (rep x) = x, so f^(idx x + 1) (rep x) = f x.
  -- By tauFun_well_def with a = idx x + 1: f^(-(idx x + 1)) (rep x) = tauFun (f x).
  have hrep : rep f (f x) = rep f x := by
    refine (rep_eq_of_orbit f ⟨1, ?_⟩).symm
    rw [zpow_one]
  have h1 : (f ^ (idx f x + 1)) (rep f x) = f x := by
    rw [show idx f x + 1 = 1 + idx f x from by ring, zpow_add, zpow_one,
        Equiv.Perm.mul_apply, idx_spec]
  have h2 : (f ^ (-(idx f x + 1))) (rep f (f x)) = tauFun f (f x) := by
    apply tauFun_well_def
    rw [hrep]
    exact h1
  rw [hrep] at h2
  -- Now: f⁻¹ (tauFun f x) = f⁻¹ (f^(-(idx x)) (rep x)) = f^(-1) f^(-(idx x)) (rep x)
  --     = f^(-1 + -(idx x)) (rep x) = f^(-(idx x + 1)) (rep x) = tauFun (f x).
  show tauFun f (f x) = f⁻¹ (tauFun f x)
  rw [← h2]
  show (f ^ (-(idx f x + 1))) (rep f x) = f⁻¹ (tauFun f x)
  unfold tauFun
  rw [show -(idx f x + 1) = -1 + -(idx f x) from by ring, zpow_add,
      Equiv.Perm.mul_apply, zpow_neg_one]

end Flip

/-- **Existence of a flip involution.** For any permutation `f`, there is an
involution `τ` such that `τ * f = f⁻¹ * τ`. -/
lemma exists_flip {X : Type*} (f : Equiv.Perm X) :
    ∃ τ : Equiv.Perm X, τ * τ = 1 ∧ τ * f = f⁻¹ * τ :=
  ⟨tauPerm f, tauPerm_sq f, tauPerm_flip f⟩

/-- **IMC 1997, Problem 11.** Every bijection `f : X → X` is a composition of
two involutions. -/
problem imc1997_p11 {X : Type*} (f : X ≃ X) :
    ∃ g₁ g₂ : X ≃ X,
      (∀ x, g₁ (g₁ x) = x) ∧ (∀ x, g₂ (g₂ x) = x) ∧
      (∀ x, f x = g₁ (g₂ x)) := by
  obtain ⟨τ, hτ, hflip⟩ := exists_flip f
  obtain ⟨g₁, g₂, hg₁, hg₂, hfg⟩ := decomposition_from_flip f τ hτ hflip
  refine ⟨g₁, g₂, ?_, ?_, ?_⟩
  · intro x
    have := congrArg (· x) hg₁
    simpa [Equiv.Perm.mul_apply] using this
  · intro x
    have := congrArg (· x) hg₂
    simpa [Equiv.Perm.mul_apply] using this
  · intro x
    have := congrArg (· x) hfg
    simpa [Equiv.Perm.mul_apply] using this

end Imc1997P11
