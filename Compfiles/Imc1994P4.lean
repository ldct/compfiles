/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Eigenspace.Basic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 1994, Problem 4

Let `α ∈ ℝ \ {0}` and `F, G : ℝⁿ → ℝⁿ` be linear maps satisfying
`F ∘ G - G ∘ F = α • F`.

(a) Show that `F^k ∘ G - G ∘ F^k = (α k) • F^k` for all `k ≥ 0`.
(b) Show that there exists `k ≥ 1` with `F^k = 0`.

## Proof outline

(a) Induct on `k`. The base case `k = 0` is trivial; for the inductive step,
`F^(k+1) G - G F^(k+1) = F (F^k G - G F^k) + (FG - GF) F^k
                      = F (αk F^k) + α F · F^k = α(k+1) F^(k+1)`.

(b) Consider the linear endomorphism `L : End(ℝ^n) → End(ℝ^n)` defined by
`L(X) = X G - G X`. By (a), `L(F^k) = αk · F^k`. If `F^k ≠ 0` for all `k ≥ 1`,
then for each `k ≥ 1` the value `αk` is an eigenvalue of `L` with eigenvector `F^k`.
Eigenvectors corresponding to distinct eigenvalues are linearly independent;
since the `αk` are distinct (as `α ≠ 0`), the family `{F^k}_{k ≥ 1}` is linearly
independent in `End(ℝ^n)`. But `End(ℝ^n)` is finite-dimensional, so this is a
contradiction.
-/

namespace Imc1994P4

open Module

snip begin

/-- Part (a) as a lemma: `F^k G - G F^k = (αk) F^k`. -/
lemma commutator_pow {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F G : Module.End ℝ V) (α : ℝ)
    (h : F * G - G * F = α • F) (k : ℕ) :
    F ^ k * G - G * F ^ k = (α * k) • F ^ k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    -- F^(k+1) G - G F^(k+1) = F (F^k G - G F^k) + (FG - GF) F^k
    -- F * (F^k G - G F^k) + (FG - GF) F^k = F F^k G - F G F^k + F G F^k - G F F^k
    --                                    = F F^k G - G F F^k = F^(k+1) G - G F^(k+1)
    have key : F ^ (k+1) * G - G * F ^ (k+1) =
               F * (F ^ k * G - G * F ^ k) + (F * G - G * F) * F ^ k := by
      rw [pow_succ']
      noncomm_ring
    rw [key, ih, h]
    rw [mul_smul_comm, smul_mul_assoc]
    -- Goal: (α * ↑k) • (F * F^k) + α • (F * F^k) = (α * ↑(k+1)) • F^(k+1)
    rw [pow_succ']
    rw [Nat.cast_succ]
    rw [show α * ((k : ℝ) + 1) = α * (k : ℝ) + α from by ring]
    rw [add_smul]

/-- The "ad" linear map: `adRight G (X) = X * G - G * X`. -/
def adRight {V : Type*} [AddCommGroup V] [Module ℝ V] (G : Module.End ℝ V) :
    Module.End ℝ (Module.End ℝ V) where
  toFun X := X * G - G * X
  map_add' X Y := by
    show (X + Y) * G - G * (X + Y) = (X * G - G * X) + (Y * G - G * Y)
    rw [add_mul, mul_add]; abel
  map_smul' c X := by
    show (c • X) * G - G * (c • X) = c • (X * G - G * X)
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]

@[simp] lemma adRight_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G X : Module.End ℝ V) : adRight G X = X * G - G * X := rfl

/-- Part (b) abstracted: any finite-dimensional `ℝ`-module `V` with linear maps
`F, G` satisfying the commutator relation `FG - GF = α • F` and `α ≠ 0` has `F`
nilpotent. -/
lemma end_nilpotent (V : Type*) [AddCommGroup V] [Module ℝ V]
    [Module.Free ℝ V] [Module.Finite ℝ V]
    (F G : Module.End ℝ V) (α : ℝ) (hα : α ≠ 0)
    (h : F * G - G * F = α • F) :
    ∃ k : ℕ, 1 ≤ k ∧ F ^ k = 0 := by
  by_contra hno
  push Not at hno
  -- hno : ∀ k, 1 ≤ k → F^k ≠ 0
  -- For k ≥ 1, F^k is an eigenvector of adRight G with eigenvalue α*k.
  have hHasEV : ∀ k : {k : ℕ // 1 ≤ k},
      (adRight G).HasEigenvector (α * k.val) (F ^ k.val) := by
    intro k
    refine ⟨?_, hno k.val k.property⟩
    rw [Module.End.mem_eigenspace_iff, adRight_apply]
    exact commutator_pow F G α h k.val
  have hμ_inj : Function.Injective (fun k : {k : ℕ // 1 ≤ k} => α * (k.val : ℝ)) := by
    intro a b hab
    apply Subtype.ext
    have h1 : (a.val : ℝ) = b.val := mul_left_cancel₀ hα hab
    exact_mod_cast h1
  let v : {k : ℕ // 1 ≤ k} → Module.End ℝ V := fun k => F ^ k.val
  have hindep : LinearIndependent ℝ v := by
    apply Module.End.eigenvectors_linearIndependent' (adRight G) (fun k => α * k.val) hμ_inj v
    exact hHasEV
  exact Module.Finite.not_linearIndependent_of_infinite v hindep

snip end

variable {n : ℕ}

/-- Part (a). -/
problem imc1994_p4a (F G : Module.End ℝ (Fin n → ℝ)) (α : ℝ)
    (h : F * G - G * F = α • F) (k : ℕ) :
    F ^ k * G - G * F ^ k = (α * k) • F ^ k :=
  commutator_pow F G α h k

/-- Part (b). -/
problem imc1994_p4b (F G : Module.End ℝ (Fin n → ℝ)) (α : ℝ) (hα : α ≠ 0)
    (h : F * G - G * F = α • F) :
    ∃ k : ℕ, 1 ≤ k ∧ F ^ k = 0 := by
  -- Strategy: define L : End(End V) by L(X) = XG - GX. Show L(F^k) = αk · F^k.
  -- If no F^k = 0 for k ≥ 1, the family {F^k}_{k ≥ 1} would be linearly independent
  -- in End(V), which has finite dimension. Contradiction.
  exact end_nilpotent (Fin n → ℝ) F G α hα h

end Imc1994P4
