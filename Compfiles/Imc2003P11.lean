/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2003, Problem 11
(IMC 2003, Day 2, Problem 5)

(a) Show that for every function `f : ℚ × ℚ → ℝ` there exists a function
    `g : ℚ → ℝ` such that `f(x, y) ≤ g(x) + g(y)` for all `x, y ∈ ℚ`.

(b) Find a function `f : ℝ × ℝ → ℝ` for which there is no such `g : ℝ → ℝ`.
-/

namespace Imc2003P11

open Set

snip begin

/-- The counterexample for part (b): `f(x, y) = 1/|x - y|` for `x ≠ y`. -/
noncomputable def fCounter : ℝ × ℝ → ℝ := fun p => if p.1 = p.2 then 0 else 1 / |p.1 - p.2|

/-- For any injective `φ : ℚ → ℕ` and `n : ℕ`, the preimage of `Iic n` is finite. -/
lemma finite_preimage_le {φ : ℚ → ℕ} (hφ : Function.Injective φ) (n : ℕ) :
    {q : ℚ | φ q ≤ n}.Finite :=
  Set.Finite.subset (Set.Finite.preimage hφ.injOn (Set.finite_Iic n)) (fun _ hq => hq)

snip end

problem imc2003_p11 :
    (∀ f : ℚ × ℚ → ℝ, ∃ g : ℚ → ℝ, ∀ x y : ℚ, f (x, y) ≤ g x + g y) ∧
    (∃ f : ℝ × ℝ → ℝ, ¬ ∃ g : ℝ → ℝ, ∀ x y : ℝ, f (x, y) ≤ g x + g y) := by
  refine ⟨?_, fCounter, ?_⟩
  · -- Part (a).
    intro f
    classical
    obtain ⟨φ, hφ⟩ := (inferInstance : Countable ℚ).exists_injective_nat
    have hfin : ∀ n, {q : ℚ | φ q ≤ n}.Finite := finite_preimage_le hφ
    -- Define T(n) as the Finset of q : ℚ with φ q ≤ n.
    set T : ℕ → Finset ℚ := fun n => (hfin n).toFinset with hT_def
    have hT_mem : ∀ q n, q ∈ T n ↔ φ q ≤ n := by
      intro q n
      simp [hT_def]
    -- g(x) is the sup of |f| on T (φ x) × T (φ x). Nonempty witness: (x, x).
    set g : ℚ → ℝ := fun x =>
      ((T (φ x) ×ˢ T (φ x)).image (fun p : ℚ × ℚ => |f p|)).sup'
        (by
          refine ⟨|f (x, x)|, Finset.mem_image.mpr ⟨(x, x), ?_, rfl⟩⟩
          refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;> exact (hT_mem x _).mpr le_rfl) id with hg_def
    refine ⟨g, ?_⟩
    -- g q ≥ |f (q, q)| ≥ 0.
    have hg_abs_ge : ∀ q a b : ℚ, φ a ≤ φ q → φ b ≤ φ q → |f (a, b)| ≤ g q := by
      intro q a b ha hb
      have hmem_ab : (a, b) ∈ T (φ q) ×ˢ T (φ q) := Finset.mem_product.mpr
        ⟨(hT_mem a _).mpr ha, (hT_mem b _).mpr hb⟩
      have hmem_img : |f (a, b)| ∈ (T (φ q) ×ˢ T (φ q)).image (fun p : ℚ × ℚ => |f p|) :=
        Finset.mem_image.mpr ⟨(a, b), hmem_ab, rfl⟩
      have := Finset.le_sup' (f := id) hmem_img
      simpa [hg_def] using this
    have hg_nn : ∀ q, 0 ≤ g q := fun q =>
      le_trans (abs_nonneg (f (q, q))) (hg_abs_ge q q q le_rfl le_rfl)
    intro x y
    have hxy_abs : f (x, y) ≤ |f (x, y)| := le_abs_self _
    rcases le_or_gt (φ y) (φ x) with hxy | hxy
    · have h := hg_abs_ge x x y le_rfl hxy
      linarith [hg_nn y]
    · have h := hg_abs_ge y x y (le_of_lt hxy) le_rfl
      linarith [hg_nn x]
  · -- Part (b): counterexample.
    rintro ⟨g, hg⟩
    have hg' : ∀ x y : ℝ, x ≠ y → 1 / |x - y| ≤ g x + g y := by
      intro x y hxy
      have h := hg x y
      simp only [fCounter] at h
      rwa [if_neg hxy] at h
    -- A_k = {x : g x ≤ k}. For k ≥ 1, A_k is 1/(2k)-separated.
    -- A (1/(2k))-separated subset of ℝ is countable (inj into ℤ via ⌊2k·x⌋).
    -- Since ℝ = ⋃_k A_k, we'd get ℝ countable. Contradiction.
    have hcount : ∀ k : ℕ, 1 ≤ k → {x : ℝ | g x ≤ (k : ℝ)}.Countable := by
      intro k hk
      set A : Set ℝ := {x : ℝ | g x ≤ (k : ℝ)}
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
      have h2k_pos : (0 : ℝ) < 2 * k := by linarith
      have hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (1 : ℝ) / (2 * k) ≤ |x - y| := by
        intro x hx y hy hxy
        have h1 : 1 / |x - y| ≤ g x + g y := hg' x y hxy
        have h2 : g x + g y ≤ 2 * k := by
          simp only [A, mem_setOf_eq] at hx hy; linarith
        have h_abs_pos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
        rw [div_le_iff₀ h_abs_pos] at h1
        rw [div_le_iff₀ h2k_pos]
        nlinarith
      -- Inject A into ℤ via x ↦ ⌊2k · x⌋.
      have hinj : InjOn (fun x : ℝ => ⌊2 * (k : ℝ) * x⌋) A := by
        intro x hx y hy heq
        by_contra hne
        have hlb := hsep x hx y hy hne
        -- From hlb: |x-y| ≥ 1/(2k), so |2kx - 2ky| ≥ 1.
        have habs_ge : (1 : ℝ) ≤ |2 * (k : ℝ) * x - 2 * (k : ℝ) * y| := by
          have heq1 : 2 * (k : ℝ) * x - 2 * (k : ℝ) * y = 2 * k * (x - y) := by ring
          rw [heq1, abs_mul, abs_of_pos h2k_pos]
          have : 2 * (k : ℝ) * (1 / (2 * k)) = 1 := by field_simp
          have hmul : 2 * (k : ℝ) * (1 / (2 * k)) ≤ 2 * (k : ℝ) * |x - y| :=
            mul_le_mul_of_nonneg_left hlb h2k_pos.le
          linarith
        -- But ⌊2kx⌋ = ⌊2ky⌋ implies |2kx - 2ky| < 1.
        have h1 : 2 * (k : ℝ) * x - 1 < (⌊2 * (k : ℝ) * x⌋ : ℝ) := Int.sub_one_lt_floor _
        have h2 : (⌊2 * (k : ℝ) * x⌋ : ℝ) ≤ 2 * (k : ℝ) * x := Int.floor_le _
        have h3 : 2 * (k : ℝ) * y - 1 < (⌊2 * (k : ℝ) * y⌋ : ℝ) := Int.sub_one_lt_floor _
        have h4 : (⌊2 * (k : ℝ) * y⌋ : ℝ) ≤ 2 * (k : ℝ) * y := Int.floor_le _
        simp only at heq
        rw [heq] at h1 h2
        have hlt : |2 * (k : ℝ) * x - 2 * (k : ℝ) * y| < 1 := by
          rw [abs_lt]; refine ⟨?_, ?_⟩ <;> linarith
        linarith
      -- InjOn to ℤ ⇒ Countable.
      have : A.Countable := by
        have hmaps : MapsTo (fun x : ℝ => ⌊2 * (k : ℝ) * x⌋) A Set.univ := fun _ _ => trivial
        exact hmaps.countable_of_injOn hinj Set.countable_univ
      exact this
    -- ⋃_{k ≥ 1} A_k covers ℝ.
    have hcover : (Set.univ : Set ℝ) ⊆ ⋃ k : ℕ, {x : ℝ | g x ≤ ((k + 1 : ℕ) : ℝ)} := by
      intro x _
      rw [mem_iUnion]
      obtain ⟨k, hk⟩ := exists_nat_ge (g x)
      refine ⟨k, ?_⟩
      simp only [mem_setOf_eq]
      push_cast
      linarith
    have hunion_count : (⋃ k : ℕ, {x : ℝ | g x ≤ ((k + 1 : ℕ) : ℝ)}).Countable := by
      apply Set.countable_iUnion
      intro k
      exact hcount (k + 1) (by omega)
    exact Cardinal.not_countable_real (hunion_count.mono hcover)

end Imc2003P11
