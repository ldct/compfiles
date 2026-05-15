/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2019, Problem 8

Let `x₁, …, xₙ ∈ ℝ`. For `I ⊆ {1, …, n}`, let `s(I) = ∑_{i ∈ I} xᵢ`.
If `I ↦ s(I)` takes at least `1.8^n` values, prove that at most `1.7^n`
sets `I` satisfy `s(I) = 2019`.

We model `I ⊆ {1, …, n}` as `Finset (Fin n)`.

The proof is a pigeonhole argument: choose representatives, one per
value in the image of `s`, getting `≥ 1.8^n` subsets `S` with pairwise
distinct sums. Together with the `> 1.7^n` subsets `T` summing to `2019`,
we get `> 3.06^n > 3^n` pairs `(I, J) ∈ S × T`. The map
`(I, J) ↦ 𝟙_I − 𝟙_J ∈ ℤ^n` lands in `{-1, 0, 1}^n`, of size `3^n`.
Pigeonhole gives `(I₁, J₁) ≠ (I₂, J₂)` with the same image; dotting with
`x` shows `s I₁ − s J₁ = s I₂ − s J₂`. Since `s J₁ = s J₂ = 2019`, we
get `s I₁ = s I₂`, hence `I₁ = I₂` (distinct sums on `S`). Then `J₁ = J₂`.
Contradiction.
-/

namespace Imc2019P8

open scoped BigOperators
open Finset

/-- Sum of `xᵢ` over `i ∈ I`. -/
def s {n : ℕ} (x : Fin n → ℝ) (I : Finset (Fin n)) : ℝ := ∑ i ∈ I, x i

snip begin

/-- Indicator difference `𝟙_I(i) − 𝟙_J(i)`, valued in `{-1, 0, 1}`. -/
def diffMap {n : ℕ} (I J : Finset (Fin n)) : Fin n → ℤ :=
  fun i => (if i ∈ I then (1 : ℤ) else 0) - (if i ∈ J then 1 else 0)

/-- The cube `{-1, 0, 1}^n` as a Finset. -/
def cube (n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ : Fin n => ({-1, 0, 1} : Finset ℤ))

/-- Membership: `diffMap I J ∈ cube n`. -/
lemma diffMap_mem_cube {n : ℕ} (I J : Finset (Fin n)) :
    diffMap I J ∈ cube n := by
  rw [cube, Fintype.mem_piFinset]
  intro i
  simp only [diffMap, mem_insert, mem_singleton]
  by_cases hi1 : i ∈ I <;> by_cases hi2 : i ∈ J <;> simp [hi1, hi2]

/-- The cube has cardinality `3^n`. -/
lemma card_cube (n : ℕ) : (cube n).card = 3^n := by
  rw [cube, Fintype.card_piFinset]
  have h : ({-1, 0, 1} : Finset ℤ).card = 3 := by decide
  simp [h]

/-- `3^n < 1.8^n * 1.7^n` for `n ≥ 1`. -/
lemma key_numeric {n : ℕ} (hn : 1 ≤ n) :
    (3 : ℝ)^n < (1.8 : ℝ)^n * (1.7 : ℝ)^n := by
  rw [← mul_pow]
  have h306 : (1.8 : ℝ) * 1.7 = 3.06 := by norm_num
  rw [h306]
  have hne : n ≠ 0 := by omega
  have h3lt : (3 : ℝ) < 3.06 := by norm_num
  have h3nn : (0 : ℝ) ≤ 3 := by norm_num
  exact pow_lt_pow_left₀ h3lt h3nn hne

/-- Auxiliary: `∑ i, (𝟙_K(i) : ℝ) * x i = ∑ i ∈ K, x i`. -/
lemma sum_indicator_mul {n : ℕ} (x : Fin n → ℝ) (K : Finset (Fin n)) :
    ∑ i, ((if i ∈ K then (1 : ℝ) else 0) * x i) = ∑ i ∈ K, x i := by
  have step : ∀ i, ((if i ∈ K then (1 : ℝ) else 0) * x i) =
              (if i ∈ K then x i else 0) := by
    intro i
    by_cases h : i ∈ K <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => step i)]
  rw [Finset.sum_ite_mem]
  congr 1
  exact (Finset.univ_inter K)

/-- Dotting `diffMap I J` with `x` gives `s I − s J`. -/
lemma sum_diffMap_eq {n : ℕ} (x : Fin n → ℝ) (I J : Finset (Fin n)) :
    (∑ i, (diffMap I J i : ℝ) * x i) = s x I - s x J := by
  unfold s
  calc ∑ i, ((diffMap I J i : ℝ) * x i)
      = ∑ i, (((if i ∈ I then (1 : ℝ) else 0) - (if i ∈ J then 1 else 0)) * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [diffMap]
        push_cast
        ring
    _ = ∑ i, ((if i ∈ I then (1 : ℝ) else 0) * x i) -
        ∑ i, ((if i ∈ J then (1 : ℝ) else 0) * x i) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _; ring
    _ = (∑ i ∈ I, x i) - (∑ i ∈ J, x i) := by
        rw [sum_indicator_mul x I, sum_indicator_mul x J]

/-- If `diffMap I₁ J₁ = diffMap I₂ J₂`, then `s I₁ - s J₁ = s I₂ - s J₂`. -/
lemma s_sub_eq_of_diffMap_eq {n : ℕ} (x : Fin n → ℝ)
    {I₁ J₁ I₂ J₂ : Finset (Fin n)} (h : diffMap I₁ J₁ = diffMap I₂ J₂) :
    s x I₁ - s x J₁ = s x I₂ - s x J₂ := by
  rw [← sum_diffMap_eq x I₁ J₁, ← sum_diffMap_eq x I₂ J₂]
  apply Finset.sum_congr rfl
  intro i _
  rw [h]

/-- If `diffMap I₁ J = diffMap I₂ J`, then `I₁ = I₂`. -/
lemma fst_eq_of_diffMap_eq {n : ℕ}
    {I₁ I₂ J : Finset (Fin n)} (h : diffMap I₁ J = diffMap I₂ J) :
    I₁ = I₂ := by
  ext i
  have hi := congrFun h i
  simp only [diffMap] at hi
  -- (𝟙 I₁ - 𝟙 J) = (𝟙 I₂ - 𝟙 J), so 𝟙 I₁ = 𝟙 I₂.
  have hI : (if i ∈ I₁ then (1 : ℤ) else 0) = (if i ∈ I₂ then (1 : ℤ) else 0) := by
    linarith
  by_cases h1 : i ∈ I₁ <;> by_cases h2 : i ∈ I₂ <;> simp [h1, h2] at hI ⊢

/-- If `diffMap I J₁ = diffMap I J₂`, then `J₁ = J₂`. -/
lemma snd_eq_of_diffMap_eq {n : ℕ}
    {I J₁ J₂ : Finset (Fin n)} (h : diffMap I J₁ = diffMap I J₂) :
    J₁ = J₂ := by
  ext i
  have hi := congrFun h i
  simp only [diffMap] at hi
  have hJ : (if i ∈ J₁ then (1 : ℤ) else 0) = (if i ∈ J₂ then (1 : ℤ) else 0) := by
    linarith
  by_cases h1 : i ∈ J₁ <;> by_cases h2 : i ∈ J₂ <;> simp [h1, h2] at hJ ⊢

snip end

problem imc2019_p8 (n : ℕ) (x : Fin n → ℝ)
    (hImg : (1.8 : ℝ)^n ≤ ((Finset.univ : Finset (Finset (Fin n))).image (s x)).card) :
    (((Finset.univ : Finset (Finset (Fin n))).filter (fun I => s x I = 2019)).card : ℝ) ≤
      (1.7 : ℝ)^n := by
  -- Edge case: n = 0.
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · subst hn0
    have h_le_one :
        (((Finset.univ : Finset (Finset (Fin 0))).filter
            (fun I => s x I = 2019)).card : ℝ) ≤ 1 := by
      have hfin : (Finset.univ : Finset (Finset (Fin 0))).card = 1 := by decide
      have hle : ((Finset.univ : Finset (Finset (Fin 0))).filter
                  (fun I => s x I = 2019)).card ≤
                  (Finset.univ : Finset (Finset (Fin 0))).card :=
        card_le_card (filter_subset _ _)
      have h1 : ((Finset.univ : Finset (Finset (Fin 0))).filter
                (fun I => s x I = 2019)).card ≤ 1 := by omega
      exact_mod_cast h1
    have h17 : (1.7 : ℝ)^0 = 1 := pow_zero _
    rw [h17]; exact h_le_one
  -- Main case, n ≥ 1.
  by_contra hcontra
  push Not at hcontra
  set T : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun I => s x I = 2019) with hT_def
  set V : Finset ℝ := (Finset.univ : Finset (Finset (Fin n))).image (s x) with hV_def
  classical
  have section_exists : ∀ v ∈ V, ∃ I : Finset (Fin n), s x I = v := by
    intro v hv
    rw [hV_def, mem_image] at hv
    obtain ⟨I, _, hI⟩ := hv
    exact ⟨I, hI⟩
  let σ : ℝ → Finset (Fin n) := fun v =>
    if h : v ∈ V then (section_exists v h).choose else ∅
  have hσ : ∀ v ∈ V, s x (σ v) = v := by
    intro v hv
    show s x (if h : v ∈ V then (section_exists v h).choose else ∅) = v
    rw [dif_pos hv]
    exact (section_exists v hv).choose_spec
  set S : Finset (Finset (Fin n)) := V.image σ with hS_def
  have hσ_injOn : Set.InjOn σ V := by
    intro v hv w hw hvw
    have h1 := hσ v hv
    have h2 := hσ w hw
    rw [← h1, ← h2, hvw]
  have hcard_S : S.card = V.card := by
    rw [hS_def]
    exact card_image_of_injOn hσ_injOn
  have hS_ge : (1.8 : ℝ)^n ≤ S.card := by rw [hcard_S]; exact hImg
  have hT_gt : (1.7 : ℝ)^n < (T.card : ℝ) := hcontra
  have h17_nn : (0 : ℝ) ≤ (1.7 : ℝ)^n := by positivity
  have hST_gt : (3 : ℝ)^n < (S.card : ℝ) * (T.card : ℝ) := by
    have h1 : (1.8 : ℝ)^n * (1.7 : ℝ)^n ≤ (S.card : ℝ) * (T.card : ℝ) := by
      apply mul_le_mul hS_ge hT_gt.le h17_nn
      exact_mod_cast Nat.zero_le _
    exact lt_of_lt_of_le (key_numeric hn_pos) h1
  have h_prod_gt : (3^n : ℕ) < (S ×ˢ T).card := by
    rw [Finset.card_product]
    have h3pow : ((3^n : ℕ) : ℝ) = (3 : ℝ)^n := by push_cast; ring
    have hcasted : ((S.card * T.card : ℕ) : ℝ) = (S.card : ℝ) * (T.card : ℝ) := by
      push_cast; ring
    have hreal : ((3^n : ℕ) : ℝ) < ((S.card * T.card : ℕ) : ℝ) := by
      rw [h3pow, hcasted]; exact hST_gt
    exact_mod_cast hreal
  have h_card_cube_lt : (cube n).card < (S ×ˢ T).card := by
    rw [card_cube]; exact h_prod_gt
  -- Pigeonhole.
  have h_map_in_cube : ∀ p ∈ S ×ˢ T, diffMap p.1 p.2 ∈ cube n :=
    fun p _ => diffMap_mem_cube p.1 p.2
  have hpig : ∃ p ∈ S ×ˢ T, ∃ q ∈ S ×ˢ T,
      p ≠ q ∧ diffMap p.1 p.2 = diffMap q.1 q.2 := by
    by_contra hne
    push Not at hne
    let F : Finset (Fin n) × Finset (Fin n) → (Fin n → ℤ) := fun p => diffMap p.1 p.2
    have himg_sub : (S ×ˢ T).image F ⊆ cube n := by
      intro a ha
      rw [mem_image] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      exact h_map_in_cube p hp
    have hinj_image : ((S ×ˢ T).image F).card = (S ×ˢ T).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      by_contra hne'
      exact hne p hp q hq hne' hpq
    have h_card_le : (S ×ˢ T).card ≤ (cube n).card := by
      rw [← hinj_image]
      exact Finset.card_le_card himg_sub
    omega
  obtain ⟨⟨I₁, J₁⟩, hp, ⟨I₂, J₂⟩, hq, hpq, hfpq⟩ := hpig
  rw [Finset.mem_product] at hp hq
  obtain ⟨hI₁S, hJ₁T⟩ := hp
  obtain ⟨hI₂S, hJ₂T⟩ := hq
  -- Decode: hfpq has type diffMap (I₁,J₁).1 (I₁,J₁).2 = diffMap (I₂,J₂).1 (I₂,J₂).2.
  -- Simplify it.
  simp only [] at hfpq
  -- s I₁ - s J₁ = s I₂ - s J₂
  have hsdiff : s x I₁ - s x J₁ = s x I₂ - s x J₂ :=
    s_sub_eq_of_diffMap_eq x hfpq
  -- s J₁ = s J₂ = 2019
  have hsJ₁ : s x J₁ = 2019 := by rw [hT_def] at hJ₁T; exact (mem_filter.mp hJ₁T).2
  have hsJ₂ : s x J₂ = 2019 := by rw [hT_def] at hJ₂T; exact (mem_filter.mp hJ₂T).2
  have hsI : s x I₁ = s x I₂ := by linarith
  -- I₁, I₂ in image of σ.
  rw [hS_def, mem_image] at hI₁S hI₂S
  obtain ⟨v₁, hv₁V, hv₁eq⟩ := hI₁S
  obtain ⟨v₂, hv₂V, hv₂eq⟩ := hI₂S
  -- Note: hv₁eq has type `σ v₁ = (I₁, J₁).1`. Reduce using `show`.
  have hv₁eq' : σ v₁ = I₁ := hv₁eq
  have hv₂eq' : σ v₂ = I₂ := hv₂eq
  have hsI₁eq : s x I₁ = v₁ := by rw [← hv₁eq']; exact hσ v₁ hv₁V
  have hsI₂eq : s x I₂ = v₂ := by rw [← hv₂eq']; exact hσ v₂ hv₂V
  have hv12 : v₁ = v₂ := by linarith [hsI, hsI₁eq, hsI₂eq]
  have hI₁I₂ : I₁ = I₂ := by rw [← hv₁eq', ← hv₂eq', hv12]
  -- Since I₁ = I₂, hfpq becomes diffMap I₁ J₁ = diffMap I₁ J₂; hence J₁ = J₂.
  have hfpq' : diffMap I₁ J₁ = diffMap I₁ J₂ := by rw [hI₁I₂] at hfpq ⊢; exact hfpq
  have hJ₁J₂ : J₁ = J₂ := snd_eq_of_diffMap_eq hfpq'
  apply hpq
  rw [Prod.mk.injEq]
  exact ⟨hI₁I₂, hJ₁J₂⟩

end Imc2019P8
