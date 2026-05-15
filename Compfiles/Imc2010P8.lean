/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2010, Problem 8
(IMC 2010, Day 2, Problem 3)

Denote by `S_n` the group of permutations of `(1, 2, …, n)`. Suppose
`G ≤ S_n` is such that for every `π ∈ G \ {e}` there exists a unique
`k ∈ {1, …, n}` with `π(k) = k`. Show that this `k` is the same for all
`π ∈ G \ {e}`.

## Proof outline

Pick a non-identity `π₀ ∈ G` and let `x₀` be its (unique) fixed point.
We claim `x₀` is a global fixed point. Suppose not, with `σ x₀ = y ≠ x₀`.
By orbit-stabilizer applied to the orbit of `x₀`, the contribution of
that orbit to `∑_x (|stab x| - 1) = |G| - 1` equals `|G| - |orbit(x₀)|`.
Since `|orbit(x₀)| ≥ 2`, the remaining contribution from other orbits is
`|orbit(x₀)| - 1 ≥ 1`. But any other orbit `O'` with non-trivial
stabilizer contributes `|G| - |O'| ≥ |G|/2`, while we need
`≤ |orbit(x₀)| - 1 < |G|/2`, contradiction. Hence other orbits act
freely (stabilizer trivial), contributing `0`, forcing
`|orbit(x₀)| = 1`, contradiction.
-/

namespace Imc2010P8

open MulAction Finset

snip begin

variable {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))

/-- The set of fixed points of `π : G` as a `Finset` of `Fin n`. -/
def fixSet (π : G) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun k => (π : Equiv.Perm (Fin n)) k = k)

/-- The set of group elements fixing `x` as a `Finset` of `G`. -/
def stabSet [Fintype G] (x : Fin n) : Finset G :=
  (univ : Finset G).filter (fun π : G => (π : Equiv.Perm (Fin n)) x = x)

/-- Double counting: `∑_x |stabSet x| = ∑_π |fixSet π|`. -/
lemma sum_stabSet_eq_sum_fixSet [Fintype G] :
    ∑ x : Fin n, (stabSet G x).card = ∑ π : G, (fixSet G π).card := by
  classical
  unfold stabSet fixSet
  rw [show (∑ x : Fin n,
        ((univ : Finset G).filter (fun π : G => (π : Equiv.Perm (Fin n)) x = x)).card)
        = ∑ x : Fin n, ∑ π : G,
            (if (π : Equiv.Perm (Fin n)) x = x then 1 else 0) by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.card_filter]]
  rw [show (∑ π : G,
        ((univ : Finset (Fin n)).filter
          (fun k => (π : Equiv.Perm (Fin n)) k = k)).card)
        = ∑ π : G, ∑ x : Fin n,
            (if (π : Equiv.Perm (Fin n)) x = x then 1 else 0) by
    refine Finset.sum_congr rfl ?_
    intro π _
    rw [Finset.card_filter]]
  exact Finset.sum_comm

/-- The size of the stabilizer subgroup of `x` matches `(stabSet x).card`. -/
lemma card_stabilizer_eq_stabSet_card [Fintype G] (x : Fin n) :
    Fintype.card (stabilizer G x) = (stabSet G x).card := by
  classical
  unfold stabSet
  rw [Fintype.card_subtype]
  refine Finset.card_bij (fun π _ => π) ?_ ?_ ?_
  · intros π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    exact mem_stabilizer_iff.mp hπ
  · intros _ _ _ _ heq; exact heq
  · intros π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    refine ⟨π, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_stabilizer_iff.mpr hπ

/-- Under the unique-fixed-point hypothesis, for `π ≠ 1` in `G`,
`(fixSet π).card = 1`. -/
lemma fixSet_card_of_ne_one [Fintype G]
    (h : ∀ π : G, π ≠ 1 → ∃! k : Fin n, (π : Equiv.Perm (Fin n)) k = k)
    (π : G) (hπ : π ≠ 1) : (fixSet G π).card = 1 := by
  classical
  unfold fixSet
  obtain ⟨k, hk, hk_uniq⟩ := h π hπ
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hi => hk_uniq i hi, fun hi => hi ▸ hk⟩

/-- For `π = 1`, `(fixSet 1).card = n`. -/
lemma fixSet_one_card [Fintype G] :
    (fixSet G (1 : G)).card = n := by
  classical
  unfold fixSet
  have : ((univ : Finset (Fin n)).filter
      (fun k => ((1 : G) : Equiv.Perm (Fin n)) k = k)) = univ := by
    apply Finset.filter_eq_self.mpr
    intro k _
    show (1 : Equiv.Perm (Fin n)) k = k
    rfl
  rw [this]
  exact Finset.card_univ.trans (by rw [Fintype.card_fin])

/-- The double-count gives `|G| + n - 1 = ∑_x |stab x|`. -/
lemma sum_stab_card [Fintype G]
    (h : ∀ π : G, π ≠ 1 → ∃! k : Fin n, (π : Equiv.Perm (Fin n)) k = k) :
    ∑ x : Fin n, Fintype.card (stabilizer G x) = (Fintype.card G - 1) + n := by
  classical
  rw [show (∑ x : Fin n, Fintype.card (stabilizer G x))
        = ∑ x : Fin n, (stabSet G x).card from by
    refine Finset.sum_congr rfl ?_
    intros x _
    exact card_stabilizer_eq_stabSet_card G x]
  rw [sum_stabSet_eq_sum_fixSet]
  rw [show (∑ π : G, (fixSet G π).card)
        = (fixSet G (1 : G)).card +
            ∑ π ∈ ((univ : Finset G).erase 1), (fixSet G π).card from by
    rw [← Finset.add_sum_erase (univ : Finset G) (fun π => (fixSet G π).card)
        (Finset.mem_univ _)]]
  rw [fixSet_one_card]
  rw [show (∑ π ∈ ((univ : Finset G).erase 1), (fixSet G π).card)
        = ∑ π ∈ ((univ : Finset G).erase 1), 1 from by
    refine Finset.sum_congr rfl ?_
    intros π hπ
    have hπ_ne : π ≠ 1 := Finset.ne_of_mem_erase hπ
    exact fixSet_card_of_ne_one G h π hπ_ne]
  rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  rw [Finset.card_univ]
  ring

snip end

/-- The IMC 2010, Problem 8 (Day 2, Problem 3) main theorem.

We add the natural hypothesis `0 < n` since the problem implicitly assumes
`S_n` is the group of permutations of `(1, 2, …, n)`, requiring `n ≥ 1`.

NOTE: The current proof formalises the key counting lemma
`sum_stab_card` (`∑_x |stab G x| = (|G| - 1) + n`) but the
deduction of a global fixed point via orbit-stabilizer is left as a
TODO. The remaining argument: pick `π₀ ≠ 1` with fixed point `x₀`, and
show `orbit(x₀) = {x₀}` by counting. -/
problem imc2010_p8 (n : ℕ) (hn : 0 < n) (G : Subgroup (Equiv.Perm (Fin n)))
    (h : ∀ π ∈ G, π ≠ 1 → ∃! k : Fin n, π k = k) :
    ∃ k : Fin n, ∀ π ∈ G, π ≠ 1 → π k = k := by
  classical
  have hG : ∀ π : G, π ≠ 1 → ∃! k : Fin n, (π : Equiv.Perm (Fin n)) k = k := by
    intro π hπ
    apply h π.val π.property
    intro heq; apply hπ; exact Subtype.ext heq
  suffices hsuff : ∃ k : Fin n, ∀ π : G, π ≠ 1 → (π : Equiv.Perm (Fin n)) k = k by
    obtain ⟨k, hk⟩ := hsuff
    refine ⟨k, fun π hπ hπ1 => ?_⟩
    have h1 : (⟨π, hπ⟩ : G) ≠ 1 := fun heq => hπ1 (congrArg Subtype.val heq)
    exact hk ⟨π, hπ⟩ h1
  haveI : Fintype G := Fintype.ofFinite G
  -- Case split on whether G is trivial.
  by_cases htriv : ∀ π : G, π = 1
  · -- G trivial: take any k (using hn) and conclude vacuously.
    refine ⟨⟨0, hn⟩, fun π hπ => absurd (htriv π) hπ⟩
  · -- G non-trivial: pick π₀ ≠ 1.
    push Not at htriv
    obtain ⟨π₀, hπ₀⟩ := htriv
    obtain ⟨x₀, hx₀, hx₀_uniq⟩ := hG π₀ hπ₀
    -- Goal: show x₀ is a global fixed point.
    refine ⟨x₀, ?_⟩
    -- The remaining argument using orbit-counting is left as a TODO.
    sorry

end Imc2010P8
