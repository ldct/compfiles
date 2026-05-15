/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2002, Problem 4
(IMC 2002, Day 1, Problem 4)

Let `f : [a,b] → [a,b]` be continuous, and define `p_0 = p`, `p_{n+1} = f(p_n)`.
If the orbit `T_p = {p_n : n ∈ ℕ}` is closed in `ℝ`, show that `T_p` is finite.

We formulate this as: assume `f : ℝ → ℝ` continuous with
`f '' [a, b] ⊆ [a, b]` (encoded as `∀ x ∈ [a,b], f x ∈ [a,b]`) and `p ∈ [a, b]`.
The orbit is the range of `O : ℕ → ℝ` with `O 0 = p`, `O (n+1) = f (O n)`.
If `Set.range O` is closed in `ℝ`, then it is finite.

Proof strategy (full mathematical argument):

Assume `T` is infinite. Then the orbit `O : ℕ → ℝ` is injective — otherwise
some value repeats, forcing `O` to be eventually periodic and `T` finite.

`T` is bounded (in `[a,b]`) and closed, hence compact. Since `T` is infinite
and compact, `T` contains an accumulation point `q ∈ T`.

Let `D` be the set of accumulation points of `T` within `T` (the derived set).
`D` is closed in `T`. Using injectivity of `O` and continuity of `f`, one shows
that `f(D) ⊆ D`: if `x = O N ∈ D`, take `y_k ∈ T \ {x}` with `y_k → x`; then
`f(y_k) → f(x)` with `f(y_k) ∈ T`. Either infinitely many `f(y_k) ≠ f(x)`
(giving `f(x) ∈ D`), or eventually all `f(y_k) = f(x) = O (N+1)`, whence
by injectivity of `O` each such `y_k` equals `O N = x`, contradicting `y_k ≠ x`.

Since `D ≠ ∅`, pick `O N₀ ∈ D`. Forward-invariance gives
`{O N₀, O (N₀ + 1), ...} ⊆ D`. In particular, `D` is infinite.

Remove the finitely many isolated points from `T` to get `T' := T \ (T \ D)`:
a closed subset of `T`, hence a complete metric space. Every point of `T'`
is an accumulation point of `T'` (each point of `T'` is an accumulation
point of `T` with nearby points eventually in `T'` since isolated points
of `T` are finite/discrete). Thus `T' = ⋃ {O n : n} \ (isolated)` is a
countable union of closed singletons with empty interior in `T'`, covering
all of `T'`. Baire's theorem yields a contradiction.

The Lean formalization below captures the statement and a partial proof,
leaving a `sorry` for the dynamical/Baire contradiction, as a full
formalization would be substantial.
-/

namespace Imc2002P4

open Set Filter Topology

/-- The orbit of `p` under `f`. -/
noncomputable def orbit (f : ℝ → ℝ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => f (orbit f p n)

lemma orbit_succ (f : ℝ → ℝ) (p : ℝ) (n : ℕ) :
    orbit f p (n + 1) = f (orbit f p n) := rfl

lemma orbit_zero (f : ℝ → ℝ) (p : ℝ) :
    orbit f p 0 = p := rfl

snip begin

/-- The orbit stays in the invariant interval. -/
lemma orbit_mem_Icc {f : ℝ → ℝ} {a b p : ℝ} (hp : p ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, f x ∈ Icc a b) (n : ℕ) :
    orbit f p n ∈ Icc a b := by
  induction n with
  | zero => exact hp
  | succ k ih => exact hf _ ih

/-- The range of the orbit is contained in the invariant interval. -/
lemma orbit_range_subset_Icc {f : ℝ → ℝ} {a b p : ℝ} (hp : p ∈ Icc a b)
    (hf : ∀ x ∈ Icc a b, f x ∈ Icc a b) :
    Set.range (orbit f p) ⊆ Icc a b := by
  rintro y ⟨n, rfl⟩
  exact orbit_mem_Icc hp hf n

/-- If `orbit f p m = orbit f p n` with `m < n`, then the orbit is eventually
periodic with period `n - m` starting at index `m`. This makes the range finite. -/
lemma orbit_range_finite_of_repeat {f : ℝ → ℝ} {p : ℝ} {m n : ℕ} (hmn : m < n)
    (heq : orbit f p m = orbit f p n) :
    (Set.range (orbit f p)).Finite := by
  -- Show: range (orbit f p) ⊆ (orbit f p) '' Finset.range n
  -- This suffices since the image of a finite set is finite.
  have hperiodic : ∀ k, orbit f p (m + k) = orbit f p (n + k) := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ j ih =>
      have h1 : orbit f p (m + (j + 1)) = f (orbit f p (m + j)) := by
        rw [show m + (j + 1) = (m + j) + 1 from rfl, orbit_succ]
      have h2 : orbit f p (n + (j + 1)) = f (orbit f p (n + j)) := by
        rw [show n + (j + 1) = (n + j) + 1 from rfl, orbit_succ]
      rw [h1, h2, ih]
  -- Now: for any i ≥ m, orbit f p i = orbit f p (i - (n - m) * k) for k = ⌊(i-m)/(n-m)⌋,
  -- giving i mod (n-m) + m kind of representative. Simpler: show range ⊆ orbit '' (Finset.range n).
  have hperiod_nonzero : 0 < n - m := by omega
  apply Set.Finite.subset (Set.Finite.image _ (Set.finite_Iio n))
  rintro y ⟨i, rfl⟩
  -- Find j ∈ Iio n with orbit f p i = orbit f p j.
  -- If i < n, take j = i.
  by_cases hi : i < n
  · exact ⟨i, hi, rfl⟩
  · -- i ≥ n. Reduce using periodicity.
    push Not at hi
    -- i ≥ n ≥ m + (n - m). Let j = m + ((i - m) % (n - m)). Then j < m + (n - m) = n, j ≥ m.
    -- And orbit f p i = orbit f p j by repeated application of hperiodic.
    set d : ℕ := n - m with hd_def
    have hd_pos : 0 < d := hperiod_nonzero
    -- i - m ≥ 0 since i ≥ n > m.
    have him : m ≤ i := by omega
    -- Let q = (i - m) / d, r = (i - m) % d.
    -- Then i = m + q * d + r with r < d.
    -- Claim: orbit f p i = orbit f p (m + r).
    -- Proof: by induction on q.
    set r : ℕ := (i - m) % d with hr_def
    set q : ℕ := (i - m) / d with hq_def
    have hr_lt : r < d := Nat.mod_lt _ hd_pos
    have hqdr : d * q + r = i - m := Nat.div_add_mod (i - m) d
    have hi_eq : i = m + q * d + r := by
      have hcomm : d * q = q * d := Nat.mul_comm d q
      rw [hcomm] at hqdr
      omega
    -- Claim: orbit f p (m + q * d + j) = orbit f p (m + j) for all j.
    have hreduce : ∀ q' j, orbit f p (m + q' * d + j) = orbit f p (m + j) := by
      intro q'
      induction q' with
      | zero => intro j; simp
      | succ k ih =>
        intro j
        -- orbit f p (m + (k+1) * d + j) = orbit f p (m + k * d + d + j)
        --                                = orbit f p ((m + d) + (k * d + j))
        --                                = orbit f p (n + (k * d + j))  -- since m + d = n
        --                                = orbit f p (m + (k * d + j))  -- by hperiodic
        --                                = orbit f p (m + k * d + j)
        have hmd : m + d = n := by omega
        have h1 : m + (k + 1) * d + j = (m + d) + (k * d + j) := by ring
        rw [h1, hmd]
        have h2 : orbit f p (n + (k * d + j)) = orbit f p (m + (k * d + j)) :=
          (hperiodic (k * d + j)).symm
        rw [h2]
        have h3 : m + (k * d + j) = m + k * d + j := by ring
        rw [h3, ih j]
    have hmd : m + d = n := by show m + (n - m) = n; omega
    refine ⟨m + r, ?_, ?_⟩
    · -- m + r < n, using d = n - m
      have hmr : m + r < m + d := Nat.add_lt_add_left hr_lt m
      exact hmd ▸ hmr
    · rw [hi_eq]; exact (hreduce q r).symm

/-- If the range of the orbit is infinite, then the orbit function is injective. -/
lemma orbit_injective_of_infinite {f : ℝ → ℝ} {p : ℝ}
    (hinf : (Set.range (orbit f p)).Infinite) :
    Function.Injective (orbit f p) := by
  intro m n heq
  by_contra hne
  wlog hmn : m < n with h
  · exact h hinf heq.symm (Ne.symm hne) (by omega)
  exact hinf (orbit_range_finite_of_repeat hmn heq)

snip end

problem imc2002_p4 (a b p : ℝ) (_hab : a ≤ b) (hp : p ∈ Icc a b)
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hinv : ∀ x ∈ Icc a b, f x ∈ Icc a b)
    (hclosed : IsClosed (Set.range (orbit f p))) :
    (Set.range (orbit f p)).Finite := by
  set T : Set ℝ := Set.range (orbit f p) with hT
  have hsub : T ⊆ Icc a b := orbit_range_subset_Icc hp hinv
  have hbdd : Bornology.IsBounded T := (Metric.isBounded_Icc a b).subset hsub
  have _hcpt : IsCompact T := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  -- Argue by contradiction: assume infinite.
  by_contra hne
  have hinf : T.Infinite := Set.not_finite.mp hne
  -- The orbit function is injective on ℕ (otherwise range is finite).
  have _hinj : Function.Injective (orbit f p) := orbit_injective_of_infinite hinf
  -- The infinite compact set T ⊆ ℝ has an accumulation point in T.
  -- Via forward-invariance of the derived set (using injectivity), one derives
  -- a nonempty forward-invariant accumulation set. Applying the Baire category
  -- theorem to T (closed in ℝ, hence complete metric space), viewed as a
  -- countable union of singletons, yields the contradiction.
  -- The remaining dynamical/Baire contradiction is left as a sorry.
  sorry

end Imc2002P4
