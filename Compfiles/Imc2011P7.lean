/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2011, Problem 7

(IMC 2011, Day 2, Problem 2.)

An alien race has three genders: male, female, and emale. A *married triple*
consists of three persons, one from each gender, who all like each other. Any
person belongs to at most one married triple. Feelings are mutual.

The expedition has `n` males, `n` females, and `n` emales; every member likes
at least `k` persons of each of the two other genders.

a) If `n` is even and `k = n/2`, it might be impossible to create even one
   married triple.

b) If `k ≥ 3n/4`, it is always possible to create `n` disjoint married triples.

## Solution sketch

Model the three gender sets as `Fin n` and the (mutual) liking relations as
three symmetric Boolean relations `MF`, `FE`, `ME`. A married triple is a
triple `(m, f, e)` with `MF m f`, `FE f e`, `ME m e` all true. `n` disjoint
triples are encoded as a permutation `σ : Fin n → Fin n` and `τ : Fin n → Fin n`
with `MF i (σ i)`, `FE (σ i) (τ i)`, `ME i (τ i)` for each `i`.

(a) Split each gender into halves of size `n/2`. Place edges only between
different-indexed parts. Each vertex has degree `n/2` to the other genders, but
a 3-cycle would have to traverse an even number of part-swaps, contradiction.

(b) "Unhappiness" argument: assign arbitrary triples; if not all are married,
swap an emale to reduce unhappiness. Counting: with `k ≥ 3n/4`, at most `n/4`
indices are bad in each direction, so a valid swap exists.
-/

namespace Imc2011P7

open Finset

/-- A married triple is a choice of (male, female, emale) all of whom like
each other in pairs. We encode the three liking relations as `MF`, `FE`, `ME`.
Mutuality is built into the directed predicates (it does not matter which side
we ask). -/
def IsMarriedTriple {n : ℕ}
    (MF : Fin n → Fin n → Prop) (FE : Fin n → Fin n → Prop)
    (ME : Fin n → Fin n → Prop) (m f e : Fin n) : Prop :=
  MF m f ∧ FE f e ∧ ME m e

/-- `n` disjoint married triples = perfect matching: there exist permutations
`σ` (males ↔ females) and `τ` (males ↔ emales) so that for each male `i`, the
triple `(i, σ i, τ i)` is a married triple. -/
def HasPerfectMatching {n : ℕ}
    (MF : Fin n → Fin n → Prop) (FE : Fin n → Fin n → Prop)
    (ME : Fin n → Fin n → Prop) : Prop :=
  ∃ σ τ : Equiv.Perm (Fin n),
    ∀ i, IsMarriedTriple MF FE ME i (σ i) (τ i)

/-- Each male has degree ≥ `k` to females (in the bipartite "likes" graph).
We use `Finset.filter` to count. -/
def DegreeMF {n : ℕ} (MF : Fin n → Fin n → Prop) [DecidableRel MF] (k : ℕ) :
    Prop :=
  (∀ m : Fin n, k ≤ ((univ : Finset (Fin n)).filter fun f => MF m f).card) ∧
  (∀ f : Fin n, k ≤ ((univ : Finset (Fin n)).filter fun m => MF m f).card)

/-- Similarly for the female–emale graph. -/
def DegreeFE {n : ℕ} (FE : Fin n → Fin n → Prop) [DecidableRel FE] (k : ℕ) :
    Prop :=
  (∀ f : Fin n, k ≤ ((univ : Finset (Fin n)).filter fun e => FE f e).card) ∧
  (∀ e : Fin n, k ≤ ((univ : Finset (Fin n)).filter fun f => FE f e).card)

/-- Similarly for the male–emale graph. -/
def DegreeME {n : ℕ} (ME : Fin n → Fin n → Prop) [DecidableRel ME] (k : ℕ) :
    Prop :=
  (∀ m : Fin n, k ≤ ((univ : Finset (Fin n)).filter fun e => ME m e).card) ∧
  (∀ e : Fin n, k ≤ ((univ : Finset (Fin n)).filter fun m => ME m e).card)

/-- **Part (b).** If `4 * k ≥ 3 * n`, then any configuration in which every
member likes at least `k` of each other gender admits `n` disjoint married
triples. -/
problem imc2011_p7_b (n k : ℕ) (hk : 3 * n ≤ 4 * k)
    (MF FE ME : Fin n → Fin n → Prop)
    [DecidableRel MF] [DecidableRel FE] [DecidableRel ME]
    (hMF : DegreeMF MF k) (hFE : DegreeFE FE k) (hME : DegreeME ME k) :
    HasPerfectMatching MF FE ME := by
  -- TODO: formalize the unhappiness-reduction argument from the official
  -- solution (or the Hall's theorem approach: build a perfect MF-matching,
  -- then a perfect matching on pairs ↔ emales).
  sorry

/-- **Part (a).** If `n` is even (say `n = 2 * m`) and `k = n / 2 = m`, there
exists a configuration with the prescribed degree conditions but with no
married triple at all. We exhibit it: split each gender into halves and only
allow cross-half edges. Concretely, take `MF i j ↔ (i < m ↔ ¬ j < m)`, similarly
for `FE` and `ME`; then any 3-cycle would parity-fail. -/
problem imc2011_p7_a (m : ℕ) (hm : 0 < m) :
    ∃ (MF FE ME : Fin (2 * m) → Fin (2 * m) → Prop)
      (_ : DecidableRel MF) (_ : DecidableRel FE) (_ : DecidableRel ME),
      DegreeMF MF m ∧ DegreeFE FE m ∧ DegreeME ME m ∧
      ¬ ∃ a b c : Fin (2 * m), IsMarriedTriple MF FE ME a b c := by
  -- Bipartition each gender by `i.val < m`. A vertex is "low" iff `i.val < m`.
  -- Edges go only between low and high. Each vertex has exactly `m` neighbours
  -- in each other gender. A married triple would need an odd number of
  -- low/high transitions in a 3-cycle — impossible.
  -- TODO: formalize the construction; the key counting lemmas are:
  --   • the set of `j : Fin (2*m)` with `j.val < m` has cardinality `m`;
  --   • the set with `m ≤ j.val` has cardinality `m`;
  --   • for any low `i`, the high `j` are exactly the `m` neighbours.
  sorry

end Imc2011P7
