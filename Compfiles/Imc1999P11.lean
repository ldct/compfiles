/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 1999, Problem 11 (Day 2, Problem 5)

Let `~` be an equivalence relation on the set of words over the alphabet
`{x, y, z}` such that

* `u u ~ u` for every word `u`, and
* `v ~ w` implies `u v ~ u w` and `v u ~ w u` for every word `u`.

Prove that every word is equivalent (under `~`) to some word of length
at most `8`.

## Solution sketch (official solution)

The key lemma is: if `u` is a word containing all three letters
`x, y, z` and `v` is any word, then there exists a word `w` such that
`u v w ~ u`. This is proved first for `v` a single letter (say `x`), by
writing `u = u₁ x u₂` and taking `w = u₂`, since
`u v w = u₁ x u₂ x u₂ = u₁ (x u₂)(x u₂) ~ u₁ (x u₂) = u`. The general
case follows by iterating.

Now suppose `a` is a word of length `> 8`. If `a = u v v w` for some
nonempty `v`, then `a ~ u v w` of strictly smaller length, and we
recurse. Otherwise `a` is "square-free" in the contiguous sense.
Splitting `a = b c d` with `|b| = |d| = 4`, both `b` and `d` must
contain all three letters (else a square would appear). By the lemma
applied to `b` (with right context `c d`) we get `e` with `b c d e ~ b`,
and similarly to `d` (with right context `e`) we get `f` with
`d e f ~ d`. Combining these yields `a ~ b d`, a word of length `8`.

## Status of this formalization

Statement: complete. Proof: a `sorry` placeholder — see TODO below.
The statement universally quantifies over the equivalence relation
satisfying the two stated closure properties.
-/

namespace Imc1999P11

open List

/-- The alphabet `{x, y, z}` is encoded as `Fin 3`. A word is a list
of letters. -/
abbrev Letter : Type := Fin 3

/-- A word over the three-letter alphabet. -/
abbrev Word : Type := List Letter

/-- The structural property that `~` is an equivalence relation on
`Word` closed under the rules `u u ~ u` and `v ~ w → u v ~ u w` and
`v ~ w → v u ~ w u`. -/
structure IsCongruence (r : Word → Word → Prop) : Prop where
  refl : ∀ u, r u u
  symm : ∀ {u v}, r u v → r v u
  trans : ∀ {u v w}, r u v → r v w → r u w
  /-- Squares collapse: `u u ~ u`. -/
  square : ∀ u, r (u ++ u) u
  /-- Left congruence: `v ~ w → u v ~ u w`. -/
  left : ∀ u {v w}, r v w → r (u ++ v) (u ++ w)
  /-- Right congruence: `v ~ w → v u ~ w u`. -/
  right : ∀ u {v w}, r v w → r (v ++ u) (w ++ u)

/-- **IMC 1999 Problem 11.** For any equivalence relation `r` on words
over the three-letter alphabet `{x, y, z}` that is closed under
`u u ~ u` and the two-sided congruence rules, every word is equivalent
to some word of length at most `8`. -/
problem imc1999_p11 (r : Word → Word → Prop) (hr : IsCongruence r)
    (a : Word) : ∃ b : Word, r a b ∧ b.length ≤ 8 := by
  -- TODO: Full proof.
  --
  -- Strategy (official solution):
  --
  -- (1) **Key lemma.** If `u : Word` contains each of the three
  --     letters `0, 1, 2 : Fin 3` (i.e. `0 ∈ u ∧ 1 ∈ u ∧ 2 ∈ u`), then
  --     for every word `v` there exists a word `w` with `r (u ++ v ++ w) u`.
  --
  --     Proof. First handle `v = [c]` for a single letter `c`. Since
  --     `c ∈ u`, write `u = u₁ ++ [c] ++ u₂`. Take `w := u₂`. Then
  --       `u ++ [c] ++ u₂ = u₁ ++ [c] ++ u₂ ++ [c] ++ u₂`
  --                       = `u₁ ++ ([c] ++ u₂) ++ ([c] ++ u₂)`,
  --     and applying `hr.square` and the left/right congruences gives
  --     `r (u ++ [c] ++ u₂) (u₁ ++ ([c] ++ u₂)) = u`.
  --
  --     For general `v = c₁ :: c₂ :: … :: cₖ` proceed by induction on
  --     the length of `v`. Suppose for `v' := c₁ :: … :: c_{k-1}` we have
  --     `w'` with `r (u ++ v' ++ w') u`. Setting `u' := u ++ v' ++ w'`,
  --     we have `r u' u`, so `u'` also contains all three letters
  --     (since `u` does — formally: any equivalence-class containing a
  --     word with all letters has a representative with all letters,
  --     but actually we only need to apply the single-letter case at
  --     `u` again). A cleaner formulation: induct on `|v|` showing
  --     `∀ v, ∃ w, r (u ++ v ++ w) u` directly: if `v = []` take
  --     `w := []` and use `hr.refl`. If `v = c :: v'`, first apply the
  --     single-letter case to get `w₁` with `r (u ++ [c] ++ w₁) u`,
  --     then by IH on `v'` get `w₂` with `r (u ++ v' ++ w₂) u`. Then
  --       `u ++ (c :: v') ++ ?` should reduce to `u`. Concretely:
  --       since `r (u ++ [c] ++ w₁) u`, applying right-congruence by
  --       `v'` gives `r (u ++ [c] ++ w₁ ++ v') (u ++ v')`, then by
  --       transitivity through `r (u ++ v' ++ w₂) u` and chaining,
  --       we obtain a suitable `w`.
  --
  --     The cleanest induction is on `v`: for `v = c :: v'`, apply IH
  --     to `v'` to get `w'` with `r (u ++ v' ++ w') u`. Then by the
  --     single-letter case applied at `u` with letter `c`, get `w''`
  --     with `r (u ++ [c] ++ w'') u`, and combine via the IH applied
  --     once more to the word `w'' ++ v'` (or directly to `[c] ++ v'`):
  --     by IH on `[c] ++ v' ++ w'`, get `w` with
  --     `r (u ++ ([c] ++ v' ++ w') ++ w) u`, and observe that
  --     `[c] ++ v' = c :: v' = v`, so `w' ++ w` is the desired word.
  --
  -- (2) **No internal square.** Say a word `a` *contains a square* if
  --     there exist `u w` and a nonempty `v` with `a = u ++ v ++ v ++ w`.
  --     If `a` contains a square `u v v w` with `|v| ≥ 1`, then by
  --     `hr.square`, `hr.left`, and `hr.right`,
  --     `r a (u ++ v ++ w)`, and `(u ++ v ++ w).length = a.length - v.length
  --     < a.length`. So we may strong-induct on `a.length` to assume
  --     `a` contains no square.
  --
  -- (3) **Length-4 prefix/suffix contain all letters.** If `|a| ≥ 9`
  --     and `a` contains no square, write `a = b ++ c ++ d` with
  --     `|b| = 4` and `|d| = 4`. We claim `b` (and similarly `d`)
  --     contains all three letters: indeed, a length-4 word over a
  --     2-letter alphabet must contain a square (over `{0,1}`,
  --     enumerate the 16 words and check; equivalently, any binary
  --     word of length ≥ 4 has a square `XX` with `|X| ≤ 2`). Hence
  --     a square in `b` would give a square in `a`, contradiction.
  --
  -- (4) **Reduction to length 8.** With `b, d` each containing all
  --     three letters, apply the key lemma:
  --       (a) at `u := b`, `v := c ++ d`: get `e` with `r (b ++ (c ++ d) ++ e) b`,
  --           i.e. `r (a ++ e) b`.
  --       (b) at `u := d`, `v := e`: get `f` with `r (d ++ e ++ f) d`.
  --     Now compute:
  --       `a = b ++ c ++ d`,
  --       `r (b ++ c ++ d) (b ++ c ++ d ++ e ++ f)`  (right-congruence,
  --                                                  using (b) on
  --                                                  the suffix `d ++ e ++ f`
  --                                                  applied right of `b ++ c`,
  --                                                  reading (b) as
  --                                                  `r d (d ++ e ++ f)` via symm),
  --     hence `r a (b ++ c ++ (d ++ e ++ f))`. Combine with (a) read
  --     as `r (a ++ e) b` (so `r (a ++ e ++ f) (b ++ f)` by right-cong),
  --     and after symm/trans, `r a (b ++ d)`. Since
  --     `(b ++ d).length = 4 + 4 = 8`, this is the desired bound.
  --
  -- The total Lean development for this argument is substantial: the
  -- key lemma needs a careful induction, step (3) needs the binary
  -- pigeonhole / explicit enumeration, and step (4) is a chain of
  -- algebraic congruence manipulations.
  sorry

end Imc1999P11
