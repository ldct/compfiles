/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# International Mathematical Competition 2012, Problem 6

Consider a polynomial
`f(x) = x^2012 + a_{2011} x^{2011} + ⋯ + a_1 x + a_0`.
Albert Einstein and Homer Simpson are playing the following game. In turn,
they choose one of the coefficients `a_0, a_1, …, a_{2011}` and assign a real
value to it. Albert has the first move. Once a value is assigned to a
coefficient, it cannot be changed. The game ends after all the coefficients
have been assigned values.

Homer's goal is to make `m(x)` divide `f(x)`. Albert's goal is to prevent this.

(a) Which player has a winning strategy if `m(x) = x − 2012`?
(b) Which player has a winning strategy if `m(x) = x^2 + 1`?

Answer: Homer has a winning strategy in both cases.
-/

namespace Imc2012P6

open Polynomial

/-- Identifier for the two players. -/
inductive Player
  | Albert
  | Homer
deriving DecidableEq, Repr

/-- A *position* records the current partial assignment of coefficients.
`pos i = some r` means coefficient `a_i` has been assigned the value `r`;
`pos i = none` means it is still free. -/
abbrev Position : Type := Fin 2012 → Option ℝ

/-- A *move* picks a free coefficient and a real value to assign to it. -/
structure Move (pos : Position) where
  idx : Fin 2012
  value : ℝ
  free : pos idx = none

/-- Apply a move to a position. -/
def Move.apply {pos : Position} (m : Move pos) : Position :=
  Function.update pos m.idx (some m.value)

/-- Whose turn it is after `k` moves have been made (with Albert moving first). -/
def turn (k : ℕ) : Player := if k % 2 = 0 then .Albert else .Homer

/-- A strategy for a player: given the current position (with at least one free
coefficient), choose a move. -/
abbrev Strategy : Type :=
  ∀ pos : Position, (∃ i, pos i = none) → Move pos

/-- Whether the position is fully assigned. -/
def Filled (pos : Position) : Prop := ∀ i, (pos i).isSome

/-- The polynomial determined by a fully-assigned position, with leading
coefficient `1` of degree `2012`. -/
noncomputable def polyOf (pos : Position) : ℝ[X] :=
  X ^ 2012 + ∑ i : Fin 2012, C ((pos i).getD 0) * X ^ (i : ℕ)

/-- Run the game: starting from the empty position, Albert and Homer alternate
moves following their strategies. Returns the final filled position after 2012
moves (assuming both strategies always pick a free coefficient when one exists). -/
noncomputable def play (sA sH : Strategy) : ℕ → Position
  | 0 => fun _ => none
  | k + 1 =>
      let prev := play sA sH k
      letI := Classical.propDecidable (∃ i, prev i = none)
      if h : ∃ i, prev i = none then
        let m := match turn k with
          | .Albert => sA prev h
          | .Homer => sH prev h
        m.apply
      else prev

/-- Albert wins (against Homer's strategy `sH` with his strategy `sA`) at the divisor
polynomial `m` if, after 2012 moves, the resulting polynomial is *not* divisible by `m`. -/
def AlbertBeats (m : ℝ[X]) (sA sH : Strategy) : Prop :=
  ¬ (m ∣ polyOf (play sA sH 2012))

/-- Homer wins at `m` if, after 2012 moves, the resulting polynomial is divisible by `m`. -/
def HomerBeats (m : ℝ[X]) (sA sH : Strategy) : Prop :=
  m ∣ polyOf (play sA sH 2012)

/-- A strategy `sH` is winning for Homer at divisor `m` if it beats every
Albert strategy. -/
def HomerWinning (m : ℝ[X]) (sH : Strategy) : Prop :=
  ∀ sA : Strategy, HomerBeats m sA sH

/-- The answer for part (a) and part (b): Homer wins both. -/
determine answer : Player × Player := (Player.Homer, Player.Homer)

snip begin

/-
**Solution outline.**

In both parts the total number of moves is `2012`, an even number. Albert moves
on turns `1, 3, …, 2011` (1006 moves) and Homer moves on turns `2, 4, …, 2012`
(1006 moves). In particular **Homer moves last**.

**(a) `m(x) = x − 2012`.** Homer wants `f(2012) = 0`. The value `f(2012)` is a
linear polynomial in each individual coefficient `a_i` with leading coefficient
`2012^i ≠ 0`. Homer's strategy: on every move except his last, play the value
`0` on any free coefficient. On the last move, exactly one coefficient `a_k`
remains free, and Homer chooses
`a_k := −(2012^{2012} + ∑_{i ≠ k} a_i · 2012^i) / 2012^k`,
which makes `f(2012) = 0`, hence `(x − 2012) ∣ f(x)`.

**(b) `m(x) = x² + 1`.** Write `f(x) = g(x²) + x · h(x²)`, where
`g` consists of the even-indexed coefficients `a_0, a_2, …, a_{2010}` (1006 of
them) and `h` consists of the odd-indexed coefficients `a_1, a_3, …, a_{2011}`
(1006 of them, plus the implicit leading `1` for the `x^{2012}` term, which is
in `g`). The condition `(x² + 1) ∣ f(x)` is equivalent to `g(−1) = 0` and
`h(−1) = 0`.

Both `g` and `h` involve an even number `1006` of free coefficients. Homer's
strategy is the *mirror strategy*: whenever Albert assigns a coefficient with
even index (a coefficient of `g`), Homer also assigns an even-indexed
coefficient; and likewise for odd indices. This is feasible because each parity
class has an even number of slots, so whenever Albert picks parity `p`, there
remains at least one free coefficient of parity `p` after his move (an even
number minus an odd number is odd, hence nonzero).

Following this strategy, Homer makes the last move in the even-index class and
the last move in the odd-index class. He uses these two final moves to set
`g(−1) = 0` and `h(−1) = 0` respectively (each is a linear equation in the
last free coefficient with nonzero coefficient `(−1)^? = ±1`).

The full formalization of this game-theoretic argument requires substantial
bookkeeping over partial assignments and parities and is left for future work.
-/

snip end

problem imc2012_p6 :
    -- (a) Homer has a winning strategy when m(x) = x − 2012.
    (∃ sH : Strategy, HomerWinning (X - C 2012) sH) ∧
    -- (b) Homer has a winning strategy when m(x) = x² + 1.
    (∃ sH : Strategy, HomerWinning (X ^ 2 + 1) sH) := by
  sorry

end Imc2012P6
