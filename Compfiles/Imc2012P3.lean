/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# International Mathematical Competition 2012, Problem 3

Given an integer `n > 1`, let `S_n` be the group of permutations of
`{1, 2, …, n}`. Two players, `A` and `B`, take turns selecting distinct
elements of `S_n`. The game ends when the selected elements generate `S_n`;
the player making the last move loses. `A` moves first. Which player has
a winning strategy?

Answer:
- For `n ∈ {2, 3}`: `A` has a winning strategy.
- For `n ≥ 4`: `B` has a winning strategy.
-/

namespace Imc2012P3

open Equiv

/-- Identifier for the two players. -/
inductive Player
  | A
  | B
deriving DecidableEq, Repr

/-- The other player. -/
def Player.other : Player → Player
  | .A => .B
  | .B => .A

/-- Whose turn it is after `k` moves have been made (with `A` moving first). -/
def turn (k : ℕ) : Player := if k % 2 = 0 then .A else .B

/-- A strategy for a player: given the current finite set of already-played permutations
(it must not yet generate the whole group, since otherwise the game has ended), the
strategy returns the next element to play. The strategy may return an element already in
the set, but such "moves" count as illegal/forfeit. -/
abbrev Strategy (n : ℕ) : Type :=
  Finset (Perm (Fin n)) → Perm (Fin n)

/-- The set of permutations after `k` moves of `A`'s strategy `sA` against `B`'s strategy
`sB`. We stop updating once a player would repeat: in that case the game is degenerate
and we treat that player as the loser (their move was illegal). -/
noncomputable def play (n : ℕ) (sA sB : Strategy n) : ℕ → Finset (Perm (Fin n))
  | 0 => ∅
  | k + 1 =>
      let prev := play n sA sB k
      -- If the previous state already generates the whole group, the game is over;
      -- keep the state unchanged.
      letI := Classical.propDecidable
        (Subgroup.closure ((prev : Finset (Perm (Fin n))) : Set (Perm (Fin n))) = ⊤)
      if Subgroup.closure ((prev : Finset (Perm (Fin n))) : Set (Perm (Fin n))) = ⊤ then prev
      else
        let move := match turn k with
          | .A => sA prev
          | .B => sB prev
        if move ∈ prev then prev else insert move prev

/-- The game has ended after `k` moves: the played set generates the full symmetric
group. -/
def Ended (n : ℕ) (sA sB : Strategy n) (k : ℕ) : Prop :=
  Subgroup.closure ((play n sA sB k : Finset (Perm (Fin n))) : Set (Perm (Fin n))) = ⊤

/-- A strategy `sA` for player `A` is *winning* if for every strategy `sB` of `B`, there
exists `k` such that the game has ended after `k` moves and the player who made the
`k`-th move (i.e. the player on turn `k - 1`) is `B`. -/
def WinningA (n : ℕ) (sA : Strategy n) : Prop :=
  ∀ sB : Strategy n, ∃ k : ℕ, 0 < k ∧ Ended n sA sB k ∧ ¬ Ended n sA sB (k - 1) ∧
    turn (k - 1) = Player.B

/-- A strategy `sB` for player `B` is *winning* if for every strategy `sA` of `A`, there
exists `k` such that the game has ended after `k` moves and the player who made the
`k`-th move is `A`. -/
def WinningB (n : ℕ) (sB : Strategy n) : Prop :=
  ∀ sA : Strategy n, ∃ k : ℕ, 0 < k ∧ Ended n sA sB k ∧ ¬ Ended n sA sB (k - 1) ∧
    turn (k - 1) = Player.A

/-- The answer: which player has a winning strategy. -/
determine answer (n : ℕ) : Player :=
  if n ≤ 3 then Player.A else Player.B

snip begin

/-
The proof of this problem requires a careful game-theoretic analysis. We outline the
ideas here; the full formalization is left for future work.

For `n = 2`: `S_2 = {e, (1 2)}`. `A` plays the identity `e`. Now `B` must play `(1 2)`,
which generates `S_2` together with `e`. So `B` makes the last move and loses.

For `n = 3`: `A` plays a 3-cycle, say `(1 2 3)`. The subgroup generated is `A_3`, of order
3. Any element `B` plays must be a transposition (otherwise still in `A_3 ⊊ S_3`), and any
transposition together with a 3-cycle generates `S_3`. So `B` makes the last move and
loses.

For `n ≥ 4`: `B`'s strategy is to ensure that the final maximal proper subgroup `H` (i.e.
the subgroup at the end of the game, which must be a maximal proper subgroup, since no
further legal moves are possible) has even order. The total number of moves equals `|H|`,
so an even `|H|` makes the total odd, and `A` makes the last move. To realize this,
respond to `A`'s first move `g` as follows:
- If `ord(g)` is even: `B` plays the identity `e`. Then `⟨g, e⟩ = ⟨g⟩` has even order and
  is a proper subgroup of `S_n` (since `n ≥ 4`).
- If `ord(g)` is odd: then `g` is a product of cycles of odd length, hence is an even
  permutation, so `g ∈ A_n`. `B` plays `(1 2)(3 4)`, which is also in `A_n`. Then
  `⟨g, (1 2)(3 4)⟩ ⊆ A_n ⊊ S_n` and contains `(1 2)(3 4)` which has order 2, so the
  subgroup has even order.
After this, `B` plays arbitrarily; the parity argument is preserved.

The full formalization requires substantial subgroup-lattice and parity reasoning that
is beyond the scope of this entry.
-/

snip end

problem imc2012_p3 :
    ∀ n : ℕ, 1 < n →
      (answer n = Player.A → ∃ sA : Strategy n, WinningA n sA) ∧
      (answer n = Player.B → ∃ sB : Strategy n, WinningB n sB) := by
  sorry

end Imc2012P3
