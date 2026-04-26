/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Xuanji
-/

import Mathlib

import ProblemExtraction

problem_file { tags := [.NumberTheory] }

/-!
# International Mathematical Competition 1997, Problem 4 (Day 1)

Let `1 < α < 2`.

(a) Prove that `α` has a unique representation as an infinite product
  `α = ∏_{i ≥ 1} (1 + 1/n_i)`,
where each `n_i` is a positive integer with `n_i² ≤ n_{i+1}` for all `i`.

(b) Prove that `α` is rational if and only if there exists `m` such that
`n_{k+1} = n_k²` for all `k ≥ m` (i.e., the sequence is eventually
"saturated").

## Proof outline (official solution)

(a) **Existence and the inequality.** Define `θ_0 = α` and inductively
let `n_k` be the least positive integer with `1 + 1/n_k < θ_{k-1}`.
Since `1 < θ_{k-1} ≤ 2 < 1 + 1/(n_k - 1)` (where for `k = 1`,
`n_1 - 1 ≥ 1` because `α < 2` gives `n_1 ≥ 2`), we have
  `1 + 1/n_k < θ_{k-1} ≤ 1 + 1/(n_k - 1)`.
Then `θ_k = θ_{k-1} / (1 + 1/n_k)` satisfies
  `1 < θ_k ≤ (1 + 1/(n_k - 1))/(1 + 1/n_k) = 1 + 1/(n_k² - 1)`,
so `n_{k+1} ≥ n_k²` (since `n_{k+1}` is the least integer with
`1 + 1/n_{k+1} < θ_k`, and `1 + 1/n_k² < 1 + 1/(n_k² - 1)` is
not automatically less than `θ_k`, but a careful analysis gives
`n_{k+1} ≥ n_k²`; the official solution writes `n_k² ≤ n_{k+1}`).

The sequence `n_k` grows at least like a tower (`n_k ≥ 2^{2^{k-1}}`),
so `n_k → ∞`, hence `θ_k → 1`, and the product converges to `α`.

**Uniqueness.** If `1 + 1/n_k ≥ θ_{k-1}` then `θ_k ≤ 1`, contradicting
the convergence `θ_k → 1`. Hence at each step, `n_k` is forced to be
the *least* such integer, giving uniqueness.

(b) **The key identity.** For every integer `M ≥ 2`,
  `∏_{j ≥ 0} (1 + 1/M^{2^j}) = 1 + 1/(M − 1)`,
which follows from `(1 − 1/M)(1 + 1/M)(1 + 1/M²)(1 + 1/M^4)⋯ = 1`
(the standard telescoping `(1 − x)(1 + x)(1 + x²)⋯ = 1` for `|x| < 1`).

**(⇐)** If `n_{k+1} = n_k²` for `k ≥ m`, the tail product equals
`1 + 1/(n_m − 1)`, which is rational; combined with the rational
finite prefix, `α` is rational.

**(⇒)** Suppose `α = p/q`. Write `θ_k = p_k / q_k` with `p_k = p_{k-1} n_k`
and `q_k = q_{k-1}(n_k + 1)`. Then `p_k − q_k > 0` (since `θ_k > 1`),
and
  `(p_k − q_k) − (p_{k-1} − q_{k-1}) = (n_k − 1) p_{k-1} − n_k q_{k-1}
   = n_k (p_{k-1} − q_{k-1}) − p_{k-1}`,
which is `< 0` exactly when `θ_{k-1} < n_k / (n_k − 1) = 1 + 1/(n_k − 1)`.
If strict inequality `n_{k+1} > n_k²` holds infinitely often, then
infinitely often we have `θ_k < 1 + 1/(n_k² − 1)` strictly, equivalently
`θ_{k-1} < n_k / (n_k - 1)` strictly, giving an infinite strictly
decreasing sequence of positive integers `p_k − q_k`. Contradiction.
Hence `n_{k+1} = n_k²` from some point on.

## Status

`sorry` skeleton with:
* the auxiliary fact `prod_one_add_pow_two_succ` proving the
  Engel-style telescoping identity
  `(1 + 1/M)(1 + 1/M²)(1 + 1/M^4)⋯(1 + 1/M^{2^N}) = (1 − 1/M^{2^{N+1}})/(1 − 1/M)`
  in finite form (which gives `1 + 1/(M-1)` in the limit),
* a clean statement of (a) and (b), with the sequence `n` packaged
  as a function `ℕ → ℕ`.

The full formalization is substantial: it requires the Mathlib API
for infinite products (`Multipliable`, `HasProd`, `tprod`), an
inductive construction of the sequence `n_k`, and the integer-descent
argument in part (b). We leave the main statements as `sorry`.
-/

namespace Imc1997P4

open scoped Topology BigOperators
open Filter

/-- The Engel-product condition: `n` is a strictly positive integer
sequence with `n_i² ≤ n_{i+1}` for all `i`. We index from `0`. -/
def EngelSeq (n : ℕ → ℕ) : Prop :=
  (∀ i, 1 ≤ n i) ∧ (∀ i, n i * n i ≤ n (i + 1))

/-- The (real-valued) factor `1 + 1/n_i`. -/
noncomputable def factor (n : ℕ → ℕ) (i : ℕ) : ℝ := 1 + 1 / (n i : ℝ)

/-- The finite partial product `∏_{i < N} (1 + 1/n_i)`. -/
noncomputable def partialProd (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∏ i ∈ Finset.range N, factor n i

snip begin

/-- Telescoping identity for the geometric-tower product:
`(1 - x)(1 + x)(1 + x²)(1 + x⁴)⋯(1 + x^{2^N}) = 1 - x^{2^{N+1}}`
for all real `x` and all `N ≥ 0`. This is the algebraic engine behind
the "saturated" (`n_{k+1} = n_k²`) tail of part (b). -/
lemma telescope_pow_two (x : ℝ) :
    ∀ N : ℕ, (1 - x) * ∏ j ∈ Finset.range (N + 1), (1 + x ^ (2 ^ j))
      = 1 - x ^ (2 ^ (N + 1)) := by
  intro N
  induction N with
  | zero =>
    simp
    ring
  | succ N ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    have h : (1 - x ^ (2 ^ (N + 1))) * (1 + x ^ (2 ^ (N + 1)))
           = 1 - x ^ (2 ^ (N + 1)) * x ^ (2 ^ (N + 1)) := by ring
    rw [h]
    congr 1
    rw [← pow_add]
    congr 1
    show 2 ^ (N + 1) + 2 ^ (N + 1) = 2 ^ (N + 1 + 1)
    ring

/-- Closed form of the saturated finite product:
for integer `M ≥ 2`,
`∏_{j < N+1} (1 + 1/M^{2^j}) = (1 - 1/M^{2^{N+1}}) / (1 - 1/M)`.
This converges, as `N → ∞`, to `1 / (1 - 1/M) = M/(M-1) = 1 + 1/(M-1)`. -/
lemma saturated_partial_prod (M : ℝ) (hM : 1 < M) (N : ℕ) :
    (∏ j ∈ Finset.range (N + 1), (1 + (1 / M) ^ (2 ^ j)))
      = (1 - (1 / M) ^ (2 ^ (N + 1))) / (1 - 1 / M) := by
  have hM' : (1 : ℝ) - 1 / M ≠ 0 := by
    have : 1 / M < 1 := by
      rw [div_lt_one (by linarith : (0:ℝ) < M)]; exact hM
    linarith
  have key := telescope_pow_two (1 / M) N
  rw [eq_div_iff hM']
  linarith [key]

snip end

/-- **Part (a).** Every `α ∈ (1, 2)` admits a unique representation
as an infinite product `α = ∏ (1 + 1/n_i)` where the integer sequence
`n` satisfies the Engel condition `n_i² ≤ n_{i+1}`.

We state existence + uniqueness as a single `ExistsUnique`. -/
problem imc1997_p4_part_a (α : ℝ) (h1 : 1 < α) (h2 : α < 2) :
    ∃! n : ℕ → ℕ, EngelSeq n ∧
      Tendsto (fun N => partialProd n N) atTop (𝓝 α) := by
  -- Existence: define `n_k` by greedy choice; show partial product → α.
  -- Uniqueness: any other sequence violating the greedy choice would
  -- force `θ_k ≤ 1`, contradicting `θ_k → 1`.
  --
  -- TODO (full proof outline):
  --
  --  1. Define `θ : ℕ → ℝ` and `n : ℕ → ℕ` simultaneously by:
  --       θ 0 = α
  --       n k = Nat.find (existence of n with 1 + 1/n < θ k)
  --       θ (k+1) = θ k / (1 + 1/(n k))
  --     The Nat.find is well-defined because θ k > 1.
  --  2. Prove by induction:
  --       (i) θ k > 1 for all k,
  --       (ii) 1 + 1/(n k) < θ k ≤ 1 + 1/(n k - 1),
  --       (iii) n (k+1) ≥ (n k)² (the Engel condition),
  --       (iv) n k ≥ 2^(2^(k-1)) (super-exponential growth),
  --       (v) θ k → 1 as k → ∞.
  --  3. From (v), partialProd n N = α / θ N → α.
  --  4. Uniqueness: if n' ≠ n is another such sequence, then at the first
  --     index of difference n' k differs from the greedy choice, and one
  --     verifies θ' k ≤ 1, contradicting θ' k → 1.
  sorry

/-- **Part (b).** For `α ∈ (1, 2)` with its unique representation,
`α` is rational iff the sequence is eventually saturated:
`∃ m, ∀ k ≥ m, n_{k+1} = n_k²`. -/
problem imc1997_p4_part_b (α : ℝ) (h1 : 1 < α) (h2 : α < 2)
    (n : ℕ → ℕ) (hEngel : EngelSeq n)
    (hLim : Tendsto (fun N => partialProd n N) atTop (𝓝 α)) :
    (∃ q : ℚ, (q : ℝ) = α) ↔ (∃ m, ∀ k, m ≤ k → n (k + 1) = n k * n k) := by
  -- (⇐) Saturated tail: the tail product `∏_{k ≥ m} (1 + 1/n_k)` equals
  --     `1 + 1/(n_m - 1)` by `saturated_partial_prod` (in the limit).
  --     Combined with the rational finite prefix, α is rational.
  --
  -- (⇒) α = p/q rational. Track θ_k as a fraction p_k/q_k:
  --     p_0 = p, q_0 = q, p_{k+1} = p_k · n_k, q_{k+1} = q_k · (n_k + 1)
  --     (after suitable normalization).
  --     Then p_k - q_k > 0 (since θ_k > 1).
  --     The claim is: if n_{k+1} > n_k² (strict), then
  --       p_{k+1} - q_{k+1} < p_k - q_k.
  --     If this strict inequality held infinitely often, we'd get
  --     an infinite strictly decreasing sequence of positive integers.
  --     Contradiction. Hence eventually n_{k+1} = n_k².
  sorry

end Imc1997P4
