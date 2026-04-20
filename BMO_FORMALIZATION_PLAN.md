# BMO Formalization Plan

A plan to port 21 years of British Mathematical Olympiad problems (2005–2025) into the Compfiles Lean 4 repo.

## Inputs

- **`bmo_problems.md`** — verbatim statements for 210 problems (BMO1 + BMO2, 2005–2025), pulled from the official BMOS archive at `https://bmos.ukmt.org.uk/home/bmo.shtml`.
- **`bmo_classification.md`** — every problem assigned to one of four formalization-difficulty tiers (T1–T4).

Those two files are the source of truth for statements and difficulty. This document is the *plan of action*.

## Repo conventions to follow

- **Filename.** `Compfiles/UK{YYYY}R{1|2}P{N}.lean`. (The repo already uses the `UK` prefix for 2024, e.g. `UK2024R1P1.lean`. Do not introduce a new `BMO*` prefix.)
- **Namespace.** `namespace UK{YYYY}R{1|2}P{N}` inside the file.
- **Problem tags.** Only these are accepted by `ProblemExtraction.lean`: `.Algebra | .NumberTheory | .Combinatorics | .Geometry | .Inequality`. Functional-equation problems go under `.Algebra`.
- **Header comment.** `# British Mathematical Olympiad {YYYY}, Round {1|2}, Problem {N}` followed by the problem statement copied verbatim.
- **Structure.**
  - `problem_file { tags := [...] }` at the top
  - `snip begin … snip end` for any helper definitions/lemmas that should not appear in the extracted problem file
  - Answer-style problems use `determine solution_value : T := …`
  - Main theorem named `uk{year}_r{round}_p{n}` (lowercase, matches existing convention)
- **Year semantics.** "Year N" = BMO1 held in late autumn N−1 and BMO2 held in January/February N. Match what `bmo_problems.md` already uses.
- **Copyright header.** `/- Copyright (c) {year} The Compfiles Contributors. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: {you} -/`.
- **Register the file.** Add `import Compfiles.UK{YYYY}R{1|2}P{N}` to `Compfiles.lean` (alphabetical order).

## Difficulty tiers and strategy

Counts from `bmo_classification.md`: **T1 = 33, T2 = 62, T3 = 48, T4 = 67** (210 total).

### T1 — Easiest (33 problems): start here

Properties:
- Clean `∀`/`∃` statement over `ℕ`, `ℤ`, or `ℝ`.
- Answer is either a concrete natural number (`determine`) or a symmetric polynomial inequality.
- Proof should mostly close with `decide`, `norm_num`, `omega`, `nlinarith`, `polyrith`, or `positivity`, possibly after a short human-written reduction.

Tactics cheat-sheet:
- Small finite searches (primes <100, digits) → `decide` or `Finset.decidableAll`.
- Linear Diophantine → `omega`.
- Polynomial inequalities over ℝ with fixed-arity symmetric input → `nlinarith` / `polyrith` (often with `sq_nonneg` hints).
- Perfect-square / divisibility problems → `Nat.sqrt_eq_iff_sq_eq`, `Nat.dvd_iff_mod_eq_zero`, `ZMod` case splits.

**Proposed execution order (T1):** do all 33 before moving on; each should be one sitting. Bulk-test by running `lake build` after every 3–4 files. Hardest-in-tier are the recursive/sequence ones (`UK2020R1P2`, `UK2020R2P1`, `UK2021R1P1`, `UK2024R1P4`) — save those for last in the tier.

### T2 — Moderate (62 problems): the bulk of the effort

Properties:
- Statement is still clean, but the proof needs a construction, an induction over an ad-hoc structure, or a case split.
- Includes: functional equations with a simple solution form (linear/identity/constant), Pell-style NT, counting over small Finsets with a known closed form, recurrences requiring a Chebyshev/tangent-addition substitution, parity & invariant tracking.

Tactics cheat-sheet:
- FEs: extract `f(0)` / `f(1)`, plug in symmetric pairs, then induction on ℕ or ℤ.
- Pell / Vieta-jumping → build the explicit sequence as a function `ℕ → ℕ × ℕ`, prove it satisfies the condition by induction.
- Finset counting → `Finset.card_eq_of_bijective` into a tractable space (`Fin k`, `Equiv.Perm (Fin k)`, power sets); see existing `UK2024R1P1.lean` for the template.
- "Show `∃` infinitely many" → supply an `StrictMono` function `ℕ → X` with the property.

**Proposed execution order (T2):**
1. FE block (8 problems): `UK2009R2P3, UK2010R1P5, UK2015R1P6, UK2019R2P4, UK2020R1P6, UK2022R2P2, UK2024R2P2, UK2018R2P4`. Develop a reusable lemma set.
2. NT + small Diophantine (~20 problems): e.g. `UK2006R1P1, UK2007R1P6, UK2010R1P6, UK2011R2P2, UK2015R1P2, UK2018R2P3, UK2021R1P6, UK2025R1P5`.
3. Recurrences / sequences (~15 problems): `UK2009R1P5, UK2011R2P3, UK2015R2P1, UK2020R2P4, UK2024R1P2 (already done), …`.
4. Small-combinatorics closed forms (~10 problems).
5. The leftover algebra miscellany.

### T3 — Hard but tractable (48 problems): deliberately

Properties:
- Combinatorics with a custom bijection (analogous to the existing `UK2024R1P1.lean` ≈270-line proof).
- Extremal or game-with-known-winner problems where the bound is provable but the strategy encoding is delicate.
- Inequalities that need SOS, Schur, or an unusual substitution.
- Coordinate-friendly geometry (`UK2013R1P5` — max area with bounded sides; `UK2022R1P4` — circles through each other's centres).

Approach:
- Always state the problem and commit the `sorry`-filled skeleton first (the dashboard will track it). Only attempt proofs if there is appetite.
- For each, scope a plan before coding: write the mathematical proof, identify the Mathlib lemma for each step, then formalize.
- Accept that some T3s will slip to T4 once proof writing begins — that is fine, move them.

### T4 — Skip / very hard (67 problems): state-only at most

The vast majority are synthetic Euclidean geometry (angle-chase, cyclic quads, power of a point, Simson lines, incentre/circumcentre lemmas). Mathlib's `EuclideanGeometry` API is thin and formalizing these is disproportionately painful.

Also here: game-strategy problems needing a bespoke framework (`UK2007R2P4` Hexagonia graph, `UK2012R1P4` ball-bag, `UK2017R2P4` booby-trapped safe, `UK2018R2P2` Alice cakes, `UK2025R1P3` factoring game), and a few NT problems whose statement is easy but whose verification requires factoring 60-digit numbers (`UK2024R2P1`).

**Action:** for T4, do NOT attempt proofs. Two options per problem:
1. **Skip entirely** — omit from the repo.
2. **State only** — add the file with `problem_file` + statement + `sorry`, to track the existence of the problem on the dashboard.

Recommend option 2 for a small curated subset (e.g. one statement-only geometry file per year, 21 files) and skipping the rest. Discuss with repo maintainers before adding 67 sorry-laden files in bulk.

## Execution plan

### Phase 0 — Scaffolding (≤1 PR)

1. Create `Compfiles/UK2024R1P3.lean` placeholder **if we choose to add T4 statements** — otherwise skip.
2. Add a script (optional) `scripts/uk_new.sh {year} {round} {num}` that stamps out the file skeleton (copyright, imports, `problem_file`, namespace, header comment).
3. Verify naming: the single existing mismatch is `UK2024R1P*` — everything else is new.

### Phase 1 — T1 sweep (33 problems)

Work through T1 in the order listed in `bmo_classification.md`. Target: one PR per 3–5 problems grouped by year or theme. Expect most proofs to be <30 lines.

### Phase 2 — T2 FE sub-block (8 problems)

Treat FEs as one coherent batch. Build (if it doesn't already exist in Mathlib) any shared glue like "if `f : ℤ → ℤ` is linear on ℕ and …, then …". Commit shared lemmas once, then each problem becomes short.

### Phase 3 — T2 remaining (54 problems)

Break into roughly year-shaped PRs. After each year, run `lake exe extractProblems` and eyeball the extracted files for sensible statements.

### Phase 4 — T3 selective (≤20 problems)

Pick from T3 opportunistically — attempt a problem only when the mathematical proof is already in hand. Any T3 that resists >1 day of proof effort, convert to a `sorry`-statement and move on.

### Phase 5 — T4 triage (optional)

If maintainers agree, land one statement-only file per year for the "flagship" problem of each BMO (usually BMO1 P4 or BMO2 P2). That gives the dashboard year-by-year coverage without committing to unreachable proofs.

## Things to discuss before starting

1. **Branch strategy.** Currently on `bmo-formalization-plan` (no code yet). Consider one branch per phase vs. one branch per problem.
2. **Ownership.** The existing BMO 2024 files credit `short_c1rcuit`. Check whether they already have other years in flight before duplicating effort.
3. **Whether to use `UK` or introduce `Bmo1`/`Bmo2`.** Recommend sticking with `UK` for consistency with the 2024 files; the round is encoded as `R1`/`R2`.
4. **Geometry stance.** Confirm with maintainers that skipping synthetic geometry is acceptable, or pick a small pilot (e.g. `UK2013R1P5`, `UK2018R1P3`) as a coordinate-geometry experiment.
5. **Problem text licensing.** BMOS papers are © UKMT; confirm that verbatim inclusion in statements is acceptable (the repo already includes similar verbatim IMO/USAMO text, so this is almost certainly fine — but worth flagging).

## Open uncertainties (from the classification agent)

The following borderline calls may need re-tiering once we start writing proofs:

- `UK2018R1P3` (Geometry, currently T4) — coordinate-computable but messy; could slide to T3 with patience.
- `UK2021R1P2` (Geometry, currently T4) — really a Heron Diophantine; possibly T2/T3.
- `UK2013R1P5` (Geometry, currently T3) — Mathlib's area/triangle API is the friction point; could slide to T4.
- `UK2024R2P1` (NumberTheory, currently T4) — technically `decide`-able but kernel-infeasible; keep in T4.
- `UK2019R1P6` vs `UK2020R1P4` (Combinatorics) — split T2/T3; re-check once one is attempted.

## Deliverables checklist (per problem)

- [ ] `Compfiles/UK{YYYY}R{R}P{N}.lean` with copyright header, imports, `problem_file { tags := [...] }`, and header docstring containing the verbatim statement.
- [ ] `namespace UK{YYYY}R{R}P{N}` with the main theorem `uk{year}_r{r}_p{n}`.
- [ ] `import Compfiles.UK{YYYY}R{R}P{N}` added to `Compfiles.lean`.
- [ ] `lake build` passes with no new warnings.
- [ ] `lake exe extractProblems` produces a clean statement file under `_extracted/problems/`.
