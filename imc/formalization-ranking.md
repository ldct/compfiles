# IMC Formalization Ease Ranking

Ranking of IMC problems by estimated difficulty to fully formalize (statement + proof) in Lean 4 / Mathlib, from easiest to hardest.

The main table below covers 2020-2025 (where active formalization work has been done). An appendix at the end lists all pre-2020 problems (IMC 1994-2019) that have `.tex`/PDF sources in this directory but no Lean formalization yet.

Note: IMC had 4 problems/day in 2020-2022 (8/year) and 5 problems/day in 2023-2025 (10/year), giving 54 problems in total across these six years (not 60). Pre-2020, problem counts were 12/year for 1994-2008 (6 per day) and 10/year for 2009-2019 (5 per day), giving 290 problems across 1994-2019.

Status values: `not started`, `statement formalized`, `proof in progress`, `proof complete`.

LoC = total lines of the corresponding `Compfiles/Imc{YYYY}P{N}.lean` file (includes imports, comments, `snip` helpers).

## Ranking

| Rank | Problem | Status | LoC | Topic | Statement difficulty | Proof difficulty | Notes |
|------|---------|--------|-----|-------|---------------------|------------------|-------|
| 1 | IMC 2022 P1 | proof complete | 90 | integral inequality via AM-GM, reciprocal functional equation | Low | Low | One-line AM-GM or Cauchy-Schwarz; integral facts standard. |
| 2 | IMC 2025 P6 | proof complete | 120 | MVT-style: exists xi with f(xi) - xi f'(xi) = k | Low | Low | Direct Cauchy MVT with f/x. Same flavor as Imc2025P1. |
| 3 | IMC 2023 P7 | proof complete | 183 | MVT: exists xi with f(xi) + alpha = f'(xi), find alpha | Low | Low | Cauchy MVT with F = f e^{-x}. |
| 4 | IMC 2024 P1 | proof complete | 134 | \|a\|=\|b\|=1 and a+b+a\bar b real | Low | Low | Complex-number algebra; polish trig identity. |
| 5 | IMC 2021 P1 | proof complete | 224 | unique X: X + AX + XA^2 = A given A^3=0 | Low | Low | Direct matrix manipulation; existence + uniqueness explicit. |
| 6 | IMC 2020 P2 | proof complete | 155 | rank(AB-BA+I)=1 implies trace identity | Low | Low-Med | trace cyclicity, rank-1 form X+I=vw^T. |
| 7 | IMC 2024 P7 | proof complete | 386 | invertible A+B=I, polynomial identity, det(AB) values | Low | Low | Reduces to polynomial equation in C = AB; elementary. |
| 8 | IMC 2023 P2 | proof complete | 168 | A,B,C with A^2=B^2=C^2 and B^3=ABC+2I imply A^6=I | Low | Low-Med | Pure matrix algebra; commute B with ABA. |
| 9 | IMC 2022 P2 | proof complete | 256 | A+A^k=A^T with real eigenvalues, find all A | Low | Low-Med | Minimal polynomial argument; A=0. |
| 10 | IMC 2024 P2 | proof complete | 741 | limit of Riemann-sum type expression involving log | Low | Low | Convert to Riemann sum for integral of x log x. |
| 11 | IMC 2021 P2 | proof complete | 487 | P(min Y > max X) independent of a | Low-Med | Low | Counting, finite probability. |
| 12 | IMC 2020 P1 | proof complete | 272 | words over {a,b,c,d} with even count of a,b | Low | Low | Closed form 4^{n-1}+2^{n-1}; parity generating functions. |
| 13 | IMC 2021 P7 | proof complete | 159 | \|f(0)\| ≤ max_{\|z\|=1} \|f(z)p(z)\| for monic p | Low-Med | Med | Maximum modulus principle; needs complex analysis on closed disk. |
| 14 | IMC 2025 P2 | proof complete | 479 | integral of (f'')^2 >= 15 with constraints | Low-Med | Med | Cauchy-Schwarz + integration by parts; equality condition. |
| 15 | IMC 2020 P5 | proof complete | 210 | f''f >= 2(f')^2 implies f constant | Low | Med | 1/f is concave positive => constant. |
| 16 | IMC 2022 P7 | proof complete | 148 | idempotent anti-commuting complex matrices, rank bound | Low-Med | Med | trace = rank for idempotent; sum of A_i idempotent. |
| 17 | IMC 2021 P5 | statement formalized | 58 | 2021 B = A^m + B^2 for all m => \|det A\| <= 1 | Low | Med | Eigenvalue analysis; discriminant argument. |
| 18 | IMC 2025 P3 | proof complete | 557 | rank-1 ±1 symmetric matrices commuting probability | Med | Med | Bijection to Bool × (Fin (n-1) → Bool); inner-product parity. |
| 19 | IMC 2025 P8 | proof complete | 260 | A = A^R (90-degree rotation) => Re(λ)=0 or Im(λ)=0 | Med | Med | Complex inner product; algebraic eigenvalue manipulation. |
| 20 | IMC 2025 P1 | proof complete | 454 | odd-degree polynomials with tangent-sum property | Low-Med | Med | IVT for odd-degree real polys; filter limits at ±∞. |
| 21 | IMC 2024 P3 | proof complete | 203 | {0,1}-matrix with A^2 = all-ones matrix iff n square | Med | Med | Row sums argument; cyclic block construction. |
| 22 | IMC 2023 P6 | proof complete | 129 | invariance via log-determinant, reachability | Med | Med | Invariant (det of log-matrix); simple once discovered. |
| 23 | IMC 2022 P6 | proof complete | 154 | permutation with prescribed sum mod p | Low | Med | Explicit construction x_i ≡ i^{-1} mod p. |
| 24 | IMC 2025 P7 | partial: forward, additive closure, odd-element existence done; gcd/descent/ascent TODO | 169 | subsets closed under x->2x and (x+y)/2 | Low | Med | Elementary number theory; arithmetic progressions. |
| 25 | IMC 2020 P6 | proof complete | 173 | primes with unique root of x^3-3x+1 mod p | Low | Med | Elementary finite-field + root permutation via x^2-2. |
| 26 | IMC 2024 P6 | proof complete | 157 | every f:Q->Z has a,b,c with f(b) dominating | Low | Med | Pigeonhole on finite subintervals; countable argument. |
| 27 | IMC 2023 P3 | partial: easy + many multiplicative intermediates done; classification via C[x,y] factorization TODO | 129 | P(x,y)P(z,t) = P(xz-yt, xt+yz) classify polynomials | Low | Med | Complex factorization (x+iy)^n(x-iy)^m; real-coef constraint. |
| 28 | IMC 2025 P4 | partial: reverse fully proved; forward mostly proved except x ≥ -1 case | 605 | floor identity for b^{a-1} (b^a+x)^{1/a} | Low-Med | Med | Bernoulli inequality + case analysis. Real.rpow of negative base issue on a=2 noted. |
| 29 | IMC 2021 P8 | partial: achievability (2n via {±e_i}) proved; upper bound N ≤ 2n sorry | 259 | unit vectors with 3-at-a-time orthogonality condition | Low-Med | Med | Projector trace identities; algebraic inequalities. |
| 30 | IMC 2025 P9 | proof complete | 53 | expected max of a prob 2^{-i} random process | Med | Med | Induction + geometric sum; countable probability space. |
| 31 | IMC 2021 P6 | proof complete | 282 | no injection GL_2(F_p) -> S_p | Med | Med | Element-of-order-2p + structure of S_p. |
| 32 | IMC 2024 P8 | partial: positivity + lower-bound monotonicity proved; statement indexing fixed; upper bound + telescoping series remain | 79 | recursive sequence x_n/2^n limit bounds | Low | Med-High | Induction + telescoping sums; manage auxiliary sequence. |
| 33 | IMC 2023 P4 | partial: p=2 vacuous, p=3 done; p>3 structural reduction done; `key_product_lemma` remains | 246 | a_i = i^k + i complete residue system mod p | Low-Med | Med-High | Product-of-cyclotomic-lemma; finite-field machinery. |
| 34 | IMC 2020 P4 | partial: boundary-value helpers proved; main inequality (max principle on rectangle) remains | 63 | p(x+1)-p(x)=x^{100} => p(1-t) >= p(t) | Low | High | Complex analysis / max principle on rectangle. |
| 35 | IMC 2022 P3 | proof complete | 291 | flea on Z, strategies mod p | Low-Med | Med-High | Generating functions mod p; binomial identities. |
| 36 | IMC 2023 P1 | proof complete | 271 | f(7x+1)=49f(x) with C^2 => f(x)=c(6x+1)^2 | Low | Med | Fixed-point contraction argument. |
| 37 | IMC 2020 P7 | proof complete | 136 | subgroups with index conditions are conjugate | Med | Med-High | Coset counting; finite group argument. |
| 38 | IMC 2021 P3 | partial: crude d ≤ 2 bound via n=1; definition of `Good` in file differs from original, main sSup = log 2 remains | 94 | good d: sup=ln 2 with sequence partition | Med | High | Partial fraction/log identities; sequence construction. |
| 39 | IMC 2023 P8 | proof complete | 238 | tree Wiener index times harmonic index bound | Med | Med | Cauchy-Schwarz; needs graph theory library (tree, distance). |
| 40 | IMC 2022 P5 | proof complete | 794 | count monochromatic triangles on K_{43} | Med | Med-High | Double counting 'cherries'; specific 43-vertex problem. |
| 41 | IMC 2025 P5 | statement formalized | 56 | g(n) < f(n) + n^{0.501} (sym grp max order) | Med | High | Requires weak PNT bound on prime sum; Landau's function. |
| 42 | IMC 2025 P10 | statement formalized | 51 | count pairs with (a^2+a)(b^2+b) square | Med | High | Pell equation analysis; analytic number theory estimates. |
| 43 | IMC 2024 P4 | statement formalized | 60 | subgroup gen. by n-grams independent of sequence | Med-High | High | Pigeonhole + non-periodicity + induction on group. |
| 44 | IMC 2020 P8 | statement formalized | 46 | lim (1/log log n) sum (-1)^k C(n,k) log k = 1 | Med-High | High | Frullani integral; asymptotic analysis with uniform bounds. |
| 45 | IMC 2021 P4 | statement formalized | 41 | baire class 1 via oscillation hypothesis | High | High | G_delta characterization; Lebesgue's theorem on Baire class 1. |
| 46 | IMC 2023 P5 | statement formalized | 48 | preferred permutations >= k! | Med-High | High | Combinatorial argument with ordering + counting. |
| 47 | IMC 2024 P5 | statement formalized | 58 | f(p)>=f(q) for convex hull coverage in ball | Med-High | Very High | Needs convex-geometry chi-function decomposition; measure theory. |
| 48 | IMC 2022 P4 | statement formalized | 56 | chromatic number of triple-graph, log log n bounds | Med-High | Very High | Heavy graph coloring framework; iterated chromatic number. |
| 49 | IMC 2023 P9 | statement formalized | 59 | sup V of two disjoint-projection convex sets in cube | High | Very High | Convex geometry, symmetry argument, integration. |
| 50 | IMC 2022 P8 | statement formalized | 64 | expected vertices of intersection of two convex hulls | High | Very High | Integral geometry with 2 point clouds on circle. |
| 51 | IMC 2020 P3 | statement formalized | 60 | polytope eps-approximation with C(d)eps^{1-d} vertices | High | Very High | Convex body volume estimates; polytope approximation theorem. |
| 52 | IMC 2023 P10 | statement formalized | 47 | g(n) > n^{0.999n} for factorial-LCD denominator | High | Very High | Deep p-adic valuation + 'special primes' machinery. |
| 53 | IMC 2024 P9 | statement formalized | 63 | number of nice matrices is even | High | Very High | Young-tableau friendship graph handshake; bespoke combinatorics. |
| 54 | IMC 2024 P10 | statement formalized | 53 | Fermat-prime divisibility condition on almost primes | Very High | Very High | Multi-lemma cyclotomic/order argument in F_q. |

## Aggregate summary

- **Proof complete**: 30 problems (no remaining `sorry`).
- **Partial** (non-trivial proof progress, narrowed sorry): 8 problems (ranks 24, 27, 28, 29, 32, 33, 34, 38).
- **Statement formalized only**: 16 problems (ranks 17, 40 in progress, 41–54).
- Mean LoC of proof-complete files: ~240. Range: 53 (rank 30, Imc2025P9) to 741 (rank 10, Imc2024P2).
- Mean LoC of files still at statement-only: ~54. Most are small scaffolds (40–80 LoC) that would expand significantly when a real proof is attempted.

## How accurate was the ranking?

The ranking was generated before the work began. Comparing against post-hoc LoC and ease of actually discharging proofs, the verdict: **ordering within tiers is approximately right; cross-tier calibration was systematically too optimistic; a few outliers were badly misranked.**

### Hits
- Ranks 1–16 are all closed as proofs (though several needed 200–500 LoC rather than the implied "one-day" effort).
- Tier 4 (ranks 47–54) all remain statement-only, matching the "research-level" labels.
- Rank 37 (IMC 2020 P7, subgroup conjugacy) labelled Tier 3 but closed in 136 LoC — coset-counting turned out cleaner than expected.
- Rank 35 (IMC 2022 P3) Tier 3 closed cleanly once the generating-function + Frobenius trick was spotted.

### Underestimated difficulty
- **Rank 10 (IMC 2024 P2)**: "Low/Low", needed **741 LoC** with an explicit ε-N Riemann-sum argument. Mathlib lacked a direct Riemann-sum → integral convergence lemma.
- **Rank 7 (IMC 2024 P7)**: "Low/Low", took 386 LoC for eigenvalue/spectrum machinery in ℂ.
- **Rank 11 (IMC 2021 P2)**: "Low proof", took 487 LoC setting up the rank/splitting bijection with Finset.
- **Rank 18 (IMC 2025 P3)**: 557 LoC for "Med/Med" — parity-of-inner-product counting needed heavy Finset wrangling.
- **Rank 20 (IMC 2025 P1)**: 454 LoC; filter-limit reasoning on odd-degree polynomial ends was finickier than "Low-Med".
- **Rank 28 (IMC 2025 P4)**: 605 LoC and still partial — Bernoulli for real exponents + floor arithmetic was heavier than "Med".

### Overestimated difficulty
- **Rank 30 (IMC 2025 P9)**: just 53 LoC to a full proof — self-contained inductive probability statement. Arguably belongs in the low teens.
- **Rank 39 (IMC 2023 P8)**: labeled Tier 3, closed cleanly in 238 LoC once Mathlib's tree/distance lemmas lined up.
- **Rank 21 (IMC 2024 P3)**: closed in 203 LoC; the cyclic-block construction was more mechanical than Tier 2 implied.

### Cases where the stated Lean theorem differs from the original problem
- Rank 28 (IMC 2025 P4): `Real.rpow` conventions on negative bases make the "iff" subtly false for certain x when a=2.
- Rank 32 (IMC 2024 P8): original statement had off-by-one indexing (2^n vs 2^(n+1)); the formalizing agent corrected it.
- Rank 38 (IMC 2021 P3): the `Good` predicate in the file is a simplified covering condition not matching the original sorted-partition condition; the stated sSup = log 2 may not even hold as written.

### Lessons
- LoC is dominated by **Mathlib plumbing**, not the underlying mathematical depth. "Elementary" problems with lots of index juggling blow up as much as genuinely analytic ones.
- Problems where Mathlib's API is thin (Riemann sums, complex max principle, Baire class 1, simultaneous diagonalization) punch well above their competition-difficulty.
- Ordering within tiers 1–2 is more accurate than cross-tier calibration.

## Tier breakdown

### Tier 1: Likely tractable (proof in ~1 day of work)
- IMC 2022 P1: one-line AM-GM integral inequality.
- IMC 2025 P6: direct Cauchy MVT application.
- IMC 2023 P7: existence via Cauchy MVT with e^{-x} factor.
- IMC 2024 P1: classify complex pairs via trig identity.
- IMC 2021 P1: explicit matrix X = A - A^2 with A^3=0 (proof complete).
- IMC 2020 P2: trace cyclicity and rank-1 decomposition.
- IMC 2024 P7: reduce to polynomial in C = AB and factor.
- IMC 2023 P2: pure matrix algebra to A^6=I.
- IMC 2022 P2: minimal polynomial gives A=0.
- IMC 2024 P2: sum is a Riemann sum for integral of x log x.

### Tier 2: Moderate (proof in ~1 week, needs some helper lemmas)
- IMC 2021 P2: finite-probability counting identity.
- IMC 2020 P1: parity-of-counts generating function (closed form).
- IMC 2021 P7: needs maximum modulus principle on closed disk.
- IMC 2025 P2: integration-by-parts + Cauchy-Schwarz with equality case.
- IMC 2020 P5: 1/f concave positive => constant.
- IMC 2022 P7: trace = rank for idempotent; sum of A_i is idempotent.
- IMC 2021 P5: eigenvalue + discriminant argument.
- IMC 2025 P3: rank-1 ±1 symmetric matrices commuting probability (proof complete).
- IMC 2025 P8: adjoint and J-conjugation algebra.
- IMC 2025 P1: odd-degree polynomial tangent-sum property (proof complete).
- IMC 2024 P3: row-sum structure + cyclic-block construction.
- IMC 2023 P6: invariant functional on log-matrices.
- IMC 2022 P6: explicit permutation x_i = i^{-1} mod p.
- IMC 2025 P7: arithmetic progression characterization.
- IMC 2020 P6: p=3 via x^2-2 permuting roots.
- IMC 2024 P6: pigeonhole-then-case analysis on Q.
- IMC 2023 P3: complex factorization of translation-equivariant polynomial.
- IMC 2025 P4: Bernoulli inequality case analysis.
- IMC 2021 P8: projector algebra + inequality on eigenvalue sums.
- IMC 2025 P9: induction + geometric series.
- IMC 2021 P6: order-2p element does not embed in S_p.

### Tier 3: Hard (needs substantial Mathlib infrastructure or extended effort)
- IMC 2024 P8: telescoping estimate for non-linear recursion.
- IMC 2023 P4: cyclotomic-product lemma over F_p.
- IMC 2020 P4: max-principle on complex strip.
- IMC 2022 P3: binomial identity mod p via generating functions.
- IMC 2023 P1: contraction fixed-point for C^2 function.
- IMC 2020 P7: finite-group structure with disjoint-coset analysis.
- IMC 2021 P3: ln 2 supremum; delicate sequence construction.
- IMC 2023 P8: Cauchy-Schwarz over tree distances; needs combinatorial graph library.
- IMC 2022 P5: double counting on K_43 with fixed structure.
- IMC 2025 P5: weak PNT-style prime-sum bound; Landau function.
- IMC 2025 P10: Pell equation + analytic-number-theory estimates.
- IMC 2024 P4: group-theoretic non-periodicity induction.
- IMC 2020 P8: Frullani integral + uniform-convergence estimates.
- IMC 2021 P4: Baire class 1 via Lebesgue's G_delta criterion.
- IMC 2023 P5: intricate counting with order-preserving inequalities.

### Tier 4: Very hard / research-level
- IMC 2024 P5: convex-hull coverage in ball; Euler-char-style decomposition.
- IMC 2022 P4: chromatic-number bounds via auxiliary graph construction.
- IMC 2023 P9: disjoint-projection convex-body sup volume in the cube.
- IMC 2022 P8: expected convex-hull intersection vertex count.
- IMC 2020 P3: convex body ε-approximation with polynomial vertex count.
- IMC 2023 P10: "special prime" machinery on factorial-LCD denominator.
- IMC 2024 P9: nice-matrix/Young-tableau friendship-graph argument.
- IMC 2024 P10: deep cyclotomic/order argument over F_q with multiple lemmas.

## Appendix: IMC 1994-2019 (not yet formalized)

The following problems have PDFs and pdftotext-derived `.tex` in the `imc/` directory but no Lean formalization yet. All statuses are `not started`. Ordering is chronological (oldest first), by year then by problem number. Difficulty estimates are calibrated against the main 2020-2025 table. Topics are 5-15 word summaries.

Problem counts per year: 1994-2008 had 6 problems/day × 2 days = 12 per year; 2009-2019 had 5 problems/day × 2 days = 10 per year. Total: 290 problems (15 × 12 + 11 × 10).

| Problem | Status | Topic | Statement difficulty | Proof difficulty |
|---------|--------|-------|---------------------|------------------|
| IMC 1994 P1 | not started | symmetric positive matrix, zero count in inverse | Low-Med | Med |
| IMC 1994 P2 | not started | ODE inequality f' + f^2 >= -1 implies b - a >= pi | Low | Low-Med |
| IMC 1994 P3 | not started | 2n-1 irrationals, find n with Q+-independent sums | Med | Med |
| IMC 1994 P4 | not started | linear operator FG - GF = alpha F implies F nilpotent | Low | Low-Med |
| IMC 1994 P5 | not started | limit of integral f(x)g(nx) with g periodic | Low-Med | Med |
| IMC 1994 P6 | not started | convex C^2 function, rational-point count on graph | Med | Med-High |
| IMC 1994 P7 | not started | f(a)=0 and \|f'\| <= lambda \|f\| implies f = 0 | Low | Low |
| IMC 1994 P8 | not started | extrema of (x^2 - y^2)exp(-x^2 - y^2) | Low | Low |
| IMC 1994 P9 | not started | MVT-style existence via log sum of derivatives | Low | Low |
| IMC 1994 P10 | not started | dim of commutant of diagonal matrix is sum d_i^2 | Low | Low-Med |
| IMC 1994 P11 | not started | permutation of zero-sum vectors with bounded partial sums | Med | Med |
| IMC 1994 P12 | not started | asymptotic double-log Riemann sum to 1 | Low-Med | Med |
| IMC 1995 P1 | not started | column-shift matrix Y, ranks/eigenvalues of YX^-1 | Low | Low |
| IMC 1995 P2 | not started | integral tail condition implies L^2 norm lower bound | Low | Low |
| IMC 1995 P3 | not started | f/f' -> 0 given f' -> -inf, f'' -> +inf at 0+ | Low | Low-Med |
| IMC 1995 P4 | not started | range of F(x) = integral from x to x^2 of 1/ln t | Low | Low-Med |
| IMC 1995 P5 | not started | A + t_i B nilpotent at n+1 values, show A, B nilpotent | Low | Low-Med |
| IMC 1995 P6 | not started | Clarkson-type inequality for \|x\|^p + \|y\|^p = 2 | Low-Med | Med |
| IMC 1995 P7 | not started | 3x3 real matrix with Au perp u is cross product | Low | Low |
| IMC 1995 P8 | not started | nested radical sequence, evaluate sum b_n 2^n | Low | Low-Med |
| IMC 1995 P9 | not started | roots on unit circle, roots of 2z P'(z) - n P(z) too | Med | Med |
| IMC 1995 P10 | not started | approximation by odd polynomials with only odd degrees >= 3 | Low-Med | Med |
| IMC 1995 P11 | not started | cosine sum sign-change and zero-count bounds | Med | Med-High |
| IMC 1995 P12 | not started | uniformly bounded orthonormal sequence, no pointwise limit | Low-Med | Med |
| IMC 1996 P1 | not started | determinant of symmetric arithmetic-progression matrix | Low | Low-Med |
| IMC 1996 P2 | not started | integral sin(nx)/((1+2^x) sin x) = 0 or pi | Low | Low |
| IMC 1996 P3 | not started | involutions are diagonalizable; max commuting family 2^n | Low | Med |
| IMC 1996 P4 | not started | convolution recurrence, growth rate lim sup bounds | Med | Med |
| IMC 1996 P5 | not started | asymptotic of n integral (1+ax+bx^2)^n | Med | Med-High |
| IMC 1996 P6 | not started | upper content vs lower content via contractions | Med-High | High |
| IMC 1996 P7 | not started | iterates converge iff x_{n+1} - x_n -> 0 | Low | Med |
| IMC 1996 P8 | not started | cosh k theta, cosh(k+1) theta rational implies cosh theta rational | Low | Med |
| IMC 1996 P9 | not started | commutator subgroup of <diag(2,1),unipotent> not finitely generated | Med | Med |
| IMC 1996 P10 | not started | inscribed disc of convex body, arc-length 90-degree condition | High | High |
| IMC 1996 P11 | not started | limit of sum nx/(n^2+x)^2 and error rate | Low-Med | Med |
| IMC 1996 P12 | not started | Carleman's inequality and its sharp constant | Low | Med |
| IMC 1997 P1 | not started | limit (1/n) sum log(k/n + eps_n) = -1 | Low | Low-Med |
| IMC 1997 P2 | not started | convergence under two specific permutations | Low | Med |
| IMC 1997 P3 | not started | A^2 + B^2 = AB with BA - AB invertible implies 3 divides n | Low | Med |
| IMC 1997 P4 | not started | Engel-series-like expansion for alpha in (1,2) | Med | Med-High |
| IMC 1997 P5 | not started | zero-sum lattice p-norm inequality | Med | Med |
| IMC 1997 P6 | not started | finite set family pairwise intersection + transversal | Med | Med |
| IMC 1997 P7 | not started | (sqrt f / f')' bounded near zero for C^3 f with f''(0) > 0 | Low-Med | Med |
| IMC 1997 P8 | not started | block matrix inverse determinant identity det M det H = det A | Low | Low |
| IMC 1997 P9 | not started | convergence of alternating series sum (-1)^n sin(log n)/n^a | Low | Med |
| IMC 1997 P10 | not started | trace-characterization of linear functionals on matrices | Low | Low-Med |
| IMC 1997 P11 | not started | every bijection is product of two involutions | Low | Low-Med |
| IMC 1997 P12 | not started | continuous function crossing zero uncountably often | Med | Med-High |
| IMC 1998 P1 | not started | dimension of flag-preserving endomorphism space | Low | Low |
| IMC 1998 P2 | not started | given pi_1, pi_2 generating S_n for n=3,5 but not n=4 | Med | Med |
| IMC 1998 P3 | not started | iterated logistic map f(x) = 2x(1-x), closed form | Low | Low-Med |
| IMC 1998 P4 | not started | MVT variant: exists xi with f f' + f'' = 0 | Low | Low-Med |
| IMC 1998 P5 | not started | (n-1)(P')^2 >= n P P'' for polynomials with real roots | Low | Med |
| IMC 1998 P6 | not started | integral of continuous f with xf(y) + yf(x) <= 1 | Low | Low |
| IMC 1998 P7 | not started | linear functional lies in span of given functionals | Low | Low-Med |
| IMC 1998 P8 | not started | Chebyshev interpolation bound for third derivative | Low-Med | Med |
| IMC 1998 P9 | not started | tent map has 2^n fixed points of iterate; period n nonempty | Low-Med | Med |
| IMC 1998 P10 | not started | count of monotone self-maps with f(k) = f(f(k+1)) | Med | Med |
| IMC 1998 P11 | not started | sphere family with pairwise finite intersections, countable | Med | Med-High |
| IMC 1998 P12 | not started | nonzero-values function differentiability vs divergent sum | Med | Med-High |
| IMC 1999 P1 | not started | A^3 = A + I has real solution and positive determinant | Low | Low-Med |
| IMC 1999 P2 | not started | no bijection pi of N with sum pi(n)/n^2 convergent | Low | Low-Med |
| IMC 1999 P3 | not started | bounded alternating 3^k f-differences force constant f | Low | Low-Med |
| IMC 1999 P4 | not started | strictly monotonic f with f(x^2/f(x)) = x implies linear | Low-Med | Med |
| IMC 1999 P5 | not started | grid graph cycle from 2n marked points in n x n grid | Med | Med |
| IMC 1999 P6 | not started | sharp constant for Hardy-type pointwise derivative inequality | Med-High | High |
| IMC 1999 P7 | not started | ring with x^2 = 0 for all x, show 2abc = 0 | Low | Low |
| IMC 1999 P8 | not started | probability die sum divisible by 5 via roots of unity | Low-Med | Low-Med |
| IMC 1999 P9 | not started | x_i >= -1 and sum x_i^3 = 0 implies sum x_i <= n/3 | Low | Low |
| IMC 1999 P10 | not started | no f: R+ -> R+ with f(x)^2 >= f(x+y)(f(x)+y) | Low | Low-Med |
| IMC 1999 P11 | not started | word-equivalence reducible to length <= 8 | Med | Med-High |
| IMC 1999 P12 | not started | Fourier exponential-sum lower bound via pigeonhole | Med | Med |
| IMC 2000 P1 | not started | monotone increasing f:[0,1]->[0,1] has fixed point | Low | Low |
| IMC 2000 P2 | not started | complex (w,z) with w != z and two polynomial identities | Low | Low-Med |
| IMC 2000 P3 | not started | rank-1 commutator AB - BA satisfies (AB-BA)^2 = 0 | Low | Low-Med |
| IMC 2000 P4 | not started | discrete Hardy inequality and l^2/l^1 type bound | Low-Med | Med |
| IMC 2000 P5 | not started | three idempotents summing to 0 in char-0 ring are 0 | Low | Low-Med |
| IMC 2000 P6 | not started | discretization error a_n - F^{-1}(n) -> 0 | Low-Med | Med |
| IMC 2000 P7 | not started | unit cube dissection into n smaller cubes for large n | Low | Med |
| IMC 2000 P8 | not started | nowhere-monotone continuous function, dense local minima | Low | Med |
| IMC 2000 P9 | not started | polynomial of degree n has >= n+1 preimages of {0,1} | Low | Low-Med |
| IMC 2000 P10 | not started | three-tangency sextic and ratio of bounded areas | Med | Med |
| IMC 2000 P11 | not started | Aczel-type f(x)f(yf(x)) = f(x+y) classify | Low-Med | Med |
| IMC 2000 P12 | not started | matrix exponential p(e^{AB}) nilpotent iff p(e^{BA}) is | Low | Med |
| IMC 2001 P1 | not started | sum of a permutation-transversal in n x n numbered grid | Low | Low |
| IMC 2001 P2 | not started | a^r = b^s = (ab)^t = e with coprime r,s,t abelian implies a = b = e | Low-Med | Low-Med |
| IMC 2001 P3 | not started | limit (1-t) sum t^n/(1+t^n) = ln 2 | Low | Low-Med |
| IMC 2001 P4 | not started | coefficients in {-1,0,1}, divisibility forces q-th roots as roots | Med | Med-High |
| IMC 2001 P5 | not started | similar to matrix with at most one nonzero diagonal entry | Low-Med | Med |
| IMC 2001 P6 | not started | ratio-limit of f'/g' + a f/g to (A+1) | Med | Med |
| IMC 2001 P7 | not started | nonnegative coefficient polynomial product = 1+x+...+x^n | Low | Low-Med |
| IMC 2001 P8 | not started | nested trig sequences a_n = 2 sin(pi/2^{n+1}) | Low-Med | Med |
| IMC 2001 P9 | not started | max points on unit n-sphere with pairwise distance > sqrt 2 | Low | Med |
| IMC 2001 P10 | not started | principal-minor determinant vanishing implies nilpotent permutable | Med | Med |
| IMC 2001 P11 | not started | no f:R->R with f(0)>0 and f(x+y) >= f(x)+yf(f(x)) | Low | Med |
| IMC 2001 P12 | not started | product f_n(theta) = prod sin(2^k theta) bound | Low-Med | Med-High |
| IMC 2002 P1 | not started | reflection of three standard parabolas' intersection pattern | Low-Med | Low-Med |
| IMC 2002 P2 | not started | no C^1 function with f > 0 and f'(x) = f(f(x)) | Low | Low-Med |
| IMC 2002 P3 | not started | binomial-coefficient sum identity with 2^k terms | Low | Med |
| IMC 2002 P4 | not started | iterates p_n of continuous self-map of [a,b] closed implies finite | Low | Med |
| IMC 2002 P5 | not started | monotone/C^1 function with every fiber uncountable | Low-Med | Med |
| IMC 2002 P6 | not started | power-bounded matrices via norm-difference decay | Med | High |
| IMC 2002 P7 | not started | determinant of (-1)^{\|i-j\|} Toeplitz-like matrix is n+1 | Low | Low-Med |
| IMC 2002 P8 | not started | 200 students, pigeon-hole covering by two students | Low | Low-Med |
| IMC 2002 P9 | not started | bilinear exponential sum integrality a_n b_n in Z | Low | Low-Med |
| IMC 2002 P10 | not started | tetrahedron dihedral angle inequality via spherical areas | Med-High | High |
| IMC 2002 P11 | not started | A bar A = I iff A = S bar S^{-1} for some invertible S | Low | Low-Med |
| IMC 2002 P12 | not started | Lipschitz-gradient convex function squared-gradient bound | Med | Med |
| IMC 2003 P1 | not started | a_{n+1} > 3/2 a_n sequence behavior at (3/2)^{n-1} scale | Low | Low |
| IMC 2003 P2 | not started | 51 nonzero field elements, sum-of-others permutation | Low-Med | Low-Med |
| IMC 2003 P3 | not started | 3A^3 = A^2 + A + I implies A^k converges to idempotent | Low-Med | Med |
| IMC 2003 P4 | not started | partition Z+ into A, B with aA = bB for which (a,b) | Low | Med |
| IMC 2003 P5 | not started | averaging-integral iteration f_{n+1}(x) = (1/x) int f_n | Low | Med |
| IMC 2003 P6 | not started | log-concavity of coefficients for stable polynomials | Low | Med-High |
| IMC 2003 P7 | not started | AB + A + B = 0 implies AB = BA | Low | Low |
| IMC 2003 P8 | not started | limit of sin^m t / t^n integral over [x, 2x] | Low | Low-Med |
| IMC 2003 P9 | not started | closed A subset R^n, unique-nearest-point set is dense | Med | Med |
| IMC 2003 P10 | not started | Steiner triple system with closure rule iff n = 2^m - 1 | Med | Med-High |
| IMC 2003 P11 | not started | R->R function uniformly bounded by g(x)+g(y) | Low-Med | Med |
| IMC 2003 P12 | not started | limit sum a_k / 2^k via generating-function ODE | Low-Med | Med |
| IMC 2004 P1 | not started | infinite S with all finite subset sums bounded is countable | Low | Low-Med |
| IMC 2004 P2 | not started | count of real roots of iterated x^2 - 1 equal to n + 1 | Low | Low-Med |
| IMC 2004 P3 | not started | arcsine sum interval length tends to pi/2 - 1 | Low-Med | Med |
| IMC 2004 P4 | not started | 2-coloring condition on sphere intersection forces cosphericity | Med | High |
| IMC 2004 P5 | not started | monotone doubling sequence extraction from C(k-2, 2k-4) + 1 reals | Med | Med-High |
| IMC 2004 P6 | not started | sum of log^{-4} over branches equals explicit rational function | High | High |
| IMC 2004 P7 | not started | 4x2 A, 2x4 B with specific AB, compute BA | Low | Low |
| IMC 2004 P8 | not started | graph-length inequality for square-roots of monotone functions | Low-Med | Med |
| IMC 2004 P9 | not started | p in D unit disc satisfying sum \|p - p_i\| >= n | Low | Low |
| IMC 2004 P10 | not started | eigenvalues of Lyapunov-type map X -> MX + X M^T | Med | Med |
| IMC 2004 P11 | not started | double integral 1/(x^{-1} + \|ln y\| - 1) <= 1 | Low | Low-Med |
| IMC 2004 P12 | not started | row-sum of A_n^{k-1} equals row-sum of A_k^{n-1} | Med | Med-High |
| IMC 2005 P1 | not started | rank of matrix (i+j) equals 2 (n >= 2) | Low | Low |
| IMC 2005 P2 | not started | trinary sequence bijection \|A_{n+1}\| = 3 \|B_n\| | Med | Med |
| IMC 2005 P3 | not started | integral inequality \|int f^3 - f^2(0) int f\| bound | Low | Low-Med |
| IMC 2005 P4 | not started | polynomials with coefficients permutation of 0..n and rational roots | Low | Med |
| IMC 2005 P5 | not started | f'' + 2x f' + (x^2 + 1)f bounded implies f -> 0 | Low-Med | Med |
| IMC 2005 P6 | not started | G(m), G(n) commutative implies G(gcd) commutative | Low | Med |
| IMC 2005 P7 | not started | measure of \|x^2 + bx + c\| < 1 is at most 2 sqrt 2 | Low | Low-Med |
| IMC 2005 P8 | not started | f^n polynomial for all n >= 2 implies f is polynomial | Low | Low |
| IMC 2005 P9 | not started | max subspace of matrices with tr(XY) = 0, dim C(n,2) | Low | Low-Med |
| IMC 2005 P10 | not started | MVT-style identity with third derivative and divided difference | Low | Low-Med |
| IMC 2005 P11 | not started | 1-Lipschitz gradient disc max attained at unique point for r <= 1/2 | Med | High |
| IMC 2005 P12 | not started | (p + q sqrt 7) Pell-style fixed point of SL_2(Z) Mobius | Med | Med-High |
| IMC 2006 P1 | not started | three implications between continuous/monotone/surjective | Low | Low |
| IMC 2006 P2 | not started | count of 0 <= x < 10^{2006} with 10^{2006} divides x^2 - x | Low-Med | Low-Med |
| IMC 2006 P3 | not started | integer-matrix Smith-type factorization given determinant factorization | Med | Med-High |
| IMC 2006 P4 | not started | rational function integer-valued on infinitely many integers is polynomial | Low | Med |
| IMC 2006 P5 | not started | power-sum triple comparison of a^3 + b^3 + c^3 vs d^3 + e^3 | Low | Med |
| IMC 2006 P6 | not started | Rolle-type mean value for polynomials with real roots | Low-Med | Med |
| IMC 2006 P7 | not started | triangulation of n-gon with odd-degree vertices | Med | Med |
| IMC 2006 P8 | not started | f([a,b]) closed interval of length b-a classify | Low | Low-Med |
| IMC 2006 P9 | not started | tan(sin x) > sin(tan x) on (0, pi/2) | Low | Med |
| IMC 2006 P10 | not started | rational distances on n+1 points implies linear-dependence over Q | Low | Low-Med |
| IMC 2006 P11 | not started | infinitely many coprime (m, n) with (x+m)^3 = nx three integer roots | Med | Med |
| IMC 2006 P12 | not started | GL_2(R) conjugacy: simultaneous conjugation of triples | Med | High |
| IMC 2007 P1 | not started | deg-2 integer polynomial vanishing mod 5 at all integers | Low | Low |
| IMC 2007 P2 | not started | min and max rank of n x n matrix with entries 1..n^2 | Low | Low-Med |
| IMC 2007 P3 | not started | quadratic forms representable as det(sum x_i A_i) over 2x2 | Low-Med | Med |
| IMC 2007 P4 | not started | partition group G = A union B union C, triple counts N_{ABC} = N_{CBA} | Low-Med | Med |
| IMC 2007 P5 | not started | only f = 0 satisfies sum f(k + a_i l) = 0 for given a_i | Med | Med |
| IMC 2007 P6 | not started | integer polynomial with \|P\| <= 2 on unit circle has <= 2 nonzero terms | Low | Med |
| IMC 2007 P7 | not started | continuous f with f and cf related by translation-or-rotation | Low-Med | Low-Med |
| IMC 2007 P8 | not started | x^4 + y^4 + z^4 = 0 mod 29 implies all divisible by 29 | Low | Low-Med |
| IMC 2007 P9 | not started | continuous nondecreasing f: C -> C on closed bounded C has fixed point | Low | Low-Med |
| IMC 2007 P10 | not started | det of n-cycle-squared adjacency matrix equals 4 for odd n | Low | Low-Med |
| IMC 2007 P11 | not started | smallest n with k commuting square-zero matrices and A_1 ... A_k != 0 | Med | Med |
| IMC 2007 P12 | not started | iterated f_n = f_{n-1} + f_{n-1}' eventually has all real roots | Med | High |
| IMC 2008 P1 | not started | continuous f with rational preservation is f(x) = ax + b | Low | Low-Med |
| IMC 2008 P2 | not started | multiplicative linear functional on polynomial ring is evaluation | Low-Med | Med |
| IMC 2008 P3 | not started | for integer polynomial, find a with p(a_i) dividing p(a) | Low | Med |
| IMC 2008 P4 | not started | Pareto-dominating set of 3-tuples on simplex, size >= 4 | Med | Med |
| IMC 2008 P5 | not started | finite group H normal in G with \|Aut H\| > \|Aut G\| | Med | Med |
| IMC 2008 P6 | not started | permutation displacement D(sigma) distribution parity for large d | Med | Med-High |
| IMC 2008 P7 | not started | x^{2k} - x^k + 1 divides x^{2n} + x^n + 1 implies x^{2k}+x^k+1 does too | Low | Med |
| IMC 2008 P8 | not started | two distinct ellipses with common focus meet in at most 2 points | Med | Med |
| IMC 2008 P9 | not started | 2^{n-1} divides Fibonacci-coefficient binomial sum | Low | Low |
| IMC 2008 P10 | not started | f - 2008 has >= 81 integer roots, factor g divides f implies deg g > 5 | Low | Low-Med |
| IMC 2008 P11 | not started | determinant of prime-indicator matrix is a perfect square | Low-Med | Med |
| IMC 2008 P12 | not started | equidistant set in infinite Hilbert space is orthonormal translate | Med | Med-High |
| IMC 2009 P1 | not started | f <= g on Q implies f <= g on R (continuous vs monotone) | Low | Low |
| IMC 2009 P2 | not started | (A - B) C = B A^{-1} implies C (A - B) = A^{-1} B | Low | Low |
| IMC 2009 P3 | not started | friendship graph with sum a_i^2 = n^2 - n has girth 5 | Med | Med-High |
| IMC 2009 P4 | not started | polynomial convolution with convex-coefficient kernel preserves sup norm | Med | High |
| IMC 2009 P5 | not started | weighted circumcenter identity for simplex split at interior point | Med-High | High |
| IMC 2009 P6 | not started | volume of region in R^3 given line-to-point distance ratio | Low-Med | Low-Med |
| IMC 2009 P7 | not started | second-order ODE inequality implies f(x) >= 3 e^{2x} - 2 e^{3x} | Low | Low-Med |
| IMC 2009 P8 | not started | A^2 B + B A^2 = 2 A B A implies AB - BA nilpotent | Low | Low-Med |
| IMC 2009 P9 | not started | permutation group over F_p generated by two specific polynomials | Med | Med-High |
| IMC 2009 P10 | not started | minimal covering subspace T of matrices with dim bound delta(T) <= C(n,2) | Med-High | High |
| IMC 2010 P1 | not started | integral of (x^2+1) e^{-x^2} bound via antiderivative | Low | Low |
| IMC 2010 P2 | not started | series sum 1/((4k+1)(4k+2)(4k+3)(4k+4)) closed form | Low | Low-Med |
| IMC 2010 P3 | not started | product-ratio limit for x_{n+1} = x_n^2 - 2 starting sqrt 5 | Low | Low-Med |
| IMC 2010 P4 | not started | Z minus {a x^n + b y^n} finite implies n = 1 | Low | Med |
| IMC 2010 P5 | not started | 1 + 2abc >= sum a^2 generalizes to 1 + 2(abc)^n >= sum a^{2n} | Low | Med |
| IMC 2010 P6 | not started | sequence x_{n+1} = x_n cos x_n and y_{n+1} = y_n sin y_n convergence | Low | Low-Med |
| IMC 2010 P7 | not started | product inequality prod (1 + 1/(a_k - a_0)) vs prod (1 + 1/a_k) | Low | Med |
| IMC 2010 P8 | not started | each nontrivial pi in G has unique fixed point, same across G | Med | Med |
| IMC 2010 P9 | not started | F_2 symmetric zero-diagonal matrix A^n has zero in each column | Med | Med |
| IMC 2010 P10 | not started | f vanishes on interval + prime-sum relation implies f = 0 | Med | Med-High |
| IMC 2011 P1 | not started | shadow points f(a) = f(b) and f(x) <= f(b) on interior | Low | Med |
| IMC 2011 P2 | not started | real 3x3 with tr = 0 and A^2 + A^T = I exists? | Low | Low-Med |
| IMC 2011 P3 | not started | x^p - x + 1 and p divisibility; find min interesting n | Med | High |
| IMC 2011 P4 | not started | inclusion-exclusion polynomial f(t) nondecreasing on [0,1] | Med | Med-High |
| IMC 2011 P5 | not started | in F_2 vector space (2n-1)-dim, any 4n-1 vectors have 2n summing to 0 | Med | Med |
| IMC 2011 P6 | not started | iterated chord-average sequence x_n convergence | Low-Med | Med |
| IMC 2011 P7 | not started | three-gender matching problem, k >= 3n/4 suffices | Med | Med-High |
| IMC 2011 P8 | not started | triple log-product series evaluation | Low-Med | Med |
| IMC 2011 P9 | not started | integer polynomial with integer divided differences at 0..n | Low | Med |
| IMC 2011 P10 | not started | perpendicular-bisector reflection operator on polygon vertices | Med | High |
| IMC 2012 P1 | not started | p(n) - p(n-1) partition counts equal summands > 1 | Low | Med |
| IMC 2012 P2 | not started | min rank of n x n zero-diagonal positive-off-diagonal matrix | Low | Med |
| IMC 2012 P3 | not started | S_n generating game, misere-rule winner | Med | Med-High |
| IMC 2012 P4 | not started | f continuously differentiable, f' > f(f) implies f^{(3)} <= 0 on [0, inf) | Low | Med |
| IMC 2012 P5 | not started | X^{2^n} (X + a)^{2^n} + 1 irreducible in Q[X] | Low-Med | Med-High |
| IMC 2012 P6 | not started | coefficient-assignment game for divisibility of polynomial | Med | High |
| IMC 2012 P7 | not started | sum a_{k+1}/a_k for a given nonlinear recurrence | Low | Low-Med |
| IMC 2012 P8 | not started | (n! + 1) divides (2012 n)! for finitely or infinitely many n | Low | Med |
| IMC 2012 P9 | not started | symmetric product system x_i (1 - x_{i+1}) = a | Low | Med |
| IMC 2012 P10 | not started | Plunnecke-Ruzsa \|kA\| <= c^k \|A\| for abelian group | Med | High |
| IMC 2013 P1 | not started | symmetric A, B with eigenvalues > 1 and real eigenvalue of AB satisfies \|lambda\| > 1 | Low | Low-Med |
| IMC 2013 P2 | not started | MVT-style existence f''(xi) = f(xi)(1 + 2 tan^2 xi) | Low | Low-Med |
| IMC 2013 P3 | not started | 2n students, n per trip, minimum trips for pairwise coverage | Low-Med | Med |
| IMC 2013 P4 | not started | symmetric inequality (n+1) A^2 B + (n-2) B^2 >= A^4 + (2n-2) AC | Low | Med |
| IMC 2013 P5 | not started | sequence with sum a_n^p convergent iff p is not prime | Med | High |
| IMC 2013 P6 | not started | complex z with \|z + 1\| > 2 implies \|z^3 + 1\| > 1 | Low | Low-Med |
| IMC 2013 P7 | not started | signed floor-sum identity over a full residue system | Low-Med | Med |
| IMC 2013 P8 | not started | unit vectors v_i in R^d admit common unit u with small dot products | Med | Med |
| IMC 2013 P9 | not started | infinite M of positive integers with pairwise sum square-free | Low | Med |
| IMC 2013 P10 | not started | necklace coloring with 21-window coverage, count is odd | Med | Med-High |
| IMC 2014 P1 | not started | unique symmetric 2x2 matrix with prescribed trace and determinant | Low | Low |
| IMC 2014 P2 | not started | triangular-number concatenation asymptotic alpha, beta | Low-Med | Med |
| IMC 2014 P3 | not started | polynomial with arbitrary signs yielding n distinct real roots | Low-Med | Med |
| IMC 2014 P4 | not started | perfect number e_1 even smallest-prime exponent (n > 6) | Low | Med-High |
| IMC 2014 P5 | not started | closed broken line with equal 60-degree angles, self-intersection bound | Med-High | High |
| IMC 2014 P6 | not started | digit non-zero sequence d_n(a_n) implies missing positive integers | Med | Med |
| IMC 2014 P7 | not started | symmetric matrix trace identity sum a_{ii} a_{jj} >= sum lambda_i lambda_j | Low | Med |
| IMC 2014 P8 | not started | \|(sin x / x)^{(n)}\| < 1/(n+1) | Low | Med-High |
| IMC 2014 P9 | not started | k-generic subset minimal size d(k, n) in R^n | Med-High | High |
| IMC 2014 P10 | not started | derangement identity Delta(n, k) as binomial-D sum | Med | Med-High |
| IMC 2015 P1 | not started | A^{-1} + B^{-1} = (A+B)^{-1} implies det A = det B | Low | Low-Med |
| IMC 2015 P2 | not started | bit-complement f(k) has sum bound n^2/4 | Low-Med | Med |
| IMC 2015 P3 | not started | rational-test for sum 1/F(2^n) with specific recurrence | Low-Med | Med |
| IMC 2015 P4 | not started | existence of integer m_i with sum m_i arctan(i) = arctan 16 | Low | Med |
| IMC 2015 P5 | not started | angles A_i B A_j > 90 for >= n pairs in convex hull | Med | Med-High |
| IMC 2015 P6 | not started | sum 1/(sqrt n (n+1)) < 2 | Low | Low |
| IMC 2015 P7 | not started | limit of (1/A) integral A^{1/x} dx | Low | Med |
| IMC 2015 P8 | not started | weighted word count sum over 26-letter alphabet equals 3^75 | Low-Med | Med |
| IMC 2015 P9 | not started | max dim of t-normal subspace of complex matrices | Med | High |
| IMC 2015 P10 | not started | max on [0,1] of integer polynomial > 1/e^n | Low | Med |
| IMC 2016 P1 | not started | f with infinitely many zeros and no common f = f' = 0 | Low | Low-Med |
| IMC 2016 P2 | not started | k preferred matrices with A_i^2 != 0 but A_i A_j = 0: k <= n | Low-Med | Med |
| IMC 2016 P3 | not started | fractional sum bound sum (a_i b_i - b_i^2)/(a_i + b_i) | Low | Med |
| IMC 2016 P4 | not started | union-closed family with C(n,k) + 1 k-sets has >= 3 large sets | Med | Med-High |
| IMC 2016 P5 | not started | number of permutations with inv divisible by n+1, primes comparison | Med | High |
| IMC 2016 P6 | not started | double sum x_n/k^2 bound given harmonic-weighted condition | Low-Med | Med |
| IMC 2016 P7 | not started | minimum of integral over f with f(x) + f(y) >= \|x - y\| | Low | Med |
| IMC 2016 P8 | not started | Z_n function with three fixed-point-free involutions forces n = 2 mod 4 | Med | Med-High |
| IMC 2016 P9 | not started | log-concavity of lattice-ball counting function in Z^k | Low-Med | Med |
| IMC 2016 P10 | not started | spectral bound \|A^n\| <= n/ln 2 \|A\|^{n-1} for unit-spectrum A | Med-High | High |
| IMC 2017 P1 | not started | eigenvalues of real matrix with A^2 = A^T | Low | Med |
| IMC 2017 P2 | not started | Lipschitz-derivative f > 0 satisfies (f')^2 < 2L f | Low | Low-Med |
| IMC 2017 P3 | not started | divisor-product iterates, indicator-square condition on S | Med | Med-High |
| IMC 2017 P4 | not started | friendship graph with fixed degree 1000, subgroup with 2 friends | Med | High |
| IMC 2017 P5 | not started | common roots of f(z) and z^n - 1 under self-product-zero coefficient condition | Med | Med-High |
| IMC 2017 P6 | not started | integral of f(nx) on [0,1] tends to limit L of f | Low | Low-Med |
| IMC 2017 P7 | not started | all-real-roots condition for (x+1)^n p(x) + x^n p(x+1) finite-many n | Med | High |
| IMC 2017 P8 | not started | recursive block matrix A_n integer eigenvalues with binomial multiplicities | Med | Med-High |
| IMC 2017 P9 | not started | ODE-defined sequence f_n' = f_{n-1} f_n, find limit function | Low-Med | Med-High |
| IMC 2017 P10 | not started | homothetic triangles negative-ratio, perimeter blowup as area sum approaches K | Med-High | Very High |
| IMC 2018 P1 | not started | sum a_n/c_n, c_n/b_n convergent iff sum sqrt(a_n/b_n) convergent | Low | Med |
| IMC 2018 P2 | not started | no field has multiplicative group isomorphic to additive group | Low | Med |
| IMC 2018 P3 | not started | 4x4 rational matrix with specific pattern is a rational square | Med | Med |
| IMC 2018 P4 | not started | f(b) - f(a) = (b - a) f'(sqrt(ab)) classify | Low | Med |
| IMC 2018 P5 | not started | equiangular polygon pq sides distinct integers partial-sum bound | Med | High |
| IMC 2018 P6 | not started | min dimension for k near-orthogonal nonzero vectors | Low-Med | Med |
| IMC 2018 P7 | not started | sequence with a_{n+1}^3 = a_n^2 - 8, sum \|a_{n+1} - a_n\| convergent | Low | Med |
| IMC 2018 P8 | not started | frog paths in Omega subset Z^3 of (0,0,0) to (n,n,n) | Med | Med-High |
| IMC 2018 P9 | not started | P divides Q^2 + 1 and Q divides P^2 + 1, classify (P, Q) | Low | Med-High |
| IMC 2018 P10 | not started | lattice sum (-1)^{a+b}/(a^2 + b^2) as R -> infinity | Med | High |
| IMC 2019 P1 | not started | infinite product (n^3 + 3n)^2 / (n^6 - 64) closed form | Low | Low-Med |
| IMC 2019 P2 | not started | "very good year" YEAR system of equations with two solutions | Low-Med | Med |
| IMC 2019 P3 | not started | 2 f' + x f'' >= 1 implies integral x f(x) >= 1/3 | Low | Low-Med |
| IMC 2019 P4 | not started | integrality of sequence (n+3) a_{n+2} = (6n+9) a_{n+1} - n a_n | Low | Med |
| IMC 2019 P5 | not started | odd n with A, B integer n x n and A^4 + 4 A^2 B^2 + 16 B^4 = 2019 I | Low | Med |
| IMC 2019 P6 | not started | MVT: (f(0) - g'(0))(g'(1) - f(1)) > 0 implies f(c) = g'(c) | Low | Low |
| IMC 2019 P7 | not started | convergence of sum (a_n / n)^n over composite n | Low-Med | Med |
| IMC 2019 P8 | not started | subset-sum cardinality trade-off: 1.8^n distinct values, <= 1.7^n equal | Med | Med-High |
| IMC 2019 P9 | not started | invertible n x n A, B with AB - BA = B^2 A exist for which n | Low | Med |
| IMC 2019 P10 | not started | convex hull of 2019 random points: triangle vs quadrilateral probability | Med | High |
