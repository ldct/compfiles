# IMC 2020-2025: Formalization Ease Ranking

Ranking of all IMC problems from 2020-2025 by estimated difficulty to fully formalize (statement + proof) in Lean 4 / Mathlib, from easiest to hardest.

Note: IMC had 4 problems/day in 2020-2022 (8/year) and 5 problems/day in 2023-2025 (10/year), giving 54 problems in total across these six years (not 60). Imc2025P1 and Imc2025P3 are already formalized in compfiles and are used as calibration anchors.

Status values: `not started`, `statement formalized`, `proof in progress`, `proof complete`.

## Ranking

| Rank | Problem | Status | Topic | Statement difficulty | Proof difficulty | Notes |
|------|---------|--------|-------|---------------------|------------------|-------|
| 1 | IMC 2022 P1 | not started | integral inequality via AM-GM, reciprocal functional equation | Low | Low | One-line AM-GM or Cauchy-Schwarz; integral facts standard. |
| 2 | IMC 2025 P6 | statement formalized | MVT-style: exists xi with f(xi) - xi f'(xi) = k | Low | Low | Direct Cauchy MVT with f/x. Same flavor as Imc2025P1. |
| 3 | IMC 2023 P7 | not started | MVT: exists xi with f(xi) + alpha = f'(xi), find alpha | Low | Low | Cauchy MVT with F = f e^{-x}. |
| 4 | IMC 2024 P1 | not started | \|a\|=\|b\|=1 and a+b+a\bar b real | Low | Low | Complex-number algebra; polish trig identity. |
| 5 | IMC 2021 P1 | not started | unique X: X + AX + XA^2 = A given A^3=0 | Low | Low | Direct matrix manipulation; existence + uniqueness explicit. |
| 6 | IMC 2020 P2 | not started | rank(AB-BA+I)=1 implies trace identity | Low | Low-Med | trace cyclicity, rank-1 form X+I=vw^T. |
| 7 | IMC 2024 P7 | not started | invertible A+B=I, polynomial identity, det(AB) values | Low | Low | Reduces to polynomial equation in C = AB; elementary. |
| 8 | IMC 2023 P2 | not started | A,B,C with A^2=B^2=C^2 and B^3=ABC+2I imply A^6=I | Low | Low-Med | Pure matrix algebra; commute B with ABA. |
| 9 | IMC 2022 P2 | not started | A+A^k=A^T with real eigenvalues, find all A | Low | Low-Med | Minimal polynomial argument; A=0. |
| 10 | IMC 2024 P2 | not started | limit of Riemann-sum type expression involving log | Low | Low | Convert to Riemann sum for integral of x log x. |
| 11 | IMC 2021 P2 | not started | P(min Y > max X) independent of a | Low-Med | Low | Counting, finite probability. |
| 12 | IMC 2020 P1 | not started | words over {a,b,c,d} with even count of a,b | Low | Low | Closed form 4^{n-1}+2^{n-1}; parity generating functions. |
| 13 | IMC 2021 P7 | not started | \|f(0)\| ≤ max_{\|z\|=1} \|f(z)p(z)\| for monic p | Low-Med | Med | Maximum modulus principle; needs complex analysis on closed disk. |
| 14 | IMC 2025 P2 | statement formalized | integral of (f'')^2 >= 15 with constraints | Low-Med | Med | Cauchy-Schwarz + integration by parts; equality condition. |
| 15 | IMC 2020 P5 | not started | f''f >= 2(f')^2 implies f constant | Low | Med | 1/f is concave positive => constant. |
| 16 | IMC 2022 P7 | not started | idempotent anti-commuting complex matrices, rank bound | Low-Med | Med | trace = rank for idempotent; sum of A_i idempotent. |
| 17 | IMC 2021 P5 | not started | 2021 B = A^m + B^2 for all m => \|det A\| <= 1 | Low | Med | Eigenvalue analysis; discriminant argument. |
| 18 | IMC 2025 P8 | statement formalized | A = A^R (90-degree rotation) => Re(λ)=0 or Im(λ)=0 | Med | Med | Complex inner product; algebraic eigenvalue manipulation. |
| 19 | IMC 2024 P3 | not started | {0,1}-matrix with A^2 = all-ones matrix iff n square | Med | Med | Row sums argument; cyclic block construction. |
| 20 | IMC 2023 P6 | not started | invariance via log-determinant, reachability | Med | Med | Invariant (det of log-matrix); simple once discovered. |
| 21 | IMC 2022 P6 | not started | permutation with prescribed sum mod p | Low | Med | Explicit construction x_i ≡ i^{-1} mod p. |
| 22 | IMC 2025 P7 | statement formalized | subsets closed under x->2x and (x+y)/2 | Low | Med | Elementary number theory; arithmetic progressions. |
| 23 | IMC 2020 P6 | not started | primes with unique root of x^3-3x+1 mod p | Low | Med | Elementary finite-field + root permutation via x^2-2. |
| 24 | IMC 2024 P6 | not started | every f:Q->Z has a,b,c with f(b) dominating | Low | Med | Pigeonhole on finite subintervals; countable argument. |
| 25 | IMC 2023 P3 | not started | P(x,y)P(z,t) = P(xz-yt, xt+yz) classify polynomials | Low | Med | Complex factorization (x+iy)^n(x-iy)^m; real-coef constraint. |
| 26 | IMC 2025 P4 | statement formalized | floor identity for b^{a-1} (b^a+x)^{1/a} | Low-Med | Med | Bernoulli inequality + case analysis. |
| 27 | IMC 2021 P8 | not started | unit vectors with 3-at-a-time orthogonality condition | Low-Med | Med | Projector trace identities; algebraic inequalities. |
| 28 | IMC 2025 P9 | proof complete | expected max of a prob 2^{-i} random process | Med | Med | Induction + geometric sum; countable probability space. |
| 29 | IMC 2021 P6 | not started | no injection GL_2(F_p) -> S_p | Med | Med | Element-of-order-2p + structure of S_p. |
| 30 | IMC 2024 P8 | not started | recursive sequence x_n/2^n limit bounds | Low | Med-High | Induction + telescoping sums; manage auxiliary sequence. |
| 31 | IMC 2023 P4 | not started | a_i = i^k + i complete residue system mod p | Low-Med | Med-High | Product-of-cyclotomic-lemma; finite-field machinery. |
| 32 | IMC 2020 P4 | not started | p(x+1)-p(x)=x^{100} => p(1-t) >= p(t) | Low | High | Complex analysis / max principle on rectangle. |
| 33 | IMC 2022 P3 | not started | flea on Z, strategies mod p | Low-Med | Med-High | Generating functions mod p; binomial identities. |
| 34 | IMC 2023 P1 | not started | f(7x+1)=49f(x) with C^2 => f(x)=c(6x+1)^2 | Low | Med | Fixed-point contraction argument. |
| 35 | IMC 2020 P7 | not started | subgroups with index conditions are conjugate | Med | Med-High | Coset counting; finite group argument. |
| 36 | IMC 2021 P3 | not started | good d: sup=ln 2 with sequence partition | Med | High | Partial fraction/log identities; sequence construction. |
| 37 | IMC 2023 P8 | not started | tree Wiener index times harmonic index bound | Med | Med | Cauchy-Schwarz; needs graph theory library (tree, distance). |
| 38 | IMC 2022 P5 | not started | count monochromatic triangles on K_{43} | Med | Med-High | Double counting 'cherries'; specific 43-vertex problem. |
| 39 | IMC 2025 P5 | statement formalized | g(n) < f(n) + n^{0.501} (sym grp max order) | Med | High | Requires weak PNT bound on prime sum; Landau's function. |
| 40 | IMC 2025 P10 | statement formalized | count pairs with (a^2+a)(b^2+b) square | Med | High | Pell equation analysis; analytic number theory estimates. |
| 41 | IMC 2024 P4 | not started | subgroup gen. by n-grams independent of sequence | Med-High | High | Pigeonhole + non-periodicity + induction on group. |
| 42 | IMC 2020 P8 | not started | lim (1/log log n) sum (-1)^k C(n,k) log k = 1 | Med-High | High | Frullani integral; asymptotic analysis with uniform bounds. |
| 43 | IMC 2021 P4 | not started | baire class 1 via oscillation hypothesis | High | High | G_delta characterization; Lebesgue's theorem on Baire class 1. |
| 44 | IMC 2023 P5 | not started | preferred permutations >= k! | Med-High | High | Combinatorial argument with ordering + counting. |
| 45 | IMC 2024 P5 | not started | f(p)>=f(q) for convex hull coverage in ball | Med-High | Very High | Needs convex-geometry chi-function decomposition; measure theory. |
| 46 | IMC 2022 P4 | not started | chromatic number of triple-graph, log log n bounds | Med-High | Very High | Heavy graph coloring framework; iterated chromatic number. |
| 47 | IMC 2023 P9 | not started | sup V of two disjoint-projection convex sets in cube | High | Very High | Convex geometry, symmetry argument, integration. |
| 48 | IMC 2022 P8 | not started | expected vertices of intersection of two convex hulls | High | Very High | Integral geometry with 2 point clouds on circle. |
| 49 | IMC 2020 P3 | not started | polytope eps-approximation with C(d)eps^{1-d} vertices | High | Very High | Convex body volume estimates; polytope approximation theorem. |
| 50 | IMC 2023 P10 | not started | g(n) > n^{0.999n} for factorial-LCD denominator | High | Very High | Deep p-adic valuation + 'special primes' machinery. |
| 51 | IMC 2024 P9 | not started | number of nice matrices is even | High | Very High | Young-tableau friendship graph handshake; bespoke combinatorics. |
| 52 | IMC 2024 P10 | not started | Fermat-prime divisibility condition on almost primes | Very High | Very High | Multi-lemma cyclotomic/order argument in F_q. |

Not present in the main ranking but formalized in compfiles:
- IMC 2025 P1: proof complete (not listed above; would sit near rank 20).
- IMC 2025 P3: proof complete (not listed above; would sit near rank 18).

## Tier breakdown

### Tier 1: Likely tractable (proof in ~1 day of work)
- IMC 2022 P1: one-line AM-GM integral inequality.
- IMC 2025 P6: direct Cauchy MVT application.
- IMC 2023 P7: existence via Cauchy MVT with e^{-x} factor.
- IMC 2024 P1: classify complex pairs via trig identity.
- IMC 2021 P1: explicit matrix X = A - A^2 with A^3=0.
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
- IMC 2025 P8: adjoint and J-conjugation algebra.
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
