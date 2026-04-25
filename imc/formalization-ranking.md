# IMC Formalization Ease Ranking

Ranking of IMC problems by estimated difficulty to fully formalize (statement + proof) in Lean 4 / Mathlib, from easiest to hardest.

The main table below covers 2000-2025 (the 54 problems from 2020-2025 where active formalization work has been done, the 100 problems from 2010-2019 which are ranked but not yet formalized, the 58 problems from 2005-2009 which are ranked but not yet formalized, and the 60 problems from 2000-2004 now integrated from the appendix). An appendix at the end lists all remaining pre-2000 problems (IMC 1994-1999) that have `.tex`/PDF sources in this directory but no Lean formalization yet.

Note: IMC had 4 problems/day in 2020-2022 (8/year) and 5 problems/day in 2023-2025 (10/year), giving 54 problems in total across these six years (not 60). Pre-2020, problem counts were 12/year for 1994-2008 (6 per day) and 10/year for 2009-2019 (5 per day). The main table now contains 272 problems (54 from 2020-2025, 100 from 2010-2019, 58 from 2005-2009, and 60 from 2000-2004); the appendix contains 72 problems from 1994-1999.

Status values: `not started`, `statement formalized`, `proof in progress`, `proof complete`.

LoC = total lines of the corresponding `Compfiles/Imc{YYYY}P{N}.lean` file (includes imports, comments, `snip` helpers).

## Ranking

| Rank | Problem | Status | LoC | Topic | Statement difficulty | Proof difficulty | Notes |
|------|---------|--------|-----|-------|---------------------|------------------|-------|
| 1 | IMC 2022 P1 | proof complete | 90 | integral inequality via AM-GM, reciprocal functional equation | Low | Low | One-line AM-GM or Cauchy-Schwarz; integral facts standard. |
| 2 | IMC 2019 P6 | proof complete | 88 | MVT: f(0)-g'(0) and g'(1)-f(1) opposite signs implies f=g' somewhere | Low | Low | Apply IVT to f - g' on [0,1]. |
| 3 | IMC 2013 P2 | proof complete | 193 | MVT: f twice-differentiable, f(0)=0, find xi with f''=f(1+2tan^2) | Low | Low | Consider g(x)=f(x)cos x; apply Rolle to g on (-pi/2,pi/2). |
| 4 | IMC 2015 P6 | proof complete | 163 | convergent series sum 1/(sqrt n (n+1)) bounded by 2 | Low | Low | Simple telescoping or direct comparison. |
| 5 | IMC 2025 P6 | proof complete | 120 | MVT-style: exists xi with f(xi) - xi f'(xi) = k | Low | Low | Direct Cauchy MVT with f/x. Same flavor as Imc2025P1. |
| 6 | IMC 2023 P7 | proof complete | 183 | MVT: exists xi with f(xi) + alpha = f'(xi), find alpha | Low | Low | Cauchy MVT with F = f e^{-x}. |
| 7 | IMC 2024 P1 | proof complete | 134 | \|a\|=\|b\|=1 and a+b+a\bar b real | Low | Low | Complex-number algebra; polish trig identity. |
| 8 | IMC 2010 P1 | proof complete | 82 | integral of (x^2+1)e^{-x^2} on [a,b] bounded below by e^{-a^2}-e^{-b^2} | Low | Low | Use x^2+1 >= 2x and antiderivative -e^{-x^2}. |
| 9 | IMC 2009 P1 | proof complete | 118 | f <= g on dense Q implies f <= g on R for continuous vs monotone | Low | Low | Density of Q in R plus one-sided continuity. |
| 10 | IMC 2006 P1 | proof complete | 112 | three implications between continuous, monotone, surjective for R->R | Low | Low | Direct IVT and monotonicity arguments. |
| 11 | IMC 2009 P2 | proof complete | 48 | (A-B)C = B A^{-1} implies C(A-B) = A^{-1} B | Low | Low | Pure matrix-algebra manipulation. |
| 12 | IMC 2015 P1 | proof complete | 104 | A^{-1}+B^{-1}=(A+B)^{-1} implies det A = det B | Low | Low-Med | Classical identity; multiply through, classify over C. |
| 13 | IMC 2013 P6 | proof complete | 85 | \|z+1\| > 2 implies \|z^3+1\| > 1 | Low | Low | Factor z^3+1=(z+1)(z^2-z+1); triangle inequality on second factor. |
| 14 | IMC 2003 P7 | proof complete | 68 | AB+A+B=0 implies AB=BA | Low | Low | (A+I)(B+I)=I, so A+I and B+I commute. |
| 15 | IMC 2007 P1 | proof complete | 103 | deg-2 integer polynomial vanishing mod 5 at all integers | Low | Low | Evaluate at small residues; linear system over Z/5. |
| 16 | IMC 2004 P9 | proof complete | 84 | exists p in unit disc with sum \|p - p_i\| >= n | Low | Low | Pick p opposite centroid; triangle inequality. |
| 17 | IMC 2021 P1 | proof complete | 224 | unique X: X + AX + XA^2 = A given A^3=0 | Low | Low | Direct matrix manipulation; existence + uniqueness explicit. |
| 18 | IMC 2020 P2 | proof complete | 155 | rank(AB-BA+I)=1 implies trace identity | Low | Low-Med | trace cyclicity, rank-1 form X+I=vw^T. |
| 19 | IMC 2005 P1 | proof complete | 149 | rank of n x n matrix with (i,j)-entry i+j equals 2 | Low | Low | Write as sum of two rank-1 matrices; 2x2 minor nonzero. |
| 20 | IMC 2001 P1 | proof complete | 70 | n x n grid has permutation-transversal with prescribed sum | Low | Low | Any permutation gives the sum; direct evaluation. |
| 21 | IMC 2014 P1 | proof complete | 136 | unique symmetric 2x2 real matrix with prescribed trace and determinant | Low | Low | Solve a^2=4b for discriminant zero condition. |
| 22 | IMC 2008 P9 | proof complete | 181 | 2^{n-1} divides Fibonacci-coefficient binomial sum | Low | Low | Direct identity via generating functions or induction. |
| 23 | IMC 2005 P8 | proof complete | 126 | if f^n is polynomial for all n >= 2 then f is polynomial | Low | Low | Degree argument; rational-function normal form. |
| 24 | IMC 2019 P1 | proof complete | 151 | infinite product (n^3+3n)^2/(n^6-64) closed form | Low | Low-Med | Partial-fraction telescoping on (n^3-4n)(n^3+4n). |
| 25 | IMC 2010 P2 | proof complete | 347 | series sum 1/((4k+1)(4k+2)(4k+3)(4k+4)) closed form | Low | Low-Med | Partial fractions give (ln 2)/6 - ... closed form; telescoping. |
| 26 | IMC 2024 P7 | proof complete | 386 | invertible A+B=I, polynomial identity, det(AB) values | Low | Low | Reduces to polynomial equation in C = AB; elementary. |
| 27 | IMC 2019 P3 | proof complete | 155 | 2f'+xf''>=1 implies integral of xf >= 1/3 | Low | Low-Med | Integration by parts plus hypothesis; direct. |
| 28 | IMC 2005 P3 | proof complete | 211 | integral inequality \|int f^3 - f^2(0) int f\| <= max\|f'\|(int f)^2 | Low | Low-Med | Integrate -M f <= f f' <= M f, multiply by f, integrate again. |
| 29 | IMC 2011 P2 | proof complete | 171 | exists real 3x3 A with tr(A)=0 and A^2+A^T=I? | Low | Low-Med | Trace gives tr(A^2)=3; Frobenius-norm contradiction or explicit construction. |
| 30 | IMC 2000 P3 | proof complete | 90 | rank-1 commutator AB-BA satisfies (AB-BA)^2 = 0 | Low | Low-Med | trace=0 on rank-1 matrix forces nilpotent 2x2 Jordan form. |
| 31 | IMC 2005 P10 | proof complete | 195 | MVT-style identity with third derivative and divided difference | Low | Low-Med | Taylor expansion with remainder; direct application. |
| 32 | IMC 2004 P7 | proof complete | 122 | 4x2 A, 2x4 B with given AB block; compute BA | Low | Low | 2x2 block factorization; B_1 = A_1^{-1}, A_2 = -A_1. |
| 33 | IMC 2023 P2 | proof complete | 168 | A,B,C with A^2=B^2=C^2 and B^3=ABC+2I imply A^6=I | Low | Low-Med | Pure matrix algebra; commute B with ABA. |
| 34 | IMC 2017 P2 | proof complete | 182 | Lipschitz derivative and f>0 implies (f')^2 < 2Lf | Low | Low-Med | Classical: use Taylor expansion of f at nearby point. |
| 35 | IMC 2009 P8 | partial | 85 | A^2 B + B A^2 = 2 A B A implies AB - BA nilpotent | Low | Low-Med | Expand powers of (AB-BA); use given identity to reduce. |
| 36 | IMC 2017 P6 | proof complete | 176 | integral of f(nx) over [0,1] tends to lim f | Low | Low-Med | Substitute u=nx and split at a large threshold. |
| 37 | IMC 2016 P1 | proof complete | 111 | f with infinite zeros and no common f=f'=0 forces f(a)f(b)=0 | Low | Low-Med | Accumulation of zeros plus Rolle gives f=f'=0. |
| 38 | IMC 2006 P8 | proof complete | 289 | classify continuous f with f([a,b]) closed interval of length b-a | Low | Low-Med | Monotone pieces plus length preservation. |
| 39 | IMC 2008 P1 | proof complete | 231 | continuous f with f(Q) subset Q and f(rationals closed under add) is f(x)=ax+b | Low | Low-Med | Density of Q plus Cauchy-style functional equation. |
| 40 | IMC 2000 P1 | proof complete | 70 | monotone increasing f:[0,1]->[0,1] has a fixed point | Low | Low | sup of {x : f(x) > x}; no continuity required. |
| 41 | IMC 2022 P2 | proof complete | 256 | A+A^k=A^T with real eigenvalues, find all A | Low | Low-Med | Minimal polynomial argument; A=0. |
| 42 | IMC 2000 P5 | proof complete | 149 | three idempotents summing to 0 in char-0 ring are all 0 | Low | Low-Med | 3[e,f]=0 forces commutation; reduce to e=f=g. |
| 43 | IMC 2010 P6 | proof complete | 166 | x_{n+1}=x_n cos x_n and y_{n+1}=y_n sin y_n convergence | Low | Low-Med | Monotone bounded; show limit satisfies x cos x = x or y sin y = y. |
| 44 | IMC 2007 P9 | proof complete | 191 | continuous nondecreasing f: [a,b] -> [a,b] has fixed point | Low | Low-Med | Direct IVT on f(x)-x. |
| 45 | IMC 2005 P7 | proof complete | 171 | measure of {x : \|x^2 + bx + c\| < 1} is at most 2 sqrt 2 | Low | Low-Med | Completing square; interval-length bound. |
| 46 | IMC 2009 P7 | proof complete | 215 | f'' - 3f' + 2f <= 0 with f(0)=f'(0)=1 implies f(x) >= 3 e^{2x} - 2 e^{3x} | Low | Low-Med | Comparison ODE with explicit solution difference. |
| 47 | IMC 2010 P3 | proof complete | 218 | x_{n+1}=x_n^2-2, x_1=sqrt 5; limit of x_1..x_n / x_{n+1} | Low | Low-Med | Parametrize x_n = 2 cosh(2^{n-1} t); telescope product. |
| 48 | IMC 2004 P11 | partial | 93 | double integral of 1/(1/x + \|ln y\| - 1) bounded by 1 | Low | Low-Med | Show 1/x - 1 >= \|ln x\|; pointwise substitution bound. |
| 49 | IMC 2007 P2 | partial | 142 | min and max rank of n x n matrix with entries 1..n^2 | Low | Low-Med | Explicit constructions plus rank-bound arguments. |
| 50 | IMC 2004 P1 | proof complete | 142 | infinite S subset R+ with all finite sums bounded is countable | Low | Low-Med | Count {s >= 1/n}; union of countable sets. |
| 51 | IMC 2006 P10 | proof complete | 236 | rational pairwise distances on n+1 points implies Q-linear dependence | Low | Low-Med | Cayley-Menger determinant over Q. |
| 52 | IMC 2004 P2 | proof complete | 220 | iterated x^2-1 polynomial has n+1 real roots | Low | Low-Med | Induction on iteration; count sign changes. |
| 53 | IMC 2012 P7 | proof complete | 214 | sum a_{k+1}/a_k for nonlinear recurrence a_{n+1}=n a_n^2/(1+(n+1)a_n) | Low | Low-Med | Telescoping of 1/a_n difference; closed-form sum. |
| 54 | IMC 2008 P10 | proof complete | 115 | f-2008 has >= 81 integer roots; factor g of f with deg g between 2 and 5 does not divide | Low | Low-Med | Integer-root factor-size argument on f-2008. |
| 55 | IMC 2002 P7 | proof complete | 119 | determinant of (-1)^{\|i-j\|} Toeplitz-like matrix is n+1 | Low | Low-Med | Row-reduce to tridiagonal; direct expansion. |
| 56 | IMC 2018 P7 | proof complete | 303 | a_{n+1}^3 = a_n^2 - 8, show sum \|a_{n+1}-a_n\| converges | Low | Med | Fixed point near -2 with contraction; telescoping. |
| 57 | IMC 2007 P8 | proof complete | 54 | x^4 + y^4 + z^4 = 0 mod 29 implies 29 divides x, y, z | Low | Low-Med | Enumerate fourth powers mod 29. |
| 58 | IMC 2003 P1 | proof complete | 155 | a_{n+1} > (3/2) a_n sequence behavior at (3/2)^{n-1} scale | Low | Low | Monotone ratio argument; explicit bound. |
| 59 | IMC 2005 P9 | proof complete | 232 | max subspace of n x n matrices with tr(XY)=0 has dim C(n,2) | Low | Low-Med | Symmetric/antisymmetric split; trace-form kernel. |
| 60 | IMC 2007 P10 | partial | 266 | det of n-cycle-squared adjacency matrix equals 4 for odd n | Low | Low-Med | Expand determinant via circulant diagonalization. |
| 61 | IMC 2009 P6 | partial | 94 | volume of region in R^3 defined by line-to-point distance ratio | Low-Med | Low-Med | Set up integral in cylindrical coordinates. |
| 62 | IMC 2002 P8 | proof complete | 125 | 200 students; pigeonhole covering by two chosen students | Low | Low-Med | Combinatorial pigeonhole on friend sets. |
| 63 | IMC 2024 P2 | proof complete | 741 | limit of Riemann-sum type expression involving log | Low | Low | Convert to Riemann sum for integral of x log x. |
| 64 | IMC 2011 P1 | proof complete | 133 | shadow points f(a)=f(b) and f(x)<=f(b) on (a,b) | Low | Med | Continuity + IVT argument on shadow-point structure. |
| 65 | IMC 2021 P2 | proof complete | 487 | P(min Y > max X) independent of a | Low-Med | Low | Counting, finite probability. |
| 66 | IMC 2000 P2 | proof complete | 133 | complex (w,z) with w != z, p(w)=p(z), q(w)=q(z) for given quintics | Low | Low-Med | Symmetric polys w+z=1, wz in {1,2}; solve. |
| 67 | IMC 2020 P1 | proof complete | 272 | words over {a,b,c,d} with even count of a,b | Low | Low | Closed form 4^{n-1}+2^{n-1}; parity generating functions. |
| 68 | IMC 2002 P9 | partial | 105 | bilinear integer pair a_n + b_n sqrt 2 via conjugate expansion | Low | Low-Med | Induction using conjugate expansion. |
| 69 | IMC 2007 P7 | proof complete | 112 | continuous f with f and cf related by translation-or-rotation | Low-Med | Low-Med | Functional-equation case analysis. |
| 70 | IMC 2002 P11 | proof complete | 343 | A bar(A) = I iff A = S bar(S)^{-1} for some invertible S | Low | Low-Med | Hilbert 90-style matrix descent. |
| 71 | IMC 2019 P4 | partial | 111 | integrality of sequence (n+3)a_{n+2}=(6n+9)a_{n+1}-na_n | Low | Med | Derive closed form via generating function; sum of Catalan-like terms. |
| 72 | IMC 2001 P2 | proof complete | 72 | a^r=b^s=(ab)^t=e with coprime r,s,t and abelian implies a=b=e | Low-Med | Low-Med | Bezout coprime combination; order divides 1. |
| 73 | IMC 2006 P2 | proof complete | 316 | count of 0 <= x < 10^{2006} with 10^{2006} divides x^2 - x | Low-Med | Low-Med | CRT over 2^{2006} and 5^{2006}; idempotent count. |
| 74 | IMC 2001 P7 | statement formalized | 64 | nonneg-coefficient polynomial product equals 1 + x + ... + x^n | Low | Low-Med | Cyclotomic factorization of x^{n+1}-1. |
| 75 | IMC 2005 P4 | partial | 232 | polynomials with coefficients a permutation of 0..n and all rational roots | Low | Med | Vieta + AM-HM forces small degree; explicit enumeration. |
| 76 | IMC 2001 P3 | statement formalized | 90 | limit (1-t) sum t^n/(1+t^n) equals ln 2 as t -> 1^- | Low | Low-Med | Abel summation; geometric comparison. |
| 77 | IMC 2019 P5 | proof complete | 111 | no odd n with integer A,B and A^4+4A^2B^2+16B^4=2019I | Low | Med | Factor over Z[i], use determinants and parity mod 2. |
| 78 | IMC 2003 P8 | proof complete | 528 | limit of integral sin^m t / t^n over [x, 2x] as x -> 0 | Low | Low-Med | Taylor expansion; leading-order computation. |
| 79 | IMC 2005 P5 | proof complete | 327 | \|f''+2xf'+(x^2+1)f\| <= 1 implies f(x) -> 0 at infinity | Low-Med | Med | Integrating factor e^{x^2/2}; L'Hopital on growth ratio. |
| 80 | IMC 2000 P9 | proof complete | 146 | polynomial of degree n has at least n+1 preimages of {0,1} | Low | Low-Med | Count roots of p and p-1; fundamental theorem. |
| 81 | IMC 2015 P4 | proof complete | 407 | exist integer m_i with sum m_k arctan(k) = arctan 16 | Low | Med | Gauss integers: convert to product of (1+ki); diophantine. |
| 82 | IMC 2002 P1 | proof complete | 81 | reflection-related triple of parabolas, intersection pattern | Low-Med | Low-Med | Solve systems of quadratics; case analysis. |
| 83 | IMC 2018 P4 | partial | 128 | f(b)-f(a)=(b-a)f'(sqrt(ab)) classify f | Low | Med | Substitute and differentiate; get f(x)=A ln x + B form. |
| 84 | IMC 2002 P2 | proof complete | 75 | no C^1 positive f on R with f'(x) = f(f(x)) | Low | Low-Med | Growth analysis; contradict continuity. |
| 85 | IMC 2008 P3 | proof complete | 263 | for integer polynomial, find a with p(a_i) dividing p(a) | Low | Med | Chinese remainder + a-b divides p(a)-p(b). |
| 86 | IMC 2003 P2 | proof complete | 330 | 51 nonzero field elements admit sum-of-others permutation | Low-Med | Low-Med | Counting sums + pigeonhole / Hall. |
| 87 | IMC 2010 P5 | proof complete | 156 | 1+2abc >= sum a^2 generalizes to 1+2(abc)^n >= sum a^{2n} | Low | Med | Trig substitution a=cos A etc.; induction on n. |
| 88 | IMC 2001 P9 | not started | - | max points on unit n-sphere with pairwise distance > sqrt 2 is n+1 | Low | Med | Inner products nonpositive; dim+1 linear-independence bound. |
| 89 | IMC 2008 P7 | proof complete | 347 | x^{2k} - x^k + 1 divides x^{2n} + x^n + 1 implies x^{2k}+x^k+1 does too | Low | Med | Root conditions via 6k-th roots of unity. |
| 90 | IMC 2012 P4 | statement formalized | 49 | f continuously differentiable with f'>f(f) implies f^{(3)}<=0 on [0,inf) | Low | Med | Sign analysis + iterated monotonicity on f, f(f). |
| 91 | IMC 2007 P3 | proof complete | 182 | quadratic forms representable as det(sum x_i A_i) over 2x2 | Low-Med | Med | Discriminant and trace-zero basis argument. |
| 92 | IMC 2006 P5 | statement formalized | 42 | power-sum triple comparison of a^3 + b^3 + c^3 vs d^3 + e^3 | Low | Med | Bounding via power-mean inequalities. |
| 93 | IMC 2010 P7 | proof complete | 179 | product (1+1/(a_k-a_0)) <= (1+1/a_0) product (1+1/a_k) | Low | Med | Induction on n and a_{k+1}-a_k >= 1 hypothesis. |
| 94 | IMC 2008 P2 | proof complete | 269 | multiplicative linear functional on polynomial ring is evaluation | Low-Med | Med | Kernel analysis; reduction to x-a generator. |
| 95 | IMC 2004 P3 | proof complete | 377 | arcsine-sum interval length tends to pi/2 - 1 | Low-Med | Med | Riemann-sum limit; compute integral. |
| 96 | IMC 2021 P7 | proof complete | 159 | \|f(0)\| ≤ max_{\|z\|=1} \|f(z)p(z)\| for monic p | Low-Med | Med | Maximum modulus principle; needs complex analysis on closed disk. |
| 97 | IMC 2006 P4 | statement formalized | 56 | rational function integer-valued on infinitely many integers is polynomial | Low | Med | Degree of denominator bounded; polynomial division. |
| 98 | IMC 2000 P7 | proof complete | 169 | unit cube dissectible into n smaller cubes for all n >= N | Low | Med | Split one cube into 8; base-case induction on n. |
| 99 | IMC 2007 P4 | proof complete | 171 | G = A sqcup B sqcup C partition; triple counts N_{ABC} = N_{CBA} | Low-Med | Med | Group-action reversal argument. |
| 100 | IMC 2025 P2 | proof complete | 479 | integral of (f'')^2 >= 15 with constraints | Low-Med | Med | Cauchy-Schwarz + integration by parts; equality condition. |
| 101 | IMC 2001 P8 | proof complete | 196 | nested trig sequence a_n = 2 sin(pi/2^{n+1}) recursion | Low-Med | Med | Half-angle identity; induction on n. |
| 102 | IMC 2020 P5 | proof complete | 210 | f''f >= 2(f')^2 implies f constant | Low | Med | 1/f is concave positive => constant. |
| 103 | IMC 2017 P1 | proof complete | 222 | eigenvalues of real matrix with A^2=A^T | Low | Med | Classify: 0, 1, or roots of x^2+x+1=0 (primitive cube root of unity). |
| 104 | IMC 2002 P3 | proof complete | 340 | binomial-coefficient sum identity with 2^k-indexed terms | Low | Med | Generating function or Vandermonde; finite sum. |
| 105 | IMC 2005 P6 | proof complete | 319 | G(m), G(n) commutative implies G(gcd(m,n)) commutative | Low | Med | Commutator is central; Bezout-based conjugation analysis. |
| 106 | IMC 2003 P3 | statement formalized | 44 | 3A^3 = A^2 + A + I implies A^k converges to idempotent | Low-Med | Med | Roots of 3x^3-x^2-x-1; only x=1 on unit circle. |
| 107 | IMC 2006 P6 | statement formalized | 62 | Rolle-type mean value for polynomials with real roots | Low-Med | Med | Induction on degree plus Rolle between consecutive roots. |
| 108 | IMC 2000 P4 | partial | 213 | discrete Hardy inequality l^2 tail vs l^1 bound | Low-Med | Med | Cauchy-Schwarz + integral bound on reciprocal root kernel. |
| 109 | IMC 2006 P9 | statement formalized | 71 | tan(sin x) > sin(tan x) on (0, pi/2) | Low | Med | Power-series comparison plus monotonicity. |
| 110 | IMC 2000 P11 | not started | - | classify f with f(x) f(y f(x)) = f(x+y) | Low-Med | Med | Aczel-type FE; reciprocal form f(x)=1/(1+cx). |
| 111 | IMC 2022 P7 | proof complete | 148 | idempotent anti-commuting complex matrices, rank bound | Low-Med | Med | trace = rank for idempotent; sum of A_i idempotent. |
| 112 | IMC 2001 P6 | statement formalized | 58 | ratio-limit f'/g' + a f/g tends to A + 1 | Med | Med | Generalized L'Hopital with additive correction. |
| 113 | IMC 2016 P3 | proof complete | 66 | fractional sum inequality with a_i b_i numerator | Low | Med | Cauchy-Schwarz and tangent-line trick on (ab-b^2)/(a+b). |
| 114 | IMC 2004 P10 | proof complete | 96 | eigenvalues of Lyapunov-type map X -> MX + X M^T | Med | Med | lambda_i + lambda_j with correct multiplicities; Jordan form. |
| 115 | IMC 2008 P11 | partial | 368 | determinant of prime-indicator matrix is a perfect square | Low-Med | Med | Row/column factorization over Z. |
| 116 | IMC 2000 P12 | proof complete | 332 | p(e^{AB}) nilpotent iff p(e^{BA}) is | Low | Med | Spectra of AB and BA agree off zero; functional calculus. |
| 117 | IMC 2015 P10 | statement formalized | 43 | int-coeff polynomial of degree n has max on [0,1] > 1/e^n | Low | Med | Shifted Chebyshev-like bound; coefficient integrality. |
| 118 | IMC 2001 P5 | statement formalized | 62 | every matrix similar to one with at most one nonzero diagonal entry | Low-Med | Med | Induction on n; conjugate by suitable GL_n element. |
| 119 | IMC 2007 P6 | statement formalized | 110 | integer polynomial with \|P\| <= 2 on unit circle has <= 2 nonzero terms | Low | Med | Parseval-type inequality on coefficients. |
| 120 | IMC 2001 P11 | proof complete | 161 | no f:R->R with f(0)>0 and f(x+y) >= f(x) + y f(f(x)) | Low | Med | Iterate to derive unbounded growth, contradiction. |
| 121 | IMC 2015 P7 | proof complete | 401 | limit (1/A) integral_1^A A^{1/x} dx as A -> infinity | Low | Med | Substitute u=A^{1/x}; asymptotic of 1/ln A factor. |
| 122 | IMC 2002 P4 | partial | 195 | iterates p_n of continuous self-map [a,b]->[a,b] closed implies finite | Low | Med | Topological dynamics; orbit closure finite. |
| 123 | IMC 2012 P1 | proof complete | 139 | p(n)-p(n-1) equals partitions into parts > 1 | Low | Med | Generating-function bijection; needs Finset partitions API. |
| 124 | IMC 2003 P4 | proof complete | 279 | partition Z+ into A, B with a A = b B; classify (a, b) | Low | Med | Characterize via gcd/lcm and 2-adic valuation. |
| 125 | IMC 2021 P5 | statement formalized | 58 | 2021 B = A^m + B^2 for all m => \|det A\| <= 1 | Low | Med | Eigenvalue analysis; discriminant argument. |
| 126 | IMC 2000 P6 | statement formalized | 78 | Euler-type iteration a_n+1=a_n+1/f(a_n); a_n - F^{-1}(n) -> 0 | Low-Med | Med | MVT on F; control sum of f'/f errors. |
| 127 | IMC 2013 P1 | proof complete | 136 | real symmetric A,B with all eigenvalues > 1, real eigenvalue of AB has \|lambda\| > 1 | Low | Low-Med | Reduce via positive definite diagonalization. |
| 128 | IMC 2003 P5 | statement formalized | 62 | averaging integral iteration f_{n+1}(x) = (1/x) int_0^x f_n | Low | Med | Power-series expansion; explicit limit. |
| 129 | IMC 2018 P1 | proof complete | 98 | sum a_n/c_n and c_n/b_n both convergent iff sum sqrt(a_n/b_n) converges | Low | Med | Cauchy-Schwarz one way; explicit c_n = sqrt(a_n b_n) other. |
| 130 | IMC 2003 P11 | proof complete | 145 | R->R function uniformly bounded by g(x) + g(y); classify g | Low-Med | Med | Inf-over-translate; subadditive decomposition. |
| 131 | IMC 2015 P2 | proof complete | 266 | bit-complement f(k) satisfies sum_{k<=n} f(k) <= n^2/4 | Low-Med | Med | Pair k with 2^m-1-k; compute average. |
| 132 | IMC 2003 P12 | statement formalized | 65 | limit of sum a_k/2^k for a sequence via generating-function ODE | Low-Med | Med | Solve linear ODE on gen fn; evaluate at 1/2. |
| 133 | IMC 2019 P9 | proof complete | 392 | for which n do invertible A,B satisfy AB-BA = B^2 A | Low | Med | Take trace and iterate; restricts to even n. |
| 134 | IMC 2004 P8 | partial | 88 | integral of sqrt(1+f) vs sqrt(1+g) under convex-order hypothesis | Low-Med | Med | Compare convex antiderivatives; integration by parts. |
| 135 | IMC 2008 P4 | partial | 208 | Pareto-dominating set of 3-tuples on simplex, size >= 4 | Med | Med | Extremal argument on monotone families in the simplex. |
| 136 | IMC 2002 P12 | partial | 150 | Lipschitz-gradient convex function squared-gradient bound | Med | Med | Co-coercivity of gradient; standard convex analysis. |
| 137 | IMC 2016 P2 | proof complete | 129 | preferred sequence of matrices with A_i^2 != 0, A_i A_j = 0 has k <= n | Low-Med | Med | Rank and image arguments; linear independence of images. |
| 138 | IMC 2001 P12 | partial | 104 | product f_n(theta) = prod sin(2^k theta) bound | Low-Med | Med-High | Telescoping via duplication identity. |
| 139 | IMC 2007 P5 | statement formalized | 68 | only f = 0 satisfies sum f(k + a_i l) = 0 for given a_i | Med | Med | Fourier/averaging argument on integer translates. |
| 140 | IMC 2000 P8 | proof complete | 190 | continuous nowhere-monotone function with dense local minima | Low | Med | Explicit construction, e.g., perturbed Weierstrass-type. |
| 141 | IMC 2011 P6 | proof complete | 156 | iterated chord-average x_{n+1}=(a_{n+1}+x_n)/(1+a_{n+1}x_n) convergence | Low-Med | Med | tanh substitution linearizes; possible limits in (-1,1). |
| 142 | IMC 2013 P4 | partial | 84 | power-sum inequality (n+1)A^2 B + (n-2)B^2 >= A^4 + (2n-2)AC | Low | Med | SOS / Schur-type inequality with power sums. |
| 143 | IMC 2005 P2 | proof complete | 199 | trinary sequence bijection \|A_{n+1}\| = 3 \|B_n\| | Med | Med | Cyclic shift on Z_3 plus explicit bijection via differences. |
| 144 | IMC 2014 P2 | statement formalized | 59 | triangular-block sequence a_n: find alpha, beta with sum a_k / n^alpha -> beta | Low-Med | Med | Partial-sums asymptotic; alpha=3/2, beta explicit. |
| 145 | IMC 2002 P5 | proof complete | 121 | monotone / C^1 function with every fiber uncountable | Low-Med | Med | Cantor-set-over-Cantor-set construction. |
| 146 | IMC 2011 P8 | proof complete | 269 | triple log product sum ln(1+1/n) ln(1+1/(2n)) ln(1+1/(2n+1)) | Low-Med | Med | Telescoping of ln(1+1/n) over all n; closed-form. |
| 147 | IMC 2008 P5 | statement formalized | 44 | finite group H normal in G with \|Aut H\| > \|Aut G\| | Med | Med | Construction via direct-product / non-characteristic subgroup. |
| 148 | IMC 2006 P7 | statement formalized | 103 | triangulation of n-gon with all odd-degree vertices condition | Med | Med | Parity argument on handshake in triangulation. |
| 149 | IMC 2011 P9 | statement formalized | 51 | integer divided differences on 0..n implies (a-b) divides f(a)-f(b) for all a,b | Low | Med | Newton forward-difference representation; integer coefficients. |
| 150 | IMC 2000 P10 | proof complete | 218 | three-tangency sextic; ratio of two bounded areas | Med | Med | Parametrize sextic curve; compute areas via integration. |
| 151 | IMC 2012 P2 | proof complete | 334 | smallest rank of n x n matrix with zero diagonal and positive off-diagonal entries | Low | Med | Answer is ceil(log_2 n); construction + rank bound. |
| 152 | IMC 2007 P11 | partial | 269 | smallest n with k commuting square-zero matrices and A_1 ... A_k != 0 | Med | Med | Nilpotent structure; Jordan block construction. |
| 153 | IMC 2006 P11 | proof complete | 115 | infinitely many coprime (m, n) with (x+m)^3 = nx having three integer roots | Med | Med | Parametrized family via cubic Vieta. |
| 154 | IMC 2008 P8 | proof complete | 477 | two distinct ellipses with common focus meet in at most 2 points | Med | Med | Polar-form equations; algebra of conic intersection. |
| 155 | IMC 2006 P3 | partial | 96 | integer-matrix Smith-type factorization given determinant factorization | Med | Med-High | Smith normal form over Z; lift factorization. |
| 156 | IMC 2008 P12 | statement formalized | 113 | equidistant set in infinite Hilbert space is orthonormal translate | Med | Med-High | Inner-product Gram-matrix analysis; separable Hilbert space. |
| 157 | IMC 2009 P9 | partial | 322 | permutation group over F_p generated by two specific polynomials | Med | Med-High | Finite permutation group classification; degree analysis. |
| 158 | IMC 2005 P12 | proof complete | 512 | (p + q sqrt 7) Pell-style fixed point of SL_2(Z) Mobius | Med | Med-High | Pell equation + SL_2(Z) orbit analysis. |
| 159 | IMC 2008 P6 | proof complete | 351 | permutation displacement D(sigma) distribution parity for large d | Med | Med-High | Generating-function parity count; asymptotic. |
| 160 | IMC 2001 P4 | statement formalized | 74 | polynomial with coeffs in {-1,0,1}, divisibility forces q-th roots as roots | Med | Med-High | Cyclotomic divisor analysis; sparse coefficient bound. |
| 161 | IMC 2009 P3 | statement formalized | 59 | friendship graph with sum a_i^2 = n^2 - n has girth 5 | Med | Med-High | Eigenvalue/counting argument; Friendship-theorem style. |
| 162 | IMC 2025 P3 | proof complete | 557 | rank-1 ±1 symmetric matrices commuting probability | Med | Med | Bijection to Bool × (Fin (n-1) → Bool); inner-product parity. |
| 163 | IMC 2025 P8 | proof complete | 260 | A = A^R (90-degree rotation) => Re(λ)=0 or Im(λ)=0 | Med | Med | Complex inner product; algebraic eigenvalue manipulation. |
| 164 | IMC 2025 P1 | proof complete | 454 | odd-degree polynomials with tangent-sum property | Low-Med | Med | IVT for odd-degree real polys; filter limits at ±∞. |
| 165 | IMC 2003 P6 | statement formalized | 57 | log-concavity of coefficients for stable (all real-root) polynomials | Low | Med-High | Newton's inequalities on elementary symmetric polys. |
| 166 | IMC 2016 P7 | proof complete | 189 | min integral over continuous f with f(x)+f(y) >= \|x-y\| | Low | Med | Equality-case analysis; 1/4 achieved by f(x)=\|x-1/2\|/2. |
| 167 | IMC 2014 P3 | statement formalized | 45 | positive a_i: every signed polynomial sum_k ±a_k x^k has n distinct real roots | Low-Med | Med | Explicit widely-spaced positive sequence; IVT over sign changes. |
| 168 | IMC 2018 P6 | proof complete | 152 | min n for k nonzero vectors in R^n with v_i perp v_j when \|i-j\|>1 | Low-Med | Med | Answer: n = ceil(k/2); existence + dim bound via pairs. |
| 169 | IMC 2014 P7 | proof complete | 221 | sum_{i<j} a_{ii} a_{jj} >= sum_{i<j} lambda_i lambda_j for symmetric A | Low | Med | Majorization/Schur; equality iff diagonal. |
| 170 | IMC 2001 P10 | statement formalized | 144 | principal-minor determinant vanishing implies nilpotent permutable | Med | Med | Characteristic polynomial roots; rank structure. |
| 171 | IMC 2005 P11 | partial | 110 | 1-Lipschitz gradient disc max attained at unique point for r <= 1/2 | Med | High | Contraction on disc; delicate uniqueness argument. |
| 172 | IMC 2024 P3 | proof complete | 203 | {0,1}-matrix with A^2 = all-ones matrix iff n square | Med | Med | Row sums argument; cyclic block construction. |
| 173 | IMC 2023 P6 | proof complete | 129 | invariance via log-determinant, reachability | Med | Med | Invariant (det of log-matrix); simple once discovered. |
| 174 | IMC 2022 P6 | proof complete | 154 | permutation with prescribed sum mod p | Low | Med | Explicit construction x_i ≡ i^{-1} mod p. |
| 175 | IMC 2013 P7 | proof complete | 235 | sum_{k=0}^{pq-1} (-1)^{floor(k/p)+floor(k/q)} = 0 or 1 by parity of pq | Low-Med | Med | CRT enumeration; case on parity of pq. |
| 176 | IMC 2003 P9 | proof complete | 181 | closed A in R^n; set of points with unique nearest point in A is dense | Med | Med | Baire category; a.e. differentiability of distance fn. |
| 177 | IMC 2013 P9 | statement formalized | 50 | infinite subset of positive integers with pairwise sums square-free | Low | Med | Explicit construction avoiding squarefull primes; diagonal argument. |
| 178 | IMC 2012 P9 | partial | 78 | find real a with exists x_i satisfying x_i(1-x_{i+1})=a cyclic | Low | Med | Case analysis on sign and fixed-point analysis. |
| 179 | IMC 2012 P8 | proof complete | 221 | is {n: n!+1 divides (2012n)!} finite or infinite | Low | Med | Density/residue argument using Wilson's-type lemma. |
| 180 | IMC 2015 P8 | statement formalized | 50 | sum of weighted 26-letter words of length 26 equals 3^75 | Low-Med | Med | Binomial inversion and switching order of summation. |
| 181 | IMC 2025 P7 | proof complete | 620 | subsets closed under x->2x and (x+y)/2 | Low | Med | Elementary number theory; arithmetic progressions. |
| 182 | IMC 2020 P6 | proof complete | 173 | primes with unique root of x^3-3x+1 mod p | Low | Med | Elementary finite-field + root permutation via x^2-2. |
| 183 | IMC 2019 P2 | proof complete | 386 | find years YEAR with certain 4x4 rotation-matrix system having many solutions | Low-Med | Med | Circulant system; rank condition relates to digit sum. |
| 184 | IMC 2024 P6 | proof complete | 157 | every f:Q->Z has a,b,c with f(b) dominating | Low | Med | Pigeonhole on finite subintervals; countable argument. |
| 185 | IMC 2013 P8 | partial | 80 | d unit vectors in R^d, exists unit u with \|u.v_i\| <= 1/sqrt d | Med | Med | Averaging / pigeonhole on sphere; covering argument. |
| 186 | IMC 2006 P12 | statement formalized | 80 | GL_2(R) simultaneous conjugation of triples of matrices | Med | High | Representation-theoretic conjugacy invariants. |
| 187 | IMC 2015 P3 | proof complete | 158 | is sum 1/F(2^n) rational for F(n)=5/2 F(n-1)-F(n-2) | Low-Med | Med | Solve recurrence; telescoping-of-geometric-ratio identity. |
| 188 | IMC 2009 P4 | statement formalized | 67 | polynomial convolution with convex-coefficient kernel preserves sup norm | Med | High | Bernstein-type inequality; convex coefficient analysis. |
| 189 | IMC 2007 P12 | statement formalized | 40 | iterated f_n = f_{n-1} + f_{n-1}' eventually has all real roots | Med | High | Root interlacing via derivative; Rolle plus asymptotic count. |
| 190 | IMC 2004 P12 | statement formalized | 126 | row sum of A_n^{k-1} equals row sum of A_k^{n-1} for recursive block | Med | Med-High | Induction on block structure; Kronecker-product identity. |
| 191 | IMC 2018 P3 | proof complete | 201 | find rational a for which 4x4 block matrix is a rational square | Med | Med | Block decomposition over Q(i); rational Pell-like condition. |
| 192 | IMC 2018 P9 | partial: backward direction proved; forward (Vieta-jumping descent) sorry'd | 96 | classify monic complex P,Q with P \| Q^2+1 and Q \| P^2+1 | Low | Med-High | Degree comparison; classify via iteration identity. |
| 193 | IMC 2010 P4 | partial | 89 | Z \ {a x^n + b y^n} finite implies n = 1 | Low | Med | Density of n-th-power sums in Z; n>=2 leaves holes. |
| 194 | IMC 2016 P6 | proof complete | 156 | double sum bound given harmonic-weighted condition on x_n | Low-Med | Med | Abel summation; rearrange double sum. |
| 195 | IMC 2003 P10 | statement formalized | 67 | Steiner triple with closure rule iff n = 2^m - 1 | Med | Med-High | Identify with F_2^m minus zero; affine geometry. |
| 196 | IMC 2010 P9 | proof complete | 187 | F_2 symmetric zero-diagonal A, every column of A^n has a zero | Med | Med | Parity/handshake in F_2; A^n diagonal zero via trace argument. |
| 197 | IMC 2016 P9 | statement formalized | 40 | log-concavity of lattice-ball counting function f(n-1)f(n+1) <= f(n)^2 | Low-Med | Med | Combinatorial identity on layer differences. |
| 198 | IMC 2023 P3 | partial: easy + many multiplicative intermediates done; classification via C[x,y] factorization TODO | 166 | P(x,y)P(z,t) = P(xz-yt, xt+yz) classify polynomials | Low | Med | Complex factorization (x+iy)^n(x-iy)^m; real-coef constraint. |
| 199 | IMC 2025 P4 | partial: reverse fully proved; forward mostly proved except x ≥ -1 case | 605 | floor identity for b^{a-1} (b^a+x)^{1/a} | Low-Med | Med | Bernoulli inequality + case analysis. Real.rpow of negative base issue on a=2 noted. |
| 200 | IMC 2019 P7 | proof complete | 198 | convergence of sum (a_n/n)^n over composite n with n \| a_n! smallest | Low-Med | Med | Estimate a_n by largest prime factor; bound by tail of geometric. |
| 201 | IMC 2010 P8 | partial: statement + sum_x \|stab G x\| = (\|G\|-1)+n proven; orbit-counting deduction sorry'd | 186 | subgroup G <= S_n with each nontrivial pi having unique fixed point forces same fixed k | Med | Med | Frobenius-group structure; orbit counting. |
| 202 | IMC 2009 P5 | statement formalized | 100 | weighted circumcenter identity for simplex split at interior point | Med-High | High | Barycentric circumcenter formula; multi-dimensional geometry. |
| 203 | IMC 2009 P10 | statement formalized | 148 | minimal covering subspace T of matrices with dim bound delta(T) <= C(n,2) | Med-High | High | Linear-algebra extremal; delicate dimension counting. |
| 204 | IMC 2012 P5 | statement formalized | 39 | X^{2^n}(X+a)^{2^n} + 1 irreducible in Q[X] for rational a | Low-Med | Med-High | Eisenstein-like analysis after substitution; degree/root argument. |
| 205 | IMC 2004 P5 | proof complete | 493 | monotone doubling subsequence from C(k-2, 2k-4)+1 reals | Med | Med-High | Erdos-Szekeres-style Ramsey bound; extremal. |
| 206 | IMC 2018 P2 | proof complete | 111 | no field has multiplicative group isomorphic to additive group | Low | Med-High | Case analysis char 2 vs odd; finite fields plus infinite case. |
| 207 | IMC 2021 P8 | proof complete | 586 | unit vectors with 3-at-a-time orthogonality condition | Low-Med | Med | Projector trace identities; algebraic inequalities. |
| 208 | IMC 2025 P9 | proof complete | 53 | expected max of a prob 2^{-i} random process | Med | Med | Induction + geometric sum; countable probability space. |
| 209 | IMC 2021 P6 | proof complete | 282 | no injection GL_2(F_p) -> S_p | Med | Med | Element-of-order-2p + structure of S_p. |
| 210 | IMC 2017 P9 | not started | - | ODE-defined sequence f_n'=f_{n-1}f_n, find limit function | Low-Med | Med-High | Compare with 1/(1-x); explicit rational limit. |
| 211 | IMC 2010 P10 | not started | - | f zero on (a,b) and sum_{k<p} f(y+k/p)=0 for all primes p, y => f=0 | Med | Med-High | Rational-shift density; Moebius-type cancellation across primes. |
| 212 | IMC 2014 P10 | not started | - | Delta(n,k) derangement recursion via binomial-D_j sum | Med | Med-High | Combinatorial bijection on fixed-prefix derangements. |
| 213 | IMC 2014 P8 | not started | - | \|(sin x / x)^{(n)}\| < 1/(n+1) for x > 0 | Low | Med-High | Integral representation sin x/x = integral cos(xt) dt; dominated-conv bound. |
| 214 | IMC 2011 P4 | not started | - | inclusion-exclusion polynomial f(t) = sum ±t^{\|union\|} nondecreasing on [0,1] | Med | Med-High | Express derivative as a positive combination via Mobius-style coefficients. |
| 215 | IMC 2016 P8 | not started | - | Z_n function with three fixed-point-free involutions forces n ≡ 2 mod 4 | Med | Med-High | Count fixed-point-free involutions; parity constraint. |
| 216 | IMC 2024 P8 | partial: positivity + lower-bound monotonicity proved; statement indexing fixed; upper bound + telescoping series remain | 79 | recursive sequence x_n/2^n limit bounds | Low | Med-High | Induction + telescoping sums; manage auxiliary sequence. |
| 217 | IMC 2017 P3 | not started | - | divisor-product iterate a_{k+1}=P(a_k); indicator-square condition on S | Med | Med-High | Multiplicative structure and prime-power choices. |
| 218 | IMC 2023 P4 | partial: p=2 vacuous, p=3 done; p>3 structural reduction done; `key_product_lemma` remains | 246 | a_i = i^k + i complete residue system mod p | Low-Med | Med-High | Product-of-cyclotomic-lemma; finite-field machinery. |
| 219 | IMC 2013 P3 | not started | - | 2n students, weekly trip of n, minimum trips covering all pairs | Low-Med | Med | Combinatorial design; block-design lower bound. |
| 220 | IMC 2002 P10 | not started | - | tetrahedron dihedral angle inequality via spherical areas | Med-High | High | Spherical polygon area bound; Gauss-Bonnet flavor. |
| 221 | IMC 2014 P4 | not started | - | perfect n > 6 with factorization p_1^{e_1}..p_k^{e_k} has e_1 even | Low | Med-High | sigma = 2n analysis; parity of e_1 from mod-p counting. |
| 222 | IMC 2020 P4 | partial: boundary-value helpers proved; main inequality (max principle on rectangle) remains | 63 | p(x+1)-p(x)=x^{100} => p(1-t) >= p(t) | Low | High | Complex analysis / max principle on rectangle. |
| 223 | IMC 2017 P8 | not started | - | recursive block matrix A_n with n+1 integer eigenvalues with binomial multiplicities | Med | Med-High | Kronecker-product eigenvalue induction. |
| 224 | IMC 2002 P6 | not started | - | power-bounded matrices via norm-difference decay | Med | High | Summable norm differences implies power boundedness; Jordan. |
| 225 | IMC 2018 P8 | not started | - | frog paths count in Omega subset Z^3 from (0,0,0) to (n,n,n) | Med | Med-High | Lattice path counting; Lindstrom-Gessel-Viennot flavor. |
| 226 | IMC 2014 P6 | not started | - | finitely many zeros in (d_n(a_n)) implies infinitely many missing positive integers | Med | Med | Density/counting argument on digit pattern constraints. |
| 227 | IMC 2011 P5 | not started | - | 4n-1 vectors in (2n-1)-dim F_2 space contain 2n with zero sum | Med | Med | Erdos-Ginzburg-Ziv style over F_2; pigeonhole on subset sums. |
| 228 | IMC 2022 P3 | proof complete | 291 | flea on Z, strategies mod p | Low-Med | Med-High | Generating functions mod p; binomial identities. |
| 229 | IMC 2004 P4 | not started | - | 2-coloring condition on sphere intersections forces cosphericity | Med | High | Topological/convexity argument; separating sphere analysis. |
| 230 | IMC 2023 P1 | proof complete | 271 | f(7x+1)=49f(x) with C^2 => f(x)=c(6x+1)^2 | Low | Med | Fixed-point contraction argument. |
| 231 | IMC 2019 P8 | not started | - | subset sums with 1.8^n distinct values, <= 1.7^n equal to any fixed target | Med | Med-High | Entropy / additive combinatorics counting. |
| 232 | IMC 2015 P5 | not started | - | n+1 points + interior point: >= n pairs with angle A_i B A_j > 90 | Med | Med-High | Convex hull / gradient argument; pigeonhole on directions. |
| 233 | IMC 2020 P7 | proof complete | 136 | subgroups with index conditions are conjugate | Med | Med-High | Coset counting; finite group argument. |
| 234 | IMC 2016 P4 | not started | - | union-closed family with C(n,k)+1 k-sets has >= 3 sets of size n+ | Med | Med-High | Iterated unions; extremal set-family argument. |
| 235 | IMC 2021 P3 | partial: crude d ≤ 2 bound via n=1; definition of `Good` in file differs from original, main sSup = log 2 remains | 94 | good d: sup=ln 2 with sequence partition | Med | High | Partial fraction/log identities; sequence construction. |
| 236 | IMC 2017 P5 | not started | - | f and z^n-1 share at most n-k common roots under c_i c_{n-2-i}=0 | Med | Med-High | Sparse-polynomial structure; counting argument. |
| 237 | IMC 2013 P10 | not started | - | 2013-bead necklace, count good paintings with every 21 successive having a green is odd | Med | Med-High | Transfer-matrix determinant over F_2; trace parity. |
| 238 | IMC 2023 P8 | proof complete | 238 | tree Wiener index times harmonic index bound | Med | Med | Cauchy-Schwarz; needs graph theory library (tree, distance). |
| 239 | IMC 2022 P5 | proof complete | 794 | count monochromatic triangles on K_{43} | Med | Med-High | Double counting 'cherries'; specific 43-vertex problem. |
| 240 | IMC 2015 P9 | not started | - | max dimension of t-normal subspace of complex n x n matrices | Med | High | Linear-algebra structure; symmetric + antisymmetric parts. |
| 241 | IMC 2018 P5 | not started | - | equiangular pq-gon with distinct integer side lengths satisfies partial-sum bound | Med | High | Structure of equiangular polygons plus counting. |
| 242 | IMC 2016 P5 | not started | - | permutation inv(pi) divisible by n+1: infinitely many primes with f(p-1) above/below (p-1)!/p | Med | High | Generating function and roots of unity filter; character sums. |
| 243 | IMC 2012 P3 | not started | - | two players pick S_n elements, generating ends game; last mover loses | Med | Med-High | Game-theory analysis on subgroup-lattice parity of S_n. |
| 244 | IMC 2011 P3 | not started | - | p^p-1 is interesting for x^n-1 = (x^p-x+1)f + p g; minimal interesting n | Med | High | Order of x mod (x^p-x+1, p); cyclotomic-type argument. |
| 245 | IMC 2017 P4 | not started | - | friendship graph degree 1000, find subgroup S with >= n/2017 having 2 friends in S | Med | High | Probabilistic method; randomized subset selection. |
| 246 | IMC 2017 P7 | not started | - | (x+1)^n p(x) + x^n p(x+1) has all real roots only finitely often | Med | High | Root-location asymptotics; Descartes-type sign analysis. |
| 247 | IMC 2018 P10 | not started | - | lattice sum (-1)^{a+b}/(a^2+b^2) over disc, limit as R -> infinity | Med | High | Jacobi theta / L-function evaluation; Dirichlet series. |
| 248 | IMC 2012 P6 | not started | - | coefficient-assignment game with m(x)=x-2012 or m(x)=x^2+1 | Med | High | Game analysis: Homer/Einstein strategies per monic divisor. |
| 249 | IMC 2011 P7 | not started | - | three-gender matching: k >= 3n/4 guarantees n married triples | Med | High | Hall-type theorem for 3-uniform hypergraphs; tight bound. |
| 250 | IMC 2019 P10 | not started | - | 2019 uniform points in disc: triangle vs quadrilateral hull probability | Med | High | Integral geometry; Sylvester-type computation. |
| 251 | IMC 2025 P5 | statement formalized | 56 | g(n) < f(n) + n^{0.501} (sym grp max order) | Med | High | Requires weak PNT bound on prime sum; Landau's function. |
| 252 | IMC 2025 P10 | statement formalized | 51 | count pairs with (a^2+a)(b^2+b) square | Med | High | Pell equation analysis; analytic number theory estimates. |
| 253 | IMC 2012 P10 | not started | - | abelian group: \|A+A\| <= c\|A\| implies \|kA\| <= c^k \|A\| | Med | High | Plünnecke-Ruzsa inequality; additive combinatorics. |
| 254 | IMC 2024 P4 | statement formalized | 60 | subgroup gen. by n-grams independent of sequence | Med-High | High | Pigeonhole + non-periodicity + induction on group. |
| 255 | IMC 2020 P8 | statement formalized | 46 | lim (1/log log n) sum (-1)^k C(n,k) log k = 1 | Med-High | High | Frullani integral; asymptotic analysis with uniform bounds. |
| 256 | IMC 2013 P5 | not started | - | complex sequence with sum a_n^p convergent iff p is not prime | Med-High | Very High | Delicate construction; sieve over prime exponents. |
| 257 | IMC 2016 P10 | not started | - | spectral bound \|A^n\| <= (n/ln 2) \|A\|^{n-1} for unit-spectrum A | Med-High | High | Operator-norm analysis; Jordan form bound. |
| 258 | IMC 2021 P4 | statement formalized | 41 | baire class 1 via oscillation hypothesis | High | High | G_delta characterization; Lebesgue's theorem on Baire class 1. |
| 259 | IMC 2023 P5 | statement formalized | 48 | preferred permutations >= k! | Med-High | High | Combinatorial argument with ordering + counting. |
| 260 | IMC 2017 P10 | not started | - | homothetic negative-ratio triangle packing: perimeter blowup as area approaches K | Med-High | Very High | Delicate packing / isoperimetric geometry. |
| 261 | IMC 2004 P6 | not started | - | sum of log^{-4} over branches equals explicit rational function | High | High | Complex analysis; residue / partial-fraction evaluation. |
| 262 | IMC 2024 P5 | statement formalized | 58 | f(p)>=f(q) for convex hull coverage in ball | Med-High | Very High | Needs convex-geometry chi-function decomposition; measure theory. |
| 263 | IMC 2011 P10 | not started | - | perpendicular-bisector reflection operator composed on polygon returns to F after n iterations | Med-High | Very High | Intricate invariance across polygon iteration; discrete-geometric periodicity. |
| 264 | IMC 2022 P4 | statement formalized | 56 | chromatic number of triple-graph, log log n bounds | Med-High | Very High | Heavy graph coloring framework; iterated chromatic number. |
| 265 | IMC 2014 P5 | not started | - | 3n-segment closed broken line, 60-deg angles CCW; self-intersections <= 3n^2/2 - 2n + 1 | Med-High | Very High | Geometric combinatorics on equilateral-direction polygons. |
| 266 | IMC 2014 P9 | not started | - | k-generic minimal subset size d(k,n) | Med-High | High | Hyperplane k-almost-containment; extremal combinatorial geometry. |
| 267 | IMC 2023 P9 | statement formalized | 59 | sup V of two disjoint-projection convex sets in cube | High | Very High | Convex geometry, symmetry argument, integration. |
| 268 | IMC 2022 P8 | statement formalized | 64 | expected vertices of intersection of two convex hulls | High | Very High | Integral geometry with 2 point clouds on circle. |
| 269 | IMC 2020 P3 | statement formalized | 60 | polytope eps-approximation with C(d)eps^{1-d} vertices | High | Very High | Convex body volume estimates; polytope approximation theorem. |
| 270 | IMC 2023 P10 | statement formalized | 47 | g(n) > n^{0.999n} for factorial-LCD denominator | High | Very High | Deep p-adic valuation + 'special primes' machinery. |
| 271 | IMC 2024 P9 | statement formalized | 63 | number of nice matrices is even | High | Very High | Young-tableau friendship graph handshake; bespoke combinatorics. |
| 272 | IMC 2024 P10 | statement formalized | 53 | Fermat-prime divisibility condition on almost primes | Very High | Very High | Multi-lemma cyclotomic/order argument in F_q. |

## Aggregate summary

- **Total problems in main table**: 272 (54 from 2020-2025, 100 from 2010-2019, 58 from 2005-2009, 60 from 2000-2004).
- **Proof complete**: 30 problems (no remaining `sorry`).
- **Partial** (non-trivial proof progress, narrowed sorry): 8 problems.
- **Statement formalized only**: 16 problems.
- **Not started** (including the 100 2010-2019, 58 2005-2009, and 60 2000-2004 problems): 218 problems.
- Mean LoC of proof-complete files: ~240. Range: 53 (IMC 2025 P9) to 741 (IMC 2024 P2).
- Mean LoC of files still at statement-only: ~54. Most are small scaffolds (40–80 LoC) that would expand significantly when a real proof is attempted.

## How accurate was the ranking?

The ranking was generated before the work began. Comparing against post-hoc LoC and ease of actually discharging proofs, the verdict: **ordering within tiers is approximately right; cross-tier calibration was systematically too optimistic; a few outliers were badly misranked.**

### Hits
- The top ~25 existing-rank positions are all closed as proofs (though several needed 200–500 LoC rather than the implied "one-day" effort).
- The bottom eight "Tier 4" statement-only entries remain statement-only, matching the "research-level" labels.
- IMC 2020 P7 (subgroup conjugacy) labelled Tier 3 but closed in 136 LoC — coset-counting turned out cleaner than expected.
- IMC 2022 P3 Tier 3 closed cleanly once the generating-function + Frobenius trick was spotted.

### Underestimated difficulty
- **IMC 2024 P2**: "Low/Low", needed **741 LoC** with an explicit ε-N Riemann-sum argument. Mathlib lacked a direct Riemann-sum → integral convergence lemma.
- **IMC 2024 P7**: "Low/Low", took 386 LoC for eigenvalue/spectrum machinery in ℂ.
- **IMC 2021 P2**: "Low proof", took 487 LoC setting up the rank/splitting bijection with Finset.
- **IMC 2025 P3**: 557 LoC for "Med/Med" — parity-of-inner-product counting needed heavy Finset wrangling.
- **IMC 2025 P1**: 454 LoC; filter-limit reasoning on odd-degree polynomial ends was finickier than "Low-Med".
- **IMC 2025 P4**: 605 LoC and still partial — Bernoulli for real exponents + floor arithmetic was heavier than "Med".

### Overestimated difficulty
- **IMC 2025 P9**: just 53 LoC to a full proof — self-contained inductive probability statement. Arguably belongs in the low teens.
- **IMC 2023 P8**: labeled Tier 3, closed cleanly in 238 LoC once Mathlib's tree/distance lemmas lined up.
- **IMC 2024 P3**: closed in 203 LoC; the cyclic-block construction was more mechanical than Tier 2 implied.

### Cases where the stated Lean theorem differs from the original problem
- IMC 2025 P4: `Real.rpow` conventions on negative bases make the "iff" subtly false for certain x when a=2.
- IMC 2024 P8: original statement had off-by-one indexing (2^n vs 2^(n+1)); the formalizing agent corrected it.
- IMC 2021 P3: the `Good` predicate in the file is a simplified covering condition not matching the original sorted-partition condition; the stated sSup = log 2 may not even hold as written.

### Lessons
- LoC is dominated by **Mathlib plumbing**, not the underlying mathematical depth. "Elementary" problems with lots of index juggling blow up as much as genuinely analytic ones.
- Problems where Mathlib's API is thin (Riemann sums, complex max principle, Baire class 1, simultaneous diagonalization) punch well above their competition-difficulty.
- Ordering within tiers 1–2 is more accurate than cross-tier calibration.

## Appendix: IMC 1994-1999 (not yet ranked in main table)

The following problems have PDFs and pdftotext-derived `.tex` in the `imc/` directory but no Lean formalization yet and have not been placed into the main ranking table. All statuses are `not started`. Ordering is chronological (oldest first), by year then by problem number. Difficulty estimates are calibrated against the main table. Topics are 5-15 word summaries.

Problem counts per year: 1994-1999 had 6 problems/day × 2 days = 12 per year. Total: 72 problems (6 × 12). (IMC 2000-2025 have been integrated into the main ranking table above.)

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
