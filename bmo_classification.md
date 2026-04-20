# BMO Formalization-Difficulty Classification

Tiers: T1 (easiest) · T2 (moderate) · T3 (hard-tractable) · T4 (skip/very hard)

## Summary counts
- T1: 33 problems
- T2: 62 problems
- T3: 48 problems
- T4: 67 problems

## T1 — Easiest (recommended to start here)
| Year | Round | # | Topic | Lean filename | One-line statement gist | Rationale |
| ---- | ----- | - | ----- | ------------- | ----------------------- | --------- |
| 2005 | 1 | 1 | Algebra | UK2005R1P1.lean | Paul/Jenny pounds, find positive integer n | Small linear Diophantine, omega/decide |
| 2005 | 1 | 4 | NumberTheory | UK2005R1P4.lean | AP of 7 distinct primes, minimise max term | Concrete integer answer, decidable search |
| 2005 | 2 | 3 | Inequality | UK2005R2P3.lean | (a/b+b/c+c/a)² ≥ (a+b+c)(1/a+1/b+1/c) | Symmetric inequality, nlinarith/polyrith |
| 2007 | 1 | 1 | NumberTheory | UK2007R1P1.lean | Four primes <100 dividing 3^32−2^32 | Concrete factoring, norm_num |
| 2007 | 1 | 5 | Inequality | UK2007R1P5.lean | (a²+b²)² ≥ (a+b+c)(a+b−c)(b+c−a)(c+a−b) | Polynomial inequality, nlinarith |
| 2008 | 1 | 1 | Algebra | UK2008R1P1.lean | Compute (1⁴+2007⁴+2008⁴)/(1²+2007²+2008²) | Pure arithmetic, norm_num |
| 2008 | 1 | 2 | NumberTheory | UK2008R1P2.lean | Positive int solutions to x+y−z=12, x²+y²−z²=12 | Small Diophantine, decide |
| 2008 | 2 | 1 | Algebra | UK2008R2P1.lean | Min x²+y²+z² given x³+y³+z³−3xyz=1 | Polynomial min, polyrith |
| 2009 | 1 | 2 | Algebra | UK2009R1P2.lean | Real (x,y,z) with (x+1)yz=12, etc. | Polynomial system, polyrith |
| 2009 | 1 | 4 | NumberTheory | UK2009R1P4.lean | n with n+2008\|n²+2008 and n+2009\|n²+2009 | Divisibility, bounded search |
| 2009 | 2 | 1 | NumberTheory | UK2009R2P1.lean | √a+√b=√2009 in nonneg integers | Small Diophantine |
| 2010 | 1 | 1 | NumberTheory | UK2010R1P1.lean | x²+y²+z²=2(yz+1), x+y+z=4018 | Diophantine reduction |
| 2010 | 2 | 4 | Inequality | UK2010R2P4.lean | 4(x+y+z)³ > 27(x²y+y²z+z²x) | Classic polynomial inequality, nlinarith |
| 2011 | 1 | 1 | Algebra | UK2011R1P1.lean | Removed number from {1..n}, avg 40¾ | Arithmetic, omega |
| 2011 | 1 | 6 | Inequality | UK2011R1P6.lean | ab+bc+ca=1 implies (a+1)(b+1)(c+1)<4 | Polynomial inequality, nlinarith |
| 2012 | 1 | 1 | NumberTheory | UK2012R1P1.lean | n²+20n+11 a perfect square | Completing-square, small Diophantine |
| 2013 | 1 | 3 | Algebra | UK2013R1P3.lean | Real solutions to three quadratic identities | SOS reduction, polyrith |
| 2013 | 1 | 4 | NumberTheory | UK2013R1P4.lean | 12n−119 and 75n−539 both squares | Small Diophantine |
| 2013 | 2 | 1 | NumberTheory | UK2013R2P1.lean | ∃ infinitely many (m,n) with m\|n²+1 and n\|m²+1 | Fibonacci-like construction |
| 2014 | 1 | 1 | Algebra | UK2014R1P1.lean | Compute specific algebraic expression | Pure arithmetic, norm_num |
| 2014 | 1 | 3 | NumberTheory | UK2014R1P3.lean | Power of 3 dividing a repunit of 3s | Lifting-the-exponent, direct |
| 2017 | 1 | 3 | NumberTheory | UK2017R1P3.lean | n²−6n=m²+m−10 in positive integers | Small Diophantine |
| 2018 | 1 | 1 | NumberTheory | UK2018R1P1.lean | Sum of remainders 365/k vs 366/k | Direct computation |
| 2019 | 1 | 3 | NumberTheory | UK2019R1P3.lean | x(x+9)=y(y+6) same product T | Small Diophantine |
| 2020 | 1 | 1 | NumberTheory | UK2020R1P1.lean | Prime quadruples/quintuples with given gaps | Finite search, decide |
| 2020 | 1 | 2 | Algebra | UK2020R1P2.lean | 4a_{n+1}²−4aₙa_{n+1}+aₙ²−1=0 values of a₁ | Quadratic recurrence, direct |
| 2020 | 2 | 1 | Algebra | UK2020R2P1.lean | a_{n+1}=aₙ(aₙ−1)/2, all terms odd iff a₁=… | Parity analysis |
| 2021 | 1 | 1 | Algebra | UK2021R1P1.lean | Alice/Bob ±, 2x,x−45 recurrence, repeat of a | Linear recurrence |
| 2022 | 1 | 1 | NumberTheory | UK2022R1P1.lean | Three even <400, ≥6 ways sum of consec odds | Bounded search, decide |
| 2023 | 1 | 1 | NumberTheory | UK2023R1P1.lean | 3-digit n, exactly 1/k start with 2 | Finite search |
| 2024 | 1 | 4 | NumberTheory | UK2024R1P4.lean | n·2ⁿ+1 a square | Small Diophantine |
| 2025 | 2 | 1 | NumberTheory | UK2025R2P1.lean | 1/n as sum of reciprocals of triangular numbers | Constructive greedy, inductive |
| 2005 | 2 | 1 | NumberTheory | UK2005R2P1.lean | Exactly 2005 pairs with 1/x+1/y=1/N ⇒ N is square | Divisor count, arithmetic |

## T2 — Moderate
| Year | Round | # | Topic | Lean filename | One-line statement gist | Rationale |
| ---- | ----- | - | ----- | ------------- | ----------------------- | --------- |
| 2005 | 1 | 5 | Algebra | UK2005R1P5.lean | Set S of rationals closed under 1/(x+1), x/(x+1) | Stern–Brocot induction |
| 2006 | 1 | 1 | NumberTheory | UK2006R1P1.lean | n−1,n+1 prime ⇒ 720\|n²(n²+16); converse? | Modular case analysis |
| 2006 | 2 | 1 | Algebra | UK2006R2P1.lean | Min x²+y² given xy(x²−y²)=x²+y² | Polynomial optimisation |
| 2006 | 2 | 2 | NumberTheory | UK2006R2P2.lean | x,y only 2,3,5 factors, x²−y²=2ᵏ | Bounded factor cases |
| 2007 | 1 | 6 | NumberTheory | UK2007R1P6.lean | 2+2√(1+12n²) integer ⇒ square | Pell-style argument |
| 2007 | 2 | 1 | NumberTheory | UK2007R2P1.lean | Triangle integer sides, AC=2007, bisector DB=AB | Specific integer triangle |
| 2007 | 2 | 2 | NumberTheory | UK2007R2P2.lean | ∞ many (m,n) with (m+1)/n+(n+1)/m integer | Explicit Fibonacci/Vieta construction |
| 2008 | 1 | 6 | NumberTheory | UK2008R1P6.lean | Recursive f on positives, count f(n)=2n | Recurrence analysis |
| 2008 | 2 | 4 | NumberTheory | UK2008R2P4.lean | ∞ pairs x,y with x³+y²\|x²+y³ | Explicit family |
| 2009 | 1 | 5 | Algebra | UK2009R1P5.lean | a_{n+1}=2aₙ²−1, periodic with rational start | Chebyshev/cos substitution |
| 2009 | 1 | 6 | Inequality | UK2009R1P6.lean | a³cosA+b³cosB+c³cosC<abc for obtuse | Trig inequality |
| 2009 | 2 | 3 | FunctionalEquation | UK2009R2P3.lean | f(x³)+f(y³)=(x+y)(f(x²)+f(y²)−f(xy)) | Linear FE, f(x)=kx |
| 2010 | 1 | 5 | FunctionalEquation | UK2010R1P5.lean | f(x)f(y)=f(x+y)+xy | Exponential/linear FE |
| 2010 | 1 | 6 | NumberTheory | UK2010R1P6.lean | Unique (x,y) from x²+y and x+y² | Injectivity argument |
| 2010 | 2 | 3 | NumberTheory | UK2010R2P3.lean | p^k \| x⁶−1 ⇒ p^{3k}<8n | Factoring x⁶−1 |
| 2011 | 1 | 2 | Algebra | UK2011R1P2.lean | Cube with hole, volume = surface area | Small integer search |
| 2011 | 1 | 4 | Combinatorics | UK2011R1P4.lean | 8×8 3-colour counters parity of red | Parity/generating function |
| 2011 | 2 | 2 | NumberTheory | UK2011R2P2.lean | x+y+1\|2xy, x+y−1\|x²+y²−1 | Divisibility manipulation |
| 2011 | 2 | 3 | NumberTheory | UK2011R2P3.lean | Recursive f, count n<2011 with f(n)=f(2011) | Binary encoding |
| 2012 | 1 | 2 | Combinatorics | UK2012R1P2.lean | Max t in arrangement of 1..n with consec diff ≥t | Closed form ⌊n/2⌋ |
| 2012 | 1 | 5 | NumberTheory | UK2012R1P5.lean | 4 consec ints ≠ product of 2 consec ints | Bounding argument |
| 2012 | 2 | 2 | NumberTheory | UK2012R2P2.lean | f(n)=f(⌊(2n−1)/3⌋)+f(⌊2n/3⌋), is f(n)−f(n−1)≤n | Induction on recurrence |
| 2012 | 2 | 4 | NumberTheory | UK2012R2P4.lean | Existence of k s.t. divisibility finite check | Newton's identities |
| 2013 | 2 | 3 | Combinatorics | UK2013R2P3.lean | 2013-bit ints with more 0s than 1s, sum parity | Counting argument |
| 2014 | 1 | 4 | Combinatorics | UK2014R1P4.lean | 9-day holiday, no consec different watersports | Linear recurrence |
| 2014 | 2 | 2 | Algebra | UK2014R2P2.lean | No cuboid with vol=SA=perim | Finite AM-GM style |
| 2014 | 2 | 3 | NumberTheory | UK2014R2P3.lean | aₙ=a_{n−1}²−a_{n−1}, ∞ primes dividing some term | Euclid-style argument |
| 2015 | 1 | 1 | Algebra | UK2015R1P1.lean | Order 3^{3^4},3^{4^3},3^{4^4},4^{3^3},4^{3^4} | Direct exponent comparisons |
| 2015 | 1 | 2 | NumberTheory | UK2015R1P2.lean | p²+a²=b², p prime>3 ⇒ 12\|a and 2(p+a+1) square | Modular analysis |
| 2015 | 1 | 3 | Combinatorics | UK2015R1P3.lean | 7 rooms, no adjacents on same side of corridor | Binomial counting |
| 2015 | 1 | 4 | Algebra | UK2015R1P4.lean | t=x+1/x integer >2, show tₙ integer, t\|tₙ cases | Recurrence, integrality |
| 2015 | 1 | 6 | FunctionalEquation | UK2015R1P6.lean | f positive, 1/a+1/b=1/c ⇒ 1/f(a)+1/f(b)=1/f(c) | Multiplicative, simple form |
| 2015 | 2 | 1 | Algebra | UK2015R2P1.lean | x_{n+1}=((√2+1)xₙ−1)/((√2+1)+xₙ), find x₂₀₁₅ | Tangent-addition periodicity |
| 2016 | 1 | 3 | Algebra | UK2016R1P3.lean | tₙ=An²+Bn+C matches most Fibonacci terms | Small-case calculation |
| 2016 | 1 | 6 | NumberTheory | UK2016R1P6.lean | Every positive int is sum of distinct charming nums | Greedy/induction |
| 2016 | 2 | 4 | NumberTheory | UK2016R2P4.lean | p²=mean(u²,v²) ⇒ 2p−u−v square or 2·square | Algebraic manipulation |
| 2017 | 1 | 1 | Combinatorics | UK2017R1P1.lean | Count odd digits in 1..2016 | Direct summation |
| 2017 | 1 | 2 | Algebra | UK2017R1P2.lean | 5y{8y}{25y}=1 with {} = max(x,1/x) | Case split |
| 2017 | 1 | 6 | NumberTheory | UK2017R1P6.lean | Smallest m consec divisible by n,n+2,n+4,n+6 | CRT |
| 2017 | 2 | 2 | Algebra | UK2017R2P2.lean | aₙ=(1/n)Σ⌊n/i⌋, infinitely increases/decreases? | Prime-gap analysis |
| 2018 | 1 | 2 | Combinatorics | UK2018R1P2.lean | 6 friends, 75/100 days, bounds on n days ≥5 swim | Inclusion-exclusion |
| 2018 | 1 | 4 | Algebra | UK2018R1P4.lean | aₙ₊₁+aₙ=(aₙ₊₁−aₙ)², how many values a_{2017} | Recurrence branches counting |
| 2018 | 2 | 3 | NumberTheory | UK2018R2P3.lean | Is (m+1)³+…+(2m)³ a square? | Cube-sum identity |
| 2019 | 1 | 2 | NumberTheory | UK2019R1P2.lean | n-ring positive integers, product of 3 neighbours=n | Divisibility classification |
| 2019 | 1 | 5 | Algebra | UK2019R1P5.lean | Similar cylinders h₁+h₂=1, SA,V given | Polynomial system |
| 2019 | 1 | 6 | Combinatorics | UK2019R1P6.lean | Ada's walk, count returns to origin mod 10 | Generating function |
| 2019 | 2 | 3 | NumberTheory | UK2019R2P3.lean | Subsets of {1..p−1} with sum ≡0 mod p | Roots-of-unity filter |
| 2019 | 2 | 4 | FunctionalEquation | UK2019R2P4.lean | Monotone f, f(x⁴)+f(x²)+f(x)+f(1)=x⁴+x²+x+1 | f=id forced |
| 2020 | 1 | 6 | FunctionalEquation | UK2020R1P6.lean | f: ℤ×ℤ→ℤ, two linear relations | Linear algebra over ℤ² |
| 2020 | 2 | 4 | Algebra | UK2020R2P4.lean | bₙ₊₂=(bₙ₊₁²−1)/bₙ, bounded and unbounded cases | Cosh/cos substitution |
| 2021 | 1 | 4 | Algebra | UK2021R1P4.lean | AAA+AA=B,BBC,… decode digits | Finite digit search, decide |
| 2021 | 1 | 6 | NumberTheory | UK2021R1P6.lean | Sum of 2 powers of 2 and 2 Mersenne primes ⇒ sum of 2 squares | Case split on Mersenne exponent |
| 2021 | 2 | 4 | NumberTheory | UK2021R2P4.lean | aₙ smallest new integer with integer mean, aᵢ−i bijection | Constructive NT |
| 2022 | 1 | 3 | Combinatorics | UK2022R1P3.lean | 3 copies each of 2⁰,…,2¹¹ summing to 2021 | Generating function/binary |
| 2022 | 1 | 5 | NumberTheory | UK2022R1P5.lean | m(N) integer for how many N<2021 | Arithmetic classification |
| 2022 | 2 | 2 | FunctionalEquation | UK2022R2P2.lean | 2y·f(f(x²)+x)=f(x+1)f(2xy) | Multiplicative FE, f(n)=n forced |
| 2023 | 1 | 2 | NumberTheory | UK2023R1P2.lean | Two-rule recurrence, max squares in first 2022 | Parity & structure |
| 2024 | 1 | 2 | Algebra | UK2024R1P2.lean | Either-or recurrence, a_{2023},a_{2024} consec ⇒ a₀,a₁ consec | Invariant tracking |
| 2024 | 2 | 2 | FunctionalEquation | UK2024R2P2.lean | 2f(f(n))=5f(n)−2n over ℤ | Linear, f(n)=2n or n/... |
| 2024 | 2 | 4 | Combinatorics | UK2024R2P4.lean | n piles of m, remove n from two piles, empty | Invariant (arithmetic condition) |
| 2025 | 1 | 5 | NumberTheory | UK2025R1P5.lean | Smallest n>1 with p\|n⁶−1, then (n+1) or (n+2) works | Roots of x⁶=1 mod p |
| 2025 | 2 | 4 | Algebra | UK2025R2P4.lean | u₁=1, u_{n+1}=(uₙ²+uₙ+1)^{2025}/u_{n−1}, count sequences | Divisibility constraint counting |

## T3 — Hard but tractable
| Year | Round | # | Topic | Lean filename | One-line statement gist | Rationale |
| ---- | ----- | - | ----- | ------------- | ----------------------- | --------- |
| 2005 | 1 | 3 | Combinatorics | UK2005R1P3.lean | Least n so any 2-colouring of {1..n} has mono x+y+z=w | Schur-like, needs case analysis |
| 2005 | 2 | 4 | Combinatorics | UK2005R2P4.lean | 3-subsets of {1..36}, intersecting, total ∩ empty | Combinatorial counting, explicit max |
| 2006 | 1 | 2 | Combinatorics | UK2006R1P2.lean | Adrian splits 6 pairs twins into teams (2×6 and 3×4) | Closed-form counting |
| 2006 | 1 | 6 | Combinatorics | UK2006R1P6.lean | Even # triangles a point lies in, 2005 points | Parity combinatorial argument |
| 2006 | 2 | 4 | Combinatorics | UK2006R2P4.lean | 2006 kids, 6 questions, any 3 answer ≥5, min total right | Extremal combinatorics |
| 2007 | 1 | 3 | Combinatorics | UK2007R1P3.lean | Permutations of digits 1–9 with order constraints | Direct counting |
| 2008 | 1 | 4 | Combinatorics | UK2008R1P4.lean | 756 from {1..2008}: two sum divisible by 8 | Pigeonhole on residues |
| 2008 | 2 | 3 | Combinatorics | UK2008R2P3.lean | Adrian's circle radius deduced in 60 questions | Search strategy framework |
| 2009 | 1 | 1 | Combinatorics | UK2009R1P1.lean | Zigzag paths on 8×8 chessboard count | Dynamic programming count |
| 2009 | 2 | 4 | Combinatorics | UK2009R2P4.lean | b(n) blocks in binary, n≤2500 ⇒ b(n)≤39 | Explicit binary structure |
| 2010 | 1 | 3 | Combinatorics | UK2010R1P3.lean | Nondecreasing sequences of 6 scores 0–10 | Stars & bars, closed form |
| 2011 | 2 | 4 | Combinatorics | UK2011R2P4.lean | Parallelogram-free subset of 2011×2011 grid | Extremal construction |
| 2012 | 2 | 3 | Combinatorics | UK2012R2P3.lean | Reals split in two, m(z−y)=n(y−x) exists mono | Density / choice |
| 2013 | 1 | 1 | Combinatorics | UK2013R1P1.lean | Max counters 8×8, ≤4 per row/col/diag | Extremal with explicit max |
| 2013 | 1 | 5 | Geometry | UK2013R1P5.lean | Max area of triangle with sides ≤2,3,4 | Coord-friendly area optimisation |
| 2014 | 2 | 1 | Combinatorics | UK2014R2P1.lean | Min colours for 2014-gon crossing diagonals | Chromatic number of intersection graph |
| 2015 | 2 | 2 | Combinatorics | UK2015R2P2.lean | Equivalence of two parity statements on councils | Parity/generating function |
| 2015 | 2 | 4 | Combinatorics | UK2015R2P4.lean | Existence of 100-loop (see-relation) | Existence construction |
| 2016 | 1 | 1 | Combinatorics | UK2016R1P1.lean | Days when books split evenly among shelves | Direct counting, arithmetic |
| 2016 | 1 | 4 | Combinatorics | UK2016R1P4.lean | James' red/blue jars max moves under constraints | Extremal path counting |
| 2017 | 1 | 4 | Combinatorics | UK2017R1P4.lean | Naomi/Tom pick to keep sum = diff of squares | Game with explicit strategy |
| 2017 | 2 | 1 | Combinatorics | UK2017R2P1.lean | Right isoceles triangle with n lattice pts on perim | Lattice counting |
| 2017 | 2 | 4 | Combinatorics | UK2017R2P4.lean | Booby-trapped safe Close/Fail optimal attempts | Information theory + strategy |
| 2018 | 1 | 5 | Combinatorics | UK2018R1P5.lean | Min coloured cells so no 100-comb in 200×200 | Extremal combinatorics |
| 2018 | 1 | 6 | Combinatorics | UK2018R1P6.lean | Min cards with integer running mean from {1..300} | Number-theoretic min argument |
| 2018 | 2 | 4 | FunctionalEquation | UK2018R2P4.lean | Monotone f, f^{2018}(z) integer, existence questions | Construction/analysis |
| 2019 | 1 | 1 | Combinatorics | UK2019R1P1.lean | 5 two-digit multiples of 3, each digit once | Finite search, 250k cases |
| 2019 | 2 | 2 | Combinatorics | UK2019R2P2.lean | n² chess pieces teleport distance n, valid n | Combinatorial construction |
| 2020 | 1 | 4 | Combinatorics | UK2020R1P4.lean | Penguin queue via largest proper divisor | Recursive tree structure |
| 2020 | 1 | 5 | Combinatorics | UK2020R1P5.lean | 6 kids circular, sweet-sharing move, perfect n | Invariant mod |
| 2020 | 2 | 2 | Geometry | UK2020R2P2.lean | ≥4 points, every triangle same circumradius | Classification problem |
| 2020 | 2 | 3 | Combinatorics | UK2020R2P3.lean | Balanced colouring of 2019×2019 grid | Extremal counting |
| 2021 | 1 | 3 | Combinatorics | UK2021R1P3.lean | Counting fold sequences of a square n∈{3,6,9} | Finite tree enumeration |
| 2021 | 1 | 7 | Combinatorics | UK2021R1P7.lean | Evie/Odette pebble game, values of n Evie wins | Game analysis |
| 2021 | 2 | 1 | NumberTheory | UK2021R2P1.lean | Every n has a "good" multiple | Constructive existence |
| 2021 | 2 | 2 | Combinatorics | UK2021R2P2.lean | Tile n×n with a² and b²; single-tile alternative | Constructive tiling |
| 2022 | 1 | 2 | Combinatorics | UK2022R1P2.lean | Min games with 30/40/50/60/70% wins | Bounded search + constraint |
| 2022 | 1 | 6 | Combinatorics | UK2022R1P6.lean | 71-term lists doubling/repeating, sum 999999 count | Enumeration |
| 2022 | 1 | 4 | Geometry | UK2022R1P4.lean | Circles intersecting through centres, equilateral D0₁E | Coordinate geometry feasible |
| 2022 | 2 | 1 | NumberTheory | UK2022R2P1.lean | k-numbers characterisation (∞ many) | Diophantine classification |
| 2022 | 2 | 3 | Combinatorics | UK2022R2P3.lean | Decks of 50, boxes ≤2022, split into two regular piles | Pigeonhole/existence |
| 2023 | 1 | 4 | Combinatorics | UK2023R1P4.lean | Alex/Katy 8×8 game, Katy's guaranteed score | Game/strategy (tractable size) |
| 2023 | 1 | 5 | Combinatorics | UK2023R1P5.lean | Count chains of divisors, N\|f(n) | Number-theoretic counting |
| 2023 | 2 | 3 | Combinatorics | UK2023R2P3.lean | Count ideal n-lists | Complex but closed-form count |
| 2023 | 2 | 4 | NumberTheory | UK2023R2P4.lean | Triangle integer sides, ∠A=3∠B ⇒ a cube | Algebraic NT |
| 2024 | 1 | 1 | Combinatorics | UK2024R1P1.lean | Unreliable typist OLYMPIADS spellings count | Similar to existing UK2024R1P1 |
| 2024 | 1 | 5 | Combinatorics | UK2024R1P5.lean | 1000 dots, red adj/blue 2-apart fault min | Extremal via LP/DP |
| 2025 | 2 | 3 | Combinatorics | UK2025R2P3.lean | Min row/col swaps to restore chess colouring | Permutation/sort bound |

## T4 — Skip / very hard
| Year | Round | # | Topic | Lean filename | One-line statement gist | Why skip |
| ---- | ----- | - | ----- | ------------- | ----------------------- | -------- |
| 2005 | 1 | 2 | Geometry | UK2005R1P2.lean | Semicircles on BC, AC: CP = CQ | Synthetic Euclidean, thin API |
| 2005 | 2 | 2 | Geometry | UK2005R2P2.lean | ∠BAC=120°, circle on EF passes through D | Angle chase, cyclic quad |
| 2006 | 1 | 3 | Geometry | UK2006R1P3.lean | Cyclic quad, AC bisects ∠DAB, CE=CA iff DE=AB | Iff with directed angles |
| 2006 | 1 | 4 | Combinatorics | UK2006R1P4.lean | Greatest cells on equilateral triangular path | Ad-hoc path combinatorics, hard encoding |
| 2006 | 1 | 5 | Geometry | UK2006R1P5.lean | Convex quad has area-bisecting point ⇔ parallelogram | Integral/area geometry |
| 2006 | 2 | 3 | Geometry | UK2006R2P3.lean | ∠BPC+∠BAC=180° construction | Synthetic geometry |
| 2007 | 1 | 2 | Geometry | UK2007R1P2.lean | Divide sides into thirds, area equalities in quad | Area chase in generic quad |
| 2007 | 1 | 4 | Geometry | UK2007R1P4.lean | Touching circles, AP diameter, PQ tangent = AP | Power of a point |
| 2007 | 2 | 3 | Geometry | UK2007R2P3.lean | ∠BAC=60°, OH hits AB at P, AC at Q, PO=HQ | Euler line, synthetic |
| 2007 | 2 | 4 | Combinatorics | UK2007R2P4.lean | Hexagonia rail network connected subgraphs count | Graph-theoretic enumeration |
| 2008 | 1 | 3 | Geometry | UK2008R1P3.lean | Circumcircle, feet of perpendiculars, similar triangles | Synthetic similarity |
| 2008 | 1 | 5 | Geometry | UK2008R1P5.lean | (BL/LC)(CM/MA)(AN/NB)≤1/8, internal point | Cevian inequality, AM-GM chasing |
| 2008 | 2 | 2 | Geometry | UK2008R2P2.lean | Incentre I, circumcentre O, ∠AIO=90° ∠CIO=45°, ratio | Hard trig identity |
| 2009 | 1 | 3 | Geometry | UK2009R1P3.lean | Parallelogram, circumcircle, PQ=AC iff ∠BAC=60° | Synthetic iff |
| 2009 | 2 | 2 | Geometry | UK2009R2P2.lean | Centre of circle BOH lies on AB | Synthetic circumcentre |
| 2010 | 1 | 2 | Geometry | UK2010R1P2.lean | AB∥ED in circle, ∠ABC=90° iff AC²=BD²+CE² | Cyclic quad chase |
| 2010 | 1 | 4 | Geometry | UK2010R1P4.lean | Two tangent circles, BC=2AF | Synthetic, perp bisector |
| 2010 | 2 | 1 | Combinatorics | UK2010R2P1.lean | 2010^2010 children, ≤3 friends, line-up condition | Graph theory framework |
| 2010 | 2 | 2 | Geometry | UK2010R2P2.lean | Centroid, midpoints, ∠AEC=∠DGC iff ∠ACB=90° | Synthetic angle chase |
| 2011 | 1 | 3 | Geometry | UK2011R1P3.lean | Circles ABL, CAL, L,M,N collinear | Synthetic with two circles |
| 2011 | 1 | 5 | Geometry | UK2011R1P5.lean | Two circles meet L,M, K lies on fixed circle | Locus/inversion |
| 2011 | 2 | 1 | Geometry | UK2011R2P1.lean | Concyclic R,W,V,Q from interior X | Cyclic quad via parallels |
| 2012 | 1 | 3 | Geometry | UK2012R1P3.lean | S₁,S₂ tangent to S at X,Y, radii difference independent | Inversion/power of a point |
| 2012 | 1 | 4 | Combinatorics | UK2012R1P4.lean | Ball-bag game (double / triple) always emptiable | Game/strategy framework |
| 2012 | 1 | 6 | Geometry | UK2012R1P6.lean | DE+DF ≤ BC, orthic triangle | Synthetic trig inequality |
| 2012 | 2 | 1 | Geometry | UK2012R2P1.lean | Midpoints of cyclic quad sides, equal-radius circles | Synthetic, hard |
| 2013 | 1 | 2 | Geometry | UK2013R1P2.lean | Two tangent circles, B,X,P collinear | Synthetic |
| 2013 | 1 | 6 | Geometry | UK2013R1P6.lean | Circles S,T,ABC; D midpoint of AE | Radical axis / circle chase |
| 2013 | 2 | 2 | Geometry | UK2013R2P2.lean | ∠ABP=∠PCA inside ABC, parallelogram, ∠QAB=∠CAP | Isogonal conjugates |
| 2013 | 2 | 4 | Geometry | UK2013R2P4.lean | Inscribed circle, all of PA…PD,AB integers | Diophantine over geometry |
| 2014 | 1 | 2 | Geometry | UK2014R1P2.lean | EF parallel to AB with tangent line | Synthetic |
| 2014 | 1 | 5 | Geometry | UK2014R1P5.lean | Equilateral triangle P inside, foot perpendicular equalities | Area/length identities |
| 2014 | 1 | 6 | Inequality | UK2014R1P6.lean | 60 ≤ (aA+bB+cC)/(a+b+c) < 90 with angles in degrees | Mixing reals and angles, trig inequality |
| 2014 | 2 | 4 | Geometry | UK2014R2P4.lean | Nested circumcircles concurrent lines | Synthetic, very deep |
| 2015 | 1 | 5 | Geometry | UK2015R1P5.lean | Cyclic quad, arc midpoint, PQ ∥ AB | Synthetic arc/chord |
| 2015 | 2 | 3 | Geometry | UK2015R2P3.lean | Locus of incentre on variable chord | Euclidean locus |
| 2016 | 1 | 2 | Geometry | UK2016R1P2.lean | Cyclic quad ABCD, tangent circle ADE, triangle CDF isoceles | Synthetic tangent/angle |
| 2016 | 1 | 5 | Geometry | UK2016R1P5.lean | P,Q,R,S collinear from orthocentric configuration | Pedal/Simson line |
| 2016 | 2 | 1 | Geometry | UK2016R2P1.lean | 3 circles on tangent, 16(r₁+r₂+r₃)≥9(AB+BC+CA) | Geometry inequality |
| 2016 | 2 | 2 | Combinatorics | UK2016R2P2.lean | Alison hockey teams, comparison queries, max N | Adversarial info strategy |
| 2016 | 2 | 3 | Geometry | UK2016R2P3.lean | PQ⊥AC ⇒ PE⊥BC, cyclic quad | Projective / synthetic |
| 2017 | 1 | 5 | Geometry | UK2017R1P5.lean | Area equalities imply ∠BCA=90° | Trig area conditions |
| 2017 | 2 | 3 | Geometry | UK2017R2P3.lean | Bisectors and parallels, cyclic quad | Synthetic bisector |
| 2018 | 1 | 3 | Geometry | UK2018R1P3.lean | Isoceles triangle, MN divides perim+area equally | Computable but messy; borderline |
| 2018 | 2 | 1 | Geometry | UK2018R2P1.lean | AB·BP=2BM², circle tangent to BC at B | Power of a point |
| 2018 | 2 | 2 | Combinatorics | UK2018R2P2.lean | Alice at circular table, eat all cakes with moves aᵢ | Game/strategy framework |
| 2019 | 1 | 4 | Geometry | UK2019R1P4.lean | Semicircle, tangents at D,E meet at F; angle identity | Synthetic tangent |
| 2019 | 2 | 1 | Geometry | UK2019R2P1.lean | Triangle BPE isoceles from perp construction | Synthetic perpendiculars |
| 2020 | 1 | 3 | Geometry | UK2020R1P3.lean | Two tangent circles, AC⊥BD | Synthetic perpendicularity |
| 2021 | 1 | 2 | Geometry | UK2021R1P2.lean | Isoceles triangle, P=A², integer cases | Heron-based Diophantine (borderline but has geom) |
| 2021 | 1 | 5 | Geometry | UK2021R1P5.lean | Tangent circles, AD=DP ⇒ BP=AC | Synthetic tangent-chord |
| 2021 | 2 | 3 | Geometry | UK2021R2P3.lean | AI and KD meet on Γ, incentre configuration | Synthetic, hard |
| 2022 | 2 | 4 | Geometry | UK2022R2P4.lean | Tangent at T, perpendiculars, AT through Q | Synthetic, advanced |
| 2023 | 1 | 3 | Geometry | UK2023R1P3.lean | Midpoints and foot perpendicular collinearity | Synthetic four-point |
| 2023 | 1 | 6 | Geometry | UK2023R1P6.lean | Frog on circle/line, finite jumps return | Dynamical/geometric argument |
| 2023 | 2 | 1 | Geometry | UK2023R2P1.lean | Obtuse ABC, incentre, BCQP cyclic | Synthetic incentre |
| 2023 | 2 | 2 | Combinatorics | UK2023R2P2.lean | Rearrange 1..n by mod-3 adjacency moves to cyclic shift | Invariant analysis, permutation |
| 2024 | 1 | 3 | Geometry | UK2024R1P3.lean | X on AC, Y on circle, BZ⊥AC | Synthetic circle |
| 2024 | 1 | 6 | Geometry | UK2024R1P6.lean | Convex polygon equal edges & equal step-3 diagonals | Classification, cyclic structure |
| 2024 | 2 | 1 | NumberTheory | UK2024R2P1.lean | First n digits of 10/13, ≥49 have ≥3 prime factors | Factor tables, huge case analysis |
| 2024 | 2 | 3 | Geometry | UK2024R2P3.lean | Midpoints PB,PC meet AB,AC; AXPY cyclic | Synthetic |
| 2025 | 1 | 1 | Combinatorics | UK2025R1P1.lean | Which n in 3..12 admit divisibility-happy circle | Classification, ad-hoc |
| 2025 | 1 | 2 | Combinatorics | UK2025R1P2.lean | Card-trick magician's order works iff n=... | Strategy/construction framework |
| 2025 | 1 | 3 | Combinatorics | UK2025R1P3.lean | Rhian/Jack 10^6 factoring game winning player | Game theory framework |
| 2025 | 1 | 4 | Geometry | UK2025R1P4.lean | AB=CP, ∠PAB=∠BCP ⇒ ∠CPB=90° | Synthetic with midpoint |
| 2025 | 1 | 6 | Combinatorics | UK2025R1P6.lean | 4×4×4 cube, 12 same-colour cubes in 6 equidistant pairs | Pigeonhole in 3D, complex |
| 2025 | 2 | 2 | Geometry | UK2025R2P2.lean | Incentre, perp bisector BC, cyclic through D | Synthetic |
