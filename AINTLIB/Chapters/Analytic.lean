import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Bertrand

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Analytic Number Theory" =>

This chapter covers the Riemann zeta function and Dirichlet $`L`-functions, Euler products, the von Mangoldt function, non-vanishing on the line $`\operatorname{Re}(s) = 1`, Dirichlet's theorem on primes in arithmetic progressions, and Bertrand's postulate. Throughout, $`s` denotes a complex variable, $`p` a prime, and $`\chi` a Dirichlet character of modulus $`q`.

# The Riemann zeta function

:::definition "riemann-zeta" (lean := "riemannZeta")
The *Riemann zeta function* $`\zeta(s)` is the meromorphic continuation to all of $`\mathbb{C}` of the Dirichlet series
$$`\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}, \qquad \operatorname{Re}(s) > 1.`
It has a simple pole at $`s = 1` and is holomorphic everywhere else.
:::

:::theorem "zeta-euler-product" (lean := "riemannZeta_eulerProduct_tprod")
*(Euler product for $`\zeta`.)* For $`\operatorname{Re}(s) > 1`,
$$`\zeta(s) = \prod_{p} \frac{1}{1 - p^{-s}},`
where the product is taken over all primes $`p` and converges absolutely.
:::

:::proof "zeta-euler-product"
For $`\operatorname{Re}(s) > 1` the series $`\sum_{n \ge 1} n^{-s}` defining $`\zeta` ({uses "riemann-zeta"}[]) converges absolutely. The Euler product is exactly the analytic incarnation of unique factorisation ({uses "fta-uniqueness"}[]): because every $`n \ge 1` is uniquely a product of prime powers, expanding the product $`\prod_p \sum_{k \ge 0} p^{-ks}` and using the multiplicativity of $`n \mapsto n^{-s}` reproduces each term $`n^{-s}` exactly once. Each local factor $`\sum_{k \ge 0} p^{-ks} = (1 - p^{-s})^{-1}` converges geometrically since $`|p^{-s}| = p^{-\operatorname{Re}(s)} < 1`, and absolute convergence lets one rearrange the double sum over primes and exponents into the original Dirichlet series.
:::

# Dirichlet characters and $`L`-functions

:::definition "dirichlet-character" (lean := "DirichletCharacter")
A *Dirichlet character of modulus $`q`* is a completely multiplicative function $`\chi : \mathbb{Z}/q\mathbb{Z} \to R` that is a multiplicative character of the monoid $`\mathbb{Z}/q\mathbb{Z}` — that is, a monoid homomorphism from $`\mathbb{Z}/q\mathbb{Z}` to the multiplicative monoid of $`R` that sends non-units to $`0`. In the analytic theory one takes $`R = \mathbb{C}`.
:::

:::definition "lseries" (lean := "LSeries")
For a function $`f : \mathbb{N} \to \mathbb{C}`, the *$`L`-series* (Dirichlet series) associated to $`f` is
$$`L(f, s) = \sum_{n=1}^{\infty} \frac{f(n)}{n^s},`
defined at those $`s \in \mathbb{C}` for which the series converges absolutely.
:::

:::definition "dirichlet-lfunction" (lean := "DirichletCharacter.LFunction")
For a Dirichlet character $`\chi` of modulus $`q` ({uses "dirichlet-character"}[]), the *Dirichlet $`L`-function* $`L(s, \chi)` is the meromorphic continuation to all of $`\mathbb{C}` of the $`L`-series ({uses "lseries"}[]) of $`\chi`,
$$`L(s, \chi) = \sum_{n=1}^{\infty} \frac{\chi(n)}{n^s}, \qquad \operatorname{Re}(s) > 1.`
When $`\chi` is non-trivial the continuation is entire; when $`\chi` is the trivial character of modulus $`q` the function has a simple pole at $`s = 1` and agrees (up to finitely many Euler factors) with $`\zeta(s)`.
:::

:::theorem "dirichlet-lfunction-euler-product" (lean := "DirichletCharacter.LSeries_eulerProduct_tprod")
*(Euler product for $`L(s, \chi)`.)* For $`\operatorname{Re}(s) > 1`,
$$`L(s, \chi) = \prod_{p} \frac{1}{1 - \chi(p)\, p^{-s}},`
where the product converges absolutely.
:::

:::proof "dirichlet-lfunction-euler-product"
The proof is the same as for $`\zeta` ({uses "zeta-euler-product"}[]): the complete multiplicativity of $`\chi` ({uses "dirichlet-character"}[]) allows the absolutely convergent Dirichlet series ({uses "lseries"}[]) to be re-expanded as an Euler product, with each local factor $`\sum_{k \ge 0} \chi(p^k) p^{-ks} = \sum_{k \ge 0} \chi(p)^k p^{-ks} = (1 - \chi(p) p^{-s})^{-1}` converging geometrically.
:::

# The von Mangoldt function

:::definition "von-mangoldt" (lean := "ArithmeticFunction.vonMangoldt")
The *von Mangoldt function* $`\Lambda : \mathbb{N} \to \mathbb{R}` is defined by
$$`\Lambda(n) = \begin{cases} \log p & \text{if } n = p^k \text{ for some prime } p \text{ and } k \ge 1, \\ 0 & \text{otherwise.}\end{cases}`
At a prime $`n = p`, the value is simply $`\Lambda(p) = \log p`.
:::

:::theorem "von-mangoldt-zeta-identity" (lean := "ArithmeticFunction.vonMangoldt_mul_zeta")
The von Mangoldt function is the Dirichlet convolution of $`\log` and the Möbius function: as arithmetic functions,
$$`\Lambda * \mathbf{1} = \log,`
where $`\mathbf{1}` denotes the constant function $`1` and $`*` denotes Dirichlet convolution. Equivalently, for every $`n \ge 1`,
$$`\sum_{d \mid n} \Lambda(d) = \log n.`
:::

:::proof "von-mangoldt-zeta-identity"
The identity $`\sum_{d \mid n} \Lambda(d) = \log n` follows by comparing the unique factorization of $`n` ({uses "fta-existence"}[]): writing $`n = \prod_{p \mid n} p^{v_p(n)}`, the sum $`\sum_{d \mid n} \Lambda(d)` picks up a contribution $`\log p` for each prime power divisor $`p^k` with $`k \ge 1`, and the total is $`\sum_{p \mid n} v_p(n) \log p = \log \prod_p p^{v_p(n)} = \log n` ({uses "von-mangoldt"}[]). Dually, inverting the convolution $`\Lambda * \mathbf{1} = \log` against the Möbius function ({uses "moebius"}[]), the inverse of $`\mathbf{1}`, recovers $`\Lambda = \mu * \log`, i.e. $`\Lambda(n) = \sum_{d \mid n} \mu(n/d) \log d`.
:::

# Non-vanishing of $`L`-functions on $`\operatorname{Re}(s) \ge 1`

:::theorem "lfunction-nonvanishing" (lean := "DirichletCharacter.LFunction_ne_zero_of_one_le_re")
Let $`\chi` be a Dirichlet character of modulus $`q`. Then $`L(s, \chi) \ne 0` for all $`s` with $`\operatorname{Re}(s) \ge 1`, except when $`\chi` is the trivial character and $`s = 1` (where $`L(s, \chi)` has a simple pole rather than a zero).
:::

:::proof "lfunction-nonvanishing"
The proof has two stages. When $`\operatorname{Re}(s) > 1` the Euler product ({uses "dirichlet-lfunction-euler-product"}[]) shows $`L(s, \chi) \ne 0` directly, since each factor $`(1 - \chi(p) p^{-s})^{-1}` is finite and nonzero.

On the line $`\operatorname{Re}(s) = 1` the argument is deeper. For quadratic characters $`\chi^2 = 1` one must rule out a zero at $`s = 1` (a "Siegel zero" in its simplest form): this is done via a positivity argument exploiting the Euler product for $`\zeta(s)^3 |L(s,\chi)|^4 |L(s,\chi^2)|`, which would blow up if $`L(1,\chi) = 0`. For non-quadratic characters the non-vanishing on $`\operatorname{Re}(s) = 1` follows from analytic continuation and the fact that $`L(s,\chi)` has no pole there.
:::

:::theorem "lfunction-one-nonvanishing" (lean := "DirichletCharacter.LFunction_apply_one_ne_zero")
For a non-trivial Dirichlet character $`\chi`, the value $`L(1, \chi)` is nonzero.
:::

:::proof "lfunction-one-nonvanishing"
This is the special case $`s = 1` of {uses "lfunction-nonvanishing"}[]. It is also the key step in Dirichlet's proof of his theorem on primes in arithmetic progressions ({uses "dirichlets-theorem"}[]): if $`L(1, \chi) = 0` for some non-trivial $`\chi`, the product formula for primes in the residue class $`a \bmod q` would collapse to zero, contradicting the divergence of the series $`\sum_{p \equiv a} p^{-1}`.
:::

# Dirichlet's theorem on primes in arithmetic progressions

:::theorem "dirichlets-theorem" (lean := "Nat.infinite_setOf_prime_and_eq_mod")
*(Dirichlet's theorem.)* Let $`q` be a positive integer and let $`a` be an integer coprime to $`q`. Then there are infinitely many primes $`p` with $`p \equiv a \pmod{q}`. In particular, every residue class coprime to the modulus contains infinitely many primes.
:::

:::proof "dirichlets-theorem"
The proof uses the analytic properties of Dirichlet $`L`-functions ({uses "dirichlet-lfunction"}[]). For each Dirichlet character $`\chi` of modulus $`q` ({uses "dirichlet-character"}[]) one forms the logarithmic sum $`\sum_p \chi(p) p^{-s}`. Via the Euler product ({uses "dirichlet-lfunction-euler-product"}[]) this is asymptotically $`-\log L(s, \chi)` plus a convergent error as $`s \to 1^+`.

Orthogonality of characters then isolates the contribution from the residue class $`a`: the sum $`\sum_{p \equiv a \pmod{q}} p^{-s}` equals $`\frac{1}{\varphi(q)} \sum_\chi \overline{\chi}(a) (-\log L(s, \chi) + \text{convergent})`. The trivial character contributes a $`\log\frac{1}{s-1}` term (from the pole of $`\zeta`), while the non-trivial characters contribute finite limits at $`s = 1` because $`L(1, \chi) \ne 0` ({uses "lfunction-one-nonvanishing"}[]). Hence the full sum diverges as $`s \to 1^+`, proving the residue class contains infinitely many primes.
:::

:::corollary "dirichlets-theorem-gt" (lean := "Nat.forall_exists_prime_gt_and_modEq")
Let $`q` be a positive integer, $`a` a natural number coprime to $`q`, and $`n` any natural number. Then there exists a prime $`p > n` with $`p \equiv a \pmod{q}`.
:::

:::proof "dirichlets-theorem-gt"
By Dirichlet's theorem ({uses "dirichlets-theorem"}[]) the residue class $`a \bmod q` contains infinitely many primes. An infinite set of primes is unbounded, so for any threshold $`n` at least one of them exceeds $`n`; this is the asserted prime $`p > n` with $`p \equiv a \pmod q`.
:::

# Bertrand's postulate

:::theorem "bertrand" (lean := "Nat.exists_prime_lt_and_le_two_mul")
*(Bertrand's postulate.)* For every positive integer $`n`, there exists a prime $`p` with $`n < p \le 2n`.
:::

:::proof "bertrand"
Bertrand's postulate sharpens the infinitude of primes ({uses "infinitude-of-primes"}[]), guaranteeing a prime not merely beyond $`n` but inside the dyadic window $`(n, 2n]`. The proof is elementary and proceeds in two stages. For large $`n` (specifically $`n \ge 512`), one analyses the central binomial coefficient $`\binom{2n}{n}`. On the one hand $`\binom{2n}{n} \ge \frac{4^n}{2n+1}`, which grows exponentially. On the other hand, if no prime lies in $`(n, 2n]`, then every prime factor of $`\binom{2n}{n}` is at most $`n`, and a careful count of prime-power factors — using the Legendre formula $`v_p(m!) = \sum_{k \ge 1} \lfloor m/p^k \rfloor` for the $`p`-adic valuation ({uses "padic-val-nat"}[]) of a factorial — yields the upper bound $`\binom{2n}{n} \le \prod_{p \le \sqrt{2n}} (2n)^{1/\log p} \cdot \prod_{\sqrt{2n} < p \le 2n/3} p`, which grows subexponentially. For $`n \ge 512` these bounds contradict each other, so a prime in $`(n, 2n]` must exist.

For small $`n < 512` the postulate is verified directly by exhibiting explicit primes: the sequence $`2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631` covers all gaps up to $`521` (each prime is less than twice the previous).
:::

# Phase 3 (external projects, not yet in Mathlib)

The nodes below are *informal*: the external projects are built against Lean toolchains or Mathlib versions incompatible with AINTLIB, so they carry no `(lean := …)` reference. Each records where the result is formalised and its sorry-free / in-progress status. They connect into the dependency graph through the Mathlib-backed nodes above.

## Euler products, Wiener–Ikehara, and conditional PNT (EulerProducts)

:::definition "euler-product-general"
For a weakly multiplicative arithmetic function $`f : \mathbb{N} \to \mathbb{C}` with $`f(1) = 1`, if the $`L`-series $`L(f, s) = \sum_{n \ge 1} f(n) n^{-s}` ({uses "lseries"}[]) converges absolutely at $`s`, then
$$`L(f,s) = \prod_{p} \sum_{e \ge 0} f(p^e)\, p^{-es}.`
When $`f` is completely multiplicative the local factor simplifies to $`(1 - f(p)\,p^{-s})^{-1}`. This is the general analytic incarnation of unique factorisation ({uses "fta-uniqueness"}[]): expanding the product and grouping by $`n = \prod_p p^{e_p}` reproduces each Dirichlet coefficient $`f(n) n^{-s}` exactly once. The Euler products for $`\zeta` ({bpref "zeta-euler-product"}[]) and for Dirichlet $`L`-functions ({bpref "dirichlet-lfunction-euler-product"}[]) are the completely-multiplicative special cases.
Formalised in [`EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts) (sorry-free).
:::

:::theorem "wiener-ikehara"
*(Wiener–Ikehara Tauberian theorem.)* Let $`f : \mathbb{N} \to \mathbb{R}` be a non-negative arithmetic function with $`L`-series $`L(f, s)`. Suppose there exists $`A \in \mathbb{R}` and a function $`F` that is continuous on $`\{\operatorname{Re}(s) \ge 1\}` and satisfies
$$`F(s) = L(f, s) - \frac{A}{s - 1}, \qquad \operatorname{Re}(s) > 1.`
Then $`\sum_{n \le N} f(n) \sim AN` as $`N \to \infty`.
Formalised in [`EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts) (sorry-free).
:::

:::proof "wiener-ikehara"
The proof is a Fourier-analytic argument due to Wiener and Ikehara. One writes the partial sum $`S(N) = \sum_{n \le N} f(n)` as an inverse Mellin-type integral along the line $`\operatorname{Re}(s) = 1 + \varepsilon`, then shifts the contour left. The hypothesis that $`F` extends continuously to the closed half-plane $`\operatorname{Re}(s) \ge 1` (rather than just analytically) is enough: applying a Bochner-type criterion and the Riemann–Lebesgue lemma to a smoothed version of the partial sum shows the error vanishes as $`N \to \infty`, leaving the residue contribution $`A` at $`s = 1` ({uses "riemann-zeta"}[]).
:::

:::theorem "pnt-von-mangoldt-conditional"
*(Prime Number Theorem via Wiener–Ikehara.)* Assume the Wiener–Ikehara theorem ({uses "wiener-ikehara"}[]). Then
$$`\psi(N) \;\coloneqq\; \sum_{n \le N} \Lambda(n) \;\sim\; N`
as $`N \to \infty`, where $`\Lambda` denotes the von Mangoldt function ({uses "von-mangoldt"}[]).
Formalised in [`EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts) (sorry-free).
:::

:::proof "pnt-von-mangoldt-conditional"
One applies the Wiener–Ikehara theorem ({uses "wiener-ikehara"}[]) to $`f = \Lambda`. The non-vanishing of $`\zeta(s)` on $`\operatorname{Re}(s) = 1` ({uses "lfunction-nonvanishing"}[]) ensures that $`-\zeta'(s)/\zeta(s)` extends continuously to that line, so the hypothesis is satisfied with $`A = 1`. The Euler product ({uses "zeta-euler-product"}[]) identifies $`L(\Lambda, s) = -\zeta'(s)/\zeta(s)` for $`\operatorname{Re}(s) > 1`, and the conclusion follows.
:::

## Non-vanishing of Dirichlet L-functions on the critical line (DirichletNonvanishing)

:::theorem "dirichlet-lfunction-nonvanishing-line"
*(Non-vanishing on $`\operatorname{Re}(s) = 1`.)* Let $`\chi` be a Dirichlet character ({uses "dirichlet-character"}[]) and $`t \in \mathbb{R}`. If $`\chi \ne 1` or $`t \ne 0`, then
$$`L(\chi,\, 1 + it) \;\ne\; 0.`
In particular, for every non-trivial $`\chi` the Dirichlet $`L`-function ({uses "dirichlet-lfunction"}[]) has no zero on the entire line $`\operatorname{Re}(s) = 1`.
Formalised in [`DirichletNonvanishing`](https://github.com/CBirkbeck/DirichletNonvanishing) (sorry-free).
:::

:::proof "dirichlet-lfunction-nonvanishing-line"
The proof splits into two cases. If $`\chi^2 \ne 1` or $`t \ne 0`, a trigonometric positivity argument applied to $`|L(1,s)^3 L(\chi,s)^4 L(\chi^2,s)|` shows the product is bounded below by $`1` for $`\operatorname{Re}(s) > 1`; a zero at $`1 + it` would force this product to zero as $`\operatorname{Re}(s) \to 1^+`, a contradiction.

For a quadratic character $`\chi^2 = 1` with $`t = 0`, assume for contradiction $`L(\chi,1) = 0`. Define the entire function $`F(s) = \zeta(s) L(\chi, s)` (the simple zero of $`L(\chi, s)` at $`s = 1` cancels the pole of $`\zeta`). For $`\operatorname{Re}(s) > 1`, $`F` agrees with the $`L`-series of the Dirichlet convolution $`\mathbf{1} * \chi`, which takes non-negative values. A classical lemma relating the sign of iterated derivatives to coefficient positivity shows $`(-1)^m F^{(m)}(2) \ge 0` for all $`m \ge 0`, forcing $`F(x) > 0` for all real $`x \le 2`. But the trivial zero of $`\zeta` gives $`F(-2) = \zeta(-2) L(\chi,-2) = 0`, a contradiction ({uses "lfunction-one-nonvanishing"}[]).
:::

## The Prime Number Theorem and Chebyshev bounds (PrimeNumberTheoremAnd)

:::theorem "chebyshev-bounds"
*(Chebyshev's bounds.)* There exist positive constants $`c_1, c_2` such that for all $`x \ge 2`,
$$`c_1 x \;\le\; \psi(x) \;\le\; c_2 x,`
where $`\psi(x) = \sum_{n \le x} \Lambda(n)` is the Chebyshev $`\psi`-function ({uses "von-mangoldt"}[]). One may take $`c_1 = 1` and $`c_2 = \log 4 + 4` in the formalization.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (sorry-free).
:::

:::proof "chebyshev-bounds"
The upper bound $`\psi(x) \le (\log 4 + 4)x` follows from a comparison with central binomial coefficients: $`\binom{2n}{n} \ge 4^n / (2n+1)`, so $`\prod_{n < p \le 2n} p \le \binom{2n}{n}`, and the right-hand side is at most $`4^n`, giving the bound by induction on dyadic blocks.

The lower bound comes from the von Mangoldt convolution identity ({uses "von-mangoldt-zeta-identity"}[]): summing $`\sum_{d \mid n} \Lambda(d) = \log n` over $`n \le x` and comparing with bounds on $`\log\lfloor x \rfloor!` via the Legendre valuation formula yields $`\psi(x) \ge x \log 2 - O(\sqrt{x})`, establishing the lower bound.
:::

:::theorem "mertens-first"
*(Mertens' first theorem.)* As $`x \to \infty`,
$$`\sum_{n \le x} \frac{\Lambda(n)}{n} = \log x + O(1).`
Equivalently, $`\sum_{p \le x} \frac{\log p}{p} = \log x + O(1)` ({uses "von-mangoldt"}[]).
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (sorry-free; explicit constant $`\log 4 + 4`).
:::

:::proof "mertens-first"
The identity $`\sum_{d \mid n} \Lambda(d) = \log n` ({uses "von-mangoldt-zeta-identity"}[]) gives, after summation by parts (Abel summation applied to $`\sum_{n \le x} \frac{1}{n} \sum_{d \mid n} \Lambda(d)`), the formula $`\sum_{n \le x} \frac{\Lambda(n)}{n} = \log x - \sum_{n \le x} \frac{\Lambda(n)}{n}\big(\frac{n}{\lfloor n \rfloor} - 1\big) + E` where $`E` collects a tail bounded by the Chebyshev upper bound ({uses "chebyshev-bounds"}[]). The net error is bounded by an explicit constant.
:::

:::theorem "mertens-second"
*(Mertens' second theorem.)* As $`x \to \infty`,
$$`\sum_{p \le x} \frac{1}{p} = \log \log x + M + O\!\left(\frac{1}{\log x}\right),`
where $`M` is the Meissel–Mertens constant $`M = \gamma + \sum_p \bigl(\log(1 - p^{-1}) + p^{-1}\bigr)`.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (in progress; two technical lemmas carry sorry).
:::

:::proof "mertens-second"
From Mertens' first theorem ({uses "mertens-first"}[]) and partial summation, the sum $`\sum_{n \le x} \frac{\Lambda(n)}{n \log n}` is asymptotic to $`\log \log x + \gamma + O(1/\log x)`. The discrepancy between $`\sum_{n \le x} \frac{\Lambda(n)}{n \log n}` and $`\sum_{p \le x} \frac{1}{p}` is $`\sum_{j \ge 2} \sum_{p : p^j \le x} \frac{1}{j p^j}`, which converges to the correction constant as $`x \to \infty`. The result follows by combining these two limits and identifying the Meissel–Mertens constant via the Euler–Mascheroni constant $`\gamma`.
:::

:::theorem "prime-number-theorem"
*(Prime Number Theorem, PNT.)* As $`x \to \infty`,
$$`\psi(x) \;\sim\; x, \qquad \pi(x) \;\sim\; \frac{x}{\log x},`
where $`\psi(x) = \sum_{n \le x} \Lambda(n)` ({uses "von-mangoldt"}[]) and $`\pi(x)` counts primes up to $`x`. More precisely the Kontorovich–PrimeNumberTheoremAnd project establishes a power-of-log saving:
$$`\psi(x) = x + O\!\left(x\,\exp\!\bigl(-c\,(\log x)^{1/10}\bigr)\right)`
for some explicit $`c > 0`.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (sorry-free for the $`\psi`-form; the $`\pi`-equivalence and Wiener–Ikehara PNT are also sorry-free via the Wiener approach).
:::

:::proof "prime-number-theorem"
Two routes are formalised. The Wiener–Ikehara route ({uses "pnt-von-mangoldt-conditional"}[], {uses "wiener-ikehara"}[]) gives $`\psi(N)/N \to 1` by applying the Tauberian theorem to $`\Lambda` with non-vanishing input ({uses "lfunction-nonvanishing"}[]). The contour-integral route (MediumPNT) gives the sharper error: one inverts the Mellin transform of a smooth truncation of the Chebyshev function via a rectangle contour, uses bounds on $`\zeta'(s)/\zeta(s)` in a zero-free region of the form $`\operatorname{Re}(s) \ge 1 - c/\log(|\operatorname{Im}(s)| + 2)`, and applies a Borel–Carathéodory argument to bound the logarithmic derivative. The $`\pi(x) \sim x/\log x` equivalence then follows from $`\psi \sim x` by partial summation ({uses "chebyshev-bounds"}[]).
:::

## Brun–Titchmarsh inequality and the Selberg sieve (PrimeNumberTheoremAnd)

:::theorem "brun-titchmarsh"
*(Brun–Titchmarsh inequality.)* For any real $`x > 0`, $`y > 0`, and $`z > 1`, the number of primes in the interval $`(x, x + y]` satisfies
$$`\pi(x+y) - \pi(x) \;\le\; \frac{2y}{\log z} + 6z\,(1 + \log z)^3.`
In particular, taking $`z = \sqrt{y}` gives $`\pi(x+y) - \pi(x) \ll y/\log y`.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (sorry-free).
:::

:::proof "brun-titchmarsh"
One applies the Selberg sieve ({uses "selberg-sieve"}[]) to sift the interval $`(x, x+y]` by primes up to $`z`. The Selberg sieve gives an upper bound on the count of unsifted elements in terms of $`y / S(z)` plus a remainder sum, where $`S(z) = \sum_{d \le z,\, d \mid \mathrm{rad}} \lambda_d^2 / \nu(d)` is the Selberg bounding sum. A lower bound $`S(z) \ge \log(z)/2` follows from the primorial structure of the sieve support (each prime $`p \le z` contributes $`1/p` to $`\nu`). The remainder is bounded by $`5z(1 + \log z)^3` using divisor-sum estimates, and combining the two gives the stated inequality. Non-sifted elements not accounted for by the sieve are at most $`z`, adding the correction term. Converting the resulting bound on the number of primes in $`(x, x+y]` into the stated $`\ll y/\log y` form, and controlling the prime-counting tails, uses Chebyshev-type prime-counting estimates ({uses "chebyshev-bounds"}[]).
:::

## Non-vanishing and Dirichlet's theorem, analytic route (DirichletNonvanishing)

:::theorem "lfunction-nonvanishing-full"
*(Full non-vanishing on the closed half-plane.)* For a Dirichlet character $`\chi` ({uses "dirichlet-character"}[]) and any $`t \in \mathbb{R}`,
$$`L(\chi, 1 + it) \ne 0`
unless $`\chi = 1` and $`t = 0` (where $`L` has a pole rather than a zero). This strengthens {uses "lfunction-one-nonvanishing"}[] and is the analytic engine behind {uses "dirichlets-theorem"}[].
Formalised in [`DirichletNonvanishing`](https://github.com/CBirkbeck/DirichletNonvanishing) (sorry-free).
:::

:::proof "lfunction-nonvanishing-full"
This is exactly the content of {uses "dirichlet-lfunction-nonvanishing-line"}[]. The non-quadratic and non-zero imaginary part cases are handled by the $`3`-$`4`-$`1` positivity bound ({uses "dirichlet-lfunction-euler-product"}[]). The remaining quadratic case $`\chi^2 = 1`, $`t = 0` is the deeper assertion proved via the entire-function $`F = \zeta \cdot L(\chi, \cdot)` with positive coefficients and a trivial zero of $`\zeta` at $`s = -2`.
:::

## Bombieri–Vinogradov theorem (lean-bombieri-vinogradov)

:::theorem "bombieri-vinogradov"
*(Bombieri–Vinogradov theorem.)* For any fixed $`A \ge 0` there exists an implied constant $`C_A` such that, uniformly over $`x \ge 2` and $`1 \le Q \le x^{1/2}/(\log x)^{A+3}`,
$$`\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^\times} \left|\psi(y; q, a) - \frac{y}{\varphi(q)}\right| \;\le\; \frac{C_A \, x}{(\log x)^A},`
where $`\psi(y;q,a) = \sum_{n \le y,\, n \equiv a \pmod{q}} \Lambda(n)` ({uses "von-mangoldt"}[]) and $`\varphi(q)` is Euler's totient function. This shows that primes are equidistributed in arithmetic progressions ({uses "dirichlets-theorem"}[]) on average over moduli up to $`x^{1/2-\varepsilon}`, with the same quality of error term as the Generalised Riemann Hypothesis would give individually.
Formalised in [`lean-bombieri-vinogradov`](https://github.com/amellendijk/lean-bombieri-vinogradov) (in progress; the top-level theorem `bombieri_vinogradov` and the $`\Delta_\Lambda`-intermediate `BV_Delta_Lambda` are stated but carry `sorry`; the Siegel–Walfisz theorem and the large sieve inequality are taken as axioms).
:::

:::proof "bombieri-vinogradov"
The proof follows the Vaughan decomposition: one writes $`\Lambda = \Lambda^\sharp + \Lambda^\flat + \Lambda_{\le U}` for suitable parameters $`U, V` with $`UV \le \sqrt{x}` and $`U, V \ge e^{\sqrt{\log x}}`. The small-primes contribution $`\Lambda_{\le U}` is bounded trivially. The Type I sum $`\Lambda^\sharp` (a smooth truncation of $`\Lambda`) is bounded via Abel summation, using the fact that partial sums of character values are small (an input requiring Siegel–Walfisz). The Type II sum $`\Lambda^\flat` is a Dirichlet convolution bounded via the large sieve inequality: after decomposing into character sums via orthogonality of Dirichlet characters ({uses "dirichlet-character"}[]) and applying the large sieve to bound the sum of squared character sums over all characters of moduli $`q \le Q`, one sums the three contributions to obtain the claimed uniform bound.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib
pull requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing
at the live PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the Mathlib-backed nodes of this
chapter (and, for the modular $`L`-series, the Modular Forms chapter) via `{uses}` edges, and
should be re-pointed to `(lean := …)` once the corresponding PR merges.

:::definition "selberg-sieve" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/20008")
*(The Selberg $`\lambda^2` sieve.)* Let $`\mathcal{A}` be a finite integer sequence to be sifted
by a set of primes, with $`|\mathcal{A}_d|` the number of terms divisible by $`d`, modelled as
$`|\mathcal{A}_d| = (g(d))^{-1} X + R_d` for a multiplicative density $`g` and remainder $`R_d`.
For a real *level* $`z`, the *Selberg sieve* chooses real weights $`(\lambda_d)_{d \le z}` with
$`\lambda_1 = 1`, supported on squarefree $`d \le z` dividing the sifting radical, so as to
minimise the quadratic form bounding the sifted count. The optimal choice gives the upper bound
$$`\#\{\,a \in \mathcal{A} : a \text{ unsifted}\,\} \;\le\; \frac{X}{S(z)} \;+\; \sum_{d_1, d_2 \le z} |\lambda_{d_1}\lambda_{d_2}|\,|R_{[d_1,d_2]}|, \qquad S(z) = \sum_{d \le z} \frac{\mu^2(d)}{g_1(d)},`
where $`g_1` is the multiplicative function attached to $`g` and the main term is governed by
the Möbius function ({uses "moebius"}[]) through the squarefree support.

PR #20008 defines the Selberg weights and proves the fundamental bound and the lower bound on
$`S(z)`. It is the engine behind upper-bound sieve estimates such as the Brun–Titchmarsh
inequality ({bpref "brun-titchmarsh"}[]).
In review — [mathlib PR #20008](https://github.com/leanprover-community/mathlib4/pull/20008).
:::

:::theorem "robin-lagarias-rh" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/37585")
*(Robin's and Lagarias' inequalities equivalent to the Riemann hypothesis.)* Let
$`\sigma(n) = \sum_{d \mid n} d` be the sum-of-divisors function and $`H_n = \sum_{k=1}^n 1/k`
the $`n`-th harmonic number. The Riemann hypothesis for $`\zeta` ({uses "riemann-zeta"}[]) is
equivalent to each of the following elementary inequalities:
$$`\textbf{(Robin)}\quad \sigma(n) \;<\; e^{\gamma}\, n \log\log n \quad (n \ge 5041),`
$$`\textbf{(Lagarias)}\quad \sigma(n) \;\le\; H_n + e^{H_n}\log H_n \quad (n \ge 1),`
with equality in Lagarias' form only at $`n = 1`. Here $`\gamma` is the Euler–Mascheroni
constant.

PR #37585 formalises the *statements* of Robin's and Lagarias' inequalities and their formal
equivalence to the Riemann hypothesis, packaging a celebrated elementary reformulation of RH;
it does not prove RH.
In review — [mathlib PR #37585](https://github.com/leanprover-community/mathlib4/pull/37585).
:::

:::definition "lseries-modular-form" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/31187")
For a modular form $`f` ({uses "modular-form"}[]) with $`q`-expansion
$`f = \sum_{n \ge 0} a_n q^n`, the *$`L`-series of $`f`* is the Dirichlet series
({uses "lseries"}[]) built from its Fourier coefficients,
$$`L(f, s) \;=\; \sum_{n=1}^{\infty} \frac{a_n}{n^{s}},`
convergent in a right half-plane (for $`\operatorname{Re}(s)` large, by the polynomial growth of
the $`a_n`). For a normalised Hecke eigenform the multiplicativity of the coefficients yields an
Euler product $`L(f,s) = \prod_p (1 - a_p p^{-s} + p^{k-1-2s})^{-1}`, and $`L(f,s)` continues to
an entire function with a functional equation relating $`s` and $`k - s`.

PR #31187 defines $`L(f,s)` for a modular form by feeding its $`q`-expansion coefficients into
the existing $`L`-series machinery, the first step toward Hecke $`L`-functions and their
analytic continuation in mathlib.
In review — [mathlib PR #31187](https://github.com/leanprover-community/mathlib4/pull/31187).
:::

