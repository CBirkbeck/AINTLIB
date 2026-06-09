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

