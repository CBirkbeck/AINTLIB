import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.Bertrand

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Analytic Number Theory" =>

This chapter covers the analytic theory of the integers as it is formalised in mathlib: the
Riemann zeta function and its Euler product, special values, and functional equation; Dirichlet
characters and their $`L`-functions, with the $`L`-series machinery, Dirichlet convolution as
multiplication of $`L`-series, and meromorphic continuation; the von Mangoldt function and the
identity $`L(\Lambda, s) = -\zeta'(s)/\zeta(s)`; the non-vanishing of $`L`-functions on the closed
half-plane $`\operatorname{Re}(s) \ge 1`; Chebyshev's bounds; the Selberg upper-bound sieve;
Dirichlet's theorem on primes in arithmetic progressions; and Bertrand's postulate. It then records
the deeper results — the Wiener–Ikehara Tauberian theorem and the Prime Number Theorem, the
non-vanishing of Dirichlet $`L`-functions on the whole line $`\operatorname{Re}(s) = 1`, the
Chebyshev and Mertens asymptotics, the Brun–Titchmarsh inequality, and the Bombieri–Vinogradov
theorem — that live in external Lean projects rather than in mathlib.

Throughout, $`s` denotes a complex variable, $`p` a prime, $`q` a positive modulus, and $`\chi` a
Dirichlet character modulo $`q`. Every mathlib node carries a `(lean := …)` reference naming the
exact declaration, and its proof sketch follows the argument that declaration actually uses, naming
the lemmas the proof invokes. Every external node carries a `Formalised in` provenance line linking
to the exact source declaration at a fixed commit and reporting its true Lean status; the external
projects build against newer mathlib toolchains than the current AINTLIB build, so they carry no
`(lean := …)` reference. All four external repositories are public.

# The Riemann zeta function

:::definition "lseries" (lean := "LSeries")
For a function $`f : \mathbb{N} \to \mathbb{C}`, the *$`L`-series* (Dirichlet series) of $`f` is
$$`L(f, s) = \sum_{n=1}^{\infty} \frac{f(n)}{n^s},`
where the $`n`-th term `LSeries.term f s n` is $`f(n)/n^s` for $`n \ge 1` and $`0` for $`n = 0`. The
series is evaluated wherever it converges absolutely (`LSeriesSummable`); below the abscissa of
absolute convergence mathlib sets its value to $`0`. The Riemann zeta function, the Dirichlet
$`L`-functions, and the $`L`-series of the von Mangoldt function are all instances.
:::

:::definition "riemann-zeta" (lean := "riemannZeta")
The *Riemann zeta function* $`\zeta(s)` is the meromorphic continuation to all of $`\mathbb{C}` of
the Dirichlet series ({uses "lseries"}[])
$$`\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}, \qquad \operatorname{Re}(s) > 1.`
In mathlib it is defined as the even Hurwitz zeta function at shift $`0`, $`\zeta = \texttt{hurwitzZetaEven}\,0`,
which builds the continuation from the integral representation of the completed zeta function. It is
holomorphic away from $`s = 1`, where it has a simple pole, and its value at $`s = 0` is
$`\zeta(0) = -\tfrac12`.
:::

:::definition "completed-zeta" (lean := "completedRiemannZeta")
The *completed Riemann zeta function* $`\Lambda(s)` is
$$`\Lambda(s) = \pi^{-s/2}\,\Gamma\!\left(\tfrac{s}{2}\right)\zeta(s),`
defined in mathlib as the completed even Hurwitz zeta function at shift $`0`, so that
$`\zeta(s) = \Lambda(s)/\Gamma_\mathbb{R}(s)` away from $`s = 0` ({uses "riemann-zeta"}[]). The variant
$`\Lambda_0(s) = \Lambda(s) + \tfrac1s - \tfrac1{s-1}` (`completedRiemannZeta₀`) removes both poles and
is entire; $`\Lambda` itself is holomorphic away from $`s \in \{0, 1\}`, where it has simple poles.
:::

:::theorem "zeta-tsum" (lean := "ArithmeticFunction.LSeries_zeta_eq_riemannZeta")
For $`\operatorname{Re}(s) > 1` the continuation $`\zeta(s)` agrees with the convergent Dirichlet
series: writing $`\mathbf{1}` for the constant arithmetic function $`1`,
$$`L(\mathbf{1}, s) = \sum_{n=1}^{\infty} \frac{1}{n^s} = \zeta(s).`
:::

:::proof "zeta-tsum"
The $`L`-series ({uses "lseries"}[]) of the arithmetic zeta function $`\zeta_{\mathrm{ar}}` (the
constant $`1`, with $`\zeta_{\mathrm{ar}}(0) = 0`) is, term by term, $`\sum_{n \ge 1} n^{-s}`. mathlib
rewrites $`\zeta(s)` in the convergence range as the tsum $`\sum_{n} 1/n^s` via
`zeta_eq_tsum_one_div_nat_cpow` and matches it against the $`L`-series term `LSeries.term` after
discarding the $`n = 0` term, which gives `LSeries_zeta_eq_riemannZeta`. Pushing the coercion of the
constant sequence through then yields the constant-$`1` form `LSeries_one_eq_riemannZeta`.
:::

:::theorem "zeta-euler-product" (lean := "riemannZeta_eulerProduct_tprod")
*(Euler product for $`\zeta`.)* For $`\operatorname{Re}(s) > 1`,
$$`\prod_{p} \frac{1}{1 - p^{-s}} = \zeta(s),`
where the product is taken over all primes $`p` and converges absolutely.
:::

:::proof "zeta-euler-product"
For $`\operatorname{Re}(s) > 1` the map $`n \mapsto n^{-s}` is the completely multiplicative
monoid-with-zero homomorphism `riemannZetaSummandHom`, and it is norm-summable
(`summable_riemannZetaSummand`, comparing with $`\sum n^{-\operatorname{Re}(s)}` via the bound on
$`\|n^{-s}\|`). mathlib first rewrites $`\zeta(s)` as $`\sum_n n^{-s}` (`tsum_riemannZetaSummand`,
which is {uses "zeta-tsum"}[]), and then applies the general Euler product for a completely
multiplicative summable function, `eulerProduct_completely_multiplicative_hasProd`: this is the
analytic incarnation of unique factorisation ({uses "fta-uniqueness"}[]), where each local factor
$`\sum_{k \ge 0} p^{-ks} = (1 - p^{-s})^{-1}` is a convergent geometric series since
$`|p^{-s}| = p^{-\operatorname{Re}(s)} < 1`. The `tprod` form is the `HasProd` statement
`riemannZeta_eulerProduct_hasProd` packaged through `HasProd.tprod_eq`.
:::

:::theorem "zeta-two" (lean := "riemannZeta_two")
*(Basel problem.)* The value of $`\zeta` at $`2` is
$$`\zeta(2) = \sum_{n=1}^{\infty} \frac{1}{n^2} = \frac{\pi^2}{6}.`
:::

:::proof "zeta-two"
mathlib has the real-analytic evaluation `hasSum_zeta_two`: $`\sum_{n \ge 1} 1/n^2 = \pi^2/6`,
obtained from the Fourier expansion of the Bernoulli polynomial $`B_2` (the $`k = 1` case of the
general even-value formula). Casting this `HasSum` into $`\mathbb{C}`, identifying its sum with
$`\zeta(2)` through $`\zeta(2) = \sum_n 1/n^2` ({uses "zeta-tsum"}[]) via `zeta_nat_eq_tsum_of_gt_one`,
and simplifying gives $`\zeta(2) = \pi^2/6`. The general formula `riemannZeta_two_mul_nat` evaluates
$`\zeta(2k) = (-1)^{k+1}\,2^{2k-1}\,\pi^{2k}\,B_{2k}/(2k)!` in terms of the Bernoulli numbers
$`B_{2k}` ({uses "bernoulli-number"}[]).
:::

:::theorem "zeta-residue" (lean := "riemannZeta_residue_one")
The function $`\zeta` has a simple pole at $`s = 1` with residue $`1`:
$$`\lim_{s \to 1} (s - 1)\,\zeta(s) = 1.`
:::

:::proof "zeta-residue"
This is the residue of the even Hurwitz zeta function at shift $`0`, `hurwitzZetaEven_residue_one`,
specialised to $`\zeta = \texttt{hurwitzZetaEven}\,0` ({uses "riemann-zeta"}[]). The Hurwitz residue
is in turn read off from the residue of the completed zeta function ({uses "completed-zeta"}[]) at
$`s = 1` against the $`\Gamma`-factor, which is regular and nonzero there.
:::

:::theorem "zeta-functional-equation" (lean := "completedRiemannZeta_one_sub")
*(Functional equation.)* The completed zeta function ({uses "completed-zeta"}[]) is invariant under
$`s \mapsto 1 - s`:
$$`\Lambda(1 - s) = \Lambda(s).`
Equivalently, away from the non-positive integers and from $`s = 1`,
$$`\zeta(1 - s) = 2\,(2\pi)^{-s}\,\Gamma(s)\,\cos\!\left(\tfrac{\pi s}{2}\right)\zeta(s).`
:::

:::proof "zeta-functional-equation"
The symmetric form $`\Lambda(1-s) = \Lambda(s)` reduces to the functional equation of the completed
even Hurwitz zeta function at shift $`0`, `completedHurwitzZetaEven_one_sub`, after rewriting the
even Hurwitz function at $`0` and the corresponding cosine-zeta function back to $`\Lambda` (the
lemmas `completedHurwitzZetaEven_zero` and `completedCosZeta_zero`). Dividing through by the
$`\Gamma`-factors and unwinding $`\Lambda = \pi^{-s/2}\Gamma(s/2)\zeta` ({uses "completed-zeta"}[])
converts this into the asymmetric form for $`\zeta`, which mathlib records separately as
`riemannZeta_one_sub`.
:::

:::theorem "zeta-trivial-zeros" (lean := "riemannZeta_neg_two_mul_nat_add_one")
*(Trivial zeros.)* For every natural number $`n`,
$$`\zeta(-2(n+1)) = 0.`
Thus $`\zeta` vanishes at the negative even integers $`-2, -4, -6, \dots`
:::

:::proof "zeta-trivial-zeros"
These are the trivial zeros coming from the poles of the $`\Gamma`-factor in the functional equation
({uses "zeta-functional-equation"}[]): in $`\zeta(1-s) = 2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)\zeta(s)`
the cosine vanishes at odd integers, forcing $`\zeta` to vanish at the negative even integers. mathlib
obtains it directly as the corresponding vanishing of the even Hurwitz zeta function at shift $`0`,
`hurwitzZetaEven_neg_two_mul_nat_add_one`.
:::

:::definition "riemann-hypothesis" (lean := "RiemannHypothesis")
The *Riemann Hypothesis* is the assertion that every zero of $`\zeta` ({uses "riemann-zeta"}[]) other
than the trivial zeros ({uses "zeta-trivial-zeros"}[]) and the pole at $`s = 1` lies on the critical
line:
$$`\zeta(s) = 0,\ \ s \neq 1,\ \ s \notin \{-2(n+1) : n \in \mathbb{N}\} \ \Longrightarrow\ \operatorname{Re}(s) = \tfrac12.`
This is recorded in mathlib as a `Prop`; it is not proved.
:::

# Dirichlet characters and L-functions

:::definition "dirichlet-character" (lean := "DirichletCharacter")
A *Dirichlet character modulo $`q`* with values in a commutative monoid-with-zero $`R` is a
multiplicative character of $`\mathbb{Z}/q\mathbb{Z}`, that is, a monoid homomorphism
$`\chi : (\mathbb{Z}/q\mathbb{Z})^\times \to R^\times` extended by $`0` on non-units. In mathlib
`DirichletCharacter R q` is an abbreviation for `MulChar (ZMod q) R`; in the analytic theory one takes
$`R = \mathbb{C}`. Such a $`\chi` is completely multiplicative as a function on $`\mathbb{N}`, with
$`\chi(n) = 0` exactly when $`\gcd(n, q) > 1`.
:::

:::theorem "lseries-convolution" (lean := "LSeries_convolution', ArithmeticFunction.LSeries_mul")
The $`L`-series of a Dirichlet convolution ({uses "dirichlet-convolution"}[]) is the product of the
$`L`-series: if $`L(f, s)` and $`L(g, s)` both converge absolutely at $`s`, then
$$`L(f * g, s) = L(f, s)\, L(g, s).`
:::

:::proof "lseries-convolution"
Multiplying the two absolutely convergent series $`\sum_m f(m)/m^s` and $`\sum_n g(n)/n^s` and
collecting terms by the product $`mn = k` realises the coefficient of $`k^{-s}` as
$`\sum_{mn = k} f(m)g(n) = (f * g)(k)` ({uses "dirichlet-convolution"}[]). mathlib makes this rigorous
through `LSeriesHasSum.convolution`, which fibres the product of the two summable families over the
multiplication map $`(m, n) \mapsto mn` (`Summable.tsum_fiberwise`) and identifies each fibre sum with
the convolution term `term_convolution'`. Absolute convergence of both factors justifies the
rearrangement. The arithmetic-function form `ArithmeticFunction.LSeries_mul` is the special case where
$`f, g` are arithmetic functions and $`*` is their ring multiplication, via `coe_mul`.
:::

:::definition "dirichlet-lfunction" (lean := "DirichletCharacter.LFunction")
For a Dirichlet character $`\chi` modulo $`q` ({uses "dirichlet-character"}[]), the *Dirichlet
$`L`-function* $`L(\chi, s)` is the unique meromorphic function on $`\mathbb{C}` agreeing with the
$`L`-series ({uses "lseries"}[]) $`\sum_{n \ge 1} \chi(n) n^{-s}` wherever the latter converges. In
mathlib it is constructed as a linear combination of Hurwitz zeta functions; it is *not* literally the
$`L`-series, which is set to $`0` for $`\operatorname{Re}(s) \le 1`, but the two agree for
$`\operatorname{Re}(s) > 1` (`LFunction_eq_LSeries`). When $`\chi` is non-trivial $`L(\chi, \cdot)` is
entire; the unique character modulo $`1` gives back the Riemann zeta function, $`L(\chi_1, \cdot) = \zeta`
(`LFunction_modOne_eq`), with its simple pole at $`s = 1`.
:::

:::theorem "dirichlet-lfunction-euler-product" (lean := "DirichletCharacter.LSeries_eulerProduct_tprod")
*(Euler product for $`L(\chi, s)`.)* For $`\operatorname{Re}(s) > 1`,
$$`\prod_{p} \frac{1}{1 - \chi(p)\, p^{-s}} = L(\chi, s),`
where the product converges absolutely.
:::

:::proof "dirichlet-lfunction-euler-product"
The argument mirrors the one for $`\zeta` ({uses "zeta-euler-product"}[]). For $`\chi` modulo $`q` and
$`\operatorname{Re}(s) > 1`, the map $`n \mapsto \chi(n)\,n^{-s}` is the completely multiplicative
homomorphism `dirichletSummandHom` — its complete multiplicativity is exactly that of $`\chi`
({uses "dirichlet-character"}[]) combined with $`n \mapsto n^{-s}` — and it is norm-summable
(`summable_dirichletSummand`, dominated by $`\sum n^{-\operatorname{Re}(s)}` using $`|\chi(n)| \le 1`).
Rewriting the $`L`-series as the tsum of this homomorphism (`tsum_dirichletSummand`) and applying
`eulerProduct_completely_multiplicative_hasProd` gives the `HasProd` statement
`DirichletCharacter.LSeries_eulerProduct_hasProd`, whose local factor is
$`\sum_{k \ge 0} \chi(p)^k p^{-ks} = (1 - \chi(p) p^{-s})^{-1}`; the `tprod` form follows by
`HasProd.tprod_eq`.
:::

:::theorem "dirichlet-lfunction-functional-equation" (lean := "DirichletCharacter.IsPrimitive.completedLFunction_one_sub")
*(Functional equation for $`L(\chi, s)`.)* Let $`\chi` be a primitive Dirichlet character modulo
$`N` ({uses "dirichlet-character"}[]). Then the completed $`L`-function satisfies
$$`\Lambda(\chi, 1 - s) = N^{\,s - 1/2}\,W(\chi)\,\Lambda(\chi^{-1}, s),`
where $`W(\chi)` is the root number (a normalised Gauss sum, {uses "gauss-sum"}[]) of absolute value
$`1`.
:::

:::proof "dirichlet-lfunction-functional-equation"
The completed $`L`-function $`\Lambda(\chi, s)` is assembled from completed Hurwitz/cosine zeta
functions indexed by the residues modulo $`N`. mathlib's `completedLFunction_one_sub` reflects each
summand under $`s \mapsto 1 - s` using the Hurwitz functional equation
`completedHurwitzZetaEven_one_sub` (and its odd counterpart), then reassembles the reflected pieces:
the discrete Fourier transform of $`\chi` over $`\mathbb{Z}/N\mathbb{Z}` collapses to the root number
$`W(\chi)`, which for a *primitive* character is the normalised Gauss sum $`\tau(\chi)/\sqrt{N}` (this
primitivity is exactly the hypothesis `IsPrimitive`). The scaling $`N^{s-1/2}` is the conductor factor
introduced when normalising the archimedean and finite parts.
:::

:::theorem "dirichlet-lfunction-trivial-zeros" (lean := "DirichletCharacter.Even.LFunction_neg_two_mul_nat")
*(Trivial zeros of $`L(\chi, s)`.)* If $`\chi` is an even Dirichlet character modulo $`N`
({uses "dirichlet-character"}[]), then for every positive integer $`n`,
$$`L(\chi, -2n) = 0.`
(For odd $`\chi` the trivial zeros sit instead at the negative odd integers.)
:::

:::proof "dirichlet-lfunction-trivial-zeros"
Like the trivial zeros of $`\zeta` ({uses "zeta-trivial-zeros"}[]), these come from the poles of the
archimedean $`\Gamma`-factor. mathlib derives `Even.LFunction_neg_two_mul_nat` from the boundary case
`Even.LFunction_neg_two_mul_nat_add_one` — the vanishing $`L(\chi, -(2(n+1))) = 0` for even $`\chi`,
which is the corresponding statement `ZMod.LFunction_neg_two_mul_nat_add_one` for the underlying even
function on $`\mathbb{Z}/N\mathbb{Z}` — by clearing the successor index. The parity hypothesis
$`\chi(-1) = 1` selects which arithmetic progression of negative integers carries the zeros.
:::

# The von Mangoldt function

:::definition "von-mangoldt" (lean := "ArithmeticFunction.vonMangoldt")
The *von Mangoldt function* $`\Lambda : \mathbb{N} \to \mathbb{R}` is defined by
$$`\Lambda(n) = \begin{cases} \log p & \text{if } n = p^k \text{ for a prime } p \text{ and } k \ge 1, \\ 0 & \text{otherwise.}\end{cases}`
In mathlib $`\Lambda(n) = \log(\operatorname{minFac} n)` when $`n` is a prime power and $`0` otherwise,
where $`\operatorname{minFac} n` is the smallest prime factor. At a prime $`n = p` the value is
$`\Lambda(p) = \log p`.
:::

:::theorem "von-mangoldt-sum" (lean := "ArithmeticFunction.vonMangoldt_sum")
For every positive integer $`n`,
$$`\sum_{d \mid n} \Lambda(d) = \log n.`
:::

:::proof "von-mangoldt-sum"
mathlib proves this by the multiplicative recursion `recOnPrimeCoprime`. On a prime power $`n = p^k`
the divisors are $`1, p, \dots, p^k`, and $`\sum_{j=0}^{k} \Lambda(p^j) = \sum_{j=1}^{k} \log p =
k \log p = \log(p^k)` (using $`\Lambda(p^j) = \log p` for $`j \ge 1`, `vonMangoldt_apply_pow` and
`vonMangoldt_apply_prime`, and $`\Lambda(1) = 0`). For coprime $`a, b` both factors split: the
divisors of $`ab` supported on prime powers split disjointly between those of $`a` and of $`b`
(`mul_divisors_filter_prime_pow`), and $`\log(ab) = \log a + \log b` matches the sum splitting. This
is the additive shadow of unique factorisation ({uses "fta-existence"}[]).
:::

:::theorem "von-mangoldt-zeta-identity" (lean := "ArithmeticFunction.vonMangoldt_mul_zeta")
The von Mangoldt function is the Dirichlet convolution of $`\Lambda` with the constant function: as
arithmetic functions,
$$`\Lambda * \zeta_{\mathrm{ar}} = \log,`
where $`\zeta_{\mathrm{ar}}` is the arithmetic zeta function (constant $`1` on $`\mathbb{N}_{\ge 1}`)
and $`\log` is the arithmetic function $`n \mapsto \log n`. Dually $`\Lambda = \mu * \log`, i.e.
$`\Lambda(n) = \sum_{d \mid n} \mu(n/d) \log d`.
:::

:::proof "von-mangoldt-zeta-identity"
Convolution with the constant $`\zeta_{\mathrm{ar}}` is summation over divisors: $`(\Lambda *
\zeta_{\mathrm{ar}})(n) = \sum_{d \mid n} \Lambda(d)` (`coe_mul_zeta_apply`), which equals $`\log n`
by the divisor-sum identity ({uses "von-mangoldt-sum"}[]); this is mathlib's one-line
`vonMangoldt_mul_zeta`. Convolving instead with the Möbius function ({uses "moebius"}[]), the
Dirichlet inverse of $`\zeta_{\mathrm{ar}}`, inverts the relation: `log_mul_moebius_eq_vonMangoldt`
gives $`\log * \mu = \Lambda`, i.e. $`\Lambda(n) = \sum_{d \mid n} \mu(n/d)\log d`, the Möbius
inversion of the previous identity ({uses "dirichlet-convolution"}[]).
:::

:::theorem "von-mangoldt-lseries" (lean := "ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div")
For $`\operatorname{Re}(s) > 1`, the $`L`-series ({uses "lseries"}[]) of the von Mangoldt function is
the negative logarithmic derivative of the Riemann zeta function:
$$`L(\Lambda, s) = \sum_{n=1}^{\infty} \frac{\Lambda(n)}{n^s} = -\frac{\zeta'(s)}{\zeta(s)}.`
:::

:::proof "von-mangoldt-lseries"
Taking $`-\zeta'/\zeta` and using the Euler product $`\zeta(s) = \prod_p (1 - p^{-s})^{-1}`
({uses "zeta-euler-product"}[]), logarithmic differentiation reproduces $`\sum_p \sum_{k \ge 1}
(\log p)\,p^{-ks} = \sum_n \Lambda(n) n^{-s}`. mathlib carries this out at the level of $`L`-series.
The twisted identity `LSeries_twist_vonMangoldt_eq` gives $`L(\chi \cdot \Lambda, s) = -\frac{d}{ds}
L(\chi, s)/L(\chi, s)` for any Dirichlet character $`\chi`, proved by writing $`\chi \cdot \Lambda` as
the convolution that recovers $`-\,\mathrm{d}/\mathrm{d}s` of the $`L`-series ({uses "lseries-convolution"}[],
`convolution_twist_vonMangoldt`, `LSeries_deriv`) and dividing by the non-vanishing $`L(\chi, s)`.
Specialising to the trivial character modulo $`1` turns $`L(\chi, s)` into $`\zeta(s)` (via
`LSeries_one_eq_riemannZeta`, with `LSeries_vonMangoldt_eq` as the intermediate constant-$`1` form),
giving $`L(\Lambda, s) = -\zeta'(s)/\zeta(s)`.
:::

# Non-vanishing of L-functions on the closed right half-plane

:::theorem "lfunction-nonvanishing" (lean := "DirichletCharacter.LFunction_ne_zero_of_one_le_re")
Let $`\chi` be a Dirichlet character ({uses "dirichlet-character"}[]) and $`s \in \mathbb{C}` with
$`\operatorname{Re}(s) \ge 1`. If $`\chi` is non-trivial or $`s \ne 1`, then
$$`L(\chi, s) \ne 0.`
The only exception is the trivial character at $`s = 1`, where $`L(\chi, s)` has a simple pole rather
than a zero.
:::

:::proof "lfunction-nonvanishing"
mathlib splits on $`\operatorname{Re}(s) = 1` versus $`\operatorname{Re}(s) > 1`. For
$`\operatorname{Re}(s) > 1` the $`L`-function agrees with its $`L`-series (`LFunction_eq_LSeries`,
{uses "dirichlet-lfunction"}[]), which is nonzero because the Euler product
({uses "dirichlet-lfunction-euler-product"}[]) has every factor finite and nonzero
(`LSeries_ne_zero_of_one_lt_re`).

On the line $`\operatorname{Re}(s) = 1` (`LFunction_ne_zero_of_re_eq_one`) the argument is deeper and
itself splits. For a quadratic character $`\chi^2 = 1` at $`s = 1`, a positivity argument applied to
the series $`L(\chi, s)\,\zeta(s)`, whose Dirichlet coefficients are non-negative, shows it cannot
vanish at $`s = 1` without acquiring a pole, contradicting the cancellation of the simple zero against
the simple pole of $`\zeta` (`LFunction_apply_one_ne_zero_of_quadratic`). For all other cases
($`\chi^2 \ne 1` or $`\operatorname{Im}(s) \ne 0`) mathlib uses the classical $`3`–$`4`–$`1` trick: the
product $`L(\chi_0, 1+x)^3\,L(\chi, 1+x+iy)^4\,L(\chi^2, 1+x+2iy)` has modulus $`\ge 1` for
$`x > 0` (`norm_LFunction_product_ge_one`), so a zero at $`1 + iy` would force this product to
$`0` as $`x \downarrow 0`, an asymptotic contradiction (`LFunction_ne_zero_of_not_quadratic_or_ne_one`).
:::

:::theorem "lfunction-one-nonvanishing" (lean := "DirichletCharacter.LFunction_apply_one_ne_zero")
For a non-trivial Dirichlet character $`\chi`, the value $`L(\chi, 1)` is nonzero.
:::

:::proof "lfunction-one-nonvanishing"
This is the special case $`s = 1` of {uses "lfunction-nonvanishing"}[]: since $`\chi \ne 1`, the
hypothesis "$`\chi \ne 1` or $`s \ne 1`" holds with the disjunct $`\chi \ne 1`, and
$`\operatorname{Re}(1) = 1 \ge 1`, so `LFunction_apply_one_ne_zero` is literally
`LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) le_rfl`. It is the analytic input to Dirichlet's
theorem ({bpref "dirichlets-theorem"}[]): were $`L(\chi, 1) = 0` for some non-trivial $`\chi`, the
character-weighted prime sum isolating a residue class would converge rather than diverge.
:::

# Chebyshev's bounds

:::definition "chebyshev-psi-theta" (lean := "Chebyshev.psi, Chebyshev.theta")
The two *Chebyshev functions* are the summatory functions of the von Mangoldt function
({uses "von-mangoldt"}[]) and of $`\log p` over primes:
$$`\psi(x) = \sum_{n \le x} \Lambda(n), \qquad \vartheta(x) = \sum_{p \le x} \log p.`
They differ only by the contributions of higher prime powers; in mathlib these are the scoped
notations `ψ` and `θ` in the `Chebyshev` namespace.
:::

:::theorem "chebyshev-theta-upper" (lean := "Chebyshev.theta_le_log4_mul_x")
*(Chebyshev's upper bound for $`\vartheta`.)* For every $`x \ge 0`,
$$`\vartheta(x) = \sum_{p \le x} \log p \;\le\; (\log 4)\,x.`
:::

:::proof "chebyshev-theta-upper"
mathlib writes $`\vartheta(x) = \log(\#\lfloor x \rfloor)` where $`\#m` is the primorial, the product
of primes up to $`m` (`theta_eq_log_primorial`). The combinatorial bound $`\#m \le 4^m`
(`primorial_le_four_pow`, proved by induction splitting the primes in $`(m/2, m]` off against the
central binomial coefficient $`\binom{m}{\lfloor m/2\rfloor}`) then gives
$`\vartheta(x) \le \log(4^{\lfloor x\rfloor}) = \lfloor x\rfloor \log 4 \le x \log 4`.
:::

:::theorem "chebyshev-psi-upper" (lean := "Chebyshev.psi_le_const_mul_self")
*(Chebyshev's upper bound for $`\psi`.)* For every $`x \ge 0`, the summatory von Mangoldt function
({uses "von-mangoldt"}[]) satisfies
$$`\psi(x) = \sum_{n \le x} \Lambda(n) \;\le\; (\log 4 + 4)\,x.`
A sharper main term, $`\psi(x) \le (\log 4)\,x + 2\sqrt{x}\,\log x`, also holds.
:::

:::proof "chebyshev-psi-upper"
The difference $`\psi(x) - \vartheta(x)`, collecting only the proper prime powers $`p^k` with
$`k \ge 2`, is at most $`2\sqrt{x}\,\log x` (`abs_psi_sub_theta_le_sqrt_mul_log`, since such powers have
$`p \le \sqrt{x}`). Adding this to the bound on $`\vartheta` ({uses "chebyshev-theta-upper"}[]) gives
the sharp form $`\psi(x) \le (\log 4)x + 2\sqrt{x}\log x` (`psi_le`). Coarsening $`2\sqrt{x}\log x \le
4x` via $`\log x \le 2\sqrt{x}` then yields the clean constant $`\psi(x) \le (\log 4 + 4)x`
(`psi_le_const_mul_self`).
:::

# The Selberg sieve

:::definition "selberg-sieve" (lean := "SelbergSieve")
A *Selberg sieve* packages the data needed to bound, from above, the number of elements of a finite
weighted sequence that survive sifting by a set of primes. In mathlib a `SelbergSieve` extends a
`BoundingSieve`: a finite support with non-negative `weights`, a squarefree product of sifting primes
`prodPrimes`, a multiplicative density $`\nu` with $`0 < \nu(p) < 1` on the sifting primes, a total
mass `totalMass`, and a real *level* $`y \ge 1`. The *sifted sum*
$$`S = \sum_{d} \big[\gcd(\texttt{prodPrimes}, d) = 1\big]\,w_d`
({uses "moebius"}[]) counts the weight of the unsifted elements, and the remainders
$`R_d = \big(\sum_{d \mid n} w_n\big) - \nu(d)\,\texttt{totalMass}` measure the failure of the density
model.
:::

:::theorem "selberg-sieve-bound" (lean := "BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius")
*(Fundamental upper-bound-sieve inequality.)* Let $`(\mu^+_d)` be any *upper-Möbius* weight system,
i.e. real numbers with $`\mu^+_1 = 1` such that $`\sum_{d \mid n} \mu^+_d \ge \big[\gcd(P, n) = 1\big]`
for all $`n` (where $`P = \texttt{prodPrimes}`). Then the sifted sum ({uses "selberg-sieve"}[]) is
bounded by a main term plus a remainder term:
$$`S \;\le\; \sum_{d \mid P} \mu^+_d\,\nu(d)\,\texttt{totalMass} \;+\; \sum_{d \mid P} |\mu^+_d|\,|R_d|.`
The Selberg sieve optimises the choice of $`(\mu^+_d)` to minimise the resulting main term.
:::

:::proof "selberg-sieve-bound"
The defining property of an upper-Möbius system is that $`\sum_{d \mid n} \mu^+_d` dominates the
indicator $`[\gcd(P, n) = 1]` (`IsUpperMoebius`). Bounding the sifted sum termwise by this larger
quantity and exchanging the order of summation expresses
$`S \le \sum_{d \mid P} \mu^+_d \sum_{d \mid n} w_n = \sum_{d \mid P} \mu^+_d\,(\nu(d)\,\texttt{totalMass} + R_d)`,
using $`\sum_{d \mid n} w_n = \nu(d)\,\texttt{totalMass} + R_d` (`multSum_eq_main_err`). Splitting off
the density part as the main term and bounding the rest by $`\sum_{d \mid P} |\mu^+_d|\,|R_d|` gives the
inequality; this is mathlib's `siftedSum_le_mainSum_errSum_of_upperMoebius`, built on the basic
`siftedSum_le_sum_of_upperMoebius`. It is the engine behind upper-bound sieve estimates such as the
Brun–Titchmarsh inequality ({bpref "brun-titchmarsh"}[]).
:::

# Dirichlet's theorem on primes in arithmetic progressions

:::theorem "dirichlets-theorem" (lean := "Nat.infinite_setOf_prime_and_eq_mod")
*(Dirichlet's theorem.)* Let $`q` be a positive integer and $`a \in \mathbb{Z}/q\mathbb{Z}` a unit.
Then the set of primes $`p` with $`p \equiv a \pmod{q}` is infinite:
$$`\#\{\, p \text{ prime} : (p \bmod q) = a \,\} = \infty.`
In particular every residue class coprime to the modulus contains infinitely many primes.
:::

:::proof "dirichlets-theorem"
mathlib proves the contrapositive (`by_contra`): if the prime set were finite, then the sum of
$`\Lambda(n)/n` over that residue class restricted to primes would be summable; but the deep input
`not_summable_residueClass_prime_div` shows this sum *diverges*. That divergence is assembled from the
analytic theory: the indicator of the residue class is written via orthogonality of Dirichlet
characters ({uses "dirichlet-character"}[]) as $`\varphi(q)^{-1}\sum_{\chi}\overline{\chi(a)}\,\chi(n)`,
so $`\sum_{n \equiv a} \Lambda(n) n^{-s}` becomes a character-weighted combination of the logarithmic
derivatives $`-L'(\chi, s)/L(\chi, s)` ({uses "von-mangoldt-lseries"}[]). An auxiliary function
subtracts the pole term $`\varphi(q)^{-1}/(s-1)` coming from the trivial character and is shown to
extend *continuously* to the closed half-plane $`\operatorname{Re}(s) \ge 1`
(`continuousOn_LFunctionResidueClassAux`); this continuity rests precisely on the non-vanishing of the
$`L`-functions there ({uses "lfunction-nonvanishing"}[], {uses "lfunction-one-nonvanishing"}[]), since
a zero would create a logarithmic pole. The non-prime prime-power contribution converges
(`summable_residueClass_non_primes_div`), so the prime part must carry the divergence, contradicting
finiteness.
:::

:::corollary "dirichlets-theorem-gt" (lean := "Nat.forall_exists_prime_gt_and_modEq")
Let $`q` be a positive integer, $`a` a natural number coprime to $`q`, and $`n` any natural number.
Then there exists a prime $`p > n` with $`p \equiv a \pmod{q}`.
:::

:::proof "dirichlets-theorem-gt"
mathlib transfers the coprimality of $`a` to the unit hypothesis on $`a \bmod q`
(`ZMod.coe_int_isUnit_iff_isCoprime`) and applies Dirichlet's theorem ({uses "dirichlets-theorem"}[]).
An infinite set of naturals is unbounded above (`Set.infinite_iff_exists_gt`), so for any threshold
$`n` it contains an element exceeding $`n`; this is the asserted prime $`p > n` with $`p \equiv a
\pmod q` (the chain `forall_exists_prime_gt_and_eq_mod` to `forall_exists_prime_gt_and_zmodEq` to the
natural-number `[MOD q]` form `forall_exists_prime_gt_and_modEq`).
:::

# Bertrand's postulate

:::theorem "bertrand" (lean := "Nat.exists_prime_lt_and_le_two_mul")
*(Bertrand's postulate.)* For every positive integer $`n`, there exists a prime $`p` with
$`n < p \le 2n`.
:::

:::proof "bertrand"
Bertrand's postulate sharpens the infinitude of primes ({uses "infinitude-of-primes"}[]) to a prime
in the dyadic window $`(n, 2n]`. mathlib follows the Erdős proof from *Proofs from THE BOOK* and
splits on the size of $`n`. For $`n \ge 512` (`exists_prime_lt_and_le_two_mul_eventually`), suppose no
prime lies in $`(n, 2n]`. Then the central binomial coefficient $`\binom{2n}{n}` has all its prime
factors $`\le n`, and a count of prime-power contributions via the Legendre valuation formula
({uses "padic-val-nat"}[]) yields the sub-exponential bound $`\binom{2n}{n} \le (2n)^{\sqrt{2n}}\,4^{2n/3}`
(`centralBinom_le_of_no_bertrand_prime`). This contradicts the exponential lower bound
$`4^n < n\,\binom{2n}{n}` (`Nat.four_pow_lt_mul_centralBinom`) once $`n \ge 512`, which is the
arithmetic content of `bertrand_main_inequality`. For $`n < 521` the postulate is verified directly
from the explicit descending chain of primes $`317, 163, 83, 43, 23, 13, 7, 5, 3, 2` (each less than
twice the next), which covers every remaining window (`exists_prime_lt_and_le_two_mul_succ`).
:::

# The Wiener–Ikehara theorem and the Prime Number Theorem

The `EulerProducts` project of Michael Stoll develops Euler products in general and derives the Prime
Number Theorem and Dirichlet's theorem from a clean statement of the Wiener–Ikehara Tauberian theorem,
which is taken as a hypothesis (the Tauberian theorem itself is proved analytically in
PrimeNumberTheoremAnd). The nodes below are *informal*; each links to its exact source declaration at
commit `7376f1a` and connects into the dependency graph through the mathlib-backed nodes above.

:::theorem "euler-product-general"
*(Euler product for a multiplicative $`L`-series.)* Let $`f : \mathbb{N} \to \mathbb{C}` be weakly
multiplicative with $`f(1) = 1`, and suppose the $`L`-series $`L(f, s) = \sum_{n \ge 1} f(n) n^{-s}`
({uses "lseries"}[]) converges absolutely at $`s`. Then
$$`L(f, s) = \prod_{p} \sum_{e \ge 0} f(p^e)\, p^{-es},`
the product of local factors over primes $`p`. When $`f` is completely multiplicative the local factor
collapses to $`(1 - f(p)\,p^{-s})^{-1}`.
Formalised in [`EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts): [`LSeries.eulerProduct_of_multiplicative`](https://github.com/MichaelStollBayreuth/EulerProducts/blob/7376f1ab99e936407e76eb1dd13e3f3f482d3acc/EulerProducts/EulerProduct.lean#L50) and [`LSeries.eulerProduct_of_completelyMultiplicative`](https://github.com/MichaelStollBayreuth/EulerProducts/blob/7376f1ab99e936407e76eb1dd13e3f3f482d3acc/EulerProducts/EulerProduct.lean#L56) — sorry-free.
:::

:::proof "euler-product-general"
This is the general analytic incarnation of unique factorisation ({uses "fta-uniqueness"}[]): expanding
$`\prod_p \sum_{e \ge 0} f(p^e) p^{-es}` and grouping by $`n = \prod_p p^{e_p}` reproduces each Dirichlet
coefficient $`f(n) n^{-s}` exactly once. The repository builds the term-level multiplicativity lemmas
(`term_multiplicative`, `term_completelyMultiplicative`, `term_at_one`) and feeds them to the underlying
`eulerProduct` engine, with absolute convergence of $`L(f, s)` (`LSeriesSummable`) justifying the
rearrangement of the double sum. The Euler products for $`\zeta` ({bpref "zeta-euler-product"}[]) and
for Dirichlet $`L`-functions ({bpref "dirichlet-lfunction-euler-product"}[]) are the
completely-multiplicative special cases, now part of mathlib.
:::

:::theorem "wiener-ikehara"
*(Wiener–Ikehara Tauberian theorem, as a hypothesis.)* Let $`f : \mathbb{N} \to \mathbb{R}` be a
non-negative arithmetic function and $`A \in \mathbb{R}`. Suppose there is a function $`F` that is
continuous on $`\{\operatorname{Re}(s) \ge 1\}` and agrees on $`\{\operatorname{Re}(s) > 1\}` with
$$`L(f, s) - \frac{A}{s - 1}.`
Then the partial sums satisfy
$$`\frac{1}{N}\sum_{n < N} f(n) \;\longrightarrow\; A \qquad (N \to \infty).`
This statement is packaged in `EulerProducts` as a `Prop`-valued hypothesis `WienerIkeharaTheorem`,
used as input to the Prime Number Theorem below; the Tauberian theorem itself is proved in
PrimeNumberTheoremAnd ({bpref "prime-number-theorem"}[]).
Formalised in [`EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts): [`WienerIkeharaTheorem`](https://github.com/MichaelStollBayreuth/EulerProducts/blob/7376f1ab99e936407e76eb1dd13e3f3f482d3acc/EulerProducts/PNT.lean#L15) — statement only (a hypothesis, discharged elsewhere).
:::

:::proof "wiener-ikehara"
The classical proof is a Fourier-analytic argument: one writes the partial sum as an inverse
Mellin-type integral along $`\operatorname{Re}(s) = 1 + \varepsilon`, and the hypothesis that
$`F = L(f, \cdot) - A/(s-1)` extends *continuously* (not merely analytically) to the closed half-plane
$`\operatorname{Re}(s) \ge 1` lets a smoothing and the Riemann–Lebesgue lemma kill the oscillatory part,
leaving the residue $`A` from the simple pole at $`s = 1` ({uses "riemann-zeta"}[]). In `EulerProducts`
this is not reproved; it is named as the hypothesis `WienerIkeharaTheorem` and consumed by the PNT and
Dirichlet derivations.
:::

:::theorem "pnt-von-mangoldt-conditional"
*(Prime Number Theorem via Wiener–Ikehara.)* Assume the Wiener–Ikehara theorem
({uses "wiener-ikehara"}[]). Then
$$`\frac{1}{N}\sum_{n < N} \Lambda(n) \;\longrightarrow\; 1 \qquad (N \to \infty),`
i.e. $`\psi(N) \sim N` for the Chebyshev function ({uses "chebyshev-psi-theta"}[]). More generally, for
a unit $`a \in (\mathbb{Z}/q\mathbb{Z})^\times`, the von Mangoldt sum over the residue class
$`n \equiv a \pmod q` is asymptotic to $`\varphi(q)^{-1} N`.
Formalised in [`EulerProducts`](https://github.com/MichaelStollBayreuth/EulerProducts): [`PNT_vonMangoldt`](https://github.com/MichaelStollBayreuth/EulerProducts/blob/7376f1ab99e936407e76eb1dd13e3f3f482d3acc/EulerProducts/PNT.lean#L48) and [`Dirichlet_vonMangoldt`](https://github.com/MichaelStollBayreuth/EulerProducts/blob/7376f1ab99e936407e76eb1dd13e3f3f482d3acc/EulerProducts/PNT.lean#L30) — sorry-free (conditional on `WienerIkeharaTheorem`).
:::

:::proof "pnt-von-mangoldt-conditional"
One applies the Wiener–Ikehara hypothesis ({uses "wiener-ikehara"}[]) to the indicator-weighted von
Mangoldt function on a residue class, with $`A = \varphi(q)^{-1}`. The role of the analytic input is
the auxiliary function `vonMangoldt.LFunctionResidueClassAux`, which equals $`L(f, s) - A/(s-1)` on
$`\operatorname{Re}(s) > 1` (`eqOn_LFunctionResidueClassAux`) and is continuous on
$`\operatorname{Re}(s) \ge 1` (`continuousOn_LFunctionResidueClassAux`) — the very continuity that the
non-vanishing of $`\zeta` and the Dirichlet $`L`-functions on that line provides
({uses "lfunction-nonvanishing"}[]). The full PNT $`\psi(N) \sim N` is `PNT_vonMangoldt`, the special
case $`q = 1`, $`a = 1` of the residue-class statement `Dirichlet_vonMangoldt`, where the von Mangoldt
$`L`-series is $`-\zeta'(s)/\zeta(s)` ({uses "von-mangoldt-lseries"}[]).
:::

# Non-vanishing of Dirichlet L-functions on the line Re(s) = 1

The `DirichletNonvanishing` project (Birkbeck) gives a self-contained, sorry-free proof that Dirichlet
$`L`-functions do not vanish anywhere on the line $`\operatorname{Re}(s) = 1` (other than the pole of
$`\zeta`). The nodes below are *informal*; each links to its exact source declaration at commit
`fb3e6ac` and connects into the graph through the mathlib non-vanishing nodes above.

:::theorem "dirichlet-lfunction-nonvanishing-line"
*(Non-vanishing on $`\operatorname{Re}(s) = 1`.)* Let $`\chi` be a Dirichlet character modulo $`N`
({uses "dirichlet-character"}[]) and $`t \in \mathbb{R}`. If $`\chi \ne 1` or $`t \ne 0`, then
$$`L(\chi,\, 1 + it) \ne 0.`
In particular, for every non-trivial $`\chi` the Dirichlet $`L`-function ({uses "dirichlet-lfunction"}[])
has no zero on the entire line $`\operatorname{Re}(s) = 1`.
Formalised in [`DirichletNonvanishing`](https://github.com/CBirkbeck/DirichletNonvanishing): [`ourMainTheorem`](https://github.com/CBirkbeck/DirichletNonvanishing/blob/fb3e6ac7ca97c2dbb5ee796c87d667af360e41af/Project/MainTheorem.lean#L18) — sorry-free.
:::

:::proof "dirichlet-lfunction-nonvanishing-line"
The proof case-splits on whether $`(\chi^2 = 1 \wedge t = 0)`. The generic case $`\chi^2 \ne 1` or
$`t \ne 0` (`mainTheorem_general`) is the $`3`–$`4`–$`1` positivity bound: the product
$`|L(1, 1+x)^3\,L(\chi, 1+x+it)^4\,L(\chi^2, 1+x+2it)|` is bounded below by $`1` for $`x > 0`
(`norm_LFunction_product_ge_one`), so a zero at $`1 + it` would drive it to $`0` as $`x \downarrow 0`,
contradicting the asymptotics of the three factors (`LFunction_isBigO_…_horizontal`).

The hard quadratic case $`\chi^2 = 1`, $`t = 0` (`mainTheorem_quadratic`) supposes $`L(\chi, 1) = 0`
and derives a contradiction through a `BadChar` structure. One forms the entire function $`F(s) =
\zeta(s)\,L(\chi, s)` (the assumed simple zero of $`L(\chi, \cdot)` at $`s = 1` cancelling the pole of
$`\zeta`, `F_differentiable`). For $`\operatorname{Re}(s) > 1`, $`F` is the $`L`-series of the
non-negative convolution $`\zeta_{\mathrm{ar}} * \chi` (`F_eq_LSeries`), so a coefficient-positivity
lemma forces $`F` to be positive on the reals to the left of its convergence region; but the trivial
zero of $`\zeta` gives $`F(-2) = \zeta(-2) L(\chi, -2) = 0` (`F_neg_two`, using
{uses "lfunction-one-nonvanishing"}[]), and `BadChar.elim` closes the contradiction.
:::

# The Prime Number Theorem with error term, and Chebyshev and Mertens asymptotics

The `PrimeNumberTheoremAnd` project (Kontorovich et al.) is a large formalisation of analytic prime
number theory: the Wiener–Ikehara Tauberian theorem, the Prime Number Theorem in both a Tauberian
($`\psi \sim x`) and a contour-integral form (with a power-of-log error), the Chebyshev and Mertens
asymptotics, and the Brun–Titchmarsh inequality. The nodes below are *informal*; each links to its
exact source declaration at commit `9824b74`.

:::theorem "prime-number-theorem"
*(Prime Number Theorem.)* As $`N \to \infty`,
$$`\psi(N) = \sum_{n < N} \Lambda(n) \;\sim\; N,`
where $`\psi` is the Chebyshev function ({uses "chebyshev-psi-theta"}[]). The project also establishes
a quantitative form with a power-of-log saving: there is an explicit $`c > 0` with
$$`\psi(x) = x + O\!\left(x\,\exp\!\bigl(-c\,(\log x)^{1/10}\bigr)\right).`
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): [`WeakPNT`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/Wiener.lean#L2446) (Tauberian form, sorry-free) and [`MediumPNT`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/MediumPNT.lean#L3710) (error-term form, sorry-free).
:::

:::proof "prime-number-theorem"
Two routes are formalised. The Wiener–Ikehara route (`WeakPNT`) proves the Tauberian theorem
({uses "wiener-ikehara"}[]) outright by a Fourier-analytic argument and applies it to $`\Lambda`, whose
$`L`-series is $`-\zeta'/\zeta` ({uses "von-mangoldt-lseries"}[]) and whose hypotheses are supplied by
the non-vanishing of $`\zeta` on $`\operatorname{Re}(s) = 1` ({uses "lfunction-nonvanishing"}[]). The
contour-integral route (`MediumPNT`) gives the sharper error: it inverts the Mellin transform of a
smooth truncation of $`\psi` over a rectangle, uses bounds on $`\zeta'(s)/\zeta(s)` in a zero-free
region of the form $`\operatorname{Re}(s) \ge 1 - c/\log(|\operatorname{Im}(s)| + 2)`, and applies a
Borel–Carathéodory estimate to control the logarithmic derivative.
:::

:::theorem "chebyshev-asymptotic"
*(Chebyshev asymptotic.)* The first Chebyshev function ({uses "chebyshev-psi-theta"}[]) is asymptotic
to the identity:
$$`\vartheta(x) = \sum_{p \le x} \log p \;\sim\; x \qquad (x \to \infty).`
Equivalently $`\pi(x) \sim x/\log x`. This strengthens the elementary two-sided bounds
({bpref "chebyshev-theta-upper"}[]) to a genuine asymptotic.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): [`chebyshev_asymptotic`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/Consequences.lean#L177) — sorry-free.
:::

:::proof "chebyshev-asymptotic"
This is a consequence of the Prime Number Theorem ({uses "prime-number-theorem"}[]). Since $`\psi` and
$`\vartheta` differ only by the higher prime powers, $`|\psi(x) - \vartheta(x)| \le 2\sqrt{x}\log x`
(`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`, the same mathlib bound used for
{bpref "chebyshev-psi-upper"}[]), so $`\psi(x) \sim x` transfers to $`\vartheta(x) \sim x`. The
prime-counting form $`\pi(x) \sim x/\log x` then follows by partial summation, integrating
$`\vartheta` against $`1/(t\log^2 t)` (the identity `Chebyshev.primeCounting_eq_theta_div_log_add_integral`).
:::

:::theorem "mertens-first"
*(Mertens' first theorem.)* As $`x \to \infty`,
$$`\sum_{n \le x} \frac{\Lambda(n)}{n} = \log x + O(1),`
with the explicit two-sided error $`-2 \le \big(\sum_{n \le x}\Lambda(n)/n\big) - \log x \le \log 4 + 4`
for $`x \ge 1`. Equivalently $`\sum_{p \le x} (\log p)/p = \log x + O(1)`.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): the identity [`sum_mangoldt_div_eq`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/IEANTN/Mertens.lean#L335) with the bounds `E₁Λ.ge`/`E₁Λ.le` — sorry-free.
:::

:::proof "mertens-first"
Summing the divisor identity $`\sum_{d \mid n}\Lambda(d) = \log n` ({uses "von-mangoldt-zeta-identity"}[])
over $`n \le x` gives $`\sum_{n \le x}\log n = \sum_{d \le x}\Lambda(d)\lfloor x/d\rfloor` (the
hyperbola/Dirichlet rearrangement `sum_log_eq_sum_mangoldt`). Comparing $`\sum_{n\le x}\log n =
\log\lfloor x\rfloor!` with $`x\log x - x` (Stirling-type bounds `sum_log_ge`/`sum_log_le`), and
replacing $`\lfloor x/d\rfloor` by $`x/d` up to a bounded error, isolates
$`\sum_{d \le x}\Lambda(d)/d = \log x + E_{1,\Lambda}(x)` with $`E_{1,\Lambda}` controlled between
$`-2` and $`\log 4 + 4`; the upper bound uses the mathlib Chebyshev estimate $`\psi(x) \le (\log 4 + 4)x`
({bpref "chebyshev-psi-upper"}[]).
:::

:::theorem "mertens-second"
*(Mertens' second theorem.)* As $`x \to \infty`,
$$`\sum_{p \le x} \frac{1}{p} = \log \log x + M + O\!\left(\frac{1}{\log x}\right),`
where $`M = \gamma + \sum_p \bigl(\log(1 - p^{-1}) + p^{-1}\bigr)` is the Meissel–Mertens constant and
$`\gamma` is the Euler–Mascheroni constant. In particular $`\sum_{p \le x} 1/p \sim \log\log x`.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): [`sum_prime_div_eq`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/IEANTN/Mertens.lean#L1104) with error bound [`E₂p.bound`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/IEANTN/Mertens.lean#L1192) — in progress (the identification of the file's Euler–Mascheroni constant with mathlib's `eulerMascheroniConstant`, `γ.eq_eulerMascheroni`, still carries `sorry`).
:::

:::proof "mertens-second"
From Mertens' first theorem ({uses "mertens-first"}[]) and partial summation, the weighted sum
$`\sum_{n \le x}\Lambda(n)/(n\log n)` is $`\log\log x + \gamma + O(1/\log x)`. The discrepancy between
this von Mangoldt sum and the prime sum $`\sum_{p \le x} 1/p` is the convergent double series over
proper prime powers $`\sum_{k \ge 2}\sum_{p^k \le x} 1/(k\,p^k)`, whose limit is absorbed into the
correction constant; the project tracks the remainder $`E_{2,p}(x)` and bounds it by $`O(1/\log x)`
(`E₂p.bound`). Identifying the limiting constant as the Meissel–Mertens constant $`M = \gamma +
\sum_p(\log(1-p^{-1}) + p^{-1})` is `M.eq`. The third theorem $`\prod_{p \le x}(1 - 1/p) \sim
e^{-\gamma}/\log x` is the companion `E₃.bound''`.
:::

# The Brun–Titchmarsh inequality

:::theorem "brun-titchmarsh"
*(Brun–Titchmarsh inequality.)* For real $`x`, $`y > 0` and a sieving level $`z > 1`, the number of
primes in the interval $`(x, x + y]` satisfies
$$`\pi(x + y) - \pi(x) \;\le\; \frac{2y}{\log z} + 6z\,(1 + \log z)^3.`
Taking $`z = \sqrt{y}` gives $`\pi(x+y) - \pi(x) \ll y/\log y`.
Formalised in [`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): [`primesBetween_le`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/9824b746d3cc4e70aadac92ca1b4c8db31432955/PrimeNumberTheoremAnd/BrunTitchmarsh.lean#L248) — sorry-free.
:::

:::proof "brun-titchmarsh"
One sifts the interval $`(x, x+y]` by the primes up to $`z` using a Selberg sieve
({uses "selberg-sieve"}[]). The number of primes in the interval exceeding $`z` is at most the sifted
sum of the interval plus the $`O(z)` small primes (`primesBetween_le_siftedSum_add`). The Selberg
fundamental bound ({uses "selberg-sieve-bound"}[]) controls the sifted sum by $`y/S(z)` plus a
remainder, and the lower bound $`S(z) \ge \tfrac12\log z` on the Selberg bounding sum
(`boudingSum_ge`, from the primorial structure of the sieve support) turns this into the main term
$`2y/\log z`; the remainder is bounded by $`5z(1 + \log z)^3` via divisor-sum estimates
(`primeSieve_rem_sum_le`), and assembling the pieces (`siftedSum_le`, `primesBetween_le`) gives the
stated inequality.
:::

# The Bombieri–Vinogradov theorem

The `lean-bombieri-vinogradov` project (Mellendijk) formalises the Bombieri–Vinogradov theorem on the
distribution of primes in arithmetic progressions on average, following Koukoulopoulos. The headline
theorem and its $`\Delta_\Lambda`-intermediate are stated and the proof skeleton (Vaughan
decomposition) is in place but still carries `sorry`; the Siegel–Walfisz theorem and the large sieve
inequality are taken as axioms. The node below is *informal*, linking to its source at commit
`08696dd`.

:::theorem "bombieri-vinogradov"
*(Bombieri–Vinogradov theorem.)* For each fixed $`A \ge 0` there is an implied constant $`C_A` such
that, uniformly for $`x \ge 2` and $`1 \le Q \le \sqrt{x}/(\log x)^{A+3}`,
$$`\sum_{q \le Q} \max_{y \le x} \max_{a \in (\mathbb{Z}/q\mathbb{Z})^\times} \left|\psi(y; q, a) - \frac{y}{\varphi(q)}\right| \;\le\; \frac{C_A\, x}{(\log x)^A},`
where $`\psi(y; q, a) = \sum_{n \le y,\ n \equiv a \,(q)} \Lambda(n)` ({uses "von-mangoldt"}[]). Primes
are thus equidistributed in progressions ({uses "dirichlets-theorem"}[]) on average over moduli up to
$`x^{1/2 - \varepsilon}`, with the quality the Generalised Riemann Hypothesis would give individually.
Formalised in [`lean-bombieri-vinogradov`](https://github.com/amellendijk/lean-bombieri-vinogradov): [`bombieri_vinogradov`](https://github.com/amellendijk/lean-bombieri-vinogradov/blob/08696dd98fc2abd6f3ab61e66f859021be2f46c7/BV/MainResults.lean#L55) and [`BV_Delta_Lambda`](https://github.com/amellendijk/lean-bombieri-vinogradov/blob/08696dd98fc2abd6f3ab61e66f859021be2f46c7/BV/MainResults.lean#L35) — in progress (both top-level theorems carry `sorry`; [`siegel_walfisz`](https://github.com/amellendijk/lean-bombieri-vinogradov/blob/08696dd98fc2abd6f3ab61e66f859021be2f46c7/BV/Axioms.lean#L21) and [`large_sieve`](https://github.com/amellendijk/lean-bombieri-vinogradov/blob/08696dd98fc2abd6f3ab61e66f859021be2f46c7/BV/Axioms.lean#L36) are taken as axioms).
:::

:::proof "bombieri-vinogradov"
The proof rests on the Vaughan decomposition $`\Lambda = \Lambda^\sharp + \Lambda^\flat +
\Lambda_{\le U}` for parameters $`U, V` with $`UV \le \sqrt{x}` and $`U, V \ge e^{\sqrt{\log x}}`
(the `ProofData` typeclass). The small-primes part $`\Lambda_{\le U}` is bounded trivially. The Type I
sum $`\Lambda^\sharp` is handled by Abel summation using that partial sums of character values are
small — the input supplied by the Siegel–Walfisz axiom. The Type II sum $`\Lambda^\flat` is a Dirichlet
convolution: decomposing it into character sums by orthogonality of Dirichlet characters
({uses "dirichlet-character"}[]) and bounding the sum of squared character sums over all characters of
moduli $`q \le Q` by the large sieve axiom controls it. Summing the three contributions gives the
intermediate `BV_Delta_Lambda`, and absorbing the prime-power error terms yields the headline
`bombieri_vinogradov`.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib pull
requests (the `t-number-theory` queue). Each carries a `pr_url` pointing at the live PR and **no**
`(lean := …)` reference: the declarations are not yet in mathlib v4.30.0-rc2. They connect into the
dependency graph through the mathlib-backed nodes of this chapter (and, for the modular $`L`-series,
the Modular Forms chapter), and should be re-pointed to `(lean := …)` once the corresponding PR merges.

:::theorem "robin-lagarias-rh" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/37585")
*(Robin's and Lagarias' inequalities equivalent to the Riemann hypothesis.)* Let
$`\sigma(n) = \sum_{d \mid n} d` be the sum-of-divisors function and $`H_n = \sum_{k=1}^n 1/k` the
$`n`-th harmonic number. The Riemann hypothesis for $`\zeta` ({uses "riemann-hypothesis"}[]) is
equivalent to each of the following elementary inequalities:
$$`\textbf{(Robin)}\quad \sigma(n) \;<\; e^{\gamma}\, n \log\log n \quad (n \ge 5041),`
$$`\textbf{(Lagarias)}\quad \sigma(n) \;\le\; H_n + e^{H_n}\log H_n \quad (n \ge 1),`
with equality in Lagarias' form only at $`n = 1`. Here $`\gamma` is the Euler–Mascheroni constant.

PR #37585 formalises the *statements* of Robin's and Lagarias' inequalities and their formal
equivalence to the Riemann hypothesis, packaging a celebrated elementary reformulation of RH; it does
not prove RH.
In review — [mathlib PR #37585](https://github.com/leanprover-community/mathlib4/pull/37585).
:::

:::definition "lseries-modular-form" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/31187")
For a modular form $`f` ({uses "modular-form"}[]) with $`q`-expansion $`f = \sum_{n \ge 0} a_n q^n`, the
*$`L`-series of $`f`* is the Dirichlet series ({uses "lseries"}[]) built from its Fourier coefficients,
$$`L(f, s) \;=\; \sum_{n=1}^{\infty} \frac{a_n}{n^{s}},`
convergent in a right half-plane by the polynomial growth of the $`a_n`. For a normalised Hecke
eigenform the multiplicativity of the coefficients yields an Euler product $`L(f, s) = \prod_p
(1 - a_p p^{-s} + p^{k-1-2s})^{-1}`, and $`L(f, s)` continues to an entire function with a functional
equation relating $`s` and $`k - s`.

PR #31187 defines $`L(f, s)` for a modular form by feeding its $`q`-expansion coefficients into the
existing $`L`-series machinery ({uses "lseries"}[]), the first step toward Hecke $`L`-functions and
their analytic continuation in mathlib.
In review — [mathlib PR #31187](https://github.com/leanprover-community/mathlib4/pull/31187).
:::
