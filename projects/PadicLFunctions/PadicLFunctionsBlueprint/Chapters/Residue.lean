import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The residue at s = 1" =>

The Riemann zeta function $`\zeta(s)` has a simple pole at $`s=1` with residue
$`1`. On the $`p`-adic side we constructed $`\zp` not as a measure but as a
*pseudo-measure*, precisely so as to accommodate a
potential pole at the trivial character. In this chapter we show that this pole
is real and simple, and we compute its residue — the $`p`-adic analogue of the
analytic class number formula. Throughout, $`p` is a fixed odd prime, $`a` is a
fixed topological generator of $`\Zpx`, and $`\logp` denotes the Iwasawa
$`p`-adic logarithm.

As in the chapter on the value at $`s=1`, it is convenient to phrase everything
through the analytic *branches* $`\zpi` of the $`p`-adic zeta function: for
$`i \in \set{1, 2, \ldots, p-1}` one sets
$$`\zpi(s) = \int_{\Zpx} \Teich(x)^{i}\,\ang{x}^{1-s} \cdot \zp,`
where $`\Teich` is the Teichmüller character and
$`\ang{x} = \Teich(x)^{-1}x` is the projection of $`x \in \Zpx` to its
$`1`-units. The behaviour of $`\zp` at the trivial character is encoded by the
behaviour of $`\zeta_{p,p-1}` at $`s=1`.

# The main theorem

:::theorem "residue-zeta-p" (lean := "PadicLFunctions.continuousAt_zetaPBranch, PadicLFunctions.tendsto_sub_one_mul_zetaPBranch")
Let $`i \in \set{1, 2, \ldots, p-1}`.

* (i) If $`i \neq p-1`, then $`\zpi` is analytic at $`s=1`.
* (ii) The branch $`\zeta_{p,p-1}` has a simple pole at $`s=1`, with residue
  $$`\lim_{s\to 1} (s-1)\,\zeta_{p,p-1}(s) = 1 - p^{-1}.`

This rests on {uses "kubota-leopoldt"}[], {uses "res-g-pminus1"}[] and
{uses "res-numerator"}[].

In the formalisation "analytic at $`s=1`" is realised topologically: part (i)
is `ContinuousAt (zetaPBranch p hp2 i) 1` (the rigid-analytic structure is not
formalised), and part (ii) is the topological limit
`Tendsto (fun s => (s-1)·ζ_{p,p-1}(s)) (nhdsWithin 1 {s ≠ 1}) (nhds (1-p⁻¹))`.
:::

:::proof "residue-zeta-p"
Part (i) is immediate from {uses "res-g-pminus1"}[](i): unwinding the definition
of $`\zp` as a pseudo-measure expresses $`\zpi(s)` as a ratio whose denominator
$`g_{a,i}(s)` does not vanish at $`s=1` when $`i \neq p-1`, so the expression is
analytic there. For part (ii), the same unwinding gives, after passing to the
limit using {uses "res-limit-formula"}[],
$$`\lim_{s\to 1}(s-1)\,\zeta_{p,p-1}(s) = -\frac{\int_{\Zpx} x^{-1}\cdot \mu_a}{\logp(a)}.`
By {uses "res-integral-as-eval"}[] the numerator $`\int_{\Zpx} x^{-1}\cdot\mu_a`
equals $`\big((1-\varphi\circ\psi)\Fat\big)(0)`, which by {uses "res-numerator"}[]
is $`-(1-p^{-1})\logp(a)`; the two factors of $`\logp(a)` then cancel to leave
$`1 - p^{-1}`.
:::

# Unwinding the pseudo-measure

Recall from the construction of $`\zp` that, for any topological generator $`a`
of $`\Zpx`,
$$`\zp = \frac{x^{-1}\,\Res_{\Zpx}(\mu_a)}{[a]-[1]},`
where the $`\mu_a` are the Kubota–Leopoldt measures. Using
the rule $`\int_G \chi\cdot\lambda = (\chi(g)-1)^{-1}\int_G \chi\cdot([g]-[1])\lambda`
for integrating a pseudo-measure $`\lambda` against a non-trivial character, and
the identity $`\ang{x} = \Teich^{-1}(x)\,x`, the branch $`\zpi` becomes a ratio.

:::definition "res-denominator-g" (lean := "PadicLFunctions.zetaPBranch")
For $`i \in \set{1,\ldots,p-1}` define the *denominator*
$$`g_{a,i}(s) := \Teich(a)^{i}\,\ang{a}^{1-s} - 1.`
Substituting $`\zp = x^{-1}\Res_{\Zpx}(\mu_a)/([a]-[1])` into the definition of
$`\zpi` and integrating the pseudo-measure yields the closed form
$$`\zpi(s) = \frac{\int_{\Zpx} \Teich(x)^{s+i-1}\,x^{-s}\cdot \mu_a}{g_{a,i}(s)}.`
This rests on {uses "kubota-leopoldt"}[], {uses "measure-mu-a"}[] and
{uses "pseudo-measure"}[].

In the formalisation the closed form *is* the definition: `zetaPBranch` was
defined in the interpolation chapter as exactly this ratio
$`g_{a,i}(s)^{-1}\int\Teich(x)^i\ang{x}^{1-s}\mu_a`-numerator at the canonical
topological generator, so no separate unwinding step is needed; $`g_{a,i}`
appears inline as its denominator.
:::

:::lemma_ "res-g-pminus1" (lean := "PadicLFunctions.branch_denom_ne_zero, PadicLFunctions.tendsto_branch_denom_div, PadicLFunctions.teichmuller_isPrimitiveRoot")
With $`g_{a,i}` as above:

* (i) If $`i \neq p-1`, then $`g_{a,i}(1) \neq 0`. Consequently
  {uses "residue-zeta-p"}[Theorem (i)] holds.
* (ii) $`g_{a,p-1}(1) = 0`, and
  $$`\lim_{s\to 1} (s-1)^{-1}\,g_{a,p-1}(s) = -\logp(a).`

This depends on {uses "res-denominator-g"}[] and
{uses "teichmuller-character"}[].

The Lean statement of (i), `branch_denom_ne_zero`, is strengthened from
$`s=1` to *every* $`s` (the ultrametric isoceles argument is uniform in
$`s`); (ii) is proved through the exponential/logarithm bridge
$`\ang{a}^{1-s}=\exp((1-s)\logp\ang{a})` and the quadratic tail bound
$`\norm{\exp w - 1 - w}\le p\norm{w}^2`, rather than the notes' binomial-series
manipulation (decomposition R7, replan 3) — the limit and its value are
identical.
:::

:::proof "res-g-pminus1"
Since $`a` is a topological generator of $`\Zpx`, its image $`\Teich(a)` is a
*primitive* $`(p-1)`-th root of unity. At $`s=1` the factor $`\ang{a}^{1-s}=1`,
so $`g_{a,i}(1) = \Teich(a)^{i}-1`, which vanishes exactly when $`(p-1)\mid i`,
i.e. when $`i=p-1`. This proves (i): the closed form of {uses "res-denominator-g"}[]
then has a non-vanishing denominator at $`s=1` and is therefore analytic there.

For (ii), with $`i=p-1` we have $`\Teich(a)^{p-1}=1`, so
$`g_{a,p-1}(s) = \ang{a}^{1-s}-1`. Expanding the binomial series in
$`(\ang{a}-1)` gives
$$`g_{a,p-1}(s) = \sum_{n\ge 1}\binom{1-s}{n}(\ang{a}-1)^n = (1-s)\sum_{n\ge 1}\frac{1}{n}\binom{-s}{n-1}(\ang{a}-1)^n,`
using $`\binom{1-s}{n} = \tfrac{1-s}{n}\binom{-s}{n-1}`. As $`s\to 1` the
remaining sum tends to its value at $`s=1`, namely
$$`\sum_{n\ge 1}\frac{(-1)^{n-1}}{n}(\ang{a}-1)^n = \logp(\ang{a}) = \logp(a),`
where $`\binom{-1}{n-1}=(-1)^{n-1}` and $`\logp(\ang{a})=\logp(a)` because
$`\logp\Teich(a)=0`. Hence $`\lim_{s\to1}(s-1)^{-1}g_{a,p-1}(s) = -\logp(a)`.
:::

:::corollary "res-limit-formula"
Combining {uses "res-g-pminus1"}[](ii) with the closed form
{uses "res-denominator-g"}[] of $`\zeta_{p,p-1}`,
$$`\lim_{s\to 1} (s-1)\,\zeta_{p,p-1}(s) = -\frac{\int_{\Zpx} x^{-1}\cdot \mu_a}{\logp(a)}.`

(Not a standalone Lean declaration: this limit-algebra step — the inverse of
the denominator limit times the continuous numerator — is inlined in the proof
of `tendsto_sub_one_mul_zetaPBranch`, together with the nonvanishing
$`\logp(a)=\logp\ang{a}\neq 0` for a topological generator.)
:::

:::proof "res-limit-formula"
In the closed form $`\zeta_{p,p-1}(s) = \big(\int_{\Zpx}\Teich(x)^{s+p-2}x^{-s}\mu_a\big)/g_{a,p-1}(s)`
of {uses "res-denominator-g"}[], the numerator is analytic in $`s` and at $`s=1`
equals $`\int_{\Zpx} x^{-1}\cdot\mu_a` (since $`\Teich(x)^{p-1}=1` makes the
integrand $`\Teich(x)^{p-1}x^{-1}=x^{-1}`). The denominator $`g_{a,p-1}(s)`
vanishes to first order at $`s=1`. Multiplying by $`(s-1)` and using
{uses "res-g-pminus1"}[](ii), which gives $`(s-1)/g_{a,p-1}(s) \to 1/(-\logp(a))`,
the analytic numerator passes through the limit and yields the stated formula.
:::

# Computing the numerator

It remains to evaluate $`\int_{\Zpx} x^{-1}\cdot\mu_a`. As in the chapter on the
value at $`s=1`, the difficulty is that
multiplication by $`x^{-1}` is not defined on measures on $`\Zp`; on
Mahler transforms this is the indeterminacy in
inverting the operator $`\dpartial = (1+T)\tfrac{d}{dT}`. Recall that the Mahler
transform of $`\mu_a` is $`F_a(T) = \tfrac{1}{T} - \tfrac{a}{(1+T)^a-1}`. We seek
a primitive $`\Fat` with $`\dpartial\Fat = F_a`, lying in the ring $`\Rp` of
power series $`\sum a_n T^n` with $`\abs{a_n}r^n \to 0` for every $`0\le r<1`.

:::definition "res-primitive-Fa" (lean := "PadicLFunctions.FtildeA, PadicLFunctions.uA")
Define the *primitive of $`F_a`* by
$$`\Fat(T) := \log\!\left(\frac{T}{1+T}\cdot\frac{(1+T)^a}{(1+T)^a-1}\right) = \log\!\left(\frac{T}{(1+T)^a-1}\cdot (1+T)^{a-1}\right).`

The Lean definition realises the second expression through the unit
factorisation $`(1+T)^a-1 = aT\,u_a(T)` (with $`u_a` of constant term $`1`):
$`\Fat = -\logp(a) - \log u_a + (a-1)\log(1+T)`, each summand a legal formal
composition over a complete normed $`\Qp`-field $`K`.
:::

:::lemma_ "res-primitive-derivative" (lean := "PadicLFunctions.one_add_mul_derivative_FtildeA")
Formally, $`\dpartial \Fat(T) = F_a(T)`. This depends on
{uses "res-primitive-Fa"}[] and {uses "mahler-transform"}[].

The Lean statement carries the (implicit in the notes' §4 setting) hypothesis
$`p\nmid a`: the project's $`F_a` is the junk value $`0` when $`p \mid a`
(its denominator-inverse degenerates), while $`\dpartial\Fat` is never zero.
:::

:::proof "res-primitive-derivative"
The operator $`\dpartial = (1+T)\tfrac{d}{dT}` satisfies the chain rule, so for
any unit power series $`u` one has $`\dpartial\log u = (1+T)u'/u`. Applied to
$`u = \tfrac{(1+T)^a-1}{(1+T)^a}`, whose logarithmic derivative computes to
$`(1+T)\big[\tfrac{a(1+T)^{a-1}}{(1+T)^a-1} - \tfrac{a(1+T)^{a-1}}{(1+T)^a}\big]`,
this collapses (after clearing $`(1+T)^a`) to
$`\dpartial\log\big(\tfrac{(1+T)^a-1}{(1+T)^a}\big) = \tfrac{a}{(1+T)^a-1}`.
Specialising to $`a=1` gives $`\dpartial\log\big(\tfrac{T}{1+T}\big) = \tfrac1T`.
Since $`\Fat = \log\big(\tfrac{T}{1+T}\big) - \log\big(\tfrac{(1+T)^a-1}{(1+T)^a}\big)`,
linearity of $`\dpartial` yields
$`\dpartial\Fat = \tfrac1T - \tfrac{a}{(1+T)^a-1} = F_a(T)`, the Mahler transform
of $`\mu_a`.
:::

:::lemma_ "res-Fa-tilde-bounded"
We have $`\Fat(T) \in \Rp`, so that $`\Fat` corresponds under the Mahler
correspondence to a locally analytic distribution. This depends on
{uses "res-primitive-Fa"}[] and {uses "mahler-transform"}[].

*Not formalised as stated* (RJW Lemma 7.4): the formalisation follows a
distribution-free route (decomposition R7, replan 1) that never constructs
$`\Rp` or the locally analytic distribution $`\widetilde\mu_a`. The analytic
content actually used — the coefficients of $`\Fat` grow at most linearly, so
its evaluation series converges on the open unit disc — is proved directly
(the `norm_coeff_FtildeA_le`/`summable_seriesEval_FtildeA` layer in
`ResidueZeta.lean`), and the constant-of-integration argument runs in
$`\ker\psi` exactly as in the value-at-$`s=1` chapter.
:::

:::proof "res-Fa-tilde-bounded"
Write $`(1+T)^a-1 = aT\,(1+Tg(T))` with $`g(T) = \sum_{n\ge 2} a^{-1}\binom{a}{n}T^{n-2}`,
so that, as in the construction of $`\mu_a`,
$`\tfrac{1}{(1+T)^a-1} = \tfrac{1}{aT}(1+Th(T))` with $`h(T)\in\Zp[[T]]`. Hence
$`\tfrac{T}{(1+T)^a-1} = a^{-1}(1+Th(T))`, and
$$`\log\!\left(\frac{T}{(1+T)^a-1}\right) = -\logp(a) + \sum_{n\ge 1}\frac{(-1)^{n+1}}{n}T^n h(T)^n.`
The coefficients here grow only logarithmically in $`n` (the $`1/n` is offset by
$`\val(n)`), so this series lies in $`\Rp`. Likewise
$`(1+T)^{a-1} = 1 + T\sum_{n\ge1}\binom{a-1}{n}T^{n-1}` has a well-defined
logarithm in $`\Rp`. Adding the two elements of $`\Rp` yields $`\Fat \in \Rp`.
:::

With $`\Fat \in \Rp` in hand we may attach to it a locally analytic distribution
$`\widetilde\mu_a` (the one whose Mahler transform is $`\Fat`), and the relation
$`\dpartial\Fat = F_a` says precisely that $`x\,\widetilde\mu_a = \mu_a`. This is
the device that makes sense of the otherwise ill-defined product $`x^{-1}\mu_a`.

:::lemma_ "res-integral-as-eval" (lean := "PadicLFunctions.psi_rhoA, PadicLFunctions.one_add_mul_derivative_mahlerK_rhoA, PadicLFunctions.p_mul_constantCoeff_mahlerK_rhoA")
The numerator of the residue formula is the value at $`0` of the restriction of
$`\Fat` to $`\Zpx`:
$$`\int_{\Zpx} x^{-1}\cdot\mu_a = \big((1-\varphi\circ\psi)\Fat\big)(0),`
where $`\varphi\circ\psi` acts on power series by
$`\varphi\circ\psi(F)(T) = \tfrac1p\sum_{\xi\in\mu_p} F((1+T)\xi - 1)`. This
depends on {uses "res-primitive-derivative"}[], {uses "res-Fa-tilde-bounded"}[],
{uses "locally-analytic-distribution"}[] and {uses "p-adic-value-s1"}[].

Distribution-free realisation: instead of $`\widetilde\mu_a`, the
formalisation works with the genuine measure $`\rho_a = x^{-1}\Res_{\Zpx}(\mu_a)`
(the canonical numerator of $`\zp`), shows $`\psi(\rho_a)=0` and
$`\dpartial\sA_{\rho_a} = \sA_{\Res_{\Zpx}\mu_a}`, and pins the constant of
integration by evaluating at the $`p`-th roots of unity: the displayed identity
appears $`p`-scaled as
$`p\,\sA_{\rho_a}(0) = p\,\Fat(0) - \sum_{\xi\in\mu_p}\Fat(\xi-1)`, with the
left side equal to $`p\int_{\Zpx}x^{-1}\mu_a`.
:::

:::proof "res-integral-as-eval"
On $`\Zpx` the function $`x` is invertible, so $`x\,\widetilde\mu_a = \mu_a`
gives $`\Res_{\Zpx}(\widetilde\mu_a) = x^{-1}\Res_{\Zpx}(\mu_a)` and hence
$`\int_{\Zpx} x^{-1}\cdot\mu_a = \int_{\Zpx}\widetilde\mu_a`. The right-hand side
is the value at the trivial character of the restricted distribution, which on
Mahler transforms is read off as the constant term: writing $`\Res_{\Zpx} =
1-\varphi\circ\psi` (the complement of restriction to $`p\Zp`, whose Mahler
transform is $`\varphi\circ\psi\Fat`), one gets
$`\int_{\Zpx}\widetilde\mu_a = \big((1-\varphi\circ\psi)\Fat\big)(0)`. This is the
exact analogue, with $`\Fat` in place of $`\widetilde F_\theta`, of the
computation that produced the value at $`s=1`. This reduces the residue
computation to a single evaluation.
:::

:::lemma_ "res-numerator" (lean := "PadicLFunctions.constantCoeff_FtildeA, PadicLFunctions.sum_seriesEval_FtildeA, PadicLFunctions.constantCoeff_mahlerK_rhoA, PadicLFunctions.zetaNum_one")
We have
$$`\big((1-\varphi\circ\psi)\Fat\big)(0) = -(1-p^{-1})\,\logp(a).`
This depends on {uses "res-primitive-Fa"}[] and {uses "res-Fa-tilde-bounded"}[].

Formalised as `constantCoeff_mahlerK_rhoA` (with the left side realised as
$`\sA_{\rho_a}(0)`, see {uses "res-integral-as-eval"}[]) from the two evaluations
`constantCoeff_FtildeA` ($`\Fat(0) = -\logp a`) and `sum_seriesEval_FtildeA`
($`\sum_{\xi\in\mu_p}\Fat(\xi-1) = -\logp a`); the $`\mu_p`-collapse is run by
a product identity (the multiset $`\set{\xi^a}` equals $`\mu_p`, so
$`\prod_{\xi\neq 1} u_a(\xi-1) = a^{-(p-1)}`) together with Fermat's
$`a^{p-1}\equiv 1 \bmod p`, in a complete algebraically closed field
$`K=\CC_p` containing $`\mu_p`; `zetaNum_one` is the descent of the resulting
mass to $`\Qp` along the injective structure map.
:::

:::proof "res-numerator"
*Value of $`\Fat(0)`.* From the second expression in {uses "res-primitive-Fa"}[],
$`\Fat(0) = \log\big(\tfrac{T}{(1+T)^a-1}\big)\big|_{T=0} + \log((1+T)^{a-1})\big|_{T=0}`;
the first summand equals $`-\logp(a)` by the expansion in
{uses "res-Fa-tilde-bounded"}[] and the second is $`0`, so $`\Fat(0) = -\logp(a)`.

*Value of $`(\varphi\circ\psi)\Fat(0)`.* Summing the logarithm over $`\xi\in\mu_p`
turns the sum into the logarithm of a product, and
$`\prod_{\xi\in\mu_p}(X\xi-1) = X^p-1` collapses each factor. Using that $`a` is a
topological generator (so $`\set{\xi^a:\xi\in\mu_p}=\mu_p`) and
$`\prod_{\xi\in\mu_p}\xi^{a-1}=1`,
$$`(\varphi\circ\psi)\Fat(T) = \frac1p\log\!\left(\frac{(1+T)^p-1}{(1+T)^{ap}-1}\cdot (1+T)^{(a-1)p}\right).`
Writing $`(1+T)^p-1 = pT(1+Tj(T))` and $`\tfrac{1}{(1+T)^{ap}-1} = \tfrac{1}{apT}(1+Tk(T))`
as before, the factors of $`pT` cancel and the right-hand side at $`T=0`
collapses to $`-p^{-1}\logp(a)`.

*Conclusion.* Subtracting the two evaluations,
$$`\big((1-\varphi\circ\psi)\Fat\big)(0) = \Fat(0) - (\varphi\circ\psi)\Fat(0) = -\logp(a) + p^{-1}\logp(a) = -(1-p^{-1})\,\logp(a),`
as claimed.
:::

Combining the limit formula with the value of the numerator, the two
occurrences of $`\logp(a)` cancel and we obtain
$$`\lim_{s\to 1}(s-1)\,\zeta_{p,p-1}(s) = -\frac{-(1-p^{-1})\logp(a)}{\logp(a)} = 1 - p^{-1},`
completing the proof of the residue theorem. The residue
$`1-p^{-1}` is the precise $`p`-adic shadow of the residue $`1` of the complex
$`\zeta` at $`s=1`: it is $`\zeta(s)` with its Euler factor at $`p` removed,
evaluated at the pole.
