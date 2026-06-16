import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Measures and the Iwasawa algebra" =>

This chapter develops the $`p`-adic analysis underlying the whole story: $`p`-adic
measures on a profinite abelian group $`G`, their identification with the Iwasawa
algebra $`\Lam(G)`, and — in the key case $`G = \Zp` — a fourth description as
power series via the Mahler transform. We then build a *toolbox* of operations on
measures, introduce pseudo-measures (to accommodate the simple pole of the zeta
function), and close with locally analytic distributions. The treatment follows
{Informal.citet "RJW"}[] §3.

Throughout we fix a finite extension $`L` of $`\Qp`, with $`p`-adic valuation
$`\vp` normalised by $`\vp(p) = 1`; this is the coefficient field, and $`\OL`
denotes its ring of integers.

# Preliminaries on p-adic Banach spaces

We first fix the functional-analytic language. The reader comfortable with
$`p`-adic Banach spaces and orthonormal bases may skip to the next section.

:::definition "meas-valuation" (lean := "ValuativeRel, IsUltrametricDist")
Let $`B` be an $`L`-vector space. A *valuation* on $`B` is a function
$`v : B \to \R \cup \set{+\infty}` such that (i) $`v(x) = +\infty` iff $`x = 0`;
(ii) $`v(x+y) \geq \min(v(x), v(y))` for all $`x,y \in B`; and (iii)
$`v(\lambda x) = \vp(\lambda) + v(x)` for all $`\lambda \in L`, $`x \in B`. Such a
valuation induces a norm, hence a topology, on $`B`. (In mathlib, valuations on
rings and fields are abstracted by `ValuativeRel`; the vector-space notion above
corresponds, via $`v = -\log\norm{\cdot}`, to ultrametric norms, i.e.
`IsUltrametricDist`, which is the language the formalisation uses throughout.)
:::

:::definition "meas-banach" (lean := "NormedSpace, CompleteSpace")
An *$`L`-Banach space* is a complete topological $`L`-vector space $`B` whose
topology is induced from a valuation $`v` (in the sense of {bpref "meas-valuation"}[]).
(Mathlib expresses this as a complete normed space, `NormedSpace` +
`CompleteSpace`, with the ultrametric inequality supplied per-space.)
:::

:::definition "meas-orthonormal" (lean := "ZeroAtInftyContinuousMap")
Let $`I` be a set and $`\ell^0_\infty(I, L)` the $`L`-Banach space of families
$`(a_i)_{i \in I}` in $`L` tending to $`0` (for every $`\epsilon > 0`,
$`\abs{a_i}_L < \epsilon` for all but finitely many $`i`), with valuation
$`v((a_i)_i) = \inf_{i} \vp(a_i)`. An *orthonormal basis* of an $`L`-Banach space
$`B` is a family $`(e_i)_{i \in I}` for which the map
$$`\ell^0_\infty(I, L) \longrightarrow B, \qquad (a_i)_i \longmapsto \sum_{i} a_i e_i`
is an isometric isomorphism. (If $`B` has valuation $`v_B` with
$`v_B(B) = \vp(L)`, such a basis always exists. Mathlib has the space
$`\ell^0_\infty(I,L)` as `ZeroAtInftyContinuousMap` — written $`C_0(I, L)` — and
orthonormal bases appear as concrete isometric equivalences onto it, such as
`PadicInt.mahlerEquiv` below.)
:::

:::definition "meas-dual-topology" (lean := "NormedSpace.Dual, WeakDual")
Let $`B` be an $`L`-Banach space and $`B^* = \mathrm{Hom}_{\mathrm{cts}}(B, L)` its
continuous dual. (Mathlib: `NormedSpace.Dual` carries the strong topology,
`WeakDual` the weak one.) The *strong topology* is induced by the dual valuation
$`v^*(\mu) = \inf_{x \in B}\big(\vp(\mu(x)) - v(x)\big)`; it is the topology of
uniform convergence. The *weak topology* is induced by the semivaluations
$`v_x(\mu) = \vp(\mu(x))` for $`x \in B`; it is the topology of pointwise
convergence. The dual is complete for both, is an $`L`-Banach space for the strong
topology, and $`B` is reflexive precisely when $`B^*` carries the weak topology.
:::

# p-adic measures

We now fix the setting. Let $`G` be a profinite abelian group; the cases
$`G = \Zp` and $`G = \Zpx` are of most interest.

:::definition "meas-cts-functions" (lean := "ContinuousMap")
Let $`\cC(G, L)` be the $`L`-vector space of continuous functions $`\phi : G \to L`,
equipped with the valuation $`\vC(\phi) = \inf_{x \in G} \vp(\phi(x))`. As $`G` is
compact this is well-defined, induces the sup norm, and makes $`\cC(G, L)` an
$`L`-Banach space in the sense of {uses "meas-banach"}[].
:::

:::definition "p-adic-measure" (lean := "PadicMeasure")
The space $`\sM(G, L)` of *$`L`-valued measures on $`G`* is the continuous dual
$`\cC(G, L)^* = \mathrm{Hom}_{\mathrm{cts}}(\cC(G,L), L)`, using
{uses "meas-cts-functions"}[]. The pairing of $`\mu \in \sM(G,L)` with
$`\phi \in \cC(G,L)` is written $`\int_G \phi(x) \cdot \mu(x)` (or $`\int_G \phi \cdot \mu`).
We call $`\mu` an *$`\OL`-valued measure*, $`\mu \in \sM(G, \OL)`, if
$`\int_G \phi \cdot \mu \in \OL` for every $`\OL`-valued $`\phi`; boundedness gives
$`\sM(G, L) = \sM(G, \OL) \otimes_{\OL} L`. A *$`p`-adic measure on $`\Zp`* is such
a functional with $`G = \Zp`. (All of this applies verbatim to any subset
$`X \subseteq G` with the subspace topology, $`X` no longer needing to be a group.)
:::

:::definition "meas-dirac" (lean := "PadicMeasure.dirac")
For $`g \in G`, the *Dirac measure* $`\delta_g \in \sM(G, \OL)` is evaluation at
$`g`, i.e. $`\delta_g(\phi) = \phi(g)`. It depends on {uses "p-adic-measure"}[].
:::

:::proposition "meas-locally-constant" (lean := "PadicMeasure.exists_locallyConstant_norm_sub_le, PadicMeasure.ext_locallyConstant")
Let $`\cClc(G, \OL)` be the locally constant functions $`G \to \OL`, a dense
subspace of $`\cC(G, \OL)`, and $`\sMlc(G, \OL) = \cClc(G, \OL)^*` its dual.
Restriction induces a canonical isomorphism
$`\sM(G, \OL) \xrightarrow{\ \sim\ } \sMlc(G, \OL)`. This rests on
{uses "p-adic-measure"}[].
:::

:::proof "meas-locally-constant"
Any continuous $`\phi \in \cC(G, \OL)` is the $`p`-adic limit of its locally
constant truncations $`\phi_n(x) = \sum_{a \in \Z/p^n\Z} \phi(a)\, \one_{a + p^n\Zp}(x)`,
so $`\cClc` is dense and restriction $`\sM \to \sMlc` is injective. For surjectivity
one writes down an inverse: given $`\mu^{\mathrm{lc}} \in \sMlc(G,\OL)` and
$`\phi \in \cC(G,\OL)`, pick locally constant $`\phi_n \to \phi` and set
$`\int_G \phi \cdot \mu := \lim_n \int_G \phi_n \cdot \mu^{\mathrm{lc}}`. By
continuity the limit exists and is independent of the chosen sequence, giving a
well-defined measure inverse to restriction.
:::

:::proposition "meas-additive-functions"
Locally constant measures $`\sMlc(G, \OL)` are identified with the additive
functions $`\mu : \set{\text{open compact subsets of } G} \to \OL`. Combined with
{uses "meas-locally-constant"}[], this identifies $`\sM(G, \OL)` with the additive
functions on the open compact subsets of $`G`.
:::

:::proof "meas-additive-functions"
Given $`\mu \in \sMlc(G, \OL)`, set $`\mu(U) := \int_G \one_U \cdot \mu` for an open
compact $`U`; additivity of $`U \mapsto \mu(U)` is clear from linearity. Conversely
an additive set-function integrates a locally constant $`\phi`, factoring through
$`G/H` for some open subgroup $`H`, by the finite sum
$`\int_G \phi \cdot \mu := \sum_{[a] \in G/H} \phi(a)\,\mu(aH)`; the two
constructions are mutually inverse. (On $`\Zp` the real-valued Haar measure, with
$`a + p^n\Zp \mapsto p^{-n}`, is *not* a $`p`-adic measure, being $`p`-adically
unbounded.) Under this dictionary the Dirac measure $`\delta_g` from
{uses "meas-dirac"}[] is the set-function $`X \mapsto 1` if $`g \in X` and $`0`
otherwise.
:::

# The Iwasawa algebra

We now recast measures algebraically. The prototype is the classical fact for a
finite abelian group.

:::proposition "meas-finite-group-algebra"
If $`G` is a finite abelian group, the map $`[g] \mapsto \delta_g` induces an
isomorphism $`\Z[G] \cong \sM(G, \Z)` between the group algebra and the space of
measures on $`G` (discrete topology). It uses {uses "meas-dirac"}[].
:::

:::proof "meas-finite-group-algebra"
A measure $`\mu` on the finite set $`G` is determined by its values
$`c_g = \mu(\one_{\set g})`, and $`\mu = \sum_g c_g \delta_g`; matching $`\delta_g`
with the basis element $`[g]` of $`\Z[G]` gives a bijection that is visibly
$`\Z`-linear and multiplicative for the convolution/group multiplication.
:::

:::proposition "meas-iwasawa-inverse-limit"
For $`G` profinite abelian there is a natural isomorphism
$$`\sM(G, \OL) \cong \varprojlim_H \OL[G/H],`
the limit running over open subgroups $`H \leq G`. This builds on
{uses "meas-locally-constant"}[] and {uses "meas-finite-group-algebra"}[].
:::

:::proof "meas-iwasawa-inverse-limit"
By {uses "meas-locally-constant"}[], $`\sM(G,\OL) \cong \sMlc(G,\OL)`. Every locally
constant function factors through some finite quotient $`G/H`, so
$`\cClc(G,\OL) \cong \varinjlim_H \cC(G/H, \OL)`. Dualising turns the direct limit
into an inverse limit,
$`\sM(G, \OL) \cong \varprojlim_H \sM(G/H, \OL)`, and each finite-level term is
$`\sM(G/H, \OL) \cong \OL[G/H]` by {uses "meas-finite-group-algebra"}[] (over
$`\OL`). Explicitly, a measure $`\mu` maps to
$`\big(\sum_{[a] \in G/H} \mu(aH)\,[a]\big)_H`, additivity guaranteeing
compatibility under the projection maps; conversely the coefficients of the
finite-level elements recover the set-function $`\mu(aH)`.
:::

:::definition "iwasawa-algebra"
The *Iwasawa algebra of $`G`* is the profinite completion of the group algebra,
$$`\Lam(G) := \varprojlim_H \OL[G/H],`
the inverse limit over open subgroups $`H \leq G` (the coefficient field $`L` is
suppressed from the notation). By {uses "meas-iwasawa-inverse-limit"}[] it is
canonically isomorphic to $`\sM(G, \OL)`.
:::

:::definition "meas-convolution" (lean := "PadicMeasure.mul_apply")
Transporting the $`\OL`-algebra structure of $`\Lam(G)` to $`\sM(G, \OL)` via
{uses "iwasawa-algebra"}[], the product is *convolution of measures*: for
$`\mu, \lambda \in \sM(G, \OL)`,
$$`\int_G \phi \cdot (\mu * \lambda) = \int_G \left(\int_G \phi(x+y) \cdot \lambda(y)\right) \cdot \mu(x).`
This makes {uses "meas-iwasawa-inverse-limit"}[] an isomorphism of $`\OL`-algebras,
and sends the Dirac measures $`\delta_a` (for $`a \in \Zp`) to the group-like
elements $`[a] = ([a + p^n\Zp])_n \in \Lam(\Zp)`.
:::

# p-adic analysis and Mahler transforms

We now have three equivalent descriptions of measures on $`G`: linear functionals
on $`\cC(G,L)`, additive functions on open compact subsets, and elements of
$`\Lam(G)`. Specialising to $`G = \Zp`, we give a fourth, via the power series ring
$`\OL[[T]]`.

:::definition "meas-binomial-polynomials" (lean := "mahler")
For $`x \in \Zp` and $`n \geq 1` set
$`\binomc{x}{n} = \tfrac{x(x-1)\cdots(x-n+1)}{n!}`, with $`\binomc{x}{0} = 1`. Each
$`x \mapsto \binomc{x}{n}` lies in $`\cC(\Zp, \Zp)` with $`\vC = 0`.
:::

:::theorem "meas-mahler-basis" (lean := "PadicInt.mahlerEquiv, PadicInt.hasSum_mahler")
*(Mahler.)* Every continuous $`\phi : \Zp \to L` has a unique expansion
$$`\phi(x) = \sum_{n \geq 0} a_n(\phi)\, \binomc{x}{n}, \qquad a_n(\phi) \in L,\ a_n(\phi) \to 0,`
and $`\vC(\phi) = \inf_{n} \vp(a_n(\phi))`. Equivalently, the binomial polynomials
{uses "meas-binomial-polynomials"}[] form an orthonormal basis (in the sense of
{uses "meas-orthonormal"}[]) of the $`L`-Banach space $`\cC(\Zp, L)`.
:::

:::proof "meas-mahler-basis"
This is a foundational theorem of $`p`-adic analysis (Mahler; see Colmez). The
coefficients are given explicitly by iterated finite differences: defining the
discrete derivatives $`\phi^{[0]} = \phi` and
$`\phi^{[k+1]}(x) = \phi^{[k]}(x+1) - \phi^{[k]}(x)`, one has
$`a_n(\phi) = \phi^{[n]}(0)`. The bound $`a_n(\phi) \to 0` and the isometry
$`\vC(\phi) = \inf_n \vp(a_n(\phi))` express that the $`\binomc{x}{n}` are an
orthonormal basis; uniqueness follows because the basis is free over
$`\ell^0_\infty(\N, L)`.
:::

:::definition "mahler-transform" (lean := "PadicMeasure.mahlerTransform")
The *Mahler transform* (or *Amice transform*) of a measure
$`\mu \in \sM(\Zp, \OL)` is the power series
$$`\Am_\mu(T) := \int_{\Zp} (1+T)^x \cdot \mu(x) = \sum_{n \geq 0}\left(\int_{\Zp} \binomc{x}{n} \cdot \mu\right) T^n \in \OL[[T]].`
It encodes $`\mu` by its values on the Mahler basis {uses "meas-binomial-polynomials"}[],
using {uses "p-adic-measure"}[]. For a Dirac measure {uses "meas-dirac"}[] one has
$`\Am_{\delta_a}(T) = \sum_n \binomc{a}{n} T^n = (1+T)^a`.
:::

:::theorem "iwasawa-isomorphism" (lean := "PadicMeasure.mahlerRingEquiv")
The Mahler transform is an isomorphism of $`\OL`-algebras
$$`\Am : \sM(\Zp, \OL) \xrightarrow{\ \sim\ } \OL[[T]].`
Combined with {uses "iwasawa-algebra"}[] it gives the *Iwasawa isomorphism*
$`\Lam(\Zp) \cong \OL[[T]]`, sending the group-like generator $`[1]` to $`1+T`.
It rests on {uses "mahler-transform"}[] and {uses "meas-mahler-basis"}[].
:::

:::proof "iwasawa-isomorphism"
This is essentially a restatement of the orthonormal basis property. By
{uses "meas-mahler-basis"}[], any $`\phi \in \cC(\Zp, \OL)` is
$`\phi = \sum_n a_n(\phi)\binomc{x}{n}` with $`a_n(\phi) \to 0`, so by continuity
and linearity a measure $`\mu` is determined by the numbers
$`c_n = \int_{\Zp} \binomc{x}{n} \cdot \mu` through
$`\int_{\Zp} \phi \cdot \mu = \sum_n a_n(\phi) c_n`. Conversely any
$`g = \sum_n c_n T^n \in \OL[[T]]` defines, by exactly this formula, a measure
$`\mu_g` with $`\Am_{\mu_g} = g`; the sum converges in $`\OL` because
$`a_n(\phi) \to 0` and $`c_n \in \OL`. Thus $`\Am` is a bijection. For
multiplicativity it suffices, by density, to check on Dirac measures
{uses "meas-convolution"}[]: since $`1` topologically generates $`(\Zp, +)` and
$`1+T` topologically generates $`\OL[[T]]`, the assignment $`[1] \mapsto 1+T`
identifies $`\Lam(\Zp)` with $`\OL[[T]]`, and $`\delta_a \mapsto (1+T)^a` matches
the top arrow $`\delta_a \mapsto \Am_{\delta_a} = (1+T)^a`. Inverting $`p` gives
$`\sM(\Zp, L) \cong \OL[[T]][1/p]`.
:::

:::definition "meas-power-series-measure" (lean := "PadicMeasure.ofPowerSeries")
For $`g \in \OL[[T]]` we write $`\mu_g \in \sM(\Zp, \OL)` for the corresponding
$`\OL`-valued measure, characterised by $`\Am_{\mu_g} = g` via
{uses "iwasawa-isomorphism"}[]. The first moments are
$`\int_{\Zp} \mu_g = g(0)`, $`\int_{\Zp} x \cdot \mu_g = g'(0)`,
$`\int_{\Zp} x^2 \cdot \mu_g = g''(0) + g'(0)`, and in general
$`\int_{\Zp} x^n \cdot \mu_g` is an integral combination of $`g^{(r)}(0)`,
$`0 \le r \le n` (sharpened in {bpref "meas-eval-xk"}[]).
:::

Under {bpref "iwasawa-isomorphism"}[] the strong topology on $`\sM(\Zp, \OL)`
corresponds to the $`p`-adic topology on $`\OL[[T]]` (uniform convergence of
coefficients), and the weak topology to the $`(p,T)`-adic topology (term-by-term
convergence). For instance $`1, T, T^2, \dots` converges to $`0` weakly but not
strongly.

# A measure-theoretic toolbox

Natural operations on measures correspond, under the Mahler transform, to
operators on power series. We henceforth freely conflate $`\sM(G, \OL)` with
$`\Lam(G)`, writing $`\mu \in \Lam(G)` for a measure.

:::proposition "meas-mult-by-x" (lean := "PadicMeasure.mahlerTransform_cmul_X")
For a measure $`\mu` on $`\Zp`, define $`x\mu` by
$`\int_{\Zp} f \cdot x\mu = \int_{\Zp} xf \cdot \mu`. Then
$$`\Am_{x\mu} = \partial\, \Am_\mu, \qquad \partial := (1+T)\tfrac{d}{dT}.`
This uses {uses "mahler-transform"}[].
:::

:::proof "meas-mult-by-x"
It suffices to compute the action on the Mahler basis. From the Pascal-type
identity
$`x\binomc{x}{n} = (x-n)\binomc{x}{n} + n\binomc{x}{n} = (n+1)\binomc{x}{n+1} + n\binomc{x}{n}`,
multiplication by $`x` sends the coefficient sequence of $`\mu` to that obtained by
applying $`\partial`, since $`\partial` acts on $`T^n` exactly as
$`T^n \mapsto (1+T)\,nT^{n-1} = nT^{n-1} + nT^n`, matching the two terms above.
:::

:::corollary "meas-eval-xk" (lean := "PadicMeasure.apply_powCM")
For $`\mu \in \Lam(\Zp)` and $`k \geq 0`,
$$`\int_{\Zp} x^k \cdot \mu = (\partial^k \Am_\mu)(0).`
This is immediate from {uses "meas-mult-by-x"}[].
:::

:::proof "meas-eval-xk"
Iterating {uses "meas-mult-by-x"}[] gives $`\Am_{x^k\mu} = \partial^k \Am_\mu`, and
evaluating the moment formula $`\int_{\Zp} \mu_g = g(0)` at $`g = \Am_{x^k\mu}`
(see {uses "meas-power-series-measure"}[]) yields
$`\int_{\Zp} x^k \cdot \mu = \Am_{x^k\mu}(0) = (\partial^k \Am_\mu)(0)`.
:::

:::definition "meas-mult-by-zx" (lean := "PadicLFunctions.MeasureR.cmul, PadicLFunctions.MeasureR.mahlerTransform_charTwist")
For $`g \in \cC(\Zp, L)` define $`g(x)\mu` by
$`\int_{\Zp} f \cdot g(x)\mu := \int_{\Zp} fg \cdot \mu`. In particular, for
$`z \in \OL` with $`\abs{z-1} < 1`,
$$`\Am_{z^x \mu}(T) = \Am_\mu\big((1+T)z - 1\big),`
since $`\Am_\mu((1+T)z - 1) = \int_{\Zp}((1+T)z)^x \cdot \mu` is by definition the
Mahler transform of $`z^x\mu`. Uses {uses "mahler-transform"}[].

In the formalisation the multiplication is `MeasureR.cmul` (over the general
coefficient ring of the §5 widening) and the displayed substitution identity is
`mahlerTransform_charTwist`, stated coefficientwise — the right-hand side read
off as the convergent sum over Mahler coefficients, with `z = 1 + r` for
topologically nilpotent `r`.
:::

:::definition "meas-restriction" (lean := "PadicMeasure.res, PadicMeasure.res_union, PadicLFunctions.MeasureR.res_class_eq_sum_twists")
For an open compact $`X \subseteq \Zp` with characteristic function $`\one_X`, the
*restriction* $`\Res_X(\mu)` is the measure with
$`\int_{\Zp} f \cdot \Res_X(\mu) := \int_{\Zp} f\one_X \cdot \mu`, also written
$`\int_X f \cdot \mu`; one says $`\mu` is *supported on $`X`* if
$`\mu = \Res_X(\mu)`. For $`X = b + p^n\Zp` the characteristic function is the finite
Fourier expansion $`\one_{b+p^n\Zp}(x) = \tfrac{1}{p^n}\sum_{\xi \in \mu_{p^n}} \xi^{x-b}`
over the $`p^n`-th roots of unity (the sum being $`1` when $`p^n \mid x - b` and $`0`
otherwise). Multiplying $`\mu` by each character $`x \mapsto \xi^x` via
{uses "meas-mult-by-zx"}[] and summing gives
$$`\Am_{\Res_{b+p^n\Zp}(\mu)}(T) = \frac{1}{p^n}\sum_{\xi \in \mu_{p^n}} \xi^{-b}\, \Am_\mu\big((1+T)\xi - 1\big).`
The case $`b = 0`, $`n = 1` gives the restriction to $`\Zpx`:
$$`\Am_{\Res_{\Zpx}(\mu)}(T) = \Am_\mu(T) - \frac{1}{p}\sum_{\xi \in \mu_p}\Am_\mu\big((1+T)\xi - 1\big).`
An arbitrary open compact $`X` (or its complement, as here for $`\Zpx`) is a finite
disjoint union of such balls, so its restriction formula is obtained by summing.

The displayed Fourier-expansion formula (deferred during §3) is realised in the
§5 coefficient layer as `MeasureR.res_class_eq_sum_twists`, stated as an
identity of measures multiplied through by `p^n` and with `ξ^{-b}` written with
a positive exponent — the source's identity divided by `p^n`.
:::

:::definition "meas-sigma-phi-psi" (lean := "PadicMeasure.sigma, PadicMeasure.phi, PadicMeasure.psi, PadicMeasure.mahlerTransform_sigma, PadicMeasure.mahlerTransform_phi")
For $`a \in \Zpx` define $`\sigma_a(\mu)` by
$`\int_{\Zp} f(x) \cdot \sigma_a(\mu) = \int_{\Zp} f(ax) \cdot \mu`. Testing against
$`f(x) = (1+T)^x` (so $`f(ax) = ((1+T)^a)^x`) shows
$`\Am_{\sigma_a(\mu)} = \Am_\mu((1+T)^a - 1)`: this is the substitution
$`1+T \mapsto (1+T)^a`. Write $`\varphi := \sigma_p`, so
$`\int_{\Zp} f(x) \cdot \varphi(\mu) = \int_{\Zp} f(px) \cdot \mu` and
$`\Am_{\varphi(\mu)} = \Am_\mu((1+T)^p - 1)`. Define the partial inverse $`\psi(\mu)` by
$`\int_{\Zp} f(x) \cdot \psi(\mu) = \int_{p\Zp} f(p^{-1}x) \cdot \mu`. These use
{uses "meas-restriction"}[] and {uses "mahler-transform"}[].
:::

:::proposition "meas-phi-psi-identities" (lean := "PadicMeasure.psi_phi, PadicMeasure.phi_psi, PadicMeasure.res_units_eq")
The operators of {uses "meas-sigma-phi-psi"}[] satisfy $`\psi \circ \varphi = \mathrm{id}`
and $`\varphi \circ \psi(\mu) = \Res_{p\Zp}(\mu)`, whence
$$`\Res_{\Zpx}(\mu) = (1 - \varphi\circ\psi)(\mu).`
On power series, $`\psi` is the unique operator with
$`\varphi\circ\psi(F)(T) = \tfrac{1}{p}\sum_{\xi \in \mu_p} F((1+T)\xi - 1)`.
:::

:::proof "meas-phi-psi-identities"
Both relations are direct computations against a test function $`f`. For
$`\psi\circ\varphi`, insert $`\one_{p\Zp}(px) = 1` to get
$`\int f \cdot \psi\varphi(\mu) = \int \one_{p\Zp}(px) f(x) \cdot \varphi(\mu) = \int f(x) \cdot \mu`.
For $`\varphi\circ\psi`, $`\int f \cdot \varphi\psi(\mu) = \int f(px) \cdot \psi(\mu) = \int_{p\Zp} f \cdot \mu = \int f \cdot \Res_{p\Zp}(\mu)`.
Subtracting from the identity gives $`\Res_{\Zpx} = 1 - \varphi\psi`, matching the
$`b=0,n=1` restriction formula of {uses "meas-restriction"}[]; transporting through
$`\Am` yields the stated power-series formula.
:::

:::corollary "meas-supported-on-units" (lean := "PadicMeasure.isSupportedOn_units_iff_psi_eq_zero")
A measure $`\mu \in \Lam(\Zp)` is supported on $`\Zpx` iff $`\psi(\Am_\mu) = 0`.
:::

:::proof "meas-supported-on-units"
By {uses "meas-phi-psi-identities"}[], $`\mu = \Res_{\Zpx}(\mu)` iff
$`\Am_\mu = \Am_\mu - \varphi\psi(\Am_\mu)`, i.e. $`\varphi\psi(\Am_\mu) = 0`. As
$`\varphi` is injective on power series this is equivalent to $`\psi(\Am_\mu) = 0`.
:::

:::proposition "meas-iota-units" (lean := "PadicMeasure.iota, PadicMeasure.iota_injective, PadicMeasure.mem_range_iota_iff")
There is an injection $`\iota : \Lam(\Zpx) \hookrightarrow \Lam(\Zp)` with
$`\int_{\Zp} \phi \cdot \iota(\mu) = \int_{\Zpx} \phi|_{\Zpx} \cdot \mu`,
identifying $`\Lam(\Zpx)` with the measures supported on $`\Zpx`, i.e. those with
$`\psi(\mu) = 0` (by {uses "meas-supported-on-units"}[]). This is *not* a
subalgebra: convolution on $`\Zpx` uses the multiplicative structure,
$$`\int_{\Zpx} f(x) \cdot (\mu *_{\Zpx} \lambda) = \int_{\Zpx}\left(\int_{\Zpx} f(xy) \cdot \mu(x)\right) \cdot \lambda(y),`
whereas convolution on $`\Zp` is additive (cf. {uses "meas-convolution"}[]).
:::

:::proof "meas-iota-units"
Since $`\Res_{\Zpx} \circ \iota` is the identity on $`\Lam(\Zpx)`, the map $`\iota`
is injective and its image is exactly the measures fixed by $`\Res_{\Zpx}`, which by
{uses "meas-supported-on-units"}[] are those with $`\psi = 0`. That the
multiplicative and additive convolutions differ is immediate from their defining
formulas, so the inclusion is only $`\OL`-linear, not multiplicative.
:::

# Pseudo-measures

The Mahler transform matches measures with *bounded* analytic functions on the open
unit disc. The Riemann zeta function has a simple pole at $`s = 1`, so we must allow
simple poles on the $`p`-adic side; this is the role of pseudo-measures.

:::definition "pseudo-measure" (lean := "PadicMeasure.IsPseudoMeasure")
Let $`G` be profinite abelian and $`Q(G)` the ring of fractions of the Iwasawa
algebra {uses "iwasawa-algebra"}[]. A *pseudo-measure* on $`G` is an element
$`\lambda \in Q(G)` such that $`([g] - [1])\lambda \in \Lam(G)` for every
$`g \in G` (product = convolution {uses "meas-convolution"}[]).
:::

:::definition "meas-integrate-pseudo"
For a non-trivial character $`\chi : G \to \Cp^\times` and a pseudo-measure
$`\lambda`, define
$$`\int_G \chi \cdot \lambda := (\chi(g) - 1)^{-1} \int_G \chi \cdot ([g] - [1])\lambda,`
for any $`g` with $`\chi(g) \neq 1`. Uses {uses "pseudo-measure"}[].
:::

:::proposition "meas-integrate-pseudo-welldef"
The value $`\int_G \chi \cdot \lambda` of {uses "meas-integrate-pseudo"}[] is
independent of the chosen $`g`.
:::

:::proof "meas-integrate-pseudo-welldef"
Because $`\mu \mapsto \int_G \chi \cdot \mu` is a ring homomorphism
$`\Lam(G) \to \Cp` (convolution becomes multiplication, $`\chi` being a character),
for $`g, h` with $`\chi(g), \chi(h) \neq 1` one computes
$`(\chi(h)-1)\int_G \chi\cdot([g]-[1])\lambda = \int_G \chi\cdot([g]-[1])([h]-[1])\lambda = (\chi(g)-1)\int_G \chi\cdot([h]-[1])\lambda`,
using commutativity. Dividing through shows the two definitions agree. Equivalently,
the homomorphism $`\Lam(G) \to \Cp` extends uniquely to $`Q(G) \to \Cp`, and its
value on $`\lambda` is the expression above.
:::

:::proposition "meas-pseudo-determined" (lean := "PadicMeasure.eq_zero_of_forall_unitsPowCM_eq_zero, PadicMeasure.mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero, PadicMeasure.pseudoMeasure_eq_zero_of_moments")
Let $`\mu \in \Lam(\Zpx)`. (i) If $`\int_{\Zpx} x^k \cdot \mu = 0` for all $`k > 0`,
then $`\mu = 0`. (ii) If $`\int_{\Zpx} x^k \cdot \mu \neq 0` for all $`k > 0`, then
$`\mu` is not a zero divisor in $`\Lam(\Zpx)`. (iii) Part (i) holds more generally
for a pseudo-measure $`\mu`. In particular a pseudo-measure on $`\Zpx` is determined
by the values $`\int_{\Zpx} x^k \cdot \mu`, $`k > 0`.
:::

:::proof "meas-pseudo-determined"
(i) Each $`\binomc{x}{k}` with $`k \geq 1` is a combination of positive powers of
$`x`, so the vanishing forces $`\Am_\mu(T)` to be constant. As $`\mu` is supported
on $`\Zpx`, {uses "meas-supported-on-units"}[] gives $`\psi(\Am_\mu) = 0`; but $`\psi`
fixes constants (by the formula in {uses "meas-phi-psi-identities"}[]), so the
constant is $`0`, i.e. $`\Am_\mu = 0` and $`\mu = 0`.
(ii) If $`\mu *_{\Zpx} \lambda = 0`, then for each $`k`,
$`0 = \int_{\Zpx} x^k(\mu *_{\Zpx}\lambda) = (\int_{\Zpx} x^k\mu)(\int_{\Zpx} x^k\lambda)`
by multiplicativity of $`x^k` over the convolution {uses "meas-iota-units"}[]; the
hypothesis forces $`\int_{\Zpx} x^k \lambda = 0` for all $`k`, so $`\lambda = 0` by
(i). (iii) For a pseudo-measure $`\mu` and an integer $`a \neq 1` prime to $`p`,
$`\lambda = ([a]-[1])\mu` is a measure with
$`\int_{\Zpx} x^k \lambda = (a^k - 1)\int_{\Zpx} x^k \mu = 0`, so $`\lambda = 0` by
(i); since $`[a]-[1]` satisfies (ii) it is not a zero divisor, forcing $`\mu = 0`.
:::

:::definition "meas-augmentation-ideal" (lean := "PadicMeasure.deg, PadicMeasure.augmentationIdeal")
The *augmentation ideal* $`I((\Z/p^n\Z)^\times) \subset \OL[(\Z/p^n\Z)^\times]` is the
kernel of the degree map $`\sum_a c_a [a] \mapsto \sum_a c_a`. These assemble into a
degree map $`\Lam(\Zpx) \to \OL`, whose kernel is the *augmentation ideal*
$`I(\Zpx) \subset \Lam(\Zpx)`, and $`I(\Zpx) \cong \varprojlim_n I((\Z/p^n\Z)^\times)`.
:::

:::proposition "meas-pseudo-existence" (lean := "PadicMeasure.exists_topological_generator, PadicMeasure.augmentationIdeal_eq_span, PadicMeasure.isPseudoMeasure_mk', PadicMeasure.isPseudoMeasure_iff_exists")
Let $`a` be a topological generator of $`\Zpx` and $`\mu \in \Lam(\Zpx)` a measure.
Then $`\mu' := \mu / ([a] - [1]) \in Q(\Zpx)` is a pseudo-measure. Conversely every
pseudo-measure has this shape. This uses {uses "pseudo-measure"}[] and
{uses "meas-augmentation-ideal"}[].
:::

:::proof "meas-pseudo-existence"
As $`p` is odd, $`(\Z/p^n\Z)^\times` is cyclic generated by $`\bar a = a \bmod p^n`,
so $`I((\Z/p^n\Z)^\times) = ([\bar a]-[\bar 1])\,\OL[(\Z/p^n\Z)^\times]`. Passing to the
limit, $`I(\Zpx) = ([a]-[1])\Lam(\Zpx)`. Hence for any $`g \in \Zpx` we may write
$`[g]-[1] = \nu([a]-[1])` with $`\nu \in \Lam(\Zpx)`, and then
$`([g]-[1])\mu' = \nu([a]-[1])\mu' = \nu \cdot \mu \in \Lam(\Zpx)`, so $`\mu'` is a
pseudo-measure. Conversely, if $`\mu'` is a pseudo-measure then by definition
$`\mu := ([a]-[1])\mu'` is a measure, and $`\mu' = \mu/([a]-[1])`.
:::

# Locally analytic functions and distributions

Finally we sketch *locally analytic distributions*, the dual of locally analytic
functions, which extend the Mahler correspondence from $`\OL[[T]]` to all
everywhere-convergent power series on the open unit disc. This section is used only
peripherally (to study values of $`\zeta_p` near $`s = 1`).

:::definition "meas-rigid-analytic"
The $`p`-adic open unit ball is $`B(0,1) = \set{z \in \Cp : \abs{z} < 1}`. An
$`L`-valued function on $`B(0,1)` is *rigid analytic* if it is given by a power
series $`\sum_n a_n T^n \in L[[T]]` everywhere convergent on $`B(0,1)`
(i.e. $`\abs{a_n} r^n \to 0` for all $`r < 1`); write $`\rp \subset L[[T]]` for
these. A rigid analytic function is *bounded* if the $`\abs{a_n}` are bounded.
:::

The bounded rigid analytic functions form $`\OL[[T]] \otimes_{\OL} L`, which by
{bpref "iwasawa-isomorphism"}[] is $`\sM(\Zp, L)`: measures on $`\Zp` are precisely
the *bounded* rigid analytic functions on $`B(0,1)`. It is natural to drop
boundedness, extending the correspondence to all of $`\rp`.

:::definition "meas-locally-analytic"
A function $`f : \Zp \to L` is *locally analytic at $`z`* if there exist $`n_z \geq 0`
and $`a_k(z) \in L` with $`\sum_{k} a_k(z)(x-z)^k = f(x)` for all
$`x \in z + p^{n_z}\Zp`; it is *locally analytic* if so at every $`z \in \Zp`. Write
$`\cCla(\Zp, L)` for the $`L`-vector space of such functions. Setting
$`\cC^{n\text{-an}}(\Zp, L)` to be those with a uniform radius $`n_z = n` — a Banach
space under $`\norm{f}_n = \sup_{z} \sup_k \abs{a_k(z)} p^{-nk}` — one has
$`\cCla(\Zp, L) = \varinjlim_n \cC^{n\text{-an}}(\Zp, L)` with the direct limit
topology.
:::

Locally analytic functions are continuous, so $`\cCla(\Zp, L) \subset \cC(\Zp, L)`
densely (locally constant functions are locally analytic), though the locally
analytic topology is finer than the induced one.

:::definition "locally-analytic-distribution"
The space $`\sDla(\Zp, L)` of *locally analytic distributions* on $`\Zp` is the
continuous dual $`\mathrm{Hom}_{\mathrm{cts}}(\cCla(\Zp, L), L)`, using
{uses "meas-locally-analytic"}[]. We write $`\int_{\Zp} \phi \cdot \mu := \mu(\phi)`
and, since the binomial polynomials {uses "meas-binomial-polynomials"}[] are locally
analytic, extend the Mahler transform by
$`\Am_\mu(T) = \int_{\Zp}(1+T)^x \cdot \mu = \sum_n (\int_{\Zp}\binomc{x}{n}\cdot\mu) T^n \in L[[T]]`.
:::

:::theorem "meas-mahler-la"
The Mahler transform induces a bijection
$$`\sDla(\Zp, L) \xrightarrow{\ \sim\ } \rp \subset L[[T]],`
an isomorphism of Fréchet spaces. This extends {uses "iwasawa-isomorphism"}[] and
rests on {uses "locally-analytic-distribution"}[] and {uses "meas-rigid-analytic"}[].
:::

:::proof "meas-mahler-la"
This is a theorem of Amice–Colmez. Both sides are inverse limits of Banach spaces.
On the function side, $`\cCla = \varinjlim_n \cC^{n\text{-an}}`, so
$`\sDla = \varprojlim_n \sD^{n\text{-an}}` with each $`\sD^{n\text{-an}}` a Banach
space under the strong dual topology. On the power-series side, $`B(0,1)` is the
increasing union of the closed discs $`B(0,r)`, $`r < 1`, so
$`\rp = \varprojlim_{r < 1} \cO(B(0,r))` is an inverse limit of Banach spaces of
analytic functions; both carry Fréchet topologies. The growth condition
$`\abs{a_n} r^n \to 0` defining $`\rp` is exactly dual to the radius-$`p^{-n}`
analyticity norms on $`\cC^{n\text{-an}}`, so the term-by-term Mahler map is a
topological isomorphism at each level and hence in the limit.
:::

Restricting a measure $`\mu \in \sM(\Zp, L)` to $`\cCla(\Zp, L)` gives a locally
analytic distribution $`\widetilde\mu`; by density of $`\cCla` this is injective, so
$`\sM(\Zp, L) \subset \sDla(\Zp, L)`. Comparing {bpref "iwasawa-isomorphism"}[] with
{bpref "meas-mahler-la"}[], this matches the inclusion of bounded power series
$`\OL[[T]] \otimes_{\OL} L \subset \rp`. Every operation of the toolbox carries over
verbatim to distributions.

:::proposition "meas-weight-space"
There is a multiplicative analogue for $`\Zpx`. The *weight space* is
$`\cW(\Cp) = \mathrm{Hom}_{\mathrm{cts}}(\Zpx, \Cp^\times)`; using
$`\Zpx \cong \mu_{p-1} \times (1 + p\Zp)`, evaluation at a topological generator of
$`1 + p\Zp` identifies it with $`p - 1` copies of $`B(0,1)`,
$`\cW(\Cp) = \bigsqcup_{\nu \in (\mu_{p-1})^\vee} U_\nu`. A measure
$`\mu` on $`\Zpx` is the bounded rigid analytic function
$`F_\mu(\chi) = \int_{\Zpx} \chi \cdot \mu` on $`\cW`, multiplicative convolution
becoming pointwise multiplication; a pseudo-measure {uses "pseudo-measure"}[] is then
a rigid function on $`\cW` with at worst a simple pole at the trivial character.
:::

:::proof "meas-weight-space"
The decomposition $`\Zpx \cong \mu_{p-1} \times (1+p\Zp)` splits a continuous
character into its restriction to the torsion part $`\mu_{p-1}` (one of $`p-1`
characters $`\nu`) and to the pro-$`p` part $`1+p\Zp`; evaluating the latter at a
fixed topological generator lands in $`B(0,1)`, giving the disjoint-union
description. The pairing $`\chi \mapsto \int_{\Zpx} \chi \cdot \mu` is, by the
multiplicative analogue of {uses "iwasawa-isomorphism"}[] (Amice), a bounded rigid
function on $`\cW`, and convolution dualises to multiplication. For a pseudo-measure
$`\lambda = \mu/([a]-[1])` with $`a` a topological generator,
$`\int_{\Zpx} \chi \cdot ([a]-[1]) = \chi(a) - 1` vanishes only when $`\chi(a) = 1`,
i.e. for the trivial character; hence $`\lambda` is analytic away from the trivial
character, where it may have a simple pole, by {uses "meas-pseudo-existence"}[].
:::
