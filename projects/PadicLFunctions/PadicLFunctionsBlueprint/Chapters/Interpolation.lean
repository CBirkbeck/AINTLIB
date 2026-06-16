import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Interpolation at Dirichlet characters" =>

The Kubota–Leopoldt pseudo-measure $`\zetap` was built purely from values of the
Riemann zeta function, with Dirichlet characters never entering the construction.
Remarkably, $`\zetap` nonetheless interpolates Dirichlet $`L`-values as well. This
chapter establishes that interpolation, first for characters of $`p`-power
conductor, then for general conductors (where one even obtains a genuine measure
$`\zeta_\eta` rather than a pseudo-measure), and finally repackages everything as
analytic functions on $`\Zp` via the Mellin transform.

Throughout, $`p` is an odd prime, $`(\eps_{p^n})_{n}` is a compatible system of
primitive $`p^n`-th roots of unity in $`\Qpbar` (so $`\eps_{p^{n+1}}^p =
\eps_{p^n}`), and $`L/\Qp` is a finite extension large enough to contain the values
of the characters under consideration, with ring of integers $`\cO_L`. A Dirichlet
character $`\chi` of conductor $`p^n` is viewed, via $`\Zpx \twoheadrightarrow
(\Z/p^n\Z)^\times`, as a locally constant character of $`\Zpx`. We write $`\Am_\mu`
for the Mahler transform of a measure $`\mu` and recall the standard substitution
$`e^t = T+1` relating power series to functions of a real variable.

# Characters of p-power conductor

The headline result twists $`\zetap` by a Dirichlet character of $`p`-power
conductor. Its proof runs the construction of $`\zetap` *in reverse*: a twisted
measure is built, its Mahler transform is computed, the corresponding function of
$`t` is identified with a complex $`L`-function via the Mellin transform, and the
special-value formula is read off.

:::theorem "interpolation-property" (lean := "PadicLFunctions.MeasureR.tame_conductor, PadicLFunctions.MeasureR.tame_conductor_theta, PadicLFunctions.MeasureR.twist_muA_moments")
Let $`\chi` be a primitive Dirichlet character of conductor $`p^n`, $`n \geq 1`,
viewed as a locally constant character of $`\Zpx`. Then for every integer $`k > 0`,
$$`\int_{\Zpx}\chi(x)\,x^k \cdot \zetap = L(\chi, 1-k).`
This depends on {uses "kubota-leopoldt"}[], {uses "interp-twist"}[],
{uses "interp-dirichlet-integral"}[] and {uses "dirichlet-L-function"}[].

In the formalisation the pairing with $`\zetap` follows the witness encoding of
`PadicMeasure.kubotaLeopoldt`: `tame_conductor` states that every
measure-witness `ν` of $`([b]-[1])\zetap` has χ-twisted moments
$`(\chi(b)b^k - 1)\,L(\chi,1-k)`; the engine is the θ-form
`tame_conductor_theta` ($`\int \chi(x)x^k\,\theta_a = -(1-\chi(a)a^k)L(\chi,1-k)`,
the source's own display) and the moment formula `twist_muA_moments`. The
value $`L(\chi,1-k)` is the generalised Bernoulli expression `LvalNeg`
(complex comparison: `LFunction_neg_nat`), and a primitive `p^n`-th root of
unity in the coefficient field is assumed, mirroring the source's ambient
$`\eps_{p^n}`.
:::

:::proof "interpolation-property"
Since $`\chi` vanishes on $`p\Zp`, integrating over $`\Zpx` is the same as
integrating over $`\Zp`, and by the definition of the twist {uses "interp-twist"}[]
this equals $`\int_{\Zp} x^k \cdot \mu_{\chi,a}`, where $`\mu_{\chi,a}` is the
twist of the measure $`\mua` by $`\chi`. Under $`e^t = T+1` this integral is
$`(\partial^k F_{\chi,a})(0) = f_{\chi,a}^{(k)}(0)`. By
{uses "interp-dirichlet-integral"}[] we obtain
$`\int_{\Zpx}\chi(x)x^k\cdot\mua = -(1-\chi(a)a^{k+1})L(\chi,-k)`, and integrating
against $`x^{-1}` shifts this to
$`\int_{\Zpx}\chi(x)x^k \cdot x^{-1}\mua = -(1-\chi(a)a^{k})L(\chi,1-k)`. The
smoothing measure $`\theta_a` used in the construction of $`\zetap` satisfies
$`\int_{\Zpx}\chi(x)x^k\cdot\theta_a = -(1-\chi(a)a^{k})`; dividing the previous
identity by this Euler-type factor cancels the $`(1-\chi(a)a^k)` exactly and leaves
$`\int_{\Zpx}\chi(x)x^k\cdot\zetap = L(\chi,1-k)`, as claimed.
:::

We first record the twisting operation and the classical Gauss-sum input it
requires, then compute the Mahler transform of a twist.

:::definition "interp-twist" (lean := "PadicLFunctions.MeasureR.twist, PadicLFunctions.MeasureR.twist_res_units")
Let $`\mu` be a measure on $`\Zp` and $`\chi` a locally constant character of
$`\Zpx`. The *twist of $`\mu` by $`\chi`* is the measure $`\mu_\chi` on $`\Zp`
defined by
$$`\int_{\Zp} f(x)\cdot\mu_\chi = \int_{\Zp}\chi(x)f(x)\cdot\mu.`
Because $`\chi` is supported on $`\Zpx`, the measure $`\mu_\chi` is automatically
supported on $`\Zpx`.

The formalisation defines the twist by an arbitrary continuous function
(`MeasureR.twist`, specialised to Dirichlet characters through their
zero-extension `DirichletCharacter.toContinuousMapZp`); the automatic support
statement is the restriction-invariance lemma `twist_res_units`.
:::

:::definition "interp-gauss-sum" (lean := "gaussSum")
Let $`\chi` be a primitive Dirichlet character of conductor $`p^n`, $`n \geq 1`.
The *Gauss sum* of $`\chi` is
$$`G(\chi) := \sum_{c \in (\Z/p^n\Z)^\times} \chi(c)\,\eps_{p^n}^{\,c},`
where $`(\eps_{p^n})_n` is the fixed compatible system of primitive $`p`-power
roots of unity in $`\Qpbar` (one may take $`\eps_{p^n} = e^{2\pi i/p^n}` under a
fixed isomorphism $`\Qpbar \cong \C`).
:::

:::lemma_ "interp-gauss-sum-properties"
The Gauss sum of a primitive Dirichlet character $`\chi` of conductor $`p^n`
satisfies two basic identities. *(i)* $`G(\chi)\,G(\chi^{-1}) = \chi(-1)\,p^n`; in
particular $`G(\chi)` is nonzero. *(ii)* For every $`a \in \Zpx`, $`G(\chi) =
\chi(a)\sum_{c\in(\Z/p^n\Z)^\times}\chi(c)\,\eps_{p^n}^{\,ac}`. This rests on
{uses "interp-gauss-sum"}[].
:::

:::proof "interp-gauss-sum-properties"
These are standard facts on Gauss sums. For (ii), substituting $`c \mapsto a^{-1}c`
in the defining sum and using multiplicativity of $`\chi` rewrites $`\sum_c
\chi(c)\eps_{p^n}^{ac}` as $`\chi(a)^{-1}\sum_c \chi(c)\eps_{p^n}^{c} =
\chi(a)^{-1}G(\chi)`, which rearranges to the stated identity (the change of
variables is a bijection of $`(\Z/p^n\Z)^\times` since $`a` is a unit). For (i),
expand $`G(\chi)G(\chi^{-1})` as a double sum over $`(\Z/p^n\Z)^\times`, change
variables to separate the additive characters, and evaluate the resulting
character sums; the cross terms cancel and the diagonal contributes $`\chi(-1)p^n`.
Nonvanishing of $`G(\chi)` is immediate from (i) since $`\chi(-1)p^n \neq 0`.
:::

:::lemma_ "interp-mahler-twist" (lean := "PadicLFunctions.MeasureR.mahler_twist_formula")
Let $`\chi` be a primitive Dirichlet character of conductor $`p^n`, $`n \geq 1`,
and $`\mu` a measure on $`\Zp`. Then the Mahler transform of the twist $`\mu_\chi`
is
$$`\Am_{\mu_\chi}(T) = \frac{1}{G(\chi^{-1})}\sum_{c\in(\Z/p^n\Z)^\times}
\chi(c)^{-1}\,\Am_\mu\big((1+T)\eps_{p^n}^{\,c} - 1\big).`
This uses {uses "interp-twist"}[], {uses "interp-gauss-sum"}[],
{uses "interp-gauss-sum-properties"}[] and {uses "mahler-transform"}[].

The formalisation states this multiplied through by the Gauss sum
$`G(\chi^{-1})` and as an identity of measures (`mahler_twist_formula`):
$`G(\chi^{-1})\cdot\mu_\chi = \sum_c \chi^{-1}(c)\,\kappa_{\eps^c-1}\mu`, the
sum running over all residues (the character kills the non-units); applying
the Mahler transform recovers the display.
:::

:::proof "interp-mahler-twist"
Since $`\chi` is constant modulo $`p^n`, the twist decomposes as a weighted sum of
restrictions, $`\mu_\chi = \sum_{c\in(\Z/p^n\Z)^\times}\chi(c)\,\Res_{c+p^n\Zp}(\mu)`.
Applying the formula for the Mahler transform of a restriction to $`b + p^n\Zp`,
$$`\Am_{\Res_{b+p^n\Zp}(\mu)}(T) = \frac{1}{p^n}\sum_{\xi\in\mu_{p^n}}
\xi^{-b}\,\Am_\mu\big((1+T)\xi - 1\big),`
and summing over $`b`, we get
$`\Am_{\mu_\chi}(T) = p^{-n}\sum_{b}\chi(b)\sum_{\xi\in\mu_{p^n}}\xi^{-b}
\Am_\mu((1+T)\xi-1)`. Writing each $`\xi = \eps_{p^n}^{c}` and interchanging the
sums, the inner sum over $`b` becomes $`\sum_b \chi(b)\eps_{p^n}^{-bc}`, which by
{uses "interp-gauss-sum-properties"}[](ii) equals $`G(\chi)\chi(-c)^{-1}`. Thus
$`\Am_{\mu_\chi}(T) = p^{-n}\sum_c G(\chi)\chi(-c)^{-1}\Am_\mu((1+T)\eps_{p^n}^c-1)`,
and substituting $`G(\chi)/p^n = \chi(-1)/G(\chi^{-1})` from
{uses "interp-gauss-sum-properties"}[](i) together with $`\chi(-c)^{-1} =
\chi(-1)\chi(c)^{-1}` gives the claimed formula.
:::

Specialising to $`\mu = \mua` — the measure with $`\Am_{\mua}(T) = \tfrac1T -
\tfrac{a}{(1+T)^a - 1}` from which $`\zetap` was built — and substituting $`e^t =
T+1` motivates the study of the auxiliary function
$$`f_{\chi,a}(t) = \frac{1}{G(\chi^{-1})}\sum_{c\in(\Z/p^n\Z)^\times}\chi(c)^{-1}
\left[\frac{1}{e^t\eps_{p^n}^{\,c} - 1} - \frac{a}{e^{at}\eps_{p^n}^{\,ac} -
1}\right].`

-- Deliberately unwired (§5 board, 2026-06-10): the Mellin/analytic-continuation
-- half of this lemma is §2 material (deferred), following the
-- `kl-values-of-zeta` pattern. The L-value content the §5 statements consume is
-- encoded algebraically as `LvalNeg` (minus the (k+1)-st generalised Bernoulli
-- number over (k+1), `GenBernoulli.lean`), with the complex comparison
-- `PadicLFunctions.LFunction_neg_nat` (`GenBernoulliComplex.lean`, all k ≥ 0;
-- the k = 0 case rests on the sawtooth boundary value
-- `sinZeta_one_eq_boundary`, `Sawtooth.lean`).
:::lemma_ "interp-dirichlet-integral"
With $`f_{\chi,a}` as above and $`L(f,s) = \frac{1}{\Gamma(s)}\int_0^\infty
f(t)t^{s-1}dt` the complex Mellin transform (whose special-value formula
$`L(f,-n)=(-1)^n f^{(n)}(0)` was established earlier), we have
$$`L(f_{\chi,a}, s) = \chi(-1)\big(1-\chi(a)a^{1-s}\big)\,L(\chi,s).`
Moreover, for $`k \geq 0`,
$$`f_{\chi,a}^{(k)}(0) = \begin{cases} -\big(1-\chi(a)a^{k+1}\big)L(\chi,-k) &
\chi(-1)(-1)^k = -1,\\ 0 & \chi(-1)(-1)^k = 1.\end{cases}`
This uses {uses "interp-mahler-twist"}[] and {uses "dirichlet-L-function"}[].
:::

:::proof "interp-dirichlet-integral"
Expanding each summand as a geometric series, $`\frac{1}{e^t\eps_{p^n}^c - 1} =
\sum_{k\geq 1} e^{-kt}\eps_{p^n}^{-kc}`, and feeding this into the Mellin integral
$`L(f_{\chi,a},s) = \frac{1}{\Gamma(s)}\int_0^\infty f_{\chi,a}(t)t^{s-1}dt`, the
inner character sum $`\sum_c \chi(c)^{-1}\eps_{p^n}^{-akc}` collapses to
$`\chi(-ak)G(\chi^{-1})` (and similarly for the first term), cancelling the
$`G(\chi^{-1})` in the denominator. The integral reduces to
$`\frac{1}{\Gamma(s)}\int_0^\infty\sum_{k\geq1}\chi(-k)(e^{-kt}-\chi(a)e^{-akt})
t^{s-1}dt`. For $`\Re(s)\gg 0` one may interchange sum and integral; the $`k`-th
term integrates to $`(1-\chi(a)a^{1-s})k^{-s}`, yielding $`\chi(-1)(1-\chi(a)
a^{1-s})\sum_{k\geq1}\chi(-k)k^{-s} = \chi(-1)(1-\chi(a)a^{1-s})L(\chi,s)`. This is
entirely classical: $`p` never appears. The Mellin special-value formula then gives
$`f_{\chi,a}^{(k)}(0) = (-1)^k\chi(-1)(1-\chi(a)a^{k+1})L(\chi,-k)`.

For the parity dichotomy, the identity $`\frac{1}{e^{-t}\eps_{p^n}^c - 1} = -1 -
\frac{1}{e^t\eps_{p^n}^{-c}-1}` applied twice, followed by the substitution
$`c\mapsto -c`, shows $`f_{\chi,a}(-t) = -\chi(-1)f_{\chi,a}(t)`. Comparing $`k`-th
derivatives at $`0` gives $`(-1)^k f_{\chi,a}^{(k)}(0) = -\chi(-1)f_{\chi,a}^{(k)}
(0)`, forcing $`f_{\chi,a}^{(k)}(0) = 0` unless $`\chi(-1)(-1)^k = -1`. (In
particular this recovers the classical vanishing $`L(\chi,-k)=0` when
$`\chi(-1)(-1)^k = 1`.)
:::

# Non-trivial tame conductors

The previous theorem treats *tame conductor $`1`*. One can do better: for a
Dirichlet character $`\eta` of conductor $`D > 1` coprime to $`p`, there is a
genuine measure interpolating the twisted values $`L(\chi\eta, 1-k)`. Because
$`L`-functions of non-trivial characters are entire, no smoothing factor is needed
and one obtains a measure rather than a pseudo-measure.

:::definition "interp-mu-eta" (lean := "PadicLFunctions.MeasureR.muEtaCleared, PadicLFunctions.MeasureR.mahlerTransform_muEtaCleared, PadicLFunctions.MeasureR.isUnit_root_mul_one_add_X_sub_one, PadicLFunctions.MeasureR.gaussSum_isUnit_of_coprime")
Let $`D > 1` be coprime to $`p` and $`\eta` a primitive Dirichlet character of
conductor $`D`. Because no smoothing factor is needed (the relevant $`L`-function
is entire), set
$$`f_\eta(t) := \frac{-1}{G(\eta^{-1})}\sum_{c\in(\Z/D\Z)^\times}
\frac{\eta(c)^{-1}}{e^t\eps_D^c - 1},`
where the Gauss sum $`G(\eta^{-1})` is defined as before with $`p^n` replaced by
$`D`. Substituting $`e^t = T+1` and expanding the geometric series gives
$$`F_\eta(T) := \frac{-1}{G(\eta^{-1})}\sum_{c\in(\Z/D\Z)^\times}
\frac{\eta(c)^{-1}}{(1+T)\eps_D^c - 1} = \frac{-1}{G(\eta^{-1})}
\sum_{c\in(\Z/D\Z)^\times}\eta(c)^{-1}\sum_{k\geq 0}\frac{\eps_D^{kc}}
{(\eps_D^c-1)^{k+1}}\,T^k.`
This lies in $`\cO_L[[T]]` for a sufficiently large finite extension $`L/\Qp`
containing the values of $`\eta`: the Gauss sum is a $`p`-adic unit because
$`G(\eta)G(\eta^{-1}) = \eta(-1)D` with $`D` coprime to $`p`, and $`\eps_D^c - 1
\in \cO_L^\times` (its norm divides $`D`). Let $`\mu_\eta \in \Lam(\Zp)` be the
measure with Mahler transform $`\Am_{\mu_\eta} = F_\eta`. This uses
{uses "interp-gauss-sum"}[] and {uses "mahler-transform"}[].

In the formalisation the measure is carried in cleared form:
`muEtaCleared` is $`-G(\eta^{-1})\,F_\eta` read back through the Mahler
isomorphism (`mahlerTransform_muEtaCleared`), so the Gauss-sum
normalisation appears explicitly in each statement rather than as a
division in the definition. The two unit facts of the node are
`isUnit_root_mul_one_add_X_sub_one` ($`(1+T)\eps_D^c-1 \in
\cO_L[[T]]^\times`) and `gaussSum_isUnit_of_coprime` ($`G(\eta^{-1}) \in
\cO_L^\times`); the sum ranges over all of $`\Z/D\Z`, the non-unit terms
vanishing since $`\eta^{-1}` is zero there.
:::

:::theorem "interp-nontame" (lean := "PadicLFunctions.MeasureR.zetaEta_twisted_moments, PadicLFunctions.MeasureR.eq_of_twisted_moments_eq, PadicLFunctions.MeasureR.eq_zero_of_twisted_moments_eq_zero")
Let $`D > 1` be an integer coprime to $`p` and $`\eta` a primitive Dirichlet
character of conductor $`D`. There is a unique measure $`\zeta_\eta \in
\Lam(\Zpx)` over the Iwasawa algebra defined over a finite extension $`L/\Qp`
containing the values of $`\eta`, such that for every primitive Dirichlet character
$`\chi` of conductor $`p^n`, $`n \geq 0`, and every $`k > 0`,
$$`\int_{\Zpx}\chi(x)\,x^k\cdot\zeta_\eta = \big(1 - \chi\eta(p)\,p^{k-1}\big)
L(\chi\eta, 1-k).`
This rests on {uses "interp-zeta-eta"}[], {uses "interp-eta-restriction"}[],
{uses "interp-mahler-theta"}[] and {uses "dirichlet-L-function"}[].

The two halves are formalised separately. Existence is
`zetaEta_twisted_moments`: the displayed interpolation property for the
explicit measure $`x^{-1}\Res_{\Zpx}(\mu_\eta)`, in cleared form
(multiplied by the unit $`G(\eta^{-1})`), with the value as the
generalised Bernoulli expression `LvalNeg` and the $`x^{-1}`-shift as the
index shift `k ↦ k−1`. Uniqueness is `eq_of_twisted_moments_eq` (via the
determinacy `eq_zero_of_twisted_moments_eq_zero`): unit-supported measures
with equal χ-twisted moments coincide, under the hypothesis that the
coefficient ring contains primitive `p^n`-th roots of unity for every `n`
— the formal reading of the source's "defined over a (fixed) finite
extension `L/ℚ_p` containing the values" with the χ-quantifier ranging
over `R`-valued characters; the prime-to-`p` roots needed for character
orthogonality come from the Teichmüller lift, which `ℤ_p` already
contains. Ambient primitive roots `ε_D`, `ε_{p^n}` are assumed as in the
tame case.
:::

:::proof "interp-nontame"
The argument parallels the $`p`-power case but needs no smoothing factor, since
$`L(\eta,s)` is entire. Starting from the measure $`\mu_\eta` of
{uses "interp-mu-eta"}[], one has by {uses "interp-eta-restriction"}[] the moment
formula $`\int_{\Zpx}x^k\cdot\mu_\eta = (1-\eta(p)p^k)L(\eta,-k)`. Twisting
$`\mu_\eta` by a $`p`-power character $`\chi` and setting $`\theta := \chi\eta`,
the measure $`\mu_\theta := (\mu_\eta)_\chi` has the explicit Mahler transform of
{uses "interp-mahler-theta"}[], and the same calculation gives
$`\int_{\Zpx}\chi(x)x^k\cdot\mu_\eta = (1-\theta(p)p^k)L(\theta,-k)`. Finally
setting $`\zeta_\eta := x^{-1}\Res_{\Zpx}(\mu_\eta)` from {uses "interp-zeta-eta"}[]
shifts the exponent of the Euler factor and the argument of $`L`, yielding
$`\int_{\Zpx}\chi(x)x^k\cdot\zeta_\eta = (1-\theta(p)p^{k-1})L(\theta,1-k)`.
Uniqueness follows from the fact that a measure on $`\Zpx` is determined by its
moments $`\int x^k`.
:::

:::lemma_ "interp-eta-mellin" (lean := "PadicLFunctions.MeasureR.muEtaCleared_moments, PadicLFunctions.MeasureR.X_mul_muEtaCleared_subst")
With $`f_\eta` and $`\mu_\eta` the function and measure of {uses "interp-mu-eta"}[],
we have $`L(f_\eta, s) = -\eta(-1)L(\eta, s)`, and hence for $`k \geq 0`,
$$`\int_{\Zp}x^k\cdot\mu_\eta = L(\eta, -k).`
This uses {uses "interp-mu-eta"}[] and {uses "dirichlet-L-function"}[].

The formalisation proves the displayed moment formula in cleared form:
`muEtaCleared_moments` gives $`\int x^k \cdot (-G(\eta^{-1})\mu_\eta) =
G(\eta^{-1})\,L(\eta,-k)` with the value encoded as the generalised
Bernoulli expression `LvalNeg`, by extracting the $`(k+1)`-st coefficient
of the formal master identity `X_mul_muEtaCleared_subst`
($`t\,G(\eta^{-1})f_\eta(t)` equals the generating function of
$`-B_{k,\eta}`) — the purely $`p`-adic route through the
generalised-Bernoulli generating function `genBernoulliPowerSeries_mul`,
avoiding the complex Mellin detour. The
first display ($`L(f_\eta,s) = -\eta(-1)L(\eta,s)`, an identity of
complex $`L`-functions) is the analytic half quarantined as in
{uses "interp-dirichlet-integral"}[] and is not formalised.
:::

:::proof "interp-eta-mellin"
The $`L`-function identity is proved exactly as in {uses "interp-dirichlet-integral"}[]:
expanding $`1/(e^t\eps_D^c-1)` as a geometric series and collapsing the character
sum over $`(\Z/D\Z)^\times` against the additive characters reduces $`L(f_\eta,s)`
to $`-\eta(-1)L(\eta,s)` (the overall sign coming from the $`-1` normalisation in
$`f_\eta`). The moment formula follows by identifying the differential operator
$`\partial` with $`d/dt` and applying the Mellin special-value theorem: $`\int_{\Zp}
x^k\cdot\mu_\eta = (\partial^k F_\eta)(0) = f_\eta^{(k)}(0) = (-1)^k L(f_\eta,-k) =
-(-1)^k\eta(-1)L(\eta,-k)`. The same parity argument as in
{uses "interp-dirichlet-integral"}[] shows $`f_\eta(-t) = -\eta(-1)f_\eta(t)`, so
$`L(\eta,-k)` vanishes unless $`\eta(-1)(-1)^k = -1`, on which locus the prefactor
$`-(-1)^k\eta(-1)` equals $`1`; hence $`\int_{\Zp}x^k\cdot\mu_\eta = L(\eta,-k)`.
:::

:::lemma_ "interp-psi-twisted" (lean := "PadicLFunctions.MeasureR.psi_muEtaCleared, PadicLFunctions.MeasureR.psi_phi_mul, PadicLFunctions.MeasureR.psi_symm_inverse_denom")
The power series $`F_\eta` of {uses "interp-mu-eta"}[] satisfies $`\psi(F_\eta) =
\eta(p)\,F_\eta`, where $`\psi` is the trace-like operator on power series adjoint
to $`\varphi : G(T) \mapsto G((1+T)^p - 1)`. This uses {uses "interp-mu-eta"}[].

The formalised proof (`psi_muEtaCleared`, stated for the cleared measure)
takes a $`\mu_p`-free route equivalent to the displayed trace computation:
the cleared identity $`\varphi(\eps^{pc}\delta_1 - \delta_0)\cdot\gamma_c =
\sum_{j<p}\eps^{cj}\delta_j` (geometric telescope), the projection formula
$`\psi(\varphi(\nu)\mu) = \nu\,\psi(\mu)` (`psi_phi_mul`), and
$`\psi(\delta_j) = 0` for `j` a unit give `psi_symm_inverse_denom`
($`\psi(\gamma_c) = \gamma_{pc}`); the reindex `c ↦ pc` on $`\Z/D` then
twists the weight by $`\eta(p)`. This avoids adjoining the $`p`-th roots
of unity that the displayed $`\frac1p\sum_{\xi\in\mu_p}` computation needs,
and `η` need not be primitive.
:::

:::proof "interp-psi-twisted"
The key local computation is $`\frac1p\sum_{\xi\in\mu_p}\frac{1}{(1+T)\xi\eps_D^c -
1} = \frac{1}{(1+T)^p\eps_D^{pc}-1}`: expanding the left side as a geometric series,
$`\frac{-1}{p}\sum_{\xi}\sum_{n\geq0}(1+T)^n\eps_D^{nc}\xi^n`, the inner sum over
$`\xi\in\mu_p` annihilates every term with $`p \nmid n`, leaving $`-\sum_n
(1+T)^{pn}\eps_D^{pcn}`, which resums to the right side. Applying this to each
summand of $`F_\eta` shows $`(\varphi\circ\psi)(F_\eta) = \eta(p)\,\varphi(F_\eta)`
(the index $`c \mapsto pc` rescales the character via $`\eta(p)`); by injectivity
of $`\varphi` we conclude $`\psi(F_\eta) = \eta(p)F_\eta`.
:::

:::lemma_ "interp-eta-restriction" (lean := "PadicLFunctions.MeasureR.res_units_muEtaCleared_moments")
For all $`k \geq 0`,
$$`\int_{\Zpx}x^k\cdot\mu_\eta = \big(1-\eta(p)\,p^k\big)\,L(\eta,-k).`
This uses {uses "interp-psi-twisted"}[] and {uses "interp-eta-mellin"}[].

Formalised in cleared form (`res_units_muEtaCleared_moments`): the
Gauss-sum normalisation $`G(\eta^{-1})` multiplies both sides, and the
value $`L(\eta,-k)` is the generalised Bernoulli expression `LvalNeg`,
exactly as in the two preceding nodes.
:::

:::proof "interp-eta-restriction"
Restriction to $`\Zpx` is given by $`1 - \varphi\circ\psi`, so by
{uses "interp-psi-twisted"}[], $`\Res_{\Zpx}(\mu_\eta) = (1-\varphi\circ\psi)\mu_\eta
= \mu_\eta - \eta(p)\varphi(\mu_\eta)`. Since $`\int_{\Zp}x^k\cdot\varphi(\mu_\eta) =
p^k\int_{\Zp}x^k\cdot\mu_\eta` (the operator $`\varphi` corresponds to $`x\mapsto
px`), integrating against $`x^k` gives $`\int_{\Zpx}x^k\cdot\mu_\eta = (1-\eta(p)
p^k)\int_{\Zp}x^k\cdot\mu_\eta`, and the result follows from
{uses "interp-eta-mellin"}[].
:::

:::lemma_ "interp-mahler-theta" (lean := "PadicLFunctions.MeasureR.mahlerTransform_charTwist_muEtaCleared, PadicLFunctions.MeasureR.X_mul_twist_muEtaCleared_subst, PadicLFunctions.MeasureR.twist_muEtaCleared_moments")
Let $`\chi` be a Dirichlet character of conductor $`p^n`, $`n\geq 0`, and set
$`\theta := \chi\eta`, a Dirichlet character of conductor $`Dp^n`. Then the measure
$`\mu_\theta := (\mu_\eta)_\chi` has Mahler transform
$$`F_\theta(T) = \frac{-1}{G(\theta^{-1})}\sum_{c\in(\Z/Dp^n\Z)^\times}
\frac{\theta(c)^{-1}}{(1+T)\eps_{Dp^n}^{\,c} - 1}.`
This uses {uses "interp-mahler-twist"}[] and {uses "interp-mu-eta"}[].

The formalisation keeps the transform in the two-index form
`mahlerTransform_charTwist_muEtaCleared` (the `ε_{p^n}^b`-line twists of
the `ε_D^c`-denominators, i.e. the CRT-resolved shape of the displayed
$`(\Z/Dp^n)^\times`-sum, with `θ⁻¹(c)` realised as `η⁻¹(c)χ⁻¹(b)`) and
extracts the consequences directly: the master identity
`X_mul_twist_muEtaCleared_subst` ($`t\,G(\eta^{-1})G(\chi^{-1})f_\theta`
collapses to the generalised-Bernoulli generating function of $`\theta`,
with $`G(\chi^{-1})` cancelling) and the moment formula
`twist_muEtaCleared_moments` ($`\int\chi(x)x^m\,d\mu_\eta =
G(\eta^{-1})L(\theta,-m)`, cleared). The single-root closed form is not
restated separately.
:::

:::proof "interp-mahler-theta"
Apply the twisting formula {uses "interp-mahler-twist"}[] to $`\mu_\eta`, whose
Mahler transform is $`F_\eta(T) = \frac{-1}{G(\eta^{-1})}\sum_{c}\frac{\eta(c)^{-1}}
{(1+T)\eps_D^c-1}`. The composite sum over $`(\Z/p^n\Z)^\times` and
$`(\Z/D\Z)^\times` recombines, via the Chinese Remainder Theorem and the
multiplicativity of Gauss sums, into a single sum over $`(\Z/Dp^n\Z)^\times` with
the product character $`\theta^{-1}` and the root of unity $`\eps_{Dp^n} =
\eps_D\eps_{p^n}`, giving the stated closed form.
:::

:::definition "interp-zeta-eta" (lean := "PadicLFunctions.MeasureR.zetaEtaCleared, PadicLFunctions.MeasureR.zetaEta_twisted_moments")
With $`\mu_\eta` the measure of {uses "interp-mu-eta"}[] attached to $`\eta`,
define
$$`\zeta_\eta := x^{-1}\,\Res_{\Zpx}(\mu_\eta) \in \Lam(\Zpx).`
This is directly analogous to the construction of $`\zetap`, except that
$`\zeta_\eta` is a genuine measure (no pseudo-measure denominator is needed). This
uses {uses "interp-mu-eta"}[] and {uses "interp-eta-restriction"}[].

In the formalisation `zetaEtaCleared` is the genuine measure on `ℤ_p^×`
(pairing `g` integrates `x⁻¹·g`, extended by zero, against the
$`G(\eta^{-1})`-cleared $`\mu_\eta`), and in the moment statements the
`x⁻¹`-shift is equivalently realised by the index shift `k ↦ k−1` (the
T036 pattern): `zetaEta_twisted_moments` states the final display
$`\int\chi(x)x^k\cdot\zeta_\eta = (1-\theta(p)p^{k-1})L(\theta,1-k)`
directly as the $`(k-1)`-st χ-twisted moment of
$`\Res_{\Zpx}(\mu_\eta)` (cleared by $`G(\eta^{-1})`); the Euler factor
arises uniformly from $`\Res = 1 - \varphi\circ\psi`, with no case split
on $`n`. An ambient primitive `p^n`-th root of unity is assumed,
mirroring the source's $`\eps_{p^n}`.
:::

# Analytic functions on Zp via the Mellin transform

We now translate measures on $`\Zpx` into analytic functions on $`\Zp`, recovering
the question posed at the outset: $`p`-adic analytic functions interpolating
$`\zeta(1-k)`. The price is that no *single* analytic function captures all $`k`;
instead there are $`p-1` branches, one for each residue class modulo $`p-1`.

The obstruction is that the naive definition $`x \mapsto x^s = \exp(s\log x)`
fails: the $`p`-adic exponential does not converge on all of $`\Zpx`.

:::lemma_ "interp-padic-exp" (lean := "PadicLFunctions.padicExp_converges_on_pZp, PadicLFunctions.padicExp_smul_padicLog_eq_onePAdicPow")
The $`p`-adic exponential converges on $`p\Zp`. Consequently, for every $`s \in
\Zp` the map $`1 + p\Zp \to \Zp`, $`x \mapsto x^s := \exp(s\log x)`, is
well-defined.

In the formalisation `padicExp`/`padicLog` are developed over any complete
ultrametric $`\Qp`-algebra field (convergence, isometry, functional
equations, and the exp/log inversion on the open ball
$`\|x\|^{p-1} < p^{-1}`), `padicExp_converges_on_pZp` is the first
sentence for odd $`p`, and `padicExp_smul_padicLog_eq_onePAdicPow` both
realises the well-definedness of $`x^s = \exp(s\log x)` on `ℤ_p` and proves
it EQUAL to the continuous-character construction `PadicInt.onePAdicPow`
used throughout §5.3 (uniqueness of continuous additive characters; this
discharges the recorded replan L5.3.3).
:::

:::proof "interp-padic-exp"
This is standard local field theory: $`\exp` converges on the disc $`|z| <
p^{-1/(p-1)}`, which for odd $`p` contains $`p\Zp`, while $`\log` maps $`1+p\Zp`
into $`p\Zp`. Hence $`\exp(s\log x)` makes sense for $`x \in 1+p\Zp` and $`s \in
\Zp`, and standard properties of $`\exp` and $`\log` show it has the expected
behaviour of an exponential.
:::

:::definition "teichmuller-character" (lean := "PadicInt.teichmuller, PadicInt.angleUnit, PadicInt.teichmuller_mul_angleUnit, PadicInt.eq_one_of_pow_card_sub_one")
For odd $`p` there is a decomposition $`\Zpx \cong \mu_{p-1}\times(1+p\Zp)`. The
*Teichmüller character* $`\omega : \Zpx \to \mu_{p-1}` sends $`x` to the
Teichmüller lift of its reduction modulo $`p`, and the projection
$`\ang{\,\cdot\,} : \Zpx \to 1+p\Zp` is given by $`\ang{x} := \omega^{-1}(x)\,x`.
Every $`x\in\Zpx` factors as $`x = \omega(x)\ang{x}`. This uses
{uses "interp-padic-exp"}[].

In the formalisation $`\omega` is `PadicInt.teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ`,
built through mathlib's `Perfection.teichmuller₀` (whose construction is the
adic limit of $`p^n`-th powers of lifts, i.e. $`\omega(x) = \lim_n x^{p^n}`);
$`\mu_{p-1}`-valuedness is `teichmullerFun_pow_card_sub_one`, the $`1+p\Zp`
membership of $`\ang{x}` is `angleUnit_sub_one_mem`, and uniqueness of the
factorisation is `eq_one_of_pow_card_sub_one` ($`\mu_{p-1}\cap(1+p\Zp)=1`).
:::

Because the $`p`-adic exponential converges on $`p\Zp`, the map $`x \mapsto
\ang{x}^s` is well-defined for all $`s \in \Zp`, so for each $`i` the assignment
$`s \mapsto [x \mapsto \omega(x)^i\ang{x}^s]` embeds $`\Zp` into the continuous
characters of $`\Zpx`.

:::definition "interp-branches" (lean := "PadicLFunctions.branchChar, PadicLFunctions.zetaPBranch")
For each $`i = 1, \dots, p-1` the *$`i`-th branch of the $`p`-adic zeta function*
is
$$`\zeta_{p,i} : \Zp \to \Cp, \qquad \zeta_{p,i}(s) =
\int_{\Zpx}\omega(x)^i\,\ang{x}^{1-s}\cdot\zetap.`
This uses {uses "kubota-leopoldt"}[] and {uses "teichmuller-character"}[].

In the formalisation the character $`x \mapsto \omega(x)^i\ang{x}^{1-s}` is
`branchChar` (with $`\ang{x}^s` the continuous-character realisation of the
recorded replan L5.3.3), values are taken in $`\Qp` rather than $`\Cp` (the
running $`\Zp`-coefficient convention), and the integral against the
pseudo-measure $`\zetap` is realised through its canonical witness:
`zetaPBranch` pairs `branchChar` with `zetaNum` at the fixed topological
generator and divides by the unit pairing, with junk value at the pole
$`(i,s) = (0,1)` (RJW's "meromorphic").
:::

:::theorem "interp-branch-interpolation" (lean := "PadicLFunctions.zetaPBranch_interpolation")
For all $`k \geq 1` with $`k \equiv i \pmod{p-1}`,
$$`\zeta_{p,i}(1-k) = (1 - p^{k-1})\,\zeta(1-k).`
This uses {uses "interp-branches"}[], {uses "kubota-leopoldt"}[] and
{uses "special-values-zeta"}[].
:::

:::proof "interp-branch-interpolation"
The monomial character $`x \mapsto x^k` factors as $`\omega(x)^i\ang{x}^k`
precisely when $`k \equiv i \pmod{p-1}`, and in that case it equals the value of
$`\omega(x)^i\ang{x}^{1-s}` at $`s = 1-k`. Substituting $`s = 1-k` into the
definition of $`\zeta_{p,i}` therefore gives $`\zeta_{p,i}(1-k) =
\int_{\Zpx}x^k\cdot\zetap`. The defining interpolation property of the
Kubota–Leopoldt pseudo-measure {uses "kubota-leopoldt"}[] — the trivial-conductor
case $`\int_{\Zpx}x^k\cdot\zetap = (1-p^{k-1})\zeta(1-k)` — then evaluates this to
$`(1-p^{k-1})\zeta(1-k)`.
:::

Note that (as RJW record after the theorem) $`\zeta_{p,i}` is identically zero
whenever $`i` is odd: $`\zeta(1-k)` vanishes for every odd $`k \geq 1`, and the
congruence $`k \equiv i \pmod{p-1}` forces such $`k` to be odd exactly when
$`i` is (as $`p-1` is even). Identical vanishing on all of $`\Zp` further uses
the continuity of $`\zeta_{p,i}` in $`s`; the formalisation records the
interpolation formula itself.

We package the most general statement using the measure $`\zeta_\eta`.

:::definition "interp-Lp-theta" (lean := "PadicLFunctions.MeasureR.LpFunction")
Let $`\theta = \chi\eta` be a Dirichlet character with $`\eta` of conductor $`D`
prime to $`p` and $`\chi` of conductor $`p^n`, $`n \geq 0`. The *$`p`-adic
$`L`-function* of $`\theta` is
$$`L_p(\theta, s) := \int_{\Zpx}\chi(x)\,\ang{x}^{1-s}\cdot\zeta_\eta, \qquad s \in
\Zp.`
Equivalently, in terms of the unshifted measure $`\mu_\eta`,
$$`L_p(\theta,s) = \int_{\Zpx}\chi\omega^{-1}(x)\,\ang{x}^{-s}\cdot\mu_\eta =
\int_{\Zpx}\chi\omega^{s-1}(x)\,x^{-s}\cdot\mu_\eta.`
This uses {uses "interp-zeta-eta"}[] and {uses "teichmuller-character"}[].

In the formalisation `LpFunction` takes values in an ambient complete
ultrametric $`\Qp`-algebra `K` (standing in for the notes' $`\Cp`), pairs
`zetaEtaCleared` with the character `χ̃(x)·⟨x⟩^{1−s}` and divides the
Gauss-sum clearing back out; the `eq:alternative` description in terms of
$`\mu_\eta` is the route taken by the interpolation proof.
:::

:::theorem "interp-Lp-interpolation" (lean := "PadicLFunctions.MeasureR.Lp_interpolation")
For all $`k \geq 1`,
$$`L_p(\theta, 1-k) = \big(1 - \theta\omega^{-k}(p)\,p^{k-1}\big)\,
L(\theta\omega^{-k}, 1-k).`
This uses {uses "interp-Lp-theta"}[], {uses "interp-eta-restriction"}[],
{uses "interp-mahler-theta"}[] and {uses "dirichlet-L-function"}[].

In the formalisation $`\theta\omega^{-k}` is realised at its conductor: the
$`p`-part $`\chi\omega^{-k}` enters through its primitive core `χ'`
(supplied by `exists_primitive_pPow_factorisation`), and the right-hand side
is the L-value of $`\eta\cdot\chi'` exactly as in the final display of
{uses "interp-zeta-eta"}[]; the §5.2 standing hypothesis $`D > 1` applies.
:::

:::proof "interp-Lp-interpolation"
Use the equivalent description of {uses "interp-Lp-theta"}[]. From $`x =
\omega(x)\ang{x}` one computes $`\chi\omega^{-1}(x)\ang{x}^{k-1} = \chi\omega^{-k}
(x)\,\omega^{k-1}(x)\ang{x}^{k-1} = \chi\omega^{-k}(x)\,x^{k-1}`. Hence $`L_p(\theta,
1-k) = \int_{\Zpx}\chi\omega^{-k}(x)\,x^{k-1}\cdot\mu_\eta`. Writing $`\psi :=
\chi\omega^{-k}` for the $`p`-power-conductor character and $`\theta\omega^{-k} =
\psi\eta`, the twisted moment $`\int_{\Zpx}\psi(x)x^{k-1}\cdot\mu_\eta` is computed
exactly as in the non-tame proof: forming the twist $`\mu_{\psi\eta} =
(\mu_\eta)_\psi` with its Mahler transform {uses "interp-mahler-theta"}[] and
applying the restriction-interpolation {uses "interp-eta-restriction"}[] to it
gives $`\int_{\Zpx}\psi(x)x^{k-1}\cdot\mu_\eta = (1-\theta\omega^{-k}(p)p^{k-1})
L(\theta\omega^{-k},1-k)`.
:::

Note that (as RJW record after the theorem) directly from the definitions
$`\zeta_{p,i}(s) = L_p(\omega^i, s)`, so for arbitrary $`k > 0` the theorem
gives $`\zeta_{p,i}(1-k) = (1-\omega^{i-k}(p)p^{k-1})L(\omega^{i-k},1-k)`,
recovering the branch interpolation when $`k \equiv i \pmod{p-1}` (where
$`\omega^{i-k}` is trivial). The formalisation keeps the two routes separate:
$`\zeta_{p,i}` is built from the §4 pseudo-measure $`\zetap` (tame conductor
$`D = 1`), while $`L_p` integrates against the genuine measure $`\zeta_\eta`
of the $`D > 1` theory, so this identification is prose-level only.

Finally, the construction $`\zeta_{p,i}` is an instance of a general transform.

:::definition "mellin-transform"
For any measure $`\mu` on $`\Zpx` and $`i \in \{1,\dots,p-1\}`, the *Mellin
transform of $`\mu` at $`i`* is the function
$$`\Mellin_{\mu,i}(s) := \int_{\Zpx}\omega(x)^i\,\ang{x}^s\cdot\mu, \qquad s \in
\Zp.`
It converts $`p`-adic measures on $`\Zpx` into analytic functions on $`\Zp`; one
has $`\zeta_{p,i}(s) = \Mellin_{\zetap,i}(1-s)`. This uses
{uses "teichmuller-character"}[] and {uses "interp-branches"}[].
:::
