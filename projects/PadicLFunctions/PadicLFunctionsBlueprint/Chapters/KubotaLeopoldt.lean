import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The Kubota-Leopoldt p-adic L-function" =>

Throughout, $`p` is a fixed odd prime. The goal of this chapter is to construct
the Kubota–Leopoldt $`p`-adic $`L`-function as a pseudo-measure on $`\Zpx`
interpolating the values $`(1-p^{k-1})\zeta(1-k)` of the Riemann zeta function.
The strategy is to start from an explicit $`\cC^\infty` function, transport it to
a power series via the substitution $`e^t = T+1`, recognise that power series as
the Mahler transform of a measure $`\mua` on $`\Zp`, restrict $`\mua` to $`\Zpx`
to strip off the Euler factor at $`p`, and finally rescale by an augmentation
element to remove the auxiliary parameter $`a` and produce a pseudo-measure.

The headline result of the chapter is the following.

:::theorem "kl-existence-uniqueness" (lean := "PadicMeasure.kubotaLeopoldt")
There is a unique pseudo-measure $`\zetap` on $`\Zpx` such that, for all integers
$`k > 0`,
$$`\int_{\Zpx} x^k \cdot \zetap = (1-p^{k-1})\,\zeta(1-k).`$$
This pseudo-measure is the *Kubota–Leopoldt $`p`-adic $`L`-function*.  Existence
is supplied by the explicit construction {uses "kubota-leopoldt"}[] together with
{uses "kl-zetap-interpolation"}[], and uniqueness rests on the
{uses "pseudo-measure"}[] rigidity of {uses "kl-zetap-interpolation"}[].
:::

:::proof "kl-existence-uniqueness"
Existence is {uses "kl-zetap-interpolation"}[], which exhibits the pseudo-measure
$`\zetap` of Definition {uses "kubota-leopoldt"}[] and verifies the interpolation
formula. For uniqueness, suppose $`\zetap` and $`\zetap'` are two pseudo-measures
satisfying the displayed formula, and set $`\lambda = \zetap - \zetap'`, a
pseudo-measure with $`\int_{\Zpx} x^k \cdot \lambda = 0` for all $`k > 0`. Fix a
topological generator $`a` of $`\Zpx` and let $`\thetaa = [a]-[1]`. By definition
of a {uses "pseudo-measure"}[] pseudo-measure, $`\thetaa\lambda` is a genuine
measure on $`\Zpx`, and for $`k>0` its monomial integrals are
$`\int_{\Zpx} x^k\cdot\thetaa\lambda = (a^k-1)\int_{\Zpx} x^k\cdot\lambda = 0`.
A measure on $`\Zpx` is determined by the values $`\int_{\Zpx} x^k\cdot(-)` for
$`k > 0` (these recover all Mahler coefficients on the units), so $`\thetaa\lambda = 0`.
Since $`\thetaa` is not a zero divisor in $`\Lam(\Zpx)`, we conclude $`\lambda = 0`,
i.e. $`\zetap = \zetap'`.
:::

# The auxiliary measure

Recall the integral formula $`(s-1)\zeta(s) = L(f, s-1)`, with
$`f(t) = t/(e^t-1)`, whose value at negative integers is
$`\zeta(-k) = f^{(k)}(0) = (-1)^k B_{k+1}/(k+1)`. The factor $`s-1` smooths away
the pole of $`\zeta` at $`s=1`. To remove this smoothing we fix an integer $`a`
coprime to $`p` and replace $`f` by
$$`\fa(t) = \frac{1}{e^t-1} - \frac{a}{e^{at}-1},`$$
which is again $`\cC^\infty` and rapidly decreasing, so its $`L`-function
$`L(\fa, s)` is defined. The parameter $`a` removes the factor $`s-1` at the cost
of a different smoothing factor.

-- Deliberately unwired (§4 board, 2026-06-10): the Mellin/analytic-continuation half
-- of this lemma is §2 material (deferred). The value formula `f_a^{(k)}(0) =
-- (−1)^k(1−a^{1+k})ζ(−k)` — the part §4 consumes — is realised algebraically by
-- `PadicMeasure.muA_apply_powCM` (wired at `kl-mua-interpolation`), with the rational
-- ζ-values as `zetaNeg` (bridge to `riemannZeta`: `zetaNeg_eq_riemannZeta`).
:::lemma_ "kl-values-of-zeta"
With $`\fa` as above,
$$`L(\fa, s) = (1 - a^{1-s})\,\zeta(s),`$$
which extends analytically to all of $`\C`, and the derivatives at $`0` satisfy
$$`\fa^{(k)}(0) = (-1)^k\,(1 - a^{1+k})\,\zeta(-k).`$$
This depends on the analytic theory of {uses "riemann-zeta"}[] and on the special
values {uses "special-values-zeta"}[].
:::

:::proof "kl-values-of-zeta"
Use the Mellin presentation $`L(\fa,s) = \frac{1}{\Gamma(s)}\int_0^\infty \fa(t)\,t^{s-1}\,dt`,
valid for $`\Re(s)` large because $`\fa` is $`\cC^\infty` and rapidly decreasing.
Split $`\fa(t) = \frac{1}{e^t-1} - \frac{a}{e^{at}-1}` into its two terms. The
first gives the classical integral $`\frac{1}{\Gamma(s)}\int_0^\infty \frac{t^{s-1}}{e^t-1}\,dt = \zeta(s)`.
In the second, substitute $`u = at`: then $`a\,t^{s-1}\,dt = a^{1-s}u^{s-1}\,du`
and $`e^{at}-1 = e^u-1`, so the term becomes
$`a^{1-s}\cdot\frac{1}{\Gamma(s)}\int_0^\infty \frac{u^{s-1}}{e^u-1}\,du = a^{1-s}\zeta(s)`.
Subtracting, $`L(\fa,s) = (1-a^{1-s})\zeta(s)`, which inherits the analytic
continuation of $`\zeta` to $`\C` (the factor $`1-a^{1-s}` is entire). For the
derivatives, expand the generating series $`\frac{t}{e^t-1} = \sum_{n\ge0} B_n\frac{t^n}{n!}`,
so that $`\frac{1}{e^t-1} = \sum_{n\ge0} B_n\frac{t^{n-1}}{n!}` and
$`\fa(t) = \sum_{n\ge0} B_n(1-a^n)\frac{t^{n-1}}{n!}`. The coefficient of $`t^k`
is $`\frac{B_{k+1}(1-a^{k+1})}{(k+1)!}`, whence
$`\fa^{(k)}(0) = \frac{B_{k+1}(1-a^{k+1})}{k+1}`. Substituting the special value
$`\zeta(-k) = (-1)^k B_{k+1}/(k+1)` from {uses "special-values-zeta"}[] turns the
Bernoulli factor into $`(-1)^k\zeta(-k)`, giving
$`\fa^{(k)}(0) = (-1)^k(1-a^{1+k})\zeta(-k)`.
:::

The next observation turns the analytic object $`\fa` into a $`p`-adic power
series. Under $`e^t = T+1` the operator $`d/dt` becomes
$`\pa = (1+T)\frac{d}{dT}`.

:::lemma_ "kl-define-Fa" (lean := "PadicMeasure.constantCoeff_iterate_delQ")
Under the substitution $`e^t = T+1`, the derivative $`d/dt` corresponds to the
operator $`\pa = (1+T)\frac{d}{dT}`. Setting
$$`\Fa(T) := \frac{1}{T} - \frac{a}{(1+T)^a - 1},`$$
one has $`\fa^{(k)}(0) = (\pa^k \Fa)(0)` for all $`k \ge 0`.
:::

:::proof "kl-define-Fa"
Since $`e^t = 1+T`, we have $`\frac{dT}{dt} = e^t = 1+T`, so the chain rule turns
$`\frac{d}{dt}` into the operator
$`\frac{dT}{dt}\frac{d}{dT} = (1+T)\frac{d}{dT} = \pa` acting on functions of $`T`.
Substituting $`e^t = 1+T` and $`e^{at} = (1+T)^a` into $`\fa(t) = \frac{1}{e^t-1} - \frac{a}{e^{at}-1}`
expresses it as the rational function $`\Fa(T) = \frac1T - \frac{a}{(1+T)^a-1}`.
As $`\frac{d}{dt}` and $`\pa` agree as operators under the substitution, their
$`k`-fold iterates $`\frac{d^k}{dt^k}` and $`\pa^k` also agree; the substitution
sends $`t=0` to $`T=0`, so evaluating both at the origin gives
$`\fa^{(k)}(0) = (\pa^k \Fa)(0)`.
:::

The left-hand side $`\fa^{(k)}(0)` computes the zeta value $`\zeta(-k)` by
{bpref "kl-values-of-zeta"}[], while the right-hand side $`(\pa^k\Fa)(0)` is exactly
the shape of the formula $`\int_{\Zp} x^k\cdot\mu = (\pa^k \Am_\mu)(0)` expressing
integrals of monomials in terms of the Mahler transform $`\Am_\mu`. This motivates
seeking a measure $`\mua` with $`\Am_{\mua} = \Fa`; for that we first check $`\Fa`
is a bounded power series.

:::proposition "kl-Fa-in-Zp" (lean := "PadicMeasure.one_add_X_pow_sub_one_mul_Fa")
The function $`\Fa(T)` lies in $`\Zp[[T]]`.
:::

:::proof "kl-Fa-in-Zp"
Expand the denominator using the binomial series:
$$`(1+T)^a - 1 = \sum_{n\ge 1}\binom{a}{n}T^n = aT\bigl[\,1 + T g(T)\,\bigr],`$$
where $`g(T) = \sum_{n\ge 2}\tfrac{1}{a}\binom{a}{n}T^{n-2}`. Each coefficient
$`\tfrac1a\binom{a}{n}` is a $`p`-adic integer: the binomial coefficients
$`\binom{a}{n}` lie in $`\Z`, and dividing by $`a` does not leave $`\Zp` precisely
because $`a` is a unit in $`\Zp` (here we use that $`a` is coprime to $`p`). Thus
$`g(T)\in\Zp[[T]]`. Substituting and cancelling the factor $`a`,
$$`\frac{1}{T} - \frac{a}{(1+T)^a-1} = \frac{1}{T} - \frac{1}{T\bigl(1 + Tg(T)\bigr)} = \frac{1}{T}\Bigl(1 - \frac{1}{1+Tg(T)}\Bigr) = \frac{1}{T}\cdot\frac{Tg(T)}{1+Tg(T)}.`$$
Since $`Tg(T)` has zero constant term, $`1+Tg(T)` is a unit in $`\Zp[[T]]` and the
geometric series gives $`\frac{Tg(T)}{1+Tg(T)} = \sum_{n\ge 1}(-1)^{n-1}\bigl(Tg(T)\bigr)^n`,
each term of which is divisible by $`T`. Dividing by $`T` therefore cancels the
pole and leaves a power series with $`\Zp`-coefficients, so $`\Fa(T)\in\Zp[[T]]`.
:::

:::definition "measure-mu-a" (lean := "PadicMeasure.muA")
Fix an integer $`a` coprime to $`p`. Let $`\mua` be the (unique) $`p`-adic measure
on $`\Zp` whose Mahler transform is $`\Am_{\mua} = \Fa(T)`; this exists by
{uses "kl-Fa-in-Zp"}[] together with the {uses "mahler-transform"}[] identification
of measures with $`\Zp[[T]]`.
:::

:::proposition "kl-mua-interpolation" (lean := "PadicMeasure.muA_apply_powCM")
For all $`k \ge 0`,
$$`\int_{\Zp} x^k \cdot \mua = (-1)^k\,(1 - a^{k+1})\,\zeta(-k).`$$
:::

:::proof "kl-mua-interpolation"
The {uses "mahler-transform"}[] satisfies $`\int_{\Zp} x^k\cdot\mu = (\pa^k \Am_{\mu})(0)`,
expressing the $`k`-th monomial integral as the $`k`-fold $`\pa`-derivative of the
Mahler transform at the origin. Apply this to $`\mu = \mua`. By the definition
{uses "measure-mu-a"}[] of $`\mua` we have $`\Am_{\mua} = \Fa`, so the integral
equals $`(\pa^k \Fa)(0)`, which is $`\fa^{(k)}(0)` by {uses "kl-define-Fa"}[].
Finally $`\fa^{(k)}(0) = (-1)^k(1-a^{k+1})\zeta(-k)` by {uses "kl-values-of-zeta"}[].
:::

# Restriction to the units

We now restrict $`\mua` from $`\Zp` to $`\Zpx`, so as to obtain a measure on the
units. The restriction operator is $`\Res_{\Zpx} = 1 - \varphi\circ\psi`, where
$`\varphi` and $`\psi` are the operators on measures (and on power series, via the
Mahler transform) introduced in the toolbox; on power series $`\varphi` acts by
$`F \mapsto F((1+T)^p - 1)`. We first record a key invariance of $`\mua`.

:::lemma_ "kl-psi-invariant" (lean := "PadicMeasure.psi_muA")
The measure $`\mua` satisfies $`\psi(\mua) = \mua`; equivalently
$`\psi(\Fa) = \Fa`.
:::

:::proof "kl-psi-invariant"
Work on Mahler transforms, where it suffices to show $`\psi(\Fa) = \Fa`. Writing
$`\sigmaa` for the toolbox operator $`F(T)\mapsto F((1+T)^a - 1)`, one has
$`\Fa(T) = \tfrac{1}{T} - a\cdot\sigmaa(\tfrac{1}{T})`. Since $`\psi` commutes with
$`\sigmaa`, it is enough to prove $`\psi(\tfrac1T) = \tfrac1T`. The defining
relation reads $`(\varphi\circ\psi)(F)(T) = \tfrac1p\sum_{\xi\in\mu_p} F((1+T)\xi - 1)`.
Applying it to $`F = \tfrac1T` and using the factorisation
$`\prod_{\xi\in\mu_p}\bigl((1+T)\xi - 1\bigr) = (1+T)^p - 1`, a partial-fraction
expansion of $`\tfrac1p\sum_\xi \tfrac{1}{(1+T)\xi-1}` collapses to a single term:
$$`(\varphi\circ\psi)\!\left(\tfrac1T\right) = \frac1p\sum_{\xi\in\mu_p}\frac{1}{(1+T)\xi - 1} = \frac{1}{(1+T)^p - 1} = \varphi\!\left(\tfrac1T\right).`$$
As $`\varphi` is injective, this forces $`\psi(\tfrac1T) = \tfrac1T`, and hence
$`\psi(\Fa) = \Fa`, i.e. $`\psi(\mua) = \mua`.
:::

:::proposition "kl-restriction-interpolation" (lean := "PadicMeasure.res_units_muA_apply_powCM")
For all $`k \ge 0`,
$$`\int_{\Zpx} x^k \cdot \mua = (-1)^k\,(1 - p^k)\,(1 - a^{k+1})\,\zeta(-k).`$$
In other words, restricting from $`\Zp` to $`\Zpx` removes the Euler factor at
$`p`.
:::

:::proof "kl-restriction-interpolation"
Since $`\Res_{\Zpx} = 1 - \varphi\circ\psi`, we have
$$`\int_{\Zpx} x^k\cdot\mua = \int_{\Zp} x^k\cdot(1-\varphi\circ\psi)\mua = \int_{\Zp} x^k\cdot(1-\varphi)\mua,`$$
where the second equality uses $`\psi(\mua) = \mua` from {uses "kl-psi-invariant"}[].
The operator $`\varphi` corresponds to $`\sigma_p`, i.e. push-forward along
multiplication by $`p`, so $`\int_{\Zp} x^k\cdot\varphi\mua = p^k\int_{\Zp} x^k\cdot\mua`;
hence the right-hand side equals $`(1-p^k)\int_{\Zp} x^k\cdot\mua`. Substituting
the value of $`\int_{\Zp} x^k\cdot\mua` from {uses "kl-mua-interpolation"}[] gives
the stated formula.
:::

# Rescaling and removing the dependence on a

Thus far the parameter $`a` has played the role of the smoothing factor that
removes the pole of $`\zeta` at $`s=1`. To eliminate $`a` we must permit simple
poles on the $`p`-adic side, which is exactly what {bpref "pseudo-measure"}[]
pseudo-measures allow. The interpolation formula
{bpref "kl-restriction-interpolation"}[] features the factor $`a^{k+1}-1`, whereas
the natural augmentation element $`\thetaa` of the Iwasawa algebra produces
$`a^k - 1`; the gap is bridged by multiplication by $`x^{-1}`.

:::definition "kl-theta-a" (lean := "PadicMeasure.zetaNum_moments")
For $`a` an integer coprime to $`p`, let $`\thetaa \in \Lam(\Zpx)` be the element
corresponding to $`[a] - [1]` (in the formalisation: `dirac p a - 1`; the
$`x^{-1}`-multiplication is `unitsCmul`/`invCM`, and the displayed moment formula is
`zetaNum_moments`), so that
$$`\int_{\Zpx} x^k \cdot \thetaa = a^k - 1.`$$
On $`\Zpx` there is a well-defined operation *multiplication by $`x^{-1}`*, given on
measures by $`\int_{\Zpx} f(x)\cdot x^{-1}\mu := \int_{\Zpx} x^{-1}f(x)\cdot\mu`,
and, combining this shift with {uses "kl-restriction-interpolation"}[], one
computes
$$`\int_{\Zpx} x^k \cdot x^{-1}\mua = \int_{\Zpx} x^{k-1}\cdot\mua = (-1)^k\,(a^k - 1)\,(1 - p^{k-1})\,\zeta(1-k).`$$
This uses the {uses "iwasawa-algebra"}[] structure of $`\Lam(\Zpx)`.
:::

:::definition "kubota-leopoldt" (lean := "PadicMeasure.padicZeta")
Let $`a` be a *topological generator* of $`\Zpx`. The *$`p`-adic zeta function*
(the Kubota–Leopoldt $`p`-adic $`L`-function) is the element
$$`\zetap := \frac{x^{-1}\,\Res_{\Zpx}\mua}{\thetaa} \in Q(\Zpx)`$$
of the fraction ring of the {uses "iwasawa-algebra"}[] $`\Lam(\Zpx)`, where
$`\mua` is the measure {uses "measure-mu-a"}[] and $`\thetaa` is the augmentation
element {uses "kl-theta-a"}[].
:::

:::proposition "kl-zetap-interpolation" (lean := "PadicMeasure.padicZeta_moments")
The element $`\zetap` is a well-defined pseudo-measure, independent of the choice
of topological generator $`a`, satisfying
$$`\int_{\Zpx} x^k \cdot \zetap = (1 - p^{k-1})\,\zeta(1-k) \qquad \text{for all } k > 0.`$$
:::

:::proof "kl-zetap-interpolation"
Write $`\nu := x^{-1}\Res_{\Zpx}\mua \in \Lam(\Zpx)`, so that
$`\zetap = \nu/\thetaa`. Because $`\thetaa = [a]-[1]` for the topological generator
$`a`, every augmentation element $`[g]-[1]` is a $`\Lam(\Zpx)`-multiple of
$`\thetaa`; hence $`([g]-[1])\zetap \in \Lam(\Zpx)` for all $`g`, so $`\zetap` is a
{uses "pseudo-measure"}[] pseudo-measure. Integrating against $`x^k` via the
pseudo-measure rule $`\int x^k\cdot\zetap = (a^k-1)^{-1}\int x^k\cdot\thetaa\zetap = (a^k-1)^{-1}\int x^k\cdot\nu`,
and using $`\int_{\Zpx} x^k\cdot x^{-1}\Res_{\Zpx}\mua = (-1)^k(a^k-1)(1-p^{k-1})\zeta(1-k)`
from {uses "kl-restriction-interpolation"}[] and {uses "kl-theta-a"}[], the factor
$`a^k-1` cancels and we obtain
$$`\int_{\Zpx} x^k \cdot \zetap = (-1)^k\,(1-p^{k-1})\,\zeta(1-k).`$$
The sign $`(-1)^k` may be dropped. Indeed $`\zeta(1-k) = -B_k/k`, which vanishes
for every odd $`k \ge 3` (as $`B_k = 0` there); for even $`k` the sign is already
$`(-1)^k = +1`; and for $`k=1` the Euler factor $`1-p^{k-1} = 1-p^0 = 0` kills the
whole expression. Hence $`(-1)^k = 1` wherever the right-hand side is non-zero,
and the interpolation formula follows. Finally, independence of $`a` follows from
the rigidity of pseudo-measures on $`\Zpx`: the values $`\int_{\Zpx} x^k\cdot(-)`
for $`k>0` determine a pseudo-measure uniquely, and the resulting formula does not
involve $`a`, so any two choices of topological generator yield the same $`\zetap`.
:::
