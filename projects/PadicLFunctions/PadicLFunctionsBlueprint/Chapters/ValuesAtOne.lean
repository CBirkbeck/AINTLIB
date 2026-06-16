import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The value at s = 1" =>

Throughout, $`p` is an odd prime and $`\theta` is a *non-trivial* Dirichlet
character, written in the usual form $`\theta = \chi\eta`, where $`\chi` has
conductor $`p^n` and $`\eta` has conductor $`D` prime to $`p`. We write
$`N = Dp^n` for the conductor of $`\theta`, and let $`\varepsilon_N` denote a
fixed primitive $`N`-th root of unity. We write $`G(\theta)` for the Gauss sum
attached to $`\theta`.

The interpolation theorem identifies, for every integer $`k > 0`, the integral
$`\int_{\Zpx}\chi(x)x^k\,d\zeta_\eta` with the classical $`L`-value
$`L(\theta,1-k)`. These $`k>0` lie in the *range of interpolation*, and there the
link to classical values is explicit; such values are called *critical*. It is
natural to ask what happens *outside* this range — in particular at $`k=0`,
i.e. at $`s=1`. A priori such *non-critical* values need have nothing to do with
classical $`L`-values: indeed $`L(\theta,1)` is transcendental, so it cannot be
viewed as a $`p`-adic number in any natural way. Nevertheless there is a formula
for the $`p`-adic $`L`-function at $`s=1` strikingly parallel to its classical
analogue. The $`p`-adic formula is due to Leopoldt; it can be used to prove a
$`p`-adic analogue of the analytic class number formula, and is the simplest
instance of the $`p`-adic Beilinson / Perrin-Riou conjectures, which describe
non-critical special values of $`p`-adic $`L`-functions in arithmetic terms.

# The two formulae at s = 1

:::theorem "p-adic-value-s1"
Let $`\theta` be a non-trivial Dirichlet character of conductor $`N`, and let
$`\varepsilon_N` be a primitive $`N`-th root of unity.

*(i) Classical value at $`s=1`.* We have
$$`L(\theta,1) = -\frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\theta^{-1}(c)\,\log\!\big(1-\varepsilon_N^{\,c}\big).`

*(ii) $`p`-adic value at $`s=1`.* We have
$$`L_p(\theta,1) = -\big(1-\theta(p)p^{-1}\big)\frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\theta^{-1}(c)\,\log_p\!\big(1-\varepsilon_N^{\,c}\big).`

Part (i) rests on the special-value description of {uses "dirichlet-L-function"}[].
Part (ii) concerns the value at $`s=1` of the {uses "kubota-leopoldt"}[] $`p`-adic
$`L`-function, which lies *outside* the range of the {uses "interpolation-property"}[],
and is computed from the measures {uses "measure-mu-a"}[].
:::

The two formulae are *identical* up to replacing the complex logarithm $`\log` by
its $`p`-adic avatar $`\log_p` and inserting the missing Euler factor at $`p`,
namely $`(1-\theta(p)p^{-1})`. If $`\theta` is odd, both sides of the $`p`-adic
formula vanish.

# The complex value at s = 1

:::theorem "val1-classical-gauss-expansion" (lean := "PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum")
For $`\Re(s)>1` one has
$$`L(\theta,s) = \frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\theta^{-1}(c)\sum_{n\geq 1}\frac{\varepsilon_N^{\,nc}}{n^{s}}.`
This rests on {uses "dirichlet-L-function"}[].
:::

:::proof "val1-classical-gauss-expansion"
Start from $`L(\theta,s)=\sum_{a\in(\Z/N\Z)^\times}\theta(a)\sum_{n\equiv a\ (N)}n^{-s}`
and detect the congruence $`n\equiv a` by the orthogonality of additive
characters: $`\tfrac1N\sum_{c\in\Z/N\Z}\varepsilon_N^{(a-n)c}` equals $`1` when
$`n\equiv a\ (N)` and $`0` otherwise. Substituting and exchanging the (absolutely
convergent) sums collects the inner sum over $`a` into a Gauss sum,
$`\sum_a\theta(a)\varepsilon_N^{ac}=G(\theta)\theta^{-1}(c)`, giving
$`\tfrac{G(\theta)}{N}\sum_c\theta^{-1}(c)\sum_{n\geq1}\varepsilon_N^{-nc}n^{-s}`.
The standard Gauss-sum identity $`G(\theta)G(\theta^{-1})=\theta(-1)N` together
with $`\theta^{-1}(c)=0` for $`(c,N)\neq1` rewrites the prefactor as
$`\theta(-1)/G(\theta^{-1})`, and the change of variables $`c\mapsto -c` removes
$`\theta(-1)` and flips the sign in the exponent, yielding the stated formula.
:::

:::theorem "val1-classical-s1" (lean := "PadicLFunctions.ValuesAtOneComplex.LFunction_one_eq")
Theorem {bpref "p-adic-value-s1"}[] (i) holds: evaluating
{bpref "val1-classical-gauss-expansion"}[] at $`s=1` gives the asserted closed
formula for $`L(\theta,1)`.
:::

:::proof "val1-classical-s1"
Since $`\theta` is non-trivial we have $`N>1`, so $`\varepsilon_N^{\,c}\neq1` for
every $`c\in(\Z/N\Z)^\times`, and the Taylor expansion of the logarithm
$`-\log(1-\varepsilon_N^{\,c})=\sum_{n\geq1}\varepsilon_N^{\,nc}n^{-1}` converges.
Setting $`s=1` in {uses "val1-classical-gauss-expansion"}[] therefore replaces the
inner sum by $`-\log(1-\varepsilon_N^{\,c})`, producing
$`L(\theta,1)=-\tfrac{1}{G(\theta^{-1})}\sum_c\theta^{-1}(c)\log(1-\varepsilon_N^{\,c})`,
as claimed.
:::

The expression refines according to the parity of $`\theta`. If $`\theta` is even
then pairing $`c` with $`-c` gives
$`\theta^{-1}(c)\log(1-\varepsilon_N^{\,c})+\theta^{-1}(-c)\log(1-\varepsilon_N^{-c})
=2\theta^{-1}(c)\log\abs{1-\varepsilon_N^{\,c}}`, so $`L(\theta,1)` may be written
with $`\log\abs{1-\varepsilon_N^{\,c}}` in place of $`\log(1-\varepsilon_N^{\,c})`.
If $`\theta` is odd, the functional equation gives instead
$`L(\theta,1)=-i\pi\,G(\theta^{-1})^{-1}B_{1,\theta^{-1}}`, where
$`B_{1,\theta^{-1}}` is the first twisted Bernoulli number.

# The p-adic value at s = 1

By definition of $`L_p(\theta,s)`,

$$`L_p(\theta,1) = \int_{\Zpx}\chi(x)x^{-1}\,d\mu_\eta = \int_{\Zpx}x^{-1}\,d\mu_\theta.`

The obstruction is that *multiplication by $`x^{-1}`* is not an operation on
measures: $`x^{-1}\mu_\theta` is ill-defined. On the power-series side, where the
Mahler transform $`\sA_{\mu_\theta}(T)=F_\theta(T)` of $`\mu_\theta` lives, this is
mirrored by the indeterminacy of the formal antiderivative $`\partial^{-1}`. The
strategy is to guess an explicit antiderivative $`\widetilde F_\theta` of
$`F_\theta`, show it has just enough convergence to be a *distribution* (rather
than a measure), and then read off $`L_p(\theta,1)` from it.

Recall the explicit formula for the Mahler transform of $`\mu_\theta`,

$$`F_\theta(T)=-\frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\frac{\theta^{-1}(c)}{(1+T)\varepsilon_N^{\,c}-1},`

and the differential operator $`\partial = (1+T)\tfrac{d}{dT}` corresponding to
multiplication by $`x` on measures. Define the candidate antiderivative

$$`\widetilde F_\theta(T)=-\frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\theta^{-1}(c)\,\log\!\big((1+T)\varepsilon_N^{\,c}-1\big).`

Let $`\sR^+` denote the ring of power series $`\sum a_nT^n` with $`\abs{a_n}r^n\to0`
for every $`0\le r<1` (the functions analytic on the open unit disc).

:::lemma_ "val1-Ftilde-in-Rplus"
The power series $`\widetilde F_\theta(T)` lies in $`\sR^+`.
:::

:::proof "val1-Ftilde-in-Rplus"
Expand each logarithm as
$`\log((1+T)\varepsilon_N^{\,c}-1)=\log_p(\varepsilon_N^{\,c}-1)+\log\!\big(1+\tfrac{\varepsilon_N^{\,c}T}{\varepsilon_N^{\,c}-1}\big)`,
whose $`T^n`-coefficient is
$`\tfrac{(-1)^{n-1}}{n}\,\varepsilon_N^{\,cn}(\varepsilon_N^{\,c}-1)^{-n}`. If
$`(N,p)=1` then $`\varepsilon_N^{\,c}-1` is a $`p`-adic unit, so this coefficient
has valuation $`\ge -v_p(n)`; the coefficients grow only logarithmically and hence
$`\widetilde F_\theta\in\sR^+`. For general $`N=Dp^n`, write $`\theta=\eta\chi` and
note, exactly as for $`F_\theta`, the twisting formula
$`\widetilde F_\theta(T)=-G(\chi^{-1})^{-1}\sum_{c\in(\Z/p^n\Z)^\times}\chi^{-1}(c)\,\widetilde F_\eta\big((1+T)\varepsilon_{p^n}^{\,c}-1\big)`.
Since $`\widetilde F_\eta\in\sR^+` by the prime-to-$`p` case and $`\sR^+` is stable
under the substitution $`T\mapsto(1+T)\zeta-1` for a root of unity $`\zeta`, the
same holds for $`\widetilde F_\theta`. This uses {uses "mahler-transform"}[].

This node stays unwired: the distribution-free route (replan R6.6) never needs
full $`\sR^+`-membership, only the weaker coefficient bound
$`\|\,[T^n]\widetilde F_\theta\|\le C(n+1)` that makes the boundary evaluations
$`\widetilde F_\theta(\xi^i-1)` converge (the Lean lemma
`summable_seriesEval_Ftilde`, guarded by the norm-one fact for the contributing
coprime roots).
:::

By the theory of locally analytic distributions, a power series in $`\sR^+` is the
Mahler transform of a locally analytic distribution. Let $`\widetilde\mu_\theta`
be the distribution with $`\sA_{\widetilde\mu_\theta}=\widetilde F_\theta`.

:::lemma_ "val1-x-mu-tilde" (lean := "PadicLFunctions.MeasureR.one_add_mul_derivative_Ftilde")
We have $`x\,\widetilde\mu_\theta=\mu_\theta` as distributions on $`\Zp`. In
particular $`\Res_{\Zpx}(\widetilde\mu_\theta)=x^{-1}\Res_{\Zpx}(\mu_\theta)`,
making sense of the ill-defined product in
$`L_p(\theta,1)=\sA_{x^{-1}\Res_{\Zpx}(\mu_\theta)}(0)`. This depends on
{uses "measure-mu-a"}[] and {uses "locally-analytic-distribution"}[].

In the distribution-free route (replan R6.6) the content $`x\,\widetilde\mu_\theta
=\mu_\theta` is the Mahler-side formal identity $`\partial\widetilde F_\theta
=F_\theta`, where $`\partial=(1+T)\tfrac{d}{dT}`. The Lean lemma
`one_add_mul_derivative_Ftilde` is exactly this identity for the explicit power
series $`\widetilde F_\theta`; the companion measure-side fact
$`\partial\sA_{\rho_\theta}=\sA_{\Res_{\Zpx}(\mu_\theta)}` is
`one_add_mul_derivative_mahlerK_rhoTheta`.
:::

:::proof "val1-x-mu-tilde"
Multiplication by $`x` corresponds to the operator $`\partial=(1+T)\tfrac{d}{dT}`
on Mahler transforms, so $`x\,\widetilde\mu_\theta=\mu_\theta` amounts to
$`\partial\widetilde F_\theta=\sA_{\mu_\theta}=F_\theta`. Differentiating
termwise, $`\partial\log((1+T)\varepsilon_N^{\,c}-1)=\tfrac{(1+T)\varepsilon_N^{\,c}}{(1+T)\varepsilon_N^{\,c}-1}=1+\tfrac{1}{(1+T)\varepsilon_N^{\,c}-1}`;
summing against $`-G(\theta^{-1})^{-1}\theta^{-1}(c)` the constant terms $`1`
cancel because $`\sum_c\theta^{-1}(c)=0` (as $`\theta` is non-trivial), leaving
exactly $`F_\theta(T)`. For the second statement, on $`\Zpx` multiplication by
$`x` is invertible, and $`x\,\Res_{\Zpx}(\widetilde\mu_\theta)=\Res_{\Zpx}(\mu_\theta)`
gives $`\Res_{\Zpx}(\widetilde\mu_\theta)=x^{-1}\Res_{\Zpx}(\mu_\theta)`. This uses
{uses "val1-Ftilde-in-Rplus"}[] and the {uses "mahler-transform"}[] dictionary
under which multiplication by $`x` corresponds to $`\partial`.
:::

Combining the previous lemma with the formula for the restriction of a
distribution to $`\Zpx`, namely $`\Res_{\Zpx}=(1-\varphi\circ\psi)`, gives

$$`L_p(\theta,1)=\sA_{\Res_{\Zpx}(\widetilde\mu_\theta)}(0)=\Big((1-\varphi\circ\psi)\widetilde F_\theta\Big)(0).`

Here $`\varphi\circ\psi(\widetilde F_\theta)` is the Mahler transform of
$`\Res_{p\Zp}(\widetilde\mu_\theta)`, and concretely
$`\varphi\circ\psi(F)(T)=\tfrac1p\sum_{\xi\in\mu_p}F((1+T)\xi-1)`.

:::theorem "val1-padic-s1" (lean := "PadicLFunctions.MeasureR.LpFunction_one")
Theorem {bpref "p-adic-value-s1"}[] (ii) holds: with $`\widetilde F_\theta` as
above one has $`L_p(\theta,1)=(1-\theta(p)p^{-1})\widetilde F_\theta(0)`, and
evaluating $`\widetilde F_\theta(0)` gives the closed formula for $`L_p(\theta,1)`.
This rests on {uses "interpolation-property"}[].

The Lean statement `LpFunction_one` is the displayed closed formula, proved for
the tame conductor $`D>1` (the $`\S 5.2` standing hypotheses; the pure
$`p`-power case $`D=1` is deferred — decomposition R6, replan 4). The proof
follows a *distribution-free* route (replan R6.6): rather than constructing the
locally analytic distribution $`\widetilde\mu_\theta`, it works with the genuine
measure $`\rho_\theta=x^{-1}\Res_{\Zpx}(\mu_\theta)` and the explicit power
series $`\widetilde F_\theta` over $`K`, pinning the constant of integration in
$`\ker\psi`. The root $`\varepsilon_N` is taken in split form
$`\varepsilon_N=\zeta\,\varepsilon_{p^n}` (a primitive tame root times a primitive
wild root), which realises the Gauss-sum factorisation
$`G(\theta^{-1})=G(\eta^{-1})G(\chi^{-1})` of the displayed prefactor.
:::

:::proof "val1-padic-s1"
We evaluate $`\big((1-\varphi\circ\psi)\widetilde F_\theta\big)(0)` by computing the
operator $`\varphi\circ\psi` in two cases, using {uses "val1-x-mu-tilde"}[].

*Case $`n>1`* (so $`\chi\neq1`). Since $`\chi` vanishes on $`p\Zp`, the twisted
distribution $`\widetilde\mu_\theta=(\widetilde\mu_\eta)_\chi` is supported on
$`\Zpx`, so $`\Res_{p\Zp}(\widetilde\mu_\theta)=0` and
$`\varphi\circ\psi(\widetilde F_\theta)=0`. Hence
$`L_p(\theta,1)=\widetilde F_\theta(0)`, which we record as
$`(1-\theta(p)p^{-1})\widetilde F_\theta(0)` using $`\theta(p)=0`.

*Case $`n=0`* (so $`N=D` is coprime to $`p` and $`\theta=\eta`). Then
$`\varphi\circ\psi(\widetilde F_\theta)(T)=\tfrac1p\sum_{\xi\in\mu_p}\widetilde F_\theta((1+T)\xi-1)`.
Evaluating at $`T=0`, the inner sum over $`\xi\in\mu_p` collapses by the product
identity $`\prod_{\xi\in\mu_p}(\xi\,\varepsilon_N^{\,c}-1)=\varepsilon_N^{\,pc}-1`
(the roots of $`X^p-1`; equivalently the norm of $`\xi\varepsilon_N^{\,c}-1` from
$`\Q_p(\mu_p)` to $`\Q_p`), so $`\sum_{\xi}\log_p(\xi\varepsilon_N^{\,c}-1)
=\log_p(\varepsilon_N^{\,pc}-1)`. Substituting the automorphism $`c\mapsto c'=pc`
of $`(\Z/N\Z)^\times` (valid as $`p\nmid N`) pulls out a factor $`\theta(p)`,
giving $`\varphi\circ\psi(\widetilde F_\theta)(0)=\tfrac{\theta(p)}{p}\widetilde F_\theta(0)`.
Therefore $`L_p(\theta,1)=(1-\theta(p)p^{-1})\widetilde F_\theta(0)` again.

Finally, in all cases evaluate $`\widetilde F_\theta(0)`. Using
$`\log_p(x)=\log_p(-x)` for $`x\in\Cp^\times`, we get
$`\widetilde F_\theta(0)=-G(\theta^{-1})^{-1}\sum_c\theta^{-1}(c)\log_p(1-\varepsilon_N^{\,c})`,
and so $`L_p(\theta,1)=-(1-\theta(p)p^{-1})G(\theta^{-1})^{-1}\sum_c\theta^{-1}(c)\log_p(1-\varepsilon_N^{\,c})`,
as claimed.
:::

# Coleman's generalisation to s = k

The result extends to every positive integer $`s=k\geq1`. For $`s,z\in\C` let
$`\Li_s(z)=\sum_{n\geq1}z^n n^{-s}` be the polylogarithm, with its analytic
continuation to $`\C\setminus\{z\in\R:z\geq1\}`; then $`\Li_s(1)=\zeta(s)` and
$`\Li_1(z)=-\log(1-z)`. Coleman constructed $`p`-adic polylogarithms
$`\Li_{k,p}(z)`, locally analytic on $`\Cp\setminus\{1\}`, and proved:

:::theorem "val1-coleman-polylog"
Let $`\theta` be a non-trivial Dirichlet character of conductor $`N`, let
$`k\geq1` be an integer, and let $`\varepsilon_N` be a primitive $`N`-th root of
unity. Then

*(i)* $`\displaystyle L(\theta,k)=\frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\theta^{-1}(c)\,\Li_{k}(\varepsilon_N^{\,c})`;

*(ii)* $`\displaystyle L_p(\theta,k)=\big(1-\theta(p)p^{-k}\big)\frac{1}{G(\theta^{-1})}\sum_{c\in(\Z/N\Z)^\times}\theta^{-1}(c)\,\Li_{k,p}(\varepsilon_N^{\,c})`.

The case $`k=1` recovers Theorem {bpref "p-adic-value-s1"}[], using
$`\Li_1(z)=-\log(1-z)`. Part (i) rests on the analytic continuation of the
polylogarithm and the special values of {uses "dirichlet-L-function"}[]; part (ii)
is Coleman's theorem on the $`p`-adic polylogarithms $`\Li_{k,p}`.
:::

:::proof "val1-coleman-polylog"
Part (i) is the classical evaluation: exactly as in
{uses "val1-classical-gauss-expansion"}[] one expands $`L(\theta,k)` as a Gauss-sum
combination of $`\sum_{n\geq1}\varepsilon_N^{\,nc}n^{-k}=\Li_k(\varepsilon_N^{\,c})`,
the value at $`z=\varepsilon_N^{\,c}` of the polylogarithm. Part (ii) is Coleman's
theorem. The mechanism is the $`s=1` argument run one level up: rather than
antidifferentiating $`F_\theta` once to obtain $`\widetilde F_\theta`, one takes the
$`k`-th Coleman primitive, whose values at roots of unity are the $`p`-adic
polylogarithms $`\Li_{k,p}(\varepsilon_N^{\,c})`. Reading off $`L_p(\theta,k)` by the
same restriction-to-$`\Zpx` computation $`(1-\varphi\circ\psi)` then produces the
Euler factor $`(1-\theta(p)p^{-k})` (which for $`k=1` recovers
{bpref "p-adic-value-s1"}[]) in front of the polylogarithm sum.
:::

Theorem {bpref "p-adic-value-s1"}[] (ii) is an instance of Perrin-Riou's $`p`-adic
Beilinson conjectures, which describe non-critical special values of $`p`-adic
$`L`-functions of motives in terms of arithmetic data. Specialised to the
Kubota–Leopoldt $`p`-adic $`L`-function, they express $`L_p(\theta,k)` via $`p`-adic
regulators of {bpref "cyclotomic-units"}[cyclotomic units]; the right-hand sides of
{bpref "p-adic-value-s1"}[] (ii) and {bpref "val1-coleman-polylog"}[] (ii) can be
read in these terms. This result also yields a $`p`-adic analogue of the analytic
class number formula.
