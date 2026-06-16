import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevDensityBlueprint.Refs
import CebotarevDensityBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Dirichlet density" =>

Throughout, $`K` denotes a number field, $`\mathcal{O}_K` its ring of integers,
and $`\mathfrak{p}` ranges over nonzero prime ideals of $`\mathcal{O}_K` with
absolute norm $`\Norm\mathfrak{p} = [\mathcal{O}_K : \mathfrak{p}]`.

:::definition "def:dirichlet-density" (lean := "Chebotarev.HasDirichletDensity")
A set $`S` of nonzero prime ideals of $`\mathcal{O}_K` has *Dirichlet density*
$`\delta \in \mathbb{R}`, written $`\delta(S) = \delta`, if
$$`\lim_{s \to 1^+} \frac{\displaystyle\sum_{\mathfrak{p} \in S} \Norm\mathfrak{p}^{-s}}{\displaystyle\sum_{\mathfrak{p}} \Norm\mathfrak{p}^{-s}} = \delta,`
where the denominator sum runs over all nonzero prime ideals of $`\mathcal{O}_K`.
:::

The denominator is asymptotically $`\log\bigl(1/(s-1)\bigr)` as $`s \downarrow 1`
(Sharifi Prop. 7.1.12, p. 140); the lemmas below break out the analytic
ingredients.

:::lemma_ "lem:prime-zeta-higher-tail-bounded" (lean := "Chebotarev.primeIdealZetaHigherTail_bounded")
The higher-power tail of the log-Euler-product
$$`\sum_{\mathfrak{p},\, k \ge 2} \frac{\Norm\mathfrak{p}^{-2s}}{1 - \Norm\mathfrak{p}^{-s}}`
is bounded on a right neighbourhood of $`s = 1`.
:::

:::lemma_ "lem:logzeta-eq-primesum-bounded" (lean := "Chebotarev.logDedekindZeta_sub_primeIdealZetaSum_bounded")
Euler-product-log identity: $`\bigl|\log\zeta_K(s) - \sum_\mathfrak{p} \Norm\mathfrak{p}^{-s}\bigr| \le C`
on a right neighbourhood of $`1`.

{uses "lem:prime-zeta-higher-tail-bounded"}[]
:::

:::proof "lem:logzeta-eq-primesum-bounded"
We have $`\log\zeta_K(s) = \sum_\mathfrak{p} \Norm\mathfrak{p}^{-s} + \sum_{\mathfrak{p},\, k \ge 2} \Norm\mathfrak{p}^{-ks}/k`;
the tail is bounded by {bpref "lem:prime-zeta-higher-tail-bounded"}[].

{uses "lem:prime-zeta-higher-tail-bounded"}[]
:::

:::lemma_ "lem:logzeta-eq-loginv-bounded" (lean := "Chebotarev.logDedekindZeta_sub_log_inv_sub_one_bounded")
Simple-pole identity: $`\bigl|\log\zeta_K(s) - \log(1/(s-1))\bigr| \le C` on a
right neighbourhood of $`1`.
:::

:::proof "lem:logzeta-eq-loginv-bounded"
From the simple pole of $`\zeta_K` at $`s = 1` (mathlib's
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`): $`(s-1)\zeta_K(s) \to r > 0`
(the residue, `dedekindZeta_residue_pos`), so
$`\log\zeta_K(s) - \log(1/(s-1)) = \log\bigl((s-1)\zeta_K(s)\bigr)` converges to
$`\log r` and is therefore bounded near $`1`.
:::

:::lemma_ "lem:prime-zeta-ge-log-minus-bounded" (lean := "Chebotarev.log_minus_bounded_le_primeIdealZetaSum")
There is a constant $`C` such that, for $`s > 1` in a right neighbourhood of
$`1`,
$$`\sum_{\mathfrak{p}} \Norm\mathfrak{p}^{-s} \;\ge\; \log\frac{1}{s-1} - C.`

{uses "lem:logzeta-eq-primesum-bounded"}[] {uses "lem:logzeta-eq-loginv-bounded"}[]
:::

:::proof "lem:prime-zeta-ge-log-minus-bounded"
Chain the two identities {bpref "lem:logzeta-eq-primesum-bounded"}[] and
{bpref "lem:logzeta-eq-loginv-bounded"}[]:
$`\sum_\mathfrak{p} \Norm\mathfrak{p}^{-s} \ge \log\zeta_K(s) - C_1 \ge \log(1/(s-1)) - C_1 - C_2`.

{uses "lem:logzeta-eq-primesum-bounded"}[] {uses "lem:logzeta-eq-loginv-bounded"}[]
:::

:::lemma_ "lem:prime-zeta-le-log-plus-bounded" (lean := "Chebotarev.primeIdealZetaSum_le_log_plus_bounded")
There is a constant $`C'` such that, for $`s > 1` in a right neighbourhood of
$`1`,
$$`\sum_{\mathfrak{p}} \Norm\mathfrak{p}^{-s} \;\le\; \log\frac{1}{s-1} + C'.`

{uses "lem:logzeta-eq-primesum-bounded"}[] {uses "lem:logzeta-eq-loginv-bounded"}[]
:::

:::proof "lem:prime-zeta-le-log-plus-bounded"
The same two identities {bpref "lem:logzeta-eq-primesum-bounded"}[] and
{bpref "lem:logzeta-eq-loginv-bounded"}[], transposed.

{uses "lem:logzeta-eq-primesum-bounded"}[] {uses "lem:logzeta-eq-loginv-bounded"}[]
:::

:::lemma_ "lem:tendsto-ratio-one-of-log-pm-bounded" (lean := "Chebotarev.tendsto_ratio_one_of_log_pm_bounded")
Let $`f : (1, \infty) \to \mathbb{R}`. If $`f` is sandwiched as
$`\log\bigl(1/(s-1)\bigr) - C \le f(s) \le \log\bigl(1/(s-1)\bigr) + C'` on a right
neighbourhood of $`1`, then $`f(s)/\log\bigl(1/(s-1)\bigr) \to 1` as
$`s \downarrow 1`.
:::

:::proof "lem:tendsto-ratio-one-of-log-pm-bounded"
Since $`\log\bigl(1/(s-1)\bigr) \to \infty` as $`s \downarrow 1`, the additive
constants $`C, C'` wash out under division, and the squeeze gives the limit $`1`.
:::

:::lemma_ "lem:prime-ideal-sum-log" (lean := "Chebotarev.primeIdealZetaSum_univ_tendsto_log")
As $`s \downarrow 1`,
$$`\sum_{\mathfrak{p}} \Norm\mathfrak{p}^{-s} \sim \log\frac{1}{s-1}.`

{uses "lem:prime-zeta-ge-log-minus-bounded"}[] {uses "lem:prime-zeta-le-log-plus-bounded"}[] {uses "lem:tendsto-ratio-one-of-log-pm-bounded"}[]
:::

:::proof "lem:prime-ideal-sum-log"
Combine the lower bound {bpref "lem:prime-zeta-ge-log-minus-bounded"}[] and the
upper bound {bpref "lem:prime-zeta-le-log-plus-bounded"}[] into a two-sided
$`\log\bigl(1/(s-1)\bigr) \pm O(1)` sandwich, then apply
{bpref "lem:tendsto-ratio-one-of-log-pm-bounded"}[] to extract the ratio limit.

{uses "lem:prime-zeta-ge-log-minus-bounded"}[] {uses "lem:prime-zeta-le-log-plus-bounded"}[] {uses "lem:tendsto-ratio-one-of-log-pm-bounded"}[]
:::

# Density API

The following routine API lemmas are used by the proofs of the corollaries in the
final chapter.

:::lemma_ "lem:has-density-finite" (lean := "Chebotarev.hasDirichletDensity_of_finite")
A finite set of prime ideals has Dirichlet density $`0`.

{uses "def:dirichlet-density"}[]
:::

:::proof "lem:has-density-finite"
The numerator $`\sum_{\mathfrak{p} \in S} \Norm\mathfrak{p}^{-s}` is bounded as
$`s \to 1^+` (a finite sum of bounded terms), while the denominator
$`\sum_\mathfrak{p} \Norm\mathfrak{p}^{-s} \to \infty` by
{bpref "lem:prime-ideal-sum-log"}[]; the ratio tends to $`0`.
:::

:::lemma_ "lem:density-implies-lower" (lean := "Chebotarev.HasDirichletDensity.hasLower")
If $`S` has Dirichlet density $`\delta`, then its lower Dirichlet density is also
$`\delta`.

{uses "def:dirichlet-density"}[]
:::

:::proof "lem:density-implies-lower"
Convergence of the ratio implies the liminf and limsup coincide with the limit;
specifically the liminf equals $`\delta`.
:::
