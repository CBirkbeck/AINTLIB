import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevDensityBlueprint.Refs
import CebotarevDensityBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Chebotarev: cyclotomic case" =>

For a cyclotomic extension $`L = K(\zeta_m)`, Chebotarev's theorem reduces directly
to Dirichlet's argument. Source: Sharifi 7.2.1 (pp. 142--143).

:::lemma_ "lem:cyclotomic-frobenius-norm-power" (lean := "Chebotarev.cyclotomic_frobenius_acts_as_norm_power")
Let $`L = K(\zeta_m)`, $`\mathfrak{p}` a nonzero prime of $`\mathcal{O}_K`
unramified in $`L`, and $`\mathfrak{P}` a prime of $`\mathcal{O}_L` above
$`\mathfrak{p}`. Then for every primitive $`m`-th root of unity $`\zeta \in L`,
$$`\Frob_\mathfrak{P}(\zeta) \;=\; \zeta^{\Norm\mathfrak{p}}.`

{uses "def:frobenius-at"}[]
:::

:::proof "lem:cyclotomic-frobenius-norm-power"
By the defining property of $`\Frob_\mathfrak{P}` (it acts as the
$`\Norm\mathfrak{p}`-power map on $`\mathcal{O}_L/\mathfrak{P}`) combined with the
fact that $`\zeta_m` lifts isomorphically from the residue field for
$`\mathfrak{p} \nmid m`.
:::

:::lemma_ "lem:log-artin-asymp-character-sum" (lean := "Chebotarev.log_artinLSeries_asymp_character_sum")
For every character $`\chi` of $`G`, the partial sum
$`\sum_\mathfrak{p} \chi(\Frob_\mathfrak{p})\, \Norm\mathfrak{p}^{-s}` over
$`\mathfrak{p}` unramified in $`L` is bounded by $`C\log(1/(s-1)) + C` for some
constant $`C`, in a right neighbourhood of $`s = 1`.

{uses "thm:dedekind-zeta-factorisation"}[] {uses "def:frobenius-class"}[]
:::

:::proof "lem:log-artin-asymp-character-sum"
Expand $`\log L(\chi, s)` via the Euler product
{bpref "lem:artin-euler-product-abelian"}[]; the higher-power tail is bounded
analogously to {bpref "lem:prime-zeta-higher-tail-bounded"}[].
:::

:::lemma_ "lem:character-orthogonality-eq" (lean := "Chebotarev.character_orthogonality_cyclotomic_eq")
Let $`L = K(\zeta_m)`, $`\sigma \in G`, and $`\mathfrak{p}` a nonzero prime of
$`\mathcal{O}_K` unramified in $`L` with $`\sigma_\mathfrak{p}` the conjugacy class
of $`\sigma`. Then
$$`\sum_{\chi \in \widehat{G}} \chi(\sigma)\, \chi(\Frob_\mathfrak{p})^{-1} \;=\; |G|.`

{uses "def:galois-character"}[] {uses "def:frobenius-class"}[]
:::

:::lemma_ "lem:character-orthogonality-ne" (lean := "Chebotarev.character_orthogonality_cyclotomic_ne")
Let $`L = K(\zeta_m)`, $`\sigma \in G`, and $`\mathfrak{p}` a nonzero prime of
$`\mathcal{O}_K` unramified in $`L` whose Frobenius class is not the conjugacy class
of $`\sigma`. Then
$$`\sum_{\chi \in \widehat{G}} \chi(\sigma)\, \chi(\Frob_\mathfrak{p})^{-1} \;=\; 0.`

{uses "def:galois-character"}[] {uses "def:frobenius-class"}[]
:::

:::proof "lem:character-orthogonality-ne"
Standard finite-group character orthogonality for the dual of $`G` (Sharifi 7.2.1
step at p. 142). Under the isomorphism $`G \cong (\mathbb{Z}/m\mathbb{Z})^\times`
from {bpref "lem:cyclotomic-frobenius-norm-power"}[], $`\chi(\Frob_\mathfrak{p})`
depends only on $`\Norm\mathfrak{p} \bmod m`, and the sum reduces to the
orthogonality relation on the cyclic group $`(\mathbb{Z}/m\mathbb{Z})^\times`.
:::

:::lemma_ "lem:primesum-fibre-asymp" (lean := "Chebotarev.primeIdealZetaSum_frobeniusFibre_asymp")
Let $`L = K(\zeta_m)` and $`\sigma \in G`. The Frobenius-fibre prime sum is
asymptotic to $`(1/|G|)\log(1/(s-1))`:
$$`\lim_{s \downarrow 1} \frac{\sum_{\mathfrak{p}:\, \sigma_\mathfrak{p} = \sigma} \Norm\mathfrak{p}^{-s}}{\log(1/(s-1))} \;=\; \frac{1}{|G|}.`

{uses "lem:log-artin-asymp-character-sum"}[] {uses "lem:character-orthogonality-eq"}[] {uses "lem:character-orthogonality-ne"}[] {uses "lem:artin-one-ne-zero"}[]
:::

:::proof "lem:primesum-fibre-asymp"
Multiply $`\log L(\chi, s)` by $`\chi(\sigma)^{-1}` and sum over $`\chi`: the
orthogonality relations ({bpref "lem:character-orthogonality-eq"}[] and
{bpref "lem:character-orthogonality-ne"}[]) pick out the primes with Frobenius
$`\sigma`, giving
$`\sum_\chi \chi(\sigma)^{-1}\log L(\chi, s) \sim |G| \sum_{\sigma_\mathfrak{p} = \sigma} \Norm\mathfrak{p}^{-s}`;
on the other hand it is $`\sim \log\zeta_K(s) \sim \log(1/(s-1))` (only $`\chi = \mathbf{1}`
contributes a pole, by {bpref "lem:artin-one-ne-zero"}[]). Divide.

{uses "lem:character-orthogonality-eq"}[] {uses "lem:character-orthogonality-ne"}[] {uses "lem:artin-one-ne-zero"}[]
:::

:::lemma_ "lem:ratio-glue-numerator" (lean := "Chebotarev.tendsto_ratio_of_log_asymp_numerator")
If $`\operatorname{num}(s)/\log(1/(s-1)) \to c` and
$`\operatorname{den}(s)/\log(1/(s-1)) \to 1` as $`s \downarrow 1`, then
$`\operatorname{num}(s)/\operatorname{den}(s) \to c`.
:::

:::proof "lem:ratio-glue-numerator"
Write $`\operatorname{num}/\operatorname{den} = (\operatorname{num}/L)/(\operatorname{den}/L)`
with $`L = \log(1/(s-1))`, which is positive (hence nonzero) for $`s \in (1,2)` since
$`1/(s-1) > 1`; apply the quotient rule for limits and cancel $`L`.
:::

:::lemma_ "lem:cyclotomic-density-two-sided" (lean := "Chebotarev.cyclotomic_density_from_two_sided_asymp")
Let $`L = K(\zeta_m)` and $`\sigma \in G`. Then
$$`\lim_{s \downarrow 1} \frac{\sum_{\mathfrak{p}:\, \sigma_\mathfrak{p} = \sigma} \Norm\mathfrak{p}^{-s}}{\sum_\mathfrak{p} \Norm\mathfrak{p}^{-s}} \;=\; \frac{1}{|G|}.`

{uses "lem:primesum-fibre-asymp"}[] {uses "lem:prime-ideal-sum-log"}[] {uses "lem:ratio-glue-numerator"}[]
:::

:::proof "lem:cyclotomic-density-two-sided"
The numerator asymptotic {bpref "lem:primesum-fibre-asymp"}[]
($`\operatorname{num} \sim (1/|G|)\log(1/(s-1))`) and the denominator asymptotic
{bpref "lem:prime-ideal-sum-log"}[] ($`\operatorname{den} \sim \log(1/(s-1))`) feed
the ratio glue {bpref "lem:ratio-glue-numerator"}[].

{uses "lem:primesum-fibre-asymp"}[] {uses "lem:prime-ideal-sum-log"}[] {uses "lem:ratio-glue-numerator"}[]
:::

:::theorem "thm:chebotarev-cyclotomic" (lean := "Chebotarev.chebotarev_cyclotomic")
For $`K` a number field, $`m \ge 1`, $`L = K(\zeta_m)`, and every
$`\sigma \in G = \Gal{L/K}`,
$$`\delta\bigl(\{\mathfrak{p} \subset \mathcal{O}_K : \sigma_\mathfrak{p} = \sigma\}\bigr) \;=\; \frac{1}{|G|}.`

{uses "def:dirichlet-density"}[] {uses "def:frobenius-class"}[] {uses "lem:cyclotomic-density-two-sided"}[]
:::
