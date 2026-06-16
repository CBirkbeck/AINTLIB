import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevDensityBlueprint.Refs
import CebotarevDensityBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Chebotarev: abelian case" =>

The abelian case is reduced to the cyclotomic case by Chebotarev's original
crossing trick. Source: Sharifi 7.2.2 Step 2 (pp. 143--144).

:::lemma_ "lem:cyclic-subgroup-trivial-meet" (lean := "Chebotarev.cyclic_subgroup_meets_G_times_one_trivially")
Let $`G, H` be finite groups, $`\sigma \in G`, $`\tau \in H`. If
$`|G| \mid \operatorname{ord}(\tau)`, then
$`\langle (\sigma, \tau) \rangle \cap (G \times \{1\}) = \{1\}`.
:::

:::proof "lem:cyclic-subgroup-trivial-meet"
Pure group theory. If $`(\sigma^k, \tau^k) \in G \times \{1\}` then $`\tau^k = 1`,
so $`\operatorname{ord}(\tau) \mid k`, hence $`|G| \mid k`, hence $`\sigma^k = 1`.
:::

:::lemma_ "lem:density-S-sigma-tau" (lean := "Chebotarev.liminf_density_S_sigma_ge_card_H_n_div_GH")
Let $`L/K` be a finite abelian Galois extension with $`G = \Gal{L/K}`,
$`\sigma \in G`, and $`m \ge 1` coprime to the discriminant of $`L`, so that
$`\Gal{L(\zeta_m)/K} \cong G \times H` with
$`H = \Gal{K(\zeta_m)/K} \subseteq (\mathbb{Z}/m\mathbb{Z})^\times`. Set
$`H_n = \{\tau \in H : |G| \mid \operatorname{ord}(\tau)\}`. Then
$$`\delta_{\inf}\bigl(\{\mathfrak{p} \subset \mathcal{O}_K : \sigma_\mathfrak{p} = \sigma\}\bigr) \;\ge\; \frac{|H_n|}{|G| \cdot |H|}.`

*Corrected.* An earlier draft of this lemma claimed
$`\delta\bigl(\{\mathfrak{p} : \sigma_\mathfrak{p} = \sigma\}\bigr) = 1/(|G| \cdot |H|)`
— that is mathematically wrong (the set
$`\{\sigma_\mathfrak{p} = \sigma\}` has density $`1/|G|`, not $`1/(|G| \cdot |H|)`).
The actual per-$`m` step that feeds into the proof of
$`\delta(\sigma_\mathfrak{p} = \sigma) = 1/|G|` is the $`\liminf` lower bound above
(Sharifi p. 144).

{uses "lem:cyclic-subgroup-trivial-meet"}[] {uses "thm:chebotarev-cyclotomic"}[]
:::

:::proof "lem:density-S-sigma-tau"
By {bpref "lem:cyclic-subgroup-trivial-meet"}[], the fixed field
$`F = L(\zeta_m)^{\langle (\sigma, \tau) \rangle}` satisfies
$`F(\zeta_m) = L(\zeta_m)`, so the extension $`L(\zeta_m)/F` is cyclotomic. Apply
the cyclotomic case {bpref "thm:chebotarev-cyclotomic"}[] to $`L(\zeta_m)/F` to
obtain $`\delta_F = 1/|\langle (\sigma, \tau) \rangle|`. The conjugacy-class
reduction ({bpref "thm:chebotarev-density"}[] below, Step 1's counting) lifts this to
a $`K`-density of $`1/(|G| \cdot |H|)`.
:::

:::lemma_ "lem:H-n-over-H-formula"
Let $`n = p_1^{k_1} \cdots p_r^{k_r}` with $`p_i` distinct primes, $`k_i \ge 1`. For
an integer $`m \ge 1` with $`m \equiv 1 \pmod{n^j}`, setting
$`j_i = v_{p_i}(m-1) \ge j` and
$`H_n = \{\tau \in (\mathbb{Z}/m\mathbb{Z})^\times : n \mid \operatorname{ord}(\tau)\}`,
$$`\frac{|H_n|}{|(\mathbb{Z}/m\mathbb{Z})^\times|} \;=\; \prod_{i=1}^r \biggl(1 - \frac{p_i^{k_i - 1}}{p_i^{j_i k_i}}\biggr) \;\ge\; \prod_{i=1}^r \biggl(1 - \frac{1}{p_i^{(j-1)k_i + 1}}\biggr).`
:::

:::proof "lem:H-n-over-H-formula"
Direct combinatorial computation on $`(\mathbb{Z}/m\mathbb{Z})^\times` using CRT and
the prime-power factorisation of $`n` (Sharifi p. 144).
:::

:::lemma_ "lem:H-n-over-H-tends-one" (lean := "Chebotarev.H_n_over_H_tends_to_one")
As $`k \to \infty`, $`|H_n|/|(\mathbb{Z}/n^k\mathbb{Z})^\times| \to 1`.

{uses "lem:H-n-over-H-formula"}[]
:::

:::proof "lem:H-n-over-H-tends-one"
The limit of the product formula {bpref "lem:H-n-over-H-formula"}[] as
$`j \to \infty`: each factor tends to $`1`.
:::

:::lemma_ "lem:liminf-ratio-ge-inv-card-G" (lean := "Chebotarev.liminf_ratio_ge_inv_card_G")
For every $`\sigma \in G`,
$`\delta_{\inf}\bigl(\{\mathfrak{p} : \sigma_\mathfrak{p} = \sigma\}\bigr) \ge 1/|G|`.

{uses "lem:density-S-sigma-tau"}[] {uses "lem:H-n-over-H-tends-one"}[]
:::

:::proof "lem:liminf-ratio-ge-inv-card-G"
Take the limit of the per-$`m` bound {bpref "lem:density-S-sigma-tau"}[] as
$`m \to \infty` along $`m \equiv 1 \pmod{|G|^k}`, where $`|H_n|/|H| \to 1` by
{bpref "lem:H-n-over-H-tends-one"}[].

{uses "lem:density-S-sigma-tau"}[] {uses "lem:H-n-over-H-tends-one"}[]
:::

:::lemma_ "lem:ratiosum-fibres-tendsto-one" (lean := "Chebotarev.ratioSum_frobeniusFibres_tendsto_one")
As $`s \downarrow 1`, the sum over $`\sigma \in G` of the density ratios of the
fibres $`\{\mathfrak{p} : \sigma_\mathfrak{p} = \sigma\}` tends to $`1`.

{uses "def:frobenius-class"}[] {uses "lem:finite-ramified-primes"}[]
:::

:::proof "lem:ratiosum-fibres-tendsto-one"
The fibres partition the unramified primes; the ramified primes are finite
({bpref "lem:finite-ramified-primes"}[]) hence contribute density $`0`, so the
partial sums of the fibre ratios equal the ratio for the unramified primes, which
tends to $`1`.

{uses "lem:finite-ramified-primes"}[]
:::

:::lemma_ "lem:pigeonhole-density" (lean := "Chebotarev.tendsto_inv_card_of_liminf_ge_of_sum_tendsto_one")
Let $`g_i` ($`i` in a finite index set of size $`N`) be real functions with
$`\liminf_{s \downarrow 1} g_i \ge 1/N` for each $`i`, and $`\sum_i g_i(s) \to 1` as
$`s \downarrow 1`. Then $`g_i(s) \to 1/N` for every $`i`.
:::

:::proof "lem:pigeonhole-density"
Pure real analysis: the lower bounds and the sum-limit pin every $`g_i` to $`1/N`
by a $`\liminf`/$`\limsup` pigeonhole.
:::

:::theorem "thm:chebotarev-abelian" (lean := "Chebotarev.chebotarev_abelian")
For a finite abelian Galois extension $`L/K` of number fields with $`G = \Gal{L/K}`
and every $`\sigma \in G`,
$$`\delta\bigl(\{\mathfrak{p} \subset \mathcal{O}_K : \sigma_\mathfrak{p} = \sigma\}\bigr) \;=\; \frac{1}{|G|}.`

{uses "def:dirichlet-density"}[] {uses "def:frobenius-class"}[] {uses "lem:liminf-ratio-ge-inv-card-G"}[] {uses "lem:ratiosum-fibres-tendsto-one"}[] {uses "lem:pigeonhole-density"}[]
:::

:::proof "thm:chebotarev-abelian"
The $`|G|` fibres each have $`\liminf \ge 1/|G|`
({bpref "lem:liminf-ratio-ge-inv-card-G"}[]) and their density ratios sum to $`1`
({bpref "lem:ratiosum-fibres-tendsto-one"}[]); the pigeonhole glue
{bpref "lem:pigeonhole-density"}[] forces each fibre's ratio to the limit $`1/|G|`.

{uses "lem:liminf-ratio-ge-inv-card-G"}[] {uses "lem:ratiosum-fibres-tendsto-one"}[] {uses "lem:pigeonhole-density"}[]
:::
