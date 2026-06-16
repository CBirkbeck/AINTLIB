import Verso
import VersoManual
import VersoBlueprint
import CebotarevDensity
import CebotarevDensityBlueprint.Refs
import CebotarevDensityBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Zeta factorisation for abelian extensions" =>

For an abelian Galois extension $`L/K` of number fields with $`G = \Gal{L/K}`, the
Dedekind zeta function $`\zeta_L` factors as a product of Hecke $`L`-functions
indexed by characters of $`G`. This is the analytic engine of the cyclotomic case
of Chebotarev.

:::definition "def:galois-character" (lean := "Chebotarev.galoisCharacter")
A *character of $`G`* is a group homomorphism $`\chi : G \to \mathbb{C}^\times`.
:::

:::lemma_ "lem:artin-euler-product-abelian" (lean := "Chebotarev.exists_artinLSeries_eulerProduct_abelian")
For an abelian character $`\chi : G \to \mathbb{C}^\times`, there is a function
$`L(\chi, \cdot) : \mathbb{C} \to \mathbb{C}` such that on $`\operatorname{Re}(s) > 1`,
$$`L(\chi, s) \;=\; \prod_\mathfrak{p} \bigl(1 - \chi(\Frob_\mathfrak{p})\, \Norm\mathfrak{p}^{-s}\bigr)^{-1},`
where the product runs over primes $`\mathfrak{p}` of $`\mathcal{O}_K` unramified in
$`L`, with the convention $`\chi(\mathfrak{p}) = 0` on ramified primes.

{uses "def:galois-character"}[] {uses "def:frobenius-class"}[]
:::

:::proof "lem:artin-euler-product-abelian"
Sharifi Prop. 7.1.18 (p. 141). The Euler product converges absolutely on
$`\operatorname{Re}(s) > 1` by comparison with $`\zeta_K`.
:::

:::lemma_ "lem:dedekind-local-factor" (lean := "Chebotarev.dedekindZeta_local_factor_eq_product_artin_local")
For each unramified prime $`\mathfrak{p}` of $`\mathcal{O}_K`, the local Euler factor
of $`\zeta_L` at $`\mathfrak{p}` factors as
$$`\prod_{\mathfrak{P} \mid \mathfrak{p}} \bigl(1 - \Norm\mathfrak{P}^{-s}\bigr)^{-1} \;=\; \prod_\chi \bigl(1 - \chi(\Frob_\mathfrak{p})\, \Norm\mathfrak{p}^{-s}\bigr)^{-1}.`

{uses "lem:artin-euler-product-abelian"}[]
:::

:::proof "lem:dedekind-local-factor"
Standard cyclic-group character theory applied to the residue Galois group: the
characters of $`\Gal{(\mathcal{O}_L/\mathfrak{P})/(\mathcal{O}_K/\mathfrak{p})}`
separate elements, and the indicated product over $`\chi` recovers the local factor
(Sharifi 7.1.16 step at $`\mathfrak{p}`).
:::

:::lemma_ "lem:character-sum-geom-numbers" (lean := "Chebotarev.character_sum_geometry_of_numbers_bound")
For a nontrivial character $`\chi : G \to \mathbb{C}^\times`, there is a constant
$`C` such that
$$`\biggl\lVert \sum_{\Norm\mathfrak{a} \le N} \chi(\mathfrak{a}) \biggr\rVert \;\le\; C \cdot N^{1 - 1/[K:\mathbb{Q}]} \qquad \text{for all } N \ge 1.`
:::

:::proof "lem:character-sum-geom-numbers"
Geometry-of-numbers count of ideals in a norm-bounded region (Sharifi 7.1.19,
p. 142, step 1). The per-residue-class count is $`C N + O(N^{1 - 1/[K:\mathbb{Q}]})`;
summing over $`\chi(\mathfrak{a}) = \zeta` for $`\zeta` a root of unity, the $`C N`
contributions cancel by $`\sum_\zeta \zeta = 0`.
:::

:::lemma_ "lem:artin-analytic-extension" (lean := "Chebotarev.artinLSeries_analytic_extension")
For every nontrivial character $`\chi : G \to \mathbb{C}^\times`, the Dirichlet
series $`L(\chi, s) = \sum_{\mathfrak{a}} \chi(\mathfrak{a})\, \Norm\mathfrak{a}^{-s}`
extends to a function analytic on $`\operatorname{Re}(s) > 1 - 1/[K:\mathbb{Q}]`,
agreeing with the Euler product on $`\operatorname{Re}(s) > 1`. In particular,
$`L(\chi, 1)` is well-defined.

{uses "lem:artin-euler-product-abelian"}[] {uses "lem:character-sum-geom-numbers"}[]
:::

:::proof "lem:artin-analytic-extension"
Combine {bpref "lem:character-sum-geom-numbers"}[] (Sharifi 7.1.19 step 1a) with
Sharifi Lemma 7.1.5 (p. 138, a generic Dirichlet-series convergence criterion from a
polynomial bound on partial sums): given
$`\bigl|\sum_{n \le N} a_n\bigr| \le C N^{u}`, the Dirichlet series
$`\sum_n a_n n^{-s}` converges absolutely and uniformly on every compact subset of
$`\operatorname{Re}(s) > u`. Applied to $`a_{\mathfrak{a}} = \chi(\mathfrak{a})` with
$`u = 1 - 1/[K:\mathbb{Q}]`, the series defines an analytic function on
$`\operatorname{Re}(s) > 1 - 1/[K:\mathbb{Q}]`.
:::

:::lemma_ "lem:artin-one-ne-zero" (lean := "Chebotarev.artinLSeries_one_ne_zero")
For every nontrivial character $`\chi : G \to \mathbb{C}^\times`,
$`L(\chi, 1) \ne 0`. (Here $`L(\chi, 1)` refers to the analytic extension of
{bpref "lem:artin-analytic-extension"}[].)

{uses "lem:artin-analytic-extension"}[]
:::

:::proof "lem:artin-one-ne-zero"
Sharifi 7.1.19 step 2 (p. 142). Write $`\log\zeta_L(t) = \sum_\chi \log L(\chi, t)`
for $`t > 1`. Up to a bounded function as $`t \to 1^+`, the right side has absolute
value at least $`\bigl(1 - \sum_\chi m_\chi\bigr)\log(t-1)^{-1}`, where $`m_\chi` is
the order of vanishing of $`L(\chi, s)` at $`s = 1`. If any $`m_\chi \ge 1`, this is
at most $`0 \cdot \log(t-1)^{-1}`, contradicting
$`\log\zeta_L(s) \sim \log(s-1)^{-1}`.
:::

:::theorem "thm:dedekind-zeta-factorisation" (lean := "Chebotarev.dedekindZeta_eq_prod_artinDirichletSeries")
Let $`L/K` be a finite abelian Galois extension of number fields. There is a family
of functions $`\{L(\chi, \cdot) : \chi \in \widehat{G}\}`, each holomorphic on
$`\operatorname{Re}(s) > 1`, satisfying for $`\operatorname{Re}(s) > 1`
$$`\zeta_L(s) \;=\; \Bigl(\prod_{\chi \in \widehat{G}} L(\chi, s)\Bigr) \cdot R(s),`
together with $`L(\mathbf{1}, s) = \zeta_K(s)` and $`L(\chi, 1) \ne 0` for every
$`\chi \ne \mathbf{1}`. Here each $`L(\chi, \cdot)` is the Euler product over the
*unramified* primes only, and the correction factor $`R(s)` is the finite product of
the local factors $`(1 - \Norm\mathfrak{P}^{-s})^{-1}` over the primes $`\mathfrak{P}`
of $`\mathcal{O}_L` lying above a ramified prime of $`\mathcal{O}_K`. The naive
identity $`\zeta_L = \prod_\chi L(\chi, \cdot)` is false in this formulation,
because $`L(\chi, \cdot)` drops the ramified primes whereas $`\zeta_L` keeps them;
$`R` collects exactly the dropped factors and is nonzero for real $`s > 1`.

{uses "def:galois-character"}[] {uses "lem:dedekind-local-factor"}[] {uses "lem:artin-one-ne-zero"}[]
:::

:::proof "thm:dedekind-zeta-factorisation"
Compose {bpref "lem:dedekind-local-factor"}[] prime by prime over the unramified
primes, using the absolute convergence of the global Euler product, and split off the
finitely many ramified local factors into $`R(s)`; combine with the non-vanishing
{bpref "lem:artin-one-ne-zero"}[].

{uses "lem:dedekind-local-factor"}[] {uses "lem:artin-one-ne-zero"}[]
:::
