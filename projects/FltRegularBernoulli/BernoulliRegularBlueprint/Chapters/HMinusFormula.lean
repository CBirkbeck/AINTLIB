import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The relative class number h-minus" =>

# Analytic class number formula for h-minus

Let $`K=\mathbb{Q}(\zeta_p)`, $`K^+=\mathbb{Q}(\zeta_p)^+`, and $`n=\frac{p-1}{2}`.
Then $`K` has signature $`(0,n)` and $`K^+` has signature $`(n,0)`.

## The odd L-product as a residue quotient

The factorisation of the cyclotomic Dedekind zeta function into Dirichlet
$`L`-functions gives $`\zeta_K(s)=\prod_{\chi \bmod p} L(s,\chi)`, where the product
runs over all characters modulo $`p`. The even characters are exactly the characters
of $`\operatorname{Gal}(K^+/\mathbb{Q})`, so similarly
$`\zeta_{K^+}(s)=\prod_{\chi\bmod p,\ \chi\text{ even}} L(s,\chi)`. Dividing yields
$$`\frac{\zeta_K(s)}{\zeta_{K^+}(s)}=\prod_{\chi\text{ odd}}L(s,\chi).`
Since every odd character modulo $`p` is non-trivial, every factor on the right is
holomorphic at $`s=1`. Taking residues at $`s=1` therefore gives the following.

:::proposition "prop:odd-L-product-residue" (lean := "BernoulliRegular.residue_ready_factorization_even_odd")
One has
$$`\prod_{\chi\text{ odd}} L(1,\chi) = \frac{\operatorname*{Res}_{s=1}\zeta_K(s)}{\operatorname*{Res}_{s=1}\zeta_{K^+}(s)}.`

{uses "def:cm-real-subfield"}[] {uses "def:dirichlet-character"}[] {uses "def:even-odd"}[]
:::

:::proof "prop:odd-L-product-residue"
The quotient $`\zeta_K(s)/\zeta_{K^+}(s)` has a removable singularity at $`s=1`,
because both numerator and denominator have simple poles there. Its value at $`s=1`
is therefore the ratio of the residues. On the other hand this quotient is exactly
the product of the odd Dirichlet $`L`-functions, all of which are regular at $`s=1`.
:::

## The relative class number formula

The analytic class number formula gives
$$`\operatorname*{Res}_{s=1}\zeta_F(s) = \frac{2^{r_1(F)}(2\pi)^{r_2(F)}h_F R_F}{w_F\sqrt{|D_F|}}`
for every number field $`F`, where $`R_F` is the regulator, $`w_F` the number of
roots of unity, and $`D_F` the discriminant. For the cyclotomic fields under
consideration one uses the standard identities
$$`w_K=2p, \qquad w_{K^+}=2, \qquad R_K = 2^{n-1}R_{K^+}, \qquad |D_K|=p^n|D_{K^+}|.`
Combining these with the definition $`h^- = h_K/h_{K^+}` gives the following.

:::proposition "prop:relative-class-number-L-product" (lean := "BernoulliRegular.hMinus_formula_via_residues, BernoulliRegular.hMinus_formula_of_residue_and_hPlus_cyclotomic_and_gauss")
One has
$$`h^- = \frac{2p\,p^{n/2}}{(2\pi)^n}\prod_{\chi\text{ odd}}L(1,\chi).`

{uses "prop:odd-L-product-residue"}[] {uses "thm:h-factorisation"}[] {uses "def:class-number-h"}[] {uses "def:class-number-hplus"}[] {uses "def:class-number-hminus"}[]
:::

:::proof "prop:relative-class-number-L-product"
Applying the analytic class number formula to $`K` and $`K^+` gives
$$`h_K = \operatorname*{Res}_{s=1}\zeta_K(s)\cdot \frac{w_K\sqrt{|D_K|}}{(2\pi)^n R_K}`
and
$$`h_{K^+} = \operatorname*{Res}_{s=1}\zeta_{K^+}(s)\cdot \frac{w_{K^+}\sqrt{|D_{K^+}|}}{2^n R_{K^+}}.`
Taking the quotient,
$$`h^- = \frac{\operatorname*{Res}_{s=1}\zeta_K(s)}{\operatorname*{Res}_{s=1}\zeta_{K^+}(s)} \cdot \frac{w_K}{w_{K^+}} \cdot \frac{2^n R_{K^+}}{(2\pi)^n R_K} \cdot \sqrt{\frac{|D_K|}{|D_{K^+}|}}.`
Substituting the four identities above gives
$$`h^- = \frac{2p\,p^{n/2}}{(2\pi)^n} \frac{\operatorname*{Res}_{s=1}\zeta_K(s)}{\operatorname*{Res}_{s=1}\zeta_{K^+}(s)}.`
Now apply {bpref "prop:odd-L-product-residue"}[].
:::

## The product of the odd Gauss sums

For a primitive character $`\chi` modulo $`p`, write
$`\tau(\chi)=\sum_{a\in \mathbb{Z}/p\mathbb{Z}}\chi(a)e^{2\pi i a/p}`. The standard
identity $`\tau(\chi)\tau(\chi^{-1}) = \chi(-1)p` shows that each inverse pair of odd
characters contributes $`-p` to the product of all odd Gauss sums.

:::lemma_ "lem:odd-gauss-product" (lean := "BernoulliRegular.rawGaussProduct, BernoulliRegular.cyclotomicHGaussGoal_holds")
One has $`\prod_{\chi\text{ odd}} \tau(\chi) = i^n p^{n/2}`.

{uses "def:gauss-sum"}[] {uses "prop:gauss-norm"}[] {uses "def:even-odd"}[]
:::

:::proof "lem:odd-gauss-product"
If $`p\equiv 1\pmod 4`, then the quadratic character is even, so no odd character is
self-inverse. The odd characters split into $`n/2` inverse pairs, each contributing
$`-p`. Therefore $`\prod_{\chi\text{ odd}}\tau(\chi)=(-p)^{n/2}=i^n p^{n/2}`.

If $`p\equiv 3\pmod 4`, then the quadratic character $`\lambda` is odd and is the
unique self-inverse odd character. The remaining odd characters split into
$`(n-1)/2` inverse pairs, so
$`\prod_{\chi\text{ odd}}\tau(\chi) = \tau(\lambda)(-p)^{(n-1)/2}`. The classical
quadratic Gauss sum evaluation gives $`\tau(\lambda)=i\sqrt p`. Hence
$`\prod_{\chi\text{ odd}}\tau(\chi) = i\sqrt p\,(-p)^{(n-1)/2} = i^n p^{n/2}`.
:::

:::theorem "thm:hminus-formula" (lean := "BernoulliRegular.hMinus_formula")
**Analytic formula for $`\hminus`.** The relative class number satisfies
$$`h^- = 2p\prod_{\chi\text{ odd}} \left(-\frac12\,B_{1,\chi^{-1}}\right).`

{uses "prop:relative-class-number-L-product"}[] {uses "cor:L1-odd"}[] {uses "lem:odd-gauss-product"}[] {uses "def:gen-bernoulli"}[]
:::

:::proof "thm:hminus-formula"
There are exactly $`n=(p-1)/2` odd characters modulo $`p`. By
{bpref "prop:relative-class-number-L-product"}[],
$`h^- = \frac{2p\,p^{n/2}}{(2\pi)^n} \prod_{\chi\text{ odd}}L(1,\chi)`. For each odd
character $`\chi`, {bpref "cor:L1-odd"}[] gives
$`L(1,\chi)=\frac{\pi i\,\tau(\chi)}{p}\,B_{1,\chi^{-1}}`. Multiplying over all odd
characters yields
$$`\prod_{\chi\text{ odd}}L(1,\chi) = \left(\frac{\pi i}{p}\right)^n \left(\prod_{\chi\text{ odd}}\tau(\chi)\right) \left(\prod_{\chi\text{ odd}}B_{1,\chi^{-1}}\right).`
By {bpref "lem:odd-gauss-product"}[], this becomes
$$`\prod_{\chi\text{ odd}}L(1,\chi) = \frac{\pi^n i^{2n}}{p^{n/2}} \prod_{\chi\text{ odd}}B_{1,\chi^{-1}} = \frac{\pi^n(-1)^n}{p^{n/2}} \prod_{\chi\text{ odd}}B_{1,\chi^{-1}}.`
Substituting back gives
$$`h^- = \frac{2p\,p^{n/2}}{(2\pi)^n} \cdot \frac{\pi^n(-1)^n}{p^{n/2}} \prod_{\chi\text{ odd}}B_{1,\chi^{-1}} = 2p\left(-\frac12\right)^n \prod_{\chi\text{ odd}}B_{1,\chi^{-1}}.`
Since there are exactly $`n` odd characters, this is precisely
$`2p\prod_{\chi\text{ odd}} \left(-\frac12\,B_{1,\chi^{-1}}\right)`.
:::
