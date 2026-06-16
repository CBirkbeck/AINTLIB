import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The final proof of Kummer's criterion" =>

This chapter assembles the preceding ingredients into Kummer's criterion. The
mathematical content is the equivalence
$$`p\text{ regular} \quad\Longleftrightarrow\quad \forall k,\ 1\le k,\ 2k\le p-3,\quad p\nmid (B_{2k})_{\mathrm{num}}.`

# The minus class-number criterion

The analytic and $`p`-adic work on the relative class number gives the following
criterion.

:::theorem "thm:hminus-bernoulli-final" (lean := "BernoulliRegular.p_dvd_hMinus_iff_p_dvd_some_bernoulli")
**Minus class-number criterion.** Let $`p` be an odd prime and let $`K` be a
cyclotomic field of conductor $`p`. Then
$$`p\mid h^-(K) \quad\Longleftrightarrow\quad \exists k,\ 1\le k,\ 2k\le p-3,\quad p\mid (B_{2k})_{\mathrm{num}}.`

{uses "thm:hminus-formula"}[] {uses "thm:boundary-character-bernoulli"}[] {uses "thm:bernoulli-padicInt-below"}[] {uses "cor:bernoulli-den-coprime"}[]
:::

:::proof "thm:hminus-bernoulli-final"
Starting from the analytic class-number formula for $`h^-`, one rewrites the
odd-character product in terms of Teichmuller characters. The boundary character
contributes the unique factor containing the pole at $`p-1`; after the explicit
leading factor $`2p` is included, that boundary contribution is congruent to $`1`
modulo $`p`. The remaining factors are
$`-\frac12 B_{1,\omega^j}` ($`1\le j\le p-4`, $`j` odd). Kummer congruences replace
these factors modulo $`p` by $`-\frac12\,\frac{B_{j+1}}{j+1}`. Writing $`j+1=2k`, the
range becomes exactly $`1\le k` and $`2k\le p-3`. For these indices the denominator of
$`B_{2k}` is prime to $`p`, and so is $`2k`. Hence the corresponding $`p`-adic factor
is a unit if and only if $`p` does not divide the numerator of $`B_{2k}`. A finite
product in $`\mathbb{Z}_p` is a non-unit if and only if one of its factors is a
non-unit. This identifies $`p\mid h^-(K)` with the existence of a Bernoulli numerator
in the displayed range divisible by $`p`.
:::

We shall also use the contrapositive form of this criterion.

:::corollary "cor:hminus-not-dvd-bernoulli-nonzero" (lean := "BernoulliRegular.bernoulli_nonzero_of_not_dvd_hMinus")
**Non-divisibility of $`h^-` gives Bernoulli non-divisibility.** If
$`p\nmid h^-(K)`, then for every $`j` with $`1\le j` and $`2j\le p-3`,
$`p\nmid (B_{2j})_{\mathrm{num}}`.

{uses "thm:hminus-bernoulli-final"}[]
:::

:::proof "cor:hminus-not-dvd-bernoulli-nonzero"
This is the contrapositive of {bpref "thm:hminus-bernoulli-final"}[]. If some
Bernoulli numerator in the range were divisible by $`p`, the right-hand side of the
criterion would hold, and therefore $`p\mid h^-(K)`.
:::

# The plus-to-minus divisibility step

The cyclotomic-unit theorem from the previous chapter turns the contrapositive of the
minus criterion into a statement about $`h^+`.

:::theorem "thm:not-dvd-hplus-of-not-dvd-hminus-units" (lean := "BernoulliRegular.not_dvd_hPlus_of_not_dvd_hMinus_units")
**Contrapositive plus-to-minus divisibility.** Let $`p` be an odd prime and let $`K`
be a cyclotomic field of conductor $`p`. If $`p\nmid h^-(K)`, then $`p\nmid h^+(K)`.

{uses "cor:hminus-not-dvd-bernoulli-nonzero"}[] {uses "thm:bernoulli-nonzero-index"}[] {uses "thm:cyclotomic-unit-index-hplus"}[] {uses "lem:CPlus-index-normalized-index"}[]
:::

:::proof "thm:not-dvd-hplus-of-not-dvd-hminus-units"
Assume $`p\nmid h^-(K)`. By {bpref "cor:hminus-not-dvd-bernoulli-nonzero"}[], all
Bernoulli numerators $`(B_{2j})_{\mathrm{num}}` in Kummer's range are prime to $`p`.
The cyclotomic-unit theorem {bpref "thm:bernoulli-nonzero-index"}[] therefore gives
$`p\nmid [E^+:C^+_{\mathrm{sq}}]`. Suppose, for contradiction, that $`p\mid h^+(K)`.
The prime-conductor cyclotomic-unit index theorem
{bpref "thm:cyclotomic-unit-index-hplus"}[] gives $`p\mid [E^+:C^+_{\mathrm{norm}}]`.
By the odd-primary comparison of the two cyclotomic-unit subgroups,
{bpref "lem:CPlus-index-normalized-index"}[], this is equivalent to
$`p\mid [E^+:C^+_{\mathrm{sq}}]`, contradicting the index non-divisibility already
obtained. Hence $`p\nmid h^+(K)`.
:::

:::corollary "cor:hplus-to-hminus-units" (lean := "BernoulliRegular.weakReflection_dvd_hMinus_of_dvd_hPlus_units")
**Plus divisibility implies minus divisibility.** If $`p\mid h^+(K)`, then
$`p\mid h^-(K)`.

{uses "thm:not-dvd-hplus-of-not-dvd-hminus-units"}[]
:::

:::proof "cor:hplus-to-hminus-units"
Argue by contradiction. If $`p\nmid h^-(K)`, then
{bpref "thm:not-dvd-hplus-of-not-dvd-hminus-units"}[] gives $`p\nmid h^+(K)`,
contradicting the hypothesis. Therefore $`p\mid h^-(K)`.
:::

# The total class number

Recall from {bpref "thm:h-factorisation"}[] that $`h(K)=h^+(K)\,h^-(K)`. The previous
corollary lets us reduce divisibility of the total class number to divisibility of
the minus class number.

:::theorem "thm:dvd-h-iff-dvd-hminus-units" (lean := "BernoulliRegular.dvd_h_iff_dvd_hMinus_of_dvd_hPlus_imp")
**Total class-number divisibility.** For odd $`p`, assume that
$`p\mid h^+(K)\Longrightarrow p\mid h^-(K)`. Then
$$`p\mid h(K) \quad\Longleftrightarrow\quad p\mid h^-(K).`

{uses "thm:h-factorisation"}[] {uses "cor:hplus-to-hminus-units"}[]
:::

:::proof "thm:dvd-h-iff-dvd-hminus-units"
The implication from right to left is immediate from $`h(K)=h^+(K)h^-(K)`.
Conversely, suppose $`p\mid h(K)`. Since $`h(K)=h^+(K)h^-(K)` and $`p` is prime,
Euclid's lemma gives $`p\mid h^+(K)` or $`p\mid h^-(K)`. In the second case we are
done. In the first case, the assumed implication converts $`p\mid h^+(K)` into
$`p\mid h^-(K)`. Thus $`p\mid h^-(K)` in all cases.
:::

:::theorem "thm:dvd-h-iff-bernoulli-units" (lean := "BernoulliRegular.dvd_h_iff_exists_dvd_bernoulli_units")
**Total class number and Bernoulli numerators.** For odd $`p`,
$$`p\mid h(K) \quad\Longleftrightarrow\quad \exists k,\ 1\le k,\ 2k\le p-3,\quad p\mid (B_{2k})_{\mathrm{num}}.`

{uses "thm:dvd-h-iff-dvd-hminus-units"}[] {uses "thm:hminus-bernoulli-final"}[] {uses "cor:hplus-to-hminus-units"}[]
:::

:::proof "thm:dvd-h-iff-bernoulli-units"
Apply {bpref "thm:dvd-h-iff-dvd-hminus-units"}[] with the implication supplied by
{bpref "cor:hplus-to-hminus-units"}[]. This replaces $`p\mid h(K)` by $`p\mid h^-(K)`.
Then apply the minus class-number criterion {bpref "thm:hminus-bernoulli-final"}[],
which replaces $`p\mid h^-(K)` by the existence of a divisible Bernoulli numerator in
Kummer's range.
:::

# The final theorem

:::theorem "thm:kummer-final" (lean := "BernoulliRegular.KummerCriterion")
**Kummer's criterion.** Let $`p` be an odd prime. Then
$$`\mathrm{IsRegularPrime}(p) \quad\Longleftrightarrow\quad \forall k,\ 1\le k,\ 2k\le p-3,\quad p\nmid (B_{2k})_{\mathrm{num}}.`

{uses "thm:dvd-h-iff-bernoulli-units"}[]
:::

:::proof "thm:kummer-final"
Take $`K` to be the standard cyclotomic field $`K=\mathbb{Q}(\zeta_p)`. By
definition, regularity of $`p` is coprimality with the class number of this standard
cyclotomic field. Since $`p` is prime, this is equivalent to
$`\neg\, p\mid h(\mathbb{Q}(\zeta_p))`. Applying
{bpref "thm:dvd-h-iff-bernoulli-units"}[] to this $`K` identifies divisibility by $`p`
with the existence of a Bernoulli numerator in Kummer's range divisible by $`p`.
Negating $`\exists k,\ 1\le k,\ 2k\le p-3,\quad p\mid (B_{2k})_{\mathrm{num}}` gives
exactly the displayed universal non-divisibility condition.
:::
