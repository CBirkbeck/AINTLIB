import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "L-values at non-positive integers" =>

This chapter records the special values of Dirichlet $`L`-functions needed for the
analytic formula for $`\hminus`.

# The value at s = 0

For an odd Dirichlet character $`\chi` modulo $`p` one has the finite Hurwitz
expansion
$$`L(s,\chi) = \sum_{a\in \mathbb{Z}/p\mathbb{Z}}\chi(a)\,\zeta_H^{-}\!\left(\frac{a}{p},s\right),`
where $`\zeta_H^{-}(x,s)` denotes the odd Hurwitz zeta function. The functional
equation for $`\zeta_H^{-}`, evaluated at $`s=0`, gives
$$`\zeta_H^{-}(x,0) = \frac12 - x \qquad (0<x<1).`
Substituting this identity immediately yields the desired special value.

:::theorem "thm:L0-eq-neg-B1" (lean := "BernoulliRegular.odd_LFunction_zero_eq_neg_BernoulliGen_one")
**Special value at zero.** Let $`p` be an odd prime and let $`\chi` be a non-trivial
odd Dirichlet character modulo $`p`. Then $`L(0,\chi) = -B_{1,\chi}`.

{uses "lem:gen-bernoulli-one-intermediate"}[] {uses "prop:gen-bernoulli-zero"}[]
:::

:::proof "thm:L0-eq-neg-B1"
Using the Hurwitz expansion and the value of $`\zeta_H^{-}(x,0)`, we obtain
$$`L(0,\chi) = \sum_{a\in \mathbb{Z}/p\mathbb{Z}}\chi(a)\left(\frac12-\frac{a}{p}\right) = \frac12\sum_a \chi(a) - \sum_a \chi(a)\frac{a}{p}.`
The first sum vanishes because $`\chi` is non-trivial. The second sum is the
expression for $`B_{1,\chi}` given by {bpref "lem:gen-bernoulli-one-intermediate"}[].
Hence $`L(0,\chi) = -B_{1,\chi}`.
:::

# The value at s = 1

For a primitive odd character $`\chi` modulo $`p`, define the completed $`L`-function
by
$$`\Lambda(s,\chi) := \left(\frac{p}{\pi}\right)^{(s+1)/2} \Gamma\!\left(\frac{s+1}{2}\right)L(s,\chi).`
Its functional equation is
$$`\Lambda(1-s,\chi) = \frac{\tau(\chi)}{i\sqrt p}\,\Lambda(s,\chi^{-1}),`
where $`\tau(\chi)=\sum_{a\in \mathbb{Z}/p\mathbb{Z}}\chi(a)e^{2\pi i a/p}` is the
Gauss sum of $`\chi`.

:::proposition "thm:fe-reduction" (lean := "BernoulliRegular.odd_LFunction_one_eq_oddLValueRhs_of_LFunction_inv_zero")
Let $`p` be an odd prime and let $`\chi` be a primitive odd Dirichlet character
modulo $`p`. If $`L(0,\chi^{-1}) = -B_{1,\chi^{-1}}`, then
$$`L(1,\chi) = \frac{\pi i\,\tau(\chi)}{p}\,B_{1,\chi^{-1}}.`

{uses "def:gauss-sum"}[] {uses "def:gen-bernoulli"}[] {uses "def:even-odd"}[]
:::

:::proof "thm:fe-reduction"
Set $`s=0` in the functional equation. Since $`\Lambda(1,\chi)=\frac{p}{\pi}L(1,\chi)`
and
$$`\Lambda(0,\chi^{-1}) = \left(\frac{p}{\pi}\right)^{1/2}\Gamma\!\left(\frac12\right)L(0,\chi^{-1}) = \sqrt p\,L(0,\chi^{-1}),`
we get
$$`\frac{p}{\pi}L(1,\chi) = \frac{\tau(\chi)}{i\sqrt p}\cdot \sqrt p\,L(0,\chi^{-1}) = -i\,\tau(\chi)L(0,\chi^{-1}).`
Substituting the hypothesis $`L(0,\chi^{-1})=-B_{1,\chi^{-1}}` gives the stated
formula.
:::

:::corollary "cor:L1-odd" (lean := "BernoulliRegular.odd_LFunction_one_eq_oddLValueRhs")
**Odd character formula at $`s=1`.** Let $`p` be an odd prime and let $`\chi` be a
non-trivial odd Dirichlet character modulo $`p`. Then
$$`L(1,\chi) = \frac{\pi i\,\tau(\chi)}{p}\,B_{1,\chi^{-1}}.`

{uses "thm:L0-eq-neg-B1"}[] {uses "thm:fe-reduction"}[]
:::

:::proof "cor:L1-odd"
Because $`p` is prime, every non-trivial character modulo $`p` is primitive. Applying
{bpref "thm:fe-reduction"}[] and then {bpref "thm:L0-eq-neg-B1"}[] to $`\chi^{-1}`
gives the result.
:::

This is the form of the special-value formula needed in the proof of the analytic
class number formula for $`\hminus`.
