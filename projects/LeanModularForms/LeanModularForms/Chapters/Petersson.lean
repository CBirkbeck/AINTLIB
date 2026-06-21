import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.Modularforms.PeterssonLevelN

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Petersson inner product" =>

Cusp forms of weight $`k` on the congruence subgroup $`\Gamma_1(N)` carry a Hermitian
inner product, obtained by integrating $`\overline{f(z)}\,g(z)\,\operatorname{Im}(z)^k`
against the hyperbolic area measure over a fundamental domain for $`\Gamma_1(N)`. This
pairing is conjugate-symmetric and positive definite, so it equips the space of cusp
forms with a genuine Hermitian structure. That structure is what makes orthogonal
decompositions — for instance into old and new subspaces — and adjoint computations for
Hecke operators possible \[DS, §5.4\].

:::definition "petN" (lean := "petN")
*The level-$`N` Petersson inner product.*
Fix a level $`N` and a weight $`k`, and let $`f` and $`g` be cusp forms of weight $`k`
on $`\Gamma_1(N)`. The *level-$`N` Petersson inner product* $`\langle f, g\rangle_N` is
the integral
$$`
  \langle f, g\rangle_N \;=\; \int_{\mathcal{D}_N}
  \overline{f(z)}\,g(z)\,\operatorname{Im}(z)^k \,\mathrm{d}\mu(z),
`
taken over a fundamental domain $`\mathcal{D}_N` for the action of the image of
$`\Gamma_1(N)` in $`\mathrm{PSL}_2(\mathbb{Z})` on the upper half-plane, against the
hyperbolic area measure
$$`
  \mathrm{d}\mu \;=\; \frac{\mathrm{d}x\,\mathrm{d}y}{y^2},
`
the $`\mathrm{SL}_2(\mathbb{R})`-invariant measure with $`z = x + iy`. The conjugate is
placed on the first argument, so the integrand is $`\overline{f(z)}\,g(z)\,y^k`; the
pairing is therefore conjugate-linear in $`f` and linear in $`g`.

Concretely the fundamental domain is realised as a finite union
$`\mathcal{D}_N = \bigcup_{\delta} \delta^{-1}\mathcal{D}`, where $`\mathcal{D}` is the
standard fundamental domain for $`\mathrm{SL}_2(\mathbb{Z})` and $`\delta` ranges over a
set of representatives for the cosets $`\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)`, of which
there are finitely many. Equivalently, unfolding this union turns the single integral into
the finite sum
$$`
  \langle f, g\rangle_N \;=\; \sum_{[\delta]\,\in\,\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)}
  \int_{\mathcal{D}} \overline{(f\vert\delta^{-1})(z)}\,(g\vert\delta^{-1})(z)\,
  \operatorname{Im}(z)^k \,\mathrm{d}\mu(z),
`
each term being the weight-$`k` Petersson integrand of the forms slashed by
$`\delta^{-1}` and integrated over the standard domain $`\mathcal{D}`. The inner product
is deliberately left *unnormalised*: no division by the volume of the fundamental domain
is performed, since a positive-definite Hermitian form already suffices for the intended
applications.
:::

:::lemma_ "petN-conj-symm" (lean := "petN_conj_symm")
*Conjugate symmetry of the level-$`N` Petersson inner product.* For cusp forms $`f` and
$`g` of weight $`k` on $`\Gamma_1(N)`, swapping the two arguments and taking the complex
conjugate returns the original pairing:
$$`
  \overline{\langle g, f\rangle_N} \;=\; \langle f, g\rangle_N.
`
Thus $`\langle \cdot, \cdot\rangle_N` is a Hermitian form: it is conjugate-linear in its
first argument and linear in its second.

Depends on: {uses "petN"}[]
:::

:::proof "petN-conj-symm"
Expand both sides as the finite sum over coset representatives that defines the pairing.
Complex conjugation distributes over the finite sum, so it suffices to treat a single
term. Inside each term the integrand is $`\overline{(g\vert\delta^{-1})(z)}\,
(f\vert\delta^{-1})(z)\,\operatorname{Im}(z)^k`; conjugating it turns the product
$`\overline{g}\,f` into $`\overline{f}\,g` while leaving the real factor
$`\operatorname{Im}(z)^k` unchanged, which is exactly the integrand of the corresponding
term of $`\langle f, g\rangle_N`. Summing the equalities back up gives the claim.

Depends on: {uses "petN"}[]
:::

:::theorem "petN-definite" (lean := "petN_definite")
*Positive definiteness of the level-$`N` Petersson inner product.* Let $`f` be a cusp
form of weight $`k` on $`\Gamma_1(N)`. If the self-pairing vanishes,
$$`
  \langle f, f\rangle_N \;=\; 0,
`
then $`f = 0`. Together with conjugate symmetry, this shows that
$`\langle \cdot, \cdot\rangle_N` is a genuine Hermitian inner product on the space of
cusp forms of weight $`k` on $`\Gamma_1(N)`.

Depends on: {uses "petN"}[]
:::

:::proof "petN-definite"
Unfold $`\langle f, f\rangle_N` as the finite sum over the cosets
$`\mathrm{SL}_2(\mathbb{Z})/\Gamma_1(N)` that defines the pairing. Each summand is the
self-pairing $`\int_{\mathcal{D}} |(f\vert\delta^{-1})(z)|^2 \operatorname{Im}(z)^k
\,\mathrm{d}\mu(z)`, whose integrand $`|(f\vert\delta^{-1})(z)|^2\,\operatorname{Im}(z)^k`
is pointwise non-negative; hence every summand is a non-negative real number. A finite sum
of non-negative reals that equals zero must have all of its terms equal to zero. In
particular the term attached to the trivial coset $`[1]` vanishes. Because the chosen
representative of $`[1]` lies in $`\Gamma_1(N)`, slashing by its inverse leaves $`f`
unchanged, so that term is exactly the ordinary weight-$`k` self-pairing of $`f` over the
standard fundamental domain $`\mathcal{D}` for $`\mathrm{SL}_2(\mathbb{Z})`; thus this
self-pairing also vanishes.

It remains to conclude $`f = 0` from the vanishing of $`\int_{\mathcal{D}} |f(z)|^2
\operatorname{Im}(z)^k \,\mathrm{d}\mu(z) = 0`. The integrand is continuous and
non-negative, and the factor $`\operatorname{Im}(z)^k` is strictly positive, so $`f`
vanishes identically on the interior $`\mathcal{D}^{\circ}` of the fundamental domain. The
upper half-plane is connected and $`f` is holomorphic on it, so a holomorphic function
vanishing on the open set $`\mathcal{D}^{\circ}` vanishes everywhere by the identity
theorem. Therefore $`f = 0`.

Depends on: {uses "petN"}[]
:::

:::theorem "fund-domain-Gamma1-PSL" (lean := "isFundamentalDomain_Gamma1_PSL")
*The coset-tiling fundamental domain for $`\Gamma_1(N)`.* Let $`\mathcal{D}` be the
standard open fundamental domain for the action of $`\mathrm{PSL}_2(\mathbb{Z})` on the
upper half-plane $`\mathbb{H}`, and let $`\overline{\Gamma}_1(N)` denote the image of
$`\Gamma_1(N)` in $`\mathrm{PSL}_2(\mathbb{Z})`. Choose, for each left coset in
$`\mathrm{PSL}_2(\mathbb{Z})/\overline{\Gamma}_1(N)`, a representative $`\delta`, and form
the union
$$`
  \mathcal{D}_N \;=\; \bigcup_{\delta} \delta^{-1}\mathcal{D}
`
of translated copies of $`\mathcal{D}`, indexed by these (finitely many) coset
representatives. Then $`\mathcal{D}_N` is a measure-theoretic fundamental domain for the
action of $`\overline{\Gamma}_1(N)` on $`\mathbb{H}`, with respect to the hyperbolic area
measure $`\mathrm{d}\mu = \mathrm{d}x\,\mathrm{d}y / y^2`. This is precisely the domain
over which the level-$`N` Petersson inner product is integrated.

Depends on: {uses "petN"}[]
:::

:::proof "fund-domain-Gamma1-PSL"
The statement is an instance of a general tiling principle. Suppose a group $`G` acts on a
space carrying a $`G`-invariant measure, and let $`\mathcal{D}` be a fundamental domain for
this action — so that, up to a null set, every orbit meets $`\mathcal{D}` exactly once.
For any subgroup $`H \leq G`, pick a representative $`\delta` for each left coset in
$`G/H`. Then the union $`\bigcup_{\delta} \delta^{-1}\mathcal{D}` is a fundamental domain
for the restricted action of $`H`. The covering property holds because almost every point
$`\tau` can be moved into $`\mathcal{D}` by some $`g \in G`; letting $`\delta` be the chosen
representative of the coset of $`g`, the residual element $`\delta^{-1} g` lies in $`H`,
and it carries $`\tau` into $`\delta^{-1}\mathcal{D}`, hence into the union. Almost-everywhere
disjointness of
the $`H`-translates of the union reduces to the disjointness of the $`G`-translates of
$`\mathcal{D}`, using that distinct coset representatives are sent to distinct cosets, so no
two tiles overlap on a set of positive measure.

Applying this with $`G = \mathrm{PSL}_2(\mathbb{Z})`, with $`\mathcal{D}` the standard
fundamental domain for the $`\mathrm{PSL}_2(\mathbb{Z})`-action on $`\mathbb{H}` under the
hyperbolic measure, and with $`H = \overline{\Gamma}_1(N)` the image of $`\Gamma_1(N)`,
yields that $`\mathcal{D}_N = \bigcup_{\delta} \delta^{-1}\mathcal{D}` is a fundamental
domain for $`\overline{\Gamma}_1(N)`. Since $`\overline{\Gamma}_1(N)` has finite index in
$`\mathrm{PSL}_2(\mathbb{Z})`, the coset space is finite and the union runs over finitely
many tiles.
:::
