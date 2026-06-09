import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Modular and Automorphic Forms" =>

This chapter covers the upper half-plane and the Möbius action of $`\mathrm{GL}_2(\mathbb{R})`,
the weight-$`k` slash action, modular forms and cusp forms as analytic objects bounded (respectively
vanishing) at every cusp, and the Eisenstein series $`E_k` together with their $`q`-expansions.
The chapter closes with the dimension formula for level-one spaces and the discriminant modular
form $`\Delta`. Throughout, $`\mathbb{H}` denotes the open upper half-plane,
$`\mathrm{SL}_2(\mathbb{Z})` the full modular group, and $`M_k(\Gamma)`, $`S_k(\Gamma)` the spaces
of modular forms and cusp forms of weight $`k` and level $`\Gamma`. Every mathlib node carries a
`(lean := …)` reference whose proof sketch follows the argument of the cited declaration, naming the
lemmas that proof actually invokes.

**Results from external Lean projects.** The *valence (weight) formula*, the abstract *Hecke ring*
and its $`\mathrm{GL}_2` *multiplication table* (Shimura 3.24), *eigenforms and newforms*, the
*Atkin–Lehner* old/new theory, *strong multiplicity one* (Miyake 4.6.12), and the *Shimura
surjection* (Shimura 3.35) are formalised in the **LeanModularForms** project on its `hecke-ring`
branch, and the negative-weight vanishing in **ModFormDims**. Each such node carries a
`Formalised in` provenance line linking the exact source declaration at a fixed commit and reporting
its true Lean status. They are *informal* here (no `(lean := …)`) because those projects build
against a newer mathlib than the current AINTLIB build; they connect into the dependency graph
through the mathlib-backed modular-forms nodes of this chapter.

# The upper half-plane and the Möbius action

:::definition "upper-half-plane" (lean := "UpperHalfPlane")
The *upper half-plane* $`\mathbb{H}` is the set of complex numbers with strictly positive imaginary
part:
$$`\mathbb{H} \;=\; \{\, z \in \mathbb{C} \;\mid\; \operatorname{Im}(z) > 0 \,\}.`
It is realised in mathlib as the subtype of $`\mathbb{C}` carrying the positivity condition
$`0 < \operatorname{Im}(z)`.
:::

:::definition "sl2-action" (lean := "UpperHalfPlane.glAction, UpperHalfPlane.SLAction")
Let $`g = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})` with
$`\det(g) > 0`. The *Möbius action* of $`g` on $`\mathbb{H}` is
$$`g \cdot z \;=\; \frac{az + b}{cz + d}.`
This makes $`\mathbb{H}` a left $`\mathrm{GL}_2^{+}(\mathbb{R})`-set. The modular group
$`\mathrm{SL}_2(\mathbb{Z})` acts on $`\mathbb{H}` by the same formula, since $`\det(g) = 1 > 0`
for $`g \in \mathrm{SL}_2(\mathbb{Z})`.
:::

:::proof "sl2-action"
The key ingredient is that $`\operatorname{Im}(g \cdot z) = \det(g)\,\operatorname{Im}(z)\,/\,|cz + d|^2`,
so the imaginary part stays positive when $`\det(g) > 0` and $`z \in \mathbb{H}`. The associativity
law $`g \cdot (h \cdot z) = (gh) \cdot z` follows from the denominator cocycle identity
$`c_{gh}(z) = c_g(h \cdot z)\,c_h(z)`, where $`c_g(z) = cz + d` is the denominator
({uses "upper-half-plane"}[]).
:::

# The weight-k slash action

:::definition "slash-action" (lean := "SlashAction, ModularForm.slash_apply")
For an integer $`k`, a matrix $`g \in \mathrm{GL}_2(\mathbb{R})`, and a function
$`f : \mathbb{H} \to \mathbb{C}`, mathlib's *weight-$`k` slash action* is the right action
$$`(f \mid_k g)(z) \;=\; \sigma(g)\bigl(f(g \cdot z)\bigr)\;|\det g|^{\,k-1}\;\operatorname{denom}(g, z)^{-k},`
where $`g \cdot z` is the Möbius action ({uses "sl2-action"}[]), $`\operatorname{denom}(g, z) = cz + d`
is the automorphy denominator, and $`\sigma(g)` is complex conjugation when $`\det g < 0` and the
identity otherwise (so $`\sigma` is trivial on $`\mathrm{GL}_2^{+}`). On
$`\mathrm{SL}_2(\mathbb{Z})`, where $`\det g = 1`, this reduces to the classical
$`(f \mid_k g)(z) = (cz + d)^{-k} f(g \cdot z)`. The action is multiplicative in $`g`, and on a
product of two functions it satisfies
$$`(fh) \mid_{k_1 + k_2} g \;=\; (f \mid_{k_1} g)\,(h \mid_{k_2} g).`
:::

:::definition "slash-invariant-form" (lean := "SlashInvariantForm")
A *slash-invariant form* of weight $`k` and level a subgroup $`\Gamma \le \mathrm{GL}_2(\mathbb{R})`
is a function $`f : \mathbb{H} \to \mathbb{C}` invariant under the slash action of every
$`\gamma \in \Gamma`:
$$`f \mid_k \gamma \;=\; f \qquad \text{for all } \gamma \in \Gamma.`
:::

# Modular forms and cusp forms

:::definition "modular-form" (lean := "ModularForm")
A *modular form* of weight $`k \in \mathbb{Z}` and level $`\Gamma` is a slash-invariant form
({uses "slash-invariant-form"}[]) that additionally:

1. is holomorphic on $`\mathbb{H}` (complex-differentiable at every point), and
2. is *bounded at every cusp* of $`\Gamma`: for each cusp $`c`, the function $`f \mid_k g` is
   bounded as $`\operatorname{Im}(z) \to \infty`, where $`g \in \mathrm{GL}_2(\mathbb{R})` carries
   $`\infty` to $`c`.

The space of all such forms is a $`\mathbb{C}`-vector space denoted $`M_k(\Gamma)`.
:::

:::definition "cusp-form" (lean := "CuspForm")
A *cusp form* of weight $`k` and level $`\Gamma` is a slash-invariant form
({uses "slash-invariant-form"}[]) that is holomorphic on $`\mathbb{H}` and *vanishes at every cusp*:
the same $`f \mid_k g` tends to $`0` as $`\operatorname{Im}(z) \to \infty`. The subspace of cusp
forms is denoted $`S_k(\Gamma) \subseteq M_k(\Gamma)`.
:::

:::lemma_ "cusp-form-submodule" (lean := "ModularForm.CuspForm.equivCuspFormSubmodule")
The space of cusp forms $`S_k(\Gamma)` embeds into $`M_k(\Gamma)` as a $`\mathbb{C}`-submodule, and
the type $`S_k(\Gamma)` is linearly equivalent to this submodule:
$$`S_k(\Gamma) \;\simeq_{\mathbb{C}}\; \mathrm{cuspFormSubmodule}(\Gamma, k) \;\subseteq\; M_k(\Gamma).`
:::

:::proof "cusp-form-submodule"
The submodule $`\mathrm{cuspFormSubmodule}(\Gamma, k)` is cut out inside $`M_k(\Gamma)` by the
predicate "the constant $`q`-expansion coefficient at every cusp vanishes" ({uses "cusp-form"}[]).
The forgetful map sending a cusp form to the same function viewed as a modular form is
$`\mathbb{C}`-linear and injective, with range exactly this submodule; the equivalence
$`S_k(\Gamma) \simeq_{\mathbb{C}} \mathrm{cuspFormSubmodule}(\Gamma, k)` is the linear isomorphism of
a domain onto the range of an injective linear map.
:::

# The q-expansion

:::definition "q-expansion" (lean := "UpperHalfPlane.qExpansion")
Let $`f : \mathbb{H} \to \mathbb{C}` and let $`h > 0`. The *$`q`-expansion of $`f` with parameter
$`h`* is the formal power series
$$`\mathrm{qExp}_h(f) \;=\; \sum_{n=0}^{\infty} a_n\, q^n \;\in\; \mathbb{C}[[q]],`
where $`q = e^{2\pi i z / h}` and the coefficients $`a_n` are the Taylor coefficients at $`0` of the
analytic function $`F` satisfying $`f(z) = F(e^{2\pi i z/h})` near the cusp.
:::

:::lemma_ "q-expansion-convergence" (lean := "UpperHalfPlane.hasSum_qExpansion")
Let $`f : \mathbb{H} \to \mathbb{C}` be periodic with period $`h > 0`, holomorphic, and bounded as
$`\operatorname{Im}(z) \to \infty`. Then the $`q`-expansion of $`f` converges: for every
$`z \in \mathbb{H}`,
$$`f(z) \;=\; \sum_{n=0}^{\infty} a_n\, e^{2\pi i n z / h}.`
:::

:::proof "q-expansion-convergence"
Periodicity and holomorphicity imply that $`f` factors through an analytic function $`F` on the
punctured unit disc with $`f(z) = F(e^{2\pi i z/h})` ({uses "q-expansion"}[]). Boundedness at the
cusp removes the singularity, so $`F` extends analytically across $`0` and its Taylor series
converges on the whole open unit disc. Substituting $`q = e^{2\pi i z/h}`, which lies in that disc
for $`z \in \mathbb{H}`, yields the stated sum.
:::

:::lemma_ "q-expansion-unique" (lean := "UpperHalfPlane.qExpansion_coeff_unique")
Under the same hypotheses, the $`q`-expansion coefficients are uniquely determined by $`f` and
$`h`: if $`\sum_n c_n\, e^{2\pi i n z/h} = f(z)` for all $`z \in \mathbb{H}`, then $`c_n = a_n` for
all $`n`.
:::

:::proof "q-expansion-unique"
Both the given series and the $`q`-expansion ({uses "q-expansion"}[]) represent $`f` as a power
series in $`q = e^{2\pi i z/h}` convergent on a punctured neighbourhood of $`0`
({uses "q-expansion-convergence"}[]). A holomorphic function on the disc has a unique Taylor
expansion, so two convergent power series in $`q` that agree as functions of $`z` — equivalently as
functions of $`q` — must have identical coefficients; hence $`c_n = a_n` for every $`n`.
:::

# Eisenstein series

:::definition "eisenstein-series" (lean := "ModularForm.eisensteinSeriesMF, ModularForm.E")
For an integer $`k \ge 3`, a positive integer $`N`, and a congruence datum
$`a \in (\mathbb{Z}/N\mathbb{Z})^2`, the *Eisenstein series of weight $`k`, level $`\Gamma(N)`, and
characteristic $`a`* is
$$`\mathcal{E}_{k,a}(z) \;=\; \sum_{\substack{(c,d) \equiv a \ (N) \\ (c,d) \neq (0,0)}} \frac{1}{(cz + d)^k},`
the sum running over the integer pairs congruent to $`a` modulo $`N`. The *normalised Eisenstein
series* of weight $`k` and level $`1` is the modular form
$$`E_k(z) \;=\; \sum_{\substack{(c,d) \in \mathbb{Z}^2 \\ (c,d) \neq (0,0)}} \frac{1}{(cz + d)^k}
              \Big/ \Bigl(\,2\,\zeta(k)\,\Bigr),`
the level-one Eisenstein series rescaled to have constant $`q`-coefficient $`1`.
:::

:::theorem "eisenstein-is-modular-form" (lean := "ModularForm.eisensteinSeriesMF")
For any $`k \ge 3`, $`N \ge 1`, and $`a \in (\mathbb{Z}/N\mathbb{Z})^2`, the Eisenstein series
$`\mathcal{E}_{k,a}` defines a modular form in $`M_k(\Gamma(N))`.
:::

:::proof "eisenstein-is-modular-form"
Slash-invariance of $`\mathcal{E}_{k,a}` ({uses "eisenstein-series"}[]) under $`\Gamma(N)` follows
because the row-vector action of $`\Gamma(N)` permutes the index set of pairs congruent to $`a`
modulo $`N`, exactly absorbing the automorphy factor ({uses "slash-invariant-form"}[]).
Holomorphicity on $`\mathbb{H}` comes from locally uniform convergence of the defining series, which
in turn follows from the estimate $`|cz + d|^{-k} \le C\,\operatorname{Im}(z)^{-k}` on compact
sets together with $`k \ge 3`. Boundedness at the cusps is read off from the explicit analysis of
the cusp-function transform ({uses "q-expansion"}[]).
:::

:::theorem "eisenstein-nonzero" (lean := "EisensteinSeries.E_ne_zero")
For every even $`k \ge 3`, the normalised Eisenstein series $`E_k` is nonzero.
:::

:::proof "eisenstein-nonzero"
The constant term of the $`q`-expansion of $`E_k` is $`1`
({uses "eisenstein-q-expansion-coeff-zero"}[]); were $`E_k` identically zero its $`q`-expansion
would vanish identically, contradicting a nonzero constant term. Hence $`E_k \neq 0`.
:::

:::lemma_ "eisenstein-q-expansion-coeff-zero" (lean := "EisensteinSeries.E_qExpansion_coeff_zero")
For even $`k \ge 3`, the constant term of the $`q`-expansion of $`E_k` is
$$`a_0(E_k) \;=\; 1.`
:::

:::lemma_ "eisenstein-q-expansion" (lean := "EisensteinSeries.E_qExpansion_coeff")
For even $`k \ge 3` and every $`m \ge 1`, the $`m`-th $`q`-expansion coefficient of $`E_k` is
$$`a_m(E_k) \;=\; -\frac{2k}{B_k}\,\sigma_{k-1}(m),`
where $`B_k` is the $`k`-th Bernoulli number and $`\sigma_{k-1}(m) = \sum_{d \mid m} d^{k-1}` is the
divisor-power sum.
:::

:::proof "eisenstein-q-expansion"
The engine is the Lipschitz summation formula
$$`\sum_{n \in \mathbb{Z}} (z + n)^{-k} \;=\; \frac{(-2\pi i)^k}{(k-1)!}\,\sum_{m \ge 1} m^{k-1}\, e^{2\pi i m z},`
which converts the level-one Eisenstein sum ({uses "eisenstein-series"}[]) into a series in
$`q = e^{2\pi i z}` whose $`m`-th coefficient collects the divisor-power sum $`\sigma_{k-1}(m)`.
Dividing by the normalising constant $`2\zeta(k)` and using the closed form
$`\zeta(k) = -(2\pi i)^k B_k / (2\,k!)` for even $`k` turns the leading constant into $`1` and the
$`m`-th coefficient into $`-(2k/B_k)\,\sigma_{k-1}(m)`. mathlib packages the constant-coefficient
case ({uses "eisenstein-q-expansion-coeff-zero"}[]) as the $`m = 0` specialisation, established by
the same summation identity.
:::

# The discriminant modular form

:::definition "modular-discriminant" (lean := "CuspForm.discriminant")
The *modular discriminant* $`\Delta` is the nonzero cusp form of weight $`12` and level $`1` given
by the Dedekind eta product
$$`\Delta(z) \;=\; e^{2\pi i z} \prod_{n=1}^{\infty} (1 - e^{2\pi i n z})^{24} \;=\; \eta(z)^{24},`
where $`\eta(z) = e^{\pi i z/12}\prod_{n\ge 1}(1 - e^{2\pi i n z})` is the Dedekind eta function. In
particular $`\Delta \in S_{12}(\mathrm{SL}_2(\mathbb{Z}))`, and $`\Delta(z) \neq 0` for every
$`z \in \mathbb{H}` (the eta product never vanishes). At a point $`\tau \in \mathbb{H}` the value
$`\Delta(\tau)` is, up to normalisation, the discriminant of the elliptic curve
$`\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)` in its Weierstrass model $`y^2 = 4x^3 - g_2 x - g_3`:
indeed $`(2\pi)^{12}\Delta = g_2^3 - 27 g_3^2`.
:::

:::lemma_ "discriminant-q-coeff-one" (lean := "ModularForm.discriminant_qExpansion_coeff_one")
The first $`q`-expansion coefficient of $`\Delta` is $`1`:
$$`\Delta(z) \;=\; q + \sum_{n=2}^{\infty} \tau(n)\, q^n, \qquad q = e^{2\pi i z},`
where $`\tau` is the Ramanujan tau function.
:::

:::theorem "discriminant-e4-e6" (lean := "ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq")
The modular discriminant satisfies the identity
$$`\Delta(z) \;=\; \frac{E_4(z)^3 - E_6(z)^2}{1728}`
pointwise for all $`z \in \mathbb{H}`.
:::

:::proof "discriminant-e4-e6"
mathlib forms the weight-$`12` combination $`E_4^3 - E_6^2` as a genuine modular form and checks it
is a cusp form ({uses "cusp-form"}[]): its constant $`q`-coefficient vanishes because the constant
terms of $`E_4` and $`E_6` are both $`1` ({uses "eisenstein-q-expansion-coeff-zero"}[]). Since
$`S_{12}(\mathrm{SL}_2(\mathbb{Z}))` is one-dimensional ({uses "cusp-form-weight-twelve-rank-one"}[]),
the cusp form $`E_4^3 - E_6^2` is a scalar multiple of $`\Delta`. The scalar is pinned by comparing
the coefficient of $`q^1`: a direct expansion gives $`(E_4^3 - E_6^2)` coefficient $`1728` at $`q^1`
(from $`3\cdot 240 - 2\cdot(-504) = 1728`), while $`\Delta` has coefficient $`1`
({uses "discriminant-q-coeff-one"}[]); hence the scalar is $`1728`.
:::

# Dimension formula for level-one modular forms

:::theorem "discriminant-equiv" (lean := "CuspForm.discriminantEquiv, CuspForm.ofMulDiscriminant")
For any weight $`k`, division by the discriminant $`\Delta` is a $`\mathbb{C}`-linear isomorphism
$$`S_k(\mathrm{SL}_2(\mathbb{Z})) \;\xrightarrow{\;\sim\;}\; M_{k-12}(\mathrm{SL}_2(\mathbb{Z})),
   \qquad f \;\longmapsto\; f / \Delta,`
with inverse multiplication by $`\Delta`.
:::

:::proof "discriminant-equiv"
Because $`\Delta` is everywhere nonzero on $`\mathbb{H}` ({uses "modular-discriminant"}[]), the
quotient $`f/\Delta` of a weight-$`k` cusp form by $`\Delta` is holomorphic on $`\mathbb{H}`, and the
slash-invariance descends to weight $`k - 12` since slashing commutes with division
({uses "slash-action"}[]). Boundedness of $`f/\Delta` at the cusp is the comparison
$`f/\Delta = O(1)`, which holds because a cusp form vanishes at the cusp at least as fast as
$`\Delta` (mathlib's exponential-decay estimate for the discriminant). The forward map
$`f \mapsto f/\Delta` and the inverse $`g \mapsto \Delta\, g` (multiplying a weight-$`(k-12)` form by
$`\Delta`) are mutually inverse by $`\Delta\cdot(f/\Delta) = f` and $`(\Delta g)/\Delta = g`, using
$`\Delta(z) \neq 0`.
:::

:::lemma_ "cusp-form-weight-twelve-rank-one" (lean := "CuspForm.rank_eq_one_of_weight_eq_twelve")
The space $`S_{12}(\mathrm{SL}_2(\mathbb{Z}))` is one-dimensional over $`\mathbb{C}`.
:::

:::proof "cusp-form-weight-twelve-rank-one"
The discriminant isomorphism at $`k = 12` ({uses "discriminant-equiv"}[]) identifies
$`S_{12}(\mathrm{SL}_2(\mathbb{Z}))` with $`M_0(\mathrm{SL}_2(\mathbb{Z}))`, the space of
weight-zero level-one modular forms. The latter is spanned by the constant function $`1` and so has
rank $`1`; transporting along the isomorphism gives $`\dim S_{12} = 1`. (The nonzero discriminant
itself, {uses "modular-discriminant"}[], is the corresponding basis vector.)
:::

:::lemma_ "cusp-form-rank-zero-lt-twelve" (lean := "CuspForm.rank_eq_zero_of_weight_lt_twelve")
For $`k < 12`, the space $`S_k(\mathrm{SL}_2(\mathbb{Z}))` is zero.
:::

:::proof "cusp-form-rank-zero-lt-twelve"
The discriminant isomorphism ({uses "discriminant-equiv"}[]) identifies $`S_k` with $`M_{k-12}`, and
for $`k < 12` the weight $`k - 12` is negative. Level-one modular forms of negative weight vanish
({uses "neg-weight-rank-zero"}[]), so $`M_{k-12} = 0` and hence $`S_k = 0`.
:::

:::lemma_ "rank-one-plus-rank-cusp" (lean := "ModularForm.rank_eq_one_add_rank_cuspForm")
For every even $`k \ge 3`, the dimension of $`M_k(\mathrm{SL}_2(\mathbb{Z}))` satisfies
$$`\dim M_k \;=\; 1 + \dim S_k.`
:::

:::proof "rank-one-plus-rank-cusp"
It suffices to show the quotient $`M_k / \mathrm{cuspFormSubmodule}` is one-dimensional, since then
$`\dim M_k = 1 + \dim S_k` by additivity of rank in the exact sequence
$`0 \to S_k \to M_k \to M_k/S_k \to 0` and the identification $`S_k \simeq \mathrm{cuspFormSubmodule}`
({uses "cusp-form-submodule"}[]). The class of $`E_k` ({uses "eisenstein-is-modular-form"}[]) spans
the quotient: it is nonzero there because $`E_k` has constant $`q`-coefficient $`1`
({uses "eisenstein-q-expansion-coeff-zero"}[]) and hence is not a cusp form, and every $`f \in M_k`
differs from $`a_0(f)\,E_k` by a form with vanishing constant term, i.e. a cusp form. Thus the
quotient is the line spanned by $`[E_k]`.
:::

:::theorem "dimension-level-one" (lean := "ModularForm.dimension_level_one")
For every even natural number $`k`, the dimension of $`M_k(\mathrm{SL}_2(\mathbb{Z}))` over
$`\mathbb{C}` is
$$`\dim_{\mathbb{C}} M_k(\mathrm{SL}_2(\mathbb{Z})) \;=\;
\begin{cases} \lfloor k/12 \rfloor & \text{if } k \equiv 2 \pmod{12}, \\
              \lfloor k/12 \rfloor + 1 & \text{otherwise.} \end{cases}`
In particular $`M_0 \cong \mathbb{C}`, $`M_2 = 0`, $`M_4 \cong \mathbb{C}`, and $`M_6 \cong \mathbb{C}`.
:::

:::proof "dimension-level-one"
Strong induction on $`k`, splitting into $`k < 3`, $`3 \le k < 12`, and $`12 \le k`. The small
weights are checked directly: $`M_0` is the line of constants and $`M_2 = 0`. The vanishing of
$`M_2` is the one genuinely delicate base case — it is *not* a formal triangularity argument but
uses that $`E_4^3` and $`E_6^2` span the weight-$`12` line: writing $`f \in M_2`, the products
$`f^2 \in M_4` and $`f^3 \in M_6` are forced to be scalar multiples of $`E_4` and $`E_6` (each of
those spaces being one-dimensional), and matching the $`q^0` and $`q^1` coefficients of
$`(E_4^3 - E_6^2)`-type combinations forces $`f = 0`. For $`3 \le k < 12` the splitting
$`\dim M_k = 1 + \dim S_k` ({uses "rank-one-plus-rank-cusp"}[]) combines with $`S_k = 0`
({uses "cusp-form-rank-zero-lt-twelve"}[]) to give $`\dim M_k = 1` at the even weights $`4, 6, 8, 10`.
For $`k \ge 12` the same splitting and the discriminant isomorphism $`S_k \simeq M_{k-12}`
({uses "discriminant-equiv"}[]) reduce the count to the inductive hypothesis at $`k - 12`; the
floor identity $`\lfloor k/12 \rfloor = 1 + \lfloor (k-12)/12 \rfloor` and the invariance of
$`k \bmod 12` then propagate the closed form.
:::

:::theorem "finite-dimensional-modular-forms" (lean := "ModularForm.dimension_level_one, ModularForm.levelOne_odd_weight_rank_zero")
For every weight $`k \in \mathbb{Z}`, the space $`M_k(\mathrm{SL}_2(\mathbb{Z}))` is
finite-dimensional over $`\mathbb{C}`.
:::

:::proof "finite-dimensional-modular-forms"
The rank is finite in each of three regimes. For $`k < 0` the space is zero
({uses "neg-weight-rank-zero"}[]). For even $`k \ge 0` finiteness is immediate from the explicit
dimension formula ({uses "dimension-level-one"}[]), whose value is a natural number. For odd $`k`
the element $`-1 \in \mathrm{SL}_2(\mathbb{Z})` acts on weight-$`k` forms by $`(-1)^k = -1`, forcing
$`f = -f` and hence $`f = 0`; so the rank is again zero. In all three cases the rank is below
$`\aleph_0`, which is finite-dimensionality.
:::

# Results from the LeanModularForms project

The nodes below formalise results whose proofs require substantially more machinery than is in
mathlib v4.30.0-rc2. They are drawn from the **LeanModularForms** project
([`https://github.com/CBirkbeck/LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms)),
on its `hecke-ring` branch (non-default, unmerged as of June 2026), which carries the abstract Hecke
ring, the $`\mathrm{GL}_2` multiplication table, eigenforms and newforms, the Atkin–Lehner old/new
theory, strong multiplicity one, the Shimura surjection, and the valence formula. All permalinks are
to the fixed commit `720d950b8c31ffd69b2cc7aa5323bccaefad62e1`. Each node is informal (no
`(lean := …)`) and carries a provenance line recording the exact source declaration and its true
Lean status.

The development follows Shimura's *Introduction to the Arithmetic Theory of Automorphic Functions*,
§3.1 and Theorem 3.24, and Miyake's *Modular Forms*, §4.5–4.6. Throughout this section $`N \ge 1`
is the level, $`k` the weight, $`\Gamma_0(N)`, $`\Gamma_1(N)` the standard congruence subgroups,
$`\chi` a Dirichlet character modulo $`N`, $`S_k(N, \chi)` the cusp forms of Nebentypus $`\chi`, and
$`T(n)`, $`\langle n \rangle` the Hecke and diamond operators.

## Hecke pairs and the abstract Hecke ring

:::definition "hecke-pair"
*Hecke pairs and their double cosets.*
A *Hecke pair* $`(G, H, \Delta)` consists of a group $`G`, a subgroup $`H \le G`, and a submonoid
$`\Delta` with $`H \le \Delta \le \operatorname{Comm}(H)`, where $`\operatorname{Comm}(H)` is the
commensurator of $`H` in $`G` (every $`g \in \Delta` has $`H \cap gHg^{-1}` of finite index in both
$`H` and $`gHg^{-1}`). From the pair one builds two free $`\mathbb{Z}`-modules: one on the *double
cosets* $`H\backslash\Delta/H`, which will carry the ring structure, and one on the *left cosets*
$`Hg`, on which that ring will act. The basic structural fact is that each double coset $`HgH` is a
finite disjoint union of left cosets,
$$`HgH \;=\; \bigsqcup_{i \in H/(H \cap gHg^{-1})} H\,(g_i\, g),`
indexed by the finite coset space $`H/(H \cap gHg^{-1})`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): the Hecke pair
[`HeckeRing.HeckePair`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/AbstractHeckeRing/Basic.lean#L57) and the decomposition
[`HeckeRing.DoubleCoset.doubleCoset_eq_iUnion_leftCosets`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/AbstractHeckeRing/Basic.lean#L256) — sorry-free.
:::

:::theorem "hecke-ring"
*The Hecke ring of a Hecke pair.*
For a Hecke pair $`(G, H, \Delta)` ({uses "hecke-pair"}[]), the free $`\mathbb{Z}`-module
$`\mathbb{T} = \mathcal{H}(G, H, \Delta)` on the double cosets $`H\backslash\Delta/H` is a unital
associative ring under the *convolution product*: on basis elements $`[D_1]`, $`[D_2]` it is
$$`[D_1]\cdot[D_2] \;=\; \sum_{d} \mu(D_1, D_2; d)\,[d],`
where the structure constant $`\mu(D_1, D_2; d)` counts the pairs of left-coset representatives
$`(g_i, g'_j)` from the decompositions of $`D_1`, $`D_2` with $`g_i\, g'_j\, H = d\, H`. The identity
is the basis element $`[H]` of the trivial double coset.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`HeckeRing.instRing`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/AbstractHeckeRing/Ring.lean#L88) — sorry-free.

Depends on: {uses "hecke-pair"}[]
:::

:::proof "hecke-ring"
The additive group is the free $`\mathbb{Z}`-module on double cosets, hence abelian. The convolution
product is $`\mathbb{Z}`-bilinear by construction, so distributivity and integer-scaling
compatibility are immediate. Associativity is proved by realising $`\mathbb{T}` faithfully through
its action on the free module on left cosets: ring multiplication is compatible with that module
action, and on a triple of basis elements both bracketings re-index the same triple-coset orbit sum,
so $`(f\cdot g)\cdot h` and $`f\cdot(g\cdot h)` act identically and therefore coincide. The trivial
double coset $`H` decomposes into the single left coset $`H`, whence $`[H]\cdot[D] = [D] = [D]\cdot[H]`
on basis elements, extended to a two-sided identity by bilinearity ({uses "hecke-pair"}[]).
:::

:::theorem "hecke-degree"
*The degree homomorphism.*
Counting left cosets defines a ring homomorphism $`\deg : \mathbb{T} \to \mathbb{Z}` sending each
basis double coset $`[D]`, $`D = HgH`, to its number of left cosets
$`\deg D = [\,H : H \cap gHg^{-1}\,]`. It is unital and multiplicative:
$$`\deg(f \cdot g) \;=\; \deg(f)\,\deg(g).`
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`HeckeRing.deg`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/AbstractHeckeRing/Degree.lean#L231) — sorry-free.

Depends on: {uses "hecke-ring"}[]
:::

:::proof "hecke-degree"
Additivity is built into the linear extension, so multiplicativity need only be checked on a pair of
basis elements. Expanding $`[D_1]\cdot[D_2] = \sum_d \mu(D_1, D_2; d)\,[d]` ({uses "hecke-ring"}[])
and applying $`\deg` gives $`\sum_d \mu(D_1, D_2; d)\,\deg d`, which counts with multiplicity the
left cosets occurring in the product double coset. Grouping these by the right action of $`D_2` on
the left cosets of $`D_1`, each of the $`\deg D_1` orbits contributes exactly $`\deg D_2` cosets (an
orbit-size computation), so the total is $`\deg D_1\,\deg D_2`.
:::

:::theorem "hecke-commutativity"
*Commutativity via anti-involutions, and the $`\mathrm{GL}_n` algebra.*
An *anti-involution* of $`(G, H, \Delta)` is an involutive anti-homomorphism $`g \mapsto \bar g`
preserving $`H` and $`\Delta`. If its induced map on double cosets fixes every double coset
($`H\bar gH = HgH` for all $`g`), then the Hecke ring $`\mathbb{T}` is commutative. For the
arithmetic $`\mathrm{GL}_n` pair $`G = \mathrm{GL}_n(\mathbb{Q})`, $`H = \mathrm{SL}_n(\mathbb{Z})`,
$`\Delta = ` integer matrices of positive determinant, the transpose $`g \mapsto {}^{t}g` is such a
fixing anti-involution; hence the $`\mathrm{GL}_n` Hecke algebra $`\mathcal{H}_n` is commutative.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): the criterion [`HeckeRing.AntiInvolution.mul_comm_of_antiInvolution`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/AbstractHeckeRing/Commutativity.lean#L414) and the instance [`HeckeRing.GLn.instCommRing_HeckeAlgebra`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GLn/TransposeAntiInvolution.lean#L91) — sorry-free.

Depends on: {uses "hecke-ring"}[]
:::

:::proof "hecke-commutativity"
By bilinearity, commutativity reduces to the symmetry $`\mu(D_1, D_2; d) = \mu(D_2, D_1; d)` of the
structure constants ({uses "hecke-ring"}[]). Applying the anti-involution to a left-coset
decomposition of $`D_1 D_2` carries it, because $`g \mapsto \bar g` reverses products, to a
decomposition of $`D_2 D_1`; because the induced map fixes every double coset, the double coset of
each representative is preserved. Tracking a fixed representative gives a bijection between the pairs
counted by $`\mu(D_1, D_2; d)` and those counted by $`\mu(D_2, D_1; d)`, so the two agree. For
$`\mathrm{GL}_n`, the transpose reverses products and is involutive, and every double coset has a
diagonal (Smith normal form) representative equal to its own transpose, so the induced map fixes
every double coset; the criterion then upgrades $`\mathcal{H}_n` to a commutative ring.
:::

## The GL₂ Hecke operators and Shimura's multiplication table

:::definition "hecke-operator"
*The operators $`T(a,d)` and $`T(m)`.*
Specialise the arithmetic pair to $`n = 2`. For positive integers $`a \mid d`, the operator
$`T(a, d) \in \mathcal{H}_2` is the basis element of the diagonal double coset of
$`\operatorname{diag}(a, d)` (and $`T(a,d) = 0` when $`a \nmid d`); the *scalar operator*
$`T(p, p)` is the class of $`p I`. Shimura's operator $`T(m)` is the divisor sum
$$`T(m) \;=\; \sum_{a \mid m} T\!\left(a, \tfrac{m}{a}\right),`
so that $`T(1) = 1` and, for a prime $`p`, $`T(p) = T(1, p)`. The classical *diamond operator*
$`\langle d \rangle` is the action of $`\operatorname{diag}` units recording the Nebentypus. As an
operator on $`M_k(\Gamma_1(N))`, $`T(m)` acts through the slash sum attached to its double-coset
representatives ({uses "slash-action"}[]).
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): the algebra
elements [`HeckeRing.GL2.T_ad`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Basic.lean#L33), [`HeckeRing.GL2.T_sum`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Basic.lean#L65), and the operator on cusp forms [`HeckeRing.GL2.heckeT_n`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/HeckeT_n.lean#L513) — sorry-free.

Depends on: {uses "modular-form"}[] {uses "slash-action"}[] {uses "hecke-commutativity"}[]
:::

:::theorem "hecke-multiplication-table"
*Shimura's multiplication table (Theorem 3.24).*
In the commutative algebra $`\mathcal{H}_2`, the operators $`T(m)` obey, for a prime $`p` and
$`r \le s`, the prime-power product
$$`T(p^r)\,T(p^s) \;=\; \sum_{i=0}^{r} p^{i}\, T(p^{i}, p^{i})\, T\!\left(p^{\,r+s-2i}\right),`
coprime multiplicativity $`T(m)\,T(n) = T(mn)` for $`(m,n) = 1`, and in general
$$`T(m)\,T(n) \;=\; \sum_{d \mid (m,n)} d\, T(d, d)\, T\!\left(\tfrac{mn}{d^2}\right).`
The degrees are $`\deg T(p^k) = 1 + p + \dots + p^k` and $`\deg T(m) = \sigma_1(m)`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): the general
product [`HeckeRing.GL2.T_sum_mul`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean#L1092), the prime-power case [`HeckeRing.GL2.T_sum_ppow_mul`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean#L819), and the degree [`HeckeRing.GL2.deg_T_sum`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Degree.lean#L135) — sorry-free.

Depends on: {uses "hecke-operator"}[] {uses "hecke-degree"}[]
:::

:::proof "hecke-multiplication-table"
The arguments are arithmetic and combinatorial, anchored by the central scalar class $`T(p,p)`,
which shifts both elementary divisors up by one: $`T(p,p)\,T(p^j, p^d) = T(p^{j+1}, p^{d+1})`. A key
prime computation expands $`T(p)\,T(1, p^k)` through the convolution structure constants
({uses "hecke-operator"}[]), where a determinant-and-divisibility analysis forces only the diagonal
classes $`\operatorname{diag}(1, p^{k+1})` and $`\operatorname{diag}(p, p^k)` to appear, with
coset-counting multiplicities $`1` and $`c` ($`c = p+1` if $`k = 1`, else $`c = p`). Telescoping the
expansion $`T(p^k) = \sum_i T(p^i, p^{k-i})` against $`T(p,p)\,T(p^{k-2})` yields the three-term
recurrence $`T(p^{k+1}) = T(p)\,T(p^k) - p\,T(p,p)\,T(p^{k-1})`, from which the prime-power product
formula follows by strong induction (the shifted terms cancel except at the endpoints). Coprime
multiplicativity is the Chinese Remainder Theorem on elementary divisors: for $`(m,n) = 1` the
diagonal classes of $`\operatorname{diag}(a, m/a)` and $`\operatorname{diag}(b, n/b)` fuse into the
single class of $`\operatorname{diag}(ab, mn/ab)`, and $`(a,b) \mapsto ab` bijects divisor pairs onto
divisors of $`mn`. Combining the prime-power and coprime cases prime-by-prime gives the general
divisor-sum formula. The degree statements follow by applying the multiplicative homomorphism $`\deg`
({uses "hecke-degree"}[]) to these identities: $`\deg T(p^k) = 1 + p + \dots + p^k` by induction on
the recurrence, and $`\deg T(m) = \sigma_1(m)` since both sides are multiplicative and agree on
prime powers.
:::

## Eigenforms, newforms, and the new/old decomposition

:::definition "eigenform-newform"
*Eigenforms, the old/new subspaces, and normalised newforms.*
An *eigenform* of weight $`k` and level $`\Gamma_1(N)` is a cusp form $`f` lying in a Nebentypus
eigenspace $`S_k(N, \chi) = \bigcap_d \ker(\langle d \rangle - \chi(d))` and a simultaneous
eigenfunction of all $`T(n)` with $`(n, N) = 1`, written $`T(n) f = \lambda_n f`. Commutativity of
the $`\mathrm{GL}_2` algebra ({uses "hecke-commutativity"}[]) — whose product law is the
multiplication table ({uses "hecke-multiplication-table"}[]) — makes the family
$`\{T(n)\}_{(n,N)=1}` simultaneously diagonalisable on the finite-dimensional space $`S_k(N, \chi)`,
so such eigenforms abound. The *old subspace* $`S_k^{\flat}(N)` is the span of all level-raising
images $`f(\ell z)` of cusp forms from proper divisors $`M \mid N`; the *new subspace*
$`S_k^{\sharp}(N) = (S_k^{\flat}(N))^{\perp}` is its Petersson-orthogonal complement. A *newform* is
an eigenform in $`S_k^{\sharp}(N)` normalised so that $`a_1(f) = 1`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`HeckeRing.GL2.Eigenform`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean#L49), the subspaces [`HeckeRing.GL2.cuspFormsOld`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean#L151) / [`cuspFormsNew`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean#L193), and [`HeckeRing.GL2.Newform`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/MainLemma.lean#L81) — sorry-free.

Depends on: {uses "cusp-form"}[] {uses "hecke-operator"}[]
:::

:::theorem "eigenvalue-equals-fourier-coeff"
*Eigenvalue equals Fourier coefficient for a normalised newform.*
Let $`f` be a normalised newform of weight $`k` and level $`\Gamma_1(N)` with Nebentypus $`\chi`.
For every $`n \ge 1` coprime to $`N`, the Hecke eigenvalue at $`n` equals the $`n`-th
$`q`-expansion coefficient,
$$`\lambda_n(f) \;=\; a_n(f),`
and consequently the Fourier coefficients are multiplicative: $`a_{mn}(f) = a_m(f)\,a_n(f)` for
$`(m, n) = 1`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`HeckeRing.GL2.Newform.eigenvalue_eq_coeff`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/MainLemma.lean#L126) and [`HeckeRing.GL2.Newform.eigenvalue_coprime_mul`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/CoeffSeq.lean#L50) — sorry-free.

Depends on: {uses "eigenform-newform"}[] {uses "q-expansion"}[]
:::

:::proof "eigenvalue-equals-fourier-coeff"
This is Miyake 4.5.15(1) in its normalised form. Apply $`T(n)` to $`f`: the eigenform relation gives
$`T(n) f = \lambda_n f`, so the first Fourier coefficient of $`T(n) f` is $`\lambda_n\, a_1(f)`. On
the other hand the explicit Fourier formula for $`T(n) f` expresses $`a_1(T(n) f)` as a sum over the
common divisors of $`1` and $`n`, which — since $`(n, N) = 1` — collapses to the single term
$`a_n(f)` ({uses "hecke-operator"}[]). Equating and using the normalisation $`a_1(f) = 1` gives
$`\lambda_n = a_n(f)`. Multiplicativity of the $`a_n` for coprime indices is then transported from
$`T(mn) = T(m)\,T(n)` ({uses "hecke-multiplication-table"}[]) through this identification.
:::

## Atkin–Lehner theory and strong multiplicity one

:::theorem "old-new-decomposition"
*Orthogonal old/new decomposition.*
The cusp space at level $`\Gamma_1(N)` is the internal orthogonal direct sum
$$`S_k(\Gamma_1(N)) \;=\; S_k^{\flat}(N) \;\oplus\; S_k^{\sharp}(N)`
of the old subspace and the new subspace $`S_k^{\sharp}(N) = (S_k^{\flat}(N))^{\perp}`
({uses "eigenform-newform"}[]). Consequently every cusp form $`f` has a unique decomposition
$`f = \operatorname{old}(f) + \operatorname{new}(f)` into old and new parts.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): the projections [`HeckeRing.GL2.oldPart`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean#L342) and [`newPart`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/Basic.lean#L347), built on `cuspFormsNew` — sorry-free.

Depends on: {uses "cusp-form"}[] {uses "eigenform-newform"}[]
:::

:::proof "old-new-decomposition"
Both facts are linear algebra over the Petersson inner product, which is positive-definite on
$`S_k(\Gamma_1(N))` ({uses "cusp-form"}[]). Trivial intersection
$`S_k^{\flat}(N) \cap S_k^{\sharp}(N) = 0` holds because a form in both a subspace and its orthogonal
complement is orthogonal to itself, hence of Petersson norm zero, hence zero. The spanning property
is the standard fact that a subspace and its orthogonal complement span any finite-dimensional space
with a nondegenerate inner product. Together these give the internal direct sum and the unique
old/new decomposition.
:::

:::theorem "atkin-lehner-main-lemma"
*Atkin–Lehner Main Lemma (Miyake 4.6.8 / Diamond–Shurman 5.7.1).*
Let $`f \in S_k(\Gamma_1(N))` be a cusp form whose Fourier coefficients vanish at all indices
coprime to the level,
$$`a_n(f) \;=\; 0 \qquad \text{for all } n \ge 1 \text{ with } \gcd(n, N) = 1.`
Then $`f` is an oldform: $`f \in S_k^{\flat}(N)`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): proved sorry-free
via Miyake's *descent* in the [`SMOObligations`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/SMOObligations/Lemma4_6_8.lean#L158) files and packaged as [`HeckeRing.GL2.oldPart_eq_zero_of_shared_eigenvalues`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean#L1188). (The alternative Petersson-adjoint route [`HeckeRing.GL2.mainLemma`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GL2/Newforms/MainLemma.lean#L142) remains a `sorry`, but strong multiplicity one does not use it.)

Depends on: {uses "eigenform-newform"}[] {uses "old-new-decomposition"}[] {uses "q-expansion"}[]
:::

:::proof "atkin-lehner-main-lemma"
The formalised proof avoids the Petersson adjoint entirely and instead descends, following Miyake
§4.6. Suppose $`f` is a common eigenfunction with all coprime Fourier coefficients vanishing. For
each prime $`p \mid N`, a descent witness lowers $`f` to a cusp form $`f_{\text{lower}}` at level
$`N/p` whose coprime coefficients reproduce those of $`f` at shifted indices; iterating across the
prime factors of $`N` exhibits $`f` as built from forms genuinely of lower level. Concretely, the
matching-summand construction produces, whenever the new part were nonzero, a nonzero new eigenform
$`h` at a proper divisor $`M \mid N` whose eigenvalues match $`f`'s; its leading coefficient is
nonzero ({uses "eigenvalue-equals-fourier-coeff"}[]), and $`h - c_1' f` then has vanishing coprime
coefficients, forcing $`f` itself into the old subspace — i.e. $`f \in S_k^{\flat}(N)`. This is
sorry-free; the spectral/adjoint inputs that the alternative proof would need are sidestepped.
:::

:::theorem "strong-multiplicity-one"
*Strong Multiplicity One (Miyake 4.6.12 / Diamond–Shurman 5.8.2).*
Let $`f` be a normalised newform in $`S_k(N, \chi)` and let $`g` be any cusp-form Hecke
eigenfunction in $`S_k(N, \chi)`. If $`f` and $`g` share the eigenvalue $`\lambda_n` for every
$`n` with $`(n, N) = 1` outside a finite set $`S`, then $`g = c\, f` for some $`c \in \mathbb{C}`.
In particular two normalised newforms in $`S_k(N, \chi)` agreeing on almost all $`\lambda_n` are
equal.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`HeckeRing.GL2.strongMultiplicityOne_constMul`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean#L1231) and the newform-uniqueness corollary [`HeckeRing.GL2.strongMultiplicityOne_axiom_clean`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/SMOObligations/StrongMultiplicityOneFull.lean#L1267) — sorry-free.

Depends on: {uses "eigenform-newform"}[] {uses "atkin-lehner-main-lemma"}[]
:::

:::proof "strong-multiplicity-one"
Normalise $`a_1(f) = 1` and split $`g = g^{\flat} + g^{\sharp}` along the orthogonal old/new
decomposition ({uses "old-new-decomposition"}[]). Both subspaces are Hecke-stable, so each piece is
again a common eigenfunction sharing $`f`'s eigenvalues off $`S`. For the new part: the difference
$`a_1(g^{\sharp})^{-1} g^{\sharp} - f` has vanishing coprime Fourier coefficients (by
$`a_n = a_1 \lambda_n`, {uses "eigenvalue-equals-fourier-coeff"}[], and the shared eigenvalues), so
it lies in the old subspace by the Main Lemma ({uses "atkin-lehner-main-lemma"}[]); being a
difference of new forms it is also new, hence zero, giving $`g^{\sharp} = a_1(g^{\sharp})\, f`. For
the old part: if $`g^{\flat} \neq 0` one descends to a nonzero new eigenform $`h` at a proper divisor
sharing $`f`'s eigenvalues, and then $`h - c_1' f \in S_k^{\flat}(N)` together with
$`h \in S_k^{\flat}(N)` would force $`f \in S_k^{\flat}(N)`, contradicting that $`f` is a nonzero
newform; hence $`g^{\flat} = 0`. Combining, $`g = g^{\sharp} = c\, f` with $`c = a_1(g)`. For the
two-newform corollary, comparing first coefficients of $`g = c f` with both forms normalised gives
$`c = 1`, so $`g = f`.
:::

## The Shimura surjection

:::theorem "shimura-surjection"
*Shimura surjection $`R(\Gamma, \Delta) \twoheadrightarrow R(\Gamma_0(N), \Delta_0(N))` (Shimura 3.35).*
Write $`\Gamma = \mathrm{SL}_2(\mathbb{Z})` and let $`\Delta` be the monoid of integral
$`2 \times 2` matrices of positive determinant. There is a surjective ring homomorphism
$$`\varphi \;:\; \mathbb{T}(\mathrm{GL}_2)\;=\;R(\Gamma, \Delta) \;\twoheadrightarrow\; R(\Gamma_0(N), \Delta_0(N))`
from the full $`\mathrm{GL}_2` Hecke ring onto the level-$`N` congruence Hecke ring: every element of
the congruence ring is the image of a full-level Hecke operator.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`HeckeRing.GLn.shimura_thm_3_35`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Surjectivity.lean#L1626) — sorry-free.

Depends on: {uses "hecke-ring"}[] {uses "hecke-commutativity"}[]
:::

:::proof "shimura-surjection"
The map is constructed as a lift through a quotient. A surjection $`\pi : \mathbb{Z}[X_{p,k}]
\twoheadrightarrow R(\Gamma, \Delta)` from a polynomial ring sends prime generators to the
prime-power Hecke classes; a second homomorphism $`\psi` on the same generators sends them to the
level-$`N` diagonal classes $`\operatorname{diag}(1, p)` and $`\operatorname{diag}(p, p)` for
$`p \nmid N` (and to zero otherwise). One checks $`\ker \pi \subseteq \ker \psi`, so $`\psi` factors
through $`R(\Gamma, \Delta)` to give $`\varphi`. Surjectivity holds because every basis class of the
congruence ring has a diagonal representative $`\operatorname{diag}(a, b)` with $`a \mid b` and
$`\gcd(a, N) = 1`, and the explicit coset analysis at the bad primes shows each such class is a
product of prime-power images of $`\psi`. In Lean this is exactly the lift of $`\psi` along
$`\pi`'s quotient followed by transport through the surjectivity of $`\pi`.
:::

## The valence formula

:::theorem "valence-formula"
*The valence (weight) formula for $`\mathrm{SL}_2(\mathbb{Z})`.*
Let $`k \in \mathbb{Z}` and let $`f \in M_k(\mathrm{SL}_2(\mathbb{Z}))` be a nonzero modular form on
the full modular group. Then the orders of vanishing of $`f` over the $`\mathrm{SL}_2(\mathbb{Z})`-orbits
in $`\mathbb{H}` satisfy
$$`\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f) + \tfrac{1}{3}\operatorname{ord}_\rho(f)
   + \sum_{q \in \mathrm{NonEll}} \operatorname{ord}_q(f) \;=\; \frac{k}{12},`
where the final sum runs over the $`\mathrm{SL}_2(\mathbb{Z})`-orbits other than those of $`i` and
$`\rho = e^{2\pi i/3}`, and $`\operatorname{ord}_q(f)` is the order of vanishing at any representative
of the orbit (well-defined by {uses "sl2-action"}[]).
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms): [`valence_formula_textbook`](https://github.com/CBirkbeck/LeanModularForms/blob/720d950b8c31ffd69b2cc7aa5323bccaefad62e1/LeanModularForms/ForMathlib/ValenceFormulaFinal.lean#L62) — sorry-free.

Depends on: {uses "modular-form"}[] {uses "q-expansion"}[]
:::

:::proof "valence-formula"
The proof is the textbook contour-integral argument (Diamond–Shurman 3.1.1) made rigorous through a
*generalised* residue theorem. One integrates the logarithmic derivative $`f'/f` around the boundary
$`\partial \mathcal{D}_H` of the standard fundamental domain truncated at height $`H`, using the
Hungerbühler–Wasem generalised winding-number machinery to handle the corners and the elliptic
fixed points. The simple poles of $`f'/f` inside $`\mathcal{D}` are exactly the zeros of $`f`, each
contributing its order of vanishing as residue. The boundary contributions evaluate term by term:
the top horizontal segment yields $`\operatorname{ord}_\infty(f)` via the $`q`-expansion
({uses "q-expansion"}[]); the two vertical edges cancel under $`T`-invariance and the two arcs
combine under $`S`-invariance ({uses "sl2-action"}[]); and the explicit winding numbers
$`-\tfrac12` at $`i` and $`-\tfrac16` at $`\rho` (and $`\rho + 1`) produce the fractional
coefficients $`\tfrac12` and $`\tfrac13` together with the global $`k/12`. Equating the residue sum
to the boundary integral and rearranging gives the stated identity.
:::

# Results from the ModFormDims project

The node below is drawn from the **ModFormDims** project
([`https://github.com/CBirkbeck/ModFormDims`](https://github.com/CBirkbeck/ModFormDims)), which
develops $`q`-expansion comparison tools and dimension-formula infrastructure for the modular-forms
library. It is informal here for the same reason as the LeanModularForms nodes.

:::theorem "neg-weight-rank-zero"
*Modular forms of negative weight vanish.*
For any integer $`k < 0`, the space $`M_k(\mathrm{SL}_2(\mathbb{Z}))` is zero:
$$`\operatorname{rank}_{\mathbb{C}} M_k(\mathrm{SL}_2(\mathbb{Z})) \;=\; 0.`
Equivalently, every modular form of negative weight and level $`\Gamma(1)` is identically zero.
Formalised in [`ModFormDims`](https://github.com/CBirkbeck/ModFormDims) (sorry-free).

Depends on: {uses "modular-form"}[] {uses "q-expansion"}[]
:::

:::proof "neg-weight-rank-zero"
By the maximum modulus principle applied to the cusp function. For a modular form $`f` of weight
$`k \le 0`, the function $`|f(z)|\,\operatorname{Im}(z)^{k/2}` is $`\mathrm{SL}_2(\mathbb{Z})`-invariant,
and the reduction theory of the fundamental domain translates any $`z` to a point of imaginary part
$`\ge \sqrt{3}/2`. The $`q`-expansion of $`f` ({uses "q-expansion"}[]) realises $`f` through a
function $`F` on the unit disc with $`f(z) = F(e^{2\pi i z})`; boundedness at the cusp extends $`F`
holomorphically across $`0`. The maximum modulus principle then forces $`F` to be constant, and for
$`k < 0` the slash-invariance forces that constant to be $`0` ({uses "slash-action"}[]); hence
$`f = 0` and the rank is zero.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib pull
requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing at the live
PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib v4.30.0-rc2. They
connect into the dependency graph through the mathlib-backed modular-forms nodes of this chapter via
`{uses}` edges, and should be re-pointed to `(lean := …)` once the corresponding PR merges.

:::theorem "e4-e6-graded-ring" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/38813")
*($`E_4` and $`E_6` generate the graded ring of level-one modular forms, freely.)* The graded
$`\mathbb{C}`-algebra of modular forms of level $`\mathrm{SL}_2(\mathbb{Z})`,
$`M_*(\mathrm{SL}_2(\mathbb{Z})) = \bigoplus_{k} M_k(\mathrm{SL}_2(\mathbb{Z}))`, is a free
polynomial algebra on the two Eisenstein series $`E_4` and $`E_6` ({uses "eisenstein-series"}[]):
$$`M_*(\mathrm{SL}_2(\mathbb{Z})) \;=\; \mathbb{C}[E_4, E_6],`
with $`E_4, E_6` algebraically independent. Concretely, the monomials $`E_4^a E_6^b` with
$`4a + 6b = k` form a $`\mathbb{C}`-basis of $`M_k(\mathrm{SL}_2(\mathbb{Z}))` for every even
$`k \ge 0`.

PR #38813 proves both that $`E_4, E_6` generate and that they are free (no algebraic relations),
upgrading the numerical dimension formula ({uses "dimension-level-one"}[]) to an explicit ring
presentation. Freeness is equivalent to the discriminant identity
$`\Delta = (E_4^3 - E_6^2)/1728` ({uses "discriminant-e4-e6"}[]) cutting out the cusp ideal.
In review — [mathlib PR #38813](https://github.com/leanprover-community/mathlib4/pull/38813).
:::

:::theorem "sturm-bound" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/39000")
*(Sturm bound.)* Let $`\Gamma \le \mathrm{SL}_2(\mathbb{Z})` be a finite-index subgroup and
$`f \in M_k(\Gamma)` a modular form ({uses "modular-form"}[]) of weight $`k`. If the $`q`-expansion
({uses "q-expansion"}[]) of $`f` at the cusp $`\infty` vanishes to order exceeding the *Sturm bound*
$$`B(\Gamma, k) \;=\; \left\lfloor \frac{k}{12}\,[\mathrm{SL}_2(\mathbb{Z}) : \Gamma] \right\rfloor,`
i.e. $`a_n(f) = 0` for all $`n \le B(\Gamma, k)`, then $`f = 0`. Consequently two modular forms of
weight $`k` and level $`\Gamma` agreeing up to the Sturm bound are equal.

The bound is a direct consequence of the valence (weight) formula ({uses "valence-formula"}[]): a
nonzero form of weight $`k` cannot vanish at $`\infty` to order exceeding its total allowed order of
vanishing $`\tfrac{k}{12}[\mathrm{SL}_2 : \Gamma]`. PR #39000 establishes the bound for finite-index
subgroups, the standard finite check for equality of modular forms and Hecke eigensystems.
In review — [mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000).
:::

:::definition "serre-derivative" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/36963")
For an integer $`k`, the *Serre derivative* $`\vartheta_k` sends a weight-$`k` modular form
({uses "modular-form"}[]) to a weight-$`(k+2)` modular form by correcting the naive $`q`-derivative
with the quasimodular Eisenstein series $`E_2`:
$$`\vartheta_k f \;=\; q\,\frac{df}{dq} \;-\; \frac{k}{12}\, E_2\, f, \qquad q = e^{2\pi i z},`
where $`E_2(z) = 1 - 24\sum_{n \ge 1} \sigma_1(n)\, q^n` ({uses "eisenstein-series"}[]). Although
$`q\,\tfrac{df}{dq}` and $`E_2 f` are each only quasimodular, the $`E_2`-correction cancels the
anomaly so that $`\vartheta_k f` transforms with weight $`k + 2` under the slash action
({uses "slash-action"}[]); on $`q`-expansions ({uses "q-expansion"}[]) it acts as
$`\sum a_n q^n \mapsto \sum n\, a_n q^n` plus the $`E_2`-term.

PR #36963 sets up the $`\mathrm{SL}_2` action on the relevant function spaces and defines the Serre
derivative, the basic weight-raising operator underlying the Rankin–Cohen brackets and the ring of
quasimodular forms.
In review — [mathlib PR #36963](https://github.com/leanprover-community/mathlib4/pull/36963).
:::
