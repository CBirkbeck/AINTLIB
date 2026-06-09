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
form $`\Delta`. Throughout, $`\mathbb{H}` denotes the open upper half-plane, $`\mathrm{SL}_2(\mathbb{Z})`
the full modular group, and $`M_k(\Gamma)`, $`S_k(\Gamma)` the spaces of modular forms and cusp
forms of weight $`k` and level $`\Gamma`.

**Results deferred to companion projects.** The *valence (weight) formula*, *strong multiplicity
one*, *Hecke operators and eigenforms*, and the full *dimension formula for congruence subgroups*
are being developed in the LeanModularForms and LeanModularForms-hecke projects (Phase 3 of AINTLIB).
The $`E_4`/$`E_6` graded-ring structure theorem and the Sturm bound are forthcoming mathlib PRs;
they are not yet available in mathlib v4.30.0-rc2 beyond the specific results authored below.

# The upper half-plane and the Möbius action

:::definition "upper-half-plane" (lean := "UpperHalfPlane")
The *upper half-plane* $`\mathbb{H}` is the set of complex numbers with strictly positive imaginary
part:
$$`\mathbb{H} \;=\; \{\, z \in \mathbb{C} \;\mid\; \operatorname{Im}(z) > 0 \,\}.`
It is realised in mathlib as the subtype of $`\mathbb{C}` with the positivity condition
$`0 < \operatorname{Im}(z)`.
:::

:::definition "sl2-action" (lean := "UpperHalfPlane.glAction, UpperHalfPlane.SLAction")
Let $`g = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})` with
$`\det(g) > 0`. The *Möbius action* of $`g` on $`\mathbb{H}` is
$$`g \cdot z \;=\; \frac{az + b}{cz + d}.`
This makes $`\mathbb{H}` a left $`\mathrm{GL}_2(\mathbb{R})`-set. The modular group
$`\mathrm{SL}_2(\mathbb{Z})` acts on $`\mathbb{H}` via the same formula, since $`\det(g) = 1 > 0`
for $`g \in \mathrm{SL}_2(\mathbb{Z})`.
:::

:::proof "sl2-action"
The key ingredient is that $`\mathrm{Im}(g \cdot z) = \det(g) \cdot \mathrm{Im}(z) / |cz + d|^2`,
so the imaginary part stays positive when $`\det(g) > 0` and $`z \in \mathbb{H}`. The associativity
law $`g \cdot (h \cdot z) = (gh) \cdot z` follows from the denominator cocycle identity
$`c_{gh}(z) = c_g(h \cdot z) \cdot c_h(z)`, where $`c_g(z) = cz + d` is the denominator
({uses "upper-half-plane"}[]).
:::

# The weight-$`k` slash action

:::definition "slash-action" (lean := "SlashAction, ModularForm.slash_apply")
For an integer $`k`, a matrix $`g \in \mathrm{GL}_2(\mathbb{R})`, and a function
$`f : \mathbb{H} \to \mathbb{C}`, the *weight-$`k` slash action* is
$$`(f \mid_k g)(z) \;=\; \det(g)^{k/2} \, (cz + d)^{-k} \, f(g \cdot z),`
where $`c, d` are the bottom-row entries of $`g` and $`g \cdot z` is the Möbius action
({uses "sl2-action"}[]) of $`g` on the upper half-plane. This extends to an action on functions
$`\mathbb{H} \to \mathbb{C}`. The product rule
$$`(fg) \mid_{k_1 + k_2} g \;=\; (f \mid_{k_1} g) \cdot (g \mid_{k_2} g)`
holds for any two functions $`f, g`.
:::

:::definition "slash-invariant-form" (lean := "SlashInvariantForm")
A *slash-invariant form* of weight $`k` and level $`\Gamma \le \mathrm{GL}_2(\mathbb{R})` is a
function $`f : \mathbb{H} \to \mathbb{C}` that is invariant under the slash action of every
$`\gamma \in \Gamma`:
$$`f \mid_k \gamma \;=\; f \quad \text{for all } \gamma \in \Gamma.`
:::

# Modular forms and cusp forms

:::definition "modular-form" (lean := "ModularForm")
A *modular form* of weight $`k \in \mathbb{Z}` and level $`\Gamma` is a slash-invariant form
({uses "slash-invariant-form"}[]) that additionally:

1. is holomorphic on $`\mathbb{H}` (complex-differentiable at every point), and
2. is *bounded at every cusp* of $`\Gamma`: for each cusp $`c`, the function
   $`f \mid_k g` is bounded as $`\mathrm{Im}(z) \to \infty`, where $`g \in \mathrm{GL}_2(\mathbb{R})`
   carries $`\infty` to $`c`.

The space of all such forms is a $`\mathbb{C}`-vector space denoted $`M_k(\Gamma)`.
:::

:::definition "cusp-form" (lean := "CuspForm")
A *cusp form* of weight $`k` and level $`\Gamma` is a slash-invariant form
({uses "slash-invariant-form"}[]) that is holomorphic on $`\mathbb{H}` and *vanishes at every
cusp*: the same $`f \mid_k g` tends to $`0` as $`\mathrm{Im}(z) \to \infty`. The subspace of
cusp forms is denoted $`S_k(\Gamma) \subseteq M_k(\Gamma)`.
:::

:::lemma_ "cusp-form-submodule" (lean := "ModularForm.cuspFormSubmodule, ModularForm.CuspForm.equivCuspFormSubmodule")
The space of cusp forms $`S_k(\Gamma)` embeds into $`M_k(\Gamma)` as a $`\mathbb{C}`-submodule, and
the type $`S_k(\Gamma)` is linearly equivalent to this submodule:
$$`S_k(\Gamma) \;\simeq_{\mathbb{C}}\; \mathrm{cuspFormSubmodule}(\Gamma, k) \;\subseteq\; M_k(\Gamma).`
:::

:::proof "cusp-form-submodule"
The inclusion $`S_k(\Gamma) \hookrightarrow M_k(\Gamma)` is the linear map sending a cusp form
to the same function viewed as a modular form. It is injective because a modular form is a cusp
form if and only if it vanishes at all cusps ({uses "cusp-form"}[]). The linear equivalence follows
from the fact that the range of an injective linear map is linearly equivalent to the domain.
:::

# The $`q`-expansion

:::definition "q-expansion" (lean := "UpperHalfPlane.qExpansion")
Let $`f : \mathbb{H} \to \mathbb{C}` and let $`h > 0`. The *$`q`-expansion of $`f` with parameter
$`h`* is the formal power series
$$`\mathrm{qExp}_h(f) \;=\; \sum_{n=0}^{\infty} a_n \, q^n \;\in\; \mathbb{C}[[q]],`
where $`q = e^{2\pi i z / h}` and the coefficients $`a_n` are the Taylor coefficients of the
analytic function $`F` satisfying $`f(z) = F(e^{2\pi i z/h})` near the cusp.
:::

:::lemma_ "q-expansion-convergence" (lean := "UpperHalfPlane.hasSum_qExpansion")
Let $`f : \mathbb{H} \to \mathbb{C}` be periodic with period $`h > 0`, holomorphic, and bounded
as $`\mathrm{Im}(z) \to \infty`. Then the $`q`-expansion of $`f` converges: for every
$`z \in \mathbb{H}`,
$$`f(z) \;=\; \sum_{n=0}^{\infty} a_n \, e^{2\pi i n z / h}.`
:::

:::proof "q-expansion-convergence"
Periodicity and holomorphicity imply that $`f` factors through the analytic function $`F`
satisfying $`f(z) = F(e^{2\pi iz/h})` ({uses "q-expansion"}[]). The boundedness at the cusp ensures
$`F` extends analytically to $`0`, so the Taylor series of $`F` at $`0` converges on the open unit
disc. Substituting $`q = e^{2\pi iz/h}`, which lies in the open unit disc for $`z \in \mathbb{H}`,
gives the stated sum.
:::

:::lemma_ "q-expansion-unique" (lean := "UpperHalfPlane.qExpansion_coeff_unique")
Under the same hypotheses, the $`q`-expansion coefficients are uniquely determined by $`f` and
$`h`: if $`\sum_n c_n \, e^{2\pi i n z/h} = f(z)` for all $`z \in \mathbb{H}`, then $`c_n = a_n`
for all $`n`.
:::

:::proof "q-expansion-unique"
Both the given series and the $`q`-expansion ({uses "q-expansion"}[]) represent $`f` as a power
series in $`q = e^{2\pi i z/h}` convergent on the punctured unit disc ({uses "q-expansion-convergence"}[]).
A holomorphic function on the disc has a unique Taylor expansion, so two convergent power series in
$`q` that agree as functions of $`z` — equivalently as functions of $`q` on a punctured neighbourhood
of $`0` — must have identical coefficients; hence $`c_n = a_n` for every $`n`.
:::

# Eisenstein series

:::definition "eisenstein-series" (lean := "ModularForm.eisensteinSeriesMF, ModularForm.E")
For an integer $`k \ge 3`, a positive integer $`N`, and a congruence condition
$`a \in (\mathbb{Z}/N\mathbb{Z})^2`, the *Eisenstein series of weight $`k`, level $`\Gamma(N)`,
and characteristic $`a`* is the function
$$`\mathcal{E}_{k,a}(z) \;=\; \sum_{\substack{(m,n) \in \mathbb{Z}^2,\; \gcd(m,n) = 1 \\ (m,n) \equiv a \pmod{N}}} \frac{1}{(mz + n)^k}.`
The *normalised Eisenstein series* of weight $`k` and level $`1` is
$$`E_k(z) \;=\; \tfrac{1}{2} \sum_{\substack{(m,n) \in \mathbb{Z}^2 \\ \gcd(m,n) = 1}} \frac{1}{(mz + n)^k}.`
:::

:::theorem "eisenstein-is-modular-form" (lean := "ModularForm.eisensteinSeriesMF")
For any $`k \ge 3`, $`N \ge 1`, and $`a \in (\mathbb{Z}/N\mathbb{Z})^2`, the Eisenstein series
$`\mathcal{E}_{k,a}` defines a modular form in $`M_k(\Gamma(N))`.
:::

:::proof "eisenstein-is-modular-form"
The slash-invariance of the Eisenstein series ({uses "eisenstein-series"}[]) under $`\Gamma(N)`
follows from the fact that the set of coprime pairs congruent to $`a` mod $`N` is preserved under
the row-vector action of $`\Gamma(N)` ({uses "slash-invariant-form"}[]). Holomorphicity on
$`\mathbb{H}` comes from the uniform
convergence of the defining series on compact subsets of $`\mathbb{H}`, which in turn follows from
the estimate $`|mz + n|^{-k} \le C \cdot \mathrm{Im}(z)^{-k/2}` on compact sets. Boundedness at
the cusps uses the explicit analysis of the cusp-function transform ({uses "q-expansion"}[]).
:::

:::theorem "eisenstein-nonzero" (lean := "EisensteinSeries.E_ne_zero")
For every even $`k \ge 3`, the normalised Eisenstein series $`E_k` is nonzero.
:::

:::proof "eisenstein-nonzero"
The constant term of the $`q`-expansion of $`E_k` is $`1`
({uses "eisenstein-q-expansion-coeff-zero"}[]). In particular $`E_k` is not identically zero.
:::

:::lemma_ "eisenstein-q-expansion-coeff-zero" (lean := "EisensteinSeries.E_qExpansion_coeff_zero")
For even $`k \ge 3`, the constant term of the $`q`-expansion of $`E_k` is
$$`a_0(E_k) \;=\; 1.`
:::

:::lemma_ "eisenstein-q-expansion" (lean := "EisensteinSeries.E_qExpansion_coeff")
For even $`k \ge 3` and every $`m \ge 1`, the $`m`-th $`q`-expansion coefficient of $`E_k` is
$$`a_m(E_k) \;=\; -\frac{2k}{B_k} \, \sigma_{k-1}(m),`
where $`B_k` is the $`k`-th Bernoulli number and $`\sigma_{k-1}(m) = \sum_{d \mid m} d^{k-1}` is
the divisor-power sum.
:::

:::proof "eisenstein-q-expansion"
The key identity is the Lipschitz formula
$$`\sum_{n \in \mathbb{Z}} (z + n)^{-k} \;=\; \frac{(-2\pi i)^k}{(k-1)!} \sum_{m=1}^{\infty} m^{k-1} e^{2\pi i m z},`
which converts the defining sum of the normalised Eisenstein series ({uses "eisenstein-series"}[])
over coprime pairs into a sum of divisor-power sums. Summing instead over *all* nonzero integer
pairs factors as $`2\zeta(k)` ({uses "riemann-zeta"}[]) times the coprime sum; isolating the coprime
contribution by Möbius inversion ({uses "moebius-inversion"}[]) over the gcd then yields the
coefficient formula. The stated form follows from the value $`\zeta(k) = -(2\pi i)^k B_k / (2 \cdot k!)`.
:::

# The discriminant modular form

:::definition "modular-discriminant" (lean := "CuspForm.discriminant")
The *modular discriminant* $`\Delta` is the unique (up to scalar) nonzero cusp form of weight $`12`
and level $`1`. It is given explicitly by the Dedekind eta function:
$$`\Delta(z) \;=\; e^{2\pi i z} \prod_{n=1}^{\infty} (1 - e^{2\pi i n z})^{24}
              \;=\; \eta(z)^{24},`
where $`\eta(z) = e^{\pi i z/12} \prod_{n=1}^{\infty}(1 - e^{2\pi i n z})` is the Dedekind
eta function. In particular $`\Delta` is a cusp form in $`S_{12}(\mathrm{SL}_2(\mathbb{Z}))`.
At a point $`\tau \in \mathbb{H}`, the value $`\Delta(\tau)` is, up to the standard normalisation,
the discriminant ({uses "weierstrass-discriminant"}[]) of the elliptic curve
$`\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)` in its Weierstrass model $`y^2 = 4x^3 - g_2 x - g_3`;
indeed $`(2\pi)^{12}\Delta = g_2^3 - 27 g_3^2`, the discriminant of that cubic.
:::

:::theorem "discriminant-e4-e6" (lean := "ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq")
The modular discriminant satisfies the identity
$$`\Delta(z) \;=\; \frac{E_4(z)^3 - E_6(z)^2}{1728}`
pointwise for all $`z \in \mathbb{H}`.
:::

:::proof "discriminant-e4-e6"
The combination $`E_4^3 - E_6^2` is a cusp form of weight 12
({uses "cusp-form"}[]): its constant $`q`-expansion coefficient vanishes because the constant
terms of $`E_4` and $`E_6` are both $`1`
({uses "eisenstein-q-expansion-coeff-zero"}[]). Since $`S_{12}(\mathrm{SL}_2(\mathbb{Z}))` is
one-dimensional ({uses "cusp-form-weight-twelve-rank-one"}[]), this combination is a scalar
multiple of $`\Delta`. Reading off the first $`q`-expansion coefficient on each side —
$`(E_4^3 - E_6^2)` has coefficient $`1728` at $`q^1` while $`\Delta` has coefficient $`1`
({uses "discriminant-q-coeff-one"}[]) — pins the scalar to $`1728`.
:::

# Dimension formula for level-one modular forms

:::lemma_ "cusp-form-weight-twelve-rank-one" (lean := "CuspForm.rank_eq_one_of_weight_eq_twelve")
The space $`S_{12}(\mathrm{SL}_2(\mathbb{Z}))` is one-dimensional over $`\mathbb{C}`.
:::

:::proof "cusp-form-weight-twelve-rank-one"
This is proved by establishing the linear equivalence
$`S_k \cong M_{k-12}` given by dividing by $`\Delta`
({uses "discriminant-equiv"}[]). At $`k = 12`, $`M_0` is spanned by the constant function $`1`,
so $`S_{12}` is at most one-dimensional. The discriminant itself ({uses "modular-discriminant"}[]) shows
it is at least one-dimensional.
:::

:::theorem "discriminant-equiv" (lean := "CuspForm.discriminantEquiv, CuspForm.ofMulDiscriminant")
For any weight $`k`, multiplication by the discriminant $`\Delta` defines a linear isomorphism
$$`S_k(\mathrm{SL}_2(\mathbb{Z})) \;\xrightarrow{\;\sim\;}\; M_{k-12}(\mathrm{SL}_2(\mathbb{Z})), \quad f \;\mapsto\; f / \Delta.`
:::

:::proof "discriminant-equiv"
Since $`\Delta` is everywhere nonzero on $`\mathbb{H}` (it is a nonzero eta-product), dividing a
cusp form of weight $`k` by $`\Delta` produces a holomorphic function on $`\mathbb{H}`, and the
slash-invariance passes to weight $`k - 12`
({uses "slash-action"}[]). Boundedness at the cusps follows from the fact that the zero of a cusp
form at a cusp is at least as deep as the zero of $`\Delta`. The inverse map multiplies by
$`\Delta`.
:::

:::theorem "dimension-level-one" (lean := "ModularForm.dimension_level_one")
For every even natural number $`k`, the dimension of $`M_k(\mathrm{SL}_2(\mathbb{Z}))` over
$`\mathbb{C}` is
$$`\dim_{\mathbb{C}} M_k(\mathrm{SL}_2(\mathbb{Z})) \;=\;
\begin{cases} \lfloor k/12 \rfloor & \text{if } k \equiv 2 \pmod{12}, \\
              \lfloor k/12 \rfloor + 1 & \text{otherwise.}
\end{cases}`
In particular $`M_0 = \mathbb{C}`, $`M_2 = 0`, $`M_4 \cong \mathbb{C}`, and $`M_6 \cong \mathbb{C}`.
:::

:::proof "dimension-level-one"
The proof proceeds by strong induction on $`k`. The base cases $`k \le 11` are handled directly
(using the vanishing of $`S_k` for $`k < 12`
({uses "cusp-form-rank-zero-lt-twelve"}[]) and the rank-one result for weights $`4` and $`6`).
For $`k \ge 12`, the isomorphism $`S_k \cong M_{k-12}`
({uses "discriminant-equiv"}[]) and the splitting
$`\dim M_k = 1 + \dim S_k`
({uses "rank-one-plus-rank-cusp"}[]) reduce the formula to the inductive hypothesis. The parity
condition on $`k \mod 12` is then verified by arithmetic.
:::

:::lemma_ "cusp-form-rank-zero-lt-twelve" (lean := "CuspForm.rank_eq_zero_of_weight_lt_twelve")
For $`k < 12`, the space $`S_k(\mathrm{SL}_2(\mathbb{Z}))` is zero.
:::

:::lemma_ "rank-one-plus-rank-cusp" (lean := "ModularForm.rank_eq_one_add_rank_cuspForm")
For every even $`k \ge 3`, the dimension of $`M_k(\mathrm{SL}_2(\mathbb{Z}))` satisfies
$$`\dim M_k \;=\; 1 + \dim S_k.`
:::

:::proof "rank-one-plus-rank-cusp"
The normalised Eisenstein series $`E_k` ({uses "eisenstein-is-modular-form"}[]) is nonzero
({uses "eisenstein-nonzero"}[]) and its constant $`q`-expansion term is $`1`
({uses "eisenstein-q-expansion-coeff-zero"}[]). Therefore $`E_k` does not lie in $`S_k`
(cusp forms have vanishing constant term). Every $`f \in M_k` can be adjusted by a scalar
multiple of $`E_k` to land in $`S_k`, so the quotient $`M_k / S_k` is one-dimensional, giving
$`\dim M_k = 1 + \dim S_k`.
:::

:::lemma_ "discriminant-q-coeff-one" (lean := "ModularForm.discriminant_qExpansion_coeff_one")
The first $`q`-expansion coefficient of $`\Delta` is $`1`:
$$`\Delta(z) \;=\; q \,+\, \sum_{n=2}^{\infty} \tau(n) \, q^n, \quad q = e^{2\pi i z},`
where $`\tau` is the Ramanujan tau function.
:::

:::theorem "finite-dimensional-modular-forms" (lean := "ModularForm.dimension_level_one, ModularForm.levelOne_odd_weight_rank_zero")
For every weight $`k \in \mathbb{Z}`, the space $`M_k(\mathrm{SL}_2(\mathbb{Z}))` is
finite-dimensional over $`\mathbb{C}`.
:::

:::proof "finite-dimensional-modular-forms"
For negative $`k`, the space is zero (the slash-invariance and holomorphicity force vanishing).
For even non-negative $`k`, finite-dimensionality follows directly from the dimension formula
({uses "dimension-level-one"}[]). For odd $`k`, the element $`-1 \in \mathrm{SL}_2(\mathbb{Z})`
acts on any modular form of odd weight by $`-1`, so $`f = -f`, hence $`f = 0`, and the space
is again zero.
:::

# Phase 3 (LeanModularForms — external project)

The nodes below formalise results whose proofs require substantially more machinery than is
currently in Mathlib v4.30.0-rc2. They are drawn from the **LeanModularForms** project
([`https://github.com/CBirkbeck/LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms)),
in particular its `hecke-ring` branch (unmerged as of June 2026), which carries the Hecke
algebra, eigenforms, strong multiplicity one, the Atkin–Lehner theory, the Shimura surjection,
and the valence formula. Each node carries a provenance line recording which repo and branch
holds the formalisation and its current sorry status.

Throughout this section, $`N \ge 1` is the level, $`k \in \mathbb{Z}` is the weight,
$`\Gamma_1(N)` and $`\Gamma_0(N)` are the standard congruence subgroups, and
$`M_k(\Gamma)`, $`S_k(\Gamma)` denote the spaces of modular forms and cusp forms at that
level and weight. The Hecke operators are denoted $`T(n)`, the diamond operator $`\langle n\rangle`,
and the abstract $`\mathrm{GL}_2` Hecke algebra $`\mathbb{T}`.

## The valence formula

:::theorem "valence-formula"
*The valence (weight) formula for $`\mathrm{SL}_2(\mathbb{Z})`.*
Let $`k \in \mathbb{Z}` and let $`f \in M_k(\mathrm{SL}_2(\mathbb{Z}))` be a nonzero modular
form on the full modular group. Then the orders of vanishing of $`f` at the various
$`\mathrm{SL}_2(\mathbb{Z})`-orbits satisfy
$$`
  \operatorname{ord}_\infty(f)
    + \tfrac{1}{2}\,\operatorname{ord}_i(f)
    + \tfrac{1}{3}\,\operatorname{ord}_\rho(f)
    + \sum_{q \in \mathrm{NonEll}} \operatorname{ord}_q(f)
  \;=\; \frac{k}{12},
`
where the sum runs over $`\mathrm{SL}_2(\mathbb{Z})`-orbits in $`\mathbb{H}` other than the
orbits of $`i` and $`\rho = e^{2\pi i/3}`, and $`\operatorname{ord}_q(f)` is the order of
vanishing at any representative of the orbit (well-defined by {uses "sl2-action"}[]).
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).
:::

:::proof "valence-formula"
The proof is a contour-integral argument around the fundamental-domain boundary. One applies
the Hungerbühler–Wasem generalised residue theorem to the logarithmic derivative $`f'/f`
along $`\partial \mathcal{D}_H` at a sufficiently large height $`H`. The simple poles of
$`f'/f` on $`\mathcal{D}` are exactly the zeros of $`f`, each contributing its order of
vanishing as the residue. The total contour integral evaluates to
$`2\pi i\,(\operatorname{ord}_\infty(f) - k/12)` — the top horizontal segment contributes
$`\operatorname{ord}_\infty(f)` via the {uses "q-expansion"}[], the two vertical edges cancel
by $`T`-invariance ({uses "sl2-action"}[]), and the two arcs contribute $`-k/12` by
$`S`-invariance. Equating the two expressions and using the explicit elliptic winding numbers
$`-\tfrac{1}{2}` at $`i` and $`-\tfrac{1}{6}` at $`\rho` and $`\rho+1`, together with modular
pairing of the boundary arcs and edges, rearranges into the stated formula. The connection to
the dimension formula ({uses "dimension-level-one"}[]) comes from the fact that a nonzero form
of weight $`k` cannot have total vanishing exceeding $`k/12`, bounding the dimension of
$`M_k` and yielding the formula via the discriminant isomorphism ({uses "discriminant-equiv"}[]).
Uses: {uses "modular-discriminant"}[] {uses "dimension-level-one"}[]
:::

## Hecke operators and the Hecke algebra

:::definition "hecke-operator"
*Hecke operators $`T(n)` on $`M_k(\Gamma_1(N))`.*
Fix a positive integer $`N` and weight $`k`. For each positive integer $`n`, the *Hecke
operator* $`T(n)` is a $`\mathbb{C}`-linear endomorphism of $`M_k(\Gamma_1(N))`. At a prime
$`p \nmid N` it is defined by the explicit coset-summed slash action
$$`
  T(p)\,f \;=\; \sum_{b=0}^{p-1} f\big|_k\begin{pmatrix}1 & b\\ 0 & p\end{pmatrix}
             \;+\; \langle p\rangle f\big|_k\begin{pmatrix}p & 0\\ 0 & 1\end{pmatrix},
`
where $`\langle p\rangle` is the diamond operator ({uses "slash-action"}[]). At a prime
$`p \mid N` only the upper-triangular sum survives (the diamond term is zero). Higher
prime-power operators $`T(p^v)` satisfy the three-term recurrence
$$`
  T(p^{v+2}) \;=\; T(p)\,T(p^{v+1}) - p^{k-1}\,\langle p\rangle\,T(p^{v}),
`
and general $`T(n)` is assembled multiplicatively from prime-power components.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "modular-form"}[] {uses "slash-action"}[]
:::

:::theorem "hecke-algebra-action"
*The Hecke algebra acts on modular forms.*
For each weight $`k`, the assignment $`T \mapsto (f \mapsto f|_k T)` defines a ring
homomorphism
$$`
  \mathbb{T} \;\longrightarrow\; \operatorname{End}_{\mathbb{C}}(M_k(\mathrm{SL}_2(\mathbb{Z})))
`
from the abstract $`\mathrm{GL}_2` Hecke algebra into the $`\mathbb{C}`-linear endomorphisms of
$`M_k`. The analogous statement holds at level $`\Gamma_0(N)`: there is a ring homomorphism
from the congruence Hecke ring $`R(\Gamma_0(N), \Delta_0(N))` to
$`\operatorname{End}_{\mathbb{C}}(M_k(\Gamma_0(N)))`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "hecke-operator"}[] {uses "modular-form"}[]
:::

:::proof "hecke-algebra-action"
Additivity and $`\mathbb{C}`-linearity of each individual Hecke operator $`T(n)` are immediate
from the linearity of the slash action ({uses "slash-action"}[]). The substantive content is
*multiplicativity*: the composition $`T(D_1) \circ T(D_2)` equals $`T(D_2 \cdot D_1)` as maps
on $`M_k`. This holds because the double-coset product in the Hecke ring is defined precisely
so that the slash sums compose correctly (Shimura, Proposition 3.30): the coset representatives
of the product double coset are exactly the products of coset representatives, up to the
$`\mathrm{SL}_2(\mathbb{Z})`-symmetry which merely relabels summands in $`f|_k D`. Commutativity
of the Hecke algebra then forces the image in
$`\operatorname{End}(M_k)` to be a commutative subalgebra.
:::

:::theorem "hecke-operator-multiplicativity"
*Classical multiplicativity and commutativity of the $`T(n)`.*
For $`m, n \ge 1` coprime to $`N`, the Hecke operators satisfy
$$`
  T(mn) \;=\; T(m)\,T(n) \quad (\gcd(m,n) = 1),
`
and for a prime $`p` the prime-power recurrence holds. Moreover, $`T(m)` and $`T(n)` commute
for all $`m, n` coprime to $`N`, and each $`T(n)` commutes with every diamond operator
$`\langle d \rangle`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "hecke-operator"}[]
:::

:::proof "hecke-operator-multiplicativity"
Multiplicativity is *transported from the Hecke ring*: inside the commutative ring
$`R(\Gamma_0(N), \Delta_0(N))` the ring-side elements $`D_n` satisfy $`D_{mn} = D_m D_n`
for coprime $`m, n` by pure commutative algebra (the multiplication table of Shimura 3.24).
Character-space homomorphisms sending $`D_n` to $`\chi(n)^{-1} T(n)` on each Nebentypus
subspace $`M_k(N,\chi)`, combined with the direct-sum decomposition
$`M_k(\Gamma_1(N)) = \bigoplus_\chi M_k(N,\chi)`, pull the ring identity back to the operator
identity. Commutativity is inherited from the commutativity of the Hecke ring, established via
Shimura's anti-involution argument for the Atkin–Lehner-conjugated transpose.
:::

## Eigenforms and newforms

:::definition "eigenform-newform"
*Eigenforms and normalised newforms.*
An *eigenform* of weight $`k` and level $`\Gamma_1(N)` is a cusp form $`f` carrying a
Nebentypus character $`\chi` (so $`f \in S_k(N,\chi)$`) that is a simultaneous eigenfunction
of all Hecke operators $`T(n)` with $`(n,N) = 1`: for each such $`n` there is a scalar
$`\lambda_n \in \mathbb{C}` with $`T(n) f = \lambda_n f`. The *old subspace*
$`S_k^\flat(N)` is the span of all level-raising images $`f(\ell z)` from proper divisors of
$`N`; the *new subspace* $`S_k^\sharp(N)` is its Petersson-orthogonal complement. A
*newform* (normalised) is an eigenform in $`S_k^\sharp(N)` normalised so that $`a_1(f) = 1`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "cusp-form"}[] {uses "hecke-operator"}[]
:::

:::theorem "eigenvalue-equals-fourier-coeff"
*Eigenvalue equals Fourier coefficient for a normalised newform.*
Let $`f` be a normalised newform of weight $`k` and level $`\Gamma_1(N)` with Nebentypus
character $`\chi$`. For every $`n \ge 1` coprime to $`N`, the Hecke eigenvalue at $`n` equals
the $`n$`-th $`q$`-expansion coefficient:
$$`
  \lambda_n(f) \;=\; a_n(f).
`
In particular the Fourier coefficients of a newform are multiplicative:
$`a_{mn}(f) = a_m(f) a_n(f)` for $`\gcd(m,n) = 1`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "eigenform-newform"}[] {uses "q-expansion"}[]
:::

:::proof "eigenvalue-equals-fourier-coeff"
Applying $`T(n)` to the normalised form $`f` gives $`T(n) f = \lambda_n f`; reading off the
first Fourier coefficient and using the explicit Fourier-coefficient formula for
$`T(n) f` ({uses "hecke-operator"}[]) — which at index $`1` collapses the divisor sum to the
single term $`d = 1`, yielding $`a_1(T(n)f) = a_n(f)` — together with the eigenvalue
equation $`a_1(\lambda_n f) = \lambda_n a_1(f) = \lambda_n` (since $`a_1(f) = 1`) gives
$`\lambda_n = a_n(f)`. Multiplicativity of the Fourier coefficients for coprime indices then
follows from $`T(mn) = T(m) T(n)` ({uses "hecke-operator-multiplicativity"}[]).
:::

## Strong multiplicity one

:::theorem "strong-multiplicity-one"
*Strong Multiplicity One (Miyake 4.6.12 / Diamond–Shurman 5.8.2).*
Let $`f` be a normalised newform in $`S_k(N, \chi)$` and let $`g` be any cusp-form Hecke
eigenfunction in $`S_k(N, \chi)`. If $`f` and $`g` share the same Hecke eigenvalue
$`\lambda_n` for every $`n` with $`(n,N) = 1` outside a finite set, then $`g = c f` for
some $`c \in \mathbb{C}`. In particular, two normalised newforms in $`S_k(N, \chi)` that
agree on almost all $`\lambda_n` are equal.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "eigenform-newform"}[] {uses "hecke-operator"}[]
:::

:::proof "strong-multiplicity-one"
Split $`g = g^\flat + g^\sharp$` along the Petersson-orthogonal old/new decomposition. Since
both subspaces are stable under the Hecke operators, each piece is again a common eigenfunction
sharing $`f$`'s eigenvalues off the finite set. For the new part: a difference
$`(a_1(g^\sharp))^{-1} g^\sharp - f$` (assuming $`g^\sharp \ne 0$`) has vanishing Fourier
coefficients at all indices coprime to $`N$` by the Miyake 4.5.15(1) identity
$`a_n = a_1 \lambda_n$` and the shared eigenvalues; such a form lies in the old subspace
({uses "eigenform-newform"}[]), but is also new, so it is zero, giving $`g^\sharp = a_1(g^\sharp) f$`.
For the old part: if $`g^\flat \ne 0$` one descends to a nonzero new eigenform at a proper
divisor of $`N$` whose eigenvalues match $`f$`'s, then shows $`f$` would be old — a
contradiction. Hence $`g^\flat = 0$` and $`g = c f$`.
:::

## Atkin–Lehner theory and the old/new decomposition

:::theorem "old-new-decomposition"
*Orthogonal old/new decomposition.*
The cusp space at level $`\Gamma_1(N)` decomposes as an internal direct sum,
$$`
  S_k(\Gamma_1(N)) \;=\; S_k^\flat(N) \;\oplus\; S_k^\sharp(N),
`
where $`S_k^\flat(N)$` is the old subspace and $`S_k^\sharp(N) = (S_k^\flat(N))^\perp$` is
its Petersson orthogonal complement (the new subspace).
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "cusp-form"}[] {uses "eigenform-newform"}[]
:::

:::proof "old-new-decomposition"
Trivial intersection $`S_k^\flat(N) \cap S_k^\sharp(N) = 0$` follows immediately from
positive-definiteness of the Petersson inner product: a form lying in both a subspace and its
orthogonal complement is orthogonal to itself, hence has Petersson norm zero, hence is zero.
The spanning property holds on any finite-dimensional space carrying a nondegenerate reflexive
form: a subspace and its orthogonal complement are always complementary. The Petersson inner
product is nondegenerate and positive-definite on $`S_k(\Gamma_1(N))$` ({uses "cusp-form"}[]),
so these abstract linear-algebra facts apply, giving the direct-sum decomposition.
:::

:::theorem "atkin-lehner-main-lemma"
*Atkin–Lehner Main Lemma (Diamond–Shurman 5.7.1 / Miyake 4.6.8).*
Let $`f \in S_k(\Gamma_1(N))$` be a cusp form whose Fourier coefficients vanish at all indices
coprime to the level:
$$`
  a_n(f) \;=\; 0 \quad \text{for all } n \ge 1 \text{ with } \gcd(n,N) = 1.
`
Then $`f$` is an oldform: $`f \in S_k^\flat(N)$`.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (in progress — the Petersson adjoint input is not yet available).

Depends on: {uses "eigenform-newform"}[] {uses "old-new-decomposition"}[] {uses "q-expansion"}[]
:::

:::proof "atkin-lehner-main-lemma"
Split $`f = f^\flat + f^\sharp$` and aim to show $`f^\sharp = 0$`. Subtracting the old part
$`f^\flat$` does not affect coefficients at indices coprime to $`N$` (level-raising only inserts
factors $`\ell > 1$` dividing $`N$`), so $`a_n(f^\sharp) = 0$` for all $`(n,N) = 1$` as well.
To show $`f^\sharp$` is orthogonal to the whole new subspace, fix an eigenform $`g \in S_k^\sharp(N)$`.
The Petersson adjoint relation $`\langle T(n) h, g \rangle = \overline{\lambda_n(g)} \langle h, g \rangle$`
lets one move $`T(n)$` across the inner product; since $`a_n(f^\sharp) = 0$` and the eigenvalue
of $`T(n)$` on $`f^\sharp$` at index $`1$` equals $`a_n(f^\sharp)$` via the Miyake identity
({uses "eigenvalue-equals-fourier-coeff"}[]), a nonzero eigenvalue $`\lambda_n(g)$` forces
$`\langle f^\sharp, g \rangle = 0$`. Positivity then gives $`f^\sharp = 0$`.
:::

## The Shimura surjection

:::theorem "shimura-surjection"
*Shimura surjection $`R(\Gamma, \Delta) \twoheadrightarrow R(\Gamma_0(N), \Delta_0(N))$` (Shimura 3.35).*
Write $`\Gamma = \mathrm{SL}_2(\mathbb{Z})$` and let $`\Delta$` be the monoid of integral
$`2 \times 2$` matrices with positive determinant. There is a surjective ring homomorphism
$$`
  \varphi \;\colon\; R(\Gamma, \Delta) \;\twoheadrightarrow\; R(\Gamma_0(N), \Delta_0(N))
`
from the full $`\mathrm{GL}_2$` Hecke ring to the level-$`N$` congruence Hecke ring. Every
element of the congruence ring is the image of a full-level Hecke operator.
Formalised in [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms) on branch `hecke-ring` (sorry-free).

Depends on: {uses "hecke-algebra-action"}[]
:::

:::proof "shimura-surjection"
The proof uses the polynomial presentation of the full Hecke ring. Over the prime generators
$`X_{p,0}, X_{p,1}$` there is a surjection
$`\pi \colon \mathbb{Z}[X_{p,k}] \twoheadrightarrow R(\Gamma,\Delta)$` sending each
generator to the corresponding prime-power Hecke class. Define a second homomorphism
$`\psi$` on the same generators, sending $`X_{p,0}$` to the class of
$`\operatorname{diag}(1,p)$` and $`X_{p,1}$` to $`\operatorname{diag}(p,p)$` for $`p \nmid N$`
(zero otherwise). Since the prime-power generators are algebraically independent, $`\pi$` is
injective and $`\psi$` factors through $`R(\Gamma,\Delta)$`, producing $`\varphi$`. Surjectivity
holds because every basis class of $`R(\Gamma_0(N), \Delta_0(N))$` admits a diagonal
representative $`\operatorname{diag}(a,b)$` with $`a \mid b$` and $`\gcd(a,N) = 1$`, and the
identification of level-$`N$` classes with coprime-determinant full-level classes (Shimura
Prop. 3.31) together with multiplicativity of the bad classes (Shimura Prop. 3.33) reduces
every such class to a product of prime-power images of $`\psi$`.
:::

# Phase 3 (ModFormDims — external project)

The node below is drawn from the **ModFormDims** project
([`https://github.com/CBirkbeck/ModFormDims`](https://github.com/CBirkbeck/ModFormDims)),
which extends the modular-forms library with Petersson-product tools, $`q$`-expansion
comparisons, and preliminary dimension-formula infrastructure for congruence subgroups.

## Dimension formula and $`q$`-expansion comparison

:::theorem "neg-weight-rank-zero"
*Modular forms of negative weight vanish.*
For any integer $`k < 0$`, the space $`M_k(\mathrm{SL}_2(\mathbb{Z}))$` is zero:
$$`
  \operatorname{rank}_{\mathbb{C}} M_k(\mathrm{SL}_2(\mathbb{Z})) \;=\; 0.
`
Equivalently, every modular form of negative weight and level $`\Gamma(1)$` is identically
zero.
Formalised in [`ModFormDims`](https://github.com/CBirkbeck/ModFormDims) (sorry-free).

Depends on: {uses "modular-form"}[] {uses "q-expansion"}[]
:::

:::proof "neg-weight-rank-zero"
By the maximum modulus principle applied to the cusp function. For $`k \le 0$` and any
modular form $`f$` of weight $`k$` for $`\Gamma(1)$`, the function $`|f(z)| \cdot \operatorname{Im}(z)^{k/2}$`
is $`\mathrm{SL}_2(\mathbb{Z})$`-invariant; the reduction theory for the fundamental domain shows
there exists a translate of $`z$` to the standard fundamental domain $`\mathcal{D}$`
with $`\operatorname{Im}(z') \ge \sqrt{3}/2$`. The $`q$`-expansion of $`f$`
({uses "q-expansion"}[]) expresses $`f$` through the cusp function $`F(q)$` satisfying
$`f(z) = F(e^{2\pi i z})$`. Since $`f$` is bounded at the cusp, $`F$` extends holomorphically
to the closed unit disc. The maximum modulus principle forces $`F$` to be constant; for $`k < 0$`
the slash-invariance forces that constant to be zero ({uses "slash-action"}[]), giving $`f = 0$`.
The rank-zero statement follows.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib
pull requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing
at the live PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the Mathlib-backed modular-forms
nodes of this chapter via `{uses}` edges, and should be re-pointed to `(lean := …)` once the
corresponding PR merges.

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
$`f \in M_k(\Gamma)` a modular form ({uses "modular-form"}[]) of weight $`k`. If the
$`q`-expansion ({uses "q-expansion"}[]) of $`f` at the cusp $`\infty` vanishes to order
exceeding the *Sturm bound*
$$`B(\Gamma, k) \;=\; \left\lfloor \frac{k}{12}\,[\mathrm{SL}_2(\mathbb{Z}) : \Gamma] \right\rfloor,`
i.e. $`a_n(f) = 0` for all $`n \le B(\Gamma, k)`, then $`f = 0`. Consequently two modular forms
of weight $`k` and level $`\Gamma` agreeing up to the Sturm bound are equal.

The bound is a direct consequence of the valence (weight) formula ({uses "valence-formula"}[]):
a nonzero form of weight $`k` cannot vanish at $`\infty` to order exceeding its total allowed
order of vanishing $`\tfrac{k}{12}[\mathrm{SL}_2 : \Gamma]`. PR #39000 establishes the bound for
finite-index subgroups, the standard finite check for equality of modular forms and Hecke
eigensystems.
In review — [mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000).
:::

:::definition "serre-derivative" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/36963")
For an integer $`k`, the *Serre derivative* $`\vartheta_k` sends a weight-$`k` modular form
({uses "modular-form"}[]) to a weight-$`(k+2)` modular form by correcting the naive $`q`-derivative
with the quasimodular Eisenstein series $`E_2`:
$$`\vartheta_k f \;=\; q\,\frac{d f}{d q} \;-\; \frac{k}{12}\, E_2\, f, \qquad q = e^{2\pi i z},`
where $`E_2(z) = 1 - 24\sum_{n \ge 1} \sigma_1(n) q^n` ({uses "eisenstein-series"}[]). Although
$`q\,\tfrac{df}{dq}` and $`E_2 f` are each only quasimodular, the $`E_2`-correction cancels the
anomaly so that $`\vartheta_k f` transforms with weight $`k + 2` under the slash action
({uses "slash-action"}[]); on $`q`-expansions ({uses "q-expansion"}[]) it acts as
$`\sum a_n q^n \mapsto \sum n\,a_n q^n` plus the $`E_2`-term.

PR #36963 sets up the $`\mathrm{SL}_2` action on the relevant function spaces and defines the
Serre derivative, the basic weight-raising operator underlying the Rankin–Cohen brackets and the
ring of quasimodular forms.
In review — [mathlib PR #36963](https://github.com/leanprover-community/mathlib4/pull/36963).
:::
