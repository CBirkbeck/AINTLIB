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
where $`c, d` are the bottom-row entries of $`g`. This extends to an action on functions
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
The slash-invariance under $`\Gamma(N)` follows from the fact that the set of coprime pairs
congruent to $`a` mod $`N` is preserved under the row-vector action of $`\Gamma(N)`
({uses "slash-invariant-form"}[]). Holomorphicity on $`\mathbb{H}` comes from the uniform
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
which converts the defining sum over coprime pairs into a sum of divisor-power sums via the
Riemann zeta factorisation. Specifically, summing over all integer pairs (not just coprime ones)
and factoring out the zeta value at $`k`, then applying Möbius inversion, yields the coefficient
formula. The stated form follows from the value $`\zeta(k) = -(2\pi i)^k B_k / (2 \cdot k!)`.
:::

# The discriminant modular form

:::definition "modular-discriminant" (lean := "CuspForm.discriminant")
The *modular discriminant* $`\Delta` is the unique (up to scalar) nonzero cusp form of weight $`12`
and level $`1`. It is given explicitly by the Dedekind eta function:
$$`\Delta(z) \;=\; e^{2\pi i z} \prod_{n=1}^{\infty} (1 - e^{2\pi i n z})^{24}
              \;=\; \eta(z)^{24},`
where $`\eta(z) = e^{\pi i z/12} \prod_{n=1}^{\infty}(1 - e^{2\pi i n z})` is the Dedekind
eta function. In particular $`\Delta` is a cusp form in $`S_{12}(\mathrm{SL}_2(\mathbb{Z}))`.
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
