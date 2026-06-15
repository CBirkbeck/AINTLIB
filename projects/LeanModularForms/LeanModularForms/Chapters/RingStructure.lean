import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Module
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Hecke ring structure" =>

Fix a Hecke pair $`(G,H,\Delta)`. This chapter equips the free $`\mathbb{Z}`-module
$`\mathbb{T}` on the double cosets $`H\backslash\Delta/H` with its convolution product,
whose structure constants are Shimura's coset-overlap multiplicities, and assembles the
result into a unital associative ring \[Sh, §3.1\].

:::definition "mulMap" (lean := "HeckeRing.mulMap")
*Product map on representatives.*
Let $`g,g'\in\Delta`, and choose left-coset representatives so that
$`HgH=\bigsqcup_i Hg_i` and $`Hg'H=\bigsqcup_j Hg'_j`. The *product map* sends a pair
of representatives $`(g_i,g'_j)` to the double coset $`H(g_i\,g'_j)H` of their product.

Depends on: {uses "decomp-quot"}[] {uses "hecke-coset"}[]
:::

:::definition "hecke-multiplicity" (lean := "HeckeRing.heckeMultiplicity")
*Shimura's multiplicity.*
For $`g,g',d\in\Delta` define the *multiplicity* $`\mu(g,g';d)` to be the number of
pairs of left-coset representatives $`(g_i,g'_j)`, drawn from the decompositions
$`HgH=\bigsqcup_i Hg_i` and $`Hg'H=\bigsqcup_j Hg'_j`, that satisfy
$`g_i\,g'_j\,H=d\,H`. This is the structure constant of the Hecke ring
\[Sh, §3.1, Prop 3.2\].

Depends on: {uses "decomp-quot"}[]
:::

:::definition "m-finsupp" (lean := "HeckeRing.m")
*Structure-constant coefficients.*
For $`g,g'\in\Delta` let $`m(g,g')` be the finitely-supported function on double cosets
$`d\mapsto\mu(g,g';d)`. Only finitely many double cosets occur as $`H(g_i\,g'_j)H`, so this
is well defined; it records the coefficients of the product of the two basis elements.

Depends on: {uses "hecke-multiplicity"}[]
:::

:::definition "T-single" (lean := "HeckeRing.T_single")
*Basis element.*
For a double coset $`D=HgH` and a coefficient $`b`, let $`T_D` (also written $`[D]`) be the
corresponding basis element of $`\mathbb{T}`: the function on double cosets taking the
value $`b` at $`D` and $`0` elsewhere. The elements $`T_D` with $`b=1` form a $`\mathbb{Z}`-basis
of $`\mathbb{T}`.

Depends on: {uses "hecke-ring-carrier"}[]
:::

:::lemma_ "mul-def" (lean := "HeckeRing.mul_def")
*Convolution product.*
For $`f,g\in\mathbb{T}` the product is the convolution
$$`
  f\cdot g \;=\; \sum_{D_1}\sum_{D_2} f(D_1)\,g(D_2)\,\bigl(T_{D_1}\cdot T_{D_2}\bigr),
`
the sums running over the (finite) supports of $`f` and $`g`, with each basis product
$`T_{D_1}\cdot T_{D_2}` expanded through the structure constants $`\mu(D_1,D_2;\,\cdot\,)`.

Depends on: {uses "hecke-multiplicity"}[] {uses "T-single"}[]
:::

:::proof "mul-def"
Both $`f` and $`g` are finite $`\mathbb{Z}`-linear combinations of basis elements. The
product is defined to be $`\mathbb{Z}`-bilinear, so it distributes over these
combinations, and the displayed double sum is exactly its unfolding on the supports. The
inner term $`T_{D_1}\cdot T_{D_2}` is, by definition, the coefficient function
$`m(D_1,D_2)` collecting the multiplicities $`\mu(D_1,D_2;d)`. Hence the identity holds by
definition of the convolution.

Uses: {uses "hecke-multiplicity"}[] {uses "T-single"}[]
:::

:::lemma_ "T-single-mul" (lean := "HeckeRing.T_single_mul_T_single")
*Product of basis elements.*
For double cosets $`D_1,D_2`,
$$`
  [D_1]\cdot[D_2] \;=\; \sum_{d} \mu(D_1,D_2;d)\,[d],
`
the sum running over double cosets $`d`, with at most finitely many nonzero terms. More
generally, for coefficients $`a,b` one has
$`T_{D_1}\cdot T_{D_2}=a\,b\cdot m(D_1,D_2)`.

Depends on: {uses "T-single"}[] {uses "hecke-multiplicity"}[] {uses "m-finsupp"}[]
:::

:::proof "T-single-mul"
Apply the convolution formula of {bpref "mul-def"}[] to $`f=[D_1]` and $`g=[D_2]`. Each
is supported on a single double coset, so the double sum collapses to the single term
$`a\,b` times the coefficient function $`m(D_1,D_2)`. By definition of
{bpref "m-finsupp"}[] the value of $`m(D_1,D_2)` at $`d` is the multiplicity
$`\mu(D_1,D_2;d)`, giving the displayed expansion.

Uses: {uses "T-single"}[] {uses "hecke-multiplicity"}[] {uses "m-finsupp"}[]
:::

:::lemma_ "smul-eq-sum" (lean := "HeckeRing.smul_eq_sum")
*Module action as a coset sum.*
The Hecke ring $`\mathbb{T}` acts on the left-coset module. For $`T\in\mathbb{T}` and a
formal sum $`\nu` of left cosets, the action is the double sum
$$`
  T\cdot\nu \;=\; \sum_{D_1}\sum_{\beta} T(D_1)\,\nu(\beta)
    \sum_{i} \bigl[\,g_i\,\beta\,\bigr],
`
where $`D_1` ranges over the support of $`T`, $`\beta` over the support of $`\nu`, and $`g_i`
over left-coset representatives of $`D_1`, each summand $`[\,g_i\,\beta\,]` being the left
coset obtained by translating $`\beta` by the representative $`g_i`.

Depends on: {uses "hecke-module"}[] {uses "decomp-quot"}[]
:::

:::proof "smul-eq-sum"
This is the unfolding of the definition of the action. The action is $`\mathbb{Z}`-bilinear
in $`T` and $`\nu`, so it distributes over their basis expansions; on a pair of basis
elements it sends $`([D_1],[\beta])` to the sum of the left cosets $`[\,g_i\,\beta\,]` over
the representatives $`g_i` of $`D_1`, which is precisely the displayed orbit sum.

Uses: {uses "hecke-module"}[] {uses "decomp-quot"}[]
:::

:::lemma_ "mul-assoc" (lean := "HeckeRing.mul_assoc_𝕋")
*Associativity.*
The product on $`\mathbb{T}` is associative: $`(f\cdot g)\cdot h=f\cdot(g\cdot h)` for all
$`f,g,h\in\mathbb{T}`.

Depends on: {uses "T-single-mul"}[] {uses "smul-eq-sum"}[]
:::

:::proof "mul-assoc"
Associativity is deduced from the action of $`\mathbb{T}` on the left-coset module of
{bpref "smul-eq-sum"}[]. That action is a faithful scalar tower: ring multiplication
is compatible with the module action, so $`((f\cdot g)\cdot h)\cdot\nu` and
$`(f\cdot(g\cdot h))\cdot\nu` agree for every formal sum $`\nu` of left cosets. The two
agree because each amounts to acting successively by $`h`, then $`g`, then $`f`, a
re-indexing of the triple coset sum that is manifestly independent of bracketing. By
faithfulness of the action, the two ring elements are equal. Concretely on basis elements
this is the double-coset counting identity behind {bpref "T-single-mul"}[].
:::

:::lemma_ "one-def" (lean := "HeckeRing.one_def")
*Identity element.*
The multiplicative identity of $`\mathbb{T}` is $`[H]=T_{[H]}`, the basis element attached
to the trivial double coset $`H=H\cdot 1\cdot H` with coefficient $`1`.

Depends on: {uses "T-single"}[] {uses "hecke-coset"}[]
:::

:::proof "one-def"
The trivial double coset $`H` has the single left coset $`H` as its decomposition, so for
any double coset $`D` the multiplicities $`\mu(H,D;\,\cdot\,)` and $`\mu(D,H;\,\cdot\,)` are
$`1` at $`D` and $`0` elsewhere. By {bpref "T-single-mul"}[] this gives
$`[H]\cdot[D]=[D]=[D]\cdot[H]`, and bilinearity ({bpref "mul-def"}[]) extends the
two-sided identity property from basis elements to all of $`\mathbb{T}`.
:::

:::theorem "hecke-ring" (lean := "HeckeRing.instRing")
*The Hecke ring.*
With the convolution product and identity above, $`\mathbb{T}` is a unital associative ring
(indeed a $`\mathbb{Z}`-algebra) \[Sh, §3.1\].

Depends on: {uses "mul-def"}[] {uses "mul-assoc"}[] {uses "one-def"}[]
:::

:::proof "hecke-ring"
The underlying additive group is the free $`\mathbb{Z}`-module on double cosets, hence an
abelian group. The convolution product of {bpref "mul-def"}[] is
$`\mathbb{Z}`-bilinear by construction, so distributivity over addition and compatibility
with integer scaling are immediate. Associativity is {bpref "mul-assoc"}[], and
{bpref "one-def"}[] provides a two-sided multiplicative identity. Together these are
exactly the ring axioms.
:::
