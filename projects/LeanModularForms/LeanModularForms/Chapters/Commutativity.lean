import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Commutativity
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Commutativity via anti-involutions" =>

A Hecke pair may carry an order-reversing symmetry that fixes each of its double cosets; when
it does, the structure constants are symmetric and the Hecke ring is commutative. Applying this
to the transpose on the arithmetic $`\mathrm{GL}_n` pair shows that the $`\mathrm{GL}_n` Hecke
algebra is commutative.

:::definition "anti-involution" (lean := "HeckeRing.AntiInvolution")
Let $`(G,H,\Delta)` be a Hecke pair. An *anti-involution* of $`(G,H,\Delta)` is an
anti-homomorphism $`g\mapsto\bar g` of $`G` that is involutive and preserves the pair. Explicitly,
it satisfies
$$`
  \bar{\bar g}=g,\qquad \overline{ab}=\bar b\,\bar a,
`
and maps $`H` into $`H` and $`\Delta` into $`\Delta`, that is, $`\bar g\in H` whenever $`g\in H` and
$`\bar g\in\Delta` whenever $`g\in\Delta` \[Sh, §3.1\].

Depends on: {uses "hecke-pair"}[]
:::

:::definition "onHeckeCoset" (lean := "HeckeRing.AntiInvolution.onHeckeCoset")
Let $`g\mapsto\bar g` be an anti-involution of the Hecke pair $`(G,H,\Delta)`. It induces a map on
the set $`H\backslash\Delta/H` of double cosets,
$$`
  HgH \;\longmapsto\; H\bar gH .
`
This is well defined: since the anti-involution reverses products and preserves $`H`, two
representatives of the same double coset have barred images lying in a single double coset, so
the assignment depends only on $`HgH`. The induced map is again involutive \[Sh, §3.1\].

Depends on: {uses "anti-involution"}[] {uses "hecke-coset"}[]
:::

:::theorem "mul-comm-of-ai" (lean := "HeckeRing.AntiInvolution.mul_comm_of_antiInvolution")
Let $`g\mapsto\bar g` be an anti-involution of the Hecke pair $`(G,H,\Delta)` whose induced map on
double cosets fixes every double coset, that is, $`H\bar gH=HgH` for all $`g\in\Delta`. Then the
Hecke ring $`\mathbb{T}` is commutative: for all $`f,g\in\mathbb{T}`,
$$`
  f\cdot g \;=\; g\cdot f .
`

Depends on: {uses "onHeckeCoset"}[] {uses "hecke-multiplicity"}[] {uses "hecke-ring"}[]
:::

:::proof "mul-comm-of-ai"
Since the product on $`\mathbb{T}` is $`\mathbb{Z}`-bilinear, it suffices to prove the identity on
a pair of basis elements $`[D_1]` and $`[D_2]`, where the product is governed by the structure
constants $`\mu(D_1,D_2;d)`. The claim therefore reduces to the symmetry
$$`
  \mu(D_1,D_2;d)\;=\;\mu(D_2,D_1;d)
`
for every double coset $`d`. To see this, apply the anti-involution to a left-coset
decomposition $`D_1D_2=\bigsqcup_i Hg_i`. Because $`g\mapsto\bar g` reverses products, it carries
this decomposition to one of $`D_2D_1`; because it fixes each double coset, the double coset of
each $`g_i` is preserved. Tracking the left coset of a fixed representative $`d` under this
correspondence gives a bijection between the pairs of representatives counted by
$`\mu(D_1,D_2;d)` and those counted by $`\mu(D_2,D_1;d)`, so the two multiplicities agree. Hence
the products $`[D_1]\cdot[D_2]` and $`[D_2]\cdot[D_1]` coincide on every basis pair, and
$`\mathbb{T}` is commutative \[Sh, §3.1, Prop. 3.8\].

Uses: {uses "onHeckeCoset"}[] {uses "hecke-multiplicity"}[] {uses "hecke-ring"}[]
:::

:::definition "commring-of-ai" (lean := "HeckeRing.instCommRing_of_antiInvolution")
Given an anti-involution of the Hecke pair $`(G,H,\Delta)` whose induced map fixes every double
coset, the resulting commutativity of multiplication upgrades the ring structure on $`\mathbb{T}`
to a *commutative ring* structure, obtained from the ring structure on $`\mathbb{T}` by
supplying the symmetry $`f\cdot g=g\cdot f` from {bpref "mul-comm-of-ai"}[].

Depends on: {uses "mul-comm-of-ai"}[] {uses "hecke-ring"}[]
:::

:::definition "gl-pair-ai" (lean := "HeckeRing.GLn.GL_pair_antiInvolution")
For the arithmetic $`\mathrm{GL}_n` Hecke pair, the *transpose* $`g\mapsto{}^{t}g` is an
anti-involution. It reverses products, since $`{}^{t}(ab)={}^{t}b\,{}^{t}a`, and is involutive,
since $`{}^{t}({}^{t}g)=g`. Moreover it preserves the pair: transposing a matrix in
$`\mathrm{SL}_n(\mathbb{Z})` stays in $`\mathrm{SL}_n(\mathbb{Z})`, and transposing a
positive-determinant integral matrix preserves both integrality of the entries and the value of
the determinant, so the positive-determinant integer monoid is preserved as well \[Sh, §3.1\].

Depends on: {uses "anti-involution"}[] {uses "GL-pair"}[]
:::

:::lemma_ "gl-pair-fix" (lean := "HeckeRing.GLn.GL_pair_onHeckeCoset_eq")
The transpose fixes every double coset of the arithmetic $`\mathrm{GL}_n` pair: for all $`g`,
$$`
  H\,{}^{t}gH \;=\; HgH .
`

Depends on: {uses "gl-pair-ai"}[] {uses "onHeckeCoset"}[]
:::

:::proof "gl-pair-fix"
Every double coset has a diagonal representative, given by the elementary divisors of $`g` via
the Smith normal form. A diagonal matrix is equal to its own transpose, so the transpose fixes
this representative and therefore fixes the whole double coset. Equivalently, a matrix and its
transpose share the same elementary divisors, hence lie in the same double coset \[Sh, §3.1\].

Uses: {uses "gl-pair-ai"}[] {uses "onHeckeCoset"}[]
:::

:::theorem "commring-hecke-algebra" (lean := "HeckeRing.GLn.instCommRing_HeckeAlgebra")
The $`\mathrm{GL}_n` Hecke algebra $`\mathcal{H}_n` is commutative.

Depends on: {uses "commring-of-ai"}[] {uses "gl-pair-ai"}[] {uses "gl-pair-fix"}[] {uses "hecke-algebra"}[]
:::

:::proof "commring-hecke-algebra"
The transpose is an anti-involution of the arithmetic $`\mathrm{GL}_n` pair
({bpref "gl-pair-ai"}[]) whose induced map fixes every double coset
({bpref "gl-pair-fix"}[]). Applying the commutativity criterion of
{bpref "commring-of-ai"}[] to this anti-involution endows $`\mathcal{H}_n` with a
commutative ring structure \[Sh, §3.1, Prop. 3.8\].

Uses: {uses "commring-of-ai"}[] {uses "gl-pair-ai"}[] {uses "gl-pair-fix"}[] {uses "hecke-algebra"}[]
:::
