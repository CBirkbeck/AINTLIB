import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Hecke pairs and double cosets" =>

The basic combinatorial datum of Hecke theory is a *Hecke pair* $`(G,H,\Delta)`, from
which one builds two free $`\mathbb{Z}`-modules: one on the double cosets
$`H\backslash\Delta/H`, which will carry the Hecke ring structure, and one on the left
cosets $`Hg`, on which that ring will act. This chapter records these definitions together
with the structural fact, following \[Sh, §3.1\], that each double coset $`HgH` is a finite
disjoint union of left cosets.

:::definition "hecke-pair" (lean := "HeckeRing.HeckePair")
*Hecke pair.*
A *Hecke pair* $`(G,H,\Delta)` consists of a group $`G`, a subgroup $`H` of $`G`, and a
submonoid $`\Delta` of $`G` satisfying $`H\le\Delta` and $`\Delta\le\operatorname{Comm}(H)`,
where $`\operatorname{Comm}(H)` is the commensurator of $`H` in $`G`. Equivalently, every
$`g\in\Delta` is commensurable with the identity in the sense that
$`H\cap gHg^{-1}` has finite index in both $`H` and $`gHg^{-1}`.
:::

:::definition "hecke-coset" (lean := "HeckeRing.HeckeCoset")
*Double cosets.*
For a Hecke pair $`(G,H,\Delta)`, the set of *double cosets* $`H\backslash\Delta/H` is
the quotient of $`\Delta` by the equivalence relation that identifies $`g` and $`g'` whenever
$`HgH=Hg'H`, that is, whenever $`g'=h_1 g h_2` for some $`h_1,h_2\in H`. We write a typical
double coset as $`HgH`.

Depends on: {uses "hecke-pair"}[]
:::

:::definition "hecke-left-coset" (lean := "HeckeRing.HeckeLeftCoset")
*Left cosets in $`\Delta`.*
For a Hecke pair $`(G,H,\Delta)`, the set of *left cosets* is the quotient of $`\Delta`
by the equivalence relation that identifies $`g` and $`g'` whenever $`Hg=Hg'`. We write a
typical left coset as $`Hg`.

Depends on: {uses "hecke-pair"}[]
:::

:::lemma_ "dc-eq-iUnion-lc" (lean := "HeckeRing.DoubleCoset.doubleCoset_eq_iUnion_leftCosets")
*Double coset as a union of left cosets.*
Let $`g\in\Delta`. Then the double coset $`HgH` is the union
$$`
  HgH \;=\; \bigcup_{i\,\in\, H/(H\cap gHg^{-1})} H\,(g_i\,g),
`
where $`i` ranges over the coset space $`H/(H\cap gHg^{-1})` and $`g_i\in H` is a
representative of $`i`. In particular $`HgH` is a disjoint union of finitely many left
cosets of $`H`.

Depends on: {uses "hecke-pair"}[]
:::

:::proof "dc-eq-iUnion-lc"
Writing $`K=H\cap gHg^{-1}`, the subgroup $`H` is the disjoint union of the left cosets
$`g_i K` as $`i` ranges over $`H/K`. Multiplying this decomposition on the right by the set
$`gHg^{-1}` and using that $`K` stabilises $`gHg^{-1}` under left multiplication, one obtains
$`H\,gHg^{-1}=\bigcup_i g_i\,gHg^{-1}`; cancelling $`g^{-1}` on the right and translating by
$`g` turns the left-hand side into $`HgH` and each summand into the left coset $`H(g_i g)`.
Commensurability of $`g` with the identity, which holds because
$`\Delta\le\operatorname{Comm}(H)`, makes the index $`[H:H\cap gHg^{-1}]` finite, so the
union is finite, and distinct cosets $`g_iK` give distinct left cosets $`H(g_i g)`, whence
the union is disjoint.

Uses: {uses "hecke-pair"}[]
:::

:::definition "decomp-quot" (lean := "HeckeRing.decompQuot")
*Left-coset index of a double coset.*
For $`g\in\Delta`, the *decomposition index set* of $`g` is the coset space
$`H/(H\cap gHg^{-1})`, which indexes the left cosets appearing in the decomposition
$`HgH=\bigsqcup_i H(g_i g)` of {bpref "dc-eq-iUnion-lc"}[]. Since
$`\Delta\le\operatorname{Comm}(H)`, this index set is finite.

Depends on: {uses "hecke-pair"}[] {uses "dc-eq-iUnion-lc"}[]
:::

:::definition "hecke-ring-carrier" (lean := "HeckeRing.𝕋")
*Hecke ring, underlying module.*
Let $`(G,H,\Delta)` be a Hecke pair. The *Hecke ring*
$`\mathbb{T}=\mathcal{H}(G,H,\Delta)` is, as a $`\mathbb{Z}`-module, the free
$`\mathbb{Z}`-module on the set of double cosets $`H\backslash\Delta/H`; that is, the
$`\mathbb{Z}`-valued functions on $`H\backslash\Delta/H` of finite support. Its
multiplication is introduced in the next chapter.

Depends on: {uses "hecke-coset"}[]
:::

:::definition "hecke-module" (lean := "HeckeRing.HeckeModule")
*Hecke module.*
Let $`(G,H,\Delta)` be a Hecke pair. The *Hecke module* is the free
$`\mathbb{Z}`-module on the set of left cosets $`Hg`; that is, the $`\mathbb{Z}`-valued
functions of finite support on the set of left cosets. This is the module on which the
Hecke ring $`\mathbb{T}` acts.

Depends on: {uses "hecke-left-coset"}[]
:::
