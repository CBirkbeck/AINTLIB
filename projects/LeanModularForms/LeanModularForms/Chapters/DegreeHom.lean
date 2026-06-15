import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Degree

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The degree homomorphism" =>

Each double coset splits into finitely many left cosets, and counting them defines a ring
homomorphism from the Hecke ring to $`\mathbb{Z}` that records the size of each operator.

:::definition "hecke-coset-deg" (lean := "HeckeRing.HeckeCoset_deg")
Let $`(G,H,\Delta)` be a Hecke pair and let $`D=HgH` be a double coset. Writing
$`D=\bigsqcup_i Hg_i` for its decomposition into finitely many left cosets, the
*degree* of $`D` is
$$`
  \deg D \;=\; [\,H : H\cap gHg^{-1}\,],
`
the number of left cosets $`Hg_i` comprising $`D`. Depends on: {uses "hecke-coset"}[] {uses "decomp-quot"}[]
:::

:::lemma_ "smulOrbit-card" (lean := "HeckeRing.smulOrbit_card")
Fix a double coset $`D=HgH` with left-coset representatives $`g_i`, and let $`H\beta` be any
left coset with $`\beta\in\Delta`. Then the orbit
$$`
  \{\,Hg_i\beta : i\,\}
`
has cardinality equal to $`\deg D`. Depends on: {uses "hecke-coset-deg"}[]
:::

:::proof "smulOrbit-card"
The map sending the $`i`-th representative to the left coset $`H(\beta g_i g)` is a
surjection onto the orbit by construction, so it suffices to show it is injective. If two
representatives produced the same coset, then after left-cancelling $`\beta` the
corresponding cosets $`Hg_i g` and $`Hg_j g` would meet, hence coincide; this contradicts
the fact that distinct representatives index distinct left cosets in the decomposition of
$`D`. Thus the orbit has exactly as many elements as there are left cosets in $`D`, namely
$`\deg D` \[Sh, §3.1\]. Uses: {uses "hecke-coset-deg"}[]
:::

:::definition "deg" (lean := "HeckeRing.deg")
The *degree homomorphism* is the ring homomorphism
$$`
  \deg : \mathbb{T} \longrightarrow \mathbb{Z}
`
determined by sending each basis element $`[D]` to $`\deg D` and extending
$`\mathbb{Z}`-linearly; that is, $`\deg\bigl(\sum_D a_D\,[D]\bigr)=\sum_D a_D\,\deg D`. It
sends the identity to $`1`, is additive, and is multiplicative
\[Sh, §3.1, Prop. 3.3\]. Depends on: {uses "hecke-coset-deg"}[] {uses "T-single"}[] {uses "hecke-ring"}[]
:::

:::lemma_ "deg-mul" (lean := "HeckeRing.deg_mul")
For all $`f,g` in the Hecke ring,
$$`
  \deg(f\cdot g)=\deg(f)\,\deg(g).
`
Depends on: {uses "deg"}[] {uses "smulOrbit-card"}[] {uses "hecke-multiplicity"}[]
:::

:::proof "deg-mul"
Since $`\deg` is additive, it suffices to verify multiplicativity on a pair of basis
elements $`[D_1]` and $`[D_2]`. Expanding the product in the Hecke ring via the structure
constants gives $`[D_1]\cdot[D_2]=\sum_d \mu(D_1,D_2;d)\,[d]`, so by definition
$$`
  \deg\bigl([D_1]\cdot[D_2]\bigr)=\sum_d \mu(D_1,D_2;d)\,\deg d.
`
The right-hand side counts, with multiplicity, the left cosets occurring in the product
double coset. Grouping these by the right action of $`D_2` on the left cosets of $`D_1` and
applying the orbit-size identity, each orbit contributes exactly $`\deg D_2` cosets, and
there are $`\deg D_1` orbits; hence the total is $`\deg D_1\,\deg D_2` \[Sh, §3.1\]. Uses: {uses "deg"}[] {uses "smulOrbit-card"}[] {uses "hecke-multiplicity"}[]
:::
