import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms
import LeanModularFormsBlueprint.Refs
import LeanModularFormsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The valence formula" =>

We now state the headline result of the modular side of the project: the
classical valence formula for weight-$`k` modular forms on
$`\operatorname{SL}_2(\mathbb{Z})`. The argument follows the textbook proof of
Diamond–Shurman, Theorem 3.1.1: take the logarithmic derivative $`f'/f` of $`f`
around the fundamental-domain boundary at height $`H`, identify each residue with
an order of vanishing, and match the resulting weighted sum against $`k/12` via
the Hungerbühler–Wasem residue theorem and modular invariance.

:::theorem "valence-orbit-sum-of-pvChain" (lean := "valence_formula_orbit_sum_of_pvChain")
Let $`k \in \mathbb{Z}` and let $`f` be a weight-$`k` modular form on
$`\operatorname{SL}_2(\mathbb{Z})` ($`f \in M_k(\Gamma(1))`). Let
$`S \subseteq \mathcal{D}` be a finite subset of the standard fundamental domain
such that every order-non-zero point of $`f` in $`\mathcal{D}` lies in $`S`.
Assume there exists a height $`H` and a full winding-data bundle $`D` on
$`\partial \mathcal{D}_H` (i.e. the interior winding number $`-1`, the elliptic
winding numbers $`-\tfrac{1}{2}, -\tfrac{1}{6}, -\tfrac{1}{6}` at
$`i, \rho, \rho+1` respectively, and the smooth-boundary winding $`-\tfrac{1}{2}`
at every other on-curve point of $`\partial \mathcal{D}_H`) for which every
$`s \in S` has $`\operatorname{Im}(s) < H` and the PV chain identity
$$`\sum_{s \in S} \operatorname{gWN}\!\bigl(D.\mathrm{boundary},\, s\bigr) \cdot \operatorname{ord}_{s}(f) \;=\; -\bigl(k/12 - \operatorname{ord}_\infty(f)\bigr)`
holds. Then
$$`\operatorname{ord}_\infty(f) + \tfrac{1}{2}\,\operatorname{ord}_{i}(f) + \tfrac{1}{3}\,\operatorname{ord}_{\rho}(f) + \sum_{s \in \mathrm{INT}}\operatorname{ord}_{s}(f) + \sum_{s \in \mathrm{sLeftVert}} \operatorname{ord}_{s}(f) + \sum_{s \in \mathrm{LeftArc}} \operatorname{ord}_{s}(f) = \frac{k}{12},`
where

* $`\mathrm{INT}` is the subset of $`S` of strictly interior points
  (non-elliptic, $`\|s\| > 1`, $`|\operatorname{Re} s| < 1/2`);
* $`\mathrm{sLeftVert}` is the canonical-rep subset of $`S` on the left vertical
  edge $`\operatorname{Re} s = -1/2`;
* $`\mathrm{LeftArc}` is the subset of $`S` on the left half of the unit-circle
  arc $`\|s\| = 1`, $`\operatorname{Re} s < 0` and $`s \ne \rho`.

{uses "generalized-winding-number"}[] {uses "gwn-at-i"}[] {uses "gwn-at-rho"}[] {uses "gwn-at-rho-plus-one"}[]
:::

:::proof "valence-orbit-sum-of-pvChain"
The PV chain identity gives a weighted sum of orders over $`S` matching
$`-(k/12 - \operatorname{ord}_\infty(f))`. Substituting the three explicit
elliptic winding numbers ($`-\tfrac{1}{2}` at $`i`, $`-\tfrac{1}{6}` at $`\rho`
and at $`\rho+1`, see {bpref "gwn-at-i"}[], {bpref "gwn-at-rho"}[],
{bpref "gwn-at-rho-plus-one"}[]), and using the interior winding number $`-1` at
strictly interior points and the smooth-boundary winding $`-\tfrac{1}{2}` at every
other on-curve point, replaces $`\operatorname{gWN}` in each term by an explicit
numerical weight. The right and left boundary subsets are paired via modular
invariance (the $`T`-translation identifies the two vertical edges, and the
$`S`-action identifies the two halves of the unit-circle arc), reducing each pair
to a single canonical representative. The orders at $`\rho` and $`\rho+1` are equal
by modular invariance; absorbing this identity gives the
$`\tfrac{1}{3}\operatorname{ord}_\rho(f)` term. Rearranging yields the claimed
equality.

{uses "gwn-at-i"}[] {uses "gwn-at-rho"}[] {uses "gwn-at-rho-plus-one"}[] {uses "hw-3-3-clean-full-mero"}[]
:::

:::theorem "valence-formula-textbook" (lean := "valence_formula_textbook")
Let $`k \in \mathbb{Z}` and let $`f \in M_k(\Gamma(1))` be a weight-$`k` modular
form on the full modular group $`\operatorname{SL}_2(\mathbb{Z})` with $`f \ne 0`.
Then
$$`\operatorname{ord}_\infty(f) + \tfrac{1}{2}\,\operatorname{ord}_{i}(f) + \tfrac{1}{3}\,\operatorname{ord}_{\rho}(f) + \sum_{q \in \mathrm{NonEllOrbit}} \operatorname{ord}_{q}(f) \;=\; \frac{k}{12},`
where the last sum runs over the $`\operatorname{SL}_2(\mathbb{Z})`-orbits in
$`\mathbb{H}` that are neither the orbit of $`i` nor the orbit of $`\rho`, and
$`\operatorname{ord}_q(f)` is the order of vanishing of $`f` at any representative
of $`q` (well-defined by modular invariance).

{uses "valence-orbit-sum-of-pvChain"}[]
:::

:::proof "valence-formula-textbook"
The proof is a culmination of the entire Hungerbühler–Wasem apparatus and the
orbit machinery. Apply the Hungerbühler–Wasem generalised residue theorem
({bpref "hw-3-3-clean-full-mero"}[]) to the function $`f'/f` around the
fundamental-domain boundary $`\partial \mathcal{D}_H` at a sufficiently large
height $`H`. The simple poles of $`f'/f` on $`\mathcal{D}` are precisely the zeros
of $`f`; the residue of $`f'/f` at a zero of $`f` is the order of vanishing. The
Hungerbühler–Wasem identity therefore takes the form
$$`\operatorname{PV}_S\!\!\int_{\partial \mathcal{D}_H} \frac{f'(z)}{f(z)}\,\mathrm{d}z \;=\; \sum_{s \in S} 2 \pi i \, \operatorname{gWN}(\partial \mathcal{D}_H, s) \, \operatorname{ord}_{s}(f).`
The left-hand side is in turn computed by the modular contour integral around the
closed boundary $`\partial \mathcal{D}_H` to equal
$`2\pi i \, (\operatorname{ord}_\infty(f) - k/12)` — the textbook contour-integral
calculation, in which the top horizontal segment contributes
$`\operatorname{ord}_\infty(f)` via the $`q`-expansion, the two vertical edges
cancel by $`T`-invariance, and the two arcs are related by $`S`-invariance,
summing to $`-k/12`. Equating the two sides and dividing by $`2 \pi i` gives the
PV chain identity that hypothesises {bpref "valence-orbit-sum-of-pvChain"}[]. The
orbit-sum identity of that theorem rewrites the right-hand side as
$$`\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f) + \tfrac{1}{3}\operatorname{ord}_\rho(f) + \sum_{q \in \mathrm{NonEllOrbit}} \operatorname{ord}_{q}(f) = k/12,`
which is the textbook valence formula.

{uses "valence-orbit-sum-of-pvChain"}[] {uses "hw-3-3-clean-full-mero"}[]
:::
