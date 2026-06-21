import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.ForMathlib.HW33Clean
import LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiCrossingCPV

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Hungerbühler–Wasem generalised residue theorem" =>

In this chapter we present the dependency chain culminating in the
fully discharged paper-faithful form of the Hungerbühler–Wasem
generalised residue theorem (Hungerbühler–Wasem 2018, Theorem 3.3).
The headline statement asserts that the multi-point Cauchy principal
value of $`f` along a closed null-homologous piecewise-$`C^{1}`
immersion equals a weighted sum of residues, where the weights are
the generalised winding numbers. The proof proceeds by reducing to
the per-pole problem, splitting each pole into its simple and
higher-order Laurent contributions, and handling the higher-order
part by the sector-cancellation identity under condition (B).

:::theorem "residue-paper-faithful-clean" (lean := "HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean")
*HW3.3 — paper-faithful clean form.*
Let $`U \subseteq \mathbb{C}` be a non-empty open set, $`S \subseteq U`
a finite set, and $`f : \mathbb{C} \to \mathbb{C}` a function. Assume:

* $`f` is holomorphic on $`U \setminus S` and meromorphic at
  every point of $`S`;
* $`\gamma` is a closed piecewise-$`C^{1}` immersion based at
  $`x \in U`, with $`x \notin S`;
* $`\gamma` is null-homologous in $`U`;
* $`(\gamma, f)` satisfies condition (B) relative to $`S`;
* $`\gamma` satisfies condition (A') relative to $`S` with
  $`\operatorname{poleOrder}(s)` equal to the order of the polar
  part of $`f` at $`s` provided by the canonical polar-part
  decomposition.

Then the multi-point Cauchy principal value of $`\oint_\gamma f`
exists and equals
$$`
  \operatorname{PV}_S\!\!\int_\gamma f(z)\,\mathrm{d}z
  \;=\; \sum_{s \in S}
    2 \pi i \, \operatorname{gWN}(\gamma, s) \, \operatorname{Res}(f, s).
`

Depends on: {uses "closed-pwc1-immersion"}[] {uses "null-homologous"}[] {uses "has-cauchy-pv-on"}[] {uses "generalized-winding-number"}[] {uses "condition-a-prime"}[] {uses "condition-b"}[]
:::

:::proof "residue-paper-faithful-clean"
By extracting the canonical polar-part decomposition of $`f` over
$`S` in $`U` from the condition-(B) data, we reduce to the
compositional residue theorem ({uses "residue-compositional"}[]).
That reduction in turn requires, for each $`s \in S`, an explicit
per-pole Cauchy principal value identity for the polar part. We
split the proof of those identities into two cases:

* if $`\gamma` avoids the pole $`s` on $`[0,1]`, the polar part
  is regular along $`\gamma`, and the principal value coincides
  with the ordinary contour integral; this is
  {uses "cpv-polar-uncrossed"}[];
* otherwise the set of crossings of $`\gamma` at $`s` is a
  finite subset of $`(0,1)` (its finiteness uses
  $`x \notin S`); we then combine the corner-friendly
  multi-crossing CPV identity {uses "cpv-polar-multicrossed-condB"}[]
  with the canonical right/left tangent limits at each crossing.

Together these per-pole identities, applied to every $`s \in S`,
combine via the compositional theorem to yield the stated
equality.
:::

:::theorem "residue-compositional" (lean := "HungerbuhlerWasem.residueTheorem_crossing_compositional")
*Compositional residue theorem.*
Let $`U \subseteq \mathbb{C}` be a non-empty open set,
$`S \subseteq U` a finite set, $`f : \mathbb{C} \to \mathbb{C}`
holomorphic on $`U \setminus S`, and $`\gamma` a closed piecewise-$`C^{1}`
immersion based at $`x \in U` that is null-homologous in $`U`. Assume
that $`f` admits a polar-part decomposition
$`f(z) = h(z) + \sum_{s \in S} P_s(z)`, where each $`P_s` is the
Laurent polar part at $`s` and $`h` is the analytic remainder, and
that for each $`s \in S` the polar part has principal value
$$`
  \operatorname{PV}_S\!\!\int_\gamma P_s(z)\,\mathrm{d}z
    \;=\; 2 \pi i \, \operatorname{gWN}(\gamma, s) \,
      \operatorname{Res}(f, s).
`
Then
$$`
  \operatorname{PV}_S\!\!\int_\gamma f(z)\,\mathrm{d}z
  \;=\; \sum_{s \in S}
    2 \pi i \, \operatorname{gWN}(\gamma, s) \,
      \operatorname{Res}(f, s).
`

Depends on: {uses "closed-pwc1-immersion"}[] {uses "null-homologous"}[] {uses "has-cauchy-pv-on"}[] {uses "generalized-winding-number"}[]
:::

:::proof "residue-compositional"
The analytic remainder $`h` has principal value zero by Dixon's
theorem applied to the null-homologous $`\gamma` together with the
observation that the multi-point CPV-cutoff integral of an analytic
function on $`U` along a null-homologous curve tends to the contour
integral of $`h`, which vanishes. Adding this to the assumed
per-pole identities, and exchanging finite sum with the
$`\varepsilon \to 0^{+}` limit, gives the result. The
exchange-of-limit step is justified by the integrability of each
cutoff integrand on $`[0,1]`, which holds because the polar parts
are continuous off their poles and $`h` is continuous everywhere.
:::

:::theorem "cpv-polar-uncrossed" (lean := "HungerbuhlerWasem.cpv_polarPart_at_uncrossed_pole")
*Per-pole CPV at an uncrossed pole.*
Let $`U \subseteq \mathbb{C}` be open, $`S \subseteq U` finite, and
$`f : \mathbb{C} \to \mathbb{C}` with polar-part decomposition over
$`S` in $`U`. Let $`\gamma` be a closed piecewise-$`C^{1}`
immersion null-homologous in $`U`, and let $`s \in S` be a pole that
$`\gamma` *avoids*: $`\gamma(t) \ne s` for every $`t \in [0,1]`.
Then the polar part at $`s` has multi-point Cauchy principal value
$$`
  \operatorname{PV}_S\!\!\int_\gamma P_s(z)\,\mathrm{d}z
  \;=\; 2 \pi i \, \operatorname{gWN}(\gamma, s) \,
    \operatorname{Res}(f, s).
`

Depends on: {uses "closed-pwc1-immersion"}[] {uses "null-homologous"}[] {uses "has-cauchy-pv-on"}[] {uses "generalized-winding-number"}[]
:::

:::proof "cpv-polar-uncrossed"
Since $`\gamma` avoids $`s`, the distance from $`\gamma` to $`s` is
bounded below by some $`\delta > 0` by compactness of the image.
For $`\varepsilon < \delta` the multi-point cutoff integrand for the
polar part coincides with the ordinary integrand on all of $`[0,1]`,
so the cutoff integrals are eventually constant in $`\varepsilon`
and equal to the contour integral
$`\int_\gamma P_s(z)\,\mathrm{d}z`. The dominated-convergence
argument therefore reduces to evaluating the contour integral of
$`P_s` on $`\gamma`, and the avoidance computation identifies this
with $`2\pi i \, \operatorname{gWN}(\gamma, s) \, \operatorname{Res}(f, s)`.
:::

:::theorem "cpv-polar-multicrossed-condB" (lean := "HungerbuhlerWasem.cpv_polarPart_at_multiCrossed_pole_under_condB_corner")
*Per-pole CPV at a multi-crossed pole under condition (B).*
Let $`\gamma` be a closed piecewise-$`C^{1}` immersion at $`x`, let
$`s \in S` be a pole at which the polar part of $`f` has order $`N`,
and let
$$`
  \operatorname{crossings} = \{ t \in (0,1) : \gamma(t) = s \}
`
be a finite (corner-allowing) crossing set. Assume the following
data on $`\operatorname{crossings}`:

* at every $`t \in \operatorname{crossings}` the curve
  $`\gamma` is flat of order $`N` (the condition (A') witness);
* right and left tangent limits $`L_+(t), L_-(t) \in
  \mathbb{C}^{\times}` exist;
* the angle-compatibility identity from condition (B)
  $$`
    \bigl(L_+(t) / |L_+(t)|\bigr)^{k}
    = \bigl(-L_-(t) / |L_-(t)|\bigr)^{k}
  `
  holds for every $`k \ge 1` at which the Laurent coefficient
  $`a_k` at $`s` is non-zero;
* the simple-pole Cauchy principal value of $`(z - s)^{-1}`
  along $`\gamma` exists.

Then the polar part at $`s` has multi-point CPV
$$`
  \operatorname{PV}_{\{s\}}\!\!\int_\gamma P_s(z)\,\mathrm{d}z
  \;=\; 2 \pi i \, \operatorname{gWN}(\gamma, s) \,
    \operatorname{Res}(f, s).
`

Depends on: {uses "closed-pwc1-immersion"}[] {uses "has-cauchy-pv-on"}[] {uses "generalized-winding-number"}[] {uses "condition-a-prime"}[] {uses "condition-b"}[]
:::

:::proof "cpv-polar-multicrossed-condB"
We split the polar part as
$`P_s(z) = a_0/(z-s) + \sum_{k=1}^{N-1} a_k/(z-s)^{k+1}`. The
$`k = 0` term is the simple-pole contribution: by the assumed
existence of the principal value for $`(z-s)^{-1}`, that principal
value equals $`2\pi i \, \operatorname{gWN}(\gamma, s)`, so the
$`k=0` contribution gives $`a_0` times this expression, which equals
$`2\pi i \, \operatorname{gWN}(\gamma, s) \, \operatorname{Res}(f, s)`.

For each $`k \ge 1`, two cases. If $`a_k = 0` the term is
identically zero. If $`a_k \ne 0`, the flatness-of-order-$`N`
hypothesis and the angle-compatibility condition (B) hypothesis
combine to give the sector-cancellation identity: the cutoff
integral of $`a_k/(z-s)^{k+1}` along $`\gamma` vanishes in the
$`\varepsilon \to 0^+` limit. Summing over $`k` from $`0` to $`N-1`
yields the claim.
:::

:::theorem "hw-3-3-clean-full-mero" (lean := "LeanModularForms.hw_3_3_clean_full_mero")
*HW3.3 — fully general, multi-crossing, meromorphic form.*
Let $`U \subseteq \mathbb{C}` be a non-empty open set, $`S \subseteq U`
a finite set, and $`f : \mathbb{C} \to \mathbb{C}` a function such
that

* $`f` is holomorphic on $`U \setminus S`, and
* $`f` is meromorphic at each $`s \in S`.

Let $`\gamma` be a closed piecewise-$`C^{1}` immersion based at
$`x \in U` with $`x \notin S`, null-homologous in $`U`. Suppose
that $`(\gamma, f)` satisfies condition (B) and that $`\gamma`
satisfies condition (A') with pole-order data equal to the
canonical polar-part orders extracted from the
condition-(B) witness. Then
$$`
  \operatorname{PV}_S\!\!\int_\gamma f(z)\,\mathrm{d}z
  \;=\; \sum_{s \in S} 2 \pi i \,
    \operatorname{gWN}(\gamma, s) \, \operatorname{Res}(f, s).
`
This is the maximally general paper-faithful form of
Hungerbühler–Wasem 2018, Theorem 3.3, with all six oracle
hypotheses of the intermediate "*hw\_3\_3\_paper*" formulation
discharged.

Depends on: {uses "residue-paper-faithful-clean"}[] {uses "closed-pwc1-immersion"}[] {uses "null-homologous"}[] {uses "has-cauchy-pv-on"}[] {uses "generalized-winding-number"}[] {uses "condition-a-prime"}[] {uses "condition-b"}[]
:::

:::proof "hw-3-3-clean-full-mero"
This is a direct invocation of the paper-faithful clean form
{uses "residue-paper-faithful-clean"}[]: the hypothesis list of
the present theorem matches that of the clean form term-for-term,
and no additional reduction is needed.

The single structural residual $`x \notin S` is the only
Lean-formalisation artefact (the curve in our setting carries a
typed basepoint, whereas the paper works with cycles). It is
routinely satisfiable: if $`x \in S`, replace $`\gamma` by the
cyclic shift $`\gamma(\,\cdot\, + \tau)` for a parameter
$`\tau \in (0,1)` at which $`\gamma(\tau) \notin S`, which exists
since the preimage of the finite set $`S` under $`\gamma` is
finite.
:::
