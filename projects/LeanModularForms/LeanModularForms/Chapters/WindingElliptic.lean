import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.I
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.Rho
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.RhoPlusOne

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Generalised winding numbers at the elliptic points" =>

Let $`\partial \mathcal{D}_H` denote the height-$`H` truncated boundary
of the standard fundamental domain $`\mathcal{D}` of
$`\operatorname{SL}_2(\mathbb{Z})`, parametrised on $`[0,5]` with the
five segments

- segment 0: the upward vertical edge $`\operatorname{Re} z = 1/2`,
  from $`1/2 + iH` down to $`\rho + 1 = 1/2 + i\sqrt{3}/2`;
- segment 1: the right arc of the unit circle from
  $`\rho + 1` counterclockwise to $`i`;
- segment 2: the left arc of the unit circle from $`i` to
  $`\rho = -1/2 + i\sqrt{3}/2`;
- segment 3: the upward vertical edge $`\operatorname{Re} z = -1/2`,
  from $`\rho` down to $`-1/2 + iH`;
- segment 4: the horizontal top edge from $`-1/2 + iH` to
  $`1/2 + iH`.

The closed boundary $`\partial \mathcal{D}_H` passes through the three
elliptic points $`i = \gamma(2)`, $`\rho = \gamma(3)` and
$`\rho + 1 = \gamma(1)` (using the $`[0,5]` parametrisation). At each
of these points the curve has a corner of opening angle a rational
multiple of $`\pi`, so the generalised winding number takes a
fractional value. We compute the three values via the principal value
formula of {bpref "generalized-winding-number"}[].

Although the project's file docstrings advertise headline theorems
named `gWN_fdBoundary_H_at_*`, the actual finalised
content is delivered by the three Cauchy-principal-value-limit
theorems `pv_integral_at_*_tendsto`. By
{bpref "generalized-winding-number"}[] these PV-limit theorems
*determine* $`\operatorname{gWN}(\partial \mathcal{D}_H, p)` at
the corresponding elliptic point $`p` via division by $`2\pi i`. We
therefore present the PV-limit form below; the equivalent gWN
statement is the immediate consequence
$`\operatorname{gWN} = (2 \pi i)^{-1} \cdot L` where $`L` is the
PV-limit value.

:::theorem "gwn-at-i" (lean := "pv_integral_at_i_tendsto")
*Generalised winding number at $`i`.*
For every $`H > 1`,
$$`
  \operatorname{PV}_{\{i\}}\!\!\int_{\partial \mathcal{D}_H}
    \frac{\mathrm{d}z}{z - i}
  \;=\; -i\pi,
`
i.e.\ the $`\varepsilon`-cutoff PV integral around $`i` converges to
$`-i\pi` as $`\varepsilon \to 0^{+}`. Equivalently,
$`\operatorname{gWN}(\partial \mathcal{D}_H, i) = -\tfrac{1}{2}`.

Depends on: {uses "generalized-winding-number"}[] {uses "has-cauchy-pv-on"}[]
:::

:::proof "gwn-at-i"
At the elliptic point $`i = \gamma(2)` the boundary has a corner
between segment 1 (the right arc) on the left and segment 2 (the
left arc) on the right, with combined interior opening angle $`\pi`
(each arc subtends $`\pi/2` at the corner). We apply the crossing
limit theorem with $`t_0 = 2` and cutoff
$`\delta(\varepsilon) = (12/\pi)\arcsin(\varepsilon/2)`, the
arc-length inverse of the formula
$`\|\gamma(2 \pm \delta) - i\| = 2 \sin(\delta \pi / 12)`. The
fundamental-theorem-of-calculus telescoping value is
$$`
  E(\varepsilon) =
  \log\!\bigl(\gamma(2 - \delta(\varepsilon)) - i\bigr)
  - \log\!\bigl(\gamma(2 + \delta(\varepsilon)) - i\bigr)
  - 2\pi i.
`
The arc argument computations
$`\arg(\gamma(2-\delta) - i) = -\delta\pi/12` and
$`\arg(\gamma(2+\delta) - i) = \delta\pi/12 - \pi` combine with the
norm equality above to give
$`E(\varepsilon) \to -i\pi` as $`\varepsilon \to 0^{+}`, and the PV
integral tends to the same limit.
:::

:::theorem "gwn-at-rho" (lean := "pv_integral_at_rho_tendsto")
*Generalised winding number at $`\rho`.*
For every $`H > \sqrt{3}/2`,
$$`
  \operatorname{PV}_{\{\rho\}}\!\!\int_{\partial \mathcal{D}_H}
    \frac{\mathrm{d}z}{z - \rho}
  \;=\; -\frac{i\pi}{3},
`
where $`\rho = e^{2\pi i / 3} = -1/2 + i\sqrt{3}/2` is the
elliptic point at $`\gamma(3)`. Equivalently,
$`\operatorname{gWN}(\partial \mathcal{D}_H, \rho) = -\tfrac{1}{6}`.

Depends on: {uses "generalized-winding-number"}[] {uses "has-cauchy-pv-on"}[]
:::

:::proof "gwn-at-rho"
At $`\rho = \gamma(3)` the boundary has a corner between segment 2
(the left arc) on the left and segment 3 (the vertical edge
$`\operatorname{Re} z = -1/2`) on the right. The interior opening
angle is $`\pi/3` (the left arc enters tangent to a direction
forming angle $`2\pi/3` with the downward vertical). Because the
two pieces have different tangent directions at $`\rho`, we use
the asymmetric crossing-limit theorem with two cutoffs:
$`\delta_L(\varepsilon) = \delta_{L,\rho}(\varepsilon)` measured
along the left arc and
$`\delta_R(\varepsilon) = \delta_{R,\rho}(H)(\varepsilon)` measured
along the vertical edge. The corresponding FTC-telescope
value is
$$`
  E(\varepsilon) =
  \log\!\bigl(\gamma(3 - \delta_L(\varepsilon)) - \rho\bigr)
  - \log\!\bigl(\gamma(3 + \delta_R(\varepsilon)) - \rho\bigr),
`
which by the arc and vertical-segment argument computations tends
to $`-i\pi/3` as $`\varepsilon \to 0^{+}`.
:::

:::theorem "gwn-at-rho-plus-one" (lean := "pv_integral_at_rho_plus_one_tendsto")
*Generalised winding number at $`\rho + 1`.*
For every $`H > \sqrt{3}/2`,
$$`
  \operatorname{PV}_{\{\rho + 1\}}\!\!\int_{\partial \mathcal{D}_H}
    \frac{\mathrm{d}z}{z - (\rho + 1)}
  \;=\; -\frac{i\pi}{3},
`
where $`\rho + 1 = e^{\pi i/3} = 1/2 + i\sqrt{3}/2` is the elliptic
point at $`\gamma(1)`. Equivalently,
$`\operatorname{gWN}(\partial \mathcal{D}_H, \rho + 1)
 = -\tfrac{1}{6}`.

Depends on: {uses "generalized-winding-number"}[] {uses "has-cauchy-pv-on"}[]
:::

:::proof "gwn-at-rho-plus-one"
At $`\rho + 1 = \gamma(1)` the boundary has a corner between segment
0 (the vertical edge $`\operatorname{Re} z = 1/2`) on the left and
segment 1 (the right arc) on the right. By the $`T`-symmetry of
the boundary (translation by $`1` sends segment 3 to segment 0 and
segment 2 to segment 1), this corner has the same opening angle
$`\pi/3` as the corner at $`\rho`. The proof mirrors the $`\rho`
case using asymmetric cutoffs $`\delta_L(\varepsilon)
= \varepsilon/(H - \sqrt{3}/2)` (along the vertical segment)
and $`\delta_R(\varepsilon) = (12/\pi)\arcsin(\varepsilon/2)`
(along the arc). The FTC-telescope value
$$`
  E(\varepsilon) =
  \log\!\bigl(\gamma(1 - \delta_L(\varepsilon)) - (\rho+1)\bigr)
  - \log\!\bigl(\gamma(1 + \delta_R(\varepsilon)) - (\rho+1)\bigr)
`
again tends to $`-i\pi/3`.
:::
