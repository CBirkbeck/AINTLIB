import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms
import LeanModularFormsBlueprint.Refs
import LeanModularFormsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The generalised winding number" =>

The classical winding number is defined for curves that avoid the reference
point. To accommodate curves that pass through that point, Hungerbühler–Wasem use
a Cauchy principal value of the Cauchy kernel.

:::definition "generalized-winding-number" (lean := "generalizedWindingNumber")
Let $`\gamma : [0,1] \to \mathbb{C}` be a piecewise-$`C^{1}` path from $`x` to
$`y`, and let $`z_0 \in \mathbb{C}`. The *generalised winding number* of $`\gamma`
around $`z_0` is defined by
$$`\operatorname{gWN}(\gamma, z_0) \;=\; \frac{1}{2 \pi i} \operatorname{PV}\!\!\int_{\gamma} \frac{\mathrm{d}z}{z - z_0},`
where the principal value is the single-point CPV at $`z_0` (a specialisation of
{bpref "has-cauchy-pv-on"}[] with $`S = \{z_0\}` and $`f(z) = (z-z_0)^{-1}`).
When the principal value does not exist, $`\operatorname{gWN}(\gamma, z_0)` is set
to a default value.

When $`\gamma` avoids $`z_0`, $`\operatorname{gWN}(\gamma, z_0)` coincides with the
classical winding number, an integer. When $`\gamma` crosses $`z_0` transversally
once, the principal value exists with
$`\operatorname{gWN}(\gamma, z_0) \in \tfrac{1}{2} + \mathbb{Z}`. More generally,
$`\operatorname{gWN}(\gamma, z_0)` may take any half-integer or rational value,
depending on how often and at what angles $`\gamma` meets $`z_0`.

{uses "has-cauchy-pv-on"}[]
:::
