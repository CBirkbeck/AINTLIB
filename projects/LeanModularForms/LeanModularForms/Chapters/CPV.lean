import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue
import LeanModularForms.ForMathlib.MultipointPV

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The multi-point Cauchy principal value" =>

The Hungerbühler–Wasem residue theorem replaces the classical contour
integral $`\oint_\gamma f(z)\,\mathrm{d}z` by a Cauchy principal value
when $`\gamma` passes through poles of $`f`. The principal value is
defined by removing $`\varepsilon`-neighbourhoods of every singular
point from the parameter interval and taking the limit as
$`\varepsilon \to 0^+`.

:::definition "has-cauchy-pv-on" (lean := "HasCauchyPVOn")
*Multi-point Cauchy principal value.*
Let $`\gamma : [0,1] \to \mathbb{C}` be a piecewise-$`C^{1}` path
(see {uses "closed-pwc1-immersion"}[]) from $`x` to $`y`, let
$`S \subseteq \mathbb{C}` be a finite set, let
$`f : \mathbb{C} \to \mathbb{C}`, and let $`L \in \mathbb{C}`. For
$`\varepsilon > 0` define the cutoff integrand
$$`
  F_S(\varepsilon, t) =
  \begin{cases}
    0 & \text{if } \exists\, s \in S \text{ with } \|\gamma(t) - s\| \le \varepsilon, \\
    f(\gamma(t))\, \gamma'(t) & \text{otherwise.}
  \end{cases}
`
We say that the *multi-point Cauchy principal value of
$`\oint_\gamma f` excluding $`S` exists and equals $`L`*, written
$`\operatorname{HasCauchyPVOn}(S, f, \gamma, L)`, when
$$`
  \int_0^1 F_S(\varepsilon, t)\,\mathrm{d}t
  \;\longrightarrow\; L \qquad \text{as } \varepsilon \to 0^+.
`
We write
$$`
  \operatorname{PV}_S \int_\gamma f(z)\,\mathrm{d}z = L
`
for the corresponding value. When $`S = \{z_0\}` is a singleton this
recovers the single-point Cauchy principal value at $`z_0`.
:::
