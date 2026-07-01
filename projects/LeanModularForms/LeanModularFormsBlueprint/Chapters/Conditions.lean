import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms
import LeanModularFormsBlueprint.Refs
import LeanModularFormsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Paper conditions (A') and (B)" =>

The Hungerbühler–Wasem generalised residue theorem requires two hypotheses on the
geometry of the curve at crossings. *Condition (A')* controls the flatness of the
curve transverse to its tangent at each crossing; *condition (B)* controls the
relationship between the crossing angle and the Laurent coefficients of $`f` at
the corresponding pole.

:::definition "condition-a-prime" (lean := "SatisfiesConditionA'")
Let $`\gamma` be a piecewise-$`C^{1}` immersion based at $`x`, let
$`S_0 \subseteq \mathbb{C}` be a finite set, and let
$`\operatorname{poleOrder} : \mathbb{C} \to \mathbb{N}` assign a pole order to
each candidate singular point. Following Hungerbühler–Wasem 2018, the immersion
$`\gamma` is said to *satisfy condition (A')* (relative to $`S_0` and
$`\operatorname{poleOrder}`) when: for every $`s \in S_0` and every interior
parameter $`t_0 \in (0,1)` at which $`\gamma(t_0) = s`, the curve $`\gamma` is
*flat of order $`\operatorname{poleOrder}(s)`* at $`t_0`. That is, on each side of
$`t_0` the deviation of $`\gamma` from its tangent line at $`\gamma(t_0)` is
$`o(\|\gamma(t) - \gamma(t_0)\|^{\operatorname{poleOrder}(s)})`.

Flatness of order one is automatic for a piecewise-$`C^{1}` immersion at any
interior point. Higher-order flatness is a genuine hypothesis controlling how
rapidly $`\gamma` deviates from its tangent line at a higher-order pole.

{uses "closed-pwc1-immersion"}[]
:::

:::definition "condition-b" (lean := "SatisfiesConditionB")
Let $`\gamma` be a piecewise-$`C^{1}` immersion based at $`x`, let
$`f : \mathbb{C} \to \mathbb{C}`, and let $`S_0 \subseteq \mathbb{C}` be a finite
set. Following Hungerbühler–Wasem 2018, Theorem 3.3, $`(\gamma, f)` *satisfies
condition (B)* (relative to $`S_0`) when, for every $`s \in S_0` and every
interior parameter $`t_0 \in (0,1)` with $`\gamma(t_0) = s`, both of the following
hold.

* *Rational angle.* The *crossing angle*
  $`\alpha = \operatorname{angleAtCrossing}(\gamma, t_0)` is a rational multiple
  of $`\pi`: there exist coprime naturals $`p, q` with $`q \ne 0` and
  $`\alpha = p\pi/q`.
* *Laurent compatibility.* There exist $`N \in \mathbb{N}`, complex coefficients
  $`a_0, \ldots, a_{N-1}`, and a function $`g` analytic at $`s` such that
  $$`f(z) = g(z) + \sum_{k=0}^{N-1} \frac{a_k}{(z - s)^{k+1}} \quad \text{for } z \text{ near } s,\, z \ne s,`
  and, for every $`k \ge 1` with $`a_k \ne 0`, the product $`k\alpha` is an
  integer multiple of $`2\pi`: $`k \alpha \in 2\pi \mathbb{Z}`.

Geometrically, condition (B) says that the higher-order Laurent data of $`f` at
$`s` is compatible with the angle at which $`\gamma` passes through $`s`, in the
precise sense required for the sector-cancellation identity (Hungerbühler–Wasem
2018, equation 3.4) to apply.

{uses "closed-pwc1-immersion"}[]
:::
