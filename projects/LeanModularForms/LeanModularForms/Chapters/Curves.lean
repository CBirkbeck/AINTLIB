import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.PaperPwC1Immersion

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Closed piecewise-C¹ immersions and null-homology" =>

This chapter introduces the curve types underlying the
Hungerbühler–Wasem residue theorem. The basic carrier is the
*closed piecewise-$`C^{1}` immersion*: a closed curve in
$`\mathbb{C}` that is $`C^{1}` on each of finitely many closed
sub-intervals between partition points, with nowhere-vanishing
derivative. The second concept, *null-homology in an open set*
$`U`, is the topological condition required to apply the residue
theorem along such a curve.

:::definition "closed-pwc1-immersion" (lean := "ClosedPwC1Immersion")
*Closed piecewise-$`C^{1}` immersion.*
Let $`x \in E` be a point of a real normed vector space $`E`.
A *closed piecewise-$`C^{1}` immersion* based at $`x` is the
following data:
* a continuous path $`\gamma : [0,1] \to E` with
  $`\gamma(0) = \gamma(1) = x`;
* a finite *closed partition*
  $`0 = a_0 < a_1 < \cdots < a_n = 1` of $`[0,1]`;
* on every closed sub-interval $`[a_k, a_{k+1}]` between
  consecutive partition members, the (extended) path
  $`\gamma : [a_k, a_{k+1}] \to E` is of class $`C^{1}` and its
  one-sided within-derivative is nowhere zero:
  $$`
    \dot{\gamma}|_{[a_k, a_{k+1}]}(t) \ne 0
    \quad \text{for every } t \in [a_k, a_{k+1}].
  `

This is the paper-faithful definition from Hungerbühler–Wasem 2018,
page 3. The non-vanishing-on-each-closed-piece convention forces a
well-defined right/left limit of $`\dot{\gamma}` at every partition
point and, in particular, two non-zero *tangent vectors* at each
corner of $`\gamma`.
:::

:::definition "null-homologous" (lean := "IsNullHomologous")
*Null-homologous closed immersion.*
Let $`U \subseteq \mathbb{C}` be an open set, $`x \in \mathbb{C}`, and
$`\gamma` a closed piecewise-$`C^{1}` immersion based at $`x` in the
sense of {bpref "closed-pwc1-immersion"}[]. We say that $`\gamma` is
*null-homologous in $`U`* when both
* the image of $`\gamma` lies in $`U`, that is
  $`\gamma(t) \in U` for every $`t \in [0,1]`, and
* for every point $`z \in \mathbb{C} \setminus U`, the
  generalised winding number
  $`\operatorname{gWN}(\gamma, z)` (see
  {bpref "generalized-winding-number"}[]) is zero.

Equivalently, $`\gamma` has image in $`U` and winds zero times around
every point of the complement.

Depends on: {uses "closed-pwc1-immersion"}[]
:::
