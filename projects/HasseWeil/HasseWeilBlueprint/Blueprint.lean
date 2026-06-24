import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import HasseWeil.Frobenius
import HasseWeil.Hasse.QuadraticForm
import HasseWeil.HasseBound
import HasseWeil.WeilPairing.HasseBound

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Hasse Bound — Lean blueprint" =>

This is the blueprint for the [`Hasse-Weil`](https://github.com/CBirkbeck/Hasse-Weil)
formalisation of _Hasse's theorem_ for an elliptic curve $`E` over a finite field
$`\mathbb{F}_q`: the unconditional bound
$$`\bigl|\,\#E(\mathbb{F}_q) - (q + 1)\,\bigr| \;\le\; 2\sqrt{q}`
on the number of $`\mathbb{F}_q`-rational points. Equivalently, writing
$`t = q + 1 - \#E(\mathbb{F}_q)` for the *trace of Frobenius*, it is the integer
inequality $`t^2 \le 4q`.

The argument is the classical one (Silverman V.1.1): the degree map on the
endomorphism ring $`\operatorname{End}(E)` is a positive-definite quadratic form, and
applying it to $`r\pi - s` (where $`\pi` is the $`q`-power Frobenius) forces the
discriminant of a binary quadratic form to be non-positive — which is exactly
$`t^2 \le 4q`. The Lean development isolates a *pure-arithmetic core* (the binary-form
discriminant bound and the passage to square roots) from the *geometric input* (the
non-negativity of the degree form), and the capstone `hasse_bound` is _unconditional
and sorry-free_.

Each node carries a `(lean := …)` reference to the actual declaration in the
`HasseWeil` library, so Verso reads its completion status directly from Lean. The
dependency graph at the foot of the page records the logical spine.

# Point counts and the Frobenius endomorphism

:::definition "point-count" (lean := "HasseWeil.pointCount")
For an elliptic curve $`E` over a finite field $`K = \mathbb{F}_q` whose affine point
type is finite, the *point count* $`\#E(\mathbb{F}_q)` is the cardinality of the
finite abelian group of $`\mathbb{F}_q`-rational nonsingular affine points together
with the point at infinity. In `Hasse-Weil` this is
$$`\texttt{pointCount } E \;:=\; \operatorname{card} E.\mathrm{Point}.`
:::

:::definition "frobenius-isogeny" (lean := "HasseWeil.frobeniusIsog, HasseWeil.frobeniusIsog_pullback_apply")
The *$`q`-power Frobenius* $`\pi : E \to E` is the isogeny acting on the function
field by $`f \mapsto f^{q}` ({uses "point-count"}[]). In `Hasse-Weil` it is
$`\texttt{frobeniusIsog}`, and $`\texttt{frobeniusIsog\_pullback\_apply}` records that
its pullback on the function field is exactly the $`\#K`-power map (built on
`FiniteField.frobeniusAlgHom`). Its *trace* is the integer
$$`t \;=\; q + 1 - \#E(\mathbb{F}_q),`
so that the fixed points of $`\pi` — the $`\mathbb{F}_q`-rational points — are counted
by $`\deg(1 - \pi) = \#E(\mathbb{F}_q)`.
:::

# The degree quadratic form

:::theorem "degree-quadratic-form" (lean := "HasseWeil.traceOfFrobenius_sq_le_of_qf_nonneg")
*(Geometric input.)* Suppose the degree form on $`\operatorname{End}(E)` is
non-negative on the Frobenius pencil, i.e. for all $`r, s \in \mathbb{Z}`
$$`\deg(r\pi - s) \;=\; q\,r^2 - t\,r\,s + s^2 \;\ge\; 0`
({uses "frobenius-isogeny"}[]). Then $`t^2 \le 4q`.
:::

:::proof "degree-quadratic-form"
The degree of an isogeny is a non-negative integer, and on the rank-two lattice
$`\mathbb{Z}\,1 \oplus \mathbb{Z}\,\pi \subseteq \operatorname{End}(E)` it is the
binary quadratic form $`Q(s, r) = s^2 - t\,r\,s + q\,r^2` whose middle coefficient is
the Frobenius trace and whose leading coefficient $`\deg\pi = q`. Non-negativity of a
binary quadratic form forces its discriminant to be non-positive; here that is
exactly $`t^2 - 4q \le 0`. Formally this is the arithmetic core
({uses "trace-sq-le-four-q"}[]) applied to the degree values.
:::

:::theorem "trace-sq-le-four-q" (lean := "HasseWeil.trace_sq_le_four_mul_deg")
*(Arithmetic core.)* Let $`q` be a positive integer and $`t \in \mathbb{Z}`. If the
binary form $`q\,r^2 - t\,r\,s + s^2` is non-negative for all integers $`r, s`, then
$$`t^2 \;\le\; 4q.`
:::

:::proof "trace-sq-le-four-q"
Specialise the non-negativity hypothesis at $`(r, s) = (t, 2q)`: this gives
$`q\,t^2 - 2q\,t^2 + 4q^2 = q\,(4q - t^2) \ge 0`, and since $`q > 0` we conclude
$`t^2 \le 4q`. (This is the discriminant-non-positivity of the binary form, made
elementary by evaluating at the point where the form is minimised along the line
$`s = 2q`.)
:::

:::theorem "sqrt-bound" (lean := "HasseWeil.abs_le_two_sqrt_of_sq_le")
*(Passage to square roots.)* For $`q \in \mathbb{N}` and $`t \in \mathbb{Z}`, if
$`t^2 \le 4q` then
$$`|t| \;\le\; 2\sqrt{q}`
as real numbers.
:::

:::proof "sqrt-bound"
Over $`\mathbb{R}`, $`(2\sqrt{q})^2 = 4q \ge t^2`, and both $`|t|` and $`2\sqrt{q}`
are non-negative, so taking square roots of $`t^2 \le (2\sqrt{q})^2` preserves the
inequality ({uses "trace-sq-le-four-q"}[]).
:::

# The Hasse bound

:::theorem "hasse-bound" (lean := "HasseWeil.WeilPairing.hasse_bound, HasseWeil.WeilPairing.hasse_bound_unconditional")
*(Hasse's theorem.)* For an elliptic curve $`E` over a finite field $`\mathbb{F}_q`,
$$`\bigl|\,\#E(\mathbb{F}_q) - (q + 1)\,\bigr| \;\le\; 2\sqrt{q}.`
This is the _unconditional, sorry-free_ `hasse_bound`, specialised from
`hasse_bound_unconditional` (which assumes only $`2 \le \#K`).
:::

:::proof "hasse-bound"
Let $`t = q + 1 - \#E(\mathbb{F}_q)` be the trace of Frobenius
({uses "frobenius-isogeny"}[], {uses "point-count"}[]). The degree form on
$`\operatorname{End}(E)` is positive semi-definite on the Frobenius pencil, so by the
degree-form bound $`t^2 \le 4q` ({uses "degree-quadratic-form"}[]). Passing to square
roots gives $`|t| \le 2\sqrt{q}` ({uses "sqrt-bound"}[]), and since
$`\#E(\mathbb{F}_q) - (q + 1) = -t`, this is the displayed bound. In the
formalisation the positive semi-definiteness of the degree form is discharged
unconditionally (via the kernel-cardinality degree function and the Frobenius
base-change scalings), so `hasse_bound` carries no hypotheses beyond $`E` being
elliptic over a finite field.
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}
