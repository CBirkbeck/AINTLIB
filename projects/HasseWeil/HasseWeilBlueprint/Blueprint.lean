import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import HasseWeil.Frobenius
import HasseWeil.WeilPairing.HasseBound

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Hasse Bound — Lean blueprint" =>

This is the blueprint for the [`Hasse-Weil`](https://github.com/CBirkbeck/Hasse-Weil)
formalisation of *Hasse's theorem* for elliptic curves over a finite field: the
unconditional bound
$$`\bigl|\,\#E(\mathbb{F}_q) - (q + 1)\,\bigr| \;\le\; 2\sqrt{q}`
on the number of $`\mathbb{F}_q`-points of an elliptic curve. The capstone
$`\texttt{hasse\_bound}` is *sorry-free and unconditional*: the earlier
deferred witnesses (the non-negativity of the degree form on $`\mathrm{End}(E)`
and the point-count identity) are now discharged.

Each node carries a `(lean := …)` reference to the actual declaration in the
`HasseWeil` library, so Verso reads its completion status directly from Lean —
green once the declaration is fully proved. The dependency graph at the foot of
the page records which results feed into which.

# Point counts over finite fields

:::definition "point-count" (lean := "HasseWeil.pointCount")
For a Weierstrass curve $`W` over a finite field $`K = \mathbb{F}_q` whose affine
point type is finite, the *point count* $`\#E(\mathbb{F}_q)` is the cardinality of
the finite group of nonsingular affine points together with the point at infinity.
In `Hasse-Weil` this is
$$`\texttt{pointCount } E \;:=\; \mathrm{Fintype.card}\ E.\mathrm{Point}.`
:::

# The Frobenius endomorphism

:::definition "frobenius-isogeny" (lean := "HasseWeil.frobeniusIsog")
For an elliptic curve $`E` over $`\mathbb{F}_q`, the *Frobenius endomorphism*
$`\pi : E \to E` acts on the function field by the $`q`-power map
$`f \mapsto f^q` ({uses "point-count"}[]). In `Hasse-Weil` it is the isogeny
$`\texttt{frobeniusIsog}` whose pullback is $`f \mapsto f^{\#K}`
($`\texttt{frobeniusIsog\_pullback\_apply}`), built on `FiniteField.frobeniusAlgHom`.
The *trace of Frobenius* is $`t = q + 1 - \#E(\mathbb{F}_q)`, so
$`\#E(\mathbb{F}_q) = q + 1 - t`.
:::

# The Hasse bound

:::theorem "hasse-bound" (lean := "HasseWeil.WeilPairing.hasse_bound, HasseWeil.WeilPairing.hasse_bound_unconditional")
*(Hasse's theorem.)* For an elliptic curve $`E` over a finite field
$`\mathbb{F}_q` whose point set is finite, with trace of Frobenius
$`t = q + 1 - \#E(\mathbb{F}_q)` ({uses "frobenius-isogeny"}[], {uses "point-count"}[]),
$$`\bigl|\,\#E(\mathbb{F}_q) - (q + 1)\,\bigr| \;\le\; 2\sqrt{q},`
equivalently $`t^2 \le 4q`. This is the *unconditional, sorry-free*
$`\texttt{hasse\_bound}` (specialised from $`\texttt{hasse\_bound\_unconditional}`,
which assumes only $`2 \le \#K`).
:::

:::proof "hasse-bound"
Write $`\pi` for the Frobenius isogeny ({uses "frobenius-isogeny"}[]) and consider
the endomorphism $`r\pi - s` for $`r, s \in \mathbb{Z}`. The degree map on
$`\mathrm{End}(E)` is a positive semi-definite quadratic form, so
$$`\deg(r\pi - s) = q r^2 - t r s + s^2 \;\ge\; 0 \quad\text{for all } r, s \in \mathbb{Z}.`
Non-negativity of this binary form forces its discriminant $`\le 0`, giving
$`t^2 \le 4q`; taking square roots and combining with
$`\#E(\mathbb{F}_q) - (q+1) = -t` ({uses "point-count"}[]) yields the displayed
bound. The formalisation discharges the degree-form non-negativity and the
point-count identity (the two formerly-deferred witnesses), so
$`\texttt{hasse\_bound}` is unconditional.
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}
