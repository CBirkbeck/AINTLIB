import Verso
import VersoManual
import VersoBlueprint

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elliptic Curves and Arithmetic Geometry" =>

This chapter covers Weierstrass models and the group law on an elliptic curve, the
discriminant, the $`j`-invariant and its role as an isomorphism invariant, division
polynomials, and base change. Throughout, $`R` denotes a commutative ring, $`F` a field,
$`E` an elliptic curve over $`F` given by a short or general Weierstrass equation, $`\Delta`
its discriminant, $`j(E)` its $`j`-invariant, and $`E(K)` the group of $`K`-rational points
for a field extension $`K/F`. The **Hasse–Weil bound**, the **Weil conjectures** for elliptic
curves, and the **Nagell–Lutz theorem** are supplied by the external projects `Hasse-Weil`,
`WeilConjectures`, and `Nagel--Lutz` (Phase 3) and are not authored here.

# Weierstrass equations and the discriminant

:::definition "weierstrass-curve" (lean := "WeierstrassCurve")
A *Weierstrass curve* over a commutative ring $`R` is a plane cubic of the form
$$`Y^2 + a_1 XY + a_3 Y \;=\; X^3 + a_2 X^2 + a_4 X + a_6,`
specified by the tuple of coefficients $`(a_1, a_2, a_3, a_4, a_6) \in R^5`. From
these one forms the auxiliary quantities
$$`b_2 = a_1^2 + 4a_2,\quad b_4 = 2a_4 + a_1 a_3,\quad b_6 = a_3^2 + 4a_6,\quad
  b_8 = a_1^2 a_6 + 4a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2,`
and higher invariants $`c_4, c_6` built from the $`b_i`.
:::

:::definition "weierstrass-discriminant" (lean := "WeierstrassCurve.Δ")
The *discriminant* of a Weierstrass curve $`E` over $`R` is
$$`\Delta \;=\; -b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6 \;\in R.`
If $`R` is a field, $`\Delta = 0` if and only if the cubic curve is singular. One has
the identity $`1728\,\Delta = c_4^3 - c_6^2`, relating the discriminant to the higher
invariants $`c_4` and $`c_6`.
:::

:::definition "is-elliptic" (lean := "WeierstrassCurve.IsElliptic")
A Weierstrass curve $`E` over $`R` is *elliptic* if its discriminant $`\Delta` is a
unit in $`R`. When $`R` is a field this is equivalent to $`\Delta \ne 0`, i.e. the
cubic is nonsingular.
:::

:::lemma_ "two-torsion-discriminant" (lean := "WeierstrassCurve.twoTorsionPolynomial_discr")
The discriminant $`\Delta` of a Weierstrass curve is proportional to the discriminant of
the *2-torsion polynomial* $`4X^3 + b_2 X^2 + 2b_4 X + b_6`. Precisely,
$$`\mathrm{disc}(4X^3 + b_2 X^2 + 2b_4 X + b_6) \;=\; 16\,\Delta.`
In particular, over a field of characteristic different from $`2`, $`\Delta \ne 0` if and
only if the 2-torsion polynomial is separable, i.e. its three roots in a splitting field
are distinct.
:::

:::proof "two-torsion-discriminant"
This is a polynomial identity in the coefficients $`a_i`, verified by expanding both
sides using the standard formula for the discriminant of a cubic. The constant factor
$`16 = 2^4` reflects the leading coefficient $`4` of the 2-torsion polynomial.
:::

# The $`j`-invariant

:::definition "j-invariant" (lean := "WeierstrassCurve.j")
Let $`E` be an elliptic curve over $`R` (so $`\Delta` is a unit). The *$`j`-invariant* of
$`E` is
$$`j(E) \;=\; \Delta^{-1} \cdot c_4^3 \;\in R.`
It satisfies $`j(E) = 0` if and only if $`c_4 = 0` (when $`R` is reduced).
:::

:::lemma_ "j-invariant-under-variable-change" (lean := "WeierstrassCurve.variableChange_j")
The $`j`-invariant is preserved under every change of variables. Precisely, for any
invertible change of variables $`(u, r, s, t)` acting on the Weierstrass coefficients,
$$`j(C \cdot E) \;=\; j(E).`
:::

:::proof "j-invariant-under-variable-change"
Under a change of variables with unit parameter $`u`, one checks that $`c_4` scales
as $`u^{-4} c_4` and $`\Delta` scales as $`u^{-12} \Delta`. Hence
$`\Delta^{-1} c_4^3` is multiplied by $`u^{12} \cdot u^{-12} = 1`, leaving $`j`
unchanged.
:::

:::theorem "j-isom-criterion" (lean := "WeierstrassCurve.exists_variableChange_of_j_eq")
*(Isomorphism criterion via the $`j`-invariant.)* Let $`E` and $`E'` be elliptic curves
over a separably closed field $`F`. If $`j(E) = j(E')`, then there exists a change of
variables over $`F` sending $`E` to $`E'`.
:::

:::proof "j-isom-criterion"
The proof is by cases on the characteristic of $`F`. In characteristic $`\ne 2, 3` one
first places both curves in short Weierstrass form $`Y^2 = X^3 + aX + b` and then
solves explicitly for the change-of-variables parameter $`u` satisfying $`u^4 a = a'`
and $`u^6 b = b'`; the equation $`j(E) = j(E')` together with $`F` being separably
closed guarantees a solution. The characteristic 2 and 3 cases are handled by placing
the curves in the corresponding normal forms ({uses "is-elliptic"}[]) and again solving
for the parameters using the separable closedness of $`F`.
:::

# Base change

:::definition "base-change" (lean := "WeierstrassCurve.baseChange")
Let $`W` be a Weierstrass curve over $`R` and let $`A` be an $`R`-algebra. The *base
change* $`W_A` is the Weierstrass curve over $`A` obtained by applying the structure
map $`R \to A` to each coefficient $`a_i`. If $`\phi : R \to S` is any ring
homomorphism one similarly forms $`W_S = W.{\rm map}(\phi)`.
:::

:::lemma_ "base-change-discriminant" (lean := "WeierstrassCurve.map_Δ")
Base change commutes with the discriminant: for any ring homomorphism $`\phi : R \to A`,
$$`\Delta(W_A) \;=\; \phi(\Delta(W)).`
In particular, if $`\Delta(W)` is a unit in $`R` then $`\Delta(W_A) = \phi(\Delta(W))`
is a unit in $`A`, so an elliptic curve remains elliptic after base change.
:::

:::proof "base-change-discriminant"
The discriminant is a polynomial in the $`a_i`, so applying $`\phi` to each coefficient
and then computing $`\Delta` gives the same result as computing $`\Delta` first and then
applying $`\phi`, by ring-homomorphism functoriality.
:::

:::lemma_ "base-change-j" (lean := "WeierstrassCurve.map_j")
The $`j`-invariant commutes with base change: $`j(W_A) = \phi(j(W))`.
:::

:::proof "base-change-j"
Since $`j = \Delta^{-1} c_4^3`, this follows from {uses "base-change-discriminant"}[]
and the analogous commutativity $`c_4(W_A) = \phi(c_4(W))`, both of which hold because
the relevant polynomials in the $`a_i` are mapped term-by-term by $`\phi`.
:::

# The group of rational points

:::definition "affine-point" (lean := "WeierstrassCurve.Affine.Point")
Let $`W` be an elliptic curve over a field $`F`. The *affine point type* $`E(F)` has two
sorts of elements: a distinguished *point at infinity* $`\mathcal{O}`, and *affine points*
$`(x, y) \in F^2` satisfying the Weierstrass equation $`W(x, y) = 0` and the
nonsingularity condition that the partial derivatives $`W_X(x, y)` and $`W_Y(x, y)` do
not simultaneously vanish. When $`W` is an elliptic curve the two conditions coincide:
every solution of $`W(x, y) = 0` is nonsingular ({uses "is-elliptic"}[]).
:::

:::theorem "affine-points-abelian-group" (lean := "WeierstrassCurve.Affine.Point.instAddCommGroup")
The set $`E(F)` of affine points (including $`\mathcal{O}`) of an elliptic curve $`E`
over a field $`F` is an abelian group under the chord-and-tangent addition law, with
$`\mathcal{O}` as the identity element.
:::

:::proof "affine-points-abelian-group"
Commutativity and the identity axioms follow directly from the geometric definition of
the chord-and-tangent rule. Associativity — the most demanding property — is established
via an injective group homomorphism into the ideal class group of the affine coordinate
ring $`F[E] = F[X, Y]/\langle W(X,Y) \rangle` ({uses "affine-point"}[]). Specifically,
one maps $`\mathcal{O}` to the trivial class and a point $`(x, y)` to the class of the
invertible ideal $`\langle X - x,\, Y - y \rangle \subseteq F[E]`. The coordinate ring
$`F[E]` is a free rank-two $`F[X]`-module with basis $`\{1, Y\}`, and a degree argument
for the algebra norm shows injectivity. Associativity then inherits from the abelian group
structure of the ideal class group.
:::

# Division polynomials

:::definition "division-polynomial-psi" (lean := "WeierstrassCurve.ψ")
For an integer $`n`, the *$`n`-th division polynomial* $`\psi_n \in R[X, Y]` of a
Weierstrass curve $`W` over $`R` is defined by the recurrence of a normalised
elliptic divisibility sequence with initial values
$$`\psi_0 = 0,\quad \psi_1 = 1,\quad \psi_2 = 2Y + a_1 X + a_3,`
$$`\psi_3 = 3X^4 + b_2 X^3 + 3b_4 X^2 + 3b_6 X + b_8,`
and $`\psi_4 = \psi_2 \cdot (2X^6 + b_2 X^5 + 5b_4 X^4 + 10b_6 X^3 + 10b_8 X^2 +
(b_2 b_8 - b_4 b_6) X + (b_4 b_8 - b_6^2))`.
The associated polynomials $`\Phi_n \in R[X]` and $`\phi_n \in R[X, Y]` are defined by
$$`\Phi_n = X \Psi_n^2 - \psi_{n+1} \psi_{n-1},\quad
\phi_n = ({\psi_{2n}}/{\psi_n} - \psi_n(a_1 \Phi_n + a_3 \Psi_n^2)) / 2,`
where $`\Psi_n` is a companion sequence congruent to $`\psi_n` modulo the Weierstrass
polynomial.
:::

:::definition "division-polynomial-Psi" (lean := "WeierstrassCurve.Ψ")
The *normalised companion sequence* $`\Psi_n \in R[X, Y]` is defined from the
univariate polynomials $`\mathrm{pre}\Psi_n \in R[X]` by
$$`\Psi_n = \begin{cases} \mathrm{pre}\Psi_n \cdot \psi_2 & n \text{ even,} \\
                           \mathrm{pre}\Psi_n              & n \text{ odd.} \end{cases}`
The sequence $`\mathrm{pre}\Psi_n` satisfies the same EDS recurrence as $`\psi_n`
but with the auxiliary parameter $`\Psi_2^{\,2} = 4X^3 + b_2 X^2 + 2b_4 X + b_6`
substituted for $`\psi_2^2`. In the coordinate ring $`R[E]`, $`\psi_n` and $`\Psi_n`
coincide ({uses "division-polynomial-psi"}[]).
:::

:::definition "division-polynomial-Phi" (lean := "WeierstrassCurve.Φ")
The *$`x`-coordinate companion polynomial* $`\Phi_n \in R[X]` is
$$`\Phi_n = X \cdot \Psi\!\mathrm{Sq}_n -
\mathrm{pre}\Psi_{n+1} \cdot \mathrm{pre}\Psi_{n-1} \cdot
\begin{cases} 1 & n \text{ even,} \\ \Psi_2^{\,2} & n \text{ odd,} \end{cases}`
where $`\Psi\!\mathrm{Sq}_n = \mathrm{pre}\Psi_n^2 \cdot \Psi_2^{\,2}` (even) or
$`\mathrm{pre}\Psi_n^2` (odd). In the coordinate ring, $`\Phi_n` coincides with $`\phi_n`
({uses "division-polynomial-Psi"}[]).
:::
