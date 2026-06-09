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
The *discriminant* of a Weierstrass curve $`E` over $`R` ({uses "weierstrass-curve"}[]) is
built from the auxiliary quantities $`b_2, b_4, b_6, b_8` of the curve:
$$`\Delta \;=\; -b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6 \;\in R.`
If $`R` is a field, $`\Delta = 0` if and only if the cubic curve is singular. One has
the identity $`1728\,\Delta = c_4^3 - c_6^2`, relating the discriminant to the higher
invariants $`c_4` and $`c_6`.
:::

:::definition "is-elliptic" (lean := "WeierstrassCurve.IsElliptic")
A Weierstrass curve $`E` over $`R` is *elliptic* if its discriminant $`\Delta`
({uses "weierstrass-discriminant"}[]) is a unit in $`R`. When $`R` is a field this is
equivalent to $`\Delta \ne 0`, i.e. the cubic is nonsingular.
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
sides using the standard formula for the discriminant of a cubic and the definition of
the curve discriminant $`\Delta` ({uses "weierstrass-discriminant"}[]). The constant factor
$`16 = 2^4` reflects the leading coefficient $`4` of the 2-torsion polynomial.
:::

# The $`j`-invariant

:::definition "j-invariant" (lean := "WeierstrassCurve.j")
Let $`E` be an elliptic curve over $`R`, so its discriminant $`\Delta`
({uses "weierstrass-discriminant"}[]) is a unit. The *$`j`-invariant* of $`E` is
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
as $`u^{-4} c_4` and $`\Delta` scales as $`u^{-12} \Delta`. Hence the $`j`-invariant
$`j = \Delta^{-1} c_4^3` ({uses "j-invariant"}[]) is multiplied by
$`u^{12} \cdot u^{-12} = 1`, leaving $`j` unchanged.
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
Let $`W` be a Weierstrass curve over $`R` ({uses "weierstrass-curve"}[]) and let $`A` be
an $`R`-algebra. The *base change* $`W_A` is the Weierstrass curve over $`A` obtained by
applying the structure map $`R \to A` to each coefficient $`a_i`. If $`\phi : R \to S` is
any ring homomorphism one similarly forms $`W_S = W.{\rm map}(\phi)`.
:::

:::lemma_ "base-change-discriminant" (lean := "WeierstrassCurve.map_Δ")
Base change commutes with the discriminant: for any ring homomorphism $`\phi : R \to A`,
$$`\Delta(W_A) \;=\; \phi(\Delta(W)).`
In particular, if $`\Delta(W)` is a unit in $`R` then $`\Delta(W_A) = \phi(\Delta(W))`
is a unit in $`A`, so an elliptic curve remains elliptic after base change.
:::

:::proof "base-change-discriminant"
The discriminant $`\Delta` ({uses "weierstrass-discriminant"}[]) is a polynomial in the
coefficients $`a_i`, so for the base change $`W_A` ({uses "base-change"}[]), applying $`\phi`
to each coefficient and then computing $`\Delta` gives the same result as computing $`\Delta`
first and then applying $`\phi`, by ring-homomorphism functoriality.
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
Weierstrass curve $`W` over $`R` ({uses "weierstrass-curve"}[]) — whose auxiliary quantities
$`b_2, b_4, b_6, b_8` enter the initial terms below — is defined by the recurrence of a normalised
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

# Phase 3 (external projects, not yet in Mathlib)

The nodes below record headline results from three external Lean formalisation
projects. None carries `(lean := …)` because the external projects target
Mathlib versions incompatible with this blueprint's toolchain. Each node names
the repository, states whether the formalisation is sorry-free or in progress,
and connects into the dependency graph through the Mathlib-backed nodes of this
chapter.

## Nagell–Lutz theorem (Nagel--Lutz project)

:::theorem "nagell-lutz"
*(Nagell–Lutz theorem.)* Let $`A, B \in \mathbb{Z}` with discriminant
$`\Delta_{A,B} = -16(4A^3 + 27B^2) \ne 0`. Let $`E` be the elliptic curve
({uses "is-elliptic"}[]) over $`\mathbb{Q}` given by $`y^2 = x^3 + Ax + B`
({uses "weierstrass-curve"}[]). If $`(x, y)` is a nonidentity rational point
of finite order in $`E(\mathbb{Q})` ({uses "affine-points-abelian-group"}[]),
then there exist $`x_0, y_0 \in \mathbb{Z}` with $`x = x_0` and $`y = y_0`,
and either $`y_0 = 0` or $`y_0^2 \mid \Delta_{A,B}`.
Formalised in [`LutzNagell`](https://github.com/CBirkbeck/LutzNagell) (sorry-free).
:::

:::proof "nagell-lutz"
The proof divides into two parts. For *integrality*: if the torsion order has an
odd prime factor $`p`, form the point $`Q = (m/p) \cdot P` with $`p`-power
torsion; a $`p`-adic valuation argument using the formal group of $`E`
({uses "weierstrass-curve"}[]) forces the coordinates of $`Q` into $`\mathbb{Z}`,
and a descent through integer scalar multiples ({uses "affine-points-abelian-group"}[])
gives integrality of $`P` itself. If the torsion order is a power of $`2`, a
separate order-4 argument using the doubling formula handles the case.
For *discriminant divisibility*: writing $`\kappa_0 = 2y_0 + a_1 x_0 + a_3`
(which equals $`2y_0` in the short Weierstrass case), the curve equation gives
$`\kappa_0^2 = \Psi_2^2(x_0)`. Integrality of the double $`2 \cdot P` yields
$`\kappa_0^2 \mid 4\psi_3(x_0)`, and a polynomial identity
$`h(x)^2 + 4\psi_3(x) = (12x + b_2)\Psi_2^2(x)` together with a
Bézout identity $`d_1(x)\Psi_2^2(x) + d_2(x)h(x)^2 = 4\Delta` produces
$`\kappa_0^2 \mid 4\Delta`. Specialising $`a_1 = a_3 = 0` gives $`\kappa_0 = 2y_0`,
and dividing by $`4` yields $`y_0^2 \mid \Delta_{A,B}`.
:::

## Hasse–Weil bound (Hasse-Weil project)

:::definition "point-count"
For an elliptic curve $`E` ({uses "is-elliptic"}[]) over a finite field $`\mathbb{F}_q`,
the *point count* is the cardinality $`\#E(\mathbb{F}_q)` of the finite abelian group
({uses "affine-points-abelian-group"}[]) of $`\mathbb{F}_q`-rational affine points together
with the point at infinity.
:::

:::definition "frobenius-isogeny"
For an elliptic curve $`E` ({uses "is-elliptic"}[]) over $`\mathbb{F}_q`, the
*Frobenius endomorphism* $`\pi : E \to E` is the isogeny acting on coordinates
by the $`q`-power map: on affine points $`\pi(x,y) = (x^q, y^q)`. Its degree is
$`q` (Silverman III.4.6), and $`\ker(\pi - 1) = E(\mathbb{F}_q)` as sets.
The *trace of Frobenius* is
$$`t = q + 1 - \#E(\mathbb{F}_q),`
so $`\#E(\mathbb{F}_q) = q + 1 - t` ({uses "point-count"}[]).
:::

:::theorem "hasse-bound"
*(Hasse's theorem.)* For an elliptic curve $`E` ({uses "is-elliptic"}[]) over a
finite field $`\mathbb{F}_q` with trace of Frobenius $`t = q + 1 - \#E(\mathbb{F}_q)`
({uses "frobenius-isogeny"}[], {uses "point-count"}[]),
$$`\bigl|\,\#E(\mathbb{F}_q) - (q+1)\,\bigr| \;\le\; 2\sqrt{q},`
equivalently $`t^2 \le 4q`.
Formalised in [`Hasse-Weil`](https://github.com/CBirkbeck/Hasse-Weil) (in progress — the
discriminant-bound and real-algebra steps are sorry-free; two geometric deferred witnesses
remain: the quadratic-form non-negativity of the degree map on $`\mathrm{End}(E)`, and
the identification of $`\#\ker(1-\pi)` with $`\#E(\mathbb{F}_q)`).
:::

:::proof "hasse-bound"
Write the Frobenius isogeny as $`\pi` and consider the endomorphism $`r\pi - s`
for integers $`r, s`. Because the degree map on $`\mathrm{End}(E)` is a positive
semi-definite quadratic form (Silverman III.6.3), one has
$$`\deg(r\pi - s) = qr^2 - tr \cdot s + s^2 \;\ge\; 0 \quad\text{for all } r, s \in \mathbb{Z}.`
Setting $`r = t` and $`s = 2q` shows the discriminant $`t^2 - 4q \le 0`, i.e.
$`t^2 \le 4q`. The real bound $`|t| \le 2\sqrt{q}` follows by taking square roots.
The identification $`\deg(1-\pi) = \#E(\mathbb{F}_q)` rests on
$`\ker(1-\pi) = E(\mathbb{F}_q)` and separability of $`1-\pi` (for $`q \ge 2`),
which gives $`\deg(1-\pi) = \#\ker(1-\pi) = \#E(\mathbb{F}_q)`.
:::

## Hasse–Weil zeta function and Weil conjectures (WeilConjectures project)

:::definition "hasse-weil-zeta"
For a smooth projective scheme $`X` over $`\mathbb{F}_q`, write
$`N_n = \#X(\mathbb{F}_{q^n})` for the number of rational points over the
degree-$`n` extension. The *Hasse–Weil zeta function* of $`X` is the formal
power series
$$`Z(X/\mathbb{F}_q,\, t) \;=\; \exp\!\Bigl(\sum_{n \ge 1} \frac{N_n}{n}\, t^n\Bigr) \;\in\; \mathbb{Q}[\![t]\!].`
For an elliptic curve $`E` ({uses "is-elliptic"}[]) with trace of Frobenius $`t_0`
({uses "frobenius-isogeny"}[]), the zeta function takes the rational form
$$`Z(E/\mathbb{F}_q,\, t) \;=\; \frac{1 - t_0\, t + q\, t^2}{(1-t)(1-qt)}.`
:::

:::theorem "weil-conjectures"
*(Weil conjectures for smooth projective varieties over $`\mathbb{F}_q`.)* Given a
Weil cohomology theory $`H^\bullet` with Frobenius action on a smooth projective variety
$`X/\mathbb{F}_q` of pure dimension $`d`, writing $`P_i(t) = \det(1 - t\cdot \mathrm{Fr}^* \mid H^i(X))`:

(i) *Rationality*: $`Z(X/\mathbb{F}_q, t) = \prod_{i \text{ odd}} P_i(t)^{-1} \cdot \prod_{i \text{ even}} P_i(t)^{-1}`
is a ratio of polynomials in $`\mathbb{Q}(t)`.

(ii) *Functional equation*: $`Z(X/\mathbb{F}_q,\, q^{-d} t^{-1}) = \pm\, q^{d\chi/2}\, t^{\chi}\, Z(X/\mathbb{F}_q, t)`
with $`\chi` the Euler characteristic.

(iii) *Riemann hypothesis for curves* ($`d = 1`): The roots of $`P_1(t)` have
absolute value $`q^{-1/2}`, equivalently $`|\#E(\mathbb{F}_{q^n}) - (q^n+1)| \le 2g\sqrt{q^n}` for
all $`n \ge 1` ({uses "hasse-bound"}[]).
Formalised in [`WeilConjectures`](https://github.com/CBirkbeck/WeilConjectures) (in progress —
rationality, functional equation, and curve Riemann hypothesis follow from the abstract Weil
cohomology axioms; two sorries remain in the rationality bridge: the chain rule for formal
$`\exp` and the ODE uniqueness step connecting the geometric and cohomological zeta functions).
:::

:::proof "weil-conjectures"
The proof is an abstract deduction from the axioms of a Weil cohomology theory.
Rationality: the Lefschetz trace formula $`N_n = \sum_i (-1)^i \mathrm{tr}(\mathrm{Fr}^{*n} \mid H^i)` yields
$`\log Z(X,t) = \sum_n N_n t^n/n = \sum_i (-1)^i \log\det(1-t\cdot\mathrm{Fr}^*\mid H^i)^{-1}`.
Taking exponentials gives the product formula for $`Z` in terms of the $`P_i`. The ODE
$`Z'/Z = \sum_n N_n t^{n-1}` and the ODE satisfied by $`\prod P_i^{\pm 1}` both follow
the same linear ODE; ODE uniqueness with matching initial value $`Z(0)=1` identifies the two
expressions ({uses "hasse-weil-zeta"}[]). Functional equation: Poincaré duality for $`H^\bullet`
gives a perfect pairing $`H^i \times H^{2d-i} \to H^{2d} \cong K(-d)`, exchanging $`\mathrm{Fr}^*`
with $`q^d (\mathrm{Fr}^*)^{-1}`; the resulting symmetry $`P_{2d-i}(t) = (-1)^{b_i}\det(\mathrm{Fr}^*\mid H^i)\cdot P_i(q^d t)^{-1} \cdot c` is the functional equation.
Curve Riemann hypothesis: for $`d=1`, the Hodge index theorem (Weil's Castelnuovo argument)
gives positivity of the associated bilinear form, forcing all eigenvalues of $`\mathrm{Fr}^*\mid H^1`
to have absolute value $`\sqrt q`; this is the Hasse bound ({uses "hasse-bound"}[]) for all $`n`.
:::

:::lemma_ "hasse-weil-zeta-rational-for-EC"
For an elliptic curve $`E` ({uses "is-elliptic"}[]) over $`\mathbb{F}_q`, the
Hasse–Weil zeta function ({uses "hasse-weil-zeta"}[]) is explicitly rational:
$$`Z(E/\mathbb{F}_q,\, t) \;=\; \frac{1 - t_0\, t + q\, t^2}{(1-t)(1-qt)}`
with $`t_0 = q + 1 - \#E(\mathbb{F}_q)` the trace of Frobenius
({uses "frobenius-isogeny"}[], {uses "point-count"}[]).
:::

:::proof "hasse-weil-zeta-rational-for-EC"
The denominator factor $`(1-t)(1-qt)^{-1}` comes from the degree-0 and degree-2 cohomology
groups $`H^0 \cong K` and $`H^2 \cong K(-1)`, whose Frobenius eigenvalues are $`1` and $`q`
respectively. The numerator $`1 - t_0 t + q t^2` is $`P_1(t) = \det(1 - t\cdot\mathrm{Fr}^*\mid H^1(E))`,
which has trace $`t_0` and determinant $`q` (Weil pairing). The Hasse bound
({uses "hasse-bound"}[]) is equivalent to the roots of $`P_1` having absolute value
$`q^{-1/2}`, consistent with the rationality formula.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib
pull requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing
at the live PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the Mathlib-backed nodes of this
chapter (and, where noted, the Algebraic and $`p`-adic chapters) via `{uses}` edges, and should
be re-pointed to `(lean := …)` once the corresponding PR merges.

:::definition "newton-polygon-mathlib" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/38050")
Mathlib's *Newton polygon* of a polynomial (or power series) $`f = \sum_i a_i X^i` over a field
with a valuation $`v` ({uses "valuation"}[]) is the lower convex hull of the points
$`(i, v(a_i))` for $`a_i \ne 0`. The slopes of its edges record the valuations of the roots of
$`f` (counted with multiplicity), so an edge of slope $`m` and horizontal length $`\ell`
corresponds to $`\ell` roots of valuation $`-m`.

PR #38050 introduces the Newton-polygon API in mathlib itself, the same combinatorial object
developed for $`p`-adic power series in the `NewtonPolys` project
({bpref "newton-polygon"}[informal node]); once merged it supplies the in-library foundation for
ramification, factorisation of $`p`-adic polynomials, and slope decompositions of elliptic-curve
formal groups.
In review — [mathlib PR #38050](https://github.com/leanprover-community/mathlib4/pull/38050).
:::

:::theorem "elliptic-divisibility-sequence" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/13057")
*(Characterisation of elliptic divisibility sequences.)* An *elliptic divisibility sequence*
(EDS) is a sequence $`(W_n)_{n \in \mathbb{Z}}` in a commutative ring satisfying $`W_0 = 0`,
$`W_1 = 1`, and the recurrence
$$`W_{m+n}\,W_{m-n}\,W_1^2 \;=\; W_{m+1}\,W_{m-1}\,W_n^2 \;-\; W_{n+1}\,W_{n-1}\,W_m^2 \quad (m \ge n).`
The PR proves that the full elliptic recurrence is *equivalent* to the pair of even/odd
duplication recurrences (in $`W_{2n+1}` and $`W_{2n}`), so an EDS is determined by its initial
values together with these two recursions. The division polynomials $`\psi_n` of a Weierstrass
curve ({uses "division-polynomial-psi"}[]) form the universal EDS, and evaluating an EDS along a
point records the denominators of its multiples on the curve
({uses "affine-points-abelian-group"}[]).

PR #13057 characterises EDS via the even-odd recursion, the algebraic backbone for working with
division polynomials and torsion on elliptic curves.
In review — [mathlib PR #13057](https://github.com/leanprover-community/mathlib4/pull/13057).
:::

:::theorem "northcott-property" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/39744")
*(Northcott property.)* Equip the algebraic numbers with the absolute (multiplicative or
logarithmic) Weil height $`H`. The *Northcott property* states that for every pair of real bounds
$`B \ge 0` and $`D \ge 1`, the set
$$`\{\, \alpha \in \overline{\mathbb{Q}} \;:\; H(\alpha) \le B \ \text{ and } \ [\mathbb{Q}(\alpha):\mathbb{Q}] \le D \,\}`
is **finite**. In particular a number field ({uses "number-field"}[]) contains only finitely
many elements of bounded height.

This finiteness is the engine behind the Mordell–Weil theorem and the finiteness of bounded-height
rational points on an elliptic curve ({bpref "affine-points-abelian-group"}[]). PR #39744
establishes the Northcott property for the height on number fields.
In review — [mathlib PR #39744](https://github.com/leanprover-community/mathlib4/pull/39744).
:::
