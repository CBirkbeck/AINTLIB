import Verso
import VersoManual
import VersoBlueprint

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elliptic Curves and Arithmetic Geometry" =>

This chapter follows mathlib's development of elliptic curves through the `WeierstrassCurve`
API: the Weierstrass equation and its standard quantities $`b_i, c_4, c_6`, the discriminant
$`\Delta`, the $`j`-invariant, the admissible change of variables and the normal forms it
produces, models realising any prescribed $`j`-invariant, the isomorphism criterion over a
separably closed field, the affine Weierstrass equation together with the chord-and-tangent
group law and its associativity via the ideal class group of the affine coordinate ring, maps
and base change, reduction of a curve over a local field, the division polynomials and the
elliptic divisibility sequences underpinning them, and the local and global $`L`-functions.
The mathlib-backed nodes carry a `(lean := …)` reference naming the exact declaration, and
their proof sketches follow the argument that declaration actually uses, naming the lemmas it
invokes. Throughout, $`R` denotes a commutative ring, $`F` a field, $`W` a Weierstrass curve
over $`R`, $`\Delta` its discriminant, $`j` its $`j`-invariant, and $`W(F)` the group of
nonsingular affine points over $`F`. In mathlib there is no bundled `EllipticCurve` structure
in this part of the library: a Weierstrass curve is *elliptic* exactly when it satisfies the
typeclass `WeierstrassCurve.IsElliptic`, that is, when $`\Delta` is a unit.

The closing sections record headline results from three external Lean projects — the
**Nagell–Lutz theorem** (`Nagel--Lutz`), the **Hasse bound** (`Hasse-Weil`), and the **Weil
conjectures** (`WeilConjectures`) — which target mathlib versions incompatible with this
blueprint's toolchain and so carry no `(lean := …)` reference; each names its repository,
states whether the formalisation is sorry-free or in progress, and connects into the
dependency graph through the mathlib-backed nodes. The `Hasse-Weil` and `WeilConjectures`
source links point to **private repositories and require access**; the permalinks are recorded
against their commits for provenance even though they will not resolve publicly. A final
section gathers informal statements of results that are the subject of open mathlib pull
requests.

# Weierstrass equations and the discriminant

:::definition "weierstrass-curve" (lean := "WeierstrassCurve")
A *Weierstrass curve* over a commutative ring $`R` is the plane cubic
$$`Y^2 + a_1 XY + a_3 Y \;=\; X^3 + a_2 X^2 + a_4 X + a_6,`
specified by the tuple of coefficients $`(a_1, a_2, a_3, a_4, a_6) \in R^5`. In mathlib this is
the structure `WeierstrassCurve R` with fields `a₁, a₂, a₃, a₄, a₆`.
:::

:::definition "weierstrass-quantities" (lean := "WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.c₄, WeierstrassCurve.c₆")
From the coefficients of a Weierstrass curve $`W` ({uses "weierstrass-curve"}[]) one forms the
*standard quantities*
$$`b_2 = a_1^2 + 4a_2,\quad b_4 = 2a_4 + a_1 a_3,\quad b_6 = a_3^2 + 4a_6,`
$$`b_8 = a_1^2 a_6 + 4a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2,`
and the higher invariants
$$`c_4 = b_2^2 - 24 b_4,\qquad c_6 = -b_2^3 + 36 b_2 b_4 - 216 b_6.`
These satisfy the relation $`4 b_8 = b_2 b_6 - b_4^2` (`WeierstrassCurve.b_relation`).
:::

:::definition "weierstrass-discriminant" (lean := "WeierstrassCurve.Δ")
The *discriminant* of a Weierstrass curve $`W` over $`R` is built from the standard quantities
$`b_2, b_4, b_6, b_8` ({uses "weierstrass-quantities"}[]):
$$`\Delta \;=\; -b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6 \;\in\; R.`
If $`R` is a field then $`\Delta = 0` exactly when the cubic curve is singular. (The sign
convention is the one used by the LMFDB.)
:::

:::lemma_ "c-relation" (lean := "WeierstrassCurve.c_relation")
The discriminant is tied to the higher invariants $`c_4, c_6` ({uses "weierstrass-quantities"}[])
by the identity
$$`1728\,\Delta \;=\; c_4^3 - c_6^2,`
holding in any commutative ring $`R`.
:::

:::proof "c-relation"
Both sides are polynomials in the coefficients $`a_i`. Unfolding $`\Delta`
({uses "weierstrass-discriminant"}[]), $`c_4`, $`c_6`, and the $`b_i` to their definitions in
the $`a_i` reduces the claim to a single polynomial identity, which mathlib closes with the
`ring1` tactic (after a `simp only` expanding the definitions). The same expand-and-`ring1`
mechanism proves the companion relation $`4 b_8 = b_2 b_6 - b_4^2`.
:::

:::definition "is-elliptic" (lean := "WeierstrassCurve.IsElliptic")
A Weierstrass curve $`W` over $`R` is *elliptic* if its discriminant $`\Delta`
({uses "weierstrass-discriminant"}[]) is a unit in $`R`. In mathlib this is the typeclass
`WeierstrassCurve.IsElliptic`, a one-field class asserting `IsUnit W.Δ`; over a field it is
equivalent to $`\Delta \ne 0`, i.e. nonsingularity of the cubic. When $`W` is elliptic one
writes $`\Delta'` for the chosen unit lifting $`\Delta` (`WeierstrassCurve.Δ'`).
:::

:::definition "two-torsion-polynomial" (lean := "WeierstrassCurve.twoTorsionPolynomial")
The *2-torsion polynomial* of a Weierstrass curve $`W` ({uses "weierstrass-curve"}[]) is the
cubic
$$`4X^3 + b_2 X^2 + 2 b_4 X + b_6 \;\in\; R[X],`
recorded in mathlib as the `Cubic` with coefficients $`(4, b_2, 2b_4, b_6)`. Over a field of
characteristic $`\ne 2`, its roots over a splitting field are exactly the $`X`-coordinates of
the nonzero $`2`-torsion points of $`W`.
:::

:::lemma_ "two-torsion-discriminant" (lean := "WeierstrassCurve.twoTorsionPolynomial_discr")
The cubic discriminant of the 2-torsion polynomial ({uses "two-torsion-polynomial"}[]) is a
constant multiple of the curve discriminant:
$$`\mathrm{disc}(4X^3 + b_2 X^2 + 2 b_4 X + b_6) \;=\; 16\,\Delta.`
In particular, over a field where $`2` is a unit, $`\Delta` is a unit iff this discriminant is
({uses "weierstrass-discriminant"}[]), so $`\Delta \ne 0` exactly when the 2-torsion polynomial
is separable.
:::

:::proof "two-torsion-discriminant"
This is a polynomial identity in the coefficients $`a_i`. Expanding `Cubic.discr` of the cubic
$`(4, b_2, 2b_4, b_6)` and the definition of $`\Delta` ({uses "weierstrass-discriminant"}[]),
the two sides agree by `ring1`; the constant $`16 = 2^4` reflects the leading coefficient $`4`.
The unit equivalence `twoTorsionPolynomial_discr_isUnit` then follows by factoring
$`16 = 2^4` out of the product and using that a power of the unit $`2` is a unit.
:::

# The j-invariant

:::definition "j-invariant" (lean := "WeierstrassCurve.j")
Let $`W` be an elliptic curve over $`R`, so its discriminant $`\Delta`
({uses "is-elliptic"}[]) is a unit with chosen lift $`\Delta'`. The *$`j`-invariant* of $`W` is
$$`j \;=\; \Delta'^{-1} \cdot c_4^3 \;\in\; R,`
with $`c_4` the higher invariant of $`W` ({uses "weierstrass-quantities"}[]).
:::

:::lemma_ "j-zero-criterion" (lean := "WeierstrassCurve.j_eq_zero_iff")
For an elliptic curve $`W` over a reduced ring $`R`, the $`j`-invariant
({uses "j-invariant"}[]) vanishes precisely when $`c_4` does:
$$`j = 0 \iff c_4 = 0.`
:::

:::proof "j-zero-criterion"
Since $`\Delta'` is a unit, $`j = \Delta'^{-1} c_4^3 = 0` is equivalent to $`c_4^3 = 0`
(`Units.mul_right_eq_zero`). In a reduced ring $`c_4^3 = 0 \iff c_4 = 0` by
`pow_eq_zero_iff` with exponent $`3 \ne 0`. This is mathlib's `j_eq_zero_iff`; without the
reducedness hypothesis one only gets the variant $`j = 0 \iff c_4^3 = 0`.
:::

# Change of variables and normal forms

:::definition "variable-change" (lean := "WeierstrassCurve.VariableChange")
An *admissible change of variables* over $`R` is a tuple $`(u, r, s, t)` with $`u \in R^\times`
and $`r, s, t \in R`, acting on coordinates by
$$`(X, Y) \;\longmapsto\; (u^2 X + r,\; u^3 Y + u^2 s X + t).`
In mathlib this is the structure `WeierstrassCurve.VariableChange`; such tuples form a group
under composition (matrix multiplication of the corresponding affine matrices) and act on
Weierstrass curves $`W` ({uses "weierstrass-curve"}[]) by the scalar action $`C \bullet W`,
which is a `MulAction`.
:::

:::lemma_ "variable-change-quantities" (lean := "WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_Δ")
Under a change of variables $`C = (u, r, s, t)` ({uses "variable-change"}[]), the higher
invariant $`c_4` and the discriminant $`\Delta` ({uses "weierstrass-discriminant"}[]) scale by
powers of $`u`:
$$`c_4(C \bullet W) = u^{-4}\, c_4(W),\qquad \Delta(C \bullet W) = u^{-12}\, \Delta(W).`
In particular an elliptic curve stays elliptic after a change of variables.
:::

:::proof "variable-change-quantities"
mathlib computes the transformed coefficients $`(C \bullet W).a_i` from `variableChange_def`,
then the transformed $`b_i` (`variableChange_b₂`, …, `variableChange_b₈`) — each a polynomial
identity proved by `ring1` after substituting the $`a_i` formulae. Feeding these into the
definitions of $`c_4` and $`\Delta` ({uses "weierstrass-quantities"}[]) and applying `ring1`
again gives the displayed scalings. The instance `(C • W).IsElliptic` then follows because
$`u^{-12}` is a unit and the product of units is a unit ({uses "is-elliptic"}[]).
:::

:::theorem "j-invariant-under-variable-change" (lean := "WeierstrassCurve.variableChange_j")
The $`j`-invariant is invariant under every admissible change of variables: for any
$`C` ({uses "variable-change"}[]),
$$`j(C \bullet W) \;=\; j(W).`
:::

:::proof "j-invariant-under-variable-change"
By the previous lemma ({uses "variable-change-quantities"}[]) one has
$`c_4(C \bullet W) = u^{-4} c_4(W)` and $`\Delta(C \bullet W)' = u^{-12}\Delta(W)'`, so
$`(C \bullet W)\,\Delta'^{-1} = u^{12} \Delta'^{-1}`. Substituting into
$`j = \Delta'^{-1} c_4^3` ({uses "j-invariant"}[]) gives the factor
$`u^{12} \cdot (u^{-4})^3 = u^{12} u^{-12} = 1`, so $`j` is unchanged. This is mathlib's
`variableChange_j`, proved by rewriting with `coe_inv_variableChange_Δ'` and
`variableChange_c₄` and cancelling the powers of $`u`.
:::

:::definition "short-weierstrass" (lean := "WeierstrassCurve.IsShortNF")
A Weierstrass curve is in *short normal form* if $`a_1 = a_2 = a_3 = 0`, i.e. it is
$$`Y^2 = X^3 + a_4 X + a_6.`
mathlib records this as the typeclass `WeierstrassCurve.IsShortNF`; for such a curve
$`\Delta = -16(4 a_4^3 + 27 a_6^2)` ({uses "weierstrass-discriminant"}[]) and, over a field,
$`j = 6912\, a_4^3/(4 a_4^3 + 27 a_6^2)` ({uses "j-invariant"}[]). It is the normal form in
characteristic $`\ne 2, 3` (and also in characteristic $`3` with $`j = 0`). mathlib also
provides the characteristic-2 and characteristic-3 normal forms (`IsCharTwoNF`,
`IsCharThreeNF`) and the intermediate `IsCharNeTwoNF` $`Y^2 = X^3 + a_2 X^2 + a_4 X + a_6`.
:::

:::theorem "exists-short-weierstrass" (lean := "WeierstrassCurve.exists_variableChange_isShortNF")
If $`2` and $`3` are units in $`R` (for instance over a field of characteristic $`\ne 2, 3`),
then every Weierstrass curve can be put in short normal form
({uses "short-weierstrass"}[]): there is a change of variables $`C`
({uses "variable-change"}[]) with $`C \bullet W` of the form $`Y^2 = X^3 + a_4 X + a_6`.
:::

:::proof "exists-short-weierstrass"
mathlib exhibits the change of variables explicitly. First `toCharNeTwoNF`, with parameter
$`s = \tfrac12(-a_1)`, $`t = \tfrac12(-a_3)`, completes the square in $`Y` to kill $`a_1, a_3`,
giving `IsCharNeTwoNF`. Composing with a translation in $`X` by $`r = \tfrac13(-a_2 \cdots)`
(the `toShortNF` change of variables, valid since $`3` is invertible) then removes $`a_2`. The
instance `toShortNF_spec` checks that the resulting curve satisfies `IsShortNF`, and
`exists_variableChange_isShortNF` packages the witness. The analogous statements in
characteristics $`2` and $`3` produce the corresponding normal forms.
:::

# Models with prescribed j-invariant

:::definition "models-with-j" (lean := "WeierstrassCurve.ofJ0, WeierstrassCurve.ofJ1728, WeierstrassCurve.ofJNe0Or1728, WeierstrassCurve.ofJ")
For a field $`F` and $`j \in F`, mathlib builds an explicit Weierstrass curve
({uses "weierstrass-curve"}[]) realising $`j`. The building blocks are
$$`\mathrm{ofJ0}: Y^2 + Y = X^3 \;(\Delta = -27),\qquad \mathrm{ofJ1728}: Y^2 = X^3 + X \;(\Delta = -64),`
$$`\mathrm{ofJNe0Or1728}(j): Y^2 + (j-1728)XY = X^3 - 36(j-1728)^3 X - (j-1728)^5,`
the last having $`\Delta = j^2(j-1728)^9` and $`c_4 = j(j-1728)^3`. The combined definition
$`\mathrm{ofJ}(j)` selects among these by cases on whether $`j = 0`, $`j = 1728`, and on the
characteristic, and is elliptic ({uses "is-elliptic"}[]) for every $`j`.
:::

:::theorem "j-surjective" (lean := "WeierstrassCurve.ofJ_j")
Every element of a field is the $`j`-invariant of an elliptic curve: for all $`j \in F`,
$$`j(\mathrm{ofJ}(j)) \;=\; j`
({uses "j-invariant"}[], {uses "models-with-j"}[]).
:::

:::proof "j-surjective"
The proof is by the case split defining $`\mathrm{ofJ}`. When $`j \ne 0, 1728` one computes
$`j(\mathrm{ofJNe0Or1728}(j)) = \Delta'^{-1} c_4^3 = (j^2(j-1728)^9)^{-1}(j(j-1728)^3)^3 = j`
by `ring1`, using that $`j` and $`j - 1728` are units (`ofJNe0Or1728_j`). The exceptional
values use `ofJ0_j` ($`j = 0`, valid when $`3` is a unit) and `ofJ1728_j` ($`j = 1728`, valid
when $`2` is a unit), with the small-characteristic degeneracies (where $`0` and $`1728`
coincide with each other or where $`\mathrm{ofJ0}` and $`\mathrm{ofJ1728}` swap roles) handled
by the lemmas `ofJ_0_of_three_eq_zero`, `ofJ_1728_of_two_eq_zero`, and their kin.
:::

:::theorem "isom-of-j" (lean := "WeierstrassCurve.exists_variableChange_of_j_eq")
*(Isomorphism criterion via the $`j`-invariant.)* Let $`E` and $`E'` be elliptic curves over a
separably closed field $`F`. If $`j(E) = j(E')` ({uses "j-invariant"}[]), then there is a change
of variables $`C` ({uses "variable-change"}[]) over $`F` with $`C \bullet E = E'`.
:::

:::proof "isom-of-j"
mathlib splits on the characteristic of $`F` (`CharP.exists`). In characteristic $`\ne 2, 3`
it reduces both curves to short normal form ({uses "exists-short-weierstrass"}[]) by a `wlog`,
so each is $`Y^2 = X^3 + a_4 X + a_6`; the hypothesis $`j(E) = j(E')` becomes
$`a_4^3 a_6'^2 = a_4'^3 a_6^2`, and using that $`F` is separably closed one extracts a unit
$`u` with $`u^4 = a_4/a_4'` and $`u^6 = a_6/a_6'` (via `IsSepClosed.exists_pow_nat_eq`), so
$`(u,0,0,0)` is the required change of variables — with separate branches for $`a_4 = 0` and
$`a_6 = 0`. In characteristic $`2` and $`3` the same strategy runs through the corresponding
normal forms ({uses "short-weierstrass"}[]): one places both curves in the $`j = 0` or
$`j \ne 0` normal form, then solves for the change-of-variables parameters using
separable-closedness (`IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C'`).
:::

# Affine points and the Weierstrass equation

:::definition "affine-equation" (lean := "WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.Nonsingular")
Working in affine coordinates with the polynomial
$$`W(X, Y) := Y^2 + a_1 XY + a_3 Y - (X^3 + a_2 X^2 + a_4 X + a_6),`
a pair $`(x, y) \in R^2` *satisfies the Weierstrass equation* of $`W`
({uses "weierstrass-curve"}[]) if $`W(x, y) = 0` (the predicate
`WeierstrassCurve.Affine.Equation`), and is *nonsingular* if in addition the partial
derivatives $`W_X(x, y)` and $`W_Y(x, y)` do not both vanish
(`WeierstrassCurve.Affine.Nonsingular`).
:::

:::lemma_ "equation-iff-nonsingular" (lean := "WeierstrassCurve.Affine.equation_iff_nonsingular")
Over a field, an elliptic curve has no singular points: if $`W` is elliptic
({uses "is-elliptic"}[]), then for all $`x, y`,
$$`W.\mathrm{Equation}(x, y) \iff W.\mathrm{Nonsingular}(x, y)`
({uses "affine-equation"}[]).
:::

:::proof "equation-iff-nonsingular"
It suffices to prove the statement under the weaker hypothesis $`\Delta \ne 0`
(`equation_iff_nonsingular_of_Δ_ne_zero`), since for an elliptic curve $`\Delta`, being a unit,
is nonzero ({uses "is-elliptic"}[]). For that, mathlib reduces via the translation
$`(1, x, 0, y)` to the point at the origin (`equation_iff_nonsingular_zero` after
`nonsingular_iff_variableChange`), where the nonsingularity condition unwinds explicitly: if
$`(0,0)` lay on the curve but were singular then $`a_3 = a_4 = a_6 = 0`, forcing $`\Delta = 0`,
contradiction.
:::

:::definition "group-law-formulae" (lean := "WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY")
The chord-and-tangent operations are given by explicit formulae. The negation of $`(x, y)` has
$`Y`-coordinate
$$`\mathrm{negY}(x, y) = -y - a_1 x - a_3.`
For two points the *slope* of the connecting line is
$$`\mathrm{slope}(x_1, x_2, y_1, y_2) = \begin{cases}
  \dfrac{y_1 - y_2}{x_1 - x_2} & x_1 \ne x_2,\\[1ex]
  \dfrac{3 x_1^2 + 2 a_2 x_1 + a_4 - a_1 y_1}{y_1 - \mathrm{negY}(x_1, y_1)} & x_1 = x_2,\ y_1 \ne \mathrm{negY}(x_1, y_1),
\end{cases}`
and the sum $`(x_1, y_1) + (x_2, y_2)` has
$$`\mathrm{addX} = \ell^2 + a_1 \ell - a_2 - x_1 - x_2,\qquad
  \mathrm{addY} = \mathrm{negY}(\mathrm{addX}, \ell(\mathrm{addX} - x_1) + y_1),`
where $`\ell` is the slope. mathlib proves these preserve nonsingularity
(`nonsingular_neg`, `nonsingular_add`, {uses "affine-equation"}[]).
:::

# The coordinate ring and the group law

:::definition "coordinate-ring" (lean := "WeierstrassCurve.Affine.CoordinateRing")
The *affine coordinate ring* of a Weierstrass curve $`W` ({uses "weierstrass-curve"}[]) is
$$`R[W] := R[X, Y]/\langle W(X, Y)\rangle,`
realised in mathlib as `AdjoinRoot W.polynomial` ({uses "affine-equation"}[]). It is a free
rank-two module over $`R[X]` with the *power basis* $`\{1, Y\}`
(`WeierstrassCurve.Affine.CoordinateRing.basis`), so every element is $`p + qY` with
$`p, q \in R[X]`; its fraction field is the *function field* $`R(W)`.
:::

:::lemma_ "coordinate-ring-domain"
If $`R` is an integral domain, then the affine coordinate ring $`R[W]`
({uses "coordinate-ring"}[]) is an integral domain (a mathlib `instance`).
:::

:::proof "coordinate-ring-domain"
The defining polynomial $`W(X, Y)`, viewed in $`R[X][Y]`, is irreducible
(`irreducible_polynomial`): over the fraction field of $`R` it is a monic quadratic in $`Y`
with no root in $`R(X)`, hence irreducible, and one transfers irreducibility down along the
injective base-change map. Since $`R[W]` over the fraction field is then `AdjoinRoot` of a prime
element, it is a domain (`AdjoinRoot.isDomain_of_prime`), and the injective ring map
$`R[W] \hookrightarrow (W_{\mathrm{Frac}\,R})[W]` (`CoordinateRing.map_injective`) carries the
domain property back, giving `instIsDomainCoordinateRing`.
:::

:::lemma_ "coordinate-ring-norm-degree" (lean := "WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis")
For $`p, q \in R[X]` over a domain, the $`R[X]`-algebra norm of $`p + qY \in R[W]`
({uses "coordinate-ring"}[]) is
$$`N(p + qY) = p^2 - p q (a_1 X + a_3) - q^2(X^3 + a_2 X^2 + a_4 X + a_6),`
of degree $`\max(2\deg p,\ 2\deg q + 3)`. Consequently the norm never has degree $`1`.
:::

:::proof "coordinate-ring-norm-degree"
The norm is computed as the determinant of left multiplication in the power basis
$`\{1, Y\}` ({uses "coordinate-ring"}[]): `norm_smul_basis` evaluates this $`2 \times 2`
determinant using $`Y^2 \equiv (X^3 + \cdots) - (a_1 X + a_3)Y` in $`R[W]`, giving the displayed
quadratic. For the degree, the leading terms of $`p^2` and of
$`q^2(X^3 + \cdots)` have degrees $`2\deg p` and $`2\deg q + 3`, while the cross term
$`p q(a_1 X + a_3)` is dominated by their maximum; `degree_norm_smul_basis` does the case
analysis on whether $`p` or $`q` vanishes and which leading term wins. Since the two competing
degrees are even and $`\equiv 3 \pmod 2`, their maximum is never $`1`, which is
`degree_norm_ne_one`.
:::

:::definition "affine-point" (lean := "WeierstrassCurve.Affine.Point")
The type $`W(F)` of *nonsingular affine points* of a Weierstrass curve $`W` over a field $`F`
is the inductive with two constructors: the distinguished *point at infinity* $`\mathcal{O}`,
and affine points $`(x, y)` together with a proof that $`(x, y)` is nonsingular
({uses "affine-equation"}[]). When $`W` is elliptic the nonsingularity proof is automatic for
any solution ({uses "equation-iff-nonsingular"}[]).
:::

:::theorem "affine-points-abelian-group" (lean := "WeierstrassCurve.Affine.Point.instAddCommGroup")
The set $`W(F)` of nonsingular affine points (including $`\mathcal{O}`) of a Weierstrass curve
$`W` over a field $`F` ({uses "affine-point"}[]) is an abelian group under the chord-and-tangent
addition law ({uses "group-law-formulae"}[]), with $`\mathcal{O}` as identity and negation
$`-(x, y) = (x, \mathrm{negY}(x, y))`.
:::

:::proof "affine-points-abelian-group"
Negation is an involution and $`\mathcal{O}` is an identity by direct case analysis on the
constructors. The substance is commutativity and associativity, which mathlib obtains from an
injective additive homomorphism into the ideal class group of the coordinate ring. The map
$`\mathrm{toClass}: W(F) \to \mathrm{Cl}(F[W])` ({uses "coordinate-ring"}[]) sends $`\mathcal{O}`
to $`0` and $`(x, y)` to the class of the invertible fractional ideal
$`\langle X - x, Y - y\rangle` (`XYIdeal'`). That this is additive reduces to two ideal
identities checked by explicit computation:
$`\langle X-x, Y-\mathrm{negY}\rangle \cdot \langle X-x, Y-y\rangle = \langle X-x\rangle`
(`XYIdeal_neg_mul`, giving $`\mathrm{toClass}(-P) = -\mathrm{toClass}(P)`) and a longer identity
relating the ideals of $`P`, $`Q`, and $`P + Q` (`XYIdeal_mul_XYIdeal`). Injectivity comes from
`toClass_eq_zero`: if $`\mathrm{toClass}(x, y) = 0` then $`\langle X-x, Y-y\rangle` is principal,
generated by an element whose norm — by the degree computation
({uses "coordinate-ring-norm-degree"}[]) — would have degree $`1`, which is impossible. Pulling
the commutativity, associativity, and inverse axioms back through this injection from the
abelian group $`\mathrm{Cl}(F[W])` (`add_comm`, `add_assoc`, `neg_add_cancel`, the latter via
`add_eq_zero`) gives the `AddCommGroup` instance.
:::

# Maps, base change, and reduction

:::definition "map-base-change" (lean := "WeierstrassCurve.map, WeierstrassCurve.baseChange")
For a ring homomorphism $`\phi : R \to A`, the *map* $`W.\mathrm{map}\,\phi`
({uses "weierstrass-curve"}[]) is the Weierstrass curve over $`A` obtained by applying $`\phi`
to each coefficient $`a_i`; for an $`R`-algebra $`A` the *base change* $`W_A` is
$`W.\mathrm{map}(\mathrm{algebraMap}\,R\,A)`.
:::

:::lemma_ "map-discriminant-j" (lean := "WeierstrassCurve.map_Δ, WeierstrassCurve.map_j")
Both the discriminant and the $`j`-invariant commute with maps: for $`\phi : R \to A`,
$$`\Delta(W.\mathrm{map}\,\phi) = \phi(\Delta(W)),\qquad j(W.\mathrm{map}\,\phi) = \phi(j(W))`
({uses "weierstrass-discriminant"}[], {uses "j-invariant"}[], {uses "map-base-change"}[]). In
particular an elliptic curve stays elliptic after base change ({uses "is-elliptic"}[]).
:::

:::proof "map-discriminant-j"
The $`b_i` and hence $`\Delta` are polynomials in the $`a_i` ({uses "weierstrass-quantities"}[]),
so applying $`\phi` coefficient-wise and then computing $`\Delta` agrees with computing $`\Delta`
first and applying $`\phi`, by ring-homomorphism functoriality (`map_b₂`, …, `map_Δ`, each a
`simp` with `map_simp`). For $`j`, the unit $`\Delta'` maps to $`\phi(\Delta')` and $`c_4` maps
to $`\phi(c_4)`, so $`j = \Delta'^{-1} c_4^3` ({uses "j-invariant"}[]) maps to
$`\phi(\Delta')^{-1}\phi(c_4)^3 = \phi(j)`; this is `map_j`. The instance
`(W.map f).IsElliptic` records that $`\phi(\Delta)`, the image of a unit, is a unit.
:::

:::definition "minimal-model" (lean := "WeierstrassCurve.IsIntegral, WeierstrassCurve.IsMinimal, WeierstrassCurve.reduction")
Let $`R` be a discrete valuation ring with fraction field $`K` and residue field $`\kappa`. A
Weierstrass curve $`W` over $`K` ({uses "weierstrass-curve"}[]) is *integral* (`IsIntegral`) if
it is the base change of a curve over $`R` ({uses "map-base-change"}[]), and *minimal*
(`IsMinimal`) if among all integral models reachable by a change of variables
({uses "variable-change"}[]) it maximises the valuation of $`\Delta`
({uses "weierstrass-discriminant"}[]). The *reduction* $`\widetilde{W}`
(`WeierstrassCurve.reduction`) of a minimal model is its integral model base changed to
$`\kappa`.
:::

:::theorem "exists-minimal-model" (lean := "WeierstrassCurve.exists_isIntegral, WeierstrassCurve.exists_isMinimal")
Over a discrete valuation ring $`R` with fraction field $`K`, every Weierstrass curve over $`K`
is isomorphic, by a change of variables ({uses "variable-change"}[]), to an integral one and
indeed to a minimal one ({uses "minimal-model"}[]): there exist $`C` and $`C'` with
$`C \bullet W` integral and $`C' \bullet W` minimal.
:::

:::proof "exists-minimal-model"
For integrality, mathlib scales by a single power of a uniformiser: taking $`u` to be an element
whose valuation equals the maximum of the valuations of the $`a_i`, the change of variables
$`(u, 0, 0, 0)` clears all denominators, because each transformed coefficient
$`u^{-k} a_i` then has nonnegative valuation (`exists_isIntegral`, using
`isIntegral_of_exists_lift`). For minimality, the multiplicative valuation of $`\Delta` takes
values in a well-ordered set bounded above by $`1` on integral models, so a maximiser exists
(`exists_maximalFor_of_wellFoundedGT`); translating that maximiser through the group action of
changes of variables yields a minimal model (`exists_isMinimal`).
:::

:::theorem "reduction-types" (lean := "WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction")
A minimal Weierstrass curve over the fraction field of a discrete valuation ring has exactly one
reduction type: it has *good*, *multiplicative*, or *additive* reduction
({uses "minimal-model"}[]). Good reduction (`HasGoodReduction`, $`v(\Delta) = 0`) holds exactly
when the reduction $`\widetilde{W}` is itself elliptic
({uses "is-elliptic"}[]); multiplicative reduction has $`v(\Delta) > 0`, $`v(c_4) = 0`; additive
reduction has $`v(\Delta) > 0`, $`v(c_4) > 0`.
:::

:::proof "reduction-types"
Since $`v(\Delta) \le 1` and $`v(c_4) \le 1` on a minimal integral model (the multiplicative
valuation is $`\le 1` on $`R`, `valuation_le_one`), the three classes — distinguished by whether
$`v(\Delta) = 1` and by the size of $`v(c_4)` — exhaust all possibilities, which `grind` checks
after unfolding the class predicates (`hasGoodReduction_iff` etc.). That good reduction is
equivalent to $`\widetilde{W}` being elliptic is `hasGoodReduction_iff_isElliptic_reduction`:
$`v(\Delta) = 1` says $`\Delta` is a unit in $`R` modulo the maximal ideal, i.e. its image in
$`\kappa` is nonzero, i.e. $`\widetilde{W} = W.\mathrm{map}(\mathrm{residue})` has unit
discriminant ({uses "map-discriminant-j"}[], {uses "is-elliptic"}[]). The mutual exclusions
(`HasGoodReduction.not_hasMultiplicativeReduction`, …) follow from the incompatible valuation
inequalities.
:::

# Division polynomials and elliptic divisibility sequences

:::definition "elliptic-divisibility-sequence" (lean := "IsEllSequence, IsDivSequence, normEDS")
An *elliptic sequence* is a sequence $`(W_n)_{n \in \mathbb{Z}}` in a commutative ring
(`IsEllSequence`) satisfying, for all $`m, n, r`,
$$`W_{m+n} W_{m-n} W_r^2 = W_{m+r} W_{m-r} W_n^2 - W_{n+r} W_{n-r} W_m^2,`
and a *divisibility sequence* (`IsDivSequence`) if $`m \mid n \Rightarrow W_m \mid W_n`; an *EDS*
is both. mathlib constructs the canonical *normalised* EDS `normEDS b c d` with initial values
$`W_0 = 0`, $`W_1 = 1`, $`W_2 = b`, $`W_3 = c`, $`W_4 = bd`, built from the auxiliary integer
sequence `preNormEDS (b^4) c d` (which agrees with `normEDS` at odd indices and differs by a
factor $`b` at even indices), so that ring division is never needed.
:::

:::definition "division-polynomial-psi" (lean := "WeierstrassCurve.ψ")
For an integer $`n`, the *$`n`-th division polynomial* $`\psi_n \in R[X, Y]` of a Weierstrass
curve $`W` ({uses "weierstrass-curve"}[]) is the normalised EDS
({uses "elliptic-divisibility-sequence"}[])
$$`\psi_n := \mathrm{normEDS}(\psi_2,\ C\,\Psi_3,\ C\,\mathrm{pre}\Psi_4)_n,`
with $`\psi_2 = 2Y + a_1 X + a_3` the partial derivative $`W_Y`,
$`\Psi_3 = 3X^4 + b_2 X^3 + 3 b_4 X^2 + 3 b_6 X + b_8`, and
$`\mathrm{pre}\Psi_4 = 2X^6 + b_2 X^5 + 5 b_4 X^4 + 10 b_6 X^3 + 10 b_8 X^2 + (b_2 b_8 - b_4 b_6) X + (b_4 b_8 - b_6^2)`
({uses "weierstrass-quantities"}[]). It satisfies $`\psi_0 = 0`, $`\psi_1 = 1`,
$`\psi_4 = \mathrm{pre}\Psi_4 \cdot \psi_2`, the parity $`\psi_{-n} = -\psi_n`, and the even/odd
EDS recurrences (`ψ_even`, `ψ_odd`).
:::

:::definition "division-polynomial-phi" (lean := "WeierstrassCurve.φ")
The associated *$`x`-coordinate numerators* $`\phi_n \in R[X, Y]` are
$$`\phi_n := X \cdot \psi_n^2 - \psi_{n+1}\,\psi_{n-1}`
({uses "division-polynomial-psi"}[]), so that on the curve the $`x`-coordinate of $`n \cdot P`
is $`\phi_n/\psi_n^2`. They satisfy $`\phi_0 = 1`, $`\phi_1 = X`, $`\phi_{-n} = \phi_n`.
:::

:::definition "division-polynomial-companion" (lean := "WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.preΨ, WeierstrassCurve.Ψ, WeierstrassCurve.ΨSq, WeierstrassCurve.Φ")
Because $`\psi_2^2` is congruent in $`R[W]` ({uses "coordinate-ring"}[]) to the univariate
$$`\Psi_2\mathrm{Sq} := 4X^3 + b_2 X^2 + 2 b_4 X + b_6 \in R[X]`
(the 2-torsion polynomial, {uses "two-torsion-polynomial"}[]), mathlib builds univariate
companions: $`\mathrm{pre}\Psi_n \in R[X]` as the auxiliary EDS with parameter
$`\Psi_2\mathrm{Sq}^2`, then $`\Psi_n \in R[X, Y]` equal to $`\mathrm{pre}\Psi_n \cdot \psi_2`
($`n` even) or $`\mathrm{pre}\Psi_n` ($`n` odd), the square $`\Psi\mathrm{Sq}_n`, and the
univariate $`x`-coordinate companion
$$`\Phi_n := X\,\Psi\mathrm{Sq}_n - \mathrm{pre}\Psi_{n+1}\,\mathrm{pre}\Psi_{n-1} \cdot
  \begin{cases} 1 & n \text{ even},\\ \Psi_2\mathrm{Sq} & n \text{ odd}.\end{cases}`
In $`R[W]` these companions coincide with the bivariate polynomials:
$`\psi_n \equiv \Psi_n`, $`\psi_n^2 \equiv \Psi\mathrm{Sq}_n`, and $`\phi_n \equiv \Phi_n`
({uses "division-polynomial-psi"}[], {uses "division-polynomial-phi"}[]).
:::

:::lemma_ "division-polynomial-congruence" (lean := "WeierstrassCurve.Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Affine.CoordinateRing.mk_φ")
In the coordinate ring $`R[W]` ({uses "coordinate-ring"}[]), the bivariate division polynomials
reduce to their univariate companions: the image of $`\psi_n` equals that of $`\Psi_n`, and the
image of $`\phi_n` equals that of $`C\,\Phi_n` ({uses "division-polynomial-companion"}[]).
:::

:::proof "division-polynomial-congruence"
The crux is $`\psi_2^2 \equiv \Psi_2\mathrm{Sq}` in $`R[W]`: indeed
$`C(\Psi_2\mathrm{Sq}) = \psi_2^2 - 4\,W(X,Y)`, and $`W(X,Y)` maps to $`0` in $`R[W]`
({uses "affine-equation"}[]), giving `mk_ψ₂_sq`. Since $`\psi_n` is the normalised EDS in
$`\psi_2` while $`\Psi_n`/$`\mathrm{pre}\Psi_n` is the same recurrence with $`\Psi_2\mathrm{Sq}`
substituted for $`\psi_2^2` ({uses "elliptic-divisibility-sequence"}[]), expanding both through
`normEDS`/`preNormEDS` and rewriting every $`\psi_2^2` by `mk_ψ₂_sq` identifies them
(`mk_ψ`); the same substitution applied to $`\phi_n = X\psi_n^2 - \psi_{n+1}\psi_{n-1}`
({uses "division-polynomial-phi"}[]) gives `mk_φ`.
:::

# The L-function of a Weierstrass curve

:::definition "local-polynomial" (lean := "WeierstrassCurve.localPolynomial")
Let $`R` be a discrete valuation ring with residue field $`\kappa` of cardinality $`q`, and
$`W` a Weierstrass curve over its fraction field ({uses "weierstrass-curve"}[]). The *local
polynomial* of $`W` is, in terms of the reduction type of the minimal model
({uses "reduction-types"}[]),
$$`\begin{cases}
  1 - a\,T + q\,T^2,\ a = q + 1 - \#\widetilde{W}(\kappa) & \text{good reduction},\\
  1 - T & \text{split multiplicative},\\
  1 + T & \text{nonsplit multiplicative},\\
  1 & \text{additive},
\end{cases}`
where $`\#\widetilde{W}(\kappa)` counts the points of the reduction
({uses "affine-points-abelian-group"}[]). The local Euler factor is the arithmetic function
obtained from the inverse power series of this polynomial.
:::

:::definition "weierstrass-l-function" (lean := "WeierstrassCurve.LFunction, WeierstrassCurve.LSeries")
For a Weierstrass curve $`W` over a number field $`K` ({uses "number-field"}[]), the
*$`L`-function* is the formal Dirichlet series given by the Euler product over the prime ideals
$`\mathfrak{p}` of $`\mathcal{O}_K` of the local factors of the base change of $`W` to the
completion $`K_{\mathfrak{p}}` ({uses "local-polynomial"}[], {uses "map-base-change"}[]):
$$`L(W, s) = \prod_{\mathfrak{p}} \frac{1}{f_{\mathfrak{p}}(\|\mathfrak{p}\|^{-s})}.`
Its associated complex Dirichlet $`L`-series ({bpref "lseries"}[]) is `WeierstrassCurve.LSeries`.
:::

# The Nagell–Lutz theorem

:::theorem "nagell-lutz"
*(Nagell–Lutz theorem.)* Let $`A, B \in \mathbb{Z}` with discriminant
$`\Delta_{A,B} = -16(4A^3 + 27B^2) \ne 0`, and let $`E` be the elliptic curve
({uses "is-elliptic"}[]) over $`\mathbb{Q}` given by $`y^2 = x^3 + Ax + B`
({uses "weierstrass-curve"}[]). If $`(x, y)` is a nonidentity rational point of finite order in
$`E(\mathbb{Q})` ({uses "affine-points-abelian-group"}[]), then there exist
$`x_0, y_0 \in \mathbb{Z}` with $`x = x_0`, $`y = y_0`, and either $`y_0 = 0` or
$`y_0^2 \mid \Delta_{A,B}`.
Formalised in [`LutzNagell`](https://github.com/CBirkbeck/LutzNagell/blob/c58fbfabb725e156e6c74790d8e0c3c7af856cee/LutzNagell/LutzNagellTheorem/Main.lean#L66):
`lutz_nagell` — sorry-free (the integrality part is `lutz_nagell_integrality`, the divisibility
part `lutz_nagell_discriminant`, both at the same file).
:::

:::proof "nagell-lutz"
The proof splits into integrality and discriminant divisibility, organised around the
predicate `IsOfFinAddOrder` for the affine point $`P = (x, y)`. For *integrality*
(`lutz_nagell_integrality_general` for a general Weierstrass model, specialised to the short
model by `lutz_nagell_integrality_short`): if the additive order of $`P` has an odd prime factor
$`p`, then a point $`Q = (m/p) \cdot P` of exact order $`p` exists, and a $`p`-adic valuation
estimate using the formal group of $`E` ({uses "weierstrass-curve"}[]) — transported through the
affine-to-Jacobian comparison `nsmul_eq_zero_affine_to_jac` — forces the coordinates of $`Q`,
and then by descent through integer multiples those of $`P`
({uses "affine-points-abelian-group"}[]), to be integers; if the order is a power of $`2`, an
order-four analysis (`integrality_of_four_dvd_order`, `integrality_of_order_four_general`)
handles the remaining case, with the short model collapsing the order-2 branch to $`y = 0`.
For *discriminant divisibility* (`lutz_nagell_discriminant` from
`lutz_nagell_discriminant_general`): writing $`\kappa_0 = 2 y_0 + a_1 x_0 + a_3` (which is
$`2 y_0` here since $`a_1 = a_3 = 0`), the integrality of $`2 \cdot P` together with a Bézout
identity expressing $`4\Delta` as a polynomial combination of $`\Psi_2\mathrm{Sq}`
({uses "division-polynomial-companion"}[]) and the doubling numerator yields
$`\kappa_0^2 \mid 4\Delta`; dividing by $`4` gives $`y_0^2 \mid \Delta_{A,B}`.
:::

# The Hasse bound

:::definition "point-count" (lean := "WeierstrassCurve.Affine.Point")
For a Weierstrass curve $`W` over a finite field $`K = \mathbb{F}_q` whose affine point type is
finite, the *point count* $`\#W(\mathbb{F}_q)` is the cardinality of the finite abelian group
$`W(\mathbb{F}_q)` ({uses "affine-points-abelian-group"}[]) of $`\mathbb{F}_q`-rational
nonsingular affine points together with the point at infinity. In `Hasse-Weil` this is
`pointCount E := Fintype.card E.Point`.
:::

:::definition "frobenius-isogeny"
For an elliptic curve $`E` ({uses "is-elliptic"}[]) over $`\mathbb{F}_q`, the *Frobenius
endomorphism* $`\pi : E \to E` acts on the function field by the $`q`-power map
$`f \mapsto f^q`; on affine points it is $`(x, y) \mapsto (x^q, y^q)`. The *trace of Frobenius*
is
$$`t = q + 1 - \#E(\mathbb{F}_q),`
so $`\#E(\mathbb{F}_q) = q + 1 - t` ({uses "point-count"}[]).
Formalised in `Hasse-Weil` (**private repo — link requires access**): `frobeniusIsog` and
`traceOfFrobenius` (`HasseWeil/Frobenius.lean#L53` and `#L359`, commit `1aa7429`) — the
Frobenius pullback $`f \mapsto f^q` is sorry-free (`frobeniusIsog_pullback_apply`), built on
`FiniteField.frobeniusAlgHom`.
:::

:::theorem "hasse-bound"
*(Hasse's theorem.)* For an elliptic curve $`E` ({uses "is-elliptic"}[]) over a finite field
$`\mathbb{F}_q` whose point set is finite, with trace of Frobenius
$`t = q + 1 - \#E(\mathbb{F}_q)` ({uses "frobenius-isogeny"}[], {uses "point-count"}[]),
$$`\bigl|\,\#E(\mathbb{F}_q) - (q + 1)\,\bigr| \;\le\; 2\sqrt{q},`
equivalently $`t^2 \le 4q`.
Formalised in `Hasse-Weil` (**private repo — link requires access**): `hasse_bound`
(`HasseWeil/HasseBound.lean#L85`, commit `1aa7429`) — in progress. The pure-algebra reduction
$`t^2 \le 4q \Rightarrow |t| \le 2\sqrt{q}` and the discriminant argument are sorry-free; two
deferred witnesses remain (each guarding a true integer statement): the non-negativity of the
degree quadratic form on $`\mathrm{End}(E)` inside `traceOfFrobenius_sq_le`
(`HasseBound.lean#L72`) and the point-count identity $`\#E(\mathbb{F}_q) = q + 1 - t` in
`pointCount_eq` (`Frobenius.lean#L331`).
:::

:::proof "hasse-bound"
Write $`\pi` for the Frobenius isogeny ({uses "frobenius-isogeny"}[]) and consider the
endomorphism $`r\pi - s` for $`r, s \in \mathbb{Z}`. The degree map on $`\mathrm{End}(E)` is a
positive semi-definite quadratic form (Silverman III.6.3), so
$$`\deg(r\pi - s) = q r^2 - t r s + s^2 \;\ge\; 0 \quad\text{for all } r, s \in \mathbb{Z}.`
The non-negativity of this binary form forces its discriminant $`\le 0`: substituting
$`r = t`, $`s = 2q` and clearing gives $`t^2 \le 4q` (`trace_sq_le_four_mul_deg`, a one-line
`nlinarith` once the form is known non-negative). Taking square roots,
$`|t| \le 2\sqrt{q}` (`abs_le_two_sqrt_of_sq_le`, using $`(2\sqrt q)^2 = 4q`). Combining with
$`\#E(\mathbb{F}_q) - (q+1) = -t` (`pointCount_eq`) yields the displayed bound (`hasse_bound`).
In the formalisation the quadratic-form non-negativity and the point-count identity are the two
remaining deferred witnesses, each parametrised so that the top-level bound is sorry-free
conditional on them (`hasse_bound_of_all_witnesses`).
:::

# The Weil conjectures and the Hasse–Weil zeta function

:::definition "hasse-weil-zeta"
For a smooth projective scheme $`X` over $`\mathbb{F}_q`, writing $`N_n = \#X(\mathbb{F}_{q^n})`
for the number of rational points over the degree-$`n` extension, the *Hasse–Weil zeta function*
is the formal power series
$$`Z(X/\mathbb{F}_q,\, t) \;=\; \exp\!\Bigl(\sum_{n \ge 1} \frac{N_n}{n}\, t^n\Bigr) \;\in\; \mathbb{Q}[\![t]\!].`
Formalised in `WeilConjectures` (**private repo — link requires access**):
`Scheme.zetaFunction` and `Scheme.zetaSeries` (`WeilConjectures/ZetaFunction.lean#L31` and
`#L39`, commit `b8464ee`) — sorry-free; defined as $`\exp` of the logarithmic series
$`\sum_n (N_n/n)\,t^n`.
:::

:::theorem "weil-conjectures"
*(Weil conjectures for smooth projective varieties over $`\mathbb{F}_q`.)* Given a Weil
cohomology theory $`H^\bullet` with Frobenius action on a smooth projective variety
$`X/\mathbb{F}_q` of pure dimension $`d`, and the Lefschetz trace formula
$`N_n = \sum_i (-1)^i \mathrm{tr}(\mathrm{Fr}^{*n} \mid H^i)`, the zeta function
({uses "hasse-weil-zeta"}[]) satisfies: **rationality**, the cohomological factorisation
$`Z \cdot \prod_{i\text{ even}} P_i = \prod_{i\text{ odd}} P_i` with
$`P_i(t) = \det(1 - t\,\mathrm{Fr}^* \mid H^i)`; the **functional equation** as Betti symmetry
$`b_i = b_{2d-i}` together with a per-polynomial duality
$`\det(\mathrm{Fr}\mid H^i)\,P_{2d-i}(t) = (-1)^{b_i}\,\mathrm{charpoly}(\mathrm{Fr}\mid H^i)(q^d t)`;
and, for curves ($`d = 1`), the **Riemann hypothesis** $`(N_n - (q^n+1))^2 \le (2g)^2 q^n`,
i.e. the Hasse–Weil bound ({uses "hasse-bound"}[]).
Formalised in `WeilConjectures` (**private repo — link requires access**): `weil_conjectures`
(`WeilConjectures/Statement.lean#L46`, commit `b8464ee`) — in progress. The functional
equation, per-polynomial duality, and curve Riemann hypothesis are derived from the Weil
cohomology axioms; the rationality bridge carries the two remaining sorries
(`RationalityBridge.lean#L181`, `#L205`: a chain-rule step for the formal $`\exp`-substitution
and the ODE-uniqueness identification of the geometric and cohomological zeta series).
:::

:::proof "weil-conjectures"
The argument is an abstract deduction from the axioms of a Weil cohomology theory $`W` with
Frobenius data $`F` (`abstract_weil_conjectures`). **Rationality**: the Lefschetz trace formula
turns $`\log Z = \sum_n N_n t^n/n` into $`\sum_i (-1)^i \log\det(1 - t\,\mathrm{Fr}^*\mid H^i)^{-1}`;
both $`Z \cdot \prod P_{\text{even}}` and $`\prod P_{\text{odd}}` satisfy the same linear ODE
with matching initial value, and ODE uniqueness (`ode_unique`) identifies them — this is the
`rationality_bridge`, whose two analytic steps remain deferred. **Functional equation**: the
Poincaré pairing $`H^i \times H^{2d-i} \to K` is nondegenerate (`poincare_left`,
`poincare_right`), so $`\dim H^i = \dim H^{2d-i}`, i.e. $`b_i = b_{2d-i}`
(`abstract_functional_equation`), and the duality of charpolys is `per_polynomial_duality`.
**Curve Riemann hypothesis**: for $`d = 1` the bound is packaged as the hypothesis `CurveRH`
(the Hodge-index input on the surface $`X \times X`), and `abstract_curve_rh` reads off
$`(N_n - (q^n+1))^2 \le (2g)^2 q^n`, the Hasse–Weil bound ({uses "hasse-bound"}[]) for all $`n`.
:::

:::lemma_ "hasse-weil-zeta-rational-for-EC"
For an elliptic curve $`E` ({uses "is-elliptic"}[]) over $`\mathbb{F}_q`, the Hasse–Weil zeta
function ({uses "hasse-weil-zeta"}[]) is explicitly rational:
$$`Z(E/\mathbb{F}_q,\, t) \;=\; \frac{1 - t_0\, t + q\, t^2}{(1-t)(1-qt)},`
with $`t_0 = q + 1 - \#E(\mathbb{F}_q)` the trace of Frobenius
({uses "frobenius-isogeny"}[], {uses "point-count"}[]).
:::

:::proof "hasse-weil-zeta-rational-for-EC"
This is the $`d = 1` case of the cohomological factorisation ({uses "weil-conjectures"}[]). The
denominator $`(1-t)(1-qt)` is $`P_0(t) P_2(t)` for the degree-$`0` and degree-$`2` cohomology,
whose Frobenius eigenvalues are $`1` and $`q`. The numerator $`1 - t_0 t + q t^2` is
$`P_1(t) = \det(1 - t\,\mathrm{Fr}^* \mid H^1(E))`, of trace $`t_0` and determinant $`q` (the
Weil pairing). The Riemann hypothesis for curves, equivalently the roots of $`P_1` having
absolute value $`q^{-1/2}`, is the Hasse bound ({uses "hasse-bound"}[]).
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib pull
requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing at the
live PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the mathlib-backed nodes of this
chapter via `{uses}` edges, and should be re-pointed to `(lean := …)` once the corresponding PR
merges.

:::theorem "eds-characterisation" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/13057")
*(Characterisation of elliptic divisibility sequences.)* An elliptic divisibility sequence
({uses "elliptic-divisibility-sequence"}[]) $`(W_n)` with $`W_0 = 0`, $`W_1 = 1` is determined
by its initial values together with the two even/odd duplication recurrences (in $`W_{2n+1}` and
$`W_{2n}`); equivalently, the full elliptic recurrence is *equivalent* to that pair. The division
polynomials $`\psi_n` of a Weierstrass curve ({uses "division-polynomial-psi"}[]) form the
universal EDS, and evaluating an EDS along a point records the denominators of its multiples on
the curve ({uses "affine-points-abelian-group"}[]).

PR #13057 characterises EDS via the even–odd recursion, the algebraic backbone for working with
division polynomials and torsion.
In review — [mathlib PR #13057](https://github.com/leanprover-community/mathlib4/pull/13057).
:::

:::definition "newton-polygon-mathlib" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/38050")
Mathlib's *Newton polygon* of a polynomial (or power series) $`f = \sum_i a_i X^i` over a
valued field ({uses "valuation"}[]) is the lower convex hull of the points $`(i, v(a_i))` for
$`a_i \ne 0`. The slopes of its edges record the valuations of the roots: an edge of slope $`m`
and horizontal length $`\ell` corresponds to $`\ell` roots of valuation $`-m`.

PR #38050 introduces the Newton-polygon API in mathlib itself — the same combinatorial object
developed for $`p`-adic power series in the `NewtonPolys` project ({bpref "newton-polygon"}[]);
once merged it supplies the in-library foundation for ramification, factorisation of $`p`-adic
polynomials, and slope decompositions of elliptic-curve formal groups.
In review — [mathlib PR #38050](https://github.com/leanprover-community/mathlib4/pull/38050).
:::

:::theorem "northcott-property" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/39744")
*(Northcott property.)* Equip the algebraic numbers with the absolute Weil height $`H`. For
every pair of real bounds $`B \ge 0` and $`D \ge 1`, the set
$$`\{\, \alpha \in \overline{\mathbb{Q}} \;:\; H(\alpha) \le B \ \text{ and } \ [\mathbb{Q}(\alpha):\mathbb{Q}] \le D \,\}`
is finite; in particular a number field ({uses "number-field"}[]) has only finitely many
elements of bounded height.

This finiteness is the engine behind the Mordell–Weil theorem and the finiteness of
bounded-height rational points on an elliptic curve ({bpref "affine-points-abelian-group"}[]).
PR #39744 establishes the Northcott property for the height on number fields.
In review — [mathlib PR #39744](https://github.com/leanprover-community/mathlib4/pull/39744).
:::
