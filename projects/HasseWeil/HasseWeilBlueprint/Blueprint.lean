import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import HasseWeil.Frobenius
import HasseWeil.FrobeniusIsogeny
import HasseWeil.Isogeny
import HasseWeil.Endomorphism
import HasseWeil.DualIsogeny
import HasseWeil.KernelDegree
import HasseWeil.DegreeQuadraticForm
import HasseWeil.GapSpines
import HasseWeil.Hasse.PointFix
import HasseWeil.Hasse.OneSubFrobenius
import HasseWeil.Hasse.Separability
import HasseWeil.Hasse.SumTrace
import HasseWeil.Hasse.QuadraticForm
import HasseWeil.Curves.FrobeniusFixedLocus
import HasseWeil.EC.KernelCount
import HasseWeil.EC.IsogenyKernel
import HasseWeil.WeilPairing.Discriminant
import HasseWeil.WeilPairing.DetDeg
import HasseWeil.WeilPairing.MatrixDet
import HasseWeil.WeilPairing.FrobMatrixData
import HasseWeil.WeilPairing.HasseAssembly
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
non-negativity of the degree form), discharges that geometric input two ways — through
the dual isogeny and through the Weil pairing on $`\ell`-torsion — and the capstone
`hasse_bound` is _unconditional and sorry-free_.

Each node carries a `(lean := …)` reference to the actual declaration in the
`HasseWeil` library, so Verso reads its completion status directly from Lean, and its
prose cites the corresponding numbered result in Silverman, _The Arithmetic of
Elliptic Curves_. The dependency graph at the foot of the page records the logical
spine.

# Point counts and the Frobenius endomorphism

:::definition "point-count" (lean := "HasseWeil.pointCount")
For an elliptic curve $`E` over a finite field $`K = \mathbb{F}_q` whose affine point
type is finite, the *point count* $`\#E(\mathbb{F}_q)` is the cardinality of the
finite abelian group of $`\mathbb{F}_q`-rational nonsingular affine points together
with the point at infinity. In `Hasse-Weil` this is
$$`\texttt{pointCount } E \;:=\; \operatorname{card} E.\mathrm{Point}.`
:::

:::definition "isogeny" (lean := "HasseWeil.Isogeny, HasseWeil.Isogeny.degree")
Following Silverman III.4, an _isogeny_ $`\varphi : E_1 \to E_2` is modelled by its
pullback $`\varphi^* : K(E_2) \hookrightarrow K(E_1)` on function fields (an injective
$`K`-algebra map) together with its group homomorphism $`E_1(K) \to E_2(K)` on rational
points. Its _degree_ is _computed_, not stored, as the field-extension degree
$$`\deg\varphi \;=\; [\,K(E_1) : \varphi^* K(E_2)\,] \;=\; \operatorname{finrank}_{K(E_2)} K(E_1).`
Defining the degree from the pullback is what keeps the Hasse argument non-circular.
:::

:::theorem "degree-multiplicative" (lean := "HasseWeil.Isogeny.comp_degree, HasseWeil.Isogeny.comp_degree_pos")
_(Degree is multiplicative.)_ For composable isogenies $`\varphi, \psi`,
$$`\deg(\psi \circ \varphi) \;=\; \deg\varphi \cdot \deg\psi`
({uses "isogeny"}[]), and the composite of two positive-degree isogenies again has
positive degree — the fact that $`\operatorname{End}(E)` is an integral domain
(Silverman III.4.2(c)).
:::

:::proof "degree-multiplicative"
Immediate from the tower law $`[K(E_1):K(E_3)] = [K(E_1):K(E_2)]\,[K(E_2):K(E_3)]` for
the nested function-field extensions cut out by the two pullbacks; positivity of the
product follows from positivity of each factor.
:::

:::theorem "mul-by-n-degree" (lean := "HasseWeil.mulByInt, HasseWeil.mulByInt_degree")
_(Degree of $`[n]`.)_ For each $`n \in \mathbb{Z}` the multiplication-by-$`n`
endomorphism $`[n] : E \to E` is an isogeny with
$$`\deg[n] \;=\; n^2`
(Silverman III.4.2). In particular $`[n] \ne 0` for $`n \ne 0`, so
$`\operatorname{End}(E)` is torsion-free.
:::

:::proof "mul-by-n-degree"
The pullback $`[n]^*` is built from the division polynomials; the finrank computation
gives $`\deg[n] = n^2` ({uses "isogeny"}[], {uses "mul-by-n-trace"}[]).
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

:::definition "frobenius-degree" (lean := "HasseWeil.frobeniusIsog_degree, HasseWeil.frobenius_finrank_functionField")
_(Frobenius has degree $`q`.)_ The $`q`-power Frobenius $`\pi`
({uses "frobenius-isogeny"}[]) has
$$`\deg\pi \;=\; [\,K(E) : K(E)^q\,] \;=\; q \;=\; \#K`
(Silverman III.4.6, II.2.11(a)). The core algebraic fact is that $`K(E)` is a
degree-$`q` extension of its subfield $`K(E)^q` of $`q`-th powers, which is the
substance of the pure inseparability of $`K(E)/K(E)^q`.
:::

:::theorem "frobenius-fixed-locus" (lean := "HasseWeil.frobenius_fixed_iff_mem_baseField, HasseWeil.range_algebraMap_eq_roots_X_pow_card_sub_X")
_(Frobenius fixed points are the rational points.)_ For a finite field $`K` with
$`q = \#K`, an element $`a` of the algebraic closure satisfies $`a^q = a` if and only if
$`a \in K`; equivalently, $`K` is exactly the root set of $`X^q - X` (Silverman V.1).
Transported to the curve, the fixed locus of $`\pi` is precisely $`E(\mathbb{F}_q)`.
:::

:::proof "frobenius-fixed-locus"
$`X^q - X` is separable (its derivative is $`-1`) of degree $`q`, so it has exactly $`q`
distinct roots in the algebraic closure; the $`q` elements of $`K` are distinct roots,
hence all of them.
:::

# The dual isogeny and the trace

:::definition "dual-isogeny" (lean := "HasseWeil.IsDualOf, HasseWeil.degree_dual_of_witness")
Following Silverman III.6.1, a _dual_ $`\hat\varphi` of an isogeny $`\varphi` is an
isogeny in the opposite direction with
$$`\hat\varphi \circ \varphi \;=\; [\deg\varphi] \;=\; \varphi \circ \hat\varphi`
({uses "isogeny"}[], {uses "mul-by-n-degree"}[]). A dual has the same degree as
$`\varphi` (Silverman III.6.2(a)). In `Hasse-Weil` this is the relation `IsDualOf`, used
as the hypothesis language across the degree-form development.
:::

:::theorem "dual-additivity" (lean := "HasseWeil.dual_add_of_trace_witnesses, HasseWeil.dual_add_of_sum_witnesses")
_(Duality is additive — bilinearity of the degree pairing.)_ Taking duals is additive on
point maps: $`\widehat{\varphi + \psi} = \hat\varphi + \hat\psi` at the level of
$`\operatorname{End}(E)` (Silverman III.6.2(c)). This is the algebraic engine making
$`\deg` a _quadratic_ form, with the associated pairing
$`\langle\varphi,\psi\rangle = \deg(\varphi+\psi) - \deg\varphi - \deg\psi` bilinear
({uses "dual-isogeny"}[]).
:::

:::proof "dual-additivity"
The composition $`\widehat{(\varphi+\psi)} \circ (\varphi+\psi)` expands, via the
dual-composition and trace-sum witnesses, into
$`[\deg\varphi] + [\deg\psi] + (\text{cross terms})`; matching point maps gives
additivity of the dual.
:::

:::definition "isog-trace" (lean := "HasseWeil.isogTrace")
The _trace_ of an endomorphism $`\alpha` (with $`1-\alpha` supplied) is
$$`\operatorname{tr}(\alpha) \;=\; 1 + \deg\alpha - \deg(1-\alpha) \;\in\; \mathbb{Z}`
(Silverman III.8). It is the linear coefficient of the degree quadratic form; for
Frobenius, $`\operatorname{tr}(\pi) = q + 1 - \#E(\mathbb{F}_q)`
({uses "frobenius-isogeny"}[]).
:::

:::theorem "mul-by-n-trace" (lean := "HasseWeil.isogTrace_mulByInt")
For the scalar endomorphism $`[n]` (with $`n \ne 0`, $`1-n \ne 0`),
$$`\operatorname{tr}([n]) \;=\; 1 + n^2 - (1-n)^2 \;=\; 2n`
({uses "isog-trace"}[], {uses "mul-by-n-degree"}[]).
:::

:::proof "mul-by-n-trace"
Substitute $`\deg[n] = n^2` and $`\deg[1-n] = (1-n)^2` into the definition of the trace
and expand.
:::

:::theorem "sum-trace-frobenius" (lean := "HasseWeil.sum_trace_frobenius_witness, HasseWeil.dual_comp_frobenius_witness")
_(Frobenius + Verschiebung is its trace.)_ With $`V` the Verschiebung (the dual of
$`\pi`),
$$`\pi + V \;=\; [\operatorname{tr}\pi] \quad\text{and}\quad V(\pi(P)) = q\,P,`
the diagonal value of the degree pairing on $`(1,-\pi)` (Silverman III.6.2(b)). This is
the substantive identity feeding the polarisation degree formula.
:::

:::proof "sum-trace-frobenius"
$`V \circ \pi = [\deg\pi] = [q]` from the dual relation ({uses "dual-isogeny"}[],
{uses "frobenius-degree"}[]); the sum-trace identity is then the
$`(1-\pi)\circ(1-V) = [\deg(1-\pi)]` bilinear-form value rearranged via additivity of the
dual ({uses "dual-additivity"}[]).
:::

# The degree quadratic form

:::theorem "degree-quadratic-scalar" (lean := "HasseWeil.degree_quadratic_mulByInt")
_(Degree form, scalar case — unconditional.)_ For the scalar endomorphism $`[m]` and
$`r,s \in \mathbb{Z}`,
$$`\deg([\,r m - s\,]) \;=\; m^2 r^2 - 2m\,rs + s^2 \;=\; (\deg[m])\,r^2 - \operatorname{tr}([m])\,rs + s^2.`
This is the binary-quadratic-form identity for the degree, proved unconditionally for
scalars (Silverman III.6.3).
:::

:::proof "degree-quadratic-scalar"
Substitute $`\deg[rm-s] = (rm-s)^2`, $`\deg[m]=m^2`, and $`\operatorname{tr}([m])=2m`
({uses "mul-by-n-degree"}[], {uses "mul-by-n-trace"}[]) and expand; both sides equal
$`(rm-s)^2`.
:::

:::theorem "degree-quadratic-polarisation" (lean := "HasseWeil.degree_quadratic_genuine_addIsog")
_(Degree form, genuine Frobenius pencil — Silverman III.6.3.)_ For the genuine isogeny
$`r\pi - s` (built from a dual $`V` of $`\pi` and the trace identity),
$$`\deg(r\pi - s) \;=\; q\,r^2 - t\,rs + s^2, \qquad t = \operatorname{tr}\pi,\ q=\deg\pi,`
the polarisation identity that realises the degree as a binary quadratic form on the
rank-two lattice $`\mathbb{Z}\,1 \oplus \mathbb{Z}\,\pi`.
:::

:::proof "degree-quadratic-polarisation"
Compose $`r\pi - s` with its dual $`rV - s` and read off $`\deg(r\pi-s)` from
$`(rV-s)\circ(r\pi-s) = [\,q r^2 - t rs + s^2\,]`, using the dual-composition, trace-sum
({uses "sum-trace-frobenius"}[]), and dual-additivity ({uses "dual-additivity"}[])
witnesses ({uses "frobenius-degree"}[]).
:::

:::theorem "degree-nonneg" (lean := "HasseWeil.qf_nonneg_of_genuine_chain, HasseWeil.degree_quadratic_mulByInt_nonneg")
_(Positivity of the degree form.)_ Because the degree of an isogeny is a non-negative
integer, the binary form is positive semi-definite on the Frobenius pencil:
$$`q\,r^2 - t\,rs + s^2 \;=\; \deg(r\pi - s) \;\ge\; 0 \qquad \text{for all } r,s \in \mathbb{Z}`
({uses "degree-quadratic-polarisation"}[]). This is the sole _geometric_ input to the
bound.
:::

:::proof "degree-nonneg"
Each value of the form equals a degree ({uses "degree-quadratic-polarisation"}[]), and
degrees are cardinalities of function-field extensions, hence $`\ge 0`.
:::

:::theorem "degree-quadratic-form" (lean := "HasseWeil.traceOfFrobenius_sq_le_of_qf_nonneg")
*(Geometric input, packaged.)* Suppose the degree form on $`\operatorname{End}(E)` is
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

# Separability and the point-count identity

:::theorem "kernel-card-degree" (lean := "HasseWeil.Isogeny.card_kernel_eq_degree_of_separable_witness, HasseWeil.card_kernel_eq_degree_of_separable_coordHom")
_(Separable $`\Rightarrow \#\ker = \deg`.)_ A _separable_ isogeny $`\varphi` (one whose
separable degree equals its degree) over an algebraically closed field has
$$`\#\ker\varphi \;=\; \deg\varphi`
(Silverman III.4.10(c)), proved by the classical good-fibre argument: a generic fibre has
$`\deg_s\varphi = \deg\varphi` points and every fibre is a kernel coset.
:::

:::proof "kernel-card-degree"
Choose a smooth point avoiding the (finite) ramification locus; its fibre has exactly
$`\deg_s\varphi = \deg\varphi` points, and translation identifies every nonempty fibre
with $`\ker\varphi`.
:::

:::theorem "one-sub-frobenius-separable" (lean := "HasseWeil.oneSubFrobenius_isSeparable_of_witness, HasseWeil.isSeparable_iff_of_coeff_witness")
_($`1-\pi` is separable.)_ The isogeny $`1-\pi` is separable, because its pullback acts
as the identity on the invariant differential (the coefficient $`\omega^*(1-\pi)=1 \ne 0`),
and $`m+n\pi` is separable iff $`p \nmid m` (Silverman III.5.5, V.1.2). Frobenius itself
is purely inseparable, but subtracting $`1` makes the difference separable.
:::

:::proof "one-sub-frobenius-separable"
By Silverman III.5.5 separability is detected by non-vanishing of the pullback of the
invariant differential $`\omega`; for $`1-\pi` this pullback is $`1`, since
$`\pi^*\omega = 0` ({uses "frobenius-isogeny"}[]).
:::

:::theorem "deg-one-sub-pi-eq-pointcount" (lean := "HasseWeil.isogOneSub_negFrobenius_degree_eq_pointCount, HasseWeil.kernel_eq_top_of_hom_eq_id_sub_frobenius")
_(The keystone $`\deg(1-\pi)=\#E(\mathbb{F}_q)`.)_ Since the kernel of $`1-\pi` on
rational points is all of $`E(\mathbb{F}_q)` ({uses "frobenius-fixed-locus"}[]) and
$`1-\pi` is separable,
$$`\deg(1-\pi) \;=\; \#\ker(1-\pi) \;=\; \#E(\mathbb{F}_q)`
(Silverman V.1.1). This converts a degree into the point count.
:::

:::proof "deg-one-sub-pi-eq-pointcount"
The point map of $`1-\pi` is $`\mathrm{id}-\pi`, whose kernel is the Frobenius fixed
locus, i.e. all of $`E(\mathbb{F}_q)`, so $`\#\ker(1-\pi) = \#E(\mathbb{F}_q)`.
Separability ({uses "one-sub-frobenius-separable"}[]) gives
$`\#\ker(1-\pi)=\deg(1-\pi)` via the kernel-cardinality theorem
({uses "kernel-card-degree"}[]).
:::

:::theorem "pointcount-eq-trace" (lean := "HasseWeil.pointCount_eq_of_witness, HasseWeil.pointCount_eq_of_hom_kernel_witness")
_(Point count via the trace of Frobenius.)_ Combining the keystone with the degree of
Frobenius,
$$`\#E(\mathbb{F}_q) \;=\; q + 1 - \operatorname{tr}(\pi), \qquad \operatorname{tr}(\pi)=t,`
i.e. $`\#E(\mathbb{F}_q) - (q+1) = -t` (Silverman V.1.1).
:::

:::proof "pointcount-eq-trace"
By definition $`\operatorname{tr}(\pi)=1+\deg\pi-\deg(1-\pi)` ({uses "isog-trace"}[]);
substitute $`\deg\pi=q` ({uses "frobenius-degree"}[]) and
$`\deg(1-\pi)=\#E(\mathbb{F}_q)` ({uses "deg-one-sub-pi-eq-pointcount"}[]) and rearrange.
:::

# The arithmetic core: discriminant of a binary quadratic form

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

:::theorem "qf-coprime-to-all" (lean := "HasseWeil.WeilPairing.qf_nonneg_of_nonneg_on_coprime, HasseWeil.WeilPairing.qf_nonneg_of_nonneg_on_coprime_both")
_(From the genuine locus to all of $`\mathbb{Z}^2`.)_ If the form $`q r^2 - t rs + s^2`
(with $`q>0`) is non-negative on every $`(r,s)` coprime to the characteristic $`p`, then
it is non-negative on _all_ $`(r,s)`. This is the discriminant lemma that lets the
Weil-pairing route demand the degree identity only where $`r\pi-s` is separable.
:::

:::proof "qf-coprime-to-all"
A coprime witness forces $`t^2 \le 4q` ({uses "trace-sq-le-four-q"}[]); then the
positive-semidefinite completion
$`4q\,(q r^2 - t rs + s^2) = (2qr - ts)^2 + (4q-t^2)s^2 \ge 0` extends non-negativity to
every $`(r,s)`.
:::

:::theorem "matrix-det-quadratic" (lean := "HasseWeil.WeilPairing.det_smul_sub_smul_one_fin_two, HasseWeil.WeilPairing.det_one_sub_fin_two")
_(The $`2\times2` determinant is the quadratic form.)_ For a $`2\times2` matrix $`M`,
$$`\det(rM - sI) \;=\; r^2\det M - rs\,\operatorname{tr}M + s^2, \qquad \det(I-M) = 1 - \operatorname{tr}M + \det M.`
With $`M = \rho_\ell(\pi)` the Frobenius matrix on $`E[\ell]`, the right-hand side is
exactly the Hasse quadratic form modulo $`\ell` (Silverman V.2.3.1).
:::

:::proof "matrix-det-quadratic"
Direct expansion via $`\det` of a $`2\times2` matrix; the second identity is the case
$`r=s=1` with a sign.
:::

# The Weil-pairing route to positivity

:::theorem "det-deg" (lean := "HasseWeil.WeilPairing.TorsionGeometric.det_rhoEll_eq_degree, HasseWeil.WeilPairing.TorsionGeometric.linearMap_det_torsionRestrict_eq")
_(Determinant $`=` degree on $`E[\ell]` — Silverman III.8.6.)_ For an endomorphism
$`\psi` whose Weil pairing scales by its degree,
$`e_\ell(\psi S,\psi T)=e_\ell(S,T)^{\deg\psi}`, the matrix $`\rho_\ell(\psi)` of $`\psi`
on the $`\ell`-torsion satisfies
$$`\det \rho_\ell(\psi) \;\equiv\; \deg\psi \pmod{\ell}.`
The discrete log of the symplectic Weil pairing gives an alternating bilinear form whose
top exterior power reads off the determinant.
:::

:::proof "det-deg"
Passing to the additive form $`\omega = \log e_\ell` makes the scaling
$`\omega(\psi S,\psi T) = \deg\psi \cdot \omega(S,T)`; on the $`2`-dimensional symplectic
space $`E[\ell]` the induced map on $`\Lambda^2` is multiplication by
$`\det\rho_\ell(\psi)`, forcing $`\det\rho_\ell(\psi) \equiv \deg\psi`.
:::

:::theorem "frob-det-data" (lean := "HasseWeil.WeilPairing.TorsionGeometric.frob_det_residual_of_weil_scaling, HasseWeil.WeilPairing.frob_det_residual_baseChange")
_(Frobenius determinant data on $`E[\ell]`.)_ For each prime $`\ell \ne p`, the Frobenius
matrix $`M=\rho_\ell(\pi)` over $`\overline{K}` satisfies, modulo $`\ell`,
$$`\det M = q, \qquad \det(I-M) = q+1-t, \qquad \det(rM - sI) = \deg(r\pi-s),`
assembling the determinant-degree identity across the separable pencil (Silverman III.8.6
+ V.2.3.1).
:::

:::proof "frob-det-data"
Apply the determinant-$`=`-degree identity ({uses "det-deg"}[]) to $`\pi`, $`1-\pi`, and
the separable pencil $`r\pi-s`, then expand the $`2\times2` determinants
({uses "matrix-det-quadratic"}[]); $`\deg\pi=q` ({uses "frobenius-degree"}[]) and
$`\det(I-M)=q+1-t` recovers the trace.
:::

:::theorem "qf-nonneg-weil" (lean := "HasseWeil.WeilPairing.qf_nonneg_skeleton_of_weil_det_data, HasseWeil.WeilPairing.qf_nonneg_skeleton_of_weil_det_data_both")
_(Positivity of the form, via the Weil pairing.)_ From the per-$`\ell` Frobenius
determinant data, the Hasse quadratic form is non-negative for all $`(r,s)`:
$$`q\,r^2 - t\,rs + s^2 \;\ge\; 0.`
This discharges the geometric leaf without the characteristic-$`p` dual-additivity wall,
using only the separable (genuine) locus.
:::

:::proof "qf-nonneg-weil"
On the separable locus $`\det(rM-sI) = \deg(r\pi-s) \ge 0` reduces the form modulo every
$`\ell \ne p` to a degree ({uses "frob-det-data"}[]); since this holds for infinitely many
$`\ell` the integer form is $`\ge 0` on the genuine locus, and the discriminant lemma
({uses "qf-coprime-to-all"}[]) extends it to all $`(r,s)`.
:::

# The Hasse bound

:::theorem "hasse-bound-from-witnesses" (lean := "HasseWeil.hasse_bound_of_qf_nonneg_witnesses, HasseWeil.hasse_bound_of_full_qf_nonneg_witnesses")
_(Hasse bound from positivity + point count.)_ Given the positivity of the degree form
({uses "degree-nonneg"}[]) and the point-count identity ({uses "pointcount-eq-trace"}[]),
$$`\bigl|\,\#E(\mathbb{F}_q) - (q+1)\,\bigr| \;\le\; 2\sqrt{q}.`
This is the witness-parametric assembly that isolates the pure-arithmetic core from the
geometric input.
:::

:::proof "hasse-bound-from-witnesses"
Positivity gives $`t^2 \le 4q` ({uses "trace-sq-le-four-q"}[]), hence $`|t| \le 2\sqrt q`
({uses "sqrt-bound"}[]); since $`\#E(\mathbb{F}_q)-(q+1) = -t`
({uses "pointcount-eq-trace"}[]), the bound follows.
:::

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
$`\#E(\mathbb{F}_q) - (q + 1) = -t`, this is the displayed bound.
:::

:::theorem "hasse-bound-weil-capstone" (lean := "HasseWeil.WeilPairing.hasse_bound_via_weil_pairing, HasseWeil.WeilPairing.hasse_bound_unconditional_of_baseChange_scalings_coprime")
_(Hasse's theorem — unconditional, axiom-clean, via the Weil pairing.)_ For an elliptic
curve $`E` over a finite field $`\mathbb{F}_q`,
$$`\bigl|\,\#E(\mathbb{F}_q) - (q + 1)\,\bigr| \;\le\; 2\sqrt{q},`
with no hypotheses, discharging the geometric leaf by base-changing to $`\overline{K}` and
running the Weil-pairing determinant machinery on the genuine pencil (Silverman V.1.1).
:::

:::proof "hasse-bound-weil-capstone"
The per-$`\ell` Frobenius determinant data over $`\overline{K}` gives positivity of the
degree form ({uses "qf-nonneg-weil"}[]); feeding this into the witness-parametric bound
({uses "hasse-bound-from-witnesses"}[]) with the point-count identity
({uses "pointcount-eq-trace"}[]) yields the unconditional bound, of which the headline
`hasse_bound` ({uses "hasse-bound"}[]) is the hypothesis-free specialisation.
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}
