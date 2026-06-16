import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The Coleman map" =>

Throughout this chapter $`p` is an *odd* prime and we work with coefficient field
$`\Qp`. We bring the arithmetic of cyclotomic fields into the picture through the
theory of *local units*. The main result is a theorem of Coleman identifying
norm-coherent systems of local units with a distinguished space of power series
over $`\Zp`; under the Mahler transform these become $`p`-adic measures. Applied to
*cyclotomic units*, this machinery reconstructs the Kubota–Leopoldt $`p`-adic
$`L`-function $`\zeta_p` on the *algebraic* side, packaged as the *Coleman map*.
This is the key bridge between the analytic object $`\zeta_p` and arithmetic, and is
the first step towards the Iwasawa Main Conjecture. See {Informal.citet "coleman"}[]
for Coleman's original work and {Informal.citet "RJW"}[] for the treatment we
follow.

# Notation for the cyclotomic tower

For $`n \in \N` set $`F_n := \Q(\mu_{p^n})` and $`K_n := \Qp(\mu_{p^n})`, with
maximal totally real subfields $`F_n^+`, $`K_n^+` (the fixed fields of complex
conjugation $`c`). Write
$$`\sU_n := \cO_{K_n}^{\times}, \qquad \sU_n^+ := \cO_{K_n^+}^{\times}`
for the local units. The extensions $`K_n/\Qp` are Galois and totally ramified at
$`p`, of degree $`(p-1)p^{n-1}`. Passing to the limit,
$`K_\infty := \Qp(\mu_{p^\infty}) = \bigcup_{n\ge 1} K_n`.

:::definition "col-cyclotomic-character"
Sending a primitive $`p^n`th root of unity to a primitive $`p^n`th root of unity
gives an isomorphism $`\chi_n : \Gal(F_n/\Q) \xrightarrow{\sim} (\Z/p^n\Z)^{\times}`,
characterised by $`\sigma(\xi) = \xi^{\chi_n(\sigma)}` for any
$`\xi \in \mu_{p^n}`. Taking the inverse limit yields the *cyclotomic character*
$$`\chi := \varprojlim_n \chi_n : \GCal := \Gal(F_\infty/\Q) \xrightarrow{\sim} \Zpx,`
an isomorphism of profinite groups, where $`F_\infty := \Q(\mu_{p^\infty})`. It
induces $`\GCal^+ := \Gal(F_\infty^+/\Q) \cong \Zpx/\{\pm 1\}`.
:::

:::definition "col-units-tower" (lean := "PadicLFunctions.Coleman.zetaSys, PadicLFunctions.Coleman.K, PadicLFunctions.Coleman.pi, PadicLFunctions.Coleman.O, PadicLFunctions.Coleman.levelNorm, PadicLFunctions.Coleman.NormCompatUnits")
We fix once and for all a *compatible system of roots of unity*
$`(\xi_{p^n})_{n \in \N}`: each $`\xi_{p^n}` is a primitive $`p^n`th root of unity
with $`\xi_{p^{n+1}}^p = \xi_{p^n}`. Put $`\pi_n := \xi_{p^n} - 1`, a uniformiser of
$`K_n`. The *infinite-level local units* are
$$`\sU_\infty := \varprojlim_n \sU_n,`
the inverse limit taken with respect to the norm maps
$`N_{n,n-1} : K_n \to K_{n-1}`. Together with its norm-1 submodule
$`\sU_{\infty,1} := \varprojlim_n \sU_{n,1}` (where
$`\sU_{n,1} = \{u \in \sU_n : u \equiv 1 \pmod{\mathfrak p_n}\}`) it is a compact
$`\Zp`-module carrying a continuous action of $`\GCal`, hence of the Iwasawa algebra
$`\Lam(\GCal)`. This {uses "col-cyclotomic-character"}[] $`\GCal`-action is the main
reason for passing to infinite level.

In the formalisation the tower lives *inside* `ℂ_[p]` (matching the
`B(0,1)`-framing below): the compatible system is `zetaSys` (built by
recursion from algebraic closedness), `K n` is the intermediate field
`ℚ_p(ξ_{p^n})` with `[K n : ℚ_p] = φ(p^n)` proved by an Eisenstein
argument, `O n` its norm-unit-ball, `levelNorm` the relative norm
`N_{n+1,n}` (with the collapse `N(ξ^b_{p^{n+1}} − 1) = ξ^b_{p^n} − 1`),
and `𝒰_∞` is the structure `NormCompatUnits` of norm-compatible unit
families. The `𝒢`-action and `𝒰_{∞,1}` are deferred to the §11 pass
(plan.md); the cyclotomic-character node above stays prose for the same
reason.
:::

The norm-1 units $`\sU_{n,1}` are genuine $`\Zp`-modules: for $`u \in \sU_{n,1}` and
$`a \in \Zp`, the series $`u^a = \sum_{k\ge 0}\binom{a}{k}(u-1)^k` converges. By
contrast the full local units $`\sU_n` are only $`\Z`-modules.

# Coleman's theorem

The elements $`\pi_n` lie in the open unit ball $`B(0,1) = \{z \in \Cp : |z| < 1\}`
and approach its boundary as $`n \to \infty`. Any $`f \in \Zp[[T]]` is a bounded
rigid analytic function on $`B(0,1)`, so it produces a sequence
$`(f(\pi_n))_n` with $`f(\pi_n) \in \cO_{K_n}`. We ask which sequences arise this
way; Coleman's theorem answers this for norm-compatible systems of units.

:::lemma_ "col-single-level-interp" (lean := "PadicLFunctions.Coleman.exists_evalPi_eq")
Let $`u \in \sU_n` be a local unit at level $`n`. There exists a power series
$`f \in \Zp[[T]]^{\times}` with $`f(\pi_n) = u`.
:::

:::proof "col-single-level-interp"
Because $`K_n/\Qp` is totally ramified with uniformiser $`\pi_n`, every element of
$`\cO_{K_n}` has a "$`\pi_n`-adic" expansion with $`\Zp`-coefficients. Concretely,
choose $`a_0 \in \Zp` with $`a_0 \equiv u \pmod{\pi_n}`, then $`a_1 \in \Zp` with
$`a_1 \equiv (u - a_0)/\pi_n \pmod{\pi_n}`, and continue, setting
$`f(T) = \sum_n a_n T^n`. By construction $`f(\pi_n) = u`. Since $`u` is a unit we
have $`a_0 \in \Zpx`, whence $`f` is invertible in $`\Zp[[T]]`.
:::

Such an $`f` is wildly non-unique: there were infinitely many choices for each
coefficient. Coleman's insight is that imposing the interpolation condition
*simultaneously for all $`n`* — that is, passing to the tower $`K_\infty` — pins
down a unique series.

:::theorem "coleman-theorem" (lean := "PadicLFunctions.Coleman.coleman_existsUnique, PadicLFunctions.Coleman.colemanSeries, PadicLFunctions.Coleman.colemanSeries_mul, PadicLFunctions.Coleman.colemanSeries_eq_iff")
There is a unique injective homomorphism of multiplicative groups
$$`\sU_\infty \longrightarrow \Zp[[T]]^{\times}, \qquad u \longmapsto f_u,`
such that $`f_u(\pi_n) = u_n` for all $`u = (u_n) \in \sU_\infty` and all $`n \ge 1`.
The series $`f_u` is the *Coleman power series* of $`u`. This refines
{uses "col-single-level-interp"}[] to the whole tower {uses "col-units-tower"}[].
:::

:::proof "coleman-theorem"
Uniqueness of $`f_u` is {uses "col-unique-coleman"}[]. Existence, together with the
precise description of the image, is the content of the more precise statement
{uses "col-coleman-precise"}[], proved below via the norm operator $`\cN`. That the
assignment is a group homomorphism is immediate from uniqueness: if $`f_u, f_v`
interpolate $`u, v` then $`f_u f_v` interpolates $`uv`, so $`f_{uv} = f_u f_v`.
:::

Coleman proved more: the image consists exactly of the power series fixed by a
*norm operator* $`\cN`. Norm-compatibility of the units corresponds to
$`\cN`-invariance of the series. This is made precise in
{bpref "col-coleman-precise"}[] below.

# Example: cyclotomic units

The example that motivates everything is the family of cyclotomic units, which we
shall see is directly linked to $`\zeta_p`.

:::definition "cyclotomic-units" (lean := "PadicLFunctions.Coleman.cycloUnit, PadicLFunctions.Coleman.norm_cycloUnit")
Let $`a \in \Z` be prime to $`p`. The *cyclotomic units* are
$$`c_n(a) := \frac{\xi_{p^n}^a - 1}{\xi_{p^n} - 1} \in \sU_n.`
This is a genuine unit, since both numerator and denominator are uniformisers of
$`K_n` (each $`\xi_{p^n}^a - 1` is, as $`a` is prime to $`p`).
:::

:::lemma_ "col-cyclo-norm-compatible" (lean := "PadicLFunctions.Coleman.cyclo, PadicLFunctions.Coleman.levelNorm_cycloUnit")
The system $`c(a) := (c_n(a))_n` is norm-compatible, i.e.\ $`c(a) \in \sU_\infty`.
Its Coleman power series is the polynomial
$$`f_{c(a)}(T) = \frac{(1+T)^a - 1}{T}.`
:::

:::proof "col-cyclo-norm-compatible"
Norm-compatibility means $`N_{n,n-1}(c_n(a)) = c_{n-1}(a)`. The minimal polynomial
of $`\xi_{p^n}` over $`K_{n-1}` is $`X^p - \xi_{p^{n-1}}`, so its conjugates are
$`\eta\,\xi_{p^n}` for $`\eta \in \mu_p`. Hence for any $`b` prime to $`p`,
$$`N_{n,n-1}(\xi_{p^n}^b - 1) = \prod_{\eta \in \mu_p}(\xi_{p^n}^b\eta - 1) = \xi_{p^n}^{bp} - 1 = \xi_{p^{n-1}}^b - 1,`
using $`X^p - 1 = \prod_{\eta \in \mu_p}(X\eta - 1)`. Taking $`b = a` for the
numerator and $`b = 1` for the denominator, multiplicativity of the norm gives the
claim. Finally, evaluating $`f_{c(a)}(\pi_n) = ((1+\pi_n)^a - 1)/\pi_n = (\xi_{p^n}^a - 1)/(\xi_{p^n}-1) = c_n(a)`,
so by uniqueness {uses "coleman-theorem"}[] this polynomial is the Coleman series of
$`c(a)` {uses "cyclotomic-units"}[].
:::

Recall the operator $`\partial = (1+T)\tfrac{d}{dT}` from the construction of
$`\zeta_p`, which corresponds to multiplication by $`x` on measures.

:::proposition "col-partiallog-cyclo" (lean := "PadicLFunctions.Coleman.one_add_mul_derivative_log_geomSum, PadicLFunctions.Coleman.colemanSeries_cyclo, PadicLFunctions.Coleman.dlog_geomSum")
We have
$$`\partial \log f_{c(a)}(T) = a - 1 - F_a(T),`
where $`F_a(T)` is the power series whose associated measure is $`\mu_a`.
:::

:::proof "col-partiallog-cyclo"
A direct computation using $`\partial \log g = (1+T)g'/g`:
$$`\partial \log f_{c(a)} = \partial\log((1+T)^a - 1) - \partial\log T = \frac{a(1+T)^a}{(1+T)^a - 1} - \frac{T+1}{T}.`
Writing $`a(1+T)^a = a((1+T)^a - 1) + a` in the first term and
$`(T+1)/T = 1 + 1/T` in the second gives
$$`= a - 1 - \frac1T + \frac{a}{(1+T)^a - 1} = a - 1 - F_a(T),`
which is exactly the defining expression for $`F_a` {uses "col-cyclo-norm-compatible"}[].
:::

:::lemma_ "col-relate-cyclo-mua" (lean := "PadicLFunctions.Coleman.res_derivative_log_geomSum")
The restriction to $`\Zpx` of the measure attached to $`\partial \log f_{c(a)}`
equals minus the restriction of $`\mu_a`:
$$`\Res_{\Zpx}\big(\mu_{\partial \log f_{c(a)}}\big) = -\Res_{\Zpx}(\mu_a),`
where $`\mu_a` {uses "measure-mu-a"}[] is the measure used to build $`\zeta_p`.
:::

:::proof "col-relate-cyclo-mua"
On power series, restriction of a measure to $`\Zpx` is implemented by the operator
$`1 - \varphi\circ\psi`. This operator annihilates constants, so it kills the term
$`a - 1` in {uses "col-partiallog-cyclo"}[]. Hence
$$`(1 - \varphi\circ\psi)\,\partial\log f_{c(a)} = -(1 - \varphi\circ\psi)F_a,`
which is the asserted identity of restricted measures.
:::

This relation is the engine behind the new construction of $`\zeta_p` via
cyclotomic units carried out below.

# Proof of Coleman's theorem

We prove the precise form of {bpref "coleman-theorem"}[]. The strategy: identify the
image as the $`\cN`-invariants, where $`\cN` is a *norm operator* on power series
that mirrors the field norm; then a continuity property of $`\cN` lets a diagonal
argument produce the interpolating series.

:::lemma_ "col-unique-coleman" (lean := "PadicLFunctions.Coleman.evalPi_injective")
Suppose $`u = (u_n) \in \sU_\infty` and $`f, g \in \Zp[[T]]^{\times}` both satisfy
$`f(\pi_n) = g(\pi_n) = u_n` for all $`n \ge 1`. Then $`f = g`.
:::

:::proof "col-unique-coleman"
By the Weierstrass preparation theorem any nonzero $`h \in \Zp[[T]]` factors as
$`h = p^m\,u(T)\,r(T)` with $`u` a unit and $`r` a distinguished polynomial. Such an
$`h` converges on the maximal ideal of the ring of integers of $`\Qpbar`, and since
the unit factor has no zeros there, $`h` has only finitely many zeros in that
maximal ideal. Apply this to $`h = f - g`: it vanishes at the infinitely many
distinct points $`\pi_n` (which lie in the maximal ideal), forcing $`f - g = 0`.
:::

We now build the norm operator. Recall $`\varphi` acts on $`\Zp[[T]]` by
$`\varphi(f)(T) = f((1+T)^p - 1)`, is injective, and satisfies the key identity
$$`\varphi(f)(\pi_{n+1}) = f((\pi_{n+1}+1)^p - 1) = f(\xi_{p^{n+1}}^p - 1) = f(\pi_n).`
Its measure-theoretic adjoint $`\psi` satisfies
$`(\varphi\circ\psi)(f)(T) = \tfrac1p\sum_{\eta \in \mu_p} f(\eta(1+T) - 1)`; we call
$`\psi` the *trace* operator.

:::lemma_ "col-norm-operator" (lean := "PadicLFunctions.Coleman.normOp, PadicLFunctions.Coleman.normOp_mul, PadicLFunctions.Coleman.normOp_eq_det")
There is a unique multiplicative operator $`\cN` on $`\Zp[[T]]`, the *norm
operator*, such that
$$`(\varphi\circ\cN)(f)(T) = \prod_{\eta \in \mu_p} f(\eta(1+T) - 1).`
Being multiplicative, $`\cN` preserves $`\Zp[[T]]^{\times}`.
:::

:::proof "col-norm-operator"
Let $`B = \Zp[[T]]` and $`A = \varphi(\Zp[[T]]) = \Zp[[(1+T)^p - 1]]`. Then $`B/A`
is a degree-$`p` extension, obtained by adjoining a $`p`th root of $`(1+T)^p` to
$`A`; its automorphisms over $`A` are $`T \mapsto \eta(1+T) - 1` for $`\eta \in \mu_p`.
The field/ring norm $`N_{B/A}(f) = \prod_{\eta\in\mu_p} f(\eta(1+T)-1)` lands in
$`A = \varphi(\Zp[[T]])`, so we may set $`\cN := \varphi^{-1}\circ N_{B/A}`, using
injectivity of $`\varphi`. Uniqueness and multiplicativity follow from those of
$`N_{B/A}` and injectivity of $`\varphi`.
:::

Analogously $`\psi = p^{-1}\varphi^{-1}\circ\Tr_{B/A}` is built from the trace of
$`B/A`, explaining the terminology. The point of $`\cN` is that it mirrors the
field norm $`N_{n+1,n}` defining $`\sU_\infty`.

:::lemma_ "col-norm-vs-units" (lean := "PadicLFunctions.Coleman.evalPi_normOp")
The square
$$`\begin{array}{ccc} \Zp[[T]]^{\times} & \xrightarrow{\ f\mapsto f(\pi_{n+1})\ } & \sU_{n+1} \\ \downarrow{\scriptstyle\cN} & & \downarrow{\scriptstyle N_{n+1,n}} \\ \Zp[[T]]^{\times} & \xrightarrow{\ f\mapsto f(\pi_n)\ } & \sU_n \end{array}`
commutes; i.e.\ $`N_{n+1,n}(f(\pi_{n+1})) = (\cN f)(\pi_n)` for all
$`f \in \Zp[[T]]^{\times}`.
:::

:::proof "col-norm-vs-units"
For $`f \in \Zp[[T]]^{\times}` we have $`f(\pi_n) \in \sU_n` (its inverse is
$`f^{-1}(\pi_n)`, also integral), so the horizontal maps land in units. Since the
minimal polynomial of $`\xi_{p^{n+1}}` over $`K_n` is $`X^p - \xi_{p^n}`, the
conjugates of $`\xi_{p^{n+1}}` are $`\eta\,\xi_{p^{n+1}}`, $`\eta \in \mu_p`. Hence
$$`N_{n+1,n}(f(\pi_{n+1})) = \prod_{\eta\in\mu_p} f(\eta\xi_{p^{n+1}} - 1) = (\varphi\circ\cN)(f)(\pi_{n+1}) = (\cN f)(\pi_n),`
using {uses "col-norm-operator"}[] for the middle equality and
$`\varphi(g)(\pi_{n+1}) = g(\pi_n)` for the last.
:::

:::proposition "col-R-injective" (lean := "PadicLFunctions.Coleman.evalPi_mem_O, PadicLFunctions.Coleman.evalPi_injective")
The map
$$`R : (\Zp[[T]]^{\times})^{\cN = \mathrm{id}} \hookrightarrow \sU_\infty, \qquad f \mapsto (f(\pi_n))_n`
is well defined and injective.
:::

:::proof "col-R-injective"
If $`\cN(f) = f`, then {uses "col-norm-vs-units"}[] gives
$`N_{n+1,n}(f(\pi_{n+1})) = (\cN f)(\pi_n) = f(\pi_n)`, so the sequence
$`(f(\pi_n))_n` is norm-compatible and lies in $`\sU_\infty`; thus $`R` is well
defined. Injectivity is {uses "col-unique-coleman"}[]: two $`\cN`-invariant series
with the same image agree at every $`\pi_n`, hence are equal.
:::

Surjectivity of $`R` is the crux. It rests on how $`\cN` behaves modulo powers of
$`p`.

:::lemma_ "col-norm-continuity" (lean := "PadicLFunctions.Coleman.phi_injective_mod, PadicLFunctions.Coleman.normOp_modEq_self, PadicLFunctions.Coleman.normOp_modEq_one, PadicLFunctions.Coleman.normOp_iterate_modEq")
Let $`f \in \Zp[[T]]`. Then:

(i) if $`\varphi(f) \equiv 1 \pmod{p^k}` then $`f \equiv 1 \pmod{p^k}`;

(ii) $`\cN(f) \equiv f \pmod{p}`.

If moreover $`f \in \Zp[[T]]^{\times}`, then:

(iii) if $`f \equiv 1 \pmod{p^k}` with $`k \ge 1` then $`\cN(f) \equiv 1 \pmod{p^{k+1}}`;

(iv) if $`k_2 \ge k_1 \ge 0` then $`\cN^{k_2}(f) \equiv \cN^{k_1}(f) \pmod{p^{k_1+1}}`.
:::

:::proof "col-norm-continuity"
For (i), reduce mod $`p`: since $`(1+T)^p - 1 \equiv T^p \pmod p`, the reduction of
$`\varphi` is the Frobenius substitution $`\bar f(T) \mapsto \bar f(T^p)` on
$`\Fp[[T]]`, which is injective; a dévissage up the filtration
$`p^k\Zp[[T]] \supset p^{k+1}\Zp[[T]]` promotes this to: $`\varphi(f) \equiv 1`
forces $`f \equiv 1 \pmod{p^k}`. For (ii), every $`\eta \in \mu_p` satisfies
$`\eta \equiv 1` modulo the maximal ideal $`\mathfrak p_1` of $`\cO_{K_1}`, so
$`(\varphi\circ\cN)(f) = \prod_{\eta}f(\eta(1+T)-1) \equiv f(T)^p \pmod{\mathfrak p_1}`;
as the two sides lie in $`\Zp[[T]]` this is a congruence mod $`p`, and combined with
the Frobenius relation $`f^p \equiv \varphi(f) \pmod p` it gives
$`\varphi(\cN f) \equiv \varphi(f) \pmod p`, whence $`\cN f \equiv f \pmod p` by (i).
For (iii),
let $`\mathfrak p_1` be the maximal ideal of $`\cO_{K_1}`. Since
$`(\eta-1)(1+T) \in \mathfrak p_1\Zp[[T]]`, we have
$`\eta(1+T) - 1 \equiv T \pmod{\mathfrak p_1\Zp[[T]]}`, so term-by-term
$`f(\eta(1+T)-1) \equiv f(T) \pmod{\mathfrak p_1 p^k\Zp[[T]]}` when
$`f \equiv 1 \pmod{p^k}`. Multiplying over $`\eta \in \mu_p` gives
$`(\varphi\circ\cN)(f) \equiv f^p \pmod{\mathfrak p_1 p^k}`; as both sides lie in
$`\Zp[[T]]`, this holds modulo $`\mathfrak p_1 p^k \cap \Zp = p^{k+1}`. But
$`f \equiv 1 \pmod{p^k}` gives $`f^p \equiv 1 \pmod{p^{k+1}}`, so
$`\varphi(\cN f) \equiv 1 \pmod{p^{k+1}}` and (i) yields
$`\cN(f) \equiv 1 \pmod{p^{k+1}}`. Part (iv) follows: by (ii),
$`\cN^{k_2 - k_1}f/f \equiv 1 \pmod p`, and applying (iii) while iterating $`\cN` a
further $`k_1` times upgrades the congruence to modulus $`p^{k_1+1}`.
:::

:::proposition "col-R-surjective" (lean := "PadicLFunctions.Coleman.coleman_existsUnique, PadicLFunctions.Coleman.exists_subseq_tendsto")
The map $`R : (\Zp[[T]]^{\times})^{\cN = \mathrm{id}} \to \sU_\infty` is surjective.
:::

:::proof "col-R-surjective"
Let $`u = (u_n) \in \sU_\infty`. For each $`n` pick
$`f_n \in \Zp[[T]]^{\times}` with $`f_n(\pi_n) = u_n` (possible by
{uses "col-single-level-interp"}[]). Using {uses "col-norm-vs-units"}[] and
norm-compatibility of $`u`, one checks $`(\cN^k f_{n+k})(\pi_n) = u_n` for all
$`k \ge 0`. Set $`g_n := \cN^{n} f_{2n}`. For $`m \ge n`, combining this identity
(with $`k = 2m-n`) and {uses "col-norm-continuity"}[](iv) (with $`k_2 = 2m-n`,
$`k_1 = m`) gives
$$`u_n = (\cN^{2m-n}f_{2m})(\pi_n) \equiv (\cN^m f_{2m})(\pi_n) = g_m(\pi_n) \pmod{p^{m+1}},`
so $`g_m(\pi_n) \to u_n` as $`m \to \infty`, for every $`n`. Since
$`\Zp[[T]]^{\times}` is compact, $`(g_m)` has a convergent subsequence; let $`f_u`
be its limit. Then $`f_u(\pi_n) = u_n` for all $`n`. Finally,
{uses "col-norm-vs-units"}[] and norm-compatibility give
$`(\cN f_u)(\pi_n) = N_{n+1,n}f_u(\pi_{n+1}) = N_{n+1,n}(u_{n+1}) = u_n = f_u(\pi_n)`,
so $`\cN f_u` and $`f_u` are both Coleman series for $`u`; by
{uses "col-unique-coleman"}[] they coincide, i.e.\ $`\cN(f_u) = f_u`.
:::

:::theorem "col-coleman-precise" (lean := "PadicLFunctions.Coleman.coleman_existsUnique, PadicLFunctions.Coleman.normOp_colemanSeries, PadicLFunctions.Coleman.evalPi_colemanSeries")
The map $`R` of {bpref "col-R-injective"}[] is an isomorphism of groups
$$`R : (\Zp[[T]]^{\times})^{\cN = \mathrm{id}} \xrightarrow{\ \sim\ } \sU_\infty,`
and its inverse $`u \mapsto f_u` is the unique map with $`f_u(\pi_n) = u_n` for all
$`u \in \sU_\infty`, $`n \ge 1`. In particular Coleman's power series $`f_u` is
always $`\cN`-invariant.
:::

:::proof "col-coleman-precise"
By {uses "col-R-injective"}[] the map $`R` is an injective homomorphism, and by
{uses "col-R-surjective"}[] it is surjective; hence it is a group isomorphism. Its
inverse sends $`u` to the series $`f_u = R^{-1}(u)`, which satisfies
$`f_u(\pi_n) = u_n` by construction of $`R`; uniqueness is
{uses "col-unique-coleman"}[]. This is precisely the refined form of
{uses "coleman-theorem"}[].
:::

# Definition of the Coleman map

The example of cyclotomic units suggests a recipe for $`\zeta_p`. Given the
construction of $`\zeta_p` from $`\mu_a` and the relation
{bpref "col-relate-cyclo-mua"}[], one may obtain $`\zeta_p` by: (1) take the tower
$`c(a)` of cyclotomic units; (2) form its Coleman series $`f_{c(a)}`; (3) apply
$`\partial\log`; (4) apply $`1 - \varphi\circ\psi` (restriction to $`\Zpx`); (5)
apply $`\partial^{-1}` (multiplication by $`x^{-1}` on measures); (6) invert the
Mahler transform to land in $`\Lam(\Zpx)`; (7) divide by $`\theta_a`. Abstracting
steps (2)–(6) gives the following.

:::definition "coleman-map" (lean := "PadicLFunctions.Coleman.Col, PadicLFunctions.Coleman.dlog")
The *Coleman map* is the composite
$$`\Col : \sU_\infty \xrightarrow{\ u\mapsto f_u\ } (\Zp[[T]]^{\times})^{\cN=\mathrm{id}} \xrightarrow{\ \partial\log\ } \Zp[[T]] \xrightarrow{\ 1-\varphi\circ\psi\ } \Zp[[T]]^{\psi=0} \xrightarrow{\ \partial^{-1}\ } \Zp[[T]]^{\psi=0} \xrightarrow{\ \cA^{-1}\ } \Lam(\Zpx),`
where the first map is Coleman's isomorphism {uses "coleman-theorem"}[], the second
the logarithmic derivative of {uses "col-partiallog-cyclo"}[], the third
measure-theoretic restriction from $`\Zp` to $`\Zpx`, the fourth multiplication by
$`x^{-1}`, and the last $`\cA^{-1}` the inverse Mahler transform
{uses "mahler-transform"}[] landing in the Iwasawa algebra
{uses "iwasawa-algebra"}[].
:::

:::theorem "col-coleman-to-kl" (lean := "PadicLFunctions.Coleman.coleman_to_kl, PadicLFunctions.Coleman.Col_cyclo")
For any topological generator $`a` of $`\Zpx`, the Kubota–Leopoldt $`p`-adic
$`L`-function is recovered as the pseudo-measure
$$`\zeta_p = \frac{\Col(c(a))}{\theta_a} \in Q(\Zpx).`
:::

:::proof "col-coleman-to-kl"
Track the cyclotomic tower $`c(a)` {uses "cyclotomic-units"}[] through the Coleman
map {uses "coleman-map"}[] one step at a time. Its Coleman series is
$`f_{c(a)} = ((1+T)^a-1)/T` {uses "col-cyclo-norm-compatible"}[], and applying
$`\partial\log` produces the series $`a - 1 - F_a` {uses "col-partiallog-cyclo"}[],
the measure-theoretic incarnation of $`\mu_{\partial\log f_{c(a)}}`. Restricting to
$`\Zpx` by $`1 - \varphi\circ\psi` and using
$`\Res_{\Zpx}(\mu_{\partial\log f_{c(a)}}) = -\Res_{\Zpx}(\mu_a)`
{uses "col-relate-cyclo-mua"}[] turns this into $`-\Res_{\Zpx}(\mu_a)`. The fourth
step $`\partial^{-1}` is multiplication by $`x^{-1}` on measures, so after inverting
the Mahler transform we arrive at
$$`\Col(c(a)) = -\,x^{-1}\,\Res_{\Zpx}(\mu_a) \in \Lam(\Zpx).`
Comparing with the construction $`\zeta_p = x^{-1}\Res_{\Zpx}(\mu_a)/\theta_a`
{uses "measure-mu-a"}[] {uses "kubota-leopoldt"}[], the single accumulated sign is
the very factor of $`-1` carried by the normaliser $`\theta_a`, so dividing
$`\Col(c(a))` by $`\theta_a` yields exactly $`\zeta_p`. Since $`\theta_a` is not a
unit, the quotient lives only in the fraction field $`Q(\Zpx)`, exhibiting $`\zeta_p`
as a pseudo-measure {uses "pseudo-measure"}[] with its pole at $`s=1`; the division
also cancels the dependence on the choice of topological generator $`a`.
:::

# Generalisations: Kummer sequence, Euler systems and big logarithms

This final section sketches the conjectural framework — due to Perrin-Riou — that
generalises the Coleman map to arbitrary $`p`-adic Galois representations. It is
context for Part II and may be skipped on a first reading. For a number field $`F`
write $`\sG_F` for its absolute Galois group and $`H^1(F, A) := H^1(\sG_F, A)` for
continuous Galois cohomology.

:::proposition "col-kummer-map"
Taking the long exact cohomology sequence of the Kummer sequence
$`0 \to \mu_{p^m} \to \mathbf{G}_{\mathrm m} \xrightarrow{x\mapsto x^{p^m}} \mathbf{G}_{\mathrm m} \to 0`
over $`\Qbar`, and passing to the inverse limit over $`m`, yields the *Kummer
isomorphism*
$$`\delta : F^{\times} \otimes \Zp \xrightarrow{\ \sim\ } H^1(F, \Zp(1)).`
:::

:::proof "col-kummer-map"
For each $`m` the long exact sequence reads
$`0 \to \mu_{p^m}(F) \to F^\times \xrightarrow{x^{p^m}} F^\times \to H^1(F,\mu_{p^m}) \to H^1(F, \Qbar^\times)`,
and $`H^1(F,\Qbar^\times) = 0` by Hilbert 90. Thus
$`F^\times/(F^\times)^{p^m} \xrightarrow{\sim} H^1(F,\mu_{p^m})`. Explicitly, given
$`a \in F^\times` pick $`b` with $`b^{p^m} = a`; then $`\sigma \mapsto \sigma(b)/b`
is a $`1`-cocycle, a coboundary iff $`a` is a $`p^m`th power, giving the level-$`m`
isomorphism. The inverse limit over $`m` (exact, as the systems are finite) assembles
these into $`\delta : F^\times \otimes \Zp \xrightarrow{\sim} H^1(F,\Zp(1))`.
:::

Applied to $`F = \Q(\mu_m)` with $`m = Dp^n`, the elements
$`\mathbf c_m := (\xi_m^{-1}-1)/(\xi_m - 1)` (generalising $`c_n(-1)`) map to classes
$`\mathbf z_m := \delta(\mathbf c_m) \in H^1(\Q(\mu_m),\Zp(1))` satisfying, under
corestriction, $`\cores(\mathbf z_{m\ell}) = \mathbf z_m` if $`\ell \mid m` and
$`(1 - \Frob_\ell^{-1})\mathbf z_m` if $`\ell \nmid m` — using that $`\Frob_\ell`
acts on $`\Zp(1)` by $`\ell`, and noting $`1 - \ell^{-1}` is the Euler factor at
$`\ell` of $`\zeta(s)` at $`s=1`. This is the prototype of an *Euler system*.

:::definition "col-euler-systems"
Let $`\Sigma` be a finite set of primes containing $`p`, let
$`V \in \mathrm{Rep}_L\,\sG_\Q` be a global $`p`-adic Galois representation
unramified outside $`\Sigma`, and let $`T \subseteq V` be a $`\sG_\Q`-stable
$`\cO_L`-lattice. An *Euler system* for $`(V,T,\Sigma)` is a collection of classes
$`\mathbf z_m \in H^1(\Q(\mu_m), T)`, with $`m = p^n m'` and $`m'` a square-free
product of primes outside $`\Sigma`, satisfying
$$`\cores_{\Q(\mu_{m\ell})/\Q(\mu_m)}(\mathbf z_{m\ell}) = \begin{cases} \mathbf z_m & \ell = p,\\ P_\ell(V^*(1), \sigma_\ell^{-1})\,\mathbf z_m & \ell \neq p, \end{cases}`
where $`P_\ell(V^*(1), X) = \det(1 - \Frob_\ell^{-1}X \mid V^*(1)^{I_\ell})` is the
Euler factor of $`L(V^*(1), s)` at $`\ell` and $`\sigma_\ell` is the image of
$`\Frob_\ell` in $`\Gal(\Q(\mu_m)/\Q)`.
:::

The cyclotomic units {bpref "cyclotomic-units"}[] form an Euler system
{bpref "col-euler-systems"}[] for $`\Zp(1)`, central to Rubin's proof of the Main
Conjecture.

:::definition "col-iwasawa-cohomology"
Replacing $`\Qbar` by $`\Qpbar` and $`F` by $`K_n` in
{bpref "col-kummer-map"}[] gives
$`K_n^\times \otimes \Zp \cong H^1(K_n,\Zp(1))`, intertwining norm with
corestriction. Taking the inverse limit, the *Iwasawa cohomology* is
$$`H^1_{\Iw}(\Qp, \Qp(1)) := \varprojlim_{n\ge 1} H^1(K_n, \Zp(1)) \otimes_{\Zp} \Qp,`
and more generally, for $`V \in \mathrm{Rep}_L\,\sG_{\Qp}` with stable lattice $`T`,
$`H^1_{\Iw}(\Qp, V) := \varprojlim_n H^1(K_n, T)\otimes_{\cO_L} L` (limit over
corestriction). The inclusion $`\sU_n \subset K_n^\times` induces
$`\kappa : \sU_\infty \to \varprojlim_n H^1(K_n,\Zp(1))`.
:::

:::theorem "col-perrin-riou-log"
There is a map $`\Col' : H^1_{\Iw}(\Qp,\Qp(1)) \to \cM(\Zpx,\Qp)` to the space of
$`\Qp`-valued measures, factoring the Coleman map: $`\Col' \circ \kappa = \Col`.
More generally, for crystalline $`V`, Perrin-Riou's *big logarithm map*
$$`\Log_V : H^1_{\Iw}(\Qp, V) \to \cD^{\mathrm{la}}(\Zpx, L)`
into locally analytic distributions specialises to $`\Col'` at $`V = \Qp(1)`. Thus a
$`p`-adic $`L`-function for $`V` arises from an Euler system by localising at $`p`
and applying $`\Log_V`:
$$`\{\text{Euler systems}\} \xrightarrow{\ \loc_p\ } H^1_{\Iw}(\Qp, V) \xrightarrow{\ \Log_V\ } \{p\text{-adic }L\text{-functions}\}.`
:::

:::proof "col-perrin-riou-log"
The factorisation $`\Col' \circ \kappa = \Col` is the diagram defining $`\Col'` on
the image of $`\kappa` {uses "col-iwasawa-cohomology"}[] and extending by the Iwasawa
algebra structure; combined with {uses "col-partiallog-cyclo"}[] it shows
$`\zeta_p` is the value of $`\Col'` at the cyclotomic Iwasawa class (up to dividing
by $`\theta_a`, which introduces the pole), recovering
{uses "col-coleman-to-kl"}[]. The existence and interpolation of $`\Log_V` for
crystalline $`V`, expressed through Bloch–Kato's exponential and dual-exponential
maps, is Perrin-Riou's theory; we record only that it specialises to $`\Col'` at
$`V = \Qp(1)`. This splits the construction of $`p`-adic $`L`-functions into a global
problem (producing an Euler system, e.g.\ via {uses "col-euler-systems"}[]) and a
purely local one (the big logarithm).
:::
