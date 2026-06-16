import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Iwasawa theorem on the zeros of the p-adic zeta function" =>

The Coleman map of the previous chapter lets us construct the Kubota–Leopoldt
$`p`-adic $`L`-function $`\zeta_p` from a tower of cyclotomic units. We now state a
theorem of Iwasawa that puts this on a deeper footing: it describes the *zeros* of
$`\zeta_p` — packaged as a canonical ideal in the Iwasawa algebra — in terms of the
*module* of cyclotomic units sitting inside the local units. To move all of the
analytic information to the Galois side, we first reinterpret $`\zeta_p` as a
pseudo-measure on the Galois group, then introduce the global and local modules of
cyclotomic units and their classical link to class numbers, and finally state
Iwasawa's theorem.

Throughout, $`p` is an odd prime, $`F_\infty = \bigcup_{n\ge 1}\Q(\mu_{p^n})` is the
cyclotomic $`\Z_p`-extension's ambient field, and $`\GG = \Gal(F_\infty/\Q)`. The
cyclotomic character is an isomorphism $`\chi : \GG \xrightarrow{\sim} \Zpx`.

# Measures on Galois groups

The cyclotomic character $`\chi : \GG \xrightarrow{\sim} \Zpx` transports measures on
$`\Zpx` to measures on $`\GG`. We write $`\Lam(\GG)` for the space of measures on
$`\GG`, identified with the Iwasawa algebra $`\Lam(\Zpx)` via $`\chi`. In particular
$`\zeta_p`, a priori a pseudo-measure on $`\Zpx`, is naturally a pseudo-measure on
$`\GG`.

Let $`c \in \GG` be complex conjugation, so $`\chi(c) = -1`, and let
$`\GG^+ = \Gal(F_\infty^+/\Q) = \GG/\ang{c}`, identified via $`\chi` with
$`\Zpx/\{\pm 1\}`. The $`p`-adic zeta function vanishes at the characters $`\chi^k`
for odd $`k > 1`; we use this to show it descends to a pseudo-measure on $`\GG^+`.

:::lemma_ "zeros-plus-minus-decomposition" (lean := "PadicMeasure.isCompl_invariants_antiInvariants, PadicMeasure.isCompl_plusPart_minusPart")
Let $`R` be a ring in which $`2` is invertible and let $`M` be an $`R`-module with a
continuous action of $`\GG`. Then $`M` decomposes as
$$`M \cong M^+ \oplus M^-,`
where $`c` acts as $`+1` on $`M^+` and as $`-1` on $`M^-`.
:::

:::proof "zeros-plus-minus-decomposition"
Since $`c^2 = 1`, the elements $`e^+ = \tfrac{1+c}{2}` and $`e^- = \tfrac{1-c}{2}`
are orthogonal idempotents in $`R[\ang{c}]` summing to $`1`. They project $`M` onto
$`M^+ = e^+ M` and $`M^- = e^- M`, on which $`c` acts as $`+1` and $`-1`
respectively, giving the direct sum decomposition.
:::

Since $`p` is odd, $`2` is invertible in $`\Zp`, so applying the lemma to
$`M = \Lam(\GG)` yields $`\Lam(\GG) \cong \Lam(\GG)^+ \oplus \Lam(\GG)^-`. The plus
part is governed entirely by the quotient group $`\GG^+`.

:::lemma_ "zeros-lambda-plus-iso" (lean := "PadicMeasure.plusEquiv, PadicMeasure.projPlus, PadicMeasure.plusSection, PadicMeasure.ker_projPlus")
There is a natural isomorphism $`\Lam(\GG)^+ \cong \Lam(\GG^+)`. We henceforth
identify $`\Lam(\GG^+)` with the submodule $`\Lam(\GG)^+` of $`\Lam(\GG)`. This rests
on {uses "zeros-plus-minus-decomposition"}[].
:::

:::proof "zeros-lambda-plus-iso"
Work at finite level. Writing $`\GG_n = \Gal(F_n/\Q)` and $`\GG_n^+ =
\Gal(F_n^+/\Q)`, the quotient map of Galois groups induces a surjection
$`\Zp[\GG_n] \twoheadrightarrow \Zp[\GG_n^+]` which kills $`\Zp[\GG_n]^-`, hence
factors through a map $`\Zp[\GG_n]^+ \to \Zp[\GG_n^+]`. Both sides are free
$`\Zp`-modules of rank $`(p-1)p^{n-1}/2`, and the map sends a basis to a basis, so it
is an isomorphism. Passing to the inverse limit over $`n` gives
$`\Lam(\GG)^+ \cong \Lam(\GG^+)`. (The formalisation proves bijectivity by a
functional even-part section — $`\nu \mapsto \nu\circ(f \mapsto \tfrac12(f + f\circ c))`
inverts the pushforward on the plus part — rather than the finite-level rank count,
whose inverse-limit presentation of $`\Lam` is deferred infrastructure; same map,
different proof of bijectivity.)
:::

:::lemma_ "zeros-plus-criterion" (lean := "PadicMeasure.mem_plusPart_iff_forall_odd_moment")
Let $`\mu \in \Lam(\GG)`. Then $`\mu \in \Lam(\GG^+)` if and only if
$$`\int_{\GG}\chi(x)^k\,d\mu = 0 \quad\text{for all odd } k \ge 1.`
This uses {uses "zeros-plus-minus-decomposition"}[].
:::

:::proof "zeros-plus-criterion"
By {uses "zeros-plus-minus-decomposition"}[] write $`\mu = \mu^+ + \mu^-` with
$`\mu^\pm = \tfrac{1\pm c}{2}\mu`; membership in $`\Lam(\GG^+) = \Lam(\GG)^+` means
exactly $`\mu^- = 0`. Since $`\chi(c) = -1`, the change of variables $`x \mapsto cx`
shows
$$`\int_\GG\chi(x)^k\,d\mu^+ = \tfrac12\Big(\int_\GG\chi^k\,d\mu + (-1)^k\int_\GG\chi^k\,d\mu\Big),`
which vanishes for odd $`k` and equals $`\int_\GG\chi^k\,d\mu` for even $`k`. The same
computation with $`\mu^-` shows $`\int_\GG\chi^k\,d\mu^- = 0` for all *even* $`k`,
while $`\int_\GG\chi^k\,d\mu^- = \int_\GG\chi^k\,d\mu` for all *odd* $`k`. Thus the
hypothesis "$`\int_\GG\chi^k\,d\mu = 0` for all odd $`k\ge1`" is equivalent to
"$`\int_\GG\chi^k\,d\mu^- = 0` for all $`k\ge1`". A measure on $`\Zpx`$ whose moments
$`\int x^k\,d\mu^-` vanish for every $`k > 0` is itself zero, since these moments are
the higher coefficients of its Mahler transform and the transform of a measure
supported on $`\Zpx`$ has vanishing constant term. Hence $`\mu^- = 0` precisely when
the odd moments of $`\mu` vanish.
:::

:::corollary "zeros-zeta-p-pseudo-measure-plus" (lean := "PadicMeasure.padicZetaPlus, PadicMeasure.isPlusPseudoMeasure_padicZetaPlus, PadicMeasure.dirac_neg_one_sub_one_mul_padicZeta")
The $`p`-adic zeta function $`\zeta_p` is a pseudo-measure on $`\GG^+`. This uses the
{uses "interpolation-property"}[interpolation property] and
{uses "zeros-plus-criterion"}[].
:::

:::proof "zeros-zeta-p-pseudo-measure-plus"
By the {uses "interpolation-property"}[interpolation property] the moment
$`\int_\GG\chi(x)^k\,d\zeta_p` equals, up to the Euler factor at $`p`, the value
$`(1-p^{k-1})\,\zeta(1-k)` of the Riemann zeta function at the trivial character.
For odd $`k \ge 1` this vanishes: when $`k \ge 3` is odd, $`1-k` is a negative even
integer, so $`\zeta(1-k) = 0` is a trivial zero of $`\zeta`; and at $`k = 1` the
$`p`-adic Euler factor $`(1-p^{k-1}) = 1-p^0 = 0` itself kills the moment (here
$`\zeta(0) = -\tfrac12 \neq 0`, so it is the Euler factor that is responsible —
the source's proof line "$`\zeta(1-k) = 0` for odd $`k \ge 1`" overlooks this
$`k = 1` case; erratum #13 of the formalisation's errata file).
Hence all odd moments of $`\zeta_p` vanish. Applying the plus-part criterion
{uses "zeros-plus-criterion"}[] to the measure $`([g]-[1])\zeta_p \in \Lam(\GG)`,
whose odd moments are $`(\chi(g)^k - 1)\int_\GG\chi^k\,d\zeta_p = 0`, shows it lies in
$`\Lam(\GG^+)` for every $`g`; therefore $`\zeta_p` descends to a pseudo-measure on
$`\GG^+`.
:::

# The ideal generated by the p-adic zeta function

It is natural to ask about the zeros of $`\zeta_p`. As multiplying a measure by a
unit does not change its zeros, studying the zeros of a measure on $`\GG` is the same
as studying the *ideal* it generates in $`\Lam(\GG)`. Although $`\zeta_p` is only a
pseudo-measure, and hence not itself an element of $`\Lam(\GG)`, it still generates a
natural ideal.

Recall the *augmentation ideal* $`I(\GG) = \ker\big(\Lam(\GG) \to \Zp\big)`, where the
augmentation map $`\Lam(\GG) \twoheadrightarrow \Zp` is induced by $`[g] \mapsto 1`
for every $`g \in \GG`; equivalently, $`I(\GG)` is the topological ideal generated by
the elements $`[g] - [1]`, $`g \in \GG`. The ideal $`I(\GG^+)` is defined the same
way. By the defining property of a pseudo-measure, $`([g]-[1])\zeta_p \in \Lam(\GG)`
for every $`g \in \GG`.

:::proposition "ideal-of-zeta-p" (lean := "PadicMeasure.zetaIdeal, PadicMeasure.zetaIdealPlus, PadicMeasure.zetaIdeal_eq_span, PadicMeasure.zetaIdealPlus_eq_span, PadicMeasure.augmentationIdealPlus_eq_span")
The module $`I(\GG)\,\zeta_p` is an ideal of $`\Lam(\GG)`, and likewise
$`I(\GG^+)\,\zeta_p` is an ideal of $`\Lam(\GG^+)`. This uses the
{uses "pseudo-measure"}[pseudo-measure] property of
{uses "kubota-leopoldt"}[$`\zeta_p`] and
{uses "zeros-zeta-p-pseudo-measure-plus"}[].
:::

:::proof "ideal-of-zeta-p"
Since $`\zeta_p` is a pseudo-measure, each product $`([g]-[1])\zeta_p` lies in
$`\Lam(\GG)`. As $`I(\GG)` is the topological ideal generated by the elements
$`[g]-[1]`, the set $`I(\GG)\zeta_p` is closed under multiplication by $`\Lam(\GG)`
and is therefore an ideal. The identical argument over $`\GG^+`, using that
$`\zeta_p` is a pseudo-measure on $`\GG^+`, shows $`I(\GG^+)\zeta_p` is an ideal of
$`\Lam(\GG^+)`.
:::

# Cyclotomic units and Iwasawa's theorem

Iwasawa's theorem describes the ideal $`I(\GG)\zeta_p` in terms of the module of
cyclotomic units. We recall this module and its classical link to class numbers, and
then state the theorem.

:::definition "zeros-cyclotomic-units-global" (lean := "PadicLFunctions.Coleman.Fglobal, PadicLFunctions.Coleman.FglobalPlus, PadicLFunctions.Coleman.globalUnits, PadicLFunctions.Coleman.cycloUnits, PadicLFunctions.Coleman.cycloUnitsPlus")
For $`n \ge 1`, the group $`\DD_n` of *cyclotomic units* of $`F_n` is the
intersection of $`\cO_{F_n}^\times` with the multiplicative subgroup of $`F_n^\times`
generated by $`\set{\pm\xi_{p^n},\ \xi_{p^n}^a - 1 : 1 \le a \le p^n - 1}`, where
$`\xi_{p^n}` is a primitive $`p^n`-th root of unity. We set
$`\DD_n^+ = \DD_n \cap F_n^+`.
:::

The cyclotomic units are connected to class numbers as follows.

:::theorem "zeros-cyclo-units-class-number"
Let $`n \ge 1`. The group $`\DD_n` (resp. $`\DD_n^+`) has finite index in the unit
group $`\VV_n` (resp. $`\VV_n^+`) of $`F_n` (resp. $`F_n^+`), and
$$`h_n^+ = [\VV_n : \DD_n] = [\VV_n^+ : \DD_n^+],`
where $`h_n^+ = \#\Cl(F_n^+)` is the class number of $`F_n^+`. This uses
{uses "zeros-cyclotomic-units-global"}[].
:::

:::proof "zeros-cyclo-units-class-number"
We do not reprove this here; see {Informal.citep "washington"}[Theorem 8.2]. The
argument computes the regulator of the cyclotomic units $`\DD_n^+` as a determinant
of logarithms of $`1-\xi_{p^n}^a`, which by Dirichlet's class number formula is
expressed through the special values at $`s = 1` of the
{uses "dirichlet-L-function"}[Dirichlet $`L`-functions] of the even characters of
$`\Gal(F_n^+/\Q)`. Comparing this with the analytic class number formula for
$`F_n^+`, whose regulator is that of the *full* unit group $`\VV_n^+`, the two
regulators differ exactly by the index $`[\VV_n^+ : \DD_n^+]`, which therefore equals
the class number $`h_n^+`.
:::

As explained in the construction of the Coleman map, the cyclotomic units $`c_n(a)`
used to build $`\zeta_p` are naturally elements of $`\DD_n`, hence *global*; one then
takes their image in the *local* units and applies the (purely local) Coleman map.
In the same spirit we now pass from the global
modules $`\DD_n, \DD_n^+` to their closures inside the local units. (Formalised:
the $`\DD_n`-membership of $`c_n(a)` is
`PadicLFunctions.Coleman.cyclo_elems_mem_cycloUnits`, unconditional in
$`a` coprime to $`p`; its norm-compatible tower lies in $`\CC_{\infty,1}` —
`PadicLFunctions.Coleman.cyclo_mem_cycloTower1` — under the additional
hypothesis $`a \equiv 1 \bmod p`, since $`c_n(a) \equiv a \bmod \pri_n` is a
principal unit only then; the principal-unit normalisation for general $`a` is
part of the next chapter's fundamental exact sequence.) Recall that
$`\UU_{\infty,1}^+` denotes the group of norm-compatible local units congruent to
$`1 \bmod p`.

:::definition "zeros-local-cyclotomic-units" (lean := "PadicLFunctions.Coleman.cycloClosure, PadicLFunctions.Coleman.cycloClosureOne, PadicLFunctions.Coleman.cycloTower1, PadicLFunctions.Coleman.cycloTower1Plus, PadicLFunctions.Coleman.unitsTower1, PadicLFunctions.Coleman.localUnitsOne")
For $`n \ge 1`, let $`\CC_n` be the $`p`-adic closure of $`\DD_n` inside the local
units $`\UU_n`, set $`\CC_n^+ = \CC_n \cap \UU_n^+`, and define
$$`\CC_{n,1} = \CC_n \cap \UU_{n,1}, \qquad \CC_{n,1}^+ = \CC_n^+ \cap \UU_{n,1}.`
Passing to the inverse limit over the norm maps, set
$$`\CC_{\infty,1} = \varprojlim_{n \ge 1}\CC_{n,1}, \qquad \CC_{\infty,1}^+ = \varprojlim_{n \ge 1}\CC_{n,1}^+.`
This is the local avatar of {uses "zeros-cyclotomic-units-global"}[].
:::

The module $`\UU_{\infty,1}^+`, and its quotient $`\UU_{\infty,1}^+/\CC_{\infty,1}^+`,
carry natural $`\Lam(\GG^+)`-module structures. Iwasawa related this quotient
explicitly to the $`p`-adic zeta function: the cyclotomic units capture exactly the
zeros of $`\zeta_p`. This is the theorem that ultimately motivated his Main
Conjecture.

:::theorem "iwasawa-zeros-theorem" (lean := "PadicLFunctions.Coleman.iwasawa_theorem")
The Coleman map induces an isomorphism of $`\Lam(\GG^+)`-modules
$$`\UU_{\infty,1}^+ / \CC_{\infty,1}^+ \xrightarrow{\sim} \Lam(\GG^+) / I(\GG^+)\,\zeta_p.`
This rests on the {uses "coleman-map"}[Coleman map], the ideal
{uses "ideal-of-zeta-p"}[$`I(\GG^+)\zeta_p`], and the local cyclotomic units
{uses "zeros-local-cyclotomic-units"}[].
:::

:::proof "iwasawa-zeros-theorem"
The proof is carried out in the next chapter; we sketch its spine. By
{uses "coleman-equivariance"}[equivariance of the Coleman map] the map
$`\Col : \UU_{\infty,1} \to \Lam(\GG)` is a homomorphism of $`\Lam(\GG)`-modules,
where the $`\GG`-equivariance hinges on the renormalising twist by $`1` built into
$`\zeta_p`. The {uses "fundamental-exact-sequence"}[fundamental exact sequence]
$`0 \to \Zp(1) \to \UU_{\infty,1} \xrightarrow{\Col} \Lam(\GG) \to \Zp(1) \to 0`
identifies the cokernel of $`\Col` with $`\Zp(1)`, the map to it being
$`\mu \mapsto \int_\GG\chi\,d\mu`. Passing to the plus parts (legitimate since $`p`
is odd, by {uses "zeros-plus-minus-decomposition"}[]) yields an injection
$`\UU_{\infty,1}^+ \hookrightarrow \Lam(\GG^+)` whose cokernel is computed by the
augmentation map. On the local cyclotomic units the Coleman map reproduces exactly
the construction of $`\zeta_p` out of the {uses "cyclotomic-units"}[cyclotomic units]
$`c_n(a)`, so $`\Col(\CC_{\infty,1}^+)` is precisely the ideal
{uses "ideal-of-zeta-p"}[$`I(\GG^+)\zeta_p`]. Therefore $`\Col` descends to the
displayed isomorphism $`\UU_{\infty,1}^+/\CC_{\infty,1}^+ \xrightarrow{\sim}
\Lam(\GG^+)/I(\GG^+)\zeta_p` of quotient $`\Lam(\GG^+)`-modules.
:::

The quotient $`\UU_{\infty,1}^+/\CC_{\infty,1}^+` is the infinite-level local analogue
of the cyclotomic units inside the global units, whose indices compute class numbers
in the cyclotomic tower. These modules are in turn related to the Galois modules
appearing in the Iwasawa Main Conjecture. This theorem is thus the first step towards
the deep connection between class groups and the $`p`-adic zeta function expressed by
the Main Conjecture.
