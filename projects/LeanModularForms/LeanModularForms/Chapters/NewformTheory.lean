import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq
import LeanModularForms.HeckeRIngs.GL2.FourierHecke

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Newforms and the Atkin–Lehner Main Lemma" =>

The old/new decomposition of the cusp space at level $`\Gamma_1(N)`, whose two pieces $`S_k^{\flat}(N)`
and $`S_k^{\sharp}(N)` were introduced in the Strong Multiplicity One chapter, is here shown to be a genuine
internal direct sum: every cusp form splits uniquely into an oldform and a newform component. The engine
is the Atkin–Lehner Main Lemma \[DS, Thm 5.7.1\], which says that a cusp form whose Fourier coefficients
vanish at all indices coprime to the level $`N` necessarily descends from a lower level, i.e. it is old.
On the eigenform side the same circle of ideas identifies a newform's Hecke eigenvalues with its Fourier
coefficients $`a_n`, and shows these coefficients are multiplicative in $`n`. The development follows
\[DS, §5.6–5.8\] and \[Miy, §4.6\].

:::theorem "old-new-isCompl" (lean := "HeckeRing.GL2.cuspFormsOld_isCompl_cuspFormsNew")
*Old/new direct-sum decomposition, $`\mathrm{DS}` (5.20).*
The cusp space at level $`\Gamma_1(N)` is the internal direct sum of its old and new subspaces,
$$`
  S_k(\Gamma_1(N)) \;=\; S_k^{\flat}(N) \,\oplus\, S_k^{\sharp}(N).
`
Equivalently, the two subspaces are *complementary*: they intersect trivially,
$`S_k^{\flat}(N)\cap S_k^{\sharp}(N)=0`, and together they span the whole cusp space,
$`S_k^{\flat}(N)+S_k^{\sharp}(N)=S_k(\Gamma_1(N))`.

Depends on: {uses "cuspFormsOld"}[] {uses "cuspFormsNew"}[] {uses "petN-definite"}[]
:::

:::proof "old-new-isCompl"
This is the orthogonal-complement form of \[DS, (5.20)\]. The new subspace was defined as the Petersson
orthogonal complement of the old subspace, $`S_k^{\sharp}(N)=\bigl(S_k^{\flat}(N)\bigr)^{\perp}`. Trivial
intersection is immediate from positive-definiteness of the Petersson inner product: a form lying in both
$`S_k^{\flat}(N)` and its orthogonal complement is orthogonal to itself, so its Petersson norm vanishes, and
positive-definiteness forces it to be $`0`. Hence $`S_k^{\flat}(N)\cap S_k^{\sharp}(N)=0`.

For the spanning property one passes to the underlying real inner product space. The cusp space is
finite-dimensional, and on a finite-dimensional space carrying a nondegenerate reflexive bilinear form a
subspace and its orthogonal complement are always complementary; concretely, a subspace disjoint from its
orthogonal complement together with that complement spans the whole space. Applying this to $`S_k^{\flat}(N)`
and the real form attached to the Petersson product, and recognising the resulting orthogonal complement as
$`S_k^{\sharp}(N)`, yields $`S_k^{\flat}(N)+S_k^{\sharp}(N)=S_k(\Gamma_1(N))`. Combining the trivial
intersection with the spanning gives the asserted complementarity, i.e. the internal direct-sum
decomposition.
:::

:::theorem "atkin-lehner-main-lemma" (lean := "HeckeRing.GL2.mainLemma")
*Atkin–Lehner Main Lemma, \[DS, Thm 5.7.1\] / \[Miy, §4.6\].*
Let $`f\in S_k(\Gamma_1(N))` be a cusp form, and write its Fourier expansion at the canonical width as
$`f(\tau)=\sum_{n\ge 1} a_n\,q^{n}`. Suppose every Fourier coefficient indexed by an integer coprime to the
level vanishes,
$$`
  a_n \;=\; 0 \qquad\text{for all } n\ge 1 \text{ with } (n,N)=1.
`
Then $`f` is an *oldform*: it lies in the old subspace $`S_k^{\flat}(N)`, i.e. $`f` is a linear combination of
level-raised forms coming from proper divisors of $`N`. Thus the only obstruction to descending to a lower
level is concentrated entirely in the coefficients $`a_n` with $`(n,N)>1`; vanishing of the coprime
coefficients already forces $`f` to be old.

Depends on: {uses "cuspFormsOld"}[] {uses "cuspFormsNew"}[] {uses "eigenform"}[] {uses "coeff-eq-a1-lambda"}[] {uses "eigenform-decomp"}[]
:::

:::proof "atkin-lehner-main-lemma"
The argument isolates the new component of $`f` and shows it must vanish. By the old/new direct-sum
decomposition ({bpref "old-new-isCompl"}[]) split $`f=f^{\flat}+f^{\sharp}` with $`f^{\flat}\in S_k^{\flat}(N)`
old and $`f^{\sharp}\in S_k^{\sharp}(N)` new; it suffices to prove $`f^{\sharp}=0`, for then $`f=f^{\flat}` is
old. Subtracting the old part changes no coefficient indexed coprime to $`N`, because the level-raising maps
generating $`S_k^{\flat}(N)` insert factors $`\ell>1` dividing $`N` and so contribute only at indices sharing
a factor with $`N`; hence the new part $`f^{\sharp}` again has $`a_n(f^{\sharp})=0` for every $`n` coprime to
$`N`. The new subspace is spanned by simultaneous Hecke eigenforms away from the level
({bpref "eigenform-decomp"}[]), so it is enough to show $`f^{\sharp}` is Petersson-orthogonal to every such eigenform
$`g\in S_k^{\sharp}(N)`. Fixing $`g` and its Nebentypus character $`\chi`, the diamond and Hecke operators are
self-adjoint up to the character with respect to the Petersson inner product, which lets the action of $`T(n)`
be moved across the pairing.

Concretely, for $`n` coprime to $`N` the eigenvalue identity $`T(n)g=\lambda_n g` together with the adjoint
relation gives $`\overline{\lambda_n}\,\langle f^{\sharp},g\rangle=\langle f^{\sharp},T(n)g\rangle=\langle
T(n)f^{\sharp},g\rangle`, and the $`n`-th coprime coefficient of $`T(n)f^{\sharp}` is a fixed nonzero multiple
of $`a_n(f^{\sharp})=0` ({bpref "coeff-eq-a1-lambda"}[] expressing the coprime coefficients through the
eigenvalues). Running over a generating set of indices, the eigenvalues away from the level cannot all be
zero on a nonzero eigenform — its leading coefficient would otherwise vanish — so one may divide out by a
nonzero $`\lambda_n` and conclude $`\langle f^{\sharp},g\rangle=0`. As this holds for every eigenform spanning
$`S_k^{\sharp}(N)`, the new part $`f^{\sharp}` is orthogonal to the whole new subspace, hence orthogonal to
itself; positive definiteness of the Petersson product forces $`f^{\sharp}=0`, and therefore $`f=f^{\flat}\in
S_k^{\flat}(N)` is old.
:::

:::theorem "newform-eigenvalue-eq-coeff" (lean := "HeckeRing.GL2.Newform.eigenvalue_eq_coeff")
*Eigenvalue equals Fourier coefficient for a normalised newform, \[Miy, Thm 4.5.16\] / \[DS, Prop 5.8.5\].*
Let $`f` be a newform of level $`\Gamma_1(N)` and weight $`k`, and suppose $`f` carries the Nebentypus
character $`\chi`, so that $`f` lies in the eigenspace $`S_k(N,\chi)`. For every index $`n\ge 1` coprime to the
level, $`(n,N)=1`, the classical Hecke eigenvalue of $`f` at $`n` coincides with its $`n`-th Fourier
coefficient at the canonical width,
$$`
  \lambda_n(f) \;=\; a_n(f).
`
This is the normalised form of the eigenvalue–coefficient identity: because a newform is normalised so that
$`a_1(f)=1`, the general relation $`a_n=a_1\lambda_n` collapses to an outright equality between the eigenvalue
and the coefficient. The character hypothesis is what places $`f` in a single Nebentypus eigenspace, where the
Fourier coefficients of the Hecke transforms take their multiplicative form.

Depends on: {uses "newform"}[] {uses "coeff-eq-a1-lambda"}[]
:::

:::proof "newform-eigenvalue-eq-coeff"
Specialise the un-normalised identity $`a_n(f)=a_1(f)\,\lambda_n(f)` ({bpref "coeff-eq-a1-lambda"}[]),
valid for any eigenform in the Nebentypus space $`S_k(N,\chi)` and any $`n` coprime to $`N`, to the normalised
case. By the definition of a newform ({bpref "newform"}[]) the leading coefficient is $`a_1(f)=1`, so the
factor $`a_1(f)` drops out and the relation becomes $`a_n(f)=\lambda_n(f)`, which is the asserted equality
$`\lambda_n(f)=a_n(f)`.

Uses: {uses "newform"}[] {uses "coeff-eq-a1-lambda"}[]
:::

:::theorem "eigenform-coeff-multiplicative" (lean := "HeckeRing.GL2.eigenform_coeff_multiplicative_one")
*Multiplicativity of the Fourier coefficients of a normalised eigenform, \[Miy, Thm 4.5.16\] / \[DS, Prop 5.8.5\].*
Let $`f` be a normalised eigenform of weight $`k` and level $`\Gamma_1(N)` carrying the Nebentypus character
$`\chi`, so that $`f` lies in the eigenspace $`S_k(N,\chi)` and is normalised at the canonical width with
$`a_1(f)=1`. Let $`m,n\ge 1` be two indices, each coprime to the level, $`(m,N)=(n,N)=1`. Then the product of
the corresponding Fourier coefficients is the divisor sum
$$`
  a_m(f)\,a_n(f) \;=\; \sum_{d\,\mid\,(m,n)} d^{\,k-1}\,\chi(d)\,a_{mn/d^2}(f).
`
In particular, when $`m` and $`n` are coprime, $`(m,n)=1`, the sum collapses to its single $`d=1` term and the
coefficients are *multiplicative*,
$$`
  a_{mn}(f) \;=\; a_m(f)\,a_n(f).
`

Depends on: {uses "newform-eigenvalue-eq-coeff"}[] {uses "coeff-eq-a1-lambda"}[] {uses "T-sum-mul-coprime"}[]
:::

:::proof "eigenform-coeff-multiplicative"
The identity transports the multiplicativity of the Hecke eigenvalues to the Fourier coefficients. Apply the
Hecke operator $`T(m)` to $`f`. Because $`f` is an eigenform, $`T(m)f=\lambda_m(f)\,f`, and reading off the
$`n`-th coefficient gives $`a_n\bigl(T(m)f\bigr)=\lambda_m(f)\,a_n(f)`. Under the normalisation $`a_1(f)=1` the
eigenvalue coincides with the first-index coefficient, $`\lambda_m(f)=a_m(f)` ({bpref "newform-eigenvalue-eq-coeff"}[],
itself the normalised form of $`a_n=a_1\lambda_n` from {bpref "coeff-eq-a1-lambda"}[]), so the left-hand side
becomes $`a_m(f)\,a_n(f)`. On the other hand the explicit Fourier-coefficient formula for $`T(m)f` in the
Nebentypus space expresses $`a_n\bigl(T(m)f\bigr)` as the divisor sum $`\sum_{d\mid(m,n)} d^{\,k-1}\,\chi(d)\,
a_{mn/d^2}(f)`. Equating the two expressions for $`a_n\bigl(T(m)f\bigr)` yields the stated relation.

This is the coefficient shadow of the multiplication table for the Hecke operators: the same relation arises
because the eigenvalues inherit the algebra identity $`\lambda_m\lambda_n=\lambda_{mn}` from
$`T(m)\,T(n)=T(mn)` for coprime indices ({bpref "T-sum-mul-coprime"}[]). When $`(m,n)=1` the greatest common
divisor is $`1`, so the divisor sum reduces to its $`d=1` term $`a_{mn}(f)`, and the identity specialises to the
multiplicativity $`a_{mn}(f)=a_m(f)\,a_n(f)`.

Uses: {uses "newform-eigenvalue-eq-coeff"}[] {uses "coeff-eq-a1-lambda"}[] {uses "T-sum-mul-coprime"}[]
:::
