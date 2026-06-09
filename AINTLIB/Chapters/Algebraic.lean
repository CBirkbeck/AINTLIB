import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.ChevalleyWarning

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic Number Theory" =>

This chapter covers number fields and their rings of integers, integral bases and the
trace and norm forms, ideal factorisation in Dedekind domains, fractional ideals and the
ideal class group, the absolute ideal norm and the adic valuations of the height-one
spectrum, the discriminant and its connection to the different ideal, Minkowski's bound and
the finiteness of the class group, Hermite's and Hermite–Minkowski's theorems, Kronecker's
theorem, the Dirichlet unit theorem, ramification theory and the fundamental identity,
Chevalley–Warning, and the arithmetic of cyclotomic extensions. Throughout, $`K` denotes a
number field, $`\mathcal{O}_K` its ring of integers, $`n = [K:\mathbb{Q}]` its degree,
$`\mathrm{Cl}(K)` its class group, $`\mathfrak{p}` a prime ideal, and $`r_1, r_2` the
numbers of real and of conjugate-pairs of complex embeddings of $`K`. Every mathlib-backed
node carries a `(lean := …)` reference naming the exact declaration, and its proof sketch
follows the argument that declaration actually uses, naming the lemmas the proof invokes.
The external nodes are informal — the source projects build against mathlib versions that
differ from AINTLIB's — and each records the declaration that formalises it, an exact-source
permalink, and whether that formalisation is sorry-free or still in progress.

# Number fields and their rings of integers

## Number Field

:::definition "number-field" (lean := "NumberField")
A *number field* is a field $`K` that is of characteristic zero and finite-dimensional over
$`\mathbb{Q}`. Equivalently, $`K` is a finite algebraic extension of $`\mathbb{Q}`, and its
degree $`[K : \mathbb{Q}]` is a positive integer.
:::

## Ring of Integers

:::definition "ring-of-integers" (lean := "NumberField.RingOfIntegers")
The *ring of integers* $`\mathcal{O}_K` of a number field $`K` ({uses "number-field"}[]) is
the integral closure of $`\mathbb{Z}` in $`K`: the subring of all elements of $`K` that
satisfy a monic polynomial equation with integer coefficients. In mathlib $`\mathcal{O}_K`
is the type `integralClosure ℤ K`, equipped with its induced commutative-ring structure.
:::

## The Ring of Integers Is a Free Module

:::theorem "ring-of-integers-free" (lean := "NumberField.RingOfIntegers.basis, NumberField.integralBasis")
As a $`\mathbb{Z}`-module, $`\mathcal{O}_K` ({uses "ring-of-integers"}[]) is free of finite
rank equal to $`[K:\mathbb{Q}]`; a $`\mathbb{Z}`-basis $`\omega_1, \dots, \omega_n` of
$`\mathcal{O}_K` is called an *integral basis*, and its image in $`K` is a $`\mathbb{Q}`-basis
of $`K` (the `integralBasis`).
:::

:::proof "ring-of-integers-free"
$`\mathcal{O}_K` is torsion-free as a $`\mathbb{Z}`-module (it embeds in the
characteristic-zero field $`K`), and it is finitely generated because the integral closure
of $`\mathbb{Z}` in the finite separable extension $`K/\mathbb{Q}` is a finite
$`\mathbb{Z}`-module (`IsIntegralClosure.finite`). A finitely generated torsion-free module
over the principal ideal domain $`\mathbb{Z}` is free, giving the `Free ℤ (𝓞 K)` instance.
Localising a chosen $`\mathbb{Z}`-basis at the nonzero divisors of $`\mathbb{Z}`
(`Basis.localizationLocalization`) turns it into a $`\mathbb{Q}`-basis of $`K`, which is the
`integralBasis`; in particular the rank equals $`[K:\mathbb{Q}]`.
:::

## Trace, Norm, and Trace Form

:::definition "trace-norm-form" (lean := "Algebra.trace, Algebra.norm, Algebra.traceForm")
For a finite extension $`K/\mathbb{Q}` and $`x \in K`, the *trace* $`\mathrm{Tr}_{K/\mathbb{Q}}(x)`
and *norm* $`N_{K/\mathbb{Q}}(x)` are the trace and determinant of the $`\mathbb{Q}`-linear
multiplication-by-$`x` map on $`K`; the trace is $`\mathbb{Q}`-linear and the norm is
multiplicative. The *trace form* is the symmetric $`\mathbb{Q}`-bilinear form
$$`b(x, y) = \mathrm{Tr}_{K/\mathbb{Q}}(xy),`
which is nondegenerate exactly because $`K/\mathbb{Q}` is separable.
:::

# Dedekind domains and unique factorisation of ideals

## Dedekind Domain

:::definition "dedekind-domain" (lean := "IsDedekindDomain")
A *Dedekind domain* is a Noetherian, integrally closed integral domain of Krull dimension at
most one — equivalently, in which every nonzero prime ideal is maximal. Such a domain is
characterised by the property that every nonzero ideal factors uniquely as a product of prime
ideals.
:::

## The Ring of Integers Is a Dedekind Domain

:::theorem "ring-of-integers-is-dedekind" (lean := "IsIntegralClosure.isDedekindDomain")
The ring of integers $`\mathcal{O}_K` of any number field $`K` is a Dedekind domain.
:::

:::proof "ring-of-integers-is-dedekind"
mathlib's `IsIntegralClosure.isDedekindDomain` verifies the three defining properties
({uses "dedekind-domain"}[]) for the integral closure $`C` of a Dedekind domain $`A` in a
finite separable extension $`L` of $`\mathrm{Frac}(A)`; the number-field case is $`A =
\mathbb{Z}`, $`L = K`, $`C = \mathcal{O}_K`. The closure is integrally closed by transitivity
of integral closures (`IsIntegralClosure.isIntegrallyClosed`); it is a finite $`A`-module,
hence Noetherian, because the trace form is nondegenerate over the separable extension
({uses "trace-norm-form"}[], `IsIntegralClosure.finite`); and every nonzero prime of $`C` is
maximal because $`C` is integral over the dimension-one domain $`A`
(`IsIntegralClosure.isMaximal_of_isMaximal_comap` together with the going-up property), so
$`\mathcal{O}_K/\mathfrak{p}` is a field.
:::

## Unique Factorisation of Ideals

:::theorem "ideal-unique-factorization" (lean := "Ideal.uniqueFactorizationMonoid")
In any Dedekind domain $`R` ({uses "dedekind-domain"}[]) — in particular in $`\mathcal{O}_K` —
the monoid of nonzero ideals is a unique factorisation monoid: every nonzero ideal $`I
\subseteq R` factors as a product of prime ideals
$$`I = \mathfrak{p}_1^{e_1} \cdots \mathfrak{p}_r^{e_r},`
with the $`\mathfrak{p}_i` distinct and $`e_i \ge 1`, uniquely up to the order of the factors.
:::

:::proof "ideal-unique-factorization"
This is the ideal-theoretic form of the fundamental theorem of arithmetic
({uses "fta-existence"}[]): in a Dedekind domain elements need not factor uniquely, but
*ideals* do. mathlib derives `UniqueFactorizationMonoid (Ideal R)` from the fact that the
nonzero ideals of a Dedekind domain are cancellative and the divisibility order is the
reverse-inclusion order with the descending-chain condition; concretely the result is read off
from `Ideal.isPrincipalIdealRing` failing but the *fractional* ideals forming a free abelian
group on the nonzero primes ({bpref "fractional-ideal-group"}[]). Existence of a factorisation
uses the Noetherian (ascending chain) condition; uniqueness uses cancellation of the invertible
prime factors, which is exactly the invertibility supplied by the fractional-ideal group.
:::

# Fractional ideals and the class group

## Fractional Ideals

:::definition "fractional-ideal" (lean := "FractionalIdeal")
Let $`R` be a domain with fraction field $`K`. A *fractional ideal* of $`R` is an
$`R`-submodule $`J \subseteq K` for which there exists a nonzero $`d \in R` with $`dJ
\subseteq R` — that is, an "ideal with denominators". Ordinary ideals are the integral
fractional ideals; products and (for a Dedekind domain) inverses of fractional ideals are
again fractional ideals.
:::

## Nonzero Fractional Ideals Form an Abelian Group

:::theorem "fractional-ideal-group" (lean := "IsDedekindDomainInv.commGroupWithZero")
For a Dedekind domain $`R` ({uses "dedekind-domain"}[]) with fraction field $`K`, the nonzero
fractional ideals ({uses "fractional-ideal"}[]) form an abelian group under multiplication, with
identity $`R` and inverse $`J^{-1} = \{x \in K : xJ \subseteq R\}`; including the zero ideal,
$`\mathrm{FractionalIdeal}(R^\circ, K)` is a commutative group with zero. This group is free
abelian on the set of nonzero prime ideals of $`R`.
:::

:::proof "fractional-ideal-group"
The only nontrivial axiom is that every nonzero fractional ideal $`J` is invertible, i.e.
$`J \cdot J^{-1} = R`. mathlib packages this as `IsDedekindDomainInv`, the statement that
$`I \cdot I^{-1} = 1` for all nonzero $`I`, which is equivalent to $`R` being Dedekind
(`isDedekindDomain_iff_isDedekindDomainInv`); the `commGroupWithZero` instance then reads off
`mul_inv_cancel` from this together with `inv_zero` and the division-as-multiplication law. The
free-abelian structure follows because invertibility lets one cancel primes, so the unique
factorisation of ideals ({uses "ideal-unique-factorization"}[]) extends to a $`\mathbb{Z}`-valued
valuation at each prime, giving an isomorphism with the free abelian group $`\bigoplus_{\mathfrak
p}\mathbb{Z}`.
:::

## The Ideal Class Group

:::definition "class-group" (lean := "ClassGroup")
The *class group* $`\mathrm{Cl}(R)` of a Dedekind domain $`R` (e.g. $`R = \mathcal{O}_K`,
{uses "ring-of-integers"}[]) is the quotient of the group of nonzero fractional ideals
({uses "fractional-ideal-group"}[]) by the subgroup of nonzero principal fractional ideals:
$$`\mathrm{Cl}(R) = \{\text{nonzero fractional ideals of } R\} \;/\; \{\alpha R : \alpha \in K^\times\}.`
The class group is trivial if and only if $`R` is a principal ideal domain. In mathlib
$`\mathrm{Cl}(R)` is realised as the cokernel of the map $`K^\times \to (\mathrm{FractionalIdeal}\,R^\circ\,K)^\times`.
:::

# The absolute ideal norm and bounded-norm finiteness

## The Absolute Ideal Norm

:::definition "absolute-norm" (lean := "Ideal.absNorm")
The *absolute norm* of an ideal $`I` of $`\mathcal{O}_K` is the cardinality of the finite
quotient ring,
$$`N(I) = |\mathcal{O}_K / I| = [\mathcal{O}_K : I],`
with the convention $`N(\{0\}) = 0`. mathlib defines $`N` via the additive-subgroup index
$`[\mathcal{O}_K : I]` (`Submodule.cardQuot`) and bundles it as a monoid-with-zero homomorphism
$`\mathrm{absNorm} : \mathrm{Ideal}(\mathcal{O}_K) \to^{*0} \mathbb{N}`, so $`N(\{0\}) = 0`,
$`N(\mathcal{O}_K) = 1`, and $`N(IJ) = N(I)\,N(J)`.
:::

## Norm of a Principal Ideal Equals the Absolute Value of the Field Norm

:::lemma_ "absnorm-span-singleton" (lean := "Ideal.absNorm_span_singleton")
For a principal ideal the absolute norm is the absolute value of the field norm: for $`r \in
\mathcal{O}_K`,
$$`N\bigl((r)\bigr) = \bigl|N_{K/\mathbb{Q}}(r)\bigr|.`
:::

:::proof "absnorm-span-singleton"
Both sides are computed against a fixed $`\mathbb{Z}`-basis of $`\mathcal{O}_K`
({uses "ring-of-integers-free"}[]). The index of $`(r) = r\,\mathcal{O}_K` equals the absolute
value of the determinant of multiplication by $`r` written in that basis
(`natAbs_det_basis_change`, via the change-of-basis equivalence
`Basis.basisSpanSingleton`), and that determinant is by definition the field norm
$`N_{K/\mathbb{Q}}(r)` ({uses "trace-norm-form"}[]). For $`r = 0` both sides are $`0`.
:::

## Larger Ideals Have Smaller Norm

:::lemma_ "absnorm-monotone" (lean := "Ideal.absNorm_dvd_absNorm_of_le")
If $`J \subseteq I` are ideals of $`\mathcal{O}_K`, then $`N(I) \mid N(J)`
({uses "absolute-norm"}[]). In particular a larger ideal has a smaller norm, and $`N(I) = 1`
iff $`I = \mathcal{O}_K`.
:::

:::proof "absnorm-monotone"
The inclusion $`J \subseteq I` induces a surjection of finite quotients $`\mathcal{O}_K/J \to
\mathcal{O}_K/I`, so $`[\mathcal{O}_K : I]` divides $`[\mathcal{O}_K : J]`; this is the
multiplicativity of the subgroup index along the tower $`J \le I \le \mathcal{O}_K`
(`AddSubgroup.index_dvd_of_le`). Unwinding the definition of `absNorm`
({uses "absolute-norm"}[]) gives $`N(I) \mid N(J)`.
:::

## Finitely Many Ideals of Bounded Norm

:::theorem "finite-ideals-bounded-norm" (lean := "Ideal.finite_setOf_absNorm_le")
For every bound $`B \in \mathbb{N}`, there are only finitely many ideals of $`\mathcal{O}_K`
of absolute norm ({uses "absolute-norm"}[]) at most $`B`:
$$`\#\{\, I \subseteq \mathcal{O}_K : N(I) \le B \,\} < \infty.`
:::

:::proof "finite-ideals-bounded-norm"
It suffices to bound the ideals of each fixed norm $`m \le B` and take a finite union over
$`0 \le m \le B` (`Set.Finite.biUnion` over `Set.finite_Icc`). For fixed $`m`, an ideal $`I`
with $`N(I) = m` contains $`m \in \mathcal{O}_K` (since $`m` annihilates the order-$`m` group
$`\mathcal{O}_K/I`), so $`I` corresponds to a subgroup of the *finite* ring $`\mathcal{O}_K/(m)`
({uses "absnorm-monotone"}[]); there are only finitely many such, giving
`Ideal.finite_setOf_absNorm_eq`. The characteristic-zero hypothesis enters in ensuring
$`\mathcal{O}_K/(m)` is finite for $`m \ne 0`.
:::

# The discriminant and the different ideal

## The Discriminant of a Number Field

:::definition "discriminant" (lean := "NumberField.discr")
The *discriminant* $`\mathrm{disc}(K)` of a number field $`K` is the determinant of the trace
form ({uses "trace-norm-form"}[]) in an integral basis $`\omega_1, \dots, \omega_n` of
$`\mathcal{O}_K` ({uses "ring-of-integers-free"}[]):
$$`\mathrm{disc}(K) = \det\bigl(\mathrm{Tr}_{K/\mathbb{Q}}(\omega_i \omega_j)\bigr)_{1 \le i,j \le n} \in \mathbb{Z}.`
It is independent of the chosen integral basis (two integral bases differ by a matrix in
$`\mathrm{GL}_n(\mathbb{Z})`, whose determinant is $`\pm 1`), and its absolute value measures
the arithmetic complexity of $`K`.
:::

## Discriminant Agrees with the Trace Form Discriminant

:::theorem "discriminant-integral-basis" (lean := "NumberField.coe_discr")
The integer discriminant ({uses "discriminant"}[]) agrees with the discriminant of the trace
form computed in the rational integral basis $`\{\omega_i\}` of $`K`:
$$`\mathrm{disc}(K) = \mathrm{disc}_{\mathbb{Q}}\bigl(\mathrm{integralBasis}(K)\bigr) \in \mathbb{Q}.`
:::

:::proof "discriminant-integral-basis"
By definition $`\mathrm{disc}(K) = \mathrm{disc}_{\mathbb{Z}}(\mathrm{RingOfIntegers.basis}\,K)`,
the discriminant of the $`\mathbb{Z}`-basis of $`\mathcal{O}_K`. Localising
$`\mathbb{Z} \hookrightarrow \mathbb{Q}` and $`\mathcal{O}_K \hookrightarrow K` carries this
$`\mathbb{Z}`-basis to the rational `integralBasis` ({uses "ring-of-integers-free"}[]), and the
discriminant is invariant under this localisation (`Algebra.discr_localizationLocalization`),
giving the stated equality after the canonical inclusion $`\mathbb{Z} \hookrightarrow \mathbb{Q}`.
:::

## The Different Ideal

:::definition "different-ideal" (lean := "differentIdeal")
For an extension $`B/A` of Dedekind domains, the *different ideal* $`\mathfrak{d}_{B/A}
\subseteq B` is the inverse of the dual of $`B` with respect to the trace pairing
({uses "trace-norm-form"}[]): writing $`B^\vee = \{x \in \mathrm{Frac}(B) :
\mathrm{Tr}(xB) \subseteq A\}` for the codifferent, one sets
$$`\mathfrak{d}_{B/A} = (B^\vee)^{-1}.`
For $`B/A = \mathcal{O}_K/\mathbb{Z}` it is an integral ideal whose prime factorisation records
the ramification of $`K/\mathbb{Q}`.
:::

## The Norm of the Different Equals the Absolute Discriminant

:::theorem "different-discriminant" (lean := "NumberField.absNorm_differentIdeal")
The absolute norm ({uses "absolute-norm"}[]) of the different ideal
({uses "different-ideal"}[]) of $`\mathcal{O}_K` is the absolute value of the discriminant
({uses "discriminant"}[]):
$$`N(\mathfrak{d}_{\mathcal{O}_K/\mathbb{Z}}) = |\mathrm{disc}(K)|.`
:::

:::proof "different-discriminant"
mathlib's `absNorm_differentIdeal` identifies the index $`[\mathcal{O}_K : \mathfrak{d}]`
with the index of the codifferent inside $`\mathcal{O}_K`. The trace pairing gives a perfect
$`\mathbb{Z}`-bilinear duality between $`\mathcal{O}_K` and its dual $`\mathcal{O}_K^\vee`, so
$`[\mathcal{O}_K^\vee : \mathcal{O}_K] = |\det(\mathrm{Tr}(\omega_i\omega_j))| = |\mathrm{disc}(K)|`
({uses "discriminant-integral-basis"}[]). Since $`\mathfrak{d} = (\mathcal{O}_K^\vee)^{-1}`, the
fractional-ideal quotient $`\mathcal{O}_K/\mathfrak{d} \cong \mathcal{O}_K^\vee/\mathcal{O}_K`
(`FractionalIdeal.quotientEquiv`) has the same finite cardinality, namely
$`N(\mathfrak{d}) = |\mathrm{disc}(K)|`.
:::

## Transitivity of the Different

:::theorem "different-tower" (lean := "differentIdeal_eq_differentIdeal_mul_differentIdeal")
*(Transitivity of the different.)* For a tower $`A \subseteq B \subseteq C` of Dedekind
domains, the different ideal ({uses "different-ideal"}[]) is multiplicative:
$$`\mathfrak{d}_{C/A} = \mathfrak{d}_{C/B} \cdot (\mathfrak{d}_{B/A}\,C),`
where $`\mathfrak{d}_{B/A}\,C` is the extension of $`\mathfrak{d}_{B/A}` to $`C`.
:::

:::proof "different-tower"
The codifferent of a tower factors: an element pairs into $`A` against all of $`C` iff it
pairs into $`B` against all of $`C` and then into $`A` against all of $`B`, so $`C^\vee_{/A} =
C^\vee_{/B} \cdot (B^\vee_{/A}\,C)` by transitivity of the trace $`\mathrm{Tr}_{C/A} =
\mathrm{Tr}_{B/A}\circ\mathrm{Tr}_{C/B}` ({uses "trace-norm-form"}[]). Inverting and using
multiplicativity of inverse on fractional ideals ({uses "fractional-ideal-group"}[]) yields the
product formula; this is mathlib's `differentIdeal_eq_differentIdeal_mul_differentIdeal`. Taking
absolute norms recovers the tower formula for discriminants $`|\mathrm{disc}(C/A)| =
N(\mathfrak{d}_{C/B})\cdot|\mathrm{disc}(B/A)|^{[C:B]}` ({uses "different-discriminant"}[]).
:::

# Minkowski's bound and Hermite's theorem

## The Minkowski Bound

:::definition "minkowski-bound" (lean := "NumberField.mixedEmbedding.minkowskiBound")
For a number field $`K` and a nonzero fractional ideal $`I` ({uses "fractional-ideal"}[]), the
*Minkowski bound* is the covolume threshold
$$`\mathrm{Mink}(K, I) = 2^{\dim_{\mathbb{R}} K_{\mathbb{R}}}\,\mathrm{covol}(\Lambda_I),`
where $`K_{\mathbb{R}} = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}` is the mixed-embedding space
and $`\Lambda_I` is the lattice that $`I` spans in it. By Minkowski's convex-body theorem, any
symmetric convex body of volume exceeding this bound contains a nonzero point of $`\Lambda_I`,
which produces a nonzero element of $`I` of controlled archimedean size and hence of bounded
absolute norm ({uses "absolute-norm"}[]).
:::

## The Hermite–Minkowski Theorem

:::theorem "hermite-minkowski" (lean := "NumberField.abs_discr_gt_two")
*(Hermite–Minkowski.)* Every number field $`K` of degree $`[K:\mathbb{Q}] > 1` has
discriminant ({uses "discriminant"}[]) of absolute value strictly greater than $`2`:
$$`[K:\mathbb{Q}] > 1 \implies |\mathrm{disc}(K)| > 2.`
In particular $`\mathbb{Q}` is the only number field with $`|\mathrm{disc}| = 1`; there is no
nontrivial extension of $`\mathbb{Q}` unramified at every prime.
:::

:::proof "hermite-minkowski"
From the Minkowski bound ({uses "minkowski-bound"}[]) every nonzero ideal class has a
representative of norm at most $`M_K`, and taking $`I = \mathcal{O}_K` forces
$`M_K \ge 1`, i.e. $`\sqrt{|\mathrm{disc}(K)|} \ge (\pi/4)^{r_2}\,n^n/n!`. mathlib's
`abs_discr_ge` turns this into the lower bound $`|\mathrm{disc}(K)| \ge (4/9)(3\pi/4)^{n}` for
$`n \ge 2`. Since $`(4/9)(3\pi/4)^2 > 2` already (using $`\pi > 3`) and the right-hand side is
increasing in $`n`, one gets $`|\mathrm{disc}(K)| > 2` whenever $`n > 1`; the proof is the
`nlinarith`/`gcongr` chain `abs_discr_gt_two` from $`\pi > 3`.
:::

## Hermite's Theorem

:::theorem "hermite-finite" (lean := "NumberField.finite_of_discr_bdd")
*(Hermite's theorem.)* For every bound $`N \in \mathbb{N}`, there are only finitely many number
fields $`K` (inside a fixed algebraic closure of $`\mathbb{Q}`) with
$$`|\mathrm{disc}(K)| \le N.`
:::

:::proof "hermite-finite"
mathlib splits on the signature of a chosen infinite place of $`K`, handling totally-real-place
and complex-place witnesses separately (`finite_of_discr_bdd_of_isReal` and
`finite_of_discr_bdd_of_isComplex`), and takes the union. In each case the Minkowski bound
({uses "minkowski-bound"}[]) produces an algebraic integer $`x` whose conjugates are explicitly
bounded in terms of $`|\mathrm{disc}(K)| \le N`, with $`x` a primitive element so that
$`K = \mathbb{Q}(x)`. The bounded conjugates confine the minimal polynomial of $`x` to a finite
set of integer polynomials (`finite_of_finite_generating_set`), so only finitely many fields
arise; assembling the two cases is `finite_of_discr_bdd`.
:::

## Kronecker's Theorem

:::theorem "kronecker" (lean := "NumberField.Embeddings.pow_eq_one_of_norm_le_one")
*(Kronecker's theorem.)* Let $`K` be a number field and $`x \in K` a nonzero algebraic integer
({uses "ring-of-integers"}[]) all of whose conjugates lie in the closed unit disc — that is,
$`\|\varphi(x)\| \le 1` for every embedding $`\varphi : K \to \mathbb{C}`. Then $`x` is a root
of unity: $`x^{m} = 1` for some $`m \ge 1`.
:::

:::proof "kronecker"
The powers $`x, x^2, x^3, \dots` are all algebraic integers whose conjugates stay in the closed
unit disc, hence whose minimal polynomials have coefficients bounded in absolute value (the
$`k`-th symmetric function of numbers of modulus $`\le 1` is bounded). By the finiteness of
algebraic integers of bounded conjugates and bounded degree (`Embeddings.finite_of_norm_le`),
only finitely many distinct values occur among the $`x^k`, so the infinite pigeonhole
(`Set.Infinite.exists_ne_map_eq_of_mapsTo`) gives $`x^a = x^b` with $`a > b`. Cancelling the
nonzero $`x^b` in the domain $`K` yields $`x^{a-b} = 1` with $`a - b \ge 1`. This is mathlib's
`pow_eq_one_of_norm_le_one`.
:::

# Finiteness of the class group

## The Class Group Is Finite

:::theorem "class-group-finite" (lean := "NumberField.RingOfIntegers.instFintypeClassGroup")
The class group $`\mathrm{Cl}(K)` ({uses "class-group"}[]) of the ring of integers of any number
field $`K` is finite.
:::

:::proof "class-group-finite"
The proof bounds the number of ideal classes using Minkowski's geometry-of-numbers bound
({uses "minkowski-bound"}[]). mathlib's `ClassGroup.fintypeOfAdmissibleOfFinite`-style argument
(specialised to $`\mathbb{Z}`) shows that every ideal class contains an integral ideal of
absolute norm ({uses "absolute-norm"}[]) at most the Minkowski bound
$$`M_K = \left(\tfrac{4}{\pi}\right)^{r_2}\frac{n!}{n^n}\sqrt{|\mathrm{disc}(K)|};`
indeed, applying `exists_ne_zero_mem_ideal_of_norm_le` to a fractional ideal produces a nonzero
element of small norm, hence a representative of bounded norm. Since there are only finitely many
ideals of bounded norm ({uses "finite-ideals-bounded-norm"}[]), the class group is represented by
finitely many classes, so it is finite.
:::

## The Class Number

:::definition "class-number" (lean := "NumberField.classNumber")
The *class number* $`h_K` of a number field $`K` is the cardinality of its (finite) class group
({uses "class-group-finite"}[]):
$$`h_K = |\mathrm{Cl}(K)|.`
Thus $`h_K = 1` precisely when $`\mathcal{O}_K` is a principal ideal domain, and the size of
$`h_K` measures the failure of unique factorisation of elements in $`\mathcal{O}_K`.
:::

# The Dirichlet unit theorem

## Dirichlet's Unit Theorem

:::theorem "dirichlet-unit-theorem" (lean := "NumberField.Units.exist_unique_eq_mul_prod")
*(Dirichlet's unit theorem.)* Let $`K` be a number field with $`r_1` real embeddings and
$`r_2` pairs of complex embeddings, and set $`r = r_1 + r_2 - 1`. Every unit $`u \in
\mathcal{O}_K^\times` can be written uniquely as
$$`u = \zeta \cdot \varepsilon_1^{a_1} \cdots \varepsilon_r^{a_r},`
where $`\zeta` is a root of unity in $`\mathcal{O}_K`, the $`\varepsilon_i` form a fixed
fundamental system of units, and $`a_i \in \mathbb{Z}`. Equivalently $`\mathcal{O}_K^\times
\cong \mu(K) \times \mathbb{Z}^r`, with $`\mu(K)` the finite cyclic group of roots of unity.
:::

:::proof "dirichlet-unit-theorem"
The *logarithmic embedding* sends $`u` to the vector $`(\log\|u\|_v)_v` over the infinite
places, weighted by $`1` at real and $`2` at complex places. Its kernel is the set of units of
absolute value $`1` at every place, which by Kronecker's theorem ({uses "kronecker"}[]) is
exactly the (finite) group $`\mu(K)` of roots of unity. mathlib shows the image is a full-rank
lattice in the trace-zero hyperplane of $`\mathbb{R}^{r_1+r_2}` (dimension $`r`): discreteness
comes from the Minkowski bound ({uses "minkowski-bound"}[]) controlling units of bounded
height, and full rank is the harder geometric step constructing units with prescribed
archimedean sizes (`unitLattice_rank`). The structure of finitely generated abelian groups then
gives the unique decomposition `exist_unique_eq_mul_prod`.
:::

# Ramification and the fundamental identity

## Ramification Index

:::definition "ramification-index" (lean := "Ideal.ramificationIdx")
Let $`R \subseteq S` be an extension of Dedekind domains and $`\mathfrak{p} \subseteq R` a
nonzero prime. For a prime $`\mathfrak{P}` of $`S` over $`\mathfrak{p}`, the *ramification
index* $`e(\mathfrak{P}|\mathfrak{p})` is the exponent of $`\mathfrak{P}` in the factorisation
of $`\mathfrak{p}S`:
$$`\mathfrak{p}S = \mathfrak{P}_1^{e_1} \cdots \mathfrak{P}_g^{e_g}, \quad e_i = e(\mathfrak{P}_i|\mathfrak{p}).`
If $`e(\mathfrak{P}|\mathfrak{p}) > 1`, the prime $`\mathfrak{p}` *ramifies* in $`S`.
:::

## Inertia Degree

:::definition "inertia-degree" (lean := "Ideal.inertiaDeg")
With notation as in {uses "ramification-index"}[], the *inertia degree* (residue degree)
$`f(\mathfrak{P}|\mathfrak{p})` is the degree of the residue-field extension:
$$`f(\mathfrak{P}|\mathfrak{p}) = [\,S/\mathfrak{P} : R/\mathfrak{p}\,].`
:::

## The Fundamental Identity of Ramification

:::theorem "fundamental-identity" (lean := "Ideal.sum_ramification_inertia")
*(Fundamental identity of ramification.)* Let $`S/R` be a finite extension of Dedekind domains
with fraction fields $`L/K`, and let $`\mathfrak{p}` be a nonzero maximal prime of $`R`. Summing
$`ef` over the primes $`\mathfrak{P}` of $`S` above $`\mathfrak{p}` gives
$$`\sum_{\mathfrak{P} \mid \mathfrak{p}} e(\mathfrak{P}|\mathfrak{p})\, f(\mathfrak{P}|\mathfrak{p}) = [L : K].`
:::

:::proof "fundamental-identity"
By unique factorisation of ideals ({uses "ideal-unique-factorization"}[]), $`\mathfrak{p}S =
\prod_i \mathfrak{P}_i^{e_i}` with $`e_i = e(\mathfrak{P}_i|\mathfrak{p})`. The Chinese remainder
theorem for the coprime powers gives a ring isomorphism $`S/\mathfrak{p}S \cong \prod_i
S/\mathfrak{P}_i^{e_i}` (`Ideal.quotientEquivPiOfFinsetEq`). Each factor $`S/\mathfrak{P}_i^{e_i}`
has $`R/\mathfrak{p}`-dimension $`e_i f_i`, read off from its filtration by powers of
$`\mathfrak{P}_i` whose successive quotients are copies of the residue field $`S/\mathfrak{P}_i`
of degree $`f_i`. Summing, $`\dim_{R/\mathfrak{p}}(S/\mathfrak{p}S) = \sum_i e_i f_i`, and this
dimension equals $`[L:K]` because $`S` is finite free of rank $`[L:K]` over the localisation
$`R_{\mathfrak{p}}` (flatness of $`L \cong K \otimes_R S`). This is mathlib's
`sum_ramification_inertia`.
:::

# Adic valuations and the height-one spectrum

## The Height-One Spectrum

:::definition "height-one-spectrum" (lean := "IsDedekindDomain.HeightOneSpectrum")
For a Dedekind domain $`R` ({uses "dedekind-domain"}[]), the *height-one spectrum* is the set
of nonzero prime ideals of $`R` — equivalently, the maximal ideals, since $`R` has dimension
$`\le 1`. Each such $`\mathfrak{p}` is the data of a discrete place of $`\mathrm{Frac}(R)`. For
$`R = \mathcal{O}_K` these are exactly the finite places of the number field $`K`.
:::

## The Adic Valuation

:::definition "adic-valuation" (lean := "IsDedekindDomain.HeightOneSpectrum.valuation")
Each prime $`\mathfrak{p}` of the height-one spectrum ({uses "height-one-spectrum"}[]) carries a
*$`\mathfrak{p}`-adic valuation* $`v_{\mathfrak{p}} : K \to \mathbb{Z}^{m0}` (with values in
$`\mathbb{Z}` together with $`0`), defined on $`r \in R` as the exponent of $`\mathfrak{p}` in
the factorisation of $`(r)` ({uses "ideal-unique-factorization"}[]) and extended multiplicatively
to $`K = \mathrm{Frac}(R)`. It satisfies $`v_{\mathfrak{p}}(r) \ge 0` for $`r \in R`, with
$`v_{\mathfrak{p}}(r) > 0` (i.e. valuation $`< 1` multiplicatively) exactly when $`\mathfrak{p}
\mid (r)`, that is $`r \in \mathfrak{p}`. Its valuation ring is the localisation
$`R_{\mathfrak{p}}`, a discrete valuation ring, and completing at it yields the local field at
$`\mathfrak{p}`.
:::

:::proof "adic-valuation"
mathlib builds the integral valuation `intValuation` on $`R` as $`r \mapsto
\mathrm{ofAdd}(-\,\mathrm{ord}_{\mathfrak p}(r))`, where $`\mathrm{ord}_{\mathfrak p}(r)` is the
$`\mathfrak{p}`-adic multiplicity counted by the unique factorisation monoid of ideals
({uses "ideal-unique-factorization"}[]); multiplicativity of the valuation is multiplicativity
of this multiplicity, and the ultrametric inequality is `count` monotonicity under sums. The
extension to $`K` is the unique multiplicative extension to the fraction field, and the facts
$`v_{\mathfrak p}(r) \le 1` for $`r \in R` (`valuation_le_one`) and the membership criterion
$`v_{\mathfrak p}(r) < 1 \iff r \in \mathfrak{p}` (`valuation_lt_one_iff_mem`) are read off from
$`\mathrm{ord}_{\mathfrak p}(r) \ge 0` and $`\mathrm{ord}_{\mathfrak p}(r) \ge 1 \iff
\mathfrak{p}\mid(r)`.
:::

# Chevalley–Warning over finite fields

## The Chevalley–Warning Theorem

:::theorem "chevalley-warning" (lean := "char_dvd_card_solutions")
*(Chevalley–Warning.)* Let $`\mathbb{F}_q` be a finite field of characteristic $`p`, and let
$`f \in \mathbb{F}_q[X_1, \dots, X_s]` be a polynomial whose total degree is strictly less than
the number of variables, $`\deg f < s`. Then the number of solutions of $`f = 0` in
$`\mathbb{F}_q^{\,s}` is divisible by $`p`:
$$`p \mid \#\{\, x \in \mathbb{F}_q^{\,s} : f(x) = 0 \,\}.`
In particular, if $`f` is homogeneous (so $`0` is a solution) and $`\deg f < s`, then $`f` has a
nontrivial zero.
:::

:::proof "chevalley-warning"
mathlib counts solutions through the finite-field identity $`\sum_{x \in \mathbb{F}_q} x^{k} =
-1` if $`(q-1) \mid k` with $`k > 0`, and $`0` otherwise (`FiniteField.sum_pow_units`-type
sums). The indicator of $`\{f = 0\}` is $`1 - f^{\,q-1}` modulo $`p` (by Fermat's little theorem on the
finite field $`\mathbb{F}_q`, {uses "fermat-little"}[], every $`a \in \mathbb{F}_q` satisfies
$`a^{q} = a`, hence $`a^{q-1} \in \{0,1\}`), so the number of solutions is $`\sum_x (1 -
f(x)^{q-1})` in $`\mathbb{F}_q`. Expanding $`f^{q-1}` into monomials and summing each monomial
$`\prod_i x_i^{d_i}` over $`\mathbb{F}_q^{\,s}` gives a nonzero contribution only when every
exponent $`d_i` is a positive multiple of $`q-1`, forcing $`\sum_i d_i \ge s(q-1)`; but
$`\deg(f^{q-1}) = (q-1)\deg f < (q-1)s`, so no monomial qualifies and every term vanishes. Hence
the solution count is $`0` in $`\mathbb{F}_q`, i.e. divisible by $`p`. This is
`char_dvd_card_solutions`.
:::

# Cyclotomic extensions

## Cyclotomic Extensions

:::definition "cyclotomic-extension" (lean := "IsCyclotomicExtension")
Let $`S` be a set of positive integers and $`A \subseteq B` a ring extension. We say $`B` is an
*$`S`-cyclotomic extension* of $`A` (written $`\mathrm{IsCyclotomicExtension}(S, A, B)`) if for
every $`n \in S` there is a primitive $`n`-th root of unity in $`B`, and $`B` is generated over
$`A` by all $`n`-th roots of unity for $`n \in S`. For a single integer $`n` the *$`n`-th
cyclotomic field* over $`\mathbb{Q}` is $`\mathbb{Q}(\zeta_n)`, the splitting field of the
cyclotomic polynomial $`\Phi_n`.
:::

## Degree of a Cyclotomic Extension Is Euler's Totient

:::theorem "cyclotomic-finrank" (lean := "IsCyclotomicExtension.finrank")
When $`\Phi_n` is irreducible over the base field $`K` (in particular for $`K = \mathbb{Q}` by
Gauss), the cyclotomic extension $`L = K(\zeta_n)` ({uses "cyclotomic-extension"}[]) has degree
the value of Euler's totient:
$$`[L : K] = \varphi(n).`
:::

:::proof "cyclotomic-finrank"
A primitive $`n`-th root of unity $`\zeta_n` generates $`L` over $`K` and its minimal polynomial
is a monic factor of $`\Phi_n` ({uses "cyclotomic-extension"}[]). Under the irreducibility
hypothesis $`\mathrm{minpoly}_K(\zeta_n) = \Phi_n`, so $`[L:K] = \deg \Phi_n = \varphi(n)` by the
power-basis dimension formula `PowerBasis.finrank` applied to the power basis generated by
$`\zeta_n` (`IsPrimitiveRoot.powerBasis`); this is mathlib's `IsCyclotomicExtension.finrank`. The
degree of $`\Phi_n` is $`\varphi(n) = \#(\mathbb{Z}/n\mathbb{Z})^\times`, the number of primitive
$`n`-th roots of unity.
:::

## Galois Group of a Cyclotomic Field

:::theorem "cyclotomic-galois-zmod" (lean := "IsCyclotomicExtension.Rat.galEquivZMod")
For the $`n`-th cyclotomic field $`K = \mathbb{Q}(\zeta_n)` ({uses "cyclotomic-extension"}[]),
the *cyclotomic character* gives a canonical isomorphism between the Galois group and the units
of $`\mathbb{Z}/n\mathbb{Z}`,
$$`\mathrm{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q}) \;\xrightarrow{\ \sim\ }\; (\mathbb{Z}/n\mathbb{Z})^\times,`
sending an automorphism $`\sigma` to the residue $`a` with $`\sigma(\zeta_n) = \zeta_n^{\,a}`. In
particular the extension is abelian of degree $`\varphi(n)` ({uses "cyclotomic-finrank"}[]).
:::

:::proof "cyclotomic-galois-zmod"
Every $`\sigma \in \mathrm{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q})` permutes the primitive $`n`-th
roots, so $`\sigma(\zeta_n) = \zeta_n^{\,a(\sigma)}` for a unique $`a(\sigma) \in
(\mathbb{Z}/n\mathbb{Z})^\times`, and $`a(\sigma\tau) = a(\sigma)a(\tau)` makes $`\sigma \mapsto
a(\sigma)` a group homomorphism. mathlib realises it as `IsCyclotomicExtension.autEquivPow`,
which is injective because $`\zeta_n` generates $`K` and surjective by a cardinality comparison:
both groups have order $`\varphi(n)` ({uses "cyclotomic-finrank"}[], using irreducibility of
$`\Phi_n` over $`\mathbb{Q}`). The named abbreviation `galEquivZMod` packages this equivalence.
:::

## A Prime Is Totally Ramified in the Cyclotomic Field of a Prime Power

:::theorem "cyclotomic-prime-totally-ramified" (lean := "IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow, IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow")
Let $`p` be a prime and $`K = \mathbb{Q}(\zeta_{p^{k+1}})` ({uses "cyclotomic-extension"}[]).
Then $`p` is *totally ramified* in $`K`: there is a single prime $`\mathfrak{P}` above $`p`,
with inertia degree ({uses "inertia-degree"}[]) $`f = 1` and ramification index
({uses "ramification-index"}[])
$$`e = p^{\,k}(p-1) = \varphi(p^{\,k+1}) = [K:\mathbb{Q}],`
generated by $`\mathfrak{P} = (\zeta_{p^{k+1}} - 1)`.
:::

:::proof "cyclotomic-prime-totally-ramified"
The element $`\lambda = \zeta_{p^{k+1}} - 1` has $`N_{K/\mathbb{Q}}(\lambda) = \pm p` (it is
$`\Phi_{p^{k+1}}(1) = p` up to sign), so $`N((\lambda)) = p` is prime
({uses "absnorm-span-singleton"}[], {uses "absolute-norm"}[]); hence $`(\lambda)` is a prime of
$`\mathcal{O}_K` of inertia degree $`f = 1` lying over $`p`, and $`p\mathcal{O}_K = (\lambda)^{e}`
with $`e = \mathrm{ord}_{(\lambda)}(p)`. mathlib computes $`e = p^{k}(p-1)` directly
(`ramificationIdx_span_zeta_sub_one`, via the multiplicity of $`p` in
$`(\lambda)^{\,p^k(p-1)}`), and shows $`(\lambda)` is the *only* prime above $`p` by collapsing
the Galois fundamental identity ({uses "fundamental-identity"}[]) $`r\cdot e\cdot f =
\varphi(p^{k+1})` ({uses "cyclotomic-finrank"}[]) with $`e = \varphi(p^{k+1})`, $`f = 1`, forcing
$`r = 1` (`ncard_primesOver_of_prime_pow`).
:::

## Splitting of Primes in Cyclotomic Fields

:::theorem "cyclotomic-prime-splitting" (lean := "IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd, IsCyclotomicExtension.Rat.ramificationIdxIn_eq")
Let $`K = \mathbb{Q}(\zeta_n)` ({uses "cyclotomic-extension"}[]) and write $`n = p^{k+1}m` with
$`p \nmid m`. Then a prime $`\mathfrak{P}` of $`\mathcal{O}_K` over $`p` has inertia degree
({uses "inertia-degree"}[]) and ramification index ({uses "ramification-index"}[])
$$`f = \mathrm{ord}_{(\mathbb{Z}/m\mathbb{Z})^\times}(p), \qquad e = p^{\,k}(p-1) = \varphi(p^{\,k+1}).`
In particular $`p` is unramified in $`K` exactly when $`p \nmid n`, in which case its inertia
degree is the multiplicative order of $`p` modulo $`n`, and $`p` splits completely iff $`p
\equiv 1 \pmod n`.
:::

:::proof "cyclotomic-prime-splitting"
The cyclotomic tower factors $`\mathbb{Q}(\zeta_n) = \mathbb{Q}(\zeta_{p^{k+1}})\cdot
\mathbb{Q}(\zeta_m)`, with $`p` totally ramified in the first factor
({uses "cyclotomic-prime-totally-ramified"}[]) and unramified in the second. mathlib computes
the inertia degree of $`\mathfrak{P}` over $`p` through Kummer–Dedekind: away from $`p`, the
factorisation of $`p\mathcal{O}_K` matches the factorisation of $`\Phi_n \bmod p` into
irreducibles (`inertiaDeg_primesOverSpanEquivMonicFactorsMod`), and each irreducible factor of
$`\Phi_m \bmod p` has degree $`\mathrm{ord}_{(\mathbb{Z}/m\mathbb{Z})^\times}(p)`
(`natDegree_of_dvd_cyclotomic`), giving $`f = \mathrm{ord}(p \bmod m)`
(`inertiaDeg_eq_of_not_dvd`). The ramification index is inherited from the totally ramified
$`p`-part, $`e = \varphi(p^{k+1})` (`ramificationIdxIn_eq`). Combining $`e`, $`f` with the
fundamental identity ({uses "fundamental-identity"}[]) determines the number of primes
$`r = \varphi(n)/(ef)`; $`p` splits completely ($`r = \varphi(n)`, $`e = f = 1`) iff $`p \equiv
1 \pmod n` via the Galois isomorphism ({uses "cyclotomic-galois-zmod"}[]).
:::

# Results from external Lean projects

The nodes below are *informal*: the external projects are built against Mathlib versions that
differ from AINTLIB's, so they carry no `(lean := …)` reference. Each records where the result
is formalised, an exact-source permalink to the recorded commit, and whether that formalisation
is sorry-free or still in progress. Both repositories are public.

## Ring of integers of a quadratic field

:::theorem "quadratic-ring-of-integers"
Let $`d \in \mathbb{Z}` be a squarefree integer with $`|d| \ge 2`, and let $`K =
\mathbb{Q}(\sqrt{d})` be the associated quadratic number field ({uses "number-field"}[]). The
ring of integers ({uses "ring-of-integers"}[]) $`\mathcal{O}_K` is:
$$`\mathcal{O}_K \;=\; \begin{cases} \mathbb{Z}[\sqrt{d}] & \text{if } d \equiv 2 \text{ or } 3 \pmod{4},\\[4pt] \mathbb{Z}\!\left[\tfrac{1+\sqrt{d}}{2}\right] & \text{if } d \equiv 1 \pmod{4}. \end{cases}`
In both cases $`\mathcal{O}_K` is a free $`\mathbb{Z}`-module of rank $`2`
({uses "ring-of-integers-free"}[]).
Formalised in [`QuadraticIntegers`](https://github.com/pitmonticone/QuadraticIntegers): the two
cases are [`QuadraticInteger.d_2_or_3`](https://github.com/pitmonticone/QuadraticIntegers/blob/205ad5a8b24860b1332a603e5028aa9bf8ebb495/QuadraticIntegers/RingOfIntegers.lean#L94)
and [`QuadraticInteger.d_1`](https://github.com/pitmonticone/QuadraticIntegers/blob/205ad5a8b24860b1332a603e5028aa9bf8ebb495/QuadraticIntegers/RingOfIntegers.lean#L130)
— in progress (both theorems, and the supporting trace/norm integrality lemmas they rely on, are
currently `sorry`).
:::

:::proof "quadratic-ring-of-integers"
The project models $`K` and $`R = \mathcal{O}_K`-candidate as the quadratic
$`\mathbb{Q}`- and $`\mathbb{Z}`-algebras $`\mathrm{QuadraticAlgebra}\,\mathbb{Q}\,d\,0` and
$`\mathrm{QuadraticAlgebra}\,\mathbb{Z}\,d\,0`, and reduces "$`R` is the integral closure" to the
`IsIntegralClosure R ℤ K` predicate. The criterion is the trace–norm test: an element
$`z = a + b\sqrt{d}` ($`a, b \in \mathbb{Q}`) is integral over $`\mathbb{Z}` iff its minimal
polynomial $`X^2 - (2a)X + (a^2 - db^2)` has integer coefficients
([`QuadraticInteger.minpoly`](https://github.com/pitmonticone/QuadraticIntegers/blob/205ad5a8b24860b1332a603e5028aa9bf8ebb495/QuadraticIntegers/RingOfIntegers.lean#L38)),
i.e. trace $`2a \in \mathbb{Z}` and norm $`a^2 - db^2 \in \mathbb{Z}`. From $`4(a^2 - db^2) =
(2a)^2 - d(2b)^2` and squarefreeness of $`d`, one deduces $`2a, 2b \in \mathbb{Z}`.

When $`d \equiv 2, 3 \pmod 4`, an odd value of $`2a` would require $`(2a)^2 \equiv d(2b)^2 \pmod
4`, impossible for $`d \equiv 2, 3`; so $`a, b \in \mathbb{Z}` and $`\mathcal{O}_K =
\mathbb{Z}[\sqrt d]`. When $`d \equiv 1 \pmod 4`, the half-integer case is admissible: the
project switches to the auxiliary algebra $`S = \mathrm{QuadraticAlgebra}\,\mathbb{Z}\,e\,1` with
$`e = (d-1)/4`, whose generator $`\tfrac{1+\sqrt d}{2}` satisfies $`x^2 - x - e = 0`, and a
descent argument (`d_1_int`) shows every integral element lies in $`\mathbb{Z}[\tfrac{1+\sqrt
d}{2}]`.
:::

## Order of the general linear group over a finite field

:::theorem "order-gln-fq"
Let $`\mathbb{F}_q` be the finite field with $`q` elements and $`n \ge 1`. The order of the
general linear group is
$$`|\mathrm{GL}_n(\mathbb{F}_q)| \;=\; \prod_{i=0}^{n-1}(q^n - q^i).`
Formalised in [`GLn_F_q`](https://github.com/CBirkbeck/GLn_F_q): [`card_GL`](https://github.com/CBirkbeck/GLn_F_q/blob/3fc5ad9ff7643fa20c3484e7774d4e4d7fabde22/GLnFQ/card_GLn_Fq.lean#L88)
— sorry-free.
:::

:::proof "order-gln-fq"
An $`n \times n` matrix over $`\mathbb{F}_q` is invertible iff its columns form a linearly
independent family — an ordered basis of $`\mathbb{F}_q^{\,n}`. The project builds an explicit
equivalence
[`equiv_GL_linearindependent`](https://github.com/CBirkbeck/GLn_F_q/blob/3fc5ad9ff7643fa20c3484e7774d4e4d7fabde22/GLnFQ/card_GLn_Fq.lean#L62)
between $`\mathrm{GL}_n(\mathbb{F}_q)` and the type of linearly independent $`n`-tuples of
vectors in $`\mathbb{F}_q^{\,n}`, sending a unit matrix to (the transpose of) its columns and
back via `basisOfLinearIndependentOfCardEqFinrank`. The count of linearly independent tuples is
then computed by induction on the length
([`card_LinearInependent_subtype`](https://github.com/CBirkbeck/GLn_F_q/blob/3fc5ad9ff7643fa20c3484e7774d4e4d7fabde22/GLnFQ/card_GLn_Fq.lean#L47)):
given $`k` independent vectors, the $`(k+1)`-th may be any vector outside their $`k`-dimensional
span, and the complement of a $`k`-dimensional subspace of $`\mathbb{F}_q^{\,n}` has exactly
$`q^n - q^k` elements (the count throughout rests on the cardinality $`q` of the finite field
$`\mathbb{F}_q`; the base case $`n = 1` already records $`|\mathrm{GL}_1(\mathbb{F}_q)| = q - 1 =
|\mathbb{F}_q^\times|`, the order of the unit group underlying Fermat's little theorem,
{uses "fermat-little-units"}[])
([`complement_card`](https://github.com/CBirkbeck/GLn_F_q/blob/3fc5ad9ff7643fa20c3484e7774d4e4d7fabde22/GLnFQ/card_GLn_Fq.lean#L24),
using $`\#V = q^{\dim V}` for a finite $`\mathbb{F}_q`-space). The inductive step
([`inductiveStepEquiv`](https://github.com/CBirkbeck/GLn_F_q/blob/3fc5ad9ff7643fa20c3484e7774d4e4d7fabde22/GLnFQ/card_GLn_Fq.lean#L32))
splits an independent $`(k+1)`-tuple into its first $`k` entries and a vector in the complement,
multiplying the counts to give the product $`\prod_{i=0}^{n-1}(q^n - q^i)`.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib pull
requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing at the
live PR and **no** `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the Mathlib-backed nodes of this
chapter via `{uses}` edges. Statements should be re-pointed to `(lean := …)` once the
corresponding PR merges.

## Quadratic Number Fields

:::theorem "quadratic-number-field" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/36347")
A *quadratic number field* is a number field ({uses "number-field"}[]) of degree $`2` over
$`\mathbb{Q}`. Every such field is isomorphic to $`\mathbb{Q}(\sqrt{d})` for a unique squarefree
integer $`d \ne 0, 1`, presented uniformly as the quadratic $`\mathbb{Q}`-algebra
$$`\mathbb{Q}[\sqrt{d}] \;=\; \mathrm{QuadraticAlgebra}\,\mathbb{Q}\,d\,0 \;=\; \mathbb{Q}[x]/(x^2 - d).`
The discriminant ({uses "discriminant"}[]) of $`K = \mathbb{Q}(\sqrt{d})` is $`d` when $`d
\equiv 1 \pmod 4` and $`4d` otherwise.

The PR sets up quadratic number fields as `QuadraticAlgebra ℚ d 0`, giving a uniform model in
which the ring of integers ({uses "quadratic-ring-of-integers"}[]), units, and class number of a
real or imaginary quadratic field can be developed. Parameter uniqueness (the squarefree $`d` is
determined by $`K`) is the companion PR #36387.
In review — [mathlib PR #36347](https://github.com/leanprover-community/mathlib4/pull/36347).
:::

## Unramifiedness Is Preserved under Compositum

:::theorem "hilbert-unramified-compositum" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/36843")
*(Hilbert theory — unramified compositum.)* Let $`A` be a Dedekind domain
({uses "dedekind-domain"}[]) with fraction field $`K`, let $`\mathfrak{p}` be a nonzero prime of
$`A`, and let $`L_1, L_2` be two finite separable extensions of $`K` in which $`\mathfrak{p}` is
unramified — every prime above $`\mathfrak{p}` has ramification index $`1`
({uses "ramification-index"}[]). Then $`\mathfrak{p}` is unramified in the compositum $`L_1 L_2`
as well.

This is part of the Hilbert-theory development of decomposition and inertia. The proof reduces,
via the fundamental identity ({uses "fundamental-identity"}[]) and the multiplicativity of
ramification in towers, to the statement that the inertia subgroups attached to $`L_1` and
$`L_2` generate, so their compositum carries no ramification.
In review — [mathlib PR #36843](https://github.com/leanprover-community/mathlib4/pull/36843).
:::

## Inertia Field of a Cyclotomic Extension

:::theorem "cyclotomic-inertia-field" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/37031")
*(Inertia field of a cyclotomic field.)* Let $`n = p^k m` with $`p \nmid m`, and let $`K =
\mathbb{Q}(\zeta_n)` be the $`n`-th cyclotomic field ({uses "cyclotomic-extension"}[]). The
inertia field of the prime $`p` in $`K` — the largest subextension in which $`p` is unramified —
is $`\mathbb{Q}(\zeta_m)`, the ramification index of $`p` in $`K` is $`e = \varphi(p^k)`
({uses "cyclotomic-prime-splitting"}[]), and its inertia degree
({uses "inertia-degree"}[]) is the multiplicative order of $`p` modulo $`m`. Equivalently, $`p`
is totally ramified in $`\mathbb{Q}(\zeta_{p^k})/\mathbb{Q}` and unramified in
$`\mathbb{Q}(\zeta_m)/\mathbb{Q}`, and the two extensions are linearly disjoint over
$`\mathbb{Q}`.

The PR computes the inertia field explicitly inside the cyclotomic tower, refining the splitting
of a rational prime $`p` in $`\mathbb{Q}(\zeta_n)` recorded by `galEquivZMod`
({uses "cyclotomic-galois-zmod"}[]) into the language of the decomposition and inertia fields.
In review — [mathlib PR #37031](https://github.com/leanprover-community/mathlib4/pull/37031).
:::

## Ring-of-Integers Typeclass Instances

:::theorem "ring-of-integers-instances" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/9444")
*(Ring-of-integers instances.)* For a number field $`K` ({uses "number-field"}[]) the ring of
integers $`\mathcal{O}_K` ({uses "ring-of-integers"}[]) is a Dedekind domain
({uses "ring-of-integers-is-dedekind"}[]) that is free of rank $`[K:\mathbb{Q}]` over
$`\mathbb{Z}` ({uses "ring-of-integers-free"}[]); this PR supplies the missing typeclass
instances (`IsDedekindDomain (𝓞 K)`, `Module.Free ℤ (𝓞 K)`, finiteness) so that downstream API
— the absolute norm ({uses "absolute-norm"}[]) and the class group
({uses "class-group"}[]) — applies to $`\mathcal{O}_K` without re-deriving them.

The PR is infrastructural: it threads the already-proved facts about integral closures of
Dedekind domains into instances directly on $`\mathcal{O}_K`, removing the boilerplate currently
needed at each use site.
In review — [mathlib PR #9444](https://github.com/leanprover-community/mathlib4/pull/9444).
:::
