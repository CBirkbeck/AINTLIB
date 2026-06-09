import Verso
import VersoManual
import VersoBlueprint

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Galois

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Class Field Theory and Galois Theory" =>

This chapter covers the Galois theory of field extensions, the decomposition and inertia structure
of primes in Galois extensions of Dedekind domains, and Frobenius elements, as formalised in
mathlib. It then records the deeper results of class field theory — the Chebotarev density theorem,
local fields and the local reciprocity machinery, group and Tate cohomology with the Herbrand
quotient, and power residue symbols — that live in external Lean projects rather than in mathlib.
Every mathlib node carries a `(lean := …)` reference and its proof sketch follows the argument of
the cited declaration, naming the lemmas that proof actually invokes. Every external node carries a
`Formalised in` provenance line linking to the exact source declaration and reporting its true Lean
status.

Throughout, $`K` and $`L` denote fields with $`L/K` a finite extension, $`G = \mathrm{Gal}(L/K)`
the group of $`K`-automorphisms of $`L`, $`A \subseteq B` Dedekind domains with $`B` a finite
$`A`-module (and $`L/K` the extension of their fraction fields), $`\mathfrak{p}` a nonzero prime of
$`A`, and $`\mathfrak{P}` a prime of $`B` lying over $`\mathfrak{p}`. We write
$`e(\mathfrak{P}/\mathfrak{p})` for the ramification index, $`f(\mathfrak{P}/\mathfrak{p})` for the
inertia degree, and $`N\mathfrak{p}` for the absolute norm of $`\mathfrak{p}`.

# Galois extensions and the fundamental theorem

## Galois Extensions

:::definition "is-galois" (lean := "IsGalois")
A finite-dimensional field extension $`L/K` is *Galois* if it is both separable and normal: every
element of $`L` is separable over $`K`, and the minimal polynomial over $`K` of every element of
$`L` splits completely in $`L`. (In mathlib a separable extension is by definition algebraic, so
these two conditions are exactly the data of the `IsGalois` class.) We write
$`\mathrm{Gal}(L/K)` for the group of field automorphisms of $`L` fixing $`K` pointwise.
:::

## Order of the Galois Group Equals the Degree

:::theorem "galois-card-aut" (lean := "IsGalois.card_aut_eq_finrank")
Let $`L/K` be a finite Galois extension. Then the order of the Galois group equals the degree:
$$`|\mathrm{Gal}(L/K)| = [L : K].`
:::

:::proof "galois-card-aut"
mathlib reduces to a simple extension. By the primitive element theorem $`L = K(\alpha)` for some
$`\alpha`, and there is a $`K`-algebra isomorphism $`K(\alpha) \cong L` transporting both the degree
and the automorphism count. For the simple extension, the number of $`K`-algebra homomorphisms
$`K(\alpha) \to L` equals the number of roots of $`\mathrm{minpoly}_K(\alpha)` lying in $`L`; because
$`L/K` is Galois ({uses "is-galois"}[]), separability makes this minimal polynomial have distinct
roots and normality forces them all into $`L`, so this count is exactly $`\deg \mathrm{minpoly}_K(\alpha)
= [K(\alpha) : K]`. Finally each $`K`-algebra homomorphism $`L \to L` is an automorphism (the source
and target have equal finite dimension), so $`|\mathrm{Gal}(L/K)|` equals that count of homomorphisms,
which is $`[L:K]`.
:::

## The Fundamental Theorem of Galois Theory

:::theorem "galois-correspondence" (lean := "IsGalois.intermediateFieldEquivSubgroup")
*(Fundamental theorem of Galois theory.)* Let $`L/K` be a finite Galois extension with
$`G = \mathrm{Gal}(L/K)`. The maps
$$`M \longmapsto \mathrm{Gal}(L/M), \qquad H \longmapsto L^{H}`
are mutually inverse, order-reversing bijections between the intermediate fields $`K \subseteq M
\subseteq L` and the subgroups $`H \le G`, where $`\mathrm{Gal}(L/M)` is the subgroup fixing $`M`
pointwise and $`L^{H}` is the field fixed by $`H`. Under this correspondence $`[L : M] = |\mathrm{Gal}(L/M)|`
and $`[M : K] = [G : \mathrm{Gal}(L/M)]`.
:::

:::proof "galois-correspondence"
mathlib packages the correspondence as an order isomorphism between intermediate fields and the
*order dual* of the lattice of subgroups, with the fixing-subgroup map one way and the fixed-field
map the other. Two round-trip identities make it a bijection. That $`L^{\mathrm{Gal}(L/M)} = M`
(the deep direction) is `fixedField_fixingSubgroup`: the fixed field of the fixing subgroup has
degree over $`K` equal to $`[G : \mathrm{Gal}(L/M)]` by counting automorphisms via
{uses "galois-card-aut"}[], which already equals $`[M:K]`, forcing equality. The other round trip
$`\mathrm{Gal}(L/L^{H}) = H` (`fixingSubgroup_fixedField`) holds because $`L/L^{H}` is Galois with
group $`H`. Order-reversal is immediate: a larger intermediate field is fixed by a smaller subgroup.
The degree formulas follow from {uses "galois-card-aut"}[] applied to $`L/M`.
:::

## Order of the Fixing Subgroup

:::theorem "fixing-subgroup-card" (lean := "IsGalois.card_fixingSubgroup_eq_finrank")
Let $`L/K` be a finite Galois extension and $`K \subseteq M \subseteq L` an intermediate field.
Then the subgroup of $`G = \mathrm{Gal}(L/K)` fixing $`M` pointwise has order $`[L : M]`:
$$`|\mathrm{Gal}(L/M)| = [L : M].`
:::

:::proof "fixing-subgroup-card"
This is the special case of {uses "galois-card-aut"}[] for the Galois extension $`L/M`, recast for
the fixing subgroup. mathlib rewrites the fixed field of the fixing subgroup back to $`M` via the
Galois correspondence ({uses "galois-correspondence"}[]) and then identifies the order of the fixing
subgroup with the degree $`[L:M]` through the equality $`|\mathrm{Gal}(L/M)| = [L:M]` of the
sub-extension. It is the precise quantitative content powering the degree formulas in the
correspondence.
:::

# Decomposition and inertia in Galois extensions

Throughout this section $`B/A` is a finite extension of Dedekind domains with $`B` torsion-free over
$`A`, $`G` a finite group acting on $`B` by ring automorphisms with fixed subring $`A` (a *Galois
group* for $`B/A` in mathlib's sense), and the residue extensions are taken separable.

## The Inertia Group

:::definition "inertia-group" (lean := "Ideal.inertia")
Let $`G` be a group acting on a ring $`S` and let $`I` be an ideal of $`S`. The *inertia group* of
$`I` is the subgroup of $`G` acting trivially on $`S/I`:
$$`\mathrm{inertia}(G, I) = \{\, \sigma \in G \mid \sigma(x) - x \in I \text{ for all } x \in S \,\}.`
For $`I = \mathfrak{P}` a prime of $`B` over $`\mathfrak{p}`, this is the kernel of the natural map
from the decomposition group (the stabiliser of $`\mathfrak{P}`) to the automorphism group of the
residue field extension $`k(\mathfrak{P})/k(\mathfrak{p})`.
:::

## Transitivity of the Galois Action on Primes

:::lemma_ "galois-transitive" (lean := "Ideal.exists_smul_eq_of_isGaloisGroup")
Let $`G` be a finite Galois group for $`B/A` and let $`\mathfrak{P}, \mathfrak{Q}` be primes of
$`B` lying over the same prime $`\mathfrak{p}` of $`A`. Then some $`\sigma \in G` carries
$`\mathfrak{P}` to $`\mathfrak{Q}`; equivalently, $`G` acts transitively on the set of primes of
$`B` over $`\mathfrak{p}`.
:::

:::proof "galois-transitive"
This is the ring-theoretic transitivity packaged in mathlib's invariant-theory layer: two primes
of $`B` with the same contraction to $`A` are related by an element of any Galois group, the
statement `IsInvariant.exists_smul_of_under_eq`. The hypothesis $`\mathfrak{P} \cap A = \mathfrak{p}
= \mathfrak{Q} \cap A` is exactly the "same prime below" condition, and the conclusion produces the
required $`\sigma`. Transitivity of the induced action on the finite set of primes over
$`\mathfrak{p}` is the immediate consequence used throughout the rest of the section.
:::

## Common Ramification Index and Inertia Degree

:::lemma_ "ramification-inertia-common" (lean := "Ideal.ramificationIdx_eq_of_isGaloisGroup, Ideal.inertiaDeg_eq_of_isGaloisGroup")
Let $`G` be a finite Galois group for $`B/A` and let $`\mathfrak{P}, \mathfrak{Q}` be primes of
$`B` over the same prime $`\mathfrak{p}`. Then they share a common ramification index
({uses "ramification-index"}[]) and a common inertia degree ({uses "inertia-degree"}[]):
$$`e(\mathfrak{P}/\mathfrak{p}) = e(\mathfrak{Q}/\mathfrak{p}), \qquad
   f(\mathfrak{P}/\mathfrak{p}) = f(\mathfrak{Q}/\mathfrak{p}).`
These common values are denoted $`e` and $`f` (mathlib's `ramificationIdxIn` and `inertiaDegIn`).
:::

:::proof "ramification-inertia-common"
By transitivity ({uses "galois-transitive"}[]) write $`\mathfrak{Q} = \sigma \cdot \mathfrak{P}` for
some $`\sigma \in G`. The automorphism $`\sigma` is an isomorphism of $`A`-algebras carrying
$`\mathfrak{P}` onto $`\mathfrak{Q}`, so it preserves the ramification index and the inertia degree:
these are the invariance lemmas `ramificationIdx_map_eq` and `inertiaDeg_map_eq` applied to the
algebra automorphism attached to $`\sigma`. Hence both invariants are constant on the orbit of
primes over $`\mathfrak{p}`, justifying the definitions of the common values $`e` and $`f`.
:::

## The Fundamental Identity in the Galois Case

:::theorem "galois-efr-identity" (lean := "Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn")
*(Fundamental identity, Galois form.)* Let $`G` be a finite Galois group for $`B/A` and let
$`\mathfrak{p}` be a nonzero maximal prime of $`A`. Writing $`r` for the number of primes of $`B`
over $`\mathfrak{p}`, and $`e`, $`f` for their common ramification index
({uses "ramification-index"}[]) and inertia degree ({uses "inertia-degree"}[]),
$$`r \cdot e \cdot f \;=\; |G|.`
:::

:::proof "galois-efr-identity"
In the Galois case all primes over $`\mathfrak{p}` share the same $`e` and $`f`
({uses "ramification-inertia-common"}[]), so the general fundamental identity
$`\sum_{\mathfrak{P}} e_{\mathfrak{P}} f_{\mathfrak{P}} = [L:K]` ({uses "fundamental-identity"}[])
collapses, having $`r` equal summands, to $`r \cdot e \cdot f = [L:K]`. The Galois hypothesis also
gives $`|G| = [L:K]` (the order of a Galois group equals the degree, {uses "galois-card-aut"}[],
transported through `IsGaloisGroup.card_eq_finrank` to the fraction-field extension), so
$`r \cdot e \cdot f = |G|`.
:::

## Order of the Inertia Group

:::lemma_ "inertia-card" (lean := "Ideal.card_inertia_eq_ramificationIdxIn")
With $`G`, $`\mathfrak{p}`, $`\mathfrak{P}` as above (and $`B/A` Dedekind, the residue extension
separable), the order of the inertia group ({uses "inertia-group"}[]) equals the ramification index
({uses "ramification-index"}[]):
$$`|\mathrm{inertia}(G, \mathfrak{P})| = e(\mathfrak{P}/\mathfrak{p}).`
:::

:::proof "inertia-card"
mathlib combines orbit–stabiliser with the two fundamental counts. Writing $`D(\mathfrak{P})` for
the decomposition group (the stabiliser of $`\mathfrak{P}`), the residue extension
$`k(\mathfrak{P})/k(\mathfrak{p})` is Galois and $`D(\mathfrak{P})` surjects onto its automorphism
group with kernel the inertia group, so $`|D(\mathfrak{P})| = |\mathrm{inertia}(G,\mathfrak{P})|
\cdot f` with $`f = [k(\mathfrak{P}):k(\mathfrak{p})]` counted by {uses "galois-card-aut"}[]
(`card_stabilizer_eq_card_inertia_mul_finrank`). The orbit of $`\mathfrak{P}` under $`G` is the full
set of $`r` primes over $`\mathfrak{p}` ({uses "galois-transitive"}[]), so orbit–stabiliser gives
$`r \cdot |D(\mathfrak{P})| = |G|`, i.e. $`r \cdot |\mathrm{inertia}(G,\mathfrak{P})| \cdot f = |G|`.
Comparing with the Galois fundamental identity $`r \cdot e \cdot f = |G|`
({uses "galois-efr-identity"}[]) and cancelling the nonzero factors $`r` and $`f` leaves
$`|\mathrm{inertia}(G,\mathfrak{P})| = e`. (The cancellation is where the Dedekind and separability
hypotheses enter, ensuring $`r, f \neq 0`.)
:::

## Order of the Decomposition Group

:::theorem "decomposition-card" (lean := "Ideal.card_stabilizer_eq")
Let $`G` be a finite Galois group for $`B/A`, $`\mathfrak{p}` a nonzero prime of $`A`, and
$`\mathfrak{P}` a prime of $`B` over $`\mathfrak{p}`. The decomposition group (the stabiliser of
$`\mathfrak{P}` in $`G`) has order the product of the ramification index ({uses "ramification-index"}[])
and the inertia degree ({uses "inertia-degree"}[]):
$$`|D(\mathfrak{P})| = e \cdot f.`
:::

:::proof "decomposition-card"
The decomposition group factors as $`|D(\mathfrak{P})| = |\mathrm{inertia}(G,\mathfrak{P})| \cdot
[k(\mathfrak{P}) : k(\mathfrak{p})]` — inertia times the order of the residue Galois group, counted
via {uses "galois-card-aut"}[]. The inertia factor is the ramification index ({uses "inertia-card"}[])
and the residue degree $`[k(\mathfrak{P}):k(\mathfrak{p})]` is the inertia degree $`f`, so
$`|D(\mathfrak{P})| = e \cdot f`. This is mathlib's `card_stabilizer_eq`, obtained by rewriting the
inertia–residue factorisation with the inertia-cardinality lemma.
:::

# Frobenius elements

## The Frobenius Endomorphism

:::definition "frobenius-endomorphism" (lean := "frobenius")
Let $`R` be a commutative semiring with exponential characteristic $`p` (so $`p` is either $`1` or
a prime, recorded by the `ExpChar R p` class). The *Frobenius endomorphism* is the ring
homomorphism
$$`\varphi \colon R \to R, \qquad x \mapsto x^{p}.`
It is additive because in exponential characteristic $`p` the binomial theorem degenerates to the
freshman's-dream identity $`(x + y)^{p} = x^{p} + y^{p}` (mathlib's `add_pow_expChar`); multiplicativity
is the monoid-homomorphism property of $`x \mapsto x^{p}`.
:::

## Arithmetic Frobenius Elements

:::definition "arith-frob-at" (lean := "IsArithFrobAt")
Let a monoid $`M` act on a ring $`S` by ring automorphisms, with the action trivial on a subring
$`R`, and let $`Q` be an ideal of $`S` whose contraction $`P = Q \cap R` has finite residue field of
cardinality $`q = |R/P|`. An element $`\sigma \in M` is an *arithmetic Frobenius at $`Q`* if it
induces the $`q`-power map on the residue ring, i.e.
$$`\sigma(x) - x^{q} \in Q \qquad \text{for all } x \in S.`
Equivalently $`\sigma` reduces to the Frobenius endomorphism ({uses "frobenius-endomorphism"}[]) of
$`S/Q` relative to $`R/P`.
:::

## Existence of Arithmetic Frobenius Elements

:::lemma_ "arith-frob-exists" (lean := "IsArithFrobAt.exists_of_isInvariant")
Let $`G` be a finite group acting on a ring $`S` with fixed subring $`R`, and let $`Q` be a prime
of $`S` with finite residue field. Then an arithmetic Frobenius element $`\sigma \in G` at $`Q`
exists.
:::

:::proof "arith-frob-exists"
Set $`P = Q \cap R`. mathlib first records that the residue field $`R/P` is finite, of characteristic
$`p` and cardinality $`q = p^{k}` for some $`k` (`FiniteField.card`). The residue extension
$`(S/Q)/(R/P)` is then a finite extension of finite fields, and its Frobenius — the $`q`-power map
$`x \mapsto x^{q}` ({uses "frobenius-endomorphism"}[]), here built as the $`k`-fold iterate of the
$`p`-power Frobenius — is an $`R/P`-algebra automorphism of $`S/Q` (it fixes $`R/P` pointwise by
$`a^{q} = a` on the field of $`q` elements, `FiniteField.pow_card`). The decomposition group
$`D(Q)` of $`Q` surjects onto the automorphisms of the residue extension
(`Ideal.Quotient.stabilizerHom_surjective`), so some $`\sigma \in G` realises this $`q`-power
automorphism on $`S/Q`; unwinding the surjectivity gives the congruence $`\sigma(x) \equiv x^{q}
\pmod Q`, exhibiting $`\sigma` as a Frobenius at $`Q` ({uses "arith-frob-at"}[]).
:::

## Frobenius Elements Differ by an Inertia Element

:::lemma_ "arith-frob-inertia" (lean := "IsArithFrobAt.mul_inv_mem_inertia")
Any two arithmetic Frobenius elements at the same prime $`Q` differ by an element of the inertia
group of $`Q`: if $`\sigma` and $`\sigma'` are both Frobenius at $`Q`, then $`\sigma\sigma'^{-1} \in
\mathrm{inertia}(G, Q)` ({uses "inertia-group"}[]). In particular, when $`Q` is unramified the
Frobenius at $`Q` is unique.
:::

:::proof "arith-frob-inertia"
For every $`x \in S`, both $`\sigma(\sigma'^{-1} x) - (\sigma'^{-1}x)^{q}` and $`\sigma'(\sigma'^{-1}x)
- (\sigma'^{-1}x)^{q}` lie in $`Q` by the Frobenius property ({uses "arith-frob-at"}[]). Subtracting,
$`\sigma(\sigma'^{-1}x) - \sigma'(\sigma'^{-1}x) = (\sigma\sigma'^{-1})(x) - x` lies in $`Q`, which is
exactly the condition $`\sigma\sigma'^{-1} \in \mathrm{inertia}(G, Q)`. When $`Q` is unramified the
inertia group is trivial ({uses "inertia-card"}[] gives $`|\mathrm{inertia}| = e = 1`), so the two
Frobenius elements coincide.
:::

## Frobenius Action on Roots of Unity

:::lemma_ "arith-frob-roots-of-unity" (lean := "AlgHom.IsArithFrobAt.apply_of_pow_eq_one")
Suppose $`S` is a domain and $`\varphi \colon S \to S` is an arithmetic Frobenius at a prime $`Q`
({uses "arith-frob-at"}[]). If $`\zeta \in S` is a root of unity of order $`m` coprime to the
residue characteristic (precisely, $`m \notin Q`), then $`\varphi` raises $`\zeta` to the residue
power exactly:
$$`\varphi(\zeta) = \zeta^{q}, \qquad q = |R/(Q \cap R)|.`
:::

:::proof "arith-frob-roots-of-unity"
The Frobenius congruence only gives $`\varphi(\zeta) \equiv \zeta^{q} \pmod Q`; the point is that on
roots of unity of order prime to the residue characteristic this lifts to an exact equality in $`S`.
Since $`\zeta` is a primitive $`m`-th root, $`\varphi(\zeta)` is again an $`m`-th root, so
$`\varphi(\zeta) = \zeta^{i}` for some $`i`. The congruence forces $`\zeta^{i} \equiv \zeta^{q}
\pmod Q`, and because $`m` is invertible modulo $`Q` the $`m`-th roots of unity stay distinct in
$`S/Q`, so $`i \equiv q` and hence $`\varphi(\zeta) = \zeta^{q}` already in $`S`. This is the
algebraic mechanism that ties Frobenius elements to power residue symbols below.
:::

## Conjugacy of Frobenius Elements Over the Same Prime

:::lemma_ "arith-frob-conjugate" (lean := "isConj_arithFrobAt")
Let $`G` be a finite group acting on $`S` with fixed subring $`R`, and let $`Q, Q'` be primes of
$`S` with finite residue fields lying over the same prime $`P = Q \cap R = Q' \cap R` of $`R`. Then
the canonical Frobenius elements at $`Q` and $`Q'` are conjugate in $`G`:
$$`\mathrm{Frob}_{Q'} = \tau\,\mathrm{Frob}_{Q}\,\tau^{-1} \quad\text{for some } \tau \in G.`
Consequently the Frobenius *conjugacy class* depends only on the prime $`P` below.
:::

:::proof "arith-frob-conjugate"
mathlib's canonical choice `arithFrobAt` is engineered precisely so that Frobenius elements over the
same prime $`P` are conjugate. The construction picks one Frobenius $`\sigma` at a base prime $`Q`
({uses "arith-frob-exists"}[]); for any other prime $`Q'` over $`P`, transitivity gives $`\tau \in G`
with $`Q' = \tau \cdot Q` ({uses "galois-transitive"}[] in the invariant-ring form), and conjugating
a Frobenius transports it along the action: if $`\sigma` is Frobenius at $`Q` then $`\tau\sigma\tau^{-1}`
is Frobenius at $`\tau \cdot Q = Q'` (the lemma `IsArithFrobAt.conj`). The canonical Frobenius at
$`Q'` is taken to be this $`\tau\sigma\tau^{-1}`, so any two canonical Frobenius elements over $`P`
are each conjugate to the common $`\sigma`, hence to one another.
:::

# The Chebotarev density theorem

The `chebotarev-density` project (Birkbeck–Brasca–Roblot) formalises the full Chebotarev density
theorem for number fields *without* using class field theory, following Sharifi §7.2 and
Stevenhagen–Lenstra. The headline theorem and its principal corollaries — completely split primes
and Dirichlet's theorem on primes in arithmetic progressions — are sorry-free on the project's
`development` branch. The nodes below are *informal* (no `(lean := …)`), because the project targets
a newer mathlib than the current AINTLIB build; each links to its exact source declaration and
connects into the dependency graph through the mathlib-backed Galois and Frobenius nodes above.

## Dirichlet Density of a Set of Primes

:::definition "dirichlet-density"
Let $`K` be a number field with ring of integers $`\mathcal{O}_K`. A set $`S` of nonzero prime
ideals of $`\mathcal{O}_K` has *Dirichlet density* $`\delta \in \mathbb{R}`, written
$`\delta(S) = \delta`, if the ratio of partial Dirichlet series converges:
$$`\lim_{s \to 1^+}
  \frac{\displaystyle\sum_{\mathfrak{p} \in S} N\mathfrak{p}^{-s}}
       {\displaystyle\sum_{\mathfrak{p}} N\mathfrak{p}^{-s}}
  = \delta,`
where the denominator runs over all nonzero primes of $`\mathcal{O}_K` and $`N\mathfrak{p} =
[\mathcal{O}_K : \mathfrak{p}]` is the absolute norm. The denominator is asymptotic to
$`\log(1/(s-1))` as $`s \downarrow 1` (the simple pole of the Dedekind zeta function), so $`\delta`
measures the logarithmic proportion of $`S` among all primes.
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density): [`Chebotarev.HasDirichletDensity`](https://github.com/CBirkbeck/chebotarev-density/blob/836b1320988b2333191da1a008ab444f6ecb93e2/CebotarevDensity/Density.lean#L64) — sorry-free.
:::

## The Frobenius Conjugacy Class

:::definition "frobenius-class"
Let $`L/K` be a finite Galois extension of number fields and $`\mathfrak{p}` a nonzero prime of
$`\mathcal{O}_K` unramified in $`L`. The decomposition group of any prime $`\mathfrak{P}` of
$`\mathcal{O}_L` over $`\mathfrak{p}` is cyclic, generated by the arithmetic Frobenius
$`\mathrm{Frob}_{\mathfrak{P}}` ({uses "arith-frob-at"}[]); as $`\mathfrak{P}` varies over the primes
above $`\mathfrak{p}` these generators form a single conjugacy class ({uses "arith-frob-conjugate"}[]).
The *Frobenius conjugacy class* $`\mathrm{Frob}_{\mathfrak{p}} \in \mathrm{Conj}(\mathrm{Gal}(L/K))`
is this class.
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density): [`Chebotarev.frobeniusClass`](https://github.com/CBirkbeck/chebotarev-density/blob/836b1320988b2333191da1a008ab444f6ecb93e2/CebotarevDensity/Frobenius.lean#L199) — sorry-free.
:::

## The Chebotarev Density Theorem

:::theorem "chebotarev-density"
*(Chebotarev density theorem.)* Let $`L/K` be a finite Galois extension of number fields with
$`G = \mathrm{Gal}(L/K)` ({uses "is-galois"}[]), and let $`C \subseteq G` be a conjugacy class. Then
the set of primes $`\mathfrak{p}` of $`\mathcal{O}_K` unramified in $`L` whose Frobenius conjugacy
class ({uses "frobenius-class"}[]) equals $`C` has Dirichlet density ({uses "dirichlet-density"}[])
$$`\delta\!\left(\bigl\{\mathfrak{p} :
  \mathrm{Frob}_{\mathfrak{p}} = C\bigr\}\right)
  = \frac{|C|}{|G|}.`
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density): [`Chebotarev.chebotarev_density`](https://github.com/CBirkbeck/chebotarev-density/blob/836b1320988b2333191da1a008ab444f6ecb93e2/CebotarevDensity/Main.lean#L71) — sorry-free.
:::

:::proof "chebotarev-density"
The proof reduces the conjugacy-class statement to the cyclic case and uses no class field theory
(Sharifi 7.2.2 Step 1; Stevenhagen–Lenstra Appendix). Pick a representative $`\sigma \in C` and let
$`E = L^{\langle\sigma\rangle}` be the fixed field of the cyclic subgroup generated by $`\sigma`
({uses "galois-correspondence"}[]); then $`\mathrm{Gal}(L/E) \cong \langle\sigma\rangle` is cyclic,
hence abelian. The abelian case (`chebotarev_abelian`, itself proved by a cyclotomic crossing trick)
gives Dirichlet density $`1/|\mathrm{Gal}(L/E)| = 1/f` over $`E` for the primes of $`E` whose
Frobenius is $`\sigma`, where $`f = \mathrm{ord}(\sigma)`. A counting argument over the primes of
$`L` above a prime of $`K` (`count_primes_above_with_frobenius_eq_sigma`) shows that, for a prime
$`\mathfrak{p}` of $`K` with Frobenius class $`C`, exactly $`|G|/(f\,|C|)` of the primes of $`L` above
$`\mathfrak{p}` have Frobenius equal to $`\sigma`; this uses transitivity of the Galois action and the
cyclic structure of the decomposition group ({uses "inertia-group"}[], {uses "arith-frob-conjugate"}[]).
Transporting densities between $`K` and $`E` along the asymptotic $`\sum N\mathfrak{p}^{-s} \sim
\log(1/(s-1))` (the lemma `density_lift_through_fixedField`) then yields
$`\delta_K(C) = (f\,|C|/|G|)\cdot(1/f) = |C|/|G|`.
:::

## Density of Completely Split Primes

:::theorem "chebotarev-split-completely"
*(Completely split primes.)* For a finite Galois extension $`L/K` of number fields
({uses "is-galois"}[]), the Dirichlet density of primes of $`\mathcal{O}_K` that split completely
in $`L` is
$$`\delta\!\bigl(\{\mathfrak{p} : \mathfrak{p} \text{ splits completely in } L\}\bigr)
  = \frac{1}{[L:K]}.`
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density): [`Chebotarev.density_split_completely`](https://github.com/CBirkbeck/chebotarev-density/blob/836b1320988b2333191da1a008ab444f6ecb93e2/CebotarevDensity/Main.lean#L151) — sorry-free.
:::

:::proof "chebotarev-split-completely"
A prime $`\mathfrak{p}` splits completely in $`L` exactly when every prime above it has trivial
Frobenius, i.e. its Frobenius conjugacy class is the identity class $`\{1\}`. Applying
{uses "chebotarev-density"}[] with $`C = \{1\}` gives density $`|\{1\}|/|G| = 1/|G|`, and
$`|G| = [L:K]` by {uses "galois-card-aut"}[] — exactly the rewrite by `IsGalois.card_aut_eq_finrank`
that the Lean proof performs.
:::

## Dirichlet Density in Arithmetic Progressions

:::theorem "dirichlet-density-ap"
*(Dirichlet's theorem, density form.)* For $`n \ge 1` and a unit $`a \in (\mathbb{Z}/n\mathbb{Z})^\times`,
the Dirichlet density ({uses "dirichlet-density"}[]) of the rational primes $`p \equiv a \pmod n`
is
$$`\delta\!\bigl(\{p \text{ prime} : p \equiv a \pmod n\}\bigr) = \frac{1}{\varphi(n)}.`
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density): [`Chebotarev.dirichlet_primes_in_AP`](https://github.com/CBirkbeck/chebotarev-density/blob/836b1320988b2333191da1a008ab444f6ecb93e2/CebotarevDensity/Main.lean#L517) — sorry-free.
:::

:::proof "dirichlet-density-ap"
Specialise to $`K = \mathbb{Q}` and the cyclotomic field $`L = \mathbb{Q}(\zeta_n)`
({uses "cyclotomic-extension"}[]). The cyclotomic character identifies $`\mathrm{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q})`
with $`(\mathbb{Z}/n\mathbb{Z})^\times` and sends the Frobenius at an unramified prime $`p` to
$`p \bmod n`; the Lean proof realises this via the cyclotomic case `chebotarev_cyclotomic` and the
unit $`\sigma` with $`\mathrm{autToPow}(\sigma) = a`. Since the Galois group is abelian, the
conjugacy class of $`\sigma` is the singleton $`\{\sigma\}`, so the set of primes with Frobenius
$`\sigma` is the fibre $`\{p : p \equiv a \pmod n\}` up to the finitely many primes dividing $`n`.
Because Dirichlet density is insensitive to finite symmetric differences (`hasDirichletDensity_of_finite_symmDiff`),
discarding those bad primes leaves density $`1/|(\mathbb{Z}/n\mathbb{Z})^\times| = 1/\varphi(n)`. (A
small case split handles $`n \equiv 2 \pmod 4`, where $`\mathbb{Q}(\zeta_n) = \mathbb{Q}(\zeta_{n/2})`.)
:::

## Infinitely Many Primes in Each Frobenius Class

:::theorem "chebotarev-infinitude"
*(Infinitely many primes in each Frobenius class.)* For a finite Galois extension $`L/K` of number
fields and any conjugacy class $`C \subseteq \mathrm{Gal}(L/K)`, there are infinitely many primes
$`\mathfrak{p}` of $`\mathcal{O}_K` unramified in $`L` with Frobenius conjugacy class
({uses "frobenius-class"}[]) equal to $`C`.
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density): [`Chebotarev.infinite_setOf_frobenius_class`](https://github.com/CBirkbeck/chebotarev-density/blob/836b1320988b2333191da1a008ab444f6ecb93e2/CebotarevDensity/Main.lean#L128) — sorry-free.
:::

:::proof "chebotarev-infinitude"
By {uses "chebotarev-density"}[] the set has Dirichlet density $`|C|/|G|`, which is strictly
positive since $`|C| \ge 1` (a conjugacy class contains its representative) and $`|G| \ge 1`. A set
of primes with positive Dirichlet density is infinite — a finite set has density $`0` — so the set
is infinite. This is the qualitative shadow of the quantitative density statement.
:::

# Local fields and complete discrete valuation rings

The `LocalClassFieldTheory` project (Birkbeck) formalises the foundational theory of nonarchimedean
local fields and their ramification, following Serre's *Local Fields*: complete discrete valuation
rings, the unique extension of a discrete valuation to a finite extension, the identification of the
integral closure with the unit ball, and the two flavours (mixed and equal characteristic). It does
*not* contain the local reciprocity map; the cohomological construction of local reciprocity is the
subject of the Buzzard project in the next section. The core files are sorry-free.

## Local Fields and Complete Discrete Valuation Rings

:::definition "local-field"
A *(nonarchimedean) local field* is a field $`K` that is complete with respect to a discrete
valuation $`v` and has finite residue field. A *mixed characteristic local field* is a finite
extension of the field $`\mathbb{Q}_p` of $`p`-adic numbers; an *equal characteristic local field*
is a finite extension of the field $`\mathbb{F}_p((t))` of formal Laurent series over
$`\mathbb{F}_p`.
Formalised in [`LocalClassFieldTheory`](https://github.com/CBirkbeck/LocalClassFieldTheory): [`LocalField`](https://github.com/CBirkbeck/LocalClassFieldTheory/blob/e7d457c0c9e5facbb4ef8a3b66268a3a9b217dd8/LocalClassFieldTheory/LocalField.lean#L33), [`MixedCharLocalField`](https://github.com/CBirkbeck/LocalClassFieldTheory/blob/e7d457c0c9e5facbb4ef8a3b66268a3a9b217dd8/LocalClassFieldTheory/MixedCharacteristic/Basic.lean#L40), [`EqCharLocalField`](https://github.com/CBirkbeck/LocalClassFieldTheory/blob/e7d457c0c9e5facbb4ef8a3b66268a3a9b217dd8/LocalClassFieldTheory/EqCharacteristic/Basic.lean#L349) — sorry-free.
:::

## Extensions of Complete Discrete Valuation Rings

:::theorem "local-field-extension-dvr"
Let $`K` be complete with respect to a discrete valuation $`v` and let $`L/K` be a finite extension.
Then $`v` extends to a discrete valuation $`w` on $`L`, with respect to which $`L` is again complete,
and the integral closure of the unit ball $`\mathcal{O}_K` inside $`L` coincides with the unit ball
$`\mathcal{O}_L = \{x \in L : w(x) \ge 0\}`. In particular $`\mathcal{O}_L` is a discrete valuation
ring, finite and free as an $`\mathcal{O}_K`-module of rank $`[L:K]`; the local ramification index
$`e` ({uses "ramification-index"}[]) and inertia degree $`f` ({uses "inertia-degree"}[]) satisfy the
single-prime fundamental identity
$$`e \cdot f = [L : K]`
({uses "fundamental-identity"}[]).
Formalised in [`LocalClassFieldTheory`](https://github.com/CBirkbeck/LocalClassFieldTheory): [`integralClosure_eq_integer`](https://github.com/CBirkbeck/LocalClassFieldTheory/blob/e7d457c0c9e5facbb4ef8a3b66268a3a9b217dd8/LocalClassFieldTheory/DiscreteValuationRing/Extensions.lean#L603), [`integralClosure.discreteValuationRing_of_finite_extension`](https://github.com/CBirkbeck/LocalClassFieldTheory/blob/e7d457c0c9e5facbb4ef8a3b66268a3a9b217dd8/LocalClassFieldTheory/DiscreteValuationRing/Extensions.lean#L630) — sorry-free.
:::

:::proof "local-field-extension-dvr"
This is Serre's Local Fields, Chapter II, §2, Proposition 3. Completeness of $`K` makes the
valuation extend uniquely: $`w(x) = \tfrac{1}{[L:K]}\,v(N_{L/K}(x))` is forced on each $`x`, and the
project verifies it is multiplicative and additive through the spectral/norm machinery (this is
where the discrete-norm and extension files do their work), with $`L` complete because it is finite
over the complete field $`K`. The unit ball $`\mathcal{O}_L` of $`w` is then shown to be exactly the
integral closure of $`\mathcal{O}_K` in $`L` (`integralClosure_eq_integer`), and a complete discrete
valuation ring, so $`\mathcal{O}_L` is a discrete valuation ring
(`integralClosure.discreteValuationRing_of_finite_extension`). Finiteness and freeness of rank
$`[L:K]` is the structure theorem for finitely generated torsion-free modules over a discrete
valuation ring, and the local $`ef = [L:K]` formula is the single-prime case of the fundamental
identity ({uses "fundamental-identity"}[]).
:::

## Localization at a Prime Produces a Discrete Valuation Ring

:::theorem "local-field-localization-dvr"
Let $`R` be a Dedekind domain (or any domain with a height-one prime) and $`\mathfrak{p}` a nonzero
prime of $`R`. The localisation $`R_{\mathfrak{p}}` is a discrete valuation ring, with the
$`\mathfrak{p}`-adic valuation as its discrete valuation. Completing at $`\mathfrak{p}` produces a
complete discrete valuation ring whose fraction field is a local field
({uses "local-field"}[]); for a number field this completion is a mixed characteristic local field.
Formalised in [`LocalClassFieldTheory`](https://github.com/CBirkbeck/LocalClassFieldTheory): [`discreteValuationRing`](https://github.com/CBirkbeck/LocalClassFieldTheory/blob/e7d457c0c9e5facbb4ef8a3b66268a3a9b217dd8/LocalClassFieldTheory/DiscreteValuationRing/Localization.lean#L59) — sorry-free.
:::

:::proof "local-field-localization-dvr"
The $`\mathfrak{p}`-adic valuation on $`R` is discrete, and localising at $`\mathfrak{p}` makes its
unit ball the local ring $`R_{\mathfrak{p}}`, which the project establishes is a discrete valuation
ring (`Localization.discreteValuationRing`). Completing $`R_{\mathfrak{p}}` in the
$`\mathfrak{p}`-adic metric preserves the discrete valuation and the residue field while making the
ring complete (the completion file). When $`R = \mathcal{O}_K` is the ring of integers of a number
field, the residue field $`R/\mathfrak{p}` is finite and the fraction field of the completion has
characteristic $`0`, so it is a mixed characteristic local field by definition
({uses "local-field"}[]).
:::

# Group cohomology, Tate cohomology, Herbrand quotients, and local CFT

The `ClassFieldTheory` Clay-school project (Buzzard et al.) develops a cohomological route to local
class field theory. The group- and Tate-cohomology foundations and the abstract Tate-theorem
machinery — including the reciprocity isomorphism attached to a finite class formation — are
sorry-free; the analytic input computing the Herbrand quotient of the local unit group, and hence
the construction of the *global* local-field class formation and the explicit local reciprocity map,
are still in progress. The nodes below are *informal*; each links to its exact source declaration and
states whether that declaration is currently sorry-free.

## Tate Cohomology

:::definition "tate-cohomology"
Let $`G` be a finite group and $`M` a $`\mathbb{Z}[G]`-module. The *Tate cohomology* groups
$`\widehat{H}^n(G, M)` are defined for all $`n \in \mathbb{Z}` by splicing the homological and
cohomological complexes through the *norm map* $`N_G(m) = \sum_{g \in G} g \cdot m`:
$$`\cdots \to C_1(G,M) \to C_0(G,M) \xrightarrow{\,N_G\,} C^0(G,M) \to C^1(G,M) \to \cdots.`
Thus $`\widehat{H}^n(G,M) = H^n(G,M)` for $`n \ge 1`, $`\widehat{H}^0(G,M) = M^G / N_G M`, and
$`\widehat{H}^{-1}(G,M) = \ker(N_G)/I_G M` where $`I_G M` is spanned by the differences
$`g \cdot m - m`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory): [`tateComplex`](https://github.com/kbuzzard/ClassFieldTheory/blob/d5c1d044e770994e426e49256a050cb7dfb3f7cb/ClassFieldTheory/Cohomology/TateCohomology.lean#L71) — sorry-free.
:::

## The Herbrand Quotient

:::definition "herbrand-quotient"
Let $`G` be a *finite cyclic* group and $`M` a $`\mathbb{Z}[G]`-module. Tate cohomology of a cyclic
group is $`2`-periodic, $`\widehat{H}^n(G,M) \cong \widehat{H}^{n+2}(G,M)`, so only the two groups
$`\widehat{H}^0` and $`\widehat{H}^{-1}` occur. The *Herbrand quotient* is their ratio of orders
$$`h(G,M) = \frac{|\widehat{H}^0(G,M)|}{|\widehat{H}^{-1}(G,M)|}
         = \frac{|M^G / N_G M|}{|\ker(N_G)/I_G M|},`
defined as a rational number (mathlib-style, $`|H^2(M)|/|H^1(M)|`), with the convention that it is
$`0` if either group is infinite. For the trivial module $`\mathbb{Z}`, $`h(G, \mathbb{Z}) = |G|`.
It is multiplicative on short exact sequences, which is what makes it computable.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory): [`Rep.herbrandQuotient`](https://github.com/kbuzzard/ClassFieldTheory/blob/d5c1d044e770994e426e49256a050cb7dfb3f7cb/ClassFieldTheory/Cohomology/FiniteCyclic/HerbrandQuotient/Defs.lean#L58) — sorry-free.
:::

## Herbrand Quotients of Local Field Unit Groups

:::theorem "herbrand-local-units"
Let $`l/k` be a cyclic extension of nonarchimedean local fields ({uses "local-field"}[]) with
$`G = \mathrm{Gal}(l/k)` ({uses "is-galois"}[]). Then the Herbrand quotients
({uses "herbrand-quotient"}[]) of the unit group of the ring of integers and of the multiplicative
group are
$$`h(G, \mathcal{O}_l^\times) = 1 \qquad\text{and}\qquad h(G, l^\times) = [l:k].`
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory): [`Rep.herbrandQuotient_isNonarchimedeanLocalField_units`](https://github.com/kbuzzard/ClassFieldTheory/blob/d5c1d044e770994e426e49256a050cb7dfb3f7cb/ClassFieldTheory/IsNonarchimedeanLocalField/HerbrandQuotient.lean#L35) — in progress (the input $`h(\mathcal{O}_l^\times) = 1` is still a `sorry`).
:::

:::proof "herbrand-local-units"
For $`h(G, \mathcal{O}_l^\times) = 1`: by a Serre approximation argument (the normal basis theorem
gives an open $`G`-submodule $`M \subseteq \mathcal{O}_l^\times` that is cohomologically trivial,
built from a copy of the group algebra $`k[G]`). Since $`\mathcal{O}_l^\times` is compact and $`M`
is open, the quotient $`\mathcal{O}_l^\times / M` is finite, so it has Herbrand quotient $`1`; by
multiplicativity of the Herbrand quotient on short exact sequences ({uses "herbrand-quotient"}[]),
$`h(\mathcal{O}_l^\times) = h(M) = 1`.

For $`h(G, l^\times) = [l:k]`: the valuation gives a short exact sequence of $`G`-modules
$`0 \to \mathcal{O}_l^\times \to l^\times \to \mathbb{Z} \to 0`. Multiplicativity then yields
$`h(l^\times) = h(\mathcal{O}_l^\times) \cdot h(\mathbb{Z}) = 1 \cdot [l:k] = [l:k]`, using
$`h(G,\mathbb{Z}) = |G| = [l:k]`. The Lean development carries out exactly this two-step computation;
the first step is the part still under construction.
:::

## The Reciprocity Isomorphism of a Class Formation

:::theorem "tate-reciprocity-iso"
*(Reciprocity isomorphism of a class formation.)* Let $`G` be a finite group and let $`N` be a
$`\mathbb{Z}[G]`-module equipped with a class $`\tau \in H^2(G, N)` making $`(G, N)` a *finite class
formation* (so cup product with $`\tau` induces the cohomology isomorphisms of Tate's theorem). Then
there is a canonical isomorphism
$$`\widehat{H}^0(G, N) \;\cong\; G^{\mathrm{ab}}`
between the $`0`-th Tate cohomology of $`N` and the abelianisation of $`G`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory): [`Rep.split.reciprocityIso`](https://github.com/kbuzzard/ClassFieldTheory/blob/d5c1d044e770994e426e49256a050cb7dfb3f7cb/ClassFieldTheory/Cohomology/SplittingModule.lean#L376) — sorry-free.
:::

:::proof "tate-reciprocity-iso"
This is the abstract engine of class field theory (Tate's theorem), formalised independently of any
arithmetic. From the class formation hypothesis the splitting module of $`\tau` has trivial
cohomology, so the connecting maps of the splitting short exact sequence are isomorphisms in all
degrees ({uses "tate-cohomology"}[]). Dimension-shifting by two via these isomorphisms identifies
$`\widehat{H}^0(G, N)` with $`\widehat{H}^{-2}(G, \mathbb{Z})`, which is the first group homology
$`H_1(G, \mathbb{Z}) \cong G^{\mathrm{ab}}` of the trivial module. Composing these canonical
isomorphisms produces the stated reciprocity isomorphism.
:::

## Local Reciprocity and Local Class Field Theory

:::theorem "local-reciprocity"
*(Local reciprocity / local class field theory.)* For every finite Galois extension $`l/k` of
local fields ({uses "local-field"}[]) there is a canonical isomorphism
$$`\mathrm{rec}_{l/k} : k^\times / N_{l/k}(l^\times) \xrightarrow{\;\sim\;}
   \mathrm{Gal}(l/k)^{\mathrm{ab}},`
the *local reciprocity map*, where $`N_{l/k}` is the norm. In the unramified case $`\mathrm{rec}_{l/k}`
sends a uniformiser $`\pi_k` to the arithmetic Frobenius generator ({uses "arith-frob-at"}[]) of
$`\mathrm{Gal}(l/k)`, and for finite abelian $`l/k`, the norm subgroups order the subextensions:
$`l_1 \subseteq l_2` iff $`N_{l_1/k}(l_1^\times) \supseteq N_{l_2/k}(l_2^\times)`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory): the abstract reciprocity isomorphism [`Rep.split.reciprocityIso`](https://github.com/kbuzzard/ClassFieldTheory/blob/d5c1d044e770994e426e49256a050cb7dfb3f7cb/ClassFieldTheory/Cohomology/SplittingModule.lean#L376) is sorry-free; assembling $`(G, l^\times)` into a class formation (via {uses "herbrand-local-units"}[]) and extracting the explicit map is in progress.
:::

:::proof "local-reciprocity"
The reciprocity map is the specialisation of the abstract class-formation isomorphism
({uses "tate-reciprocity-iso"}[]) to $`N = l^\times`. The two inputs that make $`(G, l^\times)` a
finite class formation are: Hilbert 90, giving $`\widehat{H}^{-1}(G, l^\times) = H^1(G, l^\times) = 0`;
and the order computation $`|H^2(G, l^\times)| = [l:k]`, which combines the local Herbrand quotient
({uses "herbrand-local-units"}[]) with an inflation–restriction upper bound to pin down a generator
$`\sigma_{l/k} \in H^2(G, l^\times)` of order $`[l:k]` — the *local fundamental class* — constructed
by lifting from the unramified case where it is explicit in terms of the Frobenius. Feeding the
fundamental class into {uses "tate-reciprocity-iso"}[] gives $`\widehat{H}^0(G, l^\times) =
k^\times/N(l^\times) \cong G^{\mathrm{ab}}`. The norm-subgroup ordering is functoriality of the
construction in $`l`.
:::

## The Local Kronecker-Weber Theorem

:::theorem "local-kronecker-weber"
*(Local Kronecker–Weber.)* Every finite abelian extension $`l/\mathbb{Q}_p` ({uses "is-galois"}[])
embeds over $`\mathbb{Q}_p` into a cyclotomic extension $`\mathbb{Q}_p(\zeta_n)`
({uses "cyclotomic-extension"}[]) for some $`n`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory): downstream of local reciprocity — in progress.
:::

:::proof "local-kronecker-weber"
By local reciprocity ({uses "local-reciprocity"}[]), $`N_{l/\mathbb{Q}_p}(l^\times)` is an open
finite-index subgroup of $`\mathbb{Q}_p^\times`, so it contains $`1 + p^n\mathbb{Z}_p` for some $`n`.
An explicit computation with the cyclotomic norm groups shows every element of
$`p^{\mathbb{Z}} \times (1 + p^n\mathbb{Z}_p)` is a norm from $`\mathbb{Q}_p(\zeta_{p^n})`, and the
unramified part is a norm from $`\mathbb{Q}_p(\zeta_{p^f - 1})`. Therefore $`N(l^\times)` contains the
norm group of $`\mathbb{Q}_p(\zeta_{p^f-1}, \zeta_{p^n})`, and the norm-subgroup ordering
({uses "local-reciprocity"}[]) forces $`l` into that cyclotomic field.
:::

# Power residue symbols

The `power_residue_symbols` project (Birkbeck) formalises the $`n`-th power residue symbol for
number fields containing the $`n`-th roots of unity. The construction of the symbol is the project's
goal; it is currently in progress (the uniqueness of the defining root of unity still rests on
`sorry`s in the supporting lemmas), and no reciprocity law for the symbol is stated in the project.

## The Power Residue Symbol

:::definition "power-residue-symbol"
Let $`F` be a number field, $`\zeta_n \in \mathcal{O}_F` a primitive $`n`-th root of unity, and
$`\mathfrak{p}` a prime of $`\mathcal{O}_F` whose absolute norm is coprime to $`n`. For
$`\alpha \in \mathcal{O}_F` with $`\alpha \notin \mathfrak{p}`, the *$`n`-th power residue symbol*
at $`\mathfrak{p}` is the unique $`n`-th root of unity $`\left(\frac{\alpha}{\mathfrak{p}}\right)_n`
characterised by the congruence
$$`\left(\frac{\alpha}{\mathfrak{p}}\right)_n \equiv \alpha^{(N\mathfrak{p}-1)/n} \pmod{\mathfrak{p}},`
where $`N\mathfrak{p} = |\mathcal{O}_F/\mathfrak{p}|` ({uses "inertia-degree"}[]) is the absolute
norm. Existence and uniqueness of this root of unity come from the fact that the residue field
$`\mathcal{O}_F/\mathfrak{p}` contains a full set of $`n`-th roots of unity (since $`n \mid
N\mathfrak{p}-1`) on which $`\alpha^{(N\mathfrak{p}-1)/n}` lands; the symbol thus packages the action
of the Frobenius ({uses "frobenius-endomorphism"}[], {uses "arith-frob-roots-of-unity"}[]) on roots
of unity, generalising the Legendre and Jacobi symbols.
Formalised in [`power_residue_symbols`](https://github.com/CBirkbeck/power_residue_symbols): [`powerResidueSymbol`](https://github.com/CBirkbeck/power_residue_symbols/blob/0b573a447c7f230d7993c2f25b031a1a87ea46b2/PowerResSymbols/PowerResidueSymbol.lean#L309) — in progress (the uniqueness lemma `exists_pth_root` it depends on still contains a `sorry`).
:::

# Forthcoming in mathlib

The node below is an *informal* statement of a result that is the subject of an open mathlib pull
request. It carries a `pr_url` pointing at the live PR and **no** `(lean := …)` reference: the
declaration is not yet in mathlib v4.30.0-rc2. It connects into the dependency graph through the
mathlib-backed Galois and inertia nodes of this chapter, and should be re-pointed to
`(lean := …)` once the PR merges.

## The Galois Group Is Generated by Inertia Subgroups

:::theorem "galois-generated-by-inertia" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/33992")
*(The Galois group is generated by inertia.)* Let $`L/K` be a finite Galois extension of number
fields ({uses "is-galois"}[]) with group $`G = \mathrm{Gal}(L/K)`, and suppose $`K = \mathbb{Q}`
(or, more generally, that $`L/K` has no nontrivial subextension unramified at every finite prime).
Then $`G` is generated by the inertia subgroups $`\mathrm{inertia}(G, \mathfrak{P})`
({uses "inertia-group"}[]) attached to the primes $`\mathfrak{P}` of $`L` ramifying over $`K`:
$$`G \;=\; \bigl\langle\, \mathrm{inertia}(G, \mathfrak{P}) \;:\;
   \mathfrak{P} \text{ ramified in } L/\mathbb{Q} \,\bigr\rangle.`
Equivalently, the maximal subextension of $`L/\mathbb{Q}` unramified at every finite prime is
$`\mathbb{Q}` itself — Minkowski's theorem that $`\mathbb{Q}` has no nontrivial everywhere-unramified
extension, in its group-theoretic form. The subgroup generated by all inertia groups fixes precisely
the maximal unramified subextension.
In review — [mathlib PR #33992](https://github.com/leanprover-community/mathlib4/pull/33992).
:::
