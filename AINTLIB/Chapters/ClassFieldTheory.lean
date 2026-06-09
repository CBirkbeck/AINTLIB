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

This chapter covers the Galois theory of field extensions, decomposition and inertia in Galois
extensions of Dedekind domains, and Frobenius elements. The deeper results of class field theory —
the Artin reciprocity law, the Chebotarev density theorem, and local/global class field theory —
are not yet in mathlib; they are supplied by the `chebotarev-density` and `LocalClassFieldTheory`
external projects, which will be integrated in Phase 3 of this blueprint.

Throughout, $`K` and $`L` denote fields with $`L/K` an algebraic extension, $`G = \mathrm{Gal}(L/K)`
the Galois group, $`A \subset B` rings of integers (or more generally Dedekind domains) with
$`B` the integral closure of $`A` in $`L`, and $`\mathfrak{p}` a nonzero prime of $`A`.

# Galois extensions and the fundamental theorem

:::definition "is-galois" (lean := "IsGalois")
A field extension $`L/K` is *Galois* if it is simultaneously separable and normal: every element
of $`L` is separable over $`K`, and every irreducible polynomial over $`K` that has one root in $`L`
splits completely in $`L`. We write $`\mathrm{Gal}(L/K)` for the group of field automorphisms of
$`L` fixing $`K` pointwise.
:::

:::theorem "galois-card-aut" (lean := "IsGalois.card_aut_eq_finrank")
Let $`L/K` be a finite Galois extension. Then
$$`|\mathrm{Gal}(L/K)| = [L : K].`
:::

:::proof "galois-card-aut"
By the primitive element theorem, $`L = K(\alpha)` for some $`\alpha`. A $`K`-automorphism of $`L`
is determined by where it sends $`\alpha`, and the image must be a root of $`\mathrm{minpoly}_K(\alpha)`.
Because $`L/K` is Galois ({uses "is-galois"}[]) it is separable and normal: separability makes the
minimal polynomial have distinct roots, and normality forces all those roots to lie in $`L`. The
count of such automorphisms therefore equals the degree of the minimal polynomial, which equals
$`[L : K]`.
:::

:::theorem "galois-correspondence" (lean := "IsGalois.intermediateFieldEquivSubgroup")
*(Fundamental theorem of Galois theory.)* Let $`L/K` be a finite Galois extension with
$`G = \mathrm{Gal}(L/K)`. There is an order-reversing bijection
$$`\left\{\text{intermediate fields } K \subseteq M \subseteq L\right\}
\;\longleftrightarrow\;
\left\{\text{subgroups of } G\right\}`
sending an intermediate field $`M` to the fixing subgroup $`\mathrm{Gal}(L/M)`, and a subgroup
$`H \le G` to the fixed field $`L^H`. Under this bijection, $`[L : M] = |H|` and
$`[M : K] = [G : H]`.
:::

:::proof "galois-correspondence"
The maps in both directions are inverse order-reversing bijections. The map $`M \mapsto \mathrm{Gal}(L/M)`
is well-defined since $`L/M` is again Galois. For the key identity $`L^{\mathrm{Gal}(L/M)} = M`: by
{uses "galois-card-aut"}[], $`|\mathrm{Gal}(L/M)| = [L:M]`, and the fixed field of a group of
automorphisms has degree over $`K` equal to $`[G : \mathrm{Gal}(L/M)]` by the same count, forcing
$`L^{\mathrm{Gal}(L/M)} = M`. The reverse direction $`H \mapsto L^H` works because $`L/L^H` is
Galois with group $`H`, so applying the first direction recovers $`H`.
:::

# Decomposition and inertia in Galois extensions

:::definition "inertia-group" (lean := "Ideal.inertia")
Let $`G` be a group acting on a ring $`S`, and let $`Q` be an ideal of $`S`. The
*inertia group* of $`Q` (with respect to $`G`) is the subgroup
$$`I(Q) = \{\, \sigma \in G \mid \sigma(x) \equiv x \pmod{Q} \text{ for all } x \in S \,\}.`
In the number-field setting, with $`G = \mathrm{Gal}(L/K)` and $`Q = \mathfrak{P}` a prime
of $`B` lying over $`\mathfrak{p}`, this is the kernel of the natural map from the
decomposition group $`D(\mathfrak{P})` to the Galois group of the residue field extension.
:::

:::lemma_ "inertia-card" (lean := "Ideal.card_inertia_eq_ramificationIdxIn")
Let $`B/A` be a Galois extension of Dedekind domains with group $`G`, and let
$`\mathfrak{P}` be a prime of $`B` lying over a nonzero prime $`\mathfrak{p}` of $`A`.
Then the order of the inertia group equals the ramification index:
$$`|I(\mathfrak{P})| = e(\mathfrak{P}/\mathfrak{p}).`
:::

:::proof "inertia-card"
The Galois group acts transitively on the primes over $`\mathfrak{p}`
({uses "galois-correspondence"}[]). The orbit-stabiliser theorem gives
$`|G| = |D(\mathfrak{P})| \cdot r`, where $`r` is the number of primes over $`\mathfrak{p}`.
The decomposition group $`D(\mathfrak{P})` surjects onto the residue Galois group
$`\mathrm{Gal}(k(\mathfrak{P})/k(\mathfrak{p}))` with kernel the inertia group $`I(\mathfrak{P})`
({uses "inertia-group"}[]), so $`|D(\mathfrak{P})| = e \cdot f` where the ramification index
$`e = e(\mathfrak{P}/\mathfrak{p})` ({uses "ramification-index"}[]) and the inertia degree
$`f = f(\mathfrak{P}/\mathfrak{p}) = [k(\mathfrak{P}) : k(\mathfrak{p})]` ({uses "inertia-degree"}[]).
Combining with the fundamental identity ({uses "galois-efr-identity"}[])
$`r \cdot e \cdot f = [L:K] = |G|` yields $`|I(\mathfrak{P})| = e`.
:::

:::theorem "galois-efr-identity" (lean := "Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn")
Let $`B/A` be a Galois extension of Dedekind domains with Galois group $`G`, and let
$`\mathfrak{p}` be a nonzero prime of $`A`. Then
$$`r \cdot e \cdot f \;=\; |G|,`
where $`r` is the number of primes of $`B` lying over $`\mathfrak{p}`, $`e` is their common
ramification index $`e(\mathfrak{P}/\mathfrak{p})`, and $`f` is their common inertia degree
$`f(\mathfrak{P}/\mathfrak{p})`.
:::

:::proof "galois-efr-identity"
In a Galois extension all primes over $`\mathfrak{p}` are conjugate under $`G`
({uses "galois-correspondence"}[]), so they share a common ramification index $`e`
({uses "ramification-index"}[]) and a common inertia degree $`f` ({uses "inertia-degree"}[]).
The general fundamental identity $`\sum_i e_i f_i = [L:K]` over all primes $`\mathfrak{P}_i`
over $`\mathfrak{p}` ({uses "fundamental-identity"}[]) therefore collapses, with $`r` equal
summands, to $`r \cdot e \cdot f = [L:K] = |G|`.
:::

# Frobenius elements

:::definition "frobenius-endomorphism" (lean := "frobenius")
Let $`R` be a commutative ring of characteristic exponent $`p` (so $`p` is either $`1`
or a prime, and $`x^p = 0 \Rightarrow x = 0`). The *Frobenius endomorphism* is the ring
homomorphism
$$`\varphi \colon R \to R, \quad x \mapsto x^p.`
It is a ring homomorphism because in characteristic $`p`, the binomial theorem gives
$`(x+y)^p = x^p + y^p`.
:::

:::definition "arith-frob-at" (lean := "IsArithFrobAt")
Let $`G` be a group acting on a ring $`S`, with fixed subring $`R`, and let $`Q` be a prime
ideal of $`S` with finite residue field $`S/Q`. Write $`q = |R/Q \cap R|`. An element
$`\sigma \in G` is an *arithmetic Frobenius element at $`Q`* if it induces the Frobenius
endomorphism ({uses "frobenius-endomorphism"}[]) $`x \mapsto x^q` on the residue field, i.e.
$$`\sigma(x) \equiv x^q \pmod{Q} \quad \text{for all } x \in S.`
:::

:::lemma_ "arith-frob-exists" (lean := "IsArithFrobAt.exists_of_isInvariant")
Let $`G` be a finite group acting on a ring $`S` with fixed subring $`R = S^G`, and let $`Q`
be a prime ideal of $`S` with finite residue field. Then an arithmetic Frobenius element
$`\sigma \in G` at $`Q` exists.
:::

:::proof "arith-frob-exists"
The residue field extension $`S/Q` over $`R/Q \cap R` is a finite extension of finite fields,
hence Galois ({uses "is-galois"}[]) with cyclic Galois group generated by the Frobenius
automorphism $`x \mapsto x^q` ({uses "frobenius-endomorphism"}[]) with $`q = |R/Q \cap R|`. The
surjectivity of the map from the decomposition group $`D(Q)` onto this residue Galois group
provides a $`\sigma \in G` whose action on $`S/Q` is exactly this Frobenius; lifting back gives the
required congruence, exhibiting $`\sigma` as an arithmetic Frobenius at $`Q` ({uses "arith-frob-at"}[]).
:::

:::lemma_ "arith-frob-conjugate" (lean := "isConj_arithFrobAt")
Let $`G` act on $`S` with fixed subring $`R`, and let $`Q, Q'` be primes of $`S` lying over
the same prime $`P = Q \cap R = Q' \cap R`, each with finite residue field. Then the
arithmetic Frobenius elements at $`Q` and $`Q'` are conjugate in $`G`: there exists
$`\tau \in G` such that
$$`\mathrm{Frob}_{Q'} = \tau \,\mathrm{Frob}_Q\, \tau^{-1}.`
:::

:::proof "arith-frob-conjugate"
Since $`G` acts transitively on the primes over $`P` — the same transitivity of the Galois action
furnished by the Galois correspondence ({uses "galois-correspondence"}[]) — there exists
$`\tau \in G` with $`\tau \cdot Q = Q'`. If $`\sigma` is an arithmetic Frobenius at $`Q`
({uses "arith-frob-at"}[]),
then for any $`x \in S`, $`\tau \sigma \tau^{-1}` acts on $`x \bmod Q'` as
$`\tau(\sigma(\tau^{-1} x))`, and reducing modulo $`\tau \cdot Q = Q'` shows this equals
$`x^q \bmod Q'`, making $`\tau\sigma\tau^{-1}` a Frobenius at $`Q'`. The class in $`G` is thus
well-defined up to conjugacy.
:::
