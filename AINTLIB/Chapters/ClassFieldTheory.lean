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

# Phase 3 (not yet in Mathlib)

The nodes below record results from four external projects that extend the Galois and class-field
machinery of this chapter beyond what is currently in Mathlib.
They are *informal*: no `(lean := …)` attribute is supplied, because the external projects target
Mathlib versions incompatible with the current AINTLIB build.
Each node carries a `Formalised in` provenance line and connects to the dep-graph through the
Mathlib-backed nodes above.

## Chebotarev density theorem (chebotarev-density)

The `chebotarev-density` project (Birkbeck–Brasca–Roblot) formalises the full Chebotarev density
theorem without using class field theory, following Sharifi §7.2 and Stevenhagen–Lenstra.
The headline theorem and its two principal corollaries are sorry-free as of the `development`
branch.

:::definition "dirichlet-density"
Let $`K` be a number field with ring of integers $`\mathcal{O}_K`. A set $`S` of nonzero prime
ideals of $`\mathcal{O}_K` has *Dirichlet density* $`\delta \in \mathbb{R}`, written
$`\delta(S) = \delta`, if
$$`\lim_{s \to 1^+}
  \frac{\displaystyle\sum_{\mathfrak{p} \in S} N\mathfrak{p}^{-s}}
       {\displaystyle\sum_{\mathfrak{p}} N\mathfrak{p}^{-s}}
  = \delta,`
where the denominator runs over all nonzero prime ideals of $`\mathcal{O}_K` and
$`N\mathfrak{p} = [\mathcal{O}_K : \mathfrak{p}]` is the absolute norm.
The denominator is asymptotic to $`\log(1/(s-1))` as $`s \downarrow 1`.
:::

:::theorem "chebotarev-density"
*(Chebotarev density theorem.)* Let $`L/K` be a finite Galois extension of number fields with
Galois group $`G = \mathrm{Gal}(L/K)` ({uses "is-galois"}[]). For any conjugacy class
$`C \subseteq G`, the Dirichlet density ({uses "dirichlet-density"}[]) of the set of primes
$`\mathfrak{p}` of $`\mathcal{O}_K` unramified in $`L` whose Frobenius conjugacy class
({uses "arith-frob-at"}[]) equals $`C` is
$$`\delta\!\left(\bigl\{\mathfrak{p} \subset \mathcal{O}_K :
  \mathrm{Frob}_{\mathfrak{p}} = C\bigr\}\right)
  = \frac{|C|}{|G|}.`
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density) (sorry-free).
:::

:::proof "chebotarev-density"
The proof reduces to the abelian case via Chebotarev's crossing trick and does not use class field
theory. Pick a representative $`\sigma \in C` and let $`E = L^{\langle\sigma\rangle}` be the fixed
field ({uses "galois-correspondence"}[]) of the cyclic subgroup generated by $`\sigma`. Since
$`L/E` is abelian, the *abelian Chebotarev theorem* (proved by the cyclotomic crossing trick)
gives $`\delta_E(\{\mathfrak{P} : \mathrm{Frob}_\mathfrak{P} = \sigma\}) = 1/|\mathrm{Gal}(L/E)|`.
For each prime $`\mathfrak{p}` of $`K` with Frobenius class $`C`, exactly
$`|G|/(f\,|C|)` primes of $`L` above $`\mathfrak{p}` have Frobenius equal to $`\sigma`
(where $`f = \mathrm{ord}(\sigma)`), by transitivity of the Galois action and the structure of
the decomposition group ({uses "inertia-group"}[]). A density comparison between $`K` and $`E`
using the asymptotic $`\sum N\mathfrak{p}^{-s} \sim \log(1/(s-1))` then gives
$`\delta_K(C) = (f\,|C|/|G|) \cdot (1/f) = |C|/|G|`.
:::

:::theorem "chebotarev-split-completely"
*(Corollary.)* For a finite Galois extension $`L/K` of number fields ({uses "is-galois"}[]),
the Dirichlet density of primes of $`\mathcal{O}_K` that split completely in $`L` equals
$$`\delta\!\bigl(\{\mathfrak{p} : \mathfrak{p} \text{ splits completely in } L\}\bigr)
  = \frac{1}{[L:K]}.`
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density) (sorry-free).
:::

:::proof "chebotarev-split-completely"
A prime $`\mathfrak{p}` splits completely in $`L` if and only if its Frobenius class is the
trivial conjugacy class $`\{1\}`. Applying {uses "chebotarev-density"}[] with $`C = \{1\}` gives
density $`1/|G| = 1/[L:K]`, using $`|\mathrm{Gal}(L/K)| = [L:K]`
({uses "galois-correspondence"}[]).
:::

:::theorem "dirichlet-density-ap"
*(Dirichlet, Chebotarev density form.)* For $`n \ge 1` and $`a \in (\mathbb{Z}/n\mathbb{Z})^\times`,
the Dirichlet density ({uses "dirichlet-density"}[]) of rational primes $`p \equiv a \pmod n` is
$$`\delta\!\bigl(\{p \text{ prime} : p \equiv a \pmod n\}\bigr) = \frac{1}{\varphi(n)}.`
Formalised in [`chebotarev-density`](https://github.com/CBirkbeck/chebotarev-density) (sorry-free).
:::

:::proof "dirichlet-density-ap"
Specialise {uses "chebotarev-density"}[] to $`K = \mathbb{Q}` and the cyclotomic extension
$`L = \mathbb{Q}(\zeta_n)` ({uses "cyclotomic-extension"}[]). The cyclotomic character identifies
$`\mathrm{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q})` with $`(\mathbb{Z}/n\mathbb{Z})^\times`; the
Frobenius at an unramified prime $`p` corresponds to $`p \bmod n`. Since $`G` is abelian every
conjugacy class is a singleton, so the Chebotarev density at $`\{a\}` is
$`1/|(\mathbb{Z}/n\mathbb{Z})^\times| = 1/\varphi(n)`.
:::

## Local fields and complete DVRs (LocalClassFieldTheory)

The `LocalClassFieldTheory` project (Birkbeck) formalises the basic theory of local fields, their
ramification and inertia structure, and—building on the Buzzard cohomological approach—the
local reciprocity isomorphism.

:::definition "local-field"
A *local field* (nonarchimedean) is a field that is complete with respect to a discrete valuation
and has finite residue field. A *mixed characteristic local field* is a finite extension of the
field $`\mathbb{Q}_p` of $`p`-adic numbers for some prime $`p`; an *equal characteristic local
field* is a finite extension of the field $`\mathbb{F}_p((t))` of formal Laurent series over
$`\mathbb{F}_p`.
:::

:::theorem "local-field-dvr"
Let $`K` be a local field (nonarchimedean) with discrete valuation $`v`. Then the unit ball
$`\mathcal{O}_K = \{x \in K : v(x) \ge 0\}` is a discrete valuation ring, and for any finite
extension $`L/K` ({uses "is-galois"}[] in the Galois case), $`L` again carries a discrete
valuation extending $`v` and $`L` is complete. The integral closure of $`\mathcal{O}_K` in $`L`
is $`\mathcal{O}_L` and is a finite free $`\mathcal{O}_K`-module of rank $`[L:K]`.
The local ramification index $`e` and inertia degree $`f` satisfy
$$`e \cdot f = [L : K]`
({uses "ramification-index"}[], {uses "inertia-degree"}[], {uses "fundamental-identity"}[]).
Formalised in [`LocalClassFieldTheory`](https://github.com/CBirkbeck/LocalClassFieldTheory) (in progress).
:::

:::proof "local-field-dvr"
Completeness of $`K` is used to show that $`v` extends uniquely to $`L` (by Hensel's lemma for
the minimal polynomial of a uniformiser of $`L`); the completion of $`L` at this valuation
coincides with $`L` because $`L` is finite over the complete field $`K`. The assertion about
$`\mathcal{O}_L` is Serre's Proposition II.3 (Cassels–Fröhlich): the integral closure of a
complete DVR inside a finite separable extension is a free module of the expected rank. The local
$`ef`-formula is the specialisation of the fundamental identity ({uses "fundamental-identity"}[])
to the case of a single prime above $`\mathfrak{p}`.
:::

:::theorem "local-field-completion"
*(Global to local.)* Let $`R` be a Dedekind domain with fraction field $`K`, and let
$`\mathfrak{p}` be a nonzero prime of $`R`. The completion $`K_\mathfrak{p}` carries a discrete
valuation extending $`v_\mathfrak{p}` and its unit ball is $`R_\mathfrak{p}`, the localisation of
$`R` at $`\mathfrak{p}`. In particular the completion of a number field at a finite place is a
mixed characteristic local field ({uses "local-field"}[]).
Formalised in [`LocalClassFieldTheory`](https://github.com/CBirkbeck/LocalClassFieldTheory) (in progress).
:::

:::proof "local-field-completion"
The valuation $`v_\mathfrak{p}` is a discrete valuation on $`K`; the universal property of
completion produces $`K_\mathfrak{p}` as the completion of $`K` in the $`v_\mathfrak{p}`-adic
metric. That $`\mathcal{O}_{K_\mathfrak{p}} = R_\mathfrak{p}` follows from the fact that the
$`v_\mathfrak{p}`-adic absolute value of $`x \in K` is determined by the $`\mathfrak{p}`-part
of the principal ideal $`(x) \subset R`. Mixedness of characteristic is immediate: $`K` has
characteristic $`0`, while the residue field of $`\mathfrak{p}` is finite of characteristic
$`p = \mathrm{char}(R/\mathfrak{p})`.
:::

## Group cohomology, Tate cohomology, Herbrand quotients, and local CFT (ClassFieldTheory-buzzard)

The `ClassFieldTheory` Clay-school project (Buzzard et al., 2025) develops a cohomological proof
of local class field theory. The group-cohomology and Tate-cohomology foundations are sorry-free;
the Herbrand-quotient computation and the construction of the local fundamental class are
substantially complete; higher-level consequences (e.g., Kronecker–Weber) are in progress.

:::definition "tate-cohomology"
Let $`G` be a finite group and $`M` a $`\mathbb{Z}[G]`-module. Recall that $`H^n(G, M)` and
$`H_n(G, M)` denote the $`n`-th group cohomology and homology respectively. The *Tate cohomology*
$`\widehat{H}^n(G, M)` is defined for all $`n \in \mathbb{Z}` by gluing the cochain and chain
complexes via the *norm map* $`N_G(m) = \sum_{g \in G} g \cdot m`:
$$`\cdots \to C_1(G,M) \to C_0(G,M) \xrightarrow{N_G} C^0(G,M) \to C^1(G,M) \to \cdots`
Thus $`\widehat{H}^n(G,M) = H^n(G,M)` for $`n \ge 1`, $`\widehat{H}^0(G,M) = M^G / N_G M`,
and $`\widehat{H}^{-1}(G,M) = \ker(N_G)/I_G M` where $`I_G M` is spanned by $`g \cdot m - m`.
:::

:::definition "herbrand-quotient"
Let $`G` be a *finite cyclic* group and $`M` a $`\mathbb{Z}[G]`-module. By the periodicity of
Tate cohomology for cyclic groups, $`\widehat{H}^n(G,M) \cong \widehat{H}^{n+2}(G,M)` for all
$`n`. The *Herbrand quotient* of $`M` is
$$`h(G,M) = \frac{|\widehat{H}^0(G,M)|}{|\widehat{H}^{-1}(G,M)|} = \frac{|M^G / N_G M|}{|\ker(N_G)/I_G M|},`
with the convention $`h(G,M) = 0` if either group is infinite. For the trivial $`G`-module
$`\mathbb{Z}`, $`h(G, \mathbb{Z}) = |G|`.
:::

:::theorem "herbrand-local-units"
Let $`l/k` be a cyclic extension of local fields ({uses "local-field"}[]) with
$`G = \mathrm{Gal}(l/k)` ({uses "is-galois"}[]). Then:
$$`h(G, \mathcal{O}_l^\times) = 1 \quad\text{and}\quad h(G, l^\times) = [l:k].`
Here $`\mathcal{O}_l^\times` denotes the unit group of the ring of integers of $`l`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory) (sorry-free).
:::

:::proof "herbrand-local-units"
For $`h(G, \mathcal{O}_l^\times) = 1`: filter $`\mathcal{O}_l^\times \supset 1 + \pi_k\mathcal{O}_l \supset \cdots` by powers of a uniformiser. The successive
subquotients are isomorphic (as $`G`-modules) to $`\mathbb{F}_l^\times` and to additive copies
of $`\mathbb{F}_l`, both of which have trivial Tate cohomology by a Serre approximation argument
(normal basis theorem for $`l \cong k[G]`). Since $`\mathcal{O}_l^\times / M` is finite for the
good open subgroup $`M` of the approximation, the Herbrand multiplicativity for short exact
sequences ({uses "herbrand-quotient"}[]) gives $`h(\mathcal{O}_l^\times) = h(M) = 1`.

For $`h(G, l^\times) = [l:k]`: split $`l^\times \cong \mathcal{O}_l^\times \oplus \mathbb{Z}` via the
valuation, so $`h(l^\times) = h(\mathcal{O}_l^\times) \cdot h(\mathbb{Z}) = 1 \cdot [l:k] = [l:k]`.
:::

:::theorem "local-reciprocity"
*(Local reciprocity / local class field theory.)* For every finite Galois extension $`l/k` of
local fields ({uses "local-field"}[]) there is a canonical isomorphism
$$`\mathrm{rec}_{l/k} : k^\times / N_{l/k}(l^\times) \xrightarrow{\;\sim\;} \mathrm{Gal}(l/k)^{\mathrm{ab}}`
called the *local reciprocity map*, where $`N_{l/k}` is the norm.
In the unramified case, $`\mathrm{rec}_{l/k}` maps a uniformiser $`\pi_k` to the arithmetic
Frobenius generator ({uses "arith-frob-at"}[]) of $`\mathrm{Gal}(l/k)`.
For a finite abelian extension, $`l_1 \subseteq l_2` iff
$`N_{l_1/k}(l_1^\times) \supseteq N_{l_2/k}(l_2^\times)`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory) (in progress).
:::

:::proof "local-reciprocity"
The key input is that $`(G, l^\times)` is a *finite class formation*: Hilbert 90 gives
$`\widehat{H}^{-1}(G, l^\times) = H^1(G, l^\times) = 0`, and the Herbrand computation
({uses "herbrand-local-units"}[]) combined with inflation-restriction yields
$`H^2(G, l^\times) \cong \mathbb{Z}/[l:k]\mathbb{Z}`. A generator $`\sigma_{l/k} \in H^2(G, l^\times)` of
order $`[l:k]` — the *fundamental class* — is constructed by lifting from the unramified case
(where it is explicit in terms of the Frobenius) to the general case via inflation and the
vanishing $`\mathrm{inv}_{m/l}(\psi) = 0`. By Tate's theorem ({uses "tate-cohomology"}[]), this
fundamental class produces the reciprocity isomorphism $`k^\times/N(l^\times) \cong G^{\mathrm{ab}}`.
The norm-subgroup ordering characterisation follows from functoriality of the construction.
:::

:::theorem "local-kronecker-weber"
*(Local Kronecker–Weber.)* Every finite abelian extension $`l/\mathbb{Q}_p` ({uses "is-galois"}[])
is isomorphic (over $`\mathbb{Q}_p`) to a subfield of a cyclotomic extension $`\mathbb{Q}_p(\zeta_n)`
({uses "cyclotomic-extension"}[]) for some $`n`.
Formalised in [`ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory) (in progress).
:::

:::proof "local-kronecker-weber"
By the local reciprocity map ({uses "local-reciprocity"}[]), $`N(l^\times)` is an open subgroup
of $`\mathbb{Q}_p^\times`, so it contains a subgroup of the form $`1 + p^n \mathbb{Z}_p`. A direct
computation using the exponential map shows that every element of $`p^\mathbb{Z} \times (1 + p^n\mathbb{Z}_p)`
is a norm from $`\mathbb{Q}_p(\zeta_{p^n})`. Therefore
$`N(l^\times) \supseteq N(\mathbb{Q}_p(\zeta_{p^f-1})^\times) \cap N(\mathbb{Q}_p(\zeta_{p^n})^\times)`,
and the norm-subgroup ordering ({uses "local-reciprocity"}[]) forces $`l` into
$`\mathbb{Q}_p(\zeta_{p^f-1}, \zeta_{p^n})`.
:::

## Power residue symbols (power_residue_symbols)

The `power_residue_symbols` project (Birkbeck) formalises power residue symbols for number
fields. The main construction is sorry-free; a full reciprocity statement for power residue
symbols is in progress.

:::definition "power-residue-symbol"
Let $`F` be a number field, $`\zeta_n` a primitive $`n`-th root of unity in $`\mathcal{O}_F`,
and $`\mathfrak{p}` a prime ideal of $`\mathcal{O}_F` coprime to $`n`. For an element
$`\alpha \in \mathcal{O}_F` not divisible by $`\mathfrak{p}`, the *$`n`-th power residue symbol*
at $`\mathfrak{p}` is the unique $`n`-th root of unity $`\zeta_n^k` satisfying
$$`\left(\frac{\alpha}{\mathfrak{p}}\right)_n \equiv \alpha^{(N\mathfrak{p}-1)/n} \pmod{\mathfrak{p}},`
where $`N\mathfrak{p} = |\mathcal{O}_F/\mathfrak{p}|` ({uses "inertia-degree"}[]) is the absolute
norm of $`\mathfrak{p}`. The symbol generalises the Legendre and Jacobi symbols; it depends
on the Frobenius endomorphism at $`\mathfrak{p}` ({uses "frobenius-endomorphism"}[]).
Formalised in [`power_residue_symbols`](https://github.com/CBirkbeck/power_residue_symbols) (sorry-free).
:::

:::theorem "power-residue-reciprocity"
*(Power residue reciprocity, abelian form.)* Let $`F = \mathbb{Q}(\zeta_n)` be the $`n`-th
cyclotomic field ({uses "cyclotomic-extension"}[]) and let $`\mathfrak{p}, \mathfrak{q}` be
distinct primes of $`\mathcal{O}_F` coprime to $`n`. If $`\alpha \in \mathcal{O}_F` and
$`\beta \in \mathcal{O}_F` are coprime to each other and to $`n`, then the $`n`-th power residue
symbol ({uses "power-residue-symbol"}[]) satisfies a *reciprocity law* of the form
$$`\left(\frac{\alpha}{\mathfrak{p}}\right)_n \big/ \left(\frac{\alpha}{\mathfrak{q}}\right)_n`
controlled by a local factor at the archimedean and $`n`-adic places, analogous to the Legendre
symbol's quadratic reciprocity.
Formalised in [`power_residue_symbols`](https://github.com/CBirkbeck/power_residue_symbols) (in progress).
:::

:::proof "power-residue-reciprocity"
In the cyclotomic field $`\mathbb{Q}(\zeta_n)`, the Artin map of global class field theory
(specialised via {uses "local-reciprocity"}[]) identifies each power residue symbol
$`(\alpha/\mathfrak{p})_n` with the image of $`\alpha` under the Frobenius automorphism at
$`\mathfrak{p}` ({uses "arith-frob-at"}[], {uses "frobenius-endomorphism"}[]). Reciprocity
then follows from the global product formula for the Artin symbol: the product over all places
of the local Artin symbols of $`\alpha` for the extension $`\mathbb{Q}(\zeta_n, \alpha^{1/n})/\mathbb{Q}(\zeta_n)` is trivial, and each local factor coincides with the appropriate power residue symbol.
:::

# Forthcoming in mathlib

The node below is an *informal* statement of a result that is the subject of an open mathlib
pull request (the `t-number-theory` queue, as of June 2026). It carries a `pr_url` pointing at
the live PR and **no** `(lean := …)` reference: the declaration is not yet in mathlib
v4.30.0-rc2. It connects into the dependency graph through the Mathlib-backed Galois and inertia
nodes of this chapter via `{uses}` edges, and should be re-pointed to `(lean := …)` once the
PR merges.

:::theorem "galois-generated-by-inertia" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/33992")
*(The Galois group is generated by inertia.)* Let $`L/K` be a finite Galois extension of number
fields ({uses "is-galois"}[]) with group $`G = \mathrm{Gal}(L/K)`, and suppose $`K = \mathbb{Q}`
(or, more generally, that $`K` has no unramified extensions inside $`L`). Then $`G` is generated
by the inertia subgroups $`I(\mathfrak{P})` ({uses "inertia-group"}[]) attached to the primes
$`\mathfrak{P}` of $`L` that ramify over $`K`:
$$`G \;=\; \bigl\langle\, I(\mathfrak{P}) \;:\; \mathfrak{P} \text{ ramified in } L/\mathbb{Q} \,\bigr\rangle.`
Equivalently, the maximal subextension of $`L/\mathbb{Q}` unramified at every finite prime is
$`\mathbb{Q}` itself — Minkowski's theorem that $`\mathbb{Q}` admits no nontrivial everywhere-unramified
extension.

The PR establishes that the inertia subgroups generate $`G`, the group-theoretic counterpart of
the absence of unramified extensions of $`\mathbb{Q}`; the subgroup generated by all inertia
groups fixes precisely the maximal unramified subextension.
In review — [mathlib PR #33992](https://github.com/leanprover-community/mathlib4/pull/33992).
:::
