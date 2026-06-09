import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Algebraic Number Theory" =>

This chapter covers number fields and their rings of integers, ideal factorisation in Dedekind domains, the class group and its finiteness, the Dirichlet unit theorem, the discriminant, ramification theory, and cyclotomic extensions. Throughout, $`K` denotes a number field, $`\mathcal{O}_K` its ring of integers, $`\mathrm{Cl}(K)` its class group, and $`\mathfrak{p}` a prime ideal.

# Number fields and their rings of integers

:::definition "number-field" (lean := "NumberField")
A *number field* is a field $`K` that is finite-dimensional over $`\mathbb{Q}`. Equivalently, $`K` is a finite algebraic extension of $`\mathbb{Q}`, and its degree $`[K : \mathbb{Q}]` is a positive integer.
:::

:::definition "ring-of-integers" (lean := "NumberField.RingOfIntegers")
The *ring of integers* $`\mathcal{O}_K` of a number field $`K` ({uses "number-field"}[]) is the integral closure of $`\mathbb{Z}` in $`K`: the subring of all elements of $`K` that satisfy a monic polynomial equation with integer coefficients. As a $`\mathbb{Z}`-module, $`\mathcal{O}_K` is free of rank $`[K : \mathbb{Q}]`.
:::

# Dedekind domains and unique factorisation of ideals

:::definition "dedekind-domain" (lean := "IsDedekindDomain")
A *Dedekind domain* is a Noetherian integrally closed integral domain in which every nonzero prime ideal is maximal. Equivalently, a Dedekind domain is an integral domain in which every nonzero ideal factors uniquely as a product of prime ideals.
:::

:::theorem "ring-of-integers-is-dedekind" (lean := "IsIntegralClosure.isDedekindDomain")
The ring of integers $`\mathcal{O}_K` of any number field $`K` is a Dedekind domain.
:::

:::proof "ring-of-integers-is-dedekind"
We verify the three defining properties of a Dedekind domain ({uses "dedekind-domain"}[]). By general integral closure theory, $`\mathcal{O}_K = \overline{\mathbb{Z}}^K` is integrally closed. The extension $`K/\mathbb{Q}` is finite and separable (as $`\mathrm{char}\,\mathbb{Q} = 0`), so $`\mathcal{O}_K` is a finite $`\mathbb{Z}`-module ({uses "ring-of-integers"}[]); in particular it is Noetherian. Every nonzero prime ideal of $`\mathcal{O}_K` is maximal because $`\mathcal{O}_K / \mathfrak{p}` is a finite integral domain, hence a field.
:::

:::theorem "ideal-unique-factorization" (lean := "Ideal.uniqueFactorizationMonoid")
In the ring of integers $`\mathcal{O}_K` of a number field — more generally, in any Dedekind domain $`R` — the monoid of nonzero ideals is a unique factorisation monoid: every nonzero ideal $`I \subseteq \mathcal{O}_K` factors uniquely as a product of prime ideals,
$$`I = \mathfrak{p}_1^{e_1} \cdots \mathfrak{p}_r^{e_r},`
with the $`\mathfrak{p}_i` distinct prime ideals and $`e_i \ge 1`.
:::

:::proof "ideal-unique-factorization"
This is the ideal-theoretic generalisation of the fundamental theorem of arithmetic ({uses "fta-existence"}[]): in $`\mathbb{Z}` prime factorisation of *elements* recovers unique factorisation, while in a general Dedekind domain — where elements need not factor uniquely — the correct objects are *ideals*. Existence of a prime factorisation follows from the ascending chain condition (Noetherian) together with the fact that every maximal ideal is prime and every proper ideal is contained in a maximal one. Uniqueness follows from the cancellation law for fractional ideals, which holds in any Dedekind domain because the group of fractional ideals is free abelian on the set of nonzero prime ideals ({uses "dedekind-domain"}[]).
:::

# The class group and its finiteness

:::definition "class-group" (lean := "ClassGroup")
The *class group* $`\mathrm{Cl}(K)` of a Dedekind domain $`R` ({uses "dedekind-domain"}[]) (e.g. $`R = \mathcal{O}_K`) is the quotient of the group of invertible fractional ideals by its subgroup of principal fractional ideals:
$$`\mathrm{Cl}(K) = \{\text{invertible fractional ideals of } \mathcal{O}_K\} \;/\; \{\alpha \mathcal{O}_K : \alpha \in K^\times\}.`
The class group is trivial if and only if $`\mathcal{O}_K` is a principal ideal domain.
:::

:::theorem "class-group-finite" (lean := "NumberField.RingOfIntegers.instFintypeClassGroup")
The class group $`\mathrm{Cl}(K)` of any number field $`K` is finite.
:::

:::proof "class-group-finite"
The proof bounds the number of ideal classes ({uses "class-group"}[]) using Minkowski's geometry-of-numbers bound ({uses "minkowski-bound"}[]): every ideal class contains an ideal of norm at most the Minkowski bound
$$`M_K = \left(\frac{4}{\pi}\right)^{r_2} \frac{n!}{n^n} \sqrt{|\mathrm{disc}(K)|},`
where $`n = [K:\mathbb{Q}]` and $`r_2` is the number of pairs of complex embeddings. Since there are only finitely many ideals of bounded norm in $`\mathcal{O}_K`, the class group is represented by finitely many ideal classes.
:::

# The discriminant

:::definition "discriminant" (lean := "NumberField.discr")
The *discriminant* $`\mathrm{disc}(K)` of a number field $`K` is the integer
$$`\mathrm{disc}(K) = \det\bigl(\mathrm{Tr}_{K/\mathbb{Q}}(\omega_i \omega_j)\bigr)_{1 \le i,j \le n},`
where $`\omega_1, \dots, \omega_n` is any $`\mathbb{Z}`-basis of the ring of integers $`\mathcal{O}_K` ({uses "ring-of-integers"}[]). The discriminant is independent of the choice of basis (up to squares of units), and its absolute value measures the arithmetic complexity of $`K`.
:::

# Minkowski's bound

:::definition "minkowski-bound" (lean := "NumberField.mixedEmbedding.minkowskiBound")
The *Minkowski bound* of a number field $`K` with a fractional ideal $`I` is the volume bound
$$`\mathrm{Mink}(K, I) = \mathrm{vol}\bigl(\mathcal{F}(\Lambda_I)\bigr) \cdot 2^{\dim_{\mathbb{R}} K_{\mathbb{R}}},`
where $`K_{\mathbb{R}}` is the mixed embedding space $`\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}`, $`\Lambda_I` is the lattice associated to $`I`, and $`\mathcal{F}(\Lambda_I)` is a fundamental domain. Any symmetric convex body of volume exceeding this bound contains a nonzero element of $`I`.
:::

# The Dirichlet unit theorem

:::theorem "dirichlet-unit-theorem" (lean := "NumberField.Units.exist_unique_eq_mul_prod")
*(Dirichlet's unit theorem.)* Let $`K` be a number field with $`r_1` real embeddings and $`r_2` pairs of complex embeddings, and let $`r = r_1 + r_2 - 1`. Every unit $`u \in \mathcal{O}_K^\times` can be written uniquely as
$$`u = \zeta \cdot \varepsilon_1^{a_1} \cdots \varepsilon_r^{a_r},`
where $`\zeta` is a root of unity in $`\mathcal{O}_K`, the $`\varepsilon_i` form a fundamental system of units, and $`a_i \in \mathbb{Z}`. Equivalently, $`\mathcal{O}_K^\times \cong \mu(K) \times \mathbb{Z}^r`, where $`\mu(K)` is the (finite cyclic) group of roots of unity in $`K`.
:::

:::proof "dirichlet-unit-theorem"
The *logarithmic embedding* sends a unit $`u` to the vector $`(\log|u|_v)_{v}` indexed by the infinite places $`v` of $`K`, with the multiplicity $`1` for real places and $`2` for complex places. Dirichlet's theorem asserts that the image of $`\mathcal{O}_K^\times` under this map is a full-rank lattice in the trace-zero hyperplane of $`\mathbb{R}^{r_1 + r_2}` (a real vector space of dimension $`r_1 + r_2 - 1 = r`).

The kernel of the logarithmic embedding is the set of units of absolute value $`1` at every infinite place, i.e. the roots of unity in $`\mathcal{O}_K`. That this group is finite follows from {uses "ring-of-integers"}[] (it is a finite set by a norm bound). That the image is a full lattice requires showing it is both discrete (using Minkowski's bound, {uses "minkowski-bound"}[]) and spans all of $`\mathbb{R}^r` (a subtler geometric argument constructing units with prescribed archimedean absolute values). Together these yield the claimed direct product decomposition.
:::

# Ramification and the fundamental identity

:::definition "ramification-index" (lean := "Ideal.ramificationIdx")
Let $`R \subseteq S` be an extension of Dedekind domains and $`\mathfrak{p} \subseteq R` a nonzero prime ideal. For a prime $`\mathfrak{P}` of $`S` lying over $`\mathfrak{p}`, the *ramification index* $`e(\mathfrak{P}|\mathfrak{p})` is the exponent of $`\mathfrak{P}` in the factorisation of $`\mathfrak{p} S`:
$$`\mathfrak{p} S = \mathfrak{P}_1^{e_1} \cdots \mathfrak{P}_g^{e_g}, \quad e_i = e(\mathfrak{P}_i|\mathfrak{p}).`
If $`e(\mathfrak{P}|\mathfrak{p}) > 1`, the prime $`\mathfrak{p}` is said to *ramify* in $`S`.
:::

:::definition "inertia-degree" (lean := "Ideal.inertiaDeg")
With notation as in {uses "ramification-index"}[], the *inertia degree* (or *residue degree*) $`f(\mathfrak{P}|\mathfrak{p})` is the degree of the residue field extension:
$$`f(\mathfrak{P}|\mathfrak{p}) = [\,S/\mathfrak{P} : R/\mathfrak{p}\,].`
:::

:::theorem "fundamental-identity" (lean := "Ideal.sum_ramification_inertia")
*(Fundamental identity of ramification.)* Let $`L/K` be a finite extension of number fields (or, more generally, let $`S/R` be a finite extension of Dedekind domains with fraction fields $`L/K`). For any nonzero prime $`\mathfrak{p}` of $`R`, summing the products of ramification and inertia indices over all primes $`\mathfrak{P}` of $`S` lying over $`\mathfrak{p}` gives
$$`\sum_{\mathfrak{P} \mid \mathfrak{p}} e(\mathfrak{P}|\mathfrak{p})\, f(\mathfrak{P}|\mathfrak{p}) = [L : K].`
:::

:::proof "fundamental-identity"
By unique factorisation of ideals ({uses "ideal-unique-factorization"}[]), $`\mathfrak{p} S` factors as $`\prod_i \mathfrak{P}_i^{e_i}`, where each ramification index $`e_i` is exactly the $`\mathfrak{P}_i`-adic valuation ({uses "valuation"}[]) of $`\mathfrak{p}` — the local measure of how $`\mathfrak{p}` ramifies at $`\mathfrak{P}_i`. The Chinese remainder theorem (for ideals) gives a ring isomorphism
$$`S / \mathfrak{p} S \;\cong\; \prod_i S / \mathfrak{P}_i^{e_i}.`
Each factor $`S/\mathfrak{P}_i^{e_i}` has $`R/\mathfrak{p}`-dimension $`e_i f_i`, as follows from the filtration by powers of $`\mathfrak{P}_i` and the identification of each successive quotient with the residue field $`S/\mathfrak{P}_i`. Summing over $`i` gives $`[S/\mathfrak{p}S : R/\mathfrak{p}] = \sum_i e_i f_i`. Comparing with the $`K`-dimension of $`L` via the flatness of $`L \cong K \otimes_R S` yields $`\sum_i e_i f_i = [L:K]`.
:::

# Cyclotomic extensions

:::definition "cyclotomic-extension" (lean := "IsCyclotomicExtension")
Let $`S` be a set of positive integers and $`A \subseteq B` a ring extension. We say that $`B` is an *$`S`-cyclotomic extension* of $`A` (and write $`\mathrm{IsCyclotomicExtension}(S, A, B)`) if for every nonzero $`n \in S` there exists a primitive $`n`-th root of unity $`\zeta_n \in B`, and $`B` is generated over $`A` by all $`n`-th roots of unity for $`n \in S`. For a single integer $`n`, the *$`n`-th cyclotomic field* over $`\mathbb{Q}` is $`\mathbb{Q}(\zeta_n)`, the splitting field of the cyclotomic polynomial $`\Phi_n`.
:::

:::lemma_ "cyclotomic-finrank" (lean := "IsCyclotomicExtension.finrank")
The cyclotomic field $`\mathbb{Q}(\zeta_n)` has degree $`\varphi(n) = [\mathbb{Q}(\zeta_n):\mathbb{Q}]` over $`\mathbb{Q}`, where $`\varphi` is Euler's totient function.
:::

:::proof "cyclotomic-finrank"
The minimal polynomial of $`\zeta_n` over $`\mathbb{Q}` is the $`n`-th cyclotomic polynomial $`\Phi_n(X)`, whose degree is the value $`\varphi(n)` of Euler's totient ({uses "totient"}[]) — the number of primitive $`n`-th roots of unity. When $`\Phi_n` is irreducible over $`K` — in particular for $`K = \mathbb{Q}` by Gauss's classical argument — the extension $`L = K(\zeta_n)` satisfies $`[L:K] = \deg \Phi_n = \varphi(n)`. The proof uses the power basis generated by a primitive $`n`-th root of unity together with the fact that its minimal polynomial is $`\Phi_n` ({uses "cyclotomic-extension"}[]).
:::
