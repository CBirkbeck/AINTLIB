import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The CM field and the class number splitting" =>

This chapter develops the CM extension $`\mathbb{Q}(\zeta_p)/\mathbb{Q}(\zeta_p)^+`
and proves that the class number of the maximal real subfield divides the full
class number, so that the relative class number $`\hminus` may be defined by
honest division.

# The maximal real subfield

:::definition "def:cm-real-subfield" (lean := "NumberField.maximalRealSubfield")
The *maximal real subfield* of $`\mathbb{Q}(\zeta_p)` is
$$`\mathbb{Q}(\zeta_p)^+ \;=\; \mathbb{Q}(\zeta_p + \zeta_p^{-1}),`
the fixed field of complex conjugation. It is a totally real subfield of
$`\mathbb{Q}(\zeta_p)` of degree $`(p-1)/2` over $`\mathbb{Q}`, and
$`\mathbb{Q}(\zeta_p)` is a CM field over $`\mathbb{Q}(\zeta_p)^+`.
:::

The class-number splitting begins by separating the class number of the full
cyclotomic field from that of its maximal real subfield.

# The class numbers h, h-plus, and h-minus

:::definition "def:class-number-h" (lean := "BernoulliRegular.h")
The class number of $`\mathbb{Q}(\zeta_p)` is
$$`h(\mathbb{Q}(\zeta_p)) \;:=\; \bigl|\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)})\bigr|.`
:::

:::definition "def:class-number-hplus" (lean := "BernoulliRegular.hPlus")
The *plus class number* is the class number of the maximal real subfield:
$$`\hplus \;:=\; \bigl|\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)^+})\bigr|.`
:::

The crucial foundational fact is that $`\hplus` divides $`h(\mathbb{Q}(\zeta_p))`.
Only after this has been proved can one define the relative class number by honest
division. The proof, occupying the rest of this chapter, follows Diekmann's
Proposition 55 (Washington's Theorem 4.14). The strategy is to show that the
natural extension-of-ideals map
$$`\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}) \longrightarrow \mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)})`
is injective; divisibility of the orders then follows from the fact that an
injective homomorphism of finite groups has image of order dividing the codomain.

# The class-group map and faithful-flat descent

There is a natural extension-of-ideals map
$$`\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}) \longrightarrow \mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)}), \qquad [I] \longmapsto [I\,\mathcal{O}_{\mathbb{Q}(\zeta_p)}].`
Throughout this chapter we abbreviate $`\mathcal{O} := \mathcal{O}_{\mathbb{Q}(\zeta_p)}`
and $`\mathcal{O}^+ := \mathcal{O}_{\mathbb{Q}(\zeta_p)^+}`.

The proof that $`\hplus \mid h(\mathbb{Q}(\zeta_p))` reduces, by
injectivity-implies-divisibility on finite groups, to the statement that an ideal
$`I` of $`\mathcal{O}^+` whose extension $`I \mathcal{O}` is principal is itself
principal. The basic descent input is that the ring extension
$`\mathcal{O}^+ \subseteq \mathcal{O}` is well-behaved.

:::theorem "thm:ring-of-integers-faithfully-flat" (lean := "BernoulliRegular.ringOfIntegers_faithfullyFlat_maximalRealSubfield")
The ring of integers $`\mathcal{O}_{\mathbb{Q}(\zeta_p)}` is faithfully flat over
$`\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}`.

{uses "def:cm-real-subfield"}[]
:::

:::proof "thm:ring-of-integers-faithfully-flat"
Flatness is automatic: $`\mathcal{O}` is finitely generated and projective as a
$`\mathcal{O}^+`-module, because $`\mathbb{Q}(\zeta_p) / \mathbb{Q}(\zeta_p)^+` is a
finite separable extension and the rings of integers form a tower of Dedekind
domains. To upgrade flatness to faithful flatness it suffices, by the
prime-spectrum criterion, to show that the comap
$`\operatorname{Spec} \mathcal{O} \to \operatorname{Spec} \mathcal{O}^+` is
surjective. Given a prime $`\mathfrak{q} \subseteq \mathcal{O}^+`, choose any prime
$`\mathfrak{Q}` of $`\mathcal{O}` lying over $`\mathfrak{q}` (such a prime exists by
integrality of $`\mathcal{O}` over $`\mathcal{O}^+`); then $`\mathfrak{Q}` maps to
$`\mathfrak{q}` under the comap.
:::

Faithful flatness gives the standard extension-contraction identity.

:::theorem "thm:map-comap-ring-of-integers" (lean := "BernoulliRegular.map_comap_eq_ringOfIntegers")
For every ideal $`J \subseteq \mathcal{O}_{\mathbb{Q}(\zeta_p)^+}` one has
$$`(J\mathcal{O}_{\mathbb{Q}(\zeta_p)}) \cap \mathcal{O}_{\mathbb{Q}(\zeta_p)^+} = J.`

{uses "thm:ring-of-integers-faithfully-flat"}[]
:::

:::proof "thm:map-comap-ring-of-integers"
Faithful flatness of $`\mathcal{O}` over $`\mathcal{O}^+` is equivalent to the
statement that the canonical map $`J \to J \mathcal{O}` is injective for every ideal
$`J` of $`\mathcal{O}^+`, and more strongly that contracting an extended ideal
recovers the original. Concretely, $`J \mathcal{O} \cap \mathcal{O}^+ \subseteq J`
holds for any faithfully flat extension by the standard descent fact; the reverse
inclusion is automatic.
:::

Consequently, principality of an extended ideal descends as soon as one can exhibit
a generator that already lives in the smaller ring of integers.

:::theorem "thm:is-principal-map-span-singleton" (lean := "BernoulliRegular.isPrincipal_of_map_eq_span_singleton_of_mem")
Let $`I` be an ideal of $`\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}`. If
$`I\mathcal{O}_{\mathbb{Q}(\zeta_p)} = (b)` for some element $`b` lying in the image
of $`\mathcal{O}_{\mathbb{Q}(\zeta_p)^+} \hookrightarrow \mathcal{O}_{\mathbb{Q}(\zeta_p)}`,
say $`b = \iota(b_0)` with $`b_0 \in \mathcal{O}^+`, then $`I = (b_0)`; in particular
$`I` is principal.

{uses "thm:map-comap-ring-of-integers"}[]
:::

:::proof "thm:is-principal-map-span-singleton"
Write $`\iota : \mathcal{O}^+ \hookrightarrow \mathcal{O}` for the inclusion. We use
{bpref "thm:map-comap-ring-of-integers"}[] twice. First, applied to $`I`,
$$`I = \iota^{-1}(I \mathcal{O}) = \iota^{-1}((b)) = \iota^{-1}((\iota(b_0))).`
Second, applied to the principal ideal $`(b_0) \subseteq \mathcal{O}^+`,
$$`\iota^{-1}((\iota(b_0))) = \iota^{-1}((b_0) \mathcal{O}) = (b_0).`
Combining the two displays gives $`I = (b_0)`.
:::

The remaining work is therefore to start from an arbitrary generator $`a` of
$`I \mathcal{O}` upstairs and replace it by an associate fixed by complex
conjugation; that associate will then lie in $`\mathcal{O}^+`.

# Conjugation on principal generators

Let $`I` be an ideal of $`\mathcal{O}^+` such that $`I \mathcal{O} = (a)` for some
$`a \in \mathcal{O}`, and write $`\overline{\,\cdot\,}` for the action of complex
conjugation on $`\mathcal{O}`. Because $`I` comes from the real subfield, the
extended ideal $`I \mathcal{O}` is fixed by conjugation.

:::theorem "thm:ideal-map-conj" (lean := "BernoulliRegular.ideal_map_conj_eq")
If $`I` is an ideal of $`\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}`, then the extended
ideal $`I\mathcal{O}_{\mathbb{Q}(\zeta_p)}` is fixed by complex conjugation.

{uses "def:cm-real-subfield"}[]
:::

:::proof "thm:ideal-map-conj"
Conjugation fixes every element of $`\mathcal{O}^+` by definition of the maximal
real subfield, so it commutes with the algebra map
$`\mathcal{O}^+ \hookrightarrow \mathcal{O}`. Functoriality of ideal extension gives
$$`\overline{I \mathcal{O}} = \overline{(\iota I)} = \iota I = I \mathcal{O},`
where $`\iota` denotes the inclusion.
:::

Hence $`a` and $`\overline a` generate the same principal ideal, so they differ by
a unit.

:::theorem "thm:conj-generator-associated" (lean := "BernoulliRegular.conj_generator_associated")
There exists a unit $`u \in \mathcal{O}_{\mathbb{Q}(\zeta_p)}^\times` such that
$$`\overline a = u\,a.`

{uses "thm:ideal-map-conj"}[]
:::

:::proof "thm:conj-generator-associated"
From $`I \mathcal{O} = (a)` and $`\overline{I \mathcal{O}} = I \mathcal{O}` we have
$`(a) = \overline{(a)} = (\overline a)` in $`\mathcal{O}`. Two generators of the same
nonzero principal ideal in an integral domain are associates, so
$`\overline a = u a` for some $`u \in \mathcal{O}^\times`.
:::

Applying conjugation a second time recovers $`a`, which forces the unit $`u` to be
antisymmetric under conjugation.

:::theorem "thm:conj-unit-mul-one" (lean := "BernoulliRegular.conj_unit_mul_eq_one")
The unit $`u` satisfies $`u\,\overline u = 1`.

{uses "thm:conj-generator-associated"}[]
:::

:::proof "thm:conj-unit-mul-one"
Apply conjugation to $`\overline a = u a` and use $`\overline{\overline a} = a`:
$$`a = \overline{\overline a} = \overline u \cdot \overline a = \overline u \cdot u\,a.`
Cancelling $`a \ne 0` in the domain $`\mathcal{O}` gives $`\overline u \, u = 1`.
:::

The next ingredient is the classification of antisymmetric units in a cyclotomic
field, sometimes called the Kronecker–Kummer lemma. We use $`\zeta` for $`\zeta_p`
and $`\langle \zeta \rangle` for the cyclic group of $`p`-th roots of unity.

:::theorem "thm:antisymmetric-unit-classification" (lean := "BernoulliRegular.antisymmetric_unit_eq_neg_one_pow_mul_zeta_pow")
If $`u \in \mathcal{O}_{\mathbb{Q}(\zeta_p)}^\times` satisfies $`u\overline u = 1`,
then there exist integers $`k,n` such that $`u = (-1)^k \zeta_p^n`.

{uses "thm:conj-unit-mul-one"}[]
:::

:::proof "thm:antisymmetric-unit-classification"
Let $`\sigma : K \hookrightarrow \mathbb{C}` be any embedding. Since complex
conjugation on $`K` commutes with every embedding, the relation $`u\overline u = 1`
implies $`|\sigma(u)|^2 = \sigma(u)\overline{\sigma(u)} = 1`. Thus every Galois
conjugate of $`u` has complex absolute value $`1`. Kronecker's theorem therefore
shows that $`u` is a root of unity. The roots of unity in $`\mathbb{Q}(\zeta_p)` are
exactly the elements $`\{\pm \zeta_p^n : 0 \le n \le p-1\}`, because $`p` is odd.
Hence there exist integers $`k,n` such that $`u = (-1)^k \zeta_p^n`.
:::

# A conjugation-fixed associate and descent to the real ring of integers

The classification of the unit $`u` is used to modify the generator $`a` by an
associate so that the new generator is fixed by conjugation. The serious content is
to eliminate the possibility $`k` odd; once this is done, $`n` can be replaced by an
even integer because $`p` is odd, and a $`p`-th root of unity adjustment produces
the fixed associate.

## Eliminating the minus-one factor

Write $`\zeta = \zeta_p` and $`\pi := \zeta - 1 \in \mathcal{O}`. Let $`P = (\pi)` be
the unique prime of $`\mathcal{O}` above $`p`, and $`P^+ \subseteq \mathcal{O}^+` the
prime below it. The extension $`\mathcal{O}^+ \subseteq \mathcal{O}` ramifies totally
at $`P^+` with $`e(P / P^+) = 2`, that is, $`P^+ \mathcal{O} = P^2`.

:::theorem "thm:ramificationIdx-zetaPrimePlus" (lean := "BernoulliRegular.ramificationIdx_zetaPrimePlus_eq_two")
**Ramification at $`\pi`.** The ramification index of $`P^+` in $`\mathcal{O}`
equals $`2`: $`P^+ \mathcal{O} = P^2`.

{uses "def:cm-real-subfield"}[]
:::

:::proof "thm:ramificationIdx-zetaPrimePlus"
Inside $`\mathcal{O}` one has the identity $`P^+ \mathcal{O} = P^2` by an explicit
computation with $`\zeta + \zeta^{-1} - 2 = -\pi \overline\pi \zeta^{-1}`, exhibiting
the totally ramified extension at the unique prime above $`p` in the maximal real
subfield.
:::

:::lemma_ "thm:multiplicity-zetaPrime-even" (lean := "BernoulliRegular.multiplicity_zetaPrime_even_of_map_eq_span")
**Even multiplicity of $`\pi` in a descended generator.** If $`I` is a nonzero
ideal of $`\mathcal{O}^+` with $`I \mathcal{O} = (a)` and $`a \ne 0`, then
$`v_\pi(a)` is even.

{uses "thm:ramificationIdx-zetaPrimePlus"}[]
:::

:::proof "thm:multiplicity-zetaPrime-even"
Let $`e = v_\pi(a)`, equivalently the multiplicity with which $`P = (\pi)` appears in
the prime factorisation of $`(a) = I \mathcal{O}` in $`\mathcal{O}`. For Dedekind
extensions one has $`v_P(I \mathcal{O}) = e(P/P^+) \cdot v_{P^+}(I)`, and the
ramification index $`e(P / P^+) = 2` by
{bpref "thm:ramificationIdx-zetaPrimePlus"}[]. Therefore
$`v_\pi(a) = 2 \cdot v_{P^+}(I)` is even.
:::

The classification {bpref "thm:antisymmetric-unit-classification"}[] is now refined
to remove the possible $`-1`.

:::theorem "thm:generator-unit-eq-zeta-pow" (lean := "BernoulliRegular.generator_unit_eq_zeta_pow")
**Pure $`\zeta`-power form of the unit.** With $`I, a, u` as above and writing
$`u = (-1)^k \zeta^n`, the integer $`k` is necessarily even, so there exists $`n`
with $`u = \zeta^n`.

{uses "thm:antisymmetric-unit-classification"}[] {uses "thm:multiplicity-zetaPrime-even"}[]
:::

:::proof "thm:generator-unit-eq-zeta-pow"
Suppose for contradiction that $`k` is odd, so $`u = -\zeta^n`. Let $`e = v_\pi(a)`
and write $`a = \pi^e b` with $`\pi \nmid b` ({bpref "thm:multiplicity-zetaPrime-even"}[]
applies and $`e` is even). Conjugation sends $`\pi` to $`\overline\pi = \gamma \cdot \pi`,
where the explicit unit $`\gamma` can be computed as $`\gamma = -\zeta^{p-1}` from
$`\overline\zeta = \zeta^{p-1}`. Substituting into $`\overline a = u a` and cancelling
$`\pi^e` — using that $`\pi` is prime and that
$`\gamma^e \cdot \zeta^e = ((-1) \zeta)^e \cdot \zeta^{(p-1)e - e}` simplifies using
$`e` even — yields $`\overline b = u' \cdot b` where
$`u' := \zeta^e \cdot u = -\zeta^{e+n}`. Reducing modulo the prime $`P = (\pi)` kills
$`\pi` and any factor of the form $`\zeta^m - 1`, so $`\zeta^{e+n} \equiv 1 \pmod P`
and therefore $`u' + 1 \equiv 0 \pmod P`. On the other hand
$`\overline b \equiv b \pmod P` since conjugation is trivial modulo $`\pi`, so
$`b (u' - 1) \equiv 0 \pmod P`. Since $`b \notin P`, this forces $`u' - 1 \in P`.
Combining $`u' + 1 \in P` and $`u' - 1 \in P` gives $`2 \in P`, which contradicts $`p`
odd (the prime $`P` lies above $`p`, not $`2`). Therefore $`k` must be even, and
$`(-1)^k = 1`.
:::

## Constructing the conjugation-fixed associate

:::theorem "thm:conj-fixed-associate" (lean := "BernoulliRegular.exists_conj_fixed_associate_of_classification")
There exists $`b \in \mathcal{O}_{\mathbb{Q}(\zeta_p)}` such that $`(b) = (a)` and
$`\overline b = b`.

{uses "thm:generator-unit-eq-zeta-pow"}[]
:::

:::proof "thm:conj-fixed-associate"
By {bpref "thm:generator-unit-eq-zeta-pow"}[] write $`u = \zeta^n`. Since $`p` is
odd, $`2` is invertible modulo $`p`, and the map $`m \mapsto 2m` is a bijection on
$`\mathbb{Z}/p\mathbb{Z}`. Choose $`m` with $`n \equiv 2m \pmod p`, so
$`\zeta^n = (\zeta^m)^2`. Set $`b := a \cdot \zeta^m`. Then $`(b) = (a)` because
$`\zeta^m \in \mathcal{O}^\times`, and using $`\overline{\zeta^m} = \zeta^{-m}`
together with $`\overline a = \zeta^n a = \zeta^{2m} a`,
$$`\overline b = \overline a \cdot \zeta^{-m} = \zeta^{2m} a \cdot \zeta^{-m} = a \cdot \zeta^m = b.`
:::

An algebraic integer of $`\mathcal{O}` fixed by complex conjugation lies in the image
of $`\mathcal{O}^+`.

:::theorem "thm:mem-ring-of-integers-conj-self" (lean := "BernoulliRegular.mem_ringOfIntegers_of_conj_eq_self")
If $`b \in \mathcal{O}_{\mathbb{Q}(\zeta_p)}` satisfies $`\overline b = b`, then $`b`
lies in the image of $`\mathcal{O}_{\mathbb{Q}(\zeta_p)^+} \hookrightarrow \mathcal{O}_{\mathbb{Q}(\zeta_p)}`.

{uses "thm:conj-fixed-associate"}[]
:::

:::proof "thm:mem-ring-of-integers-conj-self"
The maximal real subfield is by definition the fixed field of complex conjugation:
$`\mathbb{Q}(\zeta_p)^+ = \mathbb{Q}(\zeta_p)^{\overline{\,\cdot\,}}`. An element of
$`\mathcal{O} \subseteq \mathbb{Q}(\zeta_p)` fixed by $`\overline{\,\cdot\,}`
therefore lies in $`\mathbb{Q}(\zeta_p)^+`, and being an algebraic integer it lies in
$`\mathcal{O}^+`.
:::

Combining this with faithful-flat descent gives principality downstairs.

:::theorem "thm:is-principal-after-extension" (lean := "BernoulliRegular.isPrincipal_of_isPrincipal_map_Kplus")
**Diekmann Proposition 55 / Washington 4.14.** Let $`I` be an ideal of
$`\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}`. If the extended ideal
$`I\mathcal{O}_{\mathbb{Q}(\zeta_p)}` is principal, then $`I` itself is principal.

{uses "thm:is-principal-map-span-singleton"}[] {uses "thm:mem-ring-of-integers-conj-self"}[] {uses "thm:conj-fixed-associate"}[]
:::

:::proof "thm:is-principal-after-extension"
Write $`I \mathcal{O} = (a)`. We may assume $`a \ne 0`, since the case $`I = 0` is
trivial. By {bpref "thm:ideal-map-conj"}[] the ideal $`I \mathcal{O}` is
conjugation-fixed, so by {bpref "thm:conj-generator-associated"}[] there is a unit
$`u` with $`\overline a = u a`, and by {bpref "thm:conj-unit-mul-one"}[] this unit
satisfies $`u \overline u = 1`. The classification of antisymmetric units
({bpref "thm:antisymmetric-unit-classification"}[]) gives $`u = (-1)^k \zeta^n`, and
{bpref "thm:generator-unit-eq-zeta-pow"}[] eliminates the $`-1`, so $`u = \zeta^n`
for some $`n`. {bpref "thm:conj-fixed-associate"}[] produces
$`b \in \mathcal{O}` with $`(b) = (a)` and $`\overline b = b`, and
{bpref "thm:mem-ring-of-integers-conj-self"}[] gives $`b = \iota(b_0)` for some
$`b_0 \in \mathcal{O}^+`. We then have $`I \mathcal{O} = (b) = (\iota b_0)`, so
{bpref "thm:is-principal-map-span-singleton"}[] concludes that $`I = (b_0)` is
principal.
:::

# Injectivity of the class-group map and the definition of h-minus

The descent theorem immediately gives injectivity on class groups.

:::theorem "thm:class-group-map-injective" (lean := "BernoulliRegular.classGroupMap_injective")
The extension map
$$`\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}) \longrightarrow \mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)})`
is injective.

{uses "thm:is-principal-after-extension"}[]
:::

:::proof "thm:class-group-map-injective"
A homomorphism of groups is injective iff its kernel is trivial. An element
$`[I] \in \mathrm{Cl}(\mathcal{O}^+)` goes to the identity in
$`\mathrm{Cl}(\mathcal{O})` exactly when $`I \mathcal{O}` is principal in
$`\mathcal{O}`. {bpref "thm:is-principal-after-extension"}[] says that this forces
$`I` itself to be principal, i.e. $`[I] = 1` in $`\mathrm{Cl}(\mathcal{O}^+)`. Thus
the kernel is trivial.
:::

Since both class groups are finite, injectivity implies divisibility of their
cardinalities.

:::theorem "thm:hplus-divides-h" (lean := "BernoulliRegular.hPlus_dvd_h")
**$`\hplus` divides $`h(\mathbb{Q}(\zeta_p))`.** The class number $`\hplus` of
$`\mathbb{Q}(\zeta_p)^+` divides the class number $`h(\mathbb{Q}(\zeta_p))` of
$`\mathbb{Q}(\zeta_p)`.

{uses "thm:class-group-map-injective"}[] {uses "def:class-number-h"}[] {uses "def:class-number-hplus"}[]
:::

:::proof "thm:hplus-divides-h"
By {bpref "thm:class-group-map-injective"}[] the extension map
$`\mathrm{Cl}(\mathcal{O}^+) \to \mathrm{Cl}(\mathcal{O})` is an injective
homomorphism of finite groups. Its image is a subgroup of $`\mathrm{Cl}(\mathcal{O})`
of order $`\hplus`, and by Lagrange's theorem the order of any subgroup of a finite
group divides the order of the ambient group.
:::

This justifies the definition of the relative class number.

:::definition "def:class-number-hminus" (lean := "BernoulliRegular.hMinus")
The *relative class number* is defined by
$$`\hminus \;:=\; h(\mathbb{Q}(\zeta_p)) / \hplus.`

{uses "thm:hplus-divides-h"}[]
:::

We shall also use the factorisation and positivity statements below.

:::theorem "thm:h-factorisation" (lean := "BernoulliRegular.h_eq_hPlus_mul_hMinus")
One has $`h(\mathbb{Q}(\zeta_p)) = \hplus\,\hminus`.

{uses "def:class-number-hminus"}[] {uses "thm:hplus-divides-h"}[]
:::

:::proof "thm:h-factorisation"
Immediate from {bpref "def:class-number-hminus"}[] and
{bpref "thm:hplus-divides-h"}[]: dividing $`h(\mathbb{Q}(\zeta_p))` by the divisor
$`\hplus` yields $`\hminus`, and multiplying back recovers $`h(\mathbb{Q}(\zeta_p))`.
:::

:::theorem "thm:hminus-positive" (lean := "BernoulliRegular.hMinus_pos")
The relative class number $`\hminus` is strictly positive.

{uses "def:class-number-hminus"}[] {uses "thm:hplus-divides-h"}[]
:::

:::proof "thm:hminus-positive"
Both $`h(\mathbb{Q}(\zeta_p))` and $`\hplus` are positive integers (cardinalities of
nonempty finite groups), and $`\hplus \mid h(\mathbb{Q}(\zeta_p))`, so the quotient
$`h(\mathbb{Q}(\zeta_p)) / \hplus` is a positive integer.
:::
