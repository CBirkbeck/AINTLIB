import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Combinatorics.Additive.FreimanHom
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Additive.VerySmallDoubling

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Additive and Combinatorial Number Theory" =>

This chapter covers additive combinatorics as it is formalised in mathlib: the basic
arithmetic of sumsets and the doubling constant, the Cauchy–Davenport bound on sumsets in
$`\mathbb{Z}/p\mathbb{Z}`, the Erdős–Ginzburg–Ziv theorem on zero-sum subsequences, the
Plünnecke–Ruzsa inequalities together with the Ruzsa triangle and covering lemmas, Freiman
homomorphisms, and the structure theorems for sets of very small doubling. Throughout, $`A`,
$`B`, $`C` denote finite subsets of a group $`G` (written multiplicatively in the general
statements, additively where the result requires commutativity), $`|A|` denotes cardinality,
and $`A \cdot B = \{ab : a \in A,\, b \in B\}` the product set (additively, the sumset
$`A + B`). For a non-negative integer $`m` we write $`A^m` (additively $`mA`) for the $`m`-fold
product set. The *doubling constant* of the pair $`(A, B)` is $`|A \cdot B|/|A|`, and a set has
*small doubling* when $`|A \cdot A|` is not much larger than $`|A|`. Each mathlib-backed node
carries a `(lean := …)` reference naming the exact declaration, and its proof sketch follows the
argument that declaration actually uses, naming the lemmas that proof invokes.

The final section records the **Polynomial Freiman–Ruzsa (PFR) theorem** — that a subset of
$`\mathbb{F}_2^n` with doubling $`K` is covered by $`O(K^{12})` cosets of a subgroup of size at
most $`|A|` — supplied by the public `teorth/pfr` project. Those nodes are informal (the project
builds against a different mathlib version); each records its declaration, an exact-source
permalink, and that the formalisation is sorry-free. The PFR proof passes through an *entropic*
formulation in which set-doubling is replaced by the Ruzsa distance between random variables, and
it bridges back into the mathlib graph through the Ruzsa covering lemma and the additive
$`\operatorname{card}` bound that its endgame literally invokes.

# Cardinality of product sets and the doubling constant

:::theorem "card-mul-le" (lean := "Finset.card_mul_le")
*(Submultiplicativity of the product set.)* For finite subsets $`A, B` of a group,
$$`|A \cdot B| \;\le\; |A|\cdot|B|.`
Additively, $`|A + B| \le |A|\cdot|B|`; the additive statement is `Finset.card_add_le`.
:::

:::proof "card-mul-le"
The product set $`A \cdot B` is the image of $`A \times B` under the multiplication map
$`(a, b) \mapsto ab`. The cardinality of the image of a finite product under any binary operation
is at most the product of the cardinalities (`Finset.card_image₂_le`), since the map can only
identify pairs, never create new values. Specialising the operation to multiplication gives the
bound.
:::

:::theorem "card-div-le" (lean := "Finset.card_div_le")
For finite subsets $`A, B` of a group,
$$`|A / B| \;\le\; |A|\cdot|B|,`
where $`A / B = \{a b^{-1} : a \in A,\, b \in B\}` is the quotient set. Additively, this is the
difference-set bound $`|A - B| \le |A|\cdot|B|`, `Finset.card_sub_le`.
:::

:::proof "card-div-le"
Identical to the product-set bound ({uses "card-mul-le"}[]): $`A / B` is the image of
$`A \times B` under $`(a, b) \mapsto a b^{-1}`, so `Finset.card_image₂_le` bounds its size by
$`|A|\cdot|B|`.
:::

:::definition "doubling-constant" (lean := "Finset.mulConst, Finset.divConst")
For finite subsets $`A, B` of a group with $`A` nonempty, the *doubling constant* and
*difference constant* are the rationals
$$`\sigma[A, B] \;=\; \frac{|A \cdot B|}{|A|}, \qquad \delta[A, B] \;=\; \frac{|A / B|}{|A|}.`
We abbreviate $`\sigma[A] = \sigma[A, A]` and $`\delta[A] = \delta[A, A]`. By submultiplicativity
({uses "card-mul-le"}[]) one has $`1 \le \sigma[A, B] \le |B|` when $`A, B` are nonempty, and
$`\sigma[A]` measures how far $`A` is from being a subgroup: $`\sigma[A] = 1` exactly when $`A` is
a coset of a finite subgroup. In the additive setting these are `Finset.addConst` ($`\sigma`) and
`Finset.subConst` ($`\delta`).
:::

# The Cauchy–Davenport theorem

:::theorem "cauchy-davenport-min-order" (lean := "cauchy_davenport_minOrder_mul")
*(Cauchy–Davenport for arbitrary groups, DeVos.)* Let $`A, B` be nonempty finite subsets of a
group $`G`. Then
$$`\min\!\bigl(\operatorname{minOrder}(G),\; |A| + |B| - 1\bigr) \;\le\; |A \cdot B|,`
where $`\operatorname{minOrder}(G)` is the order of the smallest nontrivial subgroup of $`G` (taken
to be $`+\infty` when $`G` is torsion-free). In words, $`|A \cdot B| \ge |A| + |B| - 1` unless this
bound would exceed the size of some nontrivial subgroup.
:::

:::proof "cauchy-davenport-min-order"
The proof is DeVos's *e-transform* argument, by well-founded induction along the relation that
orders pairs $`(A, B)` lexicographically by $`(|A \cdot B|,\; -(|A| + |B|),\; |A|)`. If $`|B| < |A|`
one passes to $`(B^{-1}, A^{-1})`, which has the same data; if $`A` is a singleton the bound is
immediate. Otherwise pick distinct $`a, b \in A` and set $`g = b^{-1}a \ne 1`, so $`A` meets its
right translate $`A g`. If $`A` is *equal* to $`Ag` then $`A` contains a coset of the nontrivial
subgroup $`\langle g\rangle`, forcing $`|A \cdot B| \ge \operatorname{minOrder}(G)` and we are done.
Otherwise the *e-transform* replaces $`(A, B)` by the two pairs
$`(A \cap Ag,\; B \cup g^{-1}B)` and its complement; their total $`|A| + |B|` is preserved while
$`|A \cap Ag| < |A|`, and the identity $`|A'B'| + |A''B''| = 2(|AB|)`-type accounting (`MulETransform.card`)
shows at least one of the two new pairs is strictly smaller in the induction order. Applying the
induction hypothesis to that pair gives the bound.
:::

:::theorem "cauchy-davenport-torsion-free" (lean := "cauchy_davenport_of_isMulTorsionFree")
*(Cauchy–Davenport in torsion-free groups.)* If $`G` is a torsion-free group and $`A, B` are
nonempty finite subsets, then
$$`|A \cdot B| \;\ge\; |A| + |B| - 1.`
:::

:::proof "cauchy-davenport-torsion-free"
In a torsion-free group there is no nontrivial finite subgroup, so $`\operatorname{minOrder}(G) = +\infty`.
The minimum in the general bound ({uses "cauchy-davenport-min-order"}[]) is then attained by the
second argument, leaving exactly $`|A| + |B| - 1 \le |A \cdot B|`.
:::

:::theorem "cauchy-davenport-zmod" (lean := "ZMod.cauchy_davenport")
*(Cauchy–Davenport, 1813/1935.)* Let $`p` be a prime and let $`A, B \subseteq \mathbb{Z}/p\mathbb{Z}`
be nonempty. Then
$$`|A + B| \;\ge\; \min\!\bigl(p,\; |A| + |B| - 1\bigr).`
:::

:::proof "cauchy-davenport-zmod"
This is the additive bound ({uses "cauchy-davenport-min-order"}[]) specialised to $`G = \mathbb{Z}/p\mathbb{Z}`.
For $`p` prime the additive group $`\mathbb{F}_p` has no proper nontrivial subgroup, so
$`\operatorname{minOrder}(\mathbb{Z}/p\mathbb{Z}) = p` (mathlib's `ZMod.minOrder_of_prime` — the same
primality of the field $`\mathbb{F}_p` that powers Fermat's little theorem). Substituting
$`\operatorname{minOrder} = p` into $`\min(\operatorname{minOrder},\, |A|+|B|-1) \le |A+B|` gives the
stated $`\min(p,\, |A|+|B|-1)` bound.
:::

# The Erdős–Ginzburg–Ziv theorem

:::theorem "egz" (lean := "ZMod.erdos_ginzburg_ziv")
*(Erdős–Ginzburg–Ziv, 1961.)* Let $`n` be a positive integer. Among any $`2n - 1` elements of
$`\mathbb{Z}/n\mathbb{Z}` (a sequence $`a : \iota \to \mathbb{Z}/n\mathbb{Z}` indexed by a finite set
$`s` with $`|s| \ge 2n - 1`), there is a subset $`t \subseteq s` of exactly $`n` indices with
$`\sum_{i \in t} a_i = 0`.

Equivalently: any sequence of at least $`2n - 1` integers contains a subsequence of exactly $`n`
terms whose sum is divisible by $`n` (`Int.erdos_ginzburg_ziv`).
:::

:::proof "egz"
The prime case is the heart of the argument and is proved via the **Chevalley–Warning theorem**.
Given a sequence $`a_1, \dots, a_{2p-1}` in $`\mathbb{Z}/p\mathbb{Z}` indexed by $`s`, form the two
multivariate polynomials
$$`f_1 = \sum_{i \in s} x_i^{\,p-1}, \qquad f_2 = \sum_{i \in s} a_i\, x_i^{\,p-1}`
in $`\mathbb{F}_p[(x_i)_{i \in s}]`. Each has total degree $`p - 1` (`totalDegree_f₁_add_totalDegree_f₂`),
so their combined total degree $`2(p-1)` is strictly less than the number $`2p - 1` of variables. By
Chevalley–Warning (`char_dvd_card_solutions_of_add_lt`), the number $`N` of common zeros in
$`\mathbb{F}_p^{\,2p-1}` is divisible by $`p`. The all-zeros vector is one common zero, so $`N > 0`,
hence $`N \ge p` and there is a *nonzero* common zero $`x`. Let $`t = \{i \in s : x_i \ne 0\}`. From
$`f_1(x) = 0` and Fermat's little theorem $`x_i^{p-1} = 1` for $`x_i \ne 0`, the count $`|t|` is
divisible by $`p`; since $`0 < |t| \le 2p - 1 < 2p`, in fact $`|t| = p`. From $`f_2(x) = 0` and the
same Fermat reduction, $`\sum_{i \in t} a_i = 0`.

The general composite case follows by induction on the prime/composite structure of $`n`
(`Nat.prime_composite_induction`). For the multiplicative step $`n = m n'`, the induction
hypothesis on $`n'` is applied repeatedly to extract $`2m - 1` pairwise-disjoint index sets of
size $`n'`, each with sum divisible by $`n'`; dividing those sums by $`n'` and applying the
induction hypothesis on $`m` selects $`m` of the sets whose total is divisible by $`m`, so their
union has size $`m n' = n` and sum divisible by $`n`. The $`\mathbb{Z}/n\mathbb{Z}` statement is
the integer statement read modulo $`n` via `ZMod.intCast_zmod_eq_zero_iff_dvd`.
:::

# The Plünnecke–Ruzsa inequality

:::theorem "ruzsa-triangle" (lean := "Finset.ruzsa_triangle_inequality_div_div_div")
*(Ruzsa's triangle inequality.)* For finite sets $`A, B, C` in a group,
$$`|A / C| \cdot |B| \;\le\; |A / B| \cdot |C / B|,`
where $`A / B = \{a b^{-1} : a \in A,\, b \in B\}` is the quotient set. Additively this is the
difference-set form $`|A - C|\cdot|B| \le |A - B|\cdot|C - B|`, `Finset.ruzsa_triangle_inequality_sub_sub_sub`.
:::

:::proof "ruzsa-triangle"
The inequality is a double-counting argument cast as a cardinality bound on a graph of a map. For
each $`x = a c^{-1} \in A / C` choose witnesses $`a \in A`, $`c \in C`. The map
$`b \mapsto (a b^{-1},\; c b^{-1})` sends $`B` injectively into $`(A / B) \times (C / B)`, because the
first coordinate $`a b^{-1}` already determines $`b` (multiplication is cancellative), and its image
lands in the fibre over $`x` under $`(u, v) \mapsto u v^{-1} = a c^{-1} = x`. Mathlib packages this as
`Finset.card_mul_le_card_mul`: a relation whose fibres each inject a copy of $`B` bounds
$`|A/C|\cdot|B|` by the size $`|A/B|\cdot|C/B|` of the ambient product. The various sum/difference
versions are obtained by substituting $`B \mapsto B^{-1}` and using $`|B^{-1}| = |B|`.
:::

:::theorem "ruzsa-doubling-difference" (lean := "Finset.divConst_le_mulConst_sq")
For a nonempty finite subset $`A` of a commutative group, the difference constant
({uses "doubling-constant"}[]) is controlled by the square of the doubling constant:
$$`\delta[A] \;\le\; \sigma[A]^2, \qquad\text{i.e.}\qquad \frac{|A - A|}{|A|} \;\le\; \Bigl(\frac{|A + A|}{|A|}\Bigr)^{\!2}.`
:::

:::proof "ruzsa-doubling-difference"
This is the self-paired case of the Ruzsa triangle inequality ({uses "ruzsa-triangle"}[]). The
sum-version triangle inequality with all three sets equal to $`A` reads
$`|A - A|\cdot|A| \le |A + A|^2`, and dividing by $`|A|^2` yields
$`\delta[A] = |A-A|/|A| \le (|A+A|/|A|)^2 = \sigma[A]^2`.
:::

:::theorem "pluennecke-petridis" (lean := "Finset.pluennecke_petridis_inequality_mul")
*(Plünnecke–Petridis inequality.)* Let $`A, B` be finite sets in a group, and suppose every nonempty
subset $`A' \subseteq A` satisfies the minimising bound $`|A \cdot B|\cdot|A'| \le |A' \cdot B|\cdot|A|`
(so $`A` itself minimises the ratio $`|A' \cdot B|/|A'|`). Then for every finite set $`C`,
$$`|C \cdot A \cdot B| \cdot |A| \;\le\; |A \cdot B| \cdot |C \cdot A|.`
Additively this is `Finset.pluennecke_petridis_inequality_add`.
:::

:::proof "pluennecke-petridis"
Induction on $`C`. The empty case is trivial. For the step from $`C` to $`C' = C \cup \{x\}`, set
$`A' = A \cap (x^{-1} C A)`, the part of $`A` whose $`x`-translate already lies in $`C A`. The product
$`C' A B` decomposes as $`C A B \cup (xA B \setminus x A' B)`, so
$$`|C' A B| \;\le\; |C A B| + |A B| - |A' B|`
by inclusion–exclusion and $`|xA B| = |A B|`, $`|xA' B| = |A' B|`. Multiplying by $`|A|` and
applying the inductive hypothesis to $`C` together with the minimality bound
$`|A B|\cdot|A'| \le |A' B|\cdot|A|` at the subset $`A'`, the $`|A' B|` terms cancel against
$`|A B|\cdot|A \cap x^{-1}CA|`, leaving $`|C' A B|\cdot|A| \le |A B|\cdot|C' A|`. The minimiser $`A`
itself is produced by `Finset.exists_min_image` over the nonempty subsets, which is exactly the
hypothesis fed to this lemma in the Plünnecke–Ruzsa proof.
:::

:::theorem "pluennecke-ruzsa" (lean := "Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add")
*(Plünnecke–Ruzsa inequality.)* Let $`A` be a nonempty finite set and $`B` a finite set in an
additive commutative group, and let $`K = |A + B| / |A|` be the doubling constant
({uses "doubling-constant"}[]) of the pair $`(A, B)`. Then for all non-negative integers $`m, n`,
$$`|mB - nB| \;\le\; K^{\,m+n}\,|A|.`
In particular $`|mB| \le K^m\,|A|` for every $`m` (`Finset.pluennecke_ruzsa_inequality_nsmul_add`):
small doubling forces all iterated sumsets to stay small.
:::

:::proof "pluennecke-ruzsa"
Fix a nonempty subset $`A' \subseteq A` minimising $`|A' + B|/|A'|` (via `Finset.exists_min_image`);
its minimal ratio is at most $`K`. Two inductions follow. First, the one-sided bound
$`|A' + mB| \le (|A'+B|/|A'|)^m\,|A'|` for all $`m`, proved by induction on $`m` using the
Plünnecke–Petridis inequality ({uses "pluennecke-petridis"}[]) at the minimiser. Second, the Ruzsa
triangle inequality ({uses "ruzsa-triangle"}[]) in its sum-difference form converts a two-sided
difference into one-sided sums:
$$`|mB - nB|\cdot|A'| \;\le\; |A' + mB|\cdot|A' + nB| \;\le\; (|A'+B|/|A'|)^{m+n}\,|A'|^2.`
Dividing by $`|A'|` and replacing the minimal ratio $`|A'+B|/|A'|` by the larger $`K = |A+B|/|A|`
(again by minimality) gives $`|mB - nB| \le K^{m+n}\,|A|`. The pure-sum special case is the slice
$`n = 0`.
:::

:::theorem "ruzsa-covering" (lean := "Finset.ruzsa_covering_mul")
*(Ruzsa's covering lemma.)* Let $`A, B` be finite subsets of a group with $`B` nonempty, and
suppose $`|A \cdot B| \le K\,|B|` for a real $`K`. Then there is a subset $`F \subseteq A` with
$`|F| \le K` such that
$$`A \;\subseteq\; F \cdot (B / B).`
Additively: $`A` is covered by at most $`|A + B|/|B|` translates of $`B - B`
(`Finset.ruzsa_covering_add` for finsets, `Set.ruzsa_covering_add` for sets).
:::

:::proof "ruzsa-covering"
Greedy packing. Choose $`F \subseteq A` maximal among the subsets whose translates
$`\{f \cdot B : f \in F\}` are pairwise disjoint (`Finset.exists_maximal`). Disjointness gives
$`|F|\cdot|B| = |F \cdot B| \le |A \cdot B| \le K\,|B|`, so $`|F| \le K`. For the covering, take any
$`a \in A`. If $`a \in F` then $`a \in F \cdot (B/B)` since $`1 \in B/B`. Otherwise maximality of $`F`
means $`a \cdot B` cannot be added disjointly, so it meets some $`f \cdot B` with $`f \in F`: there
are $`b, b' \in B` with $`a b = f b'`, whence $`a = f\,(b' b^{-1})`, an element of
$`f \cdot (B/B) \subseteq F \cdot (B/B)`. This is the covering lemma whose additive set form
`Set.ruzsa_covering_add` the polynomial Freiman–Ruzsa endgame invokes to pass from a dense
intersection back to a bounded cover.
:::

# Freiman homomorphisms

:::definition "freiman-hom" (lean := "IsMulFreimanHom")
For a natural number $`n` and subsets $`A \subseteq \alpha`, $`B \subseteq \beta` of commutative
monoids, a map $`f : \alpha \to \beta` is an *$`n`-Freiman homomorphism from $`A` to $`B`* if it
sends $`A` into $`B` and preserves all $`n`-fold product relations on $`A`: whenever
$`x_1 \cdots x_n = y_1 \cdots y_n` with all $`x_i, y_j \in A`, one has
$$`f(x_1)\cdots f(x_n) \;=\; f(y_1)\cdots f(y_n).`
Additively (`IsAddFreimanHom`) the condition reads
$`x_1 + \cdots + x_n = y_1 + \cdots + y_n \implies f(x_1) + \cdots + f(x_n) = f(y_1) + \cdots + f(y_n)`.
A $`0`- or $`1`-Freiman homomorphism is just a map into $`B`; the first substantial case is $`n = 2`,
and the condition strengthens as $`n` grows. Freiman homomorphisms are the structure-preserving maps
of additive combinatorics: every monoid homomorphism is an $`n`-Freiman homomorphism for all $`n`.
:::

:::definition "freiman-iso" (lean := "IsMulFreimanIso")
An *$`n`-Freiman isomorphism from $`A` to $`B`* is a bijection $`f : A \to B` for which the $`n`-fold
product relation is preserved *and reflected*:
$$`f(x_1)\cdots f(x_n) = f(y_1)\cdots f(y_n) \iff x_1 \cdots x_n = y_1 \cdots y_n`
for all $`x_i, y_j \in A`. Every Freiman isomorphism is in particular a Freiman homomorphism
({uses "freiman-hom"}[]), and every monoid isomorphism is an $`n`-Freiman isomorphism. Two sets that
are Freiman isomorphic are indistinguishable by their additive structure up to order $`n`.
:::

:::theorem "freiman-hom-two" (lean := "isMulFreimanHom_two")
*(Characterisation of $`2`-Freiman homomorphisms.)* A map $`f` is a $`2`-Freiman homomorphism from
$`A` to $`B` if and only if $`f` maps $`A` into $`B` and
$$`\forall\, a, b, c, d \in A,\quad a b = c d \;\Longrightarrow\; f(a)\,f(b) = f(c)\,f(d).`
:::

:::proof "freiman-hom-two"
The forward direction is the defining condition ({uses "freiman-hom"}[]) restricted to the two-element
multisets $`\{a, b\}` and $`\{c, d\}`, repackaged through `Finset.prod_pair` (`IsMulFreimanHom.mul_eq_mul`).
Conversely, a $`2`-element product relation on $`A` is exactly a relation $`ab = cd` between two pairs;
since any multiset of cardinality $`2` is such a pair (`Finset.card_eq_two`), the four-point hypothesis
reconstructs the full multiset condition for $`n = 2`.
:::

:::theorem "freiman-hom-mono" (lean := "IsMulFreimanHom.mono")
*(Monotonicity in the order.)* If $`m \le n` and $`f` is an $`n`-Freiman homomorphism from $`A` to
$`B` ({uses "freiman-hom"}[]), then $`f` is also an $`m`-Freiman homomorphism from $`A` to $`B`.
:::

:::proof "freiman-hom-mono"
Given an $`m`-fold product relation $`x_1 \cdots x_m = y_1 \cdots y_m` on $`A`, pad both sides with
$`n - m` copies of a fixed element $`a_0 \in A`. The padded multisets have cardinality $`n` and the
same product, so the $`n`-Freiman condition applies and yields
$`f(x_1)\cdots f(x_m)\,f(a_0)^{n-m} = f(y_1)\cdots f(y_m)\,f(a_0)^{n-m}`; cancelling the common
$`f(a_0)^{n-m}` (the ambient monoid is commutative) gives the $`m`-fold conclusion. The case $`A = \emptyset`
is handled separately since then there is no padding element.
:::

:::theorem "monoid-hom-freiman" (lean := "MonoidHomClass.isMulFreimanHom")
Every monoid homomorphism is a Freiman homomorphism: if $`f : \alpha \to \beta` is a monoid
homomorphism and $`f` maps $`A` into $`B`, then $`f` is an $`n`-Freiman homomorphism from $`A` to
$`B` ({uses "freiman-hom"}[]) for every $`n`.
:::

:::proof "monoid-hom-freiman"
A monoid homomorphism turns a product $`x_1 \cdots x_n` into $`f(x_1)\cdots f(x_n)` (multiplicativity,
`map_multiset_prod`). Hence if $`x_1 \cdots x_n = y_1 \cdots y_n` then applying $`f` to both sides and
distributing across the products gives $`f(x_1)\cdots f(x_n) = f(y_1)\cdots f(y_n)` directly, with no
hypothesis on $`A` beyond $`f(A) \subseteq B`. This shows the Freiman condition is a genuine weakening
of being a homomorphism.
:::

# Sets of very small doubling

The doubling constant $`\sigma[A]` ({bpref "doubling-constant"}[]) controls how close $`A` is to a
subgroup. The three structure theorems below sharpen this as the doubling threshold rises from
$`1` (no doubling) through $`3/2` and the golden ratio $`\varphi = (1+\sqrt5)/2` to $`2 - \varepsilon`,
following Tointon's monograph and Tao's non-commutative Freiman theorem. They are stated for an
arbitrary group $`G`.

:::theorem "no-doubling" (lean := "Finset.smul_stabilizer_of_no_doubling")
*(Doubling exactly one.)* Let $`A` be a nonempty finite subset of a group $`G` with no doubling,
$`|A \cdot A| \le |A|`. Then for every $`a \in A`,
$$`a \cdot \operatorname{Stab}_G(A) \;=\; A,`
where $`\operatorname{Stab}_G(A) = \{g : gA = A\}` is the stabiliser subgroup. That is, a set of
doubling $`1` is exactly a left coset of a finite subgroup (its own stabiliser), and symmetrically a
right coset (`Finset.op_smul_stabilizer_of_no_doubling`).
:::

:::proof "no-doubling"
The hypothesis $`|A\cdot A| \le |A|` forces every translate to be the whole product set: for $`a \in A`,
$`aA \subseteq A\cdot A` has $`|aA| = |A| \ge |A \cdot A|`, so $`aA = A\cdot A`, and likewise $`Aa = A\cdot A`.
Thus $`aA = Aa` for all $`a \in A`, and one checks $`x A \in A \iff a x \in A` (the comparison
$`xa \in A \iff ax \in A`). Writing $`H = \operatorname{Stab}_G(A)`, these identities give
$`a^{-1}A = H` as sets for each $`a \in A` (`inv_smul_A`): an element fixes $`A` precisely when
left-multiplying it into $`a^{-1}A` stays in $`A`. Rearranging $`a^{-1}A = H` yields $`a \cdot H = A`,
and the right-handed version follows by the same computation with $`smul`/`op_smul` swapped.
:::

:::theorem "doubling-lt-two-symmetry" (lean := "Finset.mul_inv_eq_inv_mul_of_doubling_lt_two")
Let $`A` be a finite subset of a group with doubling strictly less than $`2`:
$$`|A \cdot A| \;<\; 2\,|A|.`
Then the two "difference" sets coincide:
$$`A \cdot A^{-1} \;=\; A^{-1} \cdot A.`
:::

:::proof "doubling-lt-two-symmetry"
It suffices to prove one inclusion $`A^{-1}A \subseteq A A^{-1}` and apply it to $`A^{-1}`. Take
$`x^{-1} y \in A^{-1}A` with $`x, y \in A`. The translates $`xA` and $`yA` each have size $`|A|` and
both sit inside $`A\cdot A`; since $`|A \cdot A| < 2|A|`, inclusion–exclusion forces their intersection
to be nonempty (`lt_card_smul_inter_smul` with $`K = 2`). Picking $`t` with $`xt = z` and $`yt = w`
for some $`z, w \in A` exhibits $`x^{-1}y = z w^{-1} \in A A^{-1}`. The reverse inclusion comes from the
same statement applied to $`A^{-1}` (whose doubling is also $`< 2`), giving equality.
:::

:::definition "inv-mul-subgroup" (lean := "Finset.invMulSubgroup")
For a finite subset $`A` of a group with $`|A \cdot A| < \tfrac32\,|A|`, the set
$`A^{-1} \cdot A` is a *subgroup* of $`G`, denoted $`\operatorname{invMulSubgroup}(A)`. Its carrier is
$$`\{a^{-1} b : a, b \in A\} \;=\; A^{-1} \cdot A,`
which equals $`A \cdot A^{-1}` under the same hypothesis ({uses "doubling-lt-two-symmetry"}[]). The
$`3/2` threshold is sharp: for $`A = \{0, 1\} \subseteq \mathbb{Z}` one has $`|A+A| = 3 = \tfrac32|A|`
and $`A - A = \{-1, 0, 1\}` is *not* a subgroup.
:::

:::proof "inv-mul-subgroup"
Closure under inverse is immediate, since $`(a^{-1}b)^{-1} = b^{-1}a \in A^{-1}A`. The identity lies in
$`A^{-1}A` because $`A` is nonempty ($`x^{-1}x = 1`). Closure under multiplication is where the sharper
hypothesis $`|A\cdot A| < \tfrac32|A|` enters: for $`a^{-1}b,\, c^{-1}d \in A^{-1}A`, the bound makes
every pairwise intersection of translates large, $`\tfrac12|A| < |xA \cap yA|`
(`lt_card_smul_inter_smul` with $`K = 3/2`), so two such intersections must overlap; a common point
$`t` produces the witness exhibiting $`(a^{-1}b)(c^{-1}d) \in A^{-1}A`, using the symmetry
$`A A^{-1} = A^{-1}A` ({uses "doubling-lt-two-symmetry"}[]).
:::

:::theorem "small-doubling-three-halves" (lean := "Finset.doubling_lt_three_halves")
*(Structure of sets of doubling below $`3/2`; Tointon, Theorem 2.2.1.)* Let $`A` be a finite subset
of a group $`G` with
$$`|A \cdot A| \;<\; \tfrac{3}{2}\,|A|.`
Then there is a finite subgroup $`H \le G` with $`|H| < \tfrac{3}{2}\,|A|` such that, for every
$`a \in A`,
$$`A \;\subseteq\; a \cdot H \qquad\text{and}\qquad a\,H = H\,a.`
In words, $`A` lies inside a single coset of a subgroup barely larger than $`A`, and that subgroup
is normalised by every element of $`A`.
:::

:::proof "small-doubling-three-halves"
Take $`H = \operatorname{invMulSubgroup}(A) = A^{-1}\cdot A` ({uses "inv-mul-subgroup"}[]). The
containment $`A \subseteq a\cdot H` holds for each $`a \in A` because $`a^{-1}A \subseteq A^{-1}A = H`,
and the normalisation $`aH = Ha` is `smul_inv_mul_eq_inv_mul_opSMul`, a consequence of the symmetry
$`AA^{-1} = A^{-1}A` ({uses "doubling-lt-two-symmetry"}[]). For the size bound, a double-counting of
the representations $`a^{-1}b = x` over $`A \times A` shows each element of $`H = A^{-1}A` has more
than $`\tfrac12|A|` representations (`weak_invMulSubgroup_bound`), so $`|H| < 2|A|`; combined with the
identity $`|A^{-1}A| = |A\cdot A|` valid below $`3/2` (`card_inv_mul_of_doubling_lt_three_halves`) this
upgrades to $`|H| = |A\cdot A| < \tfrac32|A|`. The threshold is sharp, as $`A = \{0,1\} \subseteq \mathbb{Z}`
witnesses ({uses "inv-mul-subgroup"}[]).
:::

:::theorem "small-doubling-golden" (lean := "Finset.doubling_lt_golden_ratio")
*(Doubling below the golden ratio.)* Let $`\varphi = (1+\sqrt5)/2` and $`\psi = (1-\sqrt5)/2` be the
roots of $`t^2 = t + 1`. If $`A` is a finite subset of a group with $`1 < K < \varphi` and
$$`|A^{-1}\cdot A| \le K\,|A|, \qquad |A \cdot A^{-1}| \le K\,|A|,`
then $`A \cdot A^{-1}` is covered by boundedly many cosets of a finite subgroup: there is a finite
subgroup $`H \le G` and a finite set $`Z` with
$$`|Z| \;\le\; \frac{(2 - K)\,K}{(\varphi - K)(K - \psi)} \qquad\text{and}\qquad H \cdot Z = A \cdot A^{-1}.`
:::

:::proof "small-doubling-golden"
Let $`S = A\cdot A^{-1}` and $`H = \operatorname{Stab}_G(S)`, a finite subgroup with $`H\cdot S = S`.
Choose coset representatives $`Z \subseteq S` with $`H \cdot Z = S` and the cosets $`Hz` disjoint, so
$`|H|\cdot|Z| = |S|`. Bounding $`|Z|` is therefore the same as lower-bounding $`|H|` relative to $`|S|`.
For $`z \in S` write $`r(z)` for the number of representations $`z = a b^{-1}` with $`a, b \in A`. A
double count of $`|A|^2 = \sum_{z \in S} r(z)`, splitting $`S` according to whether $`r(z) > (K-1)|A|`,
yields $`|S| \le (2-K)K\,\ell + (K-1)K\,|S|` where $`\ell` is the number of high-representation
elements; rearranged via $`(\varphi-K)(K-\psi) = 1 - (K-1)K` this gives the stated proportion bound. One
then shows every high-representation $`z` stabilises $`S`: since $`r(w) \ge (2-K)|A|` for all $`w \in S`
(from $`|A^{-1}A| \le K|A|`) while $`r(z) > (K-1)|A|`, inclusion–exclusion makes the relevant translates
of $`A` overlap, certifying $`zw \in S` for every $`w`, i.e. $`z \in H`. Hence the high-representation
elements lie in $`H`, giving $`|H| \ge \ell` and the cover.
:::

:::theorem "small-doubling-two-eps" (lean := "Finset.doubling_lt_two")
*(Doubling below $`2 - \varepsilon`.)* Let $`0 < \varepsilon \le 1` and let $`A` be a nonempty finite
subset of a group with
$$`|A \cdot A| \;\le\; (2 - \varepsilon)\,|A|.`
Then there is a finite subgroup $`H \le G` and a finite set $`Z` with
$$`|H| \;\le\; \Bigl(\tfrac{2}{\varepsilon} - 1\Bigr)|A|, \qquad |Z| \;\le\; \tfrac{2}{\varepsilon} - 1, \qquad A \;\subseteq\; H \cdot Z.`
So a set of doubling bounded away from $`2` is covered by a bounded number of cosets of a subgroup of
size $`O(|A|)`.
:::

:::proof "small-doubling-two-eps"
Set $`K = 1 - \varepsilon/2 < 1` and, for a finite set $`S`, define the *expansion*
$`\operatorname{ex}(B) = |B\cdot S| - K\,|B|` and the *connectivity*
$`\kappa = \inf_{B \ne \emptyset} \operatorname{ex}(B)`. Expansion is submodular and (for $`K < 1`)
positive on nonempty sets, so the infimum is attained on a nonempty *atom* — a minimal-cardinality
minimiser — and, because translates of an atom partition $`G` (atoms with nonempty intersection
coincide), a translate of an atom through the identity is a finite subgroup $`H`. Taking $`S = A` and
$`Z` a right-coset transversal of $`H` inside $`A`, the hypothesis
$`|A\cdot A| \le (2-\varepsilon)|A|` bounds $`\operatorname{ex}(H) \le (1 - \varepsilon/2)|A|`, from
which $`|H| \le (2/\varepsilon - 1)|A|` and $`|Z| = |H\cdot A|/|H| \le 2/\varepsilon - 1` follow by the
connectivity estimate. This is the case $`A = S` of the general
covering theorem `Finset.card_mul_finset_lt_two`.
:::

# The polynomial Freiman–Ruzsa theorem

The nodes below are supplied by the public [`teorth/pfr`](https://github.com/teorth/pfr) project,
which is sorry-free and ships its own LaTeX blueprint. They are *informal* here — the project builds
against a different mathlib version — so they carry no `(lean := …)` reference; instead each records
the formalising declaration, an exact-source permalink at the recorded commit, and that the proof is
sorry-free. The provenance commit is
[`901bc69`](https://github.com/teorth/pfr/tree/901bc69df2318ab450221886a92fc8f41b31e037). These
results form their own component, joined to the mathlib graph through the Ruzsa covering lemma
({bpref "ruzsa-covering"}[]) and the additive cardinality bound ({bpref "card-mul-le"}[]) that the PFR
endgame literally invokes.

## Ruzsa distance between random variables

:::definition "ruzsa-distance"
Let $`X` and $`Y` be $`G`-valued random variables, where $`G` is a countable additive group, and let
$`X', Y'` be independent copies (placed on a common probability space). The *Ruzsa distance* between
$`X` and $`Y` is
$$`d[X \,;\, Y] \;:=\; H[X' - Y'] \;-\; \tfrac12 H[X'] \;-\; \tfrac12 H[Y'],`
where $`H[\,\cdot\,]` is Shannon entropy. This is the entropic analogue of the set quantity
$`\log(|A-B|) - \tfrac12\log|A| - \tfrac12\log|B|`. It is symmetric, $`d[X;Y] = d[Y;X]`
(`rdist_symm`), non-negative, and depends only on
the laws of $`X` and $`Y`.

For finite nonempty sets $`A, B \subseteq G`, the *set Ruzsa distance* is
$`d_u[A \,;\, B] := d[U_A \,;\, U_B]`, the Ruzsa distance between uniform variables on $`A` and $`B`
(`setRuzsaDist`). The self-distance $`d[X;X] = \tfrac12 H[X - X'] - H[X]` specialises for a set to
$`d_u[A;A] = \log(|A - A|/|A|)`, so $`\exp(2\,d_u[A;A])` is the difference-doubling
$`\delta[A]` ({uses "doubling-constant"}[]) and, in $`\mathbb{F}_2^n`, the doubling $`|A+A|/|A|`.
Formalised in [`pfr`](https://github.com/teorth/pfr): [`rdist`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/ForMathlib/Entropy/RuzsaDist.lean#L66) and [`setRuzsaDist`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/ForMathlib/Entropy/RuzsaSetDist.lean#L17) — sorry-free.
:::

## Entropic Ruzsa triangle inequality

:::lemma_ "entropic-ruzsa-triangle"
*(Entropic Ruzsa triangle inequality.)* For $`G`-valued random variables $`X`, $`Y`, $`Z` (with
finite range, on probability spaces),
$$`d[X \,;\, Z] \;\le\; d[X \,;\, Y] + d[Y \,;\, Z].`
This is the entropy-theoretic analogue of the set-combinatorial Ruzsa triangle inequality
({uses "ruzsa-triangle"}[]): replacing $`H` by $`\log`-cardinality recovers
$`|A - C|\cdot|B| \le |A - B|\cdot|B - C|`.
Formalised in [`pfr`](https://github.com/teorth/pfr): [`rdist_triangle`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/ForMathlib/Entropy/RuzsaDist.lean#L444) — sorry-free.
:::

:::proof "entropic-ruzsa-triangle"
By replacing $`X, Y, Z` with jointly independent copies $`X', Y', Z'` on a common space
(`independent_copies3_nondep_finiteRange`) and using that Ruzsa distance depends only on the laws
(`IdentDistrib.rdist_congr`), one reduces to the independent case. There the core inequality is the
entropy submodularity bound
$$`H[X' - Z'] \;\le\; H[X' - Y'] + H[Y' - Z'] - H[Y'],`
which is `ent_of_diff_le` (a form of $`H[U - W] \le H[U - V] + H[V - W] - H[V]` for the difference
random variables). Expanding $`d[X';Z']`, $`d[X';Y']`, $`d[Y';Z']` through the independent-case formula
$`d[U;V] = H[U-V] - \tfrac12 H[U] - \tfrac12 H[V]` (`IndepFun.rdist_eq`) and substituting the
submodularity bound, the $`H[Y']` terms cancel and the inequality rearranges to
$`d[X;Z] \le d[X;Y] + d[Y;Z]`. This triangle inequality is the workhorse of the entropic PFR
endgame.
Formalised in [`pfr`](https://github.com/teorth/pfr): [`rdist_triangle`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/ForMathlib/Entropy/RuzsaDist.lean#L444) — sorry-free.
:::

## Entropic polynomial Freiman–Ruzsa theorem

:::theorem "entropic-pfr"
*(Entropic PFR / Marton's conjecture, entropic form.)* Let $`G = \mathbb{F}_2^n` be an elementary
abelian $`2`-group and let $`X^0_1, X^0_2` be $`G`-valued random variables. Then there is a subgroup
$`H \le G` and a $`G`-valued random variable $`U_H` uniform on $`H` such that
$$`d[X^0_1 \,;\, U_H] + d[X^0_2 \,;\, U_H] \;\le\; 11 \cdot d[X^0_1 \,;\, X^0_2],`
and moreover each of $`d[X^0_1; U_H]` and $`d[X^0_2; U_H]` is at most $`6\,d[X^0_1; X^0_2]`
(`entropic_PFR_conjecture'`).
Formalised in [`pfr`](https://github.com/teorth/pfr): [`entropic_PFR_conjecture`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/EntropyPFR.lean#L52) — sorry-free.
:::

:::proof "entropic-pfr"
The proof minimises a *tau-functional* built from the Ruzsa distance ({uses "ruzsa-distance"}[]),
$$`\tau[X_1 \,;\, X_2] \;=\; d[X_1 \,;\, X_2] + \eta\bigl(d[X^0_1 \,;\, X_1] + d[X^0_2 \,;\, X_2]\bigr),`
with $`\eta = 1/9`. A minimiser $`(X_1, X_2)` exists by compactness (`tau_minimizer_exists`: the group
is finite and $`\tau` is continuous in the laws). The crux is the *tau-decrement*
(`tau_strictly_decreases`): if $`d[X_1; X_2] > 0` at a minimiser then $`\tau` could be strictly
decreased — by combining four independent copies of the minimiser, forming the four sums, and bounding
their joint entropy through a fibring identity and the entropic Ruzsa triangle inequality
({uses "entropic-ruzsa-triangle"}[]) — contradicting minimality. Hence $`d[X_1; X_2] = 0`.

From $`d[X_1; X_2] = 0`, the **100% theorem** (`exists_isUniform_of_rdist_eq_zero`) produces a subgroup
$`H` and a uniform $`U_H` with $`d[X_1; U_H] = d[X_2; U_H] = 0`. Finally the minimiser inequality
$`\tau[X_1; X_2] \le \tau[X^0_2; X^0_1]` (`is_tau_min`), unfolded with $`\eta = 1/9` and combined with two
applications of the entropic Ruzsa triangle inequality
$`d[X^0_i; U_H] \le d[X^0_i; X_i] + d[X_i; U_H]` ({uses "entropic-ruzsa-triangle"}[]) and the symmetry of
Ruzsa distance, yields the constant $`11`; the per-variable $`6`-bound follows from one further triangle
step. The proof is independent of the deterministic Plünnecke–Ruzsa machinery, but rests on the same
Ruzsa calculus — symmetry and the triangle inequality of Ruzsa distance.
Formalised in [`pfr`](https://github.com/teorth/pfr): [`entropic_PFR_conjecture`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/EntropyPFR.lean#L52) — sorry-free.
:::

## Polynomial Freiman–Ruzsa theorem

:::theorem "pfr-conjecture"
*(Polynomial Freiman–Ruzsa theorem; Marton's conjecture for $`\mathbb{F}_2^n`, proved 2023.)* Let
$`G = \mathbb{F}_2^n` and let $`A \subseteq G` be a nonempty finite set with doubling constant
$`|A + A| \le K\,|A|`. Then there is a subgroup $`H \le G` and a set of coset representatives $`c` with
$$`|c| < 2\,K^{12}, \qquad |H| \le |A|, \qquad A \subseteq c + H.`
Equivalently, any set of small doubling in $`\mathbb{F}_2^n` is covered by fewer than $`2K^{12}`
cosets of a subgroup no larger than $`A` (`PFR_conjecture'` removes the finiteness assumption on $`G`).
Formalised in [`pfr`](https://github.com/teorth/pfr): [`PFR_conjecture`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/Main.lean#L258) — sorry-free.
:::

:::proof "pfr-conjecture"
The proof reduces the set problem to the entropic one (`PFR_conjecture_aux`). Let $`U_A` be uniform on
$`A`. Then $`H[U_A] = \log|A|`, and since $`U_A + U_A` is supported on $`A + A`, the doubling
hypothesis gives the self-distance bound $`d[U_A; U_A] \le \log K` through the Ruzsa-distance definition
({uses "ruzsa-distance"}[]). Entropic PFR ({uses "entropic-pfr"}[]) supplies a subgroup $`H` with
$`d[U_A; U_H] \le \tfrac{11}{2}\log K`; comparing entropies then bounds $`|\log|H| - \log|A|| \le 11\log K`,
so $`|H|/|A| \in [K^{-11}, K^{11}]`, and produces a translate $`x_0` with
$$`|A \cap (H + x_0)| \;\ge\; K^{-11/2}\,|A|^{1/2}\,|H|^{1/2}.`
The **Ruzsa covering lemma** ({uses "ruzsa-covering"}[]), in its additive set form
`Set.ruzsa_covering_add`, then covers $`A` by at most
$$`\frac{|A + (A \cap (H + x_0))|}{|A \cap (H + x_0)|} \;\le\; K^{13/2}\,\frac{|A|^{1/2}}{|H|^{1/2}}`
translates of $`(A \cap (H+x_0)) - (A \cap (H+x_0)) \subseteq H`. If $`|H| \le |A|` this already gives
the conclusion via the index bound. If $`|H| > |A|`, one splits $`H` into at most $`2|H|/|A|` cosets of a
subgroup $`H' \le H` with $`|H'| \le |A|` (`ZModModule.exists_submodule_subset_card_le`), and the cover
count multiplies — using the additive cardinality bound for products of cosets
(`natCard_add_le`, the set form of ({uses "card-mul-le"}[])) — to fewer than $`2K^{12}` translates of
$`H'`. Either way the bound $`2K^{12}` follows.

Conceptually this is the polynomial-in-$`K` analogue, in $`\mathbb{F}_2^n`, of the sharp-constant
structure theorem for general groups: PFR plays the role that the doubling-below-$`3/2` structure
theorem plays at doubling $`3/2`, trading the exact constant for a polynomial dependence that holds at
every doubling $`K`.
Formalised in [`pfr`](https://github.com/teorth/pfr): [`PFR_conjecture`](https://github.com/teorth/pfr/blob/901bc69df2318ab450221886a92fc8f41b31e037/PFR/Main.lean#L258) — sorry-free.
:::
