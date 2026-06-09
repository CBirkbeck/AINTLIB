import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.VerySmallDoubling

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Additive and Combinatorial Number Theory" =>

This chapter presents four cornerstones of additive combinatorics, all formalised in
Mathlib: the Erdős–Ginzburg–Ziv theorem on zero-sum subsequences; the Cauchy–Davenport
theorem on sumsets in $`\mathbb{Z}/p\mathbb{Z}`; the Plünnecke–Ruzsa inequality bounding the
size of iterated sumsets; and the small-doubling theorem characterising finite sets of
doubling less than $`3/2` in an arbitrary group. Throughout, $`A` and $`B` denote finite
subsets of an abelian group (or, where stated, a general group), and $`|A|` denotes the
cardinality of $`A`. For a positive integer $`m`, we write $`mA` for the $`m`-fold sumset
$`A + A + \cdots + A`.

The **Polynomial Freiman–Ruzsa (PFR) theorem** — asserting that a subset of
$`\mathbb{F}_2^n` with small doubling is efficiently covered by a coset of a subgroup —
is supplied by the separate `teorth/pfr` project and will be integrated in Phase 3 of
this library. No blueprint node for PFR appears here.

# Erdős–Ginzburg–Ziv

:::theorem "egz" (lean := "ZMod.erdos_ginzburg_ziv")
*(Erdős–Ginzburg–Ziv, 1961.)* Let $`n` be a positive integer. Among any $`2n - 1` elements
of $`\mathbb{Z}/n\mathbb{Z}` (not necessarily distinct), there exist $`n` of them whose sum
is zero.

Equivalently: any sequence of at least $`2n - 1` integers contains a subsequence of
exactly $`n` terms whose sum is divisible by $`n`.
:::

:::proof "egz"
The prime case is the heart of the argument and is proved via the **Chevalley–Warning
theorem**. Given a sequence $`a_1, \dots, a_{2p-1}` in $`\mathbb{Z}/p\mathbb{Z}`, form
the two multivariate polynomials
$$`f_1 = \sum_{i=1}^{2p-1} x_i^{\,p-1}, \qquad f_2 = \sum_{i=1}^{2p-1} a_i\, x_i^{\,p-1}`
in $`\mathbb{F}_p[x_1, \dots, x_{2p-1}]`. Each has total degree $`p - 1`, so their combined
total degree $`2(p-1) < 2p - 1` is strictly less than the number of variables. By
Chevalley–Warning, the number of common zeros in $`\mathbb{F}_p^{2p-1}` is divisible by
$`p`. Since the all-zeros vector is one such common zero, there exists a nonzero common
zero $`(x_1, \dots, x_{2p-1}) \ne 0`. The indices $`i` with $`x_i \ne 0` form a subset
$`T` of size exactly $`p` (from $`f_1 = 0` using Fermat's little theorem) with
$`\sum_{i \in T} a_i = 0` (from $`f_2 = 0`).

The general composite case follows by induction on the prime factorisation of $`n`:
for $`n = mn'`, use the induction hypothesis on $`n'` to extract $`2m - 1` disjoint
subsequences of length $`n'` each summing to $`0` modulo $`n'`, then apply the induction
hypothesis on $`m` to those quotient sums to find $`m` of them whose total is $`0`
modulo $`mn'`.
:::

# Cauchy–Davenport

:::theorem "cauchy-davenport" (lean := "ZMod.cauchy_davenport")
*(Cauchy–Davenport, 1813/1935.)* Let $`p` be a prime and let $`A, B \subseteq \mathbb{Z}/p\mathbb{Z}`
be nonempty. Then
$$`|A + B| \;\ge\; \min\!\bigl(p,\; |A| + |B| - 1\bigr).`
:::

:::proof "cauchy-davenport"
Mathlib proves the more general statement that for any group $`G` and nonempty finite
$`A, B \subseteq G`, one has
$$`\min(\mathrm{minOrder}(G),\; |A| + |B| - 1) \;\le\; |A + B|,`
where $`\mathrm{minOrder}(G)` is the order of the smallest nontrivial subgroup of $`G`.
The $`\mathbb{Z}/p\mathbb{Z}` statement follows because the smallest nontrivial subgroup
has order $`p`.

The general bound is proved by the **e-transform method** of DeVos. One picks a
nonidentity element $`g` such that $`A` intersects its translate $`g + A`, and replaces
the pair $`(A, B)` by either $`(A \cap (g + A),\; B \cup (-g + B))` or the complementary
pair, both of which have the same $`|A| + |B|` but strictly smaller sum-set or strictly
smaller $`|A|`. The induction terminates because the pair decreases at each step in
a well-founded lexicographic order on $`(|A + B|,\; |A| + |B|,\; |A|)`.
:::

# Plünnecke–Ruzsa

:::lemma_ "ruzsa-triangle" (lean := "Finset.ruzsa_triangle_inequality_sub_sub_sub")
*(Ruzsa's triangle inequality.)* For finite nonempty sets $`A, B, C` in a group,
$$`|A - C| \cdot |B| \;\le\; |A - B| \cdot |B - C|.`
Here $`A - B = \{a - b : a \in A,\, b \in B\}` denotes the difference set.
:::

:::proof "ruzsa-triangle"
Fix an element of $`A - C`, say $`a - c`. For each $`b \in B`, the pair
$`(a - b,\; c - b)` belongs to $`(A - B) \times (C - B)`. Different elements $`b`
give different pairs, so counting these injections gives
$`|B| \le |\{(x, y) \in (A - B) \times (C - B) : x - y = a - c\}|`.
Summing over the $`|A - C|` elements of $`A - C` and noting the sum is at most
$`|A - B| \cdot |C - B|` (trivially) yields the inequality.
:::

:::theorem "pluennecke-ruzsa" (lean := "Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add")
*(Plünnecke–Ruzsa inequality.)* Let $`A` be a nonempty finite set and $`B` a finite set
in an additive abelian group. Let $`K = |A + B| / |A|` be the *doubling constant* of
the pair $`(A, B)`. Then for all non-negative integers $`m` and $`n`,
$$`|mB - nB| \;\le\; K^{\,m+n}\,|A|.`
In particular, $`|mB| \le K^m\,|A|` for any $`m`.
:::

:::proof "pluennecke-ruzsa"
The key intermediate step is the **Plünnecke–Petridis lemma**: among all non-empty
subsets $`A' \subseteq A` minimising the ratio $`|A' + B|/|A'|`, the set $`A'` satisfies
$`|C + A' + B| \cdot |A'| \le |A' + B| \cdot |C + A'|` for every finite $`C`. This is
proved by induction on $`|C|`, with an e-transform argument at the inductive step.

Given the Petridis lemma, one shows $`|A' + mB| \le (|A'+B|/|A'|)^m \cdot |A'|` for all
$`m \ge 0` by another induction, then applies the Ruzsa triangle inequality
({uses "ruzsa-triangle"}[]) to pass from one-sided sums to difference sets:
$`|mB - nB| \le |A'+B|^{m+n}/|A'|^{m+n-1} \le K^{m+n} |A|`.
:::

# Small doubling and structure

:::theorem "small-doubling-three-halves" (lean := "Finset.doubling_lt_three_halves")
Let $`A` be a finite subset of a group $`G` with doubling strictly less than $`3/2`:
$$`|A \cdot A| \;<\; \tfrac{3}{2}\,|A|.`
Then there exists a finite subgroup $`H \le G` with $`|H| < \tfrac{3}{2}\,|A|` such that
$`A` is contained in a left coset of $`H`, and $`H` commutes with each element of $`A`
in the sense that $`a H = H a` for every $`a \in A`.
:::

:::proof "small-doubling-three-halves"
Define $`H = A^{-1} \cdot A` as a set, and show it is a subgroup under the small-doubling
hypothesis. First, if $`|A \cdot A| < 2|A|`, then $`A \cdot A^{-1} = A^{-1} \cdot A`
(proved by an intersection argument: for any $`x, y \in A`, the translates $`xA` and $`yA`
must overlap since their union has size less than $`2|A|`). This symmetry implies that $`H`
is closed under multiplication and inversion.

For the bound $`|H| < \tfrac{3}{2}|A|`, one counts pairs $`(a, b) \in A \times A` for
each element of $`H = A^{-1} A`, using the intersection bound to show the average
representation count exceeds $`\tfrac{1}{2}|A|`, which forces $`|H| < 2|A|`; the sharper
bound $`\tfrac{3}{2}` follows from a more careful version of the same double-counting.

Finally, $`A \subseteq a H` for every $`a \in A` because $`a^{-1} A \subseteq A^{-1} A = H`.
The commutativity $`aH = Ha` is a consequence of $`A \cdot A^{-1} = A^{-1} \cdot A`.

The threshold $`3/2` is sharp: the set $`\{0, 1\} \subseteq \mathbb{Z}` has doubling
exactly $`3/2` and cannot be covered by a subgroup of size at most $`2`.
:::
