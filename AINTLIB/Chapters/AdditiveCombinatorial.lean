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
$`\mathbb{F}_2^n` with small doubling is efficiently covered by boundedly many cosets of a
subgroup — is supplied by the `teorth/pfr` project (Phase 3). The PFR proof passes through
an *entropic* formulation in which set-doubling is replaced by Ruzsa distance between random
variables; this entropic route is what ties PFR directly to the Ruzsa calculus developed above.

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

The prime case is exactly the threshold instance of an iterated sumset bound, and can
equivalently be derived from the Cauchy–Davenport theorem ({uses "cauchy-davenport"}[]):
applying $`|A_1 + \dots + A_{2p-1}| \ge \min(p, \sum(|A_i| - 1) + 1)` to the two-element
sets $`A_i = \{0, a_i\}` forces a zero-sum of length $`p` once the partial sums fill all of
$`\mathbb{Z}/p\mathbb{Z}`. The step $`|T| = p` above uses Fermat's little theorem
({uses "fermat-little"}[]), since $`f_1(x) = \sum x_i^{p-1}` counts, modulo $`p`, the nonzero
coordinates of a common zero.

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
has order $`p` — for $`p` prime the additive group $`\mathbb{F}_p` has no proper nontrivial
subgroup, the same primality of the field $`\mathbb{F}_p` that powers Fermat's little theorem
({uses "fermat-little"}[]).

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
each element of $`H = A^{-1} A`. The size of this difference set is controlled by Ruzsa's
triangle inequality ({uses "ruzsa-triangle"}[]), which bounds $`|A^{-1}A|` in terms of
$`|A^{-1}A^{-1}|` and $`|A A|`; combined with the intersection bound this shows the average
representation count exceeds $`\tfrac{1}{2}|A|`, forcing $`|H| < 2|A|`. The sharper bound
$`\tfrac{3}{2}` follows from a more careful version of the same double-counting.

Finally, $`A \subseteq a H` for every $`a \in A` because $`a^{-1} A \subseteq A^{-1} A = H`.
The commutativity $`aH = Ha` is a consequence of $`A \cdot A^{-1} = A^{-1} \cdot A`.

The threshold $`3/2` is sharp: the set $`\{0, 1\} \subseteq \mathbb{Z}` has doubling
exactly $`3/2` and cannot be covered by a subgroup of size at most $`2`.
:::

# Phase 3: Polynomial Freiman–Ruzsa (teorth/pfr)

The nodes below are *informal*: the `teorth/pfr` project is built against a different
Mathlib version, so they carry no `(lean := …)` reference. Each records the relevant
declaration name and whether the formalisation is sorry-free. They connect into the
dependency graph through the Mathlib-backed Plünnecke–Ruzsa and small-doubling nodes
above via `{uses}` edges.

## Ruzsa distance

:::definition "ruzsa-distance"
Let $`X` and $`Y` be $`G`-valued random variables on probability spaces $`(\Omega, \mathbb{P})`
and $`(\Omega', \mathbb{P}')` respectively, where $`G` is a countable abelian group.
The *Ruzsa distance* between $`X` and $`Y` is
$$`d[X \,;\, Y] \;\coloneqq\; H[X' - Y'] \;-\; \tfrac12 H[X'] \;-\; \tfrac12 H[Y'],`
where $`X', Y'` are independent copies of $`X, Y` (placed on a common space), and $`H[\,\cdot\,]`
denotes Shannon entropy. For finite sets $`A, B \subseteq G` the *set Ruzsa distance* is
$`d_u[A \,;\, B] \coloneqq d[U_A \,;\, U_B]`, where $`U_A, U_B` are uniform random variables on
$`A` and $`B`.

Note that $`d[X \,;\, X] = \tfrac12 H[X - X'] - H[X]` where $`X'` is an independent copy of
$`X`; for a set this equals $`\log|A - A| - \log|A| = \log(|A - A|/|A|)`, so $`\exp(2d_u[A;A])`
is the doubling constant $`|A+A|/|A|` in the $`\mathbb{F}_2^n` setting.
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::

## Entropic Ruzsa triangle inequality

:::lemma_ "entropic-ruzsa-triangle"
*(Entropic Ruzsa triangle inequality.)* For $`G`-valued random variables $`X`, $`Y`, $`Z`
on respective probability spaces,
$$`d[X \,;\, Z] \;\le\; d[X \,;\, Y] + d[Y \,;\, Z].`
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::

:::proof "entropic-ruzsa-triangle"
Work with independent copies $`X', Y', Z'` of $`X, Y, Z` placed on a common probability
space. By the submodularity of entropy,
$$`H[X' - Z'] \;\le\; H[X' - Y'] + H[Y' - Z'] - H[Y'].`
Expanding $`d[X';Z']`, $`d[X';Y']`, $`d[Y';Z']` in terms of entropy and rearranging gives
the triangle inequality.

This is the entropy-theoretic analogue of the set-combinatorial Ruzsa triangle inequality
({uses "ruzsa-triangle"}[]): in the deterministic set setting, replacing $`H` by $`\log`-cardinality
recovers $`|A - C| \cdot |B| \le |A - B| \cdot |B - C|`.
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::

## Entropic Polynomial Freiman–Ruzsa conjecture

:::theorem "entropic-pfr"
*(Entropic PFR conjecture / Marton's conjecture, entropic form.)* Let $`G` be an elementary
abelian $`2`-group (i.e. $`G \cong \mathbb{F}_2^n` for some $`n`) and let $`X^0_1, X^0_2`
be $`G`-valued random variables. Then there exists a subgroup $`H \le G` and a random
variable $`U_H` uniformly distributed on $`H` such that
$$`d[X^0_1 \,;\, U_H] + d[X^0_2 \,;\, U_H] \;\le\; 11 \cdot d[X^0_1 \,;\, X^0_2].`
In the improved form (Liao), the constant $`11` may be replaced by $`10`.
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::

:::proof "entropic-pfr"
The proof minimises a *tau-functional*
$$`\tau[X_1 \,;\, X_2] \;\coloneqq\; d[X_1 \,;\, X_2] + \eta\bigl(d[X^0_1 \,;\, X_1] + d[X^0_2 \,;\, X_2]\bigr),`
with $`\eta = 1/9`, over all pairs of $`G`-valued random variables $`(X_1, X_2)`. A tau-minimiser
exists by compactness (the group is finite); the crux is showing that if $`d[X_1 \,;\, X_2] > 0`
at a minimiser then $`\tau` can be strictly decreased — a contradiction.

The decreasing construction combines four independently chosen copies of the minimiser, forms
four sums, and bounds their combined entropy using the entropic Ruzsa triangle inequality
({uses "entropic-ruzsa-triangle"}[]) together with a fibring argument. The bound forces
$`d[X_1 \,;\, X_2] = 0` at any minimiser.

From $`d[X_1 \,;\, X_2] = 0`, the **100% theorem** produces a subgroup $`H` and a uniform
$`U_H` with $`d[X_1 \,;\, U_H] = d[X_2 \,;\, U_H] = 0`. Transferring back via the
tau-functional bound and the Ruzsa triangle inequality ({uses "entropic-ruzsa-triangle"}[])
gives the stated $`11 d[X^0_1 \,;\, X^0_2]` bound.

The proof is independent of the Plünnecke–Ruzsa and small-doubling results in the
deterministic setting above, but the underlying Ruzsa calculus — in particular the
symmetry and triangle inequality of Ruzsa distance — is the same conceptual machinery
({uses "pluennecke-ruzsa"}[], {uses "ruzsa-triangle"}[]).
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::

## Polynomial Freiman–Ruzsa conjecture

:::theorem "pfr-conjecture"
*(Polynomial Freiman–Ruzsa conjecture, Marton 1999, proved 2023.)* Let $`G = \mathbb{F}_2^n`
and let $`A \subseteq G` be a nonempty set with doubling constant $`|A + A| \le K|A|`.
Then there exists a subgroup $`H \le G` and a set of coset representatives $`c` with
$`|c| < 2K^{12}` and $`|H| \le |A|` such that $`A \subseteq c + H`.

Equivalently, any set of small doubling in $`\mathbb{F}_2^n` is covered by at most
$`2K^{12}` cosets of a subgroup of cardinality at most $`|A|`. In the improved form
(Liao), the exponent $`12` can be replaced by $`11`, and a further refinement yields $`9`.
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::

:::proof "pfr-conjecture"
The proof reduces the set problem to the entropic setting. If $`U_A` is uniform on $`A`,
then the self-Ruzsa distance satisfies $`d[U_A \,;\, U_A] \le \log K` (using the doubling
hypothesis and the fact that $`\log|A + A| - \log|A| \le \log K`). The entropic PFR
conjecture ({uses "entropic-pfr"}[]) then produces a subgroup $`H` with
$$`d[U_A \,;\, U_H] + d[U_A \,;\, U_H] = 2d[U_A \,;\, U_H] \;\le\; 11 \log K.`
From the Ruzsa distance bound and entropy comparisons one deduces
$`|A \cap (H + x_0)|` is at least $`K^{-11/2}|A|^{1/2}|H|^{1/2}` for some translate
$`x_0`. The **Ruzsa covering lemma** (from Mathlib, based on
{uses "pluennecke-ruzsa"}[]) then covers $`A` by
$`|A + (H + x_0)|/|A \cap (H + x_0)| \le K^{13/2}|A|^{1/2}|H|^{-1/2}`
translates of $`H`. Balancing $`|H|` against $`|A|` yields the stated $`2K^{12}` bound.

The connection to the small-doubling structure theorem ({uses "small-doubling-three-halves"}[])
is conceptual: both results characterise small-doubling sets as lying close to a subgroup,
with PFR giving a polynomial-in-$`K` bound in $`\mathbb{F}_2^n` while
{uses "small-doubling-three-halves"}[] gives the sharp constant $`3/2` in general groups.
Formalised in [`pfr`](https://github.com/teorth/pfr) (sorry-free).
:::
