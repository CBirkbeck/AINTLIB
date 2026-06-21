import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.Degree
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The multiplication table (Shimura 3.24)" =>

Because the $`\mathrm{GL}_2` Hecke algebra $`\mathcal{H}_2` is commutative
({bpref "commring-hecke-algebra"}[]), its structure is completely pinned down by how the
generators $`T(a,d)` multiply. This chapter formalises Shimura's Theorem 3.24 \[Sh, Thm 3.24\]: the
identity $`T(1)=1`, the prime-power telescoping relation $`T(1,p^k)=T(p^k)-T(p,p)\,T(p^{k-2})`, the
recurrence and product formula for the prime-power operators $`T(p^r)`, full multiplicativity
$`T(m)\,T(n)=\sum_{d\mid(m,n)} d\,T(d,d)\,T(mn/d^2)`, and the degree formulas
$`\deg T(p^k)=1+p+\dots+p^k` and $`\deg T(m)=\sigma_1(m)`. The arguments are arithmetic and
combinatorial: telescoping sums of diagonal classes, the central role of the scalar class
$`T(p,p)`, coset-counting for the structure constants, and the Chinese Remainder Theorem for the
coprime factorisation.

:::lemma_ "T-sum-one" (lean := "HeckeRing.GL2.T_sum_one")
*$`T(1)=1`.*
In $`\mathcal{H}_2` one has $`T(1)=1`, the multiplicative identity of the Hecke algebra.

Depends on: {uses "T-sum"}[] {uses "T-ad"}[]
:::

:::proof "T-sum-one"
The only positive divisor of $`1` is $`1` itself, so the defining sum
$`T(1)=\sum_{a\mid 1} T(a,1/a)` collapses to the single term $`T(1,1)`. By
{bpref "T-ad-one-one"}[] this equals the identity of $`\mathcal{H}_2`.

Uses: {uses "T-sum"}[] {uses "T-ad"}[] {uses "T-ad-one-one"}[]
:::

:::theorem "T-ad-one-ppow-eq" (lean := "HeckeRing.GL2.T_ad_one_ppow_eq")
*Shimura 3.24(2): telescoping relation.*
Let $`p` be a prime and $`k\ge 2`. Then in $`\mathcal{H}_2`
$$`
  T(1,p^k) \;=\; T(p^k) \;-\; T(p,p)\,T(p^{k-2}).
`

Depends on: {uses "T-sum"}[] {uses "T-ad"}[] {uses "T-pp"}[]
:::

:::proof "T-ad-one-ppow-eq"
Expand $`T(p^k)=\sum_{i=0}^{\lfloor k/2\rfloor} T(p^i,p^{k-i})` over the diagonal classes whose
elementary divisors are powers of $`p`. Multiplying the scalar class $`T(p,p)` into a diagonal
class shifts both elementary divisors up by one, $`T(p,p)\,T(p^j,p^{d})=T(p^{j+1},p^{d+1})`, so
$`T(p,p)\,T(p^{k-2})=\sum_{j} T(p^{j+1},p^{k-1-j})`, which is exactly the expansion of $`T(p^k)`
with the leading $`i=0` term $`T(1,p^k)` removed. Subtracting the two expansions telescopes to the
single surviving term $`T(1,p^k)`, giving the stated identity. (Equivalently, the displayed sum is
proved by reindexing the shifted sum via $`i=j+1` and peeling off the bottom term.)

Uses: {uses "T-sum"}[] {uses "T-ad"}[] {uses "T-pp"}[]
:::

:::theorem "T-sum-prime-mul-T-ad" (lean := "HeckeRing.GL2.T_sum_prime_mul_T_ad")
*Key prime computation.*
Let $`p` be a prime and $`k\ge 1`. Then
$$`
  T(p)\,T(1,p^k) \;=\; T(1,p^{k+1}) \;+\; c\,T(p,p^k),
  \qquad
  c \;=\;
  \begin{cases}
    p+1, & k=1,\\
    p,   & k\ge 2.
  \end{cases}
`

Depends on: {uses "T-sum-prime"}[] {uses "T-ad"}[] {uses "T-pp"}[] {uses "hecke-multiplicity"}[]
:::

:::proof "T-sum-prime-mul-T-ad"
Since $`T(p)=T(1,p)` ({bpref "T-sum-prime"}[]), the product is the convolution of the basis
elements attached to $`\operatorname{diag}(1,p)` and $`\operatorname{diag}(1,p^k)`. By the product
formula for the Hecke ring, its coefficient at a double coset $`A` is the structure constant
$`\mu` counting pairs of left-coset representatives whose product lands in a left coset of $`A`.
A determinant computation forces every such $`A` to have total elementary divisor product
$`p^{k+1}`, and a divisibility analysis of the first elementary divisor (using that an integral
matrix of determinant $`1` has coprime first column) shows that the only double cosets that can
occur are $`\operatorname{diag}(1,p^{k+1})` and $`\operatorname{diag}(p,p^k)`. Counting the
overlapping left cosets gives multiplicity $`1` at $`\operatorname{diag}(1,p^{k+1})` and
multiplicity $`c` at $`\operatorname{diag}(p,p^k)`, where the count splits according to whether
$`k=1` (the two contributing cosets coincide, giving $`p+1`) or $`k\ge 2` (giving $`p`). All other
coefficients vanish, which is the claimed identity.

Uses: {uses "T-sum-prime"}[] {uses "T-ad"}[] {uses "T-pp"}[] {uses "hecke-multiplicity"}[]
:::

:::theorem "T-sum-ppow-recurrence" (lean := "HeckeRing.GL2.T_sum_ppow_recurrence")
*Prime-power recurrence.*
Let $`p` be a prime and $`k\ge 1`. Then
$$`
  T(p^{k+1}) \;=\; T(p)\,T(p^k) \;-\; p\,\bigl(T(p,p)\,T(p^{k-1})\bigr).
`

Depends on: {uses "T-ad-one-ppow-eq"}[] {uses "T-sum-prime-mul-T-ad"}[] {uses "T-sum-prime"}[] {uses "T-pp"}[]
:::

:::proof "T-sum-ppow-recurrence"
Apply the key computation {bpref "T-sum-prime-mul-T-ad"}[] at exponent $`k` and rewrite the
two diagonal classes through the telescoping relation {bpref "T-ad-one-ppow-eq"}[], using
$`T(p,p^k)=T(p,p)\,T(1,p^{k-1})` to express both $`T(1,p^k)`, $`T(1,p^{k+1})` and $`T(p,p^k)` in
terms of the $`T(p^\bullet)`. For $`k=1` the coefficient $`c=p+1` contributes an extra $`+T(p,p)`
which combines with the base values $`T(p^0)=1` and $`T(1,p)=T(p)`; for $`k\ge 2` one proceeds by
strong induction, substituting the recurrence already known at the smaller index and using that
$`T(p)` and $`T(p,p)` commute. Collecting the terms and isolating $`T(p^{k+1})` yields the displayed
three-term recurrence.

Uses: {uses "T-ad-one-ppow-eq"}[] {uses "T-sum-prime-mul-T-ad"}[] {uses "T-sum-prime"}[] {uses "T-pp"}[]
:::

:::theorem "T-sum-ppow-mul" (lean := "HeckeRing.GL2.T_sum_ppow_mul")
*Shimura 3.24(3): prime-power product.*
Let $`p` be a prime and let $`r\le s`. Then
$$`
  T(p^r)\,T(p^s) \;=\; \sum_{i=0}^{r} p^i\,T(p^i,p^i)\,T(p^{r+s-2i}).
`

Depends on: {uses "T-sum-ppow-recurrence"}[] {uses "T-pp"}[] {uses "T-sum"}[]
:::

:::proof "T-sum-ppow-mul"
Strong induction on $`r`. For $`r=0` the sum has the single term $`T(p^s)`, and for $`r=1` the
statement is precisely the recurrence {bpref "T-sum-ppow-recurrence"}[] solved for
$`T(p)\,T(p^s)`. For the inductive step write $`T(p^{r+2})=T(p)\,T(p^{r+1})-p\,T(p,p)\,T(p^r)` from
the recurrence and apply the induction hypothesis to $`T(p^{r+1})\,T(p^s)` and $`T(p^r)\,T(p^s)`.
Each $`T(p)\,T(p^{r+1+s-2i})` splits, again by the recurrence, into a top term
$`T(p^{r+2+s-2i})` and a shifted term $`p\,T(p,p)\,T(p^{r+s-2i})`; the shifted terms cancel against
the contribution of $`-p\,T(p,p)\,T(p^r)` except at the two endpoints, where reindexing
$`T(p,p)^{i}\cdot T(p,p)=T(p^{i+1},p^{i+1})` reassembles the sum over $`i=0,\dots,r+2`. This is the
asserted product formula.

Uses: {uses "T-sum-ppow-recurrence"}[] {uses "T-pp"}[] {uses "T-sum"}[]
:::

:::theorem "T-sum-mul-coprime" (lean := "HeckeRing.GL2.T_sum_mul_coprime")
*Coprime multiplicativity.*
Let $`m,n` be positive integers with $`(m,n)=1`. Then $`T(m)\,T(n)=T(mn)`.

Depends on: {uses "T-sum"}[] {uses "T-ad"}[] {uses "commring-hecke-algebra"}[]
:::

:::proof "T-sum-mul-coprime"
Expand both factors as sums over divisor pairs and multiply out:
$`T(m)\,T(n)=\sum_{a\mid m}\sum_{b\mid n} T(a,m/a)\,T(b,n/b)`. Because $`(m,n)=1`, the elementary
divisors of the two diagonal classes are coprime, so the corresponding diagonal double cosets
split as a single double coset under the Chinese Remainder Theorem, giving
$`T(a,m/a)\,T(b,n/b)=T(ab,(m/a)(n/b))=T(ab,mn/(ab))`. The map $`(a,b)\mapsto ab` is a bijection from
divisor pairs of $`(m,n)` onto divisors of $`mn` (again by coprimality), so the double sum
reindexes to $`\sum_{c\mid mn} T(c,mn/c)=T(mn)`. The terms where a divisibility constraint fails
contribute $`0` on both sides, matching up.

Uses: {uses "T-sum"}[] {uses "T-ad"}[] {uses "commring-hecke-algebra"}[]
:::

:::theorem "T-sum-mul" (lean := "HeckeRing.GL2.T_sum_mul")
*Shimura 3.24: general product.*
For positive integers $`m,n`,
$$`
  T(m)\,T(n) \;=\; \sum_{d\,\mid\,(m,n)} d\,T(d,d)\,T\!\left(\frac{mn}{d^2}\right),
`
the sum being over the positive divisors $`d` of the greatest common divisor $`(m,n)`.

Depends on: {uses "T-sum-ppow-mul"}[] {uses "T-sum-mul-coprime"}[] {uses "T-pp"}[] {uses "T-sum"}[]
:::

:::proof "T-sum-mul"
Both sides are multiplicative in the coprime factorisation of $`m` and $`n`, so by induction on the
gcd it suffices to treat one prime at a time. Factor out a prime $`q\mid(m,n)`, writing
$`m=q^a m'` and $`n=q^b n'` with $`q\nmid m'n'`. The coprime multiplicativity
{bpref "T-sum-mul-coprime"}[] reduces $`T(m)\,T(n)` to $`T(q^a)\,T(q^b)` times the
$`q`-free part $`T(m')\,T(n')`, to which the induction hypothesis applies. The prime-power factor is
evaluated by {bpref "T-sum-ppow-mul"}[], whose terms $`q^i\,T(q^i,q^i)\,T(q^{a+b-2i})` are
exactly the $`d=q^i` contributions to the divisor sum. Recombining the prime-power sum with the
$`q`-free divisor sum, using that divisors of $`(m,n)` factor uniquely as $`q^i` times a divisor of
$`(m',n')` and that $`T(d,d)` is multiplicative on coprime $`d`, reproduces the single sum over all
$`d\mid(m,n)`.

Uses: {uses "T-sum-ppow-mul"}[] {uses "T-sum-mul-coprime"}[] {uses "T-pp"}[] {uses "T-sum"}[]
:::

:::theorem "deg-T-sum-prime-pow" (lean := "HeckeRing.GL2.deg_T_sum_prime_pow")
*Shimura 3.24(7): degree of $`T(p^k)`.*
Let $`p` be a prime and $`k\ge 0`. Then
$$`
  \deg T(p^k) \;=\; \sum_{j=0}^{k} p^{j} \;=\; 1+p+p^2+\dots+p^k.
`

Depends on: {uses "deg"}[] {uses "T-sum"}[] {uses "T-ad"}[]
:::

:::proof "deg-T-sum-prime-pow"
The degree homomorphism sends a diagonal class to its number of left cosets: for $`2i<k` one has
$`\deg T(p^i,p^{k-i})=p^{k-2i-1}(p+1)`, while the scalar classes $`T(p^i,p^i)` have degree $`1`.
Applying $`\deg` to the expansion $`T(p^k)=\sum_{i} T(p^i,p^{k-i})` and proceeding by strong
induction: for $`k\ge 2` split off the $`i=0` term, contributing $`p^{k-1}(p+1)`, and observe that
each remaining term $`T(p^{i+1},p^{k-1-i})` has the same diagonal ratio — hence the same degree —
as the corresponding term of the $`T(p^{k-2})` expansion. Thus the tail equals
$`\deg T(p^{k-2})=1+p+\dots+p^{k-2}` by the induction hypothesis, and
$`p^{k-1}(p+1)+(1+\dots+p^{k-2})=1+p+\dots+p^k`, the geometric sum.

Uses: {uses "deg"}[] {uses "T-sum"}[] {uses "T-ad"}[]
:::

:::theorem "deg-T-sum" (lean := "HeckeRing.GL2.deg_T_sum")
*Shimura 3.24(6): degree of $`T(m)`.*
For a positive integer $`m`,
$$`
  \deg T(m) \;=\; \sum_{d\,\mid\, m} d \;=\; \sigma_1(m),
`
the sum of the positive divisors of $`m`.

Depends on: {uses "deg"}[] {uses "deg-T-sum-prime-pow"}[] {uses "T-sum-mul-coprime"}[] {uses "deg-mul"}[]
:::

:::proof "deg-T-sum"
Both $`\deg T(\cdot)` and $`\sigma_1` are multiplicative arithmetic functions, so it suffices to
match them on prime powers and to use multiplicativity on coprime factors. On a prime power
{bpref "deg-T-sum-prime-pow"}[] gives $`\deg T(p^k)=1+p+\dots+p^k=\sum_{d\mid p^k} d
=\sigma_1(p^k)`. For coprime $`a,b` the coprime multiplicativity $`T(ab)=T(a)\,T(b)`
({bpref "T-sum-mul-coprime"}[]) together with the ring-homomorphism property
$`\deg(fg)=\deg f\,\deg g` ({bpref "deg-mul"}[]) yields
$`\deg T(ab)=\deg T(a)\,\deg T(b)=\sigma_1(a)\,\sigma_1(b)=\sigma_1(ab)`. Induction on the prime
factorisation of $`m` then gives $`\deg T(m)=\sigma_1(m)`.

Uses: {uses "deg"}[] {uses "deg-T-sum-prime-pow"}[] {uses "T-sum-mul-coprime"}[] {uses "deg-mul"}[]
:::
