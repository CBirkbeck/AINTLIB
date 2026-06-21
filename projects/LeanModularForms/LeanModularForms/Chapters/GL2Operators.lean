import Verso
import VersoManual
import VersoBlueprint
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GLn.Basic
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The GL₂ Hecke operators" =>

Specialising the abstract construction to the arithmetic pair attached to $`\mathrm{GL}_n`
produces the classical Hecke operators. This chapter sets up that pair, its Hecke ring, the
diagonal double cosets that turn out to span it, and, for $`n=2`, the generators $`T(a,d)` and
$`T(m)` of Shimura's multiplication table \[Sh, §3.1\].

:::definition "GL-pair" (lean := "HeckeRing.GLn.GL_pair")
*The arithmetic Hecke pair.*
For $`n\ge 1` the *arithmetic Hecke pair* for $`\mathrm{GL}_n` is the triple with group
$`G=\mathrm{GL}_n(\mathbb{Q})`, subgroup $`H=SL_n(\mathbb{Z})`, and submonoid $`\Delta` equal
to the monoid of integer matrices with positive determinant, regarded inside
$`\mathrm{GL}_n(\mathbb{Q})`. One has $`SL_n(\mathbb{Z})\le\Delta`, since elements of
$`SL_n(\mathbb{Z})` are integral with determinant $`1`, and $`\Delta\le\operatorname{Comm}(SL_n(\mathbb{Z}))`,
the commensurator of $`SL_n(\mathbb{Z})`: an integer matrix $`\alpha` of determinant $`d>0`
conjugates the principal congruence subgroup of level $`d` into $`SL_n(\mathbb{Z})`, so
$`SL_n(\mathbb{Z})` and $`\alpha\,SL_n(\mathbb{Z})\,\alpha^{-1}` are commensurable
\[Sh, §3.1, Lemma 3.10\]. These two inclusions make the triple a Hecke pair.

Depends on: {uses "hecke-pair"}[]
:::

:::definition "hecke-algebra" (lean := "HeckeRing.GLn.HeckeAlgebra")
*The $`\mathrm{GL}_n` Hecke algebra.*
For $`n\ge 1` the *$`\mathrm{GL}_n` Hecke algebra* $`\mathcal{H}_n` is the Hecke ring
$`\mathbb{T}` of the arithmetic Hecke pair of $`\mathrm{GL}_n`, that is, the free
$`\mathbb{Z}`-module on the double cosets $`SL_n(\mathbb{Z})\backslash\Delta/SL_n(\mathbb{Z})`
equipped with its convolution product. For $`n=2` this is the ring whose structure is
described by Shimura's Theorem 3.24.

Depends on: {uses "GL-pair"}[] {uses "hecke-ring-carrier"}[]
:::

:::definition "T-diag" (lean := "HeckeRing.GLn.T_diag")
*Diagonal double coset.*
Let $`a=(a_1,\dots,a_n)` be an $`n`-tuple of positive integers. The associated
*diagonal double coset* is the double coset
$$`
  SL_n(\mathbb{Z})\,\operatorname{diag}(a_1,\dots,a_n)\,SL_n(\mathbb{Z})
`
of the diagonal matrix $`\operatorname{diag}(a_1,\dots,a_n)` in
$`SL_n(\mathbb{Z})\backslash\Delta/SL_n(\mathbb{Z})`. Every double coset of the arithmetic
pair admits such a diagonal representative, with elementary divisors $`a_1\mid a_2\mid\dots\mid a_n`,
by the theory of Smith normal form \[Sh, §3.1\].

Depends on: {uses "GL-pair"}[] {uses "hecke-coset"}[]
:::

:::definition "T-elem" (lean := "HeckeRing.GLn.T_elem")
*Diagonal basis element.*
For an $`n`-tuple $`a=(a_1,\dots,a_n)` of positive integers, the *diagonal basis element*
is the standard basis vector of $`\mathcal{H}_n` attached to the diagonal double coset of
$`\operatorname{diag}(a_1,\dots,a_n)`; that is, the basis element with coefficient $`1` at that
double coset and $`0` elsewhere.

Depends on: {uses "T-diag"}[] {uses "T-single"}[] {uses "hecke-algebra"}[]
:::

:::definition "T-ad" (lean := "HeckeRing.GL2.T_ad")
*$`T(a,d)`.*
Let $`n=2`. For positive integers $`a,d` with $`a\mid d`, the operator $`T(a,d)` is the diagonal
basis element of $`\mathcal{H}_2` attached to $`\operatorname{diag}(a,d)`. For all other pairs
$`(a,d)` — when $`a` or $`d` vanishes, or when $`a\nmid d` — one sets $`T(a,d)=0`; the
divisibility constraint $`a\mid d` records the elementary-divisor normalisation of the
diagonal double coset.

Depends on: {uses "T-elem"}[]
:::

:::definition "T-pp" (lean := "HeckeRing.GL2.T_pp")
*$`T(p,p)`.*
For a positive integer $`p`, the operator $`T(p,p)` is defined as $`T(p,p)=T(a,d)` with $`a=d=p`.
When $`p` is prime this is the central, scalar double coset of $`pI`, the basis element attached
to the scalar matrix $`\operatorname{diag}(p,p)`.

Depends on: {uses "T-ad"}[]
:::

:::definition "T-sum" (lean := "HeckeRing.GL2.T_sum")
*$`T(m)`.*
For a positive integer $`m`, Shimura's operator $`T(m)` is the sum
$$`
  T(m) \;=\; \sum_{a\,\mid\, m} T\!\left(a,\tfrac{m}{a}\right)
`
over all positive divisors $`a` of $`m`, where each summand is the operator
$`T\!\left(a,\tfrac{m}{a}\right)` of $`\mathcal{H}_2`. Only the divisor pairs $`(a,m/a)` with
$`a\mid m/a` contribute, the remaining terms vanishing by definition of $`T(a,d)`.

Depends on: {uses "T-ad"}[]
:::

:::lemma_ "T-ad-one-one" (lean := "HeckeRing.GL2.T_ad_one_one")
*$`T(1,1)` is the identity.*
In $`\mathcal{H}_2` one has $`T(1,1)=1`, the multiplicative identity of the Hecke algebra.

Depends on: {uses "T-ad"}[] {uses "one-def"}[]
:::

:::proof "T-ad-one-one"
Since $`1\mid 1` and both entries are positive, $`T(1,1)` is the diagonal basis element of
$`\operatorname{diag}(1,1)`, which is the identity matrix. Its diagonal double coset is
therefore the trivial double coset $`SL_2(\mathbb{Z})`, and the basis element attached to the
trivial double coset is exactly the identity of the Hecke ring.

Uses: {uses "T-ad"}[] {uses "one-def"}[]
:::

:::lemma_ "T-sum-prime" (lean := "HeckeRing.GL2.T_sum_prime")
*$`T(p)` at a prime.*
For a prime $`p` one has $`T(p)=T(1,p)`.

Depends on: {uses "T-sum"}[] {uses "T-ad"}[]
:::

:::proof "T-sum-prime"
The positive divisors of a prime $`p` are $`1` and $`p`, so the defining sum for $`T(p)` has the
two terms $`T(1,p)` and $`T(p,1)`. The second vanishes: $`p\nmid 1` since $`p>1`, so $`T(p,1)=0`
by definition. Hence $`T(p)=T(1,p)`.

Uses: {uses "T-sum"}[] {uses "T-ad"}[]
:::
