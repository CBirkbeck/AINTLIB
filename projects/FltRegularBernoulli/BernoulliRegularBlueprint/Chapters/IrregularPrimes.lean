import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Infinitely many irregular primes" =>

This chapter records the Carlitz route from Kummer congruences to the infinitude of
irregular primes. The theorem proved in Lean is that
$`\{p : \mathbb{N} \mid p\text{ is prime and }p\text{ is not regular}\}` is infinite.
The proof is by finite-set escape: given a finite set $`S` of candidate irregular
primes, construct a new prime $`p\notin S` dividing the numerator of a suitable
divided Bernoulli number $`B_M/M`, then use Kummer congruences and Kummer's criterion
to show that $`p` is irregular.

# The divided Kummer congruence

The Carlitz argument needs a Kummer congruence for the divided Bernoulli numbers
$`B_m/m` with no upper bound on the exponents.

:::theorem "thm:full-divided-kummer" (lean := "BernoulliRegular.bernoulli_div_sModEq_of_modEq_full")
**Full divided Kummer congruence.** Let $`p` be an odd prime. Let $`m,n>0` be even
natural numbers such that $`m \equiv n \pmod {p-1}` and $`(p-1)\nmid n`. Then there
exists $`z\in \mathbb{Z}_p` with $`\frac{B_m}{m} - \frac{B_n}{n} = pz` in
$`\mathbb{Q}_p`.
:::

:::proof "thm:full-divided-kummer"
The proof first reduces to $`p\ge 5`. If $`p=3`, then $`p-1=2` divides every even
exponent $`n`, contradicting the non-boundary hypothesis $`(p-1)\nmid n`.

For $`p\ge 5`, the proof is a strengthened elementary Voronoi argument. The first
input is the strong Faulhaber congruence
$`\sum_{x=0}^{p-1} x^h - pB_h \in h p^2\mathbb{Z}_p` for positive even $`h` with
$`(p-1)\nmid h`. In Lean this is the strong Faulhaber lemma
`sum_range_pow_sub_p_mul_bernoulli_strong`. It expands the power sum by mathlib's
Faulhaber formula and proves that every non-leading summand contains the required
$`hp^2`-factor. The delicate terms are handled with von Staudt-Clausen denominator
control and binomial divisibility.

The second input is the strong Voronoi congruence
$`(a^h-1)\frac{B_h}{h} - a^{h-1}\sum_{x=0}^{p-1} x^{h-1}\left\lfloor\frac{xa}{p}\right\rfloor \in p\mathbb{Z}_p`
for every $`a` prime to $`p`, formalized as the strong Voronoi theorem
`voronoi_congruence_mod_p_strong`. This substitutes the strong Faulhaber congruence
into a higher-modulus Voronoi sum identity and cancels the nonzero rational factor
$`hp` in $`\mathbb{Q}_p`.

Next choose a generator $`g` of $`(\mathbb{Z}/p\mathbb{Z})^\times`, represented by a
natural number $`a`. Since $`g` has order $`p-1`, the condition $`(p-1)\nmid h`
implies $`a^h-1` is a $`p`-adic unit. Dividing the strong Voronoi congruence by this
unit proves $`\frac{B_h}{h}\in \mathbb{Z}_p`, recorded as the Voronoi integrality
lemma `bernoulli_div_self_mem_padicInt_of_not_sub_one_dvd_voronoi`.

Finally apply the strong Voronoi congruence to $`m` and $`n`. The factors $`a^m` and
$`a^n` agree because $`m\equiv n\pmod{p-1}`, and the floor sums are congruent modulo
$`p` because their predecessor exponents are congruent; this is the floor-sum
comparison `voronoi_floor_sum_sModEq_of_pred_modEq`. The already-proved
$`p`-integrality of $`B_m/m` and $`B_n/n` lets the comparison be carried out inside
$`\mathbb{Z}_p`, and the difference is a multiple of $`p` in $`\mathbb{Q}_p`.
:::

# From divided Bernoulli numerators to irregularity

The finite-set construction produces a prime divisor of the numerator of $`B_M/M`,
not directly a Kummer-range numerator $`B_{2k}`. The next result is the bridge from
that unbounded witness to the usual definition of an irregular prime.

:::theorem "thm:carlitz-divisor-criterion" (lean := "BernoulliRegular.not_isRegularPrime_iff_exists_dvd_bernoulli_div_self_num")
**Carlitz divisor criterion.** Let $`q` be an odd prime. Then $`q` is not regular if
and only if there is a positive even integer $`m` such that
$`q \mid \operatorname{num}\left(\frac{B_m}{m}\right)`.

{uses "thm:full-divided-kummer"}[] {uses "thm:kummer-final"}[]
:::

:::proof "thm:carlitz-divisor-criterion"
If $`q` is not regular, Kummer's criterion gives a Kummer-range index $`k` with
$`1\le k`, $`2k\le q-3`, $`q\mid (B_{2k})_{\mathrm{num}}`. Set $`m=2k`. The range
bound implies $`q\nmid m`, so $`m` is a unit in $`\mathbb{Z}_q`. Dividing by this
unit preserves numerator divisibility, giving
$`q\mid \operatorname{num}\left(\frac{B_m}{m}\right)`. The Lean helper is the
divisibility-through-division lemma `dvd_bernoulli_div_self_num_of_dvd_bernoulli_num`.

Conversely assume $`q\mid\operatorname{num}(B_m/m)` for some positive even $`m`. Von
Staudt-Clausen excludes the boundary: $`(q-1)\nmid m`, because if $`q-1\mid m`, then
$`q` cannot divide the reduced numerator of $`B_m/m`. This is the boundary-exclusion
lemma `sub_one_not_dvd_of_dvd_num_bernoulli_div_self`. Let $`m'` be the least
nonnegative residue of $`m` modulo $`q-1`. The boundary exclusion makes $`m'>0`, and
parity gives that $`m'` is even. It also satisfies $`m'<q-1`, hence $`1\le m'/2`,
$`2(m'/2)\le q-3`.

Apply {bpref "thm:full-divided-kummer"}[] to $`m` and $`m'`. Since
$`B_m/m\equiv B_{m'}/m'\pmod q`, the numerator divisibility transfers from $`B_m/m` to
$`B_{m'}/m'`, and then to $`B_{m'}`. The transfer is formalized by the $`p`-adic
numerator-transfer lemma `dvd_bernoulli_num_of_padic_congruent_residue`. Now
$`m'=2(m'/2)` lies in Kummer's range, so Kummer's criterion gives that $`q` is not
regular.
:::

# The finite-set construction

The escape argument starts from a finite set $`S` and builds an even integer which is
divisible by $`q-1` for every prime $`q\in S`.

:::definition "def:irregular-base" (lean := "BernoulliRegular.irregularBase")
**Divisor-closed base.** For a finite set $`S\subset\mathbb{N}`, set
$$`C(S)=2\cdot \bigl(\max(3,\sup S)\bigr)!.`
:::

:::proof "def:irregular-base"
The factor $`2` makes $`C(S)` even, and the factorial makes $`q-1\mid C(S)` for every
prime $`q\in S`. The stronger closure property used internally is that if a prime
$`q` divides $`C(S)`, then $`q-1\mid C(S)` as well.
:::

:::theorem "thm:numerator-prime-for-carlitz-base" (lean := "BernoulliRegular.exists_numerator_prime_for_carlitz_base")
**A new numerator prime outside a finite set.** For every finite set
$`S\subset\mathbb{N}`, there are natural numbers $`M` and $`p` such that $`p` is
prime, $`p\ne 2`, $`M>0`, $`M` is even,
$`\forall q\in S,\ q\text{ prime}\Longrightarrow q-1\mid M`,
$`p\mid \operatorname{num}\left(\frac{B_M}{M}\right)`, and $`p\notin S`.

{uses "def:irregular-base"}[]
:::

:::proof "thm:numerator-prime-for-carlitz-base"
Start with $`C=C(S)`. The growth theorem for divided Bernoulli numbers
`exists_large_even_multiple_abs_bernoulli_div_self_gt_one` chooses $`t` such that
$`\left|\frac{B_{C2^t}}{C2^t}\right|>1`. Set $`M=C2^t`. This $`M` is positive and
even, and it is still divisible by $`q-1` for every prime $`q\in S`.

Since the rational number $`B_M/M` has absolute value greater than $`1`, its reduced
numerator has absolute value greater than $`1`, hence has a prime divisor $`p`, by the
numerator-prime lemma `exists_prime_dvd_num_of_one_lt_abs`.

It remains to prove that this prime was not already in $`S`. Suppose $`p\in S`. Then
$`p-1\mid M` by construction. But von Staudt-Clausen gives the exclusion
$`p-1\mid M \Longrightarrow p\nmid \operatorname{num}\left(\frac{B_M}{M}\right)`,
namely the von Staudt numerator-exclusion lemma
`not_dvd_num_bernoulli_div_self_of_sub_one_dvd`. This contradicts the choice of $`p`.
The same exclusion also proves $`p\ne 2`, since $`p=2` would make $`p-1=1` divide
$`M`.
:::

# Escaping every finite set

:::theorem "thm:irregular-prime-outside-finite-set" (lean := "BernoulliRegular.exists_not_isRegularPrime_not_mem_carlitz")
**Finite-set escape.** For every finite set $`S\subset\mathbb{N}`, there is a prime
$`p\notin S` such that $`p` is not regular.

{uses "thm:numerator-prime-for-carlitz-base"}[] {uses "thm:carlitz-divisor-criterion"}[]
:::

:::proof "thm:irregular-prime-outside-finite-set"
Apply {bpref "thm:numerator-prime-for-carlitz-base"}[] to $`S`, obtaining a prime
$`p\notin S` and a positive even $`M` with
$`p\mid\operatorname{num}\left(\frac{B_M}{M}\right)`. The same theorem gives
$`p\ne 2`. Therefore the Carlitz divisor criterion
{bpref "thm:carlitz-divisor-criterion"}[] applies and proves that $`p` is not regular.
:::

# Infinitude

:::theorem "thm:infinitely-many-irregular-primes" (lean := "BernoulliRegular.infinite_not_isRegularPrime")
**Infinitely many irregular primes.** The set
$`\{p:\mathbb{N} \mid p\text{ is prime and }p\text{ is not regular}\}` is infinite.

{uses "thm:irregular-prime-outside-finite-set"}[]
:::

:::proof "thm:infinitely-many-irregular-primes"
Assume the set is finite, and let $`S` be a finite set containing all of its
elements. By {bpref "thm:irregular-prime-outside-finite-set"}[], there is a prime
$`p\notin S` which is not regular. This contradicts the defining property of $`S`.
Hence no finite set covers all irregular primes, so the set is infinite. The
finite-set-to-infinite conversion is the elementary lemma that no finite cover
implies infinitude `infinite_of_forall_finite_set_not_cover`.
:::

The checked proof contains no bundled Kummer provider or side-condition package. The
only source bridge into irregularity is Kummer's criterion, and the unbounded
congruence used by Carlitz is the public theorem {bpref "thm:full-divided-kummer"}[].
