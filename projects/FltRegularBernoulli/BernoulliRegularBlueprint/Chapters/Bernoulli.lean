import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Generalised Bernoulli numbers" =>

This chapter introduces the generalised Bernoulli numbers $`B_{n,\chi}` attached to
a Dirichlet character $`\chi` and records the properties of these numbers needed for
the analytic formula for $`\hminus`.

# Definition

We follow Washington's explicit formula (Washington (4.1), Diekmann Prop. 45) rather
than the generating-function description: the explicit form is what is used
throughout, and it makes the dependence on the polynomial $`B_n(X)` manifest. Recall
that $`B_n(X) \in \mathbb{Q}[X]` denotes the $`n`-th Bernoulli polynomial.

:::definition "def:gen-bernoulli" (lean := "BernoulliRegular.BernoulliGen")
**Generalised Bernoulli number.** Let $`N \ge 1`, let $`R` be a commutative
$`\mathbb{Q}`-algebra and let $`\chi : (\mathbb{Z}/N\mathbb{Z}) \to R` be a Dirichlet
character (with $`\chi(0) = 0`). The *generalised Bernoulli number* attached to
$`\chi` in degree $`n \in \mathbb{N}` is
$$`B_{n,\chi} \;:=\; N^{\,n-1}\,\sum_{a \in \mathbb{Z}/N\mathbb{Z}} \chi(a)\,B_n\!\left(\frac{a}{N}\right) \;\in\; R,`
where $`a` is identified with its representative in $`\{0,1,\dots,N-1\}`, and
$`B_n(a/N) \in \mathbb{Q}` is sent to $`R` along $`\mathbb{Q} \to R`. For the trivial
character one recovers the classical Bernoulli number: $`B_{n,\mathbf{1}} = B_n`.

{uses "def:dirichlet-character"}[]
:::

# Vanishing in degree 0

:::proposition "prop:gen-bernoulli-zero" (lean := "BernoulliRegular.BernoulliGen_zero_of_ne_one")
**$`B_{0,\chi} = 0` for non-trivial $`\chi`.** Let $`R` be an integral domain and let
$`\chi` be a Dirichlet character modulo $`N \ge 1` valued in $`R` with
$`\chi \ne \mathbf{1}`. Then $`B_{0,\chi} = 0`.

{uses "def:gen-bernoulli"}[]
:::

:::proof "prop:gen-bernoulli-zero"
The polynomial $`B_0(X) = 1` is the constant polynomial, so its evaluation at $`a/N`
equals $`1` and the algebra map sends it to $`1 \in R`. Substituting into the
definition, $`B_{0,\chi} = \sum_{a \in \mathbb{Z}/N\mathbb{Z}} \chi(a)`. For any
non-trivial character $`\chi` of a finite abelian group, this character sum vanishes:
pick $`b` with $`\chi(b) \ne 1` and observe that the substitution $`a \mapsto a b`
multiplies the sum by $`\chi(b)`, which is only consistent with
$`\chi(b) \cdot \Sigma = \Sigma` if $`\Sigma = 0`, since $`1 - \chi(b)` is a nonzero
element of the integral domain $`R`.
:::

# The first generalised Bernoulli number

The case $`n = 1` is the one that appears in the analytic formula for $`\hminus`; we
record three forms used throughout.

:::lemma_ "lem:gen-bernoulli-one-intermediate" (lean := "BernoulliRegular.BernoulliGen_one_of_ne_one")
**Intermediate form for $`B_{1,\chi}`.** Let $`R` be an integral domain and
$`\chi : (\mathbb{Z}/N\mathbb{Z}) \to R` a non-trivial Dirichlet character. Then
$$`B_{1,\chi} \;=\; \sum_{a \in \mathbb{Z}/N\mathbb{Z}} \chi(a)\,\frac{a}{N}.`

{uses "def:gen-bernoulli"}[]
:::

:::proof "lem:gen-bernoulli-one-intermediate"
Since $`B_1(X) = X - \tfrac12` and the exponent $`1 - 1 = 0` in the definition makes
the leading $`N^{n-1}` factor equal to $`1`,
$$`B_{1,\chi} = \sum_a \chi(a) \cdot \frac{a}{N} - \sum_a \chi(a) \cdot \frac{1}{2}.`
The second sum equals $`\tfrac12 \cdot \sum_a \chi(a)`, which is zero for non-trivial
$`\chi` by the character-sum identity used in {bpref "prop:gen-bernoulli-zero"}[].
:::

:::lemma_ "lem:gen-bernoulli-one-cleared" (lean := "BernoulliRegular.natCast_mul_BernoulliGen_one_of_ne_one")
**Cleared form of $`B_{1,\chi}`.** For $`\chi` as in the previous lemma,
$$`N \cdot B_{1,\chi} \;=\; \sum_{a \in \mathbb{Z}/N\mathbb{Z}} \chi(a)\,a,`
an identity valid in any commutative $`\mathbb{Q}`-algebra (denominators have been
cleared).

{uses "lem:gen-bernoulli-one-intermediate"}[]
:::

:::proof "lem:gen-bernoulli-one-cleared"
Multiply the previous identity through by $`N` and use that the algebra map
$`\mathbb{Q} \to R` commutes with multiplication by $`N \in \mathbb{N}`.
:::

:::proposition "prop:gen-bernoulli-one-even" (lean := "BernoulliRegular.BernoulliGen_one_eq_zero_of_even_ne_one")
**Parity vanishing at $`n = 1`.** Let $`R` be an integral domain in which
$`2 \ne 0` and let $`\chi` be a non-trivial *even* Dirichlet character modulo
$`N > 1` valued in $`R`, with $`N` invertible in $`R`. Then $`B_{1,\chi} = 0`.

{uses "lem:gen-bernoulli-one-cleared"}[] {uses "def:even-odd"}[]
:::

:::proof "prop:gen-bernoulli-one-even"
Reindexing the sum in {bpref "lem:gen-bernoulli-one-cleared"}[] by $`a \mapsto -a`
and using $`\chi(-a) = \chi(-1) \chi(a) = \chi(a)` (because $`\chi` is even),
$$`\sum_a \chi(a)\,a \;=\; \sum_a \chi(a)\,(-a).\mathrm{val},`
where $`(-a).\mathrm{val}` denotes the canonical representative in $`\{0,\dots,N-1\}`.
Adding the two expressions,
$$`2 \sum_a \chi(a)\,a \;=\; \sum_a \chi(a)\,\bigl(a + (-a).\mathrm{val}\bigr).`
The pairing identity in $`\mathbb{Z}/N\mathbb{Z}` states that
$`a.\mathrm{val} + (-a).\mathrm{val}` equals $`0` when $`a = 0` and $`N` otherwise.
Substituting,
$$`2 \sum_a \chi(a)\,a \;=\; N \cdot \sum_{a \ne 0} \chi(a) \;=\; N \cdot \Bigl(\sum_a \chi(a) - \chi(0)\Bigr) \;=\; 0,`
because $`\chi(0) = 0` and $`\sum_a \chi(a) = 0` for non-trivial $`\chi`. Since
$`2 \ne 0` in $`R`, the sum vanishes, and then $`N \ne 0` forces $`B_{1,\chi} = 0`
via {bpref "lem:gen-bernoulli-one-cleared"}[].
:::

This is the special case at $`n = 1` of the general parity phenomenon. For a
non-trivial Dirichlet character $`\chi` and $`n \ge 1` one has $`B_{n,\chi} = 0`
unless $`\chi(-1) = (-1)^n`. Indeed, using the defining sum and reindexing by
$`a\mapsto -a`, the Bernoulli polynomials satisfy $`B_n(1-X)=(-1)^n B_n(X)`, and the
character contributes the scalar $`\chi(-1)`; hence
$`B_{n,\chi}=\chi(-1)(-1)^n B_{n,\chi}`. If $`\chi(-1)\ne (-1)^n`, the scalar
multiplying $`B_{n,\chi}` is not $`1`, so $`B_{n,\chi}=0`.

In particular: if $`\chi` is odd, $`B_{n,\chi}` can be non-zero only for odd $`n`; if
$`\chi` is even, only for even $`n`. Downstream this is used in two places: (i) the
cleared form of the analytic formula for $`\hminus` runs only over odd characters,
because their $`B_{1,\chi}` are the only non-vanishing terms; and (ii) the odd
special-value formula depends on the same parity constraint.

# Congruences with classical Bernoulli numbers

The remaining results in this chapter concern the classical Bernoulli numbers
$`B_n \in \mathbb{Q}` and their $`p`-adic behaviour. They are needed in two ways: to
control the ordinary Bernoulli numbers below the boundary $`p-1`, and to handle the
exceptional contribution of the boundary character $`\omega^{p-2}` to the product
side of the analytic formula for $`\hminus`.

## Integrality below the boundary

:::theorem "thm:bernoulli-padicInt-below" (lean := "BernoulliRegular.bernoulli_mem_padicInt_of_lt_sub_one")
**$`p`-integrality of $`B_k` for $`k < p - 1`.** Let $`p` be an odd prime and let
$`0 \le k < p - 1`. Then $`B_k \in \mathbb{Q}` lies in $`\mathbb{Z}_p`; equivalently,
there exists $`z \in \mathbb{Z}_p` with $`B_k = z` in $`\mathbb{Q}_p`.

{uses "def:gen-bernoulli"}[]
:::

:::proof "thm:bernoulli-padicInt-below"
Strong induction on $`k`. The base case $`k = 0` is $`B_0 = 1 \in \mathbb{Z}_p`. For
the inductive step assume $`k \ge 1` and that $`B_j \in \mathbb{Z}_p` for all $`j < k`.
The recursion $`\sum_{j=0}^{k} \binom{k+1}{j} B_j = 0` extracts the top term, and
after rearrangement, $`(k + 1)\,B_k = -\sum_{j = 0}^{k - 1} \binom{k+1}{j}\,B_j`. By
the induction hypothesis each $`B_j` is a $`p`-adic integer. The binomial
coefficients $`\binom{k+1}{j}` are integers, hence are also $`p`-adic integers. So
the right-hand side is in $`\mathbb{Z}_p`. Finally $`k + 1 \le p - 1 < p` means
$`p \nmid (k+1)`, so $`k + 1` is a unit in $`\mathbb{Z}_p` and we may divide. Hence
$`B_k \in \mathbb{Z}_p`.
:::

:::corollary "cor:bernoulli-den-coprime" (lean := "BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one")
**Denominator coprimality.** For $`p` an odd prime and $`0 \le n < p - 1`,
$$`p \nmid (B_n)_{\mathrm{den}}.`

{uses "thm:bernoulli-padicInt-below"}[]
:::

:::proof "cor:bernoulli-den-coprime"
By {bpref "thm:bernoulli-padicInt-below"}[] the $`p`-adic absolute value of $`B_n` is
at most $`1`, so the denominator of $`B_n` is a $`p`-unit. Equivalently, the cast
$`((B_n)_{\mathrm{den}} : \mathbb{Z}_p)` is a unit, which is equivalent to
$`p \nmid (B_n)_{\mathrm{den}}`.
:::

## Von Staudt–Clausen at the boundary

The recursion that pushes $`B_k` into $`\mathbb{Z}_p` for $`k < p - 1` breaks down at
$`k = p - 1`: the scalar $`k + 1 = p` is no longer a $`p`-unit. The Bernoulli number
$`B_{p-1}` has $`p` in its denominator, and the classical Von Staudt–Clausen theorem
pins this denominator down exactly.

:::theorem "thm:von-staudt-clausen" (lean := "BernoulliRegular.bernoulli_pSubOne_add_inv_p_mem_padicInt")
**Von Staudt–Clausen, $`p`-local form at $`n = p - 1`.** For $`p` an odd prime,
$$`B_{p-1} + \frac{1}{p} \;\in\; \mathbb{Z}_p.`
Equivalently, $`p \cdot B_{p-1} \equiv -1 \pmod{p}` as $`p`-adic integers.

{uses "thm:bernoulli-padicInt-below"}[]
:::

:::proof "thm:von-staudt-clausen"
Specialise the Bernoulli recursion at $`n = p`:
$`\sum_{k = 0}^{p - 1} \binom{p}{k}\,B_k = 0`. The top index $`k = p - 1` contributes
$`\binom{p}{p - 1} \cdot B_{p-1} = p \cdot B_{p-1}`. Isolating this and splitting off
$`k = 0` (which contributes $`B_0 = 1`) gives
$`p \cdot B_{p-1} + 1 = -\sum_{k = 1}^{p - 2} \binom{p}{k}\,B_k`. For each
$`1 \le k \le p - 2`, the binomial coefficient $`\binom{p}{k}` is divisible by $`p`;
write $`\binom{p}{k} = p \cdot c_k` for some $`c_k \in \mathbb{N}`. By
{bpref "thm:bernoulli-padicInt-below"}[], each $`B_k` for $`1 \le k \le p - 2` is a
$`p`-adic integer (note that $`p - 2 < p - 1`). Therefore the right-hand side is $`p`
times an element of $`\mathbb{Z}_p`, and dividing by $`p` (cancellable in
$`\mathbb{Q}_p`) yields
$`B_{p - 1} + \frac{1}{p} = -\sum_{k=1}^{p-2} c_k \cdot B_k \in \mathbb{Z}_p`, as
claimed.
:::

## The boundary character omega-to-the-minus-one

The product side of the analytic formula for $`\hminus` runs over odd Dirichlet
characters $`\chi` modulo $`p`; identifying characters with powers of the Teichmüller
character $`\omega`, every odd $`\chi` has the form $`\omega^j` for some odd
$`j \in \{1, 3, \dots, p - 2\}`. The contribution $`B_{1,\omega^j}` is $`p`-integral
for $`j \in \{1, 3, \dots, p - 4\}` (by the same recursion-based analysis used above,
extended to character twists); the exceptional case is $`j = p - 2` — the
"inverse Teichmüller" character $`\omega^{-1}`, which is the one boundary character
that sees the Von Staudt–Clausen pole. We use the $`\mathbb{Q}_p`-valued Teichmüller
character $`\omega : (\mathbb{Z}/p\mathbb{Z})^\times \to \mathbb{Q}_p^\times`.

:::theorem "thm:boundary-character-bernoulli" (lean := "BernoulliRegular.bernoulliGen_teichmuller_inverse_eq_p_sub_one_div_p_add_padicInt")
**Boundary character contribution.** For $`p` an odd prime there exists
$`z \in \mathbb{Z}_p` with
$$`B_{1,\omega^{p-2}} \;=\; \frac{p - 1}{p} \;+\; z.`
In particular, $`B_{1,\omega^{-1}}` shares the $`p`-adic pole of the classical
$`B_{p-1}` from {bpref "thm:von-staudt-clausen"}[], with residue $`(p - 1)/p`.

{uses "lem:gen-bernoulli-one-cleared"}[] {uses "def:teichmuller"}[]
:::

:::proof "thm:boundary-character-bernoulli"
Set $`\chi := \omega^{p - 2}` regarded as a Dirichlet character modulo $`p` valued in
$`\mathbb{Q}_p`, with underlying $`\mathbb{Z}_p`-valued lift
$`\chi_{\mathbb{Z}_p} := \omega_{\mathbb{Z}_p}^{p - 2}`. Since $`p` is odd,
$`p - 2 \in \{1, \dots, p - 2\}` is not divisible by $`p - 1`, so
$`\chi \ne \mathbf{1}`; the cleared form {bpref "lem:gen-bernoulli-one-cleared"}[]
gives
$$`p \cdot B_{1,\chi} \;=\; \sum_{a \in \mathbb{Z}/p\mathbb{Z}} \chi(a)\,a \;=:\; S \;\in\; \mathbb{Z}_p,`
the last identity because each summand is the product of a $`\mathbb{Z}_p`-valued
character value and an integer representative. We compute $`S` modulo $`p`. For
$`a = 0`, the summand is $`0` because $`\chi_{\mathbb{Z}_p}(0) = 0`. For $`a \ne 0`,
the Teichmüller character lifts the identity modulo $`p`:
$`\omega_{\mathbb{Z}_p}(a) \equiv a \pmod{p}`. Therefore
$`\chi_{\mathbb{Z}_p}(a) \equiv a^{p - 2} \pmod{p}`, and hence
$`\chi_{\mathbb{Z}_p}(a) \cdot a \equiv a^{p - 1} \equiv 1 \pmod{p}` by Fermat's
little theorem. Summing, $`S \equiv \sum_{a \ne 0} 1 = p - 1 \pmod{p}`. So
$`S - (p - 1) \in p \cdot \mathbb{Z}_p`; write $`S - (p - 1) = p \cdot z` with
$`z \in \mathbb{Z}_p`. Then
$`p \cdot B_{1,\chi} = S = (p - 1) + p \cdot z = p \cdot \bigl(\frac{p - 1}{p} + z\bigr)`,
and cancelling the unit $`p \in \mathbb{Q}_p^{\times}` gives the claim.
:::

The remaining bridge to the analytic formula for $`\hminus` is Euler's identity
expressing $`L(1 - n, \chi)` in terms of $`B_{n,\chi}`; this is the subject of the
next chapter.
