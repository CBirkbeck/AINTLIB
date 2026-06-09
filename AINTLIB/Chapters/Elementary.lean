import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.IntegralDomain
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.LucasLehmer

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elementary Number Theory" =>

This chapter covers the elementary core of number theory as it is formalised in mathlib: divisibility and the Euclidean algorithm, the fundamental theorem of arithmetic, congruences and the structure of the residue rings $`\mathbb{Z}/n\mathbb{Z}`, arithmetic functions and Dirichlet convolution, quadratic residues and reciprocity, and the classical Diophantine results on sums of squares, Pythagorean triples, and Fermat and Mersenne numbers. Throughout, $`p` denotes a prime, $`\mathbb{Z}` the integers, and for a positive integer $`n` we write $`\mathbb{Z}/n\mathbb{Z}` for the ring of integers modulo $`n` and $`(\mathbb{Z}/n\mathbb{Z})^\times` for its group of units. Every proof sketch below follows the argument used in the cited mathlib declaration, naming the lemmas that proof actually invokes.

# Divisibility, gcd, and the fundamental theorem of arithmetic

:::theorem "bezout" (lean := "Int.gcd_eq_gcd_ab")
*(Bézout's identity.)* For integers $`x` and $`y` there exist integers $`a` and $`b` with
$$`\gcd(x, y) = x\,a + y\,b.`
In particular $`\gcd(x,y)` is the smallest positive integer expressible as an integer combination of $`x` and $`y`, and $`x` and $`y` are coprime iff $`1` is such a combination.
:::

:::proof "bezout"
The witnesses $`a = \mathrm{gcdA}(x,y)` and $`b = \mathrm{gcdB}(x,y)` are produced by the extended Euclidean algorithm, which runs the ordinary Euclidean algorithm while carrying along the coefficients expressing each successive remainder as a combination of $`x` and $`y`. The integer statement reduces to the case of natural-number arguments, where the loop invariant of the extended algorithm is exactly the identity $`\gcd = x\,a + y\,b`; the four sign cases for the signs of $`x` and $`y` follow by substituting negations.
:::

:::theorem "euclid-lemma" (lean := "Nat.Prime.dvd_mul")
*(Euclid's lemma.)* For a prime $`p` and naturals $`m, n`,
$$`p \mid mn \iff p \mid m \ \text{or}\ p \mid n.`
:::

:::proof "euclid-lemma"
The non-trivial direction supposes $`p \mid mn` but $`p \nmid m`. Since $`p` is prime, $`p \nmid m` is equivalent to $`p` being coprime to $`m`. A number coprime to $`m` that divides the product $`mn` must divide the cofactor $`n` — this is the coprime-cancellation lemma, whose proof rests on Bézout's identity ({uses "bezout"}[]): writing $`1 = pa + mb` and multiplying by $`n` exhibits $`n = pan + (mn)b` as a multiple of $`p`. The reverse direction is immediate, as $`p \mid m` or $`p \mid n` each gives $`p \mid mn`.
:::

:::theorem "prime-dvd-pow" (lean := "Nat.Prime.dvd_of_dvd_pow")
For a prime $`p` and naturals $`m, n`, if $`p \mid m^{\,n}` then $`p \mid m`.
:::

:::proof "prime-dvd-pow"
Induct on $`n`, repeatedly applying Euclid's lemma ({uses "euclid-lemma"}[]). For $`n = 0` the hypothesis $`p \mid 1` is impossible; for the step, $`p \mid m^{\,n+1} = m \cdot m^{\,n}` forces $`p \mid m` or $`p \mid m^{\,n}`, and the latter yields $`p \mid m` by the inductive hypothesis.
:::

:::definition "factorization" (lean := "Nat.factorization")
For a positive integer $`n`, the *factorization* of $`n` is the finitely-supported function $`p \mapsto v_p(n)` whose support is the set of prime divisors of $`n` and which sends each prime $`p` to its multiplicity $`v_p(n)`, the $`p`-adic valuation of $`n` — equivalently the number of times $`p` occurs in the list of prime factors of $`n`.
:::

:::theorem "infinitude-of-primes" (lean := "Nat.exists_infinite_primes")
There are infinitely many primes: for every natural number $`n` there exists a prime $`p` with $`p \ge n`.
:::

:::proof "infinitude-of-primes"
This is Euclid's argument, in the form mathlib uses. Set $`p = \mathrm{minFac}(n! + 1)`, the smallest prime factor of $`n! + 1`; this is prime because $`n! + 1 \ne 1`. If we had $`p < n`, then $`p \mid n!` (as $`p` is one of the factors $`1, \dots, n`), and since also $`p \mid n! + 1` we would get $`p \mid 1`, contradicting primality. Hence $`p \ge n`.
:::

:::theorem "fta-existence" (lean := "Nat.prod_factorization_pow_eq_self")
*(Fundamental theorem of arithmetic — existence.)* Every positive integer $`n` is recovered from its factorization as the product over primes
$$`n = \prod_{p} p^{\,v_p(n)},`
a finite product since only finitely many exponents $`v_p(n)` are nonzero.
:::

:::proof "fta-existence"
By definition the factorization of $`n` records the multiplicities of $`n`'s prime factors ({uses "factorization"}[]). Reading the finitely-supported product $`\prod_p p^{\,v_p(n)}` off the multiset of prime factors turns it into the ordinary product of the list of prime factors of $`n`, and that product equals $`n`. (This list-product identity is the content of `Nat.prod_primeFactorsList`.)
:::

:::theorem "fta-uniqueness" (lean := "Nat.factorization_inj")
*(Fundamental theorem of arithmetic — uniqueness.)* A positive integer is determined by its factorization: if two positive integers have the same multiplicity $`v_p(\cdot)` at every prime $`p`, they are equal. Equivalently, the prime factorization of every positive integer is unique up to the order of the factors.
:::

:::proof "fta-uniqueness"
Suppose $`m, n > 0` have $`v_p(m) = v_p(n)` for all primes $`p`. Since the multiplicity $`v_p(\cdot)` is the number of occurrences of $`p` in the list of prime factors, equal multiplicities mean the prime-factor lists of $`m` and $`n` have the same count of every prime, hence are permutations of one another. Taking products of the two permuted lists — each of which equals its number ({uses "fta-existence"}[]) — gives $`m = n`. That the list of prime factors really consists of primes whose product is $`n` is where Euclid's lemma ({uses "euclid-lemma"}[]) enters, in establishing uniqueness of prime factorizations.
:::

# Congruences and the structure of the residue rings

:::theorem "lagrange-order" (lean := "orderOf_dvd_card, pow_card_eq_one")
*(Lagrange's theorem, order form.)* In a finite group $`G`, the order of any element $`x` divides $`|G|`; consequently $`x^{\,|G|} = 1`.
:::

:::proof "lagrange-order"
The cyclic subgroup $`\langle x\rangle` generated by $`x` has order $`\mathrm{ord}(x)`, and the group decomposes as $`G \cong (G/\langle x\rangle) \times \langle x\rangle` as a finite set, so $`|G| = [G : \langle x\rangle]\cdot\mathrm{ord}(x)`; thus $`\mathrm{ord}(x) \mid |G|`. Since the order is the least positive exponent with $`x^{\mathrm{ord}(x)} = 1`, divisibility of $`|G|` by $`\mathrm{ord}(x)` gives $`x^{\,|G|} = 1`.
:::

:::theorem "chinese-remainder" (lean := "ZMod.chineseRemainder")
*(Chinese remainder theorem.)* If $`m` and $`n` are coprime, then reduction modulo $`m` and modulo $`n` gives a ring isomorphism
$$`\mathbb{Z}/mn\mathbb{Z} \;\cong\; \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}.`
In particular, any pair of congruences $`x \equiv a \pmod{m}` and $`x \equiv b \pmod{n}` has a solution, unique modulo $`mn`.
:::

:::proof "chinese-remainder"
The map sending $`x \bmod mn` to the pair $`(x \bmod m,\ x \bmod n)` is a ring homomorphism. Its kernel consists of residues divisible by both $`m` and $`n`; as $`\gcd(m,n) = 1`, divisibility by both is divisibility by $`mn`, so the map is injective. Both sides have $`mn` elements, hence it is a bijection, and therefore a ring isomorphism; the explicit inverse on a pair $`(a, b)` is built from a simultaneous solution of the two congruences.
:::

:::definition "totient" (lean := "Nat.totient")
*Euler's totient function* $`\varphi(n)` counts the integers in $`\{0, 1, \dots, n-1\}` that are coprime to $`n`:
$$`\varphi(n) = \#\{\, a : 0 \le a < n,\ \gcd(n, a) = 1 \,\}.`
Equivalently, $`\varphi(n)` is the number of units of $`\mathbb{Z}/n\mathbb{Z}`, since a residue is a unit precisely when it is coprime to $`n`.
:::

:::lemma_ "totient-prime-pow" (lean := "Nat.totient_prime_pow")
For a prime $`p` and an exponent $`n \ge 1`,
$$`\varphi(p^{\,n}) = p^{\,n-1}(p - 1).`
:::

:::proof "totient-prime-pow"
By definition $`\varphi(p^{n})` counts the residues below $`p^{n}` coprime to $`p^{n}` ({uses "totient"}[]). A residue is coprime to $`p^{n}` exactly when it is not divisible by $`p`, so the coprime residues are obtained by deleting the multiples of $`p` from $`\{0, 1, \dots, p^{n}-1\}`. mathlib computes the count as the cardinality of the set difference: the multiples of $`p` below $`p^{n}` are the image of $`\{0, \dots, p^{n-1}-1\}` under $`x \mapsto px`, an injective map, so there are $`p^{n-1}` of them, leaving $`p^{n} - p^{n-1} = p^{n-1}(p-1)`.
:::

:::lemma_ "totient-prime" (lean := "Nat.totient_prime")
For a prime $`p`,
$$`\varphi(p) = p - 1.`
:::

:::proof "totient-prime"
This is the case $`n = 1` of the prime-power formula: $`\varphi(p) = \varphi(p^{1}) = p^{0}(p-1) = p - 1` ({uses "totient-prime-pow"}[]).
:::

:::theorem "totient-mul" (lean := "Nat.totient_mul")
*(Multiplicativity.)* If $`m` and $`n` are coprime, then
$$`\varphi(mn) = \varphi(m)\,\varphi(n).`
:::

:::proof "totient-mul"
Counting units, $`\varphi(k)` is the cardinality of $`(\mathbb{Z}/k\mathbb{Z})^\times` ({uses "totient"}[]). When $`\gcd(m,n) = 1`, the Chinese remainder isomorphism $`\mathbb{Z}/mn\mathbb{Z} \cong \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}` ({uses "chinese-remainder"}[]) induces a multiplicative isomorphism on unit groups, and the units of a product ring are the product of the unit groups. Hence $`|(\mathbb{Z}/mn\mathbb{Z})^\times| = |(\mathbb{Z}/m\mathbb{Z})^\times|\cdot|(\mathbb{Z}/n\mathbb{Z})^\times|`, which is the claim.
:::

:::theorem "totient-formula" (lean := "Nat.totient_eq_prod_factorization")
For $`n \ge 1`, the totient is given by the product over the distinct primes dividing $`n`:
$$`\varphi(n) = \prod_{p \mid n} p^{\,v_p(n) - 1}\,(p - 1).`
:::

:::proof "totient-formula"
The totient is multiplicative ({uses "totient-mul"}[]) and satisfies $`\varphi(1) = 1`, so its value is the product of its values on the prime-power factors $`p^{\,v_p(n)}` appearing in the factorization of $`n` ({uses "fta-existence"}[]). This is the general principle that a multiplicative arithmetic function is the product of its values over the prime powers of the factorization. Substituting the prime-power value $`\varphi(p^{\,v_p(n)}) = p^{\,v_p(n)-1}(p-1)` ({uses "totient-prime-pow"}[]) into that product gives the formula.
:::

:::theorem "fermat-little-units" (lean := "ZMod.pow_card_sub_one_eq_one")
For a prime $`p` and a nonzero residue $`a \in \mathbb{Z}/p\mathbb{Z}`,
$$`a^{\,p-1} = 1.`
:::

:::proof "fermat-little-units"
Since $`\mathbb{Z}/p\mathbb{Z}` is a field, the nonzero $`a` is a unit, and the unit group $`(\mathbb{Z}/p\mathbb{Z})^\times` has order $`p - 1`. By the order form of Lagrange's theorem ({uses "lagrange-order"}[]), raising any group element to the power equal to the group's order gives the identity, so $`a^{\,p-1} = 1`.
:::

:::theorem "fermat-little" (lean := "ZMod.pow_card")
*(Fermat's little theorem.)* For a prime $`p` and any residue $`a \in \mathbb{Z}/p\mathbb{Z}`,
$$`a^{\,p} = a.`
:::

:::proof "fermat-little"
If $`a = 0` the identity is $`0 = 0`. If $`a \ne 0`, then $`a^{\,p-1} = 1` ({uses "fermat-little-units"}[]), and multiplying through by $`a` gives $`a^{\,p} = a` after writing $`p = (p-1) + 1`.
:::

:::theorem "euler-theorem" (lean := "ZMod.pow_totient, Nat.ModEq.pow_totient")
*(Euler's theorem.)* If $`a` is coprime to $`n`, then
$$`a^{\,\varphi(n)} \equiv 1 \pmod{n}.`
Equivalently, every unit $`u` of $`\mathbb{Z}/n\mathbb{Z}` satisfies $`u^{\,\varphi(n)} = 1`.
:::

:::proof "euler-theorem"
The unit version is immediate from Lagrange: the unit group $`(\mathbb{Z}/n\mathbb{Z})^\times` has order $`\varphi(n)` ({uses "totient"}[]), so $`u^{\,\varphi(n)} = 1` for every unit $`u` ({uses "lagrange-order"}[]). The congruence form is the transfer of this identity along the unit $`u` attached to a residue $`a` coprime to $`n`. Fermat's little theorem ({uses "fermat-little-units"}[]) is the special case $`n = p`, where $`\varphi(p) = p - 1`.
:::

:::theorem "lucas-theorem" (lean := "Choose.lucas_theorem")
*(Lucas's theorem.)* For a prime $`p` and naturals $`n, k` with base-$`p` digit expansions $`n = \sum_i n_i p^{\,i}` and $`k = \sum_i k_i p^{\,i}`,
$$`\binom{n}{k} \equiv \prod_i \binom{n_i}{k_i} \pmod{p}.`
:::

:::proof "lucas-theorem"
The single-digit step is the identity, in the polynomial ring $`(\mathbb{Z}/p\mathbb{Z})[X]`,
$$`(1 + X)^{n} = (1 + X)^{\,n \bmod p}\,\bigl(1 + X^{p}\bigr)^{\lfloor n/p\rfloor},`
which follows from the Frobenius identity $`(1+X)^{p} = 1 + X^{p}` in characteristic $`p` (a generalisation of Fermat's little theorem, {uses "fermat-little"}[]). Comparing the coefficient of $`X^{k}` on both sides — using that $`1 + X^{p}` contributes only powers of $`X^{p}` — yields $`\binom{n}{k} \equiv \binom{n \bmod p}{k \bmod p}\binom{\lfloor n/p\rfloor}{\lfloor k/p\rfloor}`. Iterating this digit-by-digit over the base-$`p` expansions gives the product formula.
:::

:::theorem "lagrange-poly-bound" (lean := "Polynomial.card_roots'")
*(Lagrange's bound on polynomial roots.)* Over an integral domain, a nonzero polynomial of degree $`d` has at most $`d` roots, counted with multiplicity. In particular, a polynomial of degree $`d` over the field $`\mathbb{Z}/p\mathbb{Z}` has at most $`d` roots.
:::

:::proof "lagrange-poly-bound"
Over a domain, each root $`a` of $`f` lets one factor out $`(X - a)`, dropping the degree by one and preserving the remaining roots; iterating produces a multiset of roots whose size is bounded by $`\deg f`. mathlib packages this as the existence of a root multiset of cardinality at most the degree, from which the natural-degree bound $`\#\{\text{roots of } f\} \le \deg f` follows.
:::

:::theorem "units-cyclic" (lean := "isCyclic_of_injective_ringHom")
The unit group of a finite field — and more generally any finite subgroup of the units of an integral domain — is cyclic. In particular $`(\mathbb{Z}/p\mathbb{Z})^\times` is cyclic of order $`p - 1`, so a *primitive root* modulo $`p` exists.
:::

:::proof "units-cyclic"
A finite abelian group $`G` is cyclic provided that for each $`d` at most $`d` elements satisfy $`x^{d} = 1` (the cyclicity criterion via counting elements of each order against $`\sum_{d \mid |G|}\varphi(d) = |G|`). For a finite subgroup $`G` of the units of a domain, embedded by a ring homomorphism, the elements with $`x^{d} = 1` map to roots of $`X^{d} - 1`, of which there are at most $`d` by Lagrange's polynomial bound ({uses "lagrange-poly-bound"}[]); so the criterion applies and $`G` is cyclic.
:::

:::lemma_ "prod-units-neg-one" (lean := "FiniteField.prod_univ_units_id_eq_neg_one")
In a finite field (more generally a finite commutative integral domain), the product of all units is $`-1`:
$$`\prod_{u \in K^\times} u = -1.`
:::

:::proof "prod-units-neg-one"
Pull the unit $`-1` out of the product. On the remaining units, pair each $`u` with its multiplicative inverse $`u^{-1}`; this is an involution whose only fixed points are the units equal to their own inverse, i.e. the solutions of $`u^2 = 1`, which in a field are just $`\pm 1` (the case $`u \ne 0` of {uses "fermat-little-units"}[] underlies that the group is well-behaved, and $`(u-1)(u+1)=0` forces $`u = \pm 1`). The element $`+1` is the identity and $`-1` was removed, so every surviving unit cancels with its distinct inverse, leaving the product over $`K^\times \setminus \{-1\}` equal to $`1`. Multiplying back the removed $`-1` gives $`-1`.
:::

:::theorem "wilson" (lean := "ZMod.wilsons_lemma")
*(Wilson's theorem.)* For a prime $`p`,
$$`(p-1)! \equiv -1 \pmod{p}.`
:::

:::proof "wilson"
The factorial $`(p-1)! = \prod_{a=1}^{p-1} a` reduces, modulo $`p`, to the product of all the nonzero residues of $`\mathbb{Z}/p\mathbb{Z}`. The map $`a \mapsto \overline{a}` is a bijection from $`\{1, \dots, p-1\}` onto the units $`(\mathbb{Z}/p\mathbb{Z})^\times`, so this product is exactly $`\prod_{u \in (\mathbb{Z}/p\mathbb{Z})^\times} u`, which equals $`-1` ({uses "prod-units-neg-one"}[]). Hence $`(p-1)! \equiv -1 \pmod p`.
:::

# Arithmetic functions: Möbius, sigma, and Dirichlet convolution

:::definition "dirichlet-convolution" (lean := "ArithmeticFunction.mul_apply")
The *Dirichlet convolution* of two arithmetic functions $`f, g : \mathbb{N} \to R` (with $`f(0) = g(0) = 0`) is the arithmetic function
$$`(f * g)(n) = \sum_{d \mid n} f(d)\,g(n/d) = \sum_{\substack{x\,y = n}} f(x)\,g(y),`
the sum running over factorizations $`xy = n`. This makes the arithmetic functions a commutative ring whose identity is the function $`\delta(n) = [\,n = 1\,]`, and whose constant unit function $`\zeta(n) = 1` (for $`n \ge 1`) is the *Riemann zeta arithmetic function*.
:::

:::definition "multiplicative" (lean := "ArithmeticFunction.IsMultiplicative")
An arithmetic function $`f` is *multiplicative* if $`f(1) = 1` and $`f(mn) = f(m)\,f(n)` whenever $`\gcd(m, n) = 1`. A multiplicative function is determined by its values on prime powers, since $`f(n) = \prod_{p} f\bigl(p^{\,v_p(n)}\bigr)`.
:::

:::theorem "multiplicative-mul" (lean := "ArithmeticFunction.IsMultiplicative.mul")
The Dirichlet convolution of two multiplicative functions is multiplicative: if $`f` and $`g` are multiplicative, so is $`f * g`.
:::

:::proof "multiplicative-mul"
That $`(f*g)(1) = f(1)g(1) = 1` is clear. For coprime $`m, n`, every divisor $`d` of $`mn` factors uniquely as $`d = d_1 d_2` with $`d_1 \mid m` and $`d_2 \mid n` (coprimality of $`m, n`), and the cofactor splits accordingly. Using multiplicativity of $`f` and $`g` on the resulting coprime pieces, the convolution sum over divisors of $`mn` ({uses "dirichlet-convolution"}[]) factors as the product of the convolution sums over divisors of $`m` and of $`n` ({uses "multiplicative"}[]), giving $`(f*g)(mn) = (f*g)(m)\,(f*g)(n)`.
:::

:::definition "moebius" (lean := "ArithmeticFunction.moebius")
The *Möbius function* $`\mu : \mathbb{N} \to \mathbb{Z}` is defined by $`\mu(n) = (-1)^{\Omega(n)}` if $`n` is squarefree, where $`\Omega(n)` is the number of prime factors of $`n`, and $`\mu(n) = 0` if $`n` is divisible by the square of a prime. Thus $`\mu(1) = 1`, $`\mu(p) = -1` for a prime $`p`, and $`\mu` vanishes on non-squarefree inputs.
:::

:::lemma_ "moebius-zeta" (lean := "ArithmeticFunction.moebius_mul_coe_zeta")
The Möbius function is the Dirichlet inverse of the constant function $`\zeta`: $`\mu * \zeta = \delta`, that is, for every $`n \ge 1`,
$$`\sum_{d \mid n} \mu(d) = [\,n = 1\,].`
:::

:::proof "moebius-zeta"
Both $`\mu` and $`\zeta` are multiplicative, hence so is their convolution $`\mu * \zeta` ({uses "multiplicative-mul"}[], {uses "moebius"}[], {uses "dirichlet-convolution"}[]). A multiplicative function is determined by its values on prime powers, so it suffices to check $`(\mu * \zeta)(p^{k}) = [\,p^{k} = 1\,]`. For $`k \ge 1`, $`\sum_{d \mid p^{k}} \mu(d) = \mu(1) + \mu(p) = 1 + (-1) = 0` since $`\mu` vanishes on $`p^{2}, \dots, p^{k}`; and $`(\mu*\zeta)(1) = \mu(1) = 1`. This matches $`\delta`.
:::

:::theorem "moebius-inversion" (lean := "ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq")
*(Möbius inversion.)* Let $`f, g : \mathbb{N} \to R` be functions into a commutative ring. Then
$$`g(n) = \sum_{d \mid n} f(d) \quad\text{for all } n \ge 1`
holds if and only if
$$`f(n) = \sum_{d \mid n} \mu(n/d)\, g(d) \quad\text{for all } n \ge 1.`
:::

:::proof "moebius-inversion"
Phrased through Dirichlet convolution ({uses "dirichlet-convolution"}[]), the first relation says $`g = \zeta * f` and the second says $`f = \mu * g`. Since $`\mu * \zeta = \delta` is the convolution identity ({uses "moebius-zeta"}[]), convolving $`g = \zeta * f` with $`\mu` gives $`\mu * g = (\mu * \zeta) * f = \delta * f = f`; the converse follows symmetrically by convolving $`f = \mu * g` with $`\zeta`. The whole argument is the associativity of convolution together with the inverse relation between $`\mu` and $`\zeta`.
:::

:::definition "sigma" (lean := "ArithmeticFunction.sigma")
For $`k \in \mathbb{N}`, the *divisor-power function* $`\sigma_k` is the arithmetic function
$$`\sigma_k(n) = \sum_{d \mid n} d^{\,k}.`
Thus $`\sigma_0(n) = \tau(n)` counts the divisors of $`n`, and $`\sigma_1(n) = \sigma(n)` is the sum of the divisors of $`n`.
:::

:::theorem "sigma-multiplicative" (lean := "ArithmeticFunction.isMultiplicative_sigma")
For each $`k`, the divisor-power function $`\sigma_k` is multiplicative: $`\sigma_k(mn) = \sigma_k(m)\,\sigma_k(n)` whenever $`\gcd(m, n) = 1`.
:::

:::proof "sigma-multiplicative"
mathlib observes that $`\sigma_k = \zeta * \mathrm{pow}_k` is the Dirichlet convolution of the unit function $`\zeta` with the $`k`-th power function $`n \mapsto n^{k}` ({uses "dirichlet-convolution"}[]): indeed $`(\zeta * \mathrm{pow}_k)(n) = \sum_{d \mid n} d^{k}`. Both $`\zeta` and $`\mathrm{pow}_k` are multiplicative, so their convolution is multiplicative ({uses "multiplicative-mul"}[]).
:::

:::definition "perfect-number" (lean := "Nat.Perfect, Nat.perfect_iff_sum_divisors_eq_two_mul")
A positive integer $`n` is *perfect* if it equals the sum of its proper divisors, equivalently if
$$`\sigma(n) = \sum_{d \mid n} d = 2n,`
the sum of all divisors (the $`k = 1` case of $`\sigma_k`, {uses "sigma"}[]) being twice the number.
:::

# Quadratic residues and reciprocity

Throughout this section $`p` is an odd prime. Following mathlib, the Legendre symbol is defined as a value of the quadratic character of the finite field $`\mathbb{Z}/p\mathbb{Z}`, and the reciprocity law is obtained from quadratic Gauss sums rather than from Eisenstein's lattice-point count.

:::definition "legendre-symbol" (lean := "legendreSym")
For an odd prime $`p` and an integer $`a`, the *Legendre symbol* $`\left(\frac{a}{p}\right)` is the value $`\chi(\bar a)` of the quadratic character $`\chi` of $`\mathbb{Z}/p\mathbb{Z}` at the reduction of $`a`: it is $`0` if $`p \mid a`, $`+1` if $`a` is a nonzero square modulo $`p`, and $`-1` if $`a` is a non-square modulo $`p`. By construction $`a \mapsto \left(\frac{a}{p}\right)` is multiplicative.
:::

:::theorem "euler-criterion" (lean := "ZMod.euler_criterion")
*(Euler's criterion.)* For an odd prime $`p` and a nonzero residue $`a \in \mathbb{Z}/p\mathbb{Z}`, the element $`a` is a square if and only if
$$`a^{(p-1)/2} = 1.`
:::

:::proof "euler-criterion"
mathlib proves the unit form first: a unit $`x` of $`\mathbb{Z}/p\mathbb{Z}` is a square iff $`x^{(p-1)/2} = 1`. In the cyclic unit group ({uses "units-cyclic"}[]) of order $`p - 1`, the squaring map has image the subgroup of squares, which is exactly the kernel of $`x \mapsto x^{(p-1)/2}`: by Fermat's little theorem ({uses "fermat-little-units"}[]) every nonzero $`x` satisfies $`x^{p-1} = 1`, so $`x^{(p-1)/2} = \pm 1`, and writing $`x = g^{j}` for a generator $`g`, the value is $`1` iff $`j` is even iff $`x` is a square. Transferring from units to the nonzero residue $`a` gives the stated equivalence.
:::

:::lemma_ "legendre-eq-pow" (lean := "legendreSym.eq_pow")
For an odd prime $`p` and an integer $`a`, the Legendre symbol satisfies the congruence
$$`\left(\frac{a}{p}\right) \equiv a^{(p-1)/2} \pmod{p}.`
:::

:::proof "legendre-eq-pow"
This is the quadratic-character analogue of Euler's criterion ({uses "euler-criterion"}[]): for the quadratic character $`\chi` of a finite field of odd characteristic one has $`\chi(a) = a^{(\#F - 1)/2}` as elements of the field. Specialising to $`F = \mathbb{Z}/p\mathbb{Z}`, whose cardinality is $`p`, turns this into $`\left(\frac{a}{p}\right) \equiv a^{(p-1)/2} \pmod p` via the definition of the Legendre symbol ({uses "legendre-symbol"}[]). The two cases $`p \mid a` and $`p \nmid a` are handled by the vanishing of $`\chi` at $`0` and by the $`\pm 1` dichotomy.
:::

:::lemma_ "quadratic-gauss-sum" (lean := "gaussSum, gaussSum_sq")
*(Quadratic Gauss sum.)* For the quadratic character $`\chi` of a finite field $`F` and a nontrivial additive character $`\psi`, the *Gauss sum* is $`g = \sum_{x \in F} \chi(x)\,\psi(x)`, and it satisfies
$$`g^{2} = \chi(-1)\,\#F.`
:::

:::proof "quadratic-gauss-sum"
The product $`g \cdot \overline{g}` of the Gauss sum with the Gauss sum of the inverse character evaluates, by expanding and reindexing the double sum over $`F`, to $`\chi(-1)\,\#F` (this is `gaussSum_mul_gaussSum_eq_card`). For the *quadratic* character $`\chi = \chi^{-1}` is its own inverse, so $`g\cdot\overline{g} = g^{2}`, yielding $`g^{2} = \chi(-1)\,\#F`. This single quadratic relation is the engine that drives the values of the Legendre symbol at $`2`, at $`-1`, and the reciprocity law.
:::

:::lemma_ "legendre-neg-one" (lean := "legendreSym.at_neg_one")
*(First supplement.)* For an odd prime $`p`,
$$`\left(\frac{-1}{p}\right) = \chi_4(p) = (-1)^{(p-1)/2} = \begin{cases} +1 & p \equiv 1 \pmod 4, \\ -1 & p \equiv 3 \pmod 4. \end{cases}`
:::

:::proof "legendre-neg-one"
The Legendre symbol at $`-1` is the value of the quadratic character at $`-1`, and for a finite field of odd characteristic this equals $`\chi_4(\#F)`, where $`\chi_4` is the non-trivial character modulo $`4` — equivalently $`(-1)^{(\#F-1)/2}`. With $`\#F = p` this is $`\chi_4(p) = (-1)^{(p-1)/2}` ({uses "euler-criterion"}[]), whose value is determined by $`p \bmod 4`.
:::

:::lemma_ "legendre-two" (lean := "legendreSym.at_two")
*(Second supplement.)* For an odd prime $`p`,
$$`\left(\frac{2}{p}\right) = \chi_8(p) = (-1)^{(p^2 - 1)/8} = \begin{cases} +1 & p \equiv \pm 1 \pmod 8, \\ -1 & p \equiv \pm 3 \pmod 8. \end{cases}`
:::

:::proof "legendre-two"
The Legendre symbol at $`2` equals the quadratic character of $`\mathbb{Z}/p\mathbb{Z}` at $`2`, which mathlib evaluates as $`\chi_8(\#F) = \chi_8(p)`, the character modulo $`8`. This value of the quadratic character at $`2` is exactly where the quadratic Gauss sum is used ({uses "quadratic-gauss-sum"}[]): the relation $`g^{2} = \chi(-1)\#F` applied in a field containing a primitive eighth root of unity pins down $`\chi(2)` as $`\chi_8(\#F)`. The resulting sign depends only on $`p \bmod 8` and equals $`(-1)^{(p^{2}-1)/8}`.
:::

:::theorem "quadratic-reciprocity" (lean := "legendreSym.quadratic_reciprocity")
*(Law of quadratic reciprocity.)* For distinct odd primes $`p` and $`q`,
$$`\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\cdot\frac{q-1}{2}}.`
Thus $`\left(\frac{p}{q}\right) = \left(\frac{q}{p}\right)` unless both $`p` and $`q` are congruent to $`3 \pmod 4`, in which case the two symbols differ in sign.
:::

:::proof "quadratic-reciprocity"
mathlib proves this through Gauss sums, not the Eisenstein lattice-point count. Working in a field of characteristic $`p` that contains the needed roots of unity, let $`g` be the quadratic Gauss sum of $`\chi_q`, the quadratic character of $`\mathbb{Z}/q\mathbb{Z}`. The key relation $`g^{2} = \chi_q(-1)\,q` ({uses "quadratic-gauss-sum"}[]) lets one compute the Frobenius power $`g^{p}` in two ways. On one hand $`g^{p} = (g^{2})^{(p-1)/2}\,g = \bigl(\chi_q(-1)q\bigr)^{(p-1)/2} g`, and by Euler's criterion ({uses "legendre-eq-pow"}[], {uses "euler-criterion"}[]) the scalar is $`\left(\frac{q}{p}\right)` up to the supplement $`\left(\frac{-1}{p}\right)`. On the other hand, raising the defining sum to the $`p`-th power and using the additive Frobenius shows $`g^{p} = \chi_q(p)\,g = \left(\frac{p}{q}\right) g`. Equating the two expressions for $`g^{p}` and cancelling $`g` (which is a unit since $`g^{2} \ne 0`) gives the product $`\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\cdot\frac{q-1}{2}}` after evaluating the $`\chi_4` supplements. This is the content of mathlib's `quadraticChar_odd_prime`, on which `legendreSym.quadratic_reciprocity` is built.
:::

:::lemma_ "sqrt-neg-one" (lean := "ZMod.exists_sq_eq_neg_one_iff")
The residue $`-1` is a square modulo a prime $`p` if and only if $`p \not\equiv 3 \pmod 4`:
$$`\exists x,\ x^{2} \equiv -1 \pmod p \iff p \bmod 4 \ne 3.`
:::

:::proof "sqrt-neg-one"
By Euler's criterion ({uses "euler-criterion"}[]), $`-1` is a square modulo $`p` iff $`(-1)^{(p-1)/2} = 1`, i.e. iff $`(p-1)/2` is even, which happens exactly when $`p \equiv 1 \pmod 4`; together with the prime $`p = 2`, this is the condition $`p \bmod 4 \ne 3`. Equivalently, this reads off the first supplement $`\left(\frac{-1}{p}\right) = (-1)^{(p-1)/2}` ({uses "legendre-neg-one"}[]).
:::

:::definition "jacobi-symbol" (lean := "jacobiSym")
For an integer $`a` and a natural number $`b`, the *Jacobi symbol* $`\left(\frac{a}{b}\right)` is the product of Legendre symbols over the prime factors of $`b` (with multiplicity):
$$`\left(\frac{a}{b}\right) = \prod_{p^{e}\,\|\,b} \left(\frac{a}{p}\right)^{e}.`
It extends the Legendre symbol ({uses "legendre-symbol"}[]) to composite odd $`b` and is multiplicative in both arguments.
:::

:::theorem "jacobi-reciprocity" (lean := "jacobiSym.quadratic_reciprocity")
*(Reciprocity for the Jacobi symbol.)* For odd naturals $`a` and $`b`,
$$`\left(\frac{a}{b}\right) = (-1)^{\frac{a-1}{2}\cdot\frac{b-1}{2}}\,\left(\frac{b}{a}\right).`
:::

:::proof "jacobi-reciprocity"
Since the Jacobi symbol is, by definition, the product of Legendre symbols over the prime factors of its arguments ({uses "jacobi-symbol"}[]), the reciprocity law is built up multiplicatively from the prime case. mathlib reduces both $`a` and $`b` to their prime factors one at a time — exploiting that the right-hand side, viewed as a function of each argument, is a homomorphism $`\mathbb{N} \to \mathbb{Z}` — and at the level of two primes invokes quadratic reciprocity for the Legendre symbol ({uses "quadratic-reciprocity"}[]). A sign bookkeeping function tracks the accumulated factor $`(-1)^{\frac{a-1}{2}\cdot\frac{b-1}{2}}` across the prime decomposition.
:::

# Sums of squares and Pythagorean triples

:::theorem "two-square" (lean := "Nat.Prime.sq_add_sq")
*(Fermat's two-square theorem.)* A prime $`p` with $`p \not\equiv 3 \pmod 4` is a sum of two squares: there exist naturals $`a, b` with
$$`p = a^2 + b^2.`
In particular every prime $`p \equiv 1 \pmod 4` is a sum of two squares.
:::

:::proof "two-square"
mathlib argues in the Gaussian integers $`\mathbb{Z}[i]`, a principal ideal domain with norm $`N(a + bi) = a^{2} + b^{2}`. The hypothesis $`p \not\equiv 3 \pmod 4` is precisely the condition that $`p` is *not* irreducible in $`\mathbb{Z}[i]` (a rational prime is a Gaussian prime iff $`p \equiv 3 \pmod 4`; the bridge uses that $`-1` is a square modulo such $`p`, {uses "sqrt-neg-one"}[]). Being reducible and not a unit, $`p` factors as $`p = \alpha\beta` with $`\alpha, \beta` non-units. Taking norms, $`p^{2} = N(p) = N(\alpha)N(\beta)` with both norms $`> 1`, so $`N(\alpha) = p`. Writing $`\alpha = a + bi` gives $`p = N(\alpha) = a^{2} + b^{2}`.
:::

:::lemma_ "euler-four-squares" (lean := "Nat.euler_four_squares")
*(Euler's four-square identity.)* The sums of four squares are closed under multiplication: for all integers (or naturals) $`a, b, c, d, x, y, z, w`, the product $`(a^2+b^2+c^2+d^2)(x^2+y^2+z^2+w^2)` is again a sum of four explicit squares, namely
$$`(ax+by+cz+dw)^2 + (ay-bx+cw-dz)^2 + (az-bw-cx+dy)^2 + (aw+bz-cy-dx)^2.`
:::

:::proof "euler-four-squares"
This is a polynomial identity, verified by expanding both sides; it is the norm-multiplicativity of the Hamilton quaternions, $`N(\xi)N(\eta) = N(\xi\eta)`, written out in coordinates.
:::

:::theorem "four-square" (lean := "Nat.sum_four_squares")
*(Lagrange's four-square theorem.)* Every natural number $`n` is a sum of four squares: there exist naturals $`a, b, c, d` with
$$`n = a^2 + b^2 + c^2 + d^2.`
:::

:::proof "four-square"
By Euler's identity ({uses "euler-four-squares"}[]) the sums of four squares are closed under multiplication, so by induction on the factorization of $`n` (the multiplicative recursion: $`0`, $`1`, primes, and products) it suffices to represent each prime $`p`.

For a prime $`p`, mathlib runs Fermat's *infinite descent*. First, the same kind of residue-counting that underlies the two-square theorem ({uses "two-square"}[]) — a pigeonhole over the $`(p+1)/2` squares — produces $`a, b` and $`0 < m < p` with $`a^{2} + b^{2} + 1 = mp`, so some positive multiple $`mp` is a sum of four squares. Take the least such $`m`. If $`m > 1`, one descends: when $`m` is even one halves it using the identity, and when $`m` is odd one replaces $`a, b, c, d` by their least-absolute-value representatives modulo $`m`, obtaining via Euler's identity a representation of $`m' p` with $`0 < m' < m`, contradicting minimality. Hence the least $`m` is $`1` and $`p` itself is a sum of four squares.
:::

:::theorem "pythagorean-triples" (lean := "PythagoreanTriple, PythagoreanTriple.coprime_classification")
*(Classification of Pythagorean triples.)* A triple $`(x, y, z)` of integers with $`x^2 + y^2 = z^2` and $`\gcd(x, y) = 1` is, up to swapping $`x` and $`y`, of the form
$$`x = m^2 - n^2,\quad y = 2mn,\quad z = \pm(m^2 + n^2)`
for coprime integers $`m, n` of opposite parity; conversely every such $`(m, n)` yields a primitive triple.
:::

:::proof "pythagorean-triples"
A primitive solution of $`x^{2} + y^{2} = z^{2}` corresponds to a rational point $`(x/z, y/z)` on the unit circle. Stereographic projection from $`(-1, 0)` parametrises these rational points by a single rational $`t = n/m` in lowest terms, giving $`(x/z, y/z) = \bigl(\frac{m^{2}-n^{2}}{m^{2}+n^{2}}, \frac{2mn}{m^{2}+n^{2}}\bigr)`. Clearing denominators and using $`\gcd(x,y) = 1` — which forces $`\gcd(m, n) = 1` and opposite parity (via {uses "bezout"}[] and {uses "euclid-lemma"}[] in the coprimality bookkeeping) — produces the stated parametrisation, with the sign of $`z` recovered from $`z^{2} = (m^{2}+n^{2})^{2}`. The converse is the identity $`(m^{2}-n^{2})^{2} + (2mn)^{2} = (m^{2}+n^{2})^{2}`.
:::

# Fermat and Mersenne numbers

:::definition "fermat-numbers" (lean := "Nat.fermatNumber, Nat.coprime_fermatNumber_fermatNumber")
The *Fermat numbers* are $`F_n = 2^{\,2^{\,n}} + 1`. Distinct Fermat numbers are coprime:
$$`\gcd(F_m, F_n) = 1 \quad (m \ne n).`
:::

:::proof "fermat-numbers"
The recurrence $`\prod_{k < n} F_k = F_n - 2` is proved by induction. Hence if $`m < n`, then $`F_m \mid F_n - 2`, so any common divisor $`d` of $`F_m` and $`F_n` divides $`(F_n) - (F_n - 2) = 2`; but every Fermat number is odd, so $`d = 1`. (Coprimality of the $`F_n` gives, as a corollary, another proof of the infinitude of primes, {uses "infinitude-of-primes"}[]: a fresh prime divides each $`F_n`. The argument that a common divisor reduces to a divisor of $`2` uses divisibility in the style of {uses "euclid-lemma"}[].)
:::

:::definition "mersenne" (lean := "mersenne")
The *Mersenne numbers* are $`M_p = 2^{\,p} - 1`. If $`M_p` is prime then $`p` is prime; the primes among the $`M_p` are the *Mersenne primes*, which correspond to the even perfect numbers ({uses "perfect-number"}[]) by the Euclid–Euler theorem.
:::

:::theorem "mersenne-lucas-lehmer" (lean := "lucas_lehmer_sufficiency")
*(Lucas–Lehmer sufficiency.)* Let $`p > 1` and define the residues $`s_0 = 4`, $`s_{i+1} = s_i^2 - 2` in $`\mathbb{Z}/M_p\mathbb{Z}`. If $`s_{p-2} \equiv 0 \pmod{M_p}`, then the Mersenne number $`M_p = 2^p - 1` ({uses "mersenne"}[]) is prime.
:::

:::proof "mersenne-lucas-lehmer"
Work in the ring $`\mathbb{Z}/M_p\mathbb{Z}` adjoined with $`\sqrt 3`, where the recurrence has the closed form $`s_i = \omega^{2^{i}} + \bar\omega^{2^{i}}` for $`\omega = 2 + \sqrt 3` and $`\bar\omega = 2 - \sqrt 3` (note $`\omega\bar\omega = 1`). The vanishing $`s_{p-2} = 0` translates to $`\omega^{2^{p-2}} = -\bar\omega^{2^{p-2}}`, whence $`\omega^{2^{p-1}} = -1` and $`\omega^{2^{p}} = 1` in the ambient ring. If $`M_p` were composite it would have a prime factor $`q \le \sqrt{M_p}`; in the corresponding quotient $`\omega` would have order exactly $`2^{p}`, so by Lagrange's theorem ({uses "lagrange-order"}[]) the group of units there would have at least $`2^{p} > M_p \ge q^{2}` elements, which is impossible. Hence $`M_p` is prime.
:::

# Forthcoming in mathlib

The nodes below are *informal* statements of results that are the subject of open mathlib
pull requests (the `t-number-theory` queue, as of June 2026). Each carries a `pr_url` pointing
at the live PR and _no_ `(lean := …)` reference: the declarations are not yet in mathlib
v4.30.0-rc2. They connect into the dependency graph through the Mathlib-backed nodes of this
chapter via `{uses}` edges, and should be re-pointed to `(lean := …)` once the corresponding
PR merges.

:::theorem "aks-primality" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/34507")
*(AKS primality test, Agrawal–Kayal–Saxena.)* Let $`n \ge 2` be an integer that is not a perfect
power, let $`r` be a suitable auxiliary modulus (the smallest $`r` for which the multiplicative
order of $`n` modulo $`r` exceeds $`(\log_2 n)^2`), and suppose $`n` has no prime factor
$`\le r`. Then $`n` is prime if and only if the *introspective congruence*
$$`(X + a)^n \;\equiv\; X^n + a \pmod{\,n,\ X^r - 1\,}`
holds for every integer $`a` with $`1 \le a \le \lfloor \sqrt{\varphi(r)}\,\log_2 n \rfloor`.
This yields a deterministic polynomial-time primality test.

The introspective congruence is the polynomial-ring generalisation of Fermat's little theorem
({uses "fermat-little"}[]): for $`n` prime it holds for *all* $`a` by the Frobenius identity
$`(X+a)^n \equiv X^n + a^n \equiv X^n + a \pmod n`, and the content of AKS is that checking it
on a short range of $`a`, modulo $`X^r - 1`, already forces $`n` to be prime. PR #34507 builds
the introspective machinery; the prime-power exclusion uses the factorization
({uses "factorization"}[]) of $`n`.
In review — [mathlib PR #34507](https://github.com/leanprover-community/mathlib4/pull/34507).
:::

:::definition "farey-sequence" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/40246")
For a positive integer $`n`, the *Farey sequence* $`F_n` is the set of reduced fractions
$`a/b \in [0,1]` with denominator $`b \le n`, listed in increasing order. Two consecutive terms
$`\tfrac{a}{b} < \tfrac{c}{d}` of $`F_n` are *Farey neighbours*, characterised by the
determinant identity
$$`bc - ad \;=\; 1,`
and their *mediant* $`\tfrac{a+c}{b+d}` is the fraction with smallest denominator strictly
between them. The number of terms is
$$`|F_n| \;=\; 1 + \sum_{k=1}^{n} \varphi(k),`
counting the reduced fractions of each denominator by Euler's totient ({uses "totient"}[]).

PR #40246 develops Farey sequences, the mediant operation, and the neighbour theorem
(the $`bc - ad = 1` characterisation of adjacency), the combinatorial backbone of the
Stern–Brocot tree and of best-approximation arguments. The neighbour identity is a Bézout
relation ({uses "bezout"}[]).
In review — [mathlib PR #40246](https://github.com/leanprover-community/mathlib4/pull/40246).
:::

:::theorem "three-gap" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/40037")
*(Three-gap / Steinhaus theorem.)* Let $`\alpha \in \mathbb{R}` and $`N \ge 1`. Place the $`N`
points $`\{\alpha\}, \{2\alpha\}, \ldots, \{N\alpha\}` on the circle $`\mathbb{R}/\mathbb{Z}`,
where $`\{\,\cdot\,\}` denotes the fractional part. Then the gaps between consecutive points take
_at most three distinct values_, and when there are three the largest is the sum of the other
two.

The widths of the gaps are controlled by the best rational approximations of $`\alpha`, so the
theorem is governed by Diophantine approximation ({uses "dirichlet-approx"}[]): the two
fundamental gap lengths are $`\|q_k\alpha\|` for consecutive continued-fraction denominators
$`q_k`, and the third is their sum. PR #40037 formalises the gap-counting argument directly on
the circle.
In review — [mathlib PR #40037](https://github.com/leanprover-community/mathlib4/pull/40037).
:::

:::definition "almost-prime" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/39903")
For a positive integer $`k`, a natural number $`n` is *$`k`-almost prime* if it has exactly $`k`
prime factors counted with multiplicity:
$$`\Omega(n) \;=\; \sum_{p} v_p(n) \;=\; k,`
where $`v_p(n)` is the exponent of $`p` in the factorization of $`n` ({uses "factorization"}[]).
The $`1`-almost primes are the primes, and the $`2`-almost primes are the *semiprimes*. A number
is *almost prime* if it is $`k`-almost prime for some bounded $`k`.

PR #39903 introduces the predicate $`\Omega(n) = k` and its basic API (behaviour under
multiplication by a prime, the recursive characterisation), the elementary substrate for sieve
statements such as Chen's theorem.
In review — [mathlib PR #39903](https://github.com/leanprover-community/mathlib4/pull/39903).
:::

:::theorem "chebyshev-primorial" (pr_url := "https://github.com/leanprover-community/mathlib4/pull/37299")
*(Chebyshev's lower bound on the primorial.)* For every integer $`n \ge 1`, the *primorial*
— the product of all primes up to $`n` — satisfies an exponential lower bound
$$`\prod_{p \le n} p \;\ge\; 2^{\,n}`
for $`n` sufficiently large (more precisely, $`\vartheta(n) = \sum_{p \le n} \log p \ge cn` for
an explicit constant $`c > 0`). This is a quantitative sharpening of the infinitude of primes
({uses "infinitude-of-primes"}[]): not merely are there infinitely many primes, their product
to $`n` grows at least geometrically in $`n`.

The proof bounds the central binomial coefficient $`\binom{2n}{n}`, whose prime factorization
({uses "fta-existence"}[]) is supported on primes $`\le 2n`, between $`2^n` and the primorial of
$`2n`. PR #37299 supplies this lower bound, a standard ingredient of Chebyshev-type prime-counting
estimates and of Bertrand's postulate.
In review — [mathlib PR #37299](https://github.com/leanprover-community/mathlib4/pull/37299).
:::
