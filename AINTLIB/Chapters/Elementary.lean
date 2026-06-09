import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.SumFourSquares

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Elementary Number Theory" =>

This chapter covers primes and the fundamental theorem of arithmetic, divisibility and congruences, arithmetic functions (Möbius, totient, divisor sums), and quadratic reciprocity. Throughout, $`p` denotes a prime, $`\mathbb{Z}` the integers, and for a positive integer $`n` we write $`\mathbb{Z}/n\mathbb{Z}` for the ring of integers modulo $`n`.

# Primes and the fundamental theorem of arithmetic

:::theorem "infinitude-of-primes" (lean := "Nat.exists_infinite_primes")
There are infinitely many primes: for every natural number $`n` there exists a prime $`p` with $`p \ge n`.
:::

:::proof "infinitude-of-primes"
This is Euclid's argument. Given $`n`, consider $`N = n! + 1`. Any prime factor $`p` of $`N` must satisfy $`p \ge n`, for if $`p < n` then $`p \mid n!`, and since $`p \mid N` we would get $`p \mid (N - n!) = 1`, which is impossible. Since $`N \ge 2` has at least one prime factor — the smallest prime in its factorization ({uses "factorization"}[]) — such a $`p` exists, and it is at least $`n`.
:::

:::definition "factorization" (lean := "Nat.factorization")
For a positive integer $`n`, the *factorization* of $`n` is the finitely-supported function $`p \mapsto v_p(n)` sending each prime $`p` to the exponent $`v_p(n)` with which it occurs in $`n`; that is, the largest $`k` with $`p^k \mid n`. For a prime $`p`, the value $`v_p(n)` is the $`p`-adic valuation of $`n`.
:::

:::theorem "fta-existence" (lean := "Nat.factorization_prod_pow_eq_self")
*(Fundamental theorem of arithmetic — existence.)* Every positive integer $`n` is recovered from its factorization as the product over primes
$$`n = \prod_{p} p^{\,v_p(n)},`
a finite product since only finitely many exponents $`v_p(n)` are nonzero.
:::

:::proof "fta-existence"
By strong induction on $`n`. If $`n = 1` the product is empty and equals $`1`. Otherwise $`n` has a smallest prime factor $`p`, and $`n/p < n` is recovered from its factorization by the inductive hypothesis. Multiplying by $`p` and noting that the valuation of $`n` at each prime $`q` is that of $`n/p` plus $`[q = p]` ({uses "factorization"}[]) gives the displayed product for $`n`.
:::

:::theorem "fta-uniqueness" (lean := "Nat.factorization_inj")
*(Fundamental theorem of arithmetic — uniqueness.)* A positive integer is determined by its factorization: if two positive integers have the same exponent $`v_p(\cdot)` at every prime $`p`, they are equal. Equivalently, the prime factorization of every positive integer is unique up to the order of the factors.
:::

:::proof "fta-uniqueness"
If $`m` and $`n` are positive with $`v_p(m) = v_p(n)` for all primes $`p`, then reconstructing each side as a product of prime powers ({uses "fta-existence"}[]) gives $`m = \prod_p p^{\,v_p(m)} = \prod_p p^{\,v_p(n)} = n`. Phrased multiplicatively, two factorizations of the same number have, for each prime, the same number of occurrences, hence are permutations of one another.
:::

# Euler's totient function

:::definition "totient" (lean := "Nat.totient")
*Euler's totient function* $`\varphi(n)` counts the integers in $`\{0, 1, \dots, n-1\}` that are coprime to $`n`:
$$`\varphi(n) = \#\{\, a : 0 \le a < n,\ \gcd(a, n) = 1 \,\}.`
Equivalently, $`\varphi(n)` is the number of units of $`\mathbb{Z}/n\mathbb{Z}`.
:::

:::lemma_ "totient-prime" (lean := "Nat.totient_prime")
For a prime $`p`, every nonzero residue below $`p` is coprime to $`p`, so
$$`\varphi(p) = p - 1.`
:::

:::proof "totient-prime"
By the definition of the totient ({uses "totient"}[]), $`\varphi(p)` counts the integers in $`\{0, 1, \dots, p-1\}` coprime to $`p`. Since $`p` is prime, the only such integer that fails to be coprime to $`p` is $`0`; the remaining $`p - 1` residues $`1, \dots, p-1` are all coprime to $`p`. Hence $`\varphi(p) = p - 1`.
:::

:::lemma_ "totient-prime-pow" (lean := "Nat.totient_prime_pow")
For a prime $`p` and an exponent $`n \ge 1`,
$$`\varphi(p^{\,n}) = p^{\,n-1}(p - 1).`
:::

:::proof "totient-prime-pow"
Among $`0, 1, \dots, p^n - 1`, an integer fails to be coprime to $`p^n` exactly when it is divisible by $`p`. There are $`p^{\,n-1}` such multiples of $`p`, so $`\varphi(p^n) = p^n - p^{\,n-1} = p^{\,n-1}(p-1)`.
:::

:::theorem "totient-mul" (lean := "Nat.totient_mul")
*(Multiplicativity.)* If $`m` and $`n` are coprime, then
$$`\varphi(mn) = \varphi(m)\,\varphi(n).`
:::

:::proof "totient-mul"
When $`\gcd(m,n) = 1`, the Chinese remainder theorem ({uses "chinese-remainder"}[]) gives a ring isomorphism $`\mathbb{Z}/mn\mathbb{Z} \cong \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}`, under which units correspond to pairs of units. Counting units on each side ({uses "totient"}[]) yields $`\varphi(mn) = \varphi(m)\,\varphi(n)`.
:::

:::theorem "totient-formula" (lean := "Nat.totient_eq_prod_factorization")
For $`n \ge 1`, the totient is given by the product over the distinct primes dividing $`n`:
$$`\varphi(n) = \prod_{p \mid n} p^{\,v_p(n) - 1}\,(p - 1).`
:::

:::proof "totient-formula"
Write $`n = \prod_{p \mid n} p^{\,v_p(n)}` ({uses "fta-existence"}[]). The prime-power factors are pairwise coprime, so multiplicativity ({uses "totient-mul"}[]) reduces the computation to the prime-power case ({uses "totient-prime-pow"}[]), and multiplying the factors $`\varphi(p^{\,v_p(n)}) = p^{\,v_p(n)-1}(p-1)` gives the formula.
:::

# Congruences: the theorems of Fermat, Euler and Wilson

:::theorem "fermat-little" (lean := "ZMod.pow_card")
*(Fermat's little theorem.)* For a prime $`p` and any residue $`a \in \mathbb{Z}/p\mathbb{Z}`,
$$`a^{\,p} = a.`
:::

:::proof "fermat-little"
The ring $`\mathbb{Z}/p\mathbb{Z}` is a field with $`p` elements, so its multiplicative group has order $`p - 1`. If $`a \ne 0` then $`a^{\,p-1} = 1` ({uses "fermat-little-units"}[]), and multiplying by $`a` gives $`a^{\,p} = a`; the case $`a = 0` is immediate.
:::

:::theorem "fermat-little-units" (lean := "ZMod.pow_card_sub_one_eq_one")
For a prime $`p` and a nonzero residue $`a \in \mathbb{Z}/p\mathbb{Z}`,
$$`a^{\,p-1} = 1.`
:::

:::proof "fermat-little-units"
The nonzero residues form a group of order $`p - 1` under multiplication. By Lagrange's theorem the order of any element divides $`p - 1`, so raising any nonzero $`a` to the power $`p - 1` yields the identity.
:::

:::theorem "euler-theorem" (lean := "ZMod.pow_totient, Nat.ModEq.pow_totient")
*(Euler's theorem.)* If $`a` is coprime to $`n`, then
$$`a^{\,\varphi(n)} \equiv 1 \pmod{n}.`
Equivalently, every unit $`u` of $`\mathbb{Z}/n\mathbb{Z}` satisfies $`u^{\,\varphi(n)} = 1`.
:::

:::proof "euler-theorem"
The units of $`\mathbb{Z}/n\mathbb{Z}` form a group of order $`\varphi(n)` ({uses "totient"}[]). A residue $`a` coprime to $`n` is such a unit, and by Lagrange's theorem its order divides the group order, so $`a^{\,\varphi(n)} = 1` in $`\mathbb{Z}/n\mathbb{Z}`, i.e. $`a^{\,\varphi(n)} \equiv 1 \pmod{n}`. Fermat's little theorem ({uses "fermat-little-units"}[]) is the special case $`n = p`, where $`\varphi(p) = p - 1`.
:::

:::theorem "wilson" (lean := "ZMod.wilsons_lemma")
*(Wilson's theorem.)* For a prime $`p`,
$$`(p-1)! \equiv -1 \pmod{p}.`
:::

:::proof "wilson"
Work in the field $`\mathbb{Z}/p\mathbb{Z}`, whose nonzero residues form a multiplicative group of order $`p - 1` in which every element has a unique inverse ({uses "fermat-little-units"}[]). In the product $`(p-1)! = \prod_{a=1}^{p-1} a` of all nonzero residues, pair each $`a` with its multiplicative inverse $`a^{-1}`. The only residues that are their own inverse are the solutions of $`a^2 = 1`; since $`\mathbb{Z}/p\mathbb{Z}` is a field, $`(a-1)(a+1) = 0` forces $`a = \pm 1`. Every other residue cancels against its distinct inverse, leaving $`(p-1)! \equiv 1 \cdot (-1) = -1 \pmod{p}`.
:::

:::theorem "chinese-remainder" (lean := "ZMod.chineseRemainder")
*(Chinese remainder theorem.)* If $`m` and $`n` are coprime, then reduction modulo $`m` and modulo $`n` gives a ring isomorphism
$$`\mathbb{Z}/mn\mathbb{Z} \;\cong\; \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}.`
In particular, any pair of congruences $`x \equiv a \pmod{m}` and $`x \equiv b \pmod{n}` has a solution, unique modulo $`mn`.
:::

:::proof "chinese-remainder"
The map sending $`x \bmod mn` to the pair $`(x \bmod m,\ x \bmod n)` is a ring homomorphism. Its kernel consists of residues divisible by both $`m` and $`n`; as $`\gcd(m,n) = 1`, this means divisible by $`mn`, so the map is injective. Both sides have $`mn` elements, hence it is a bijection, and therefore a ring isomorphism.
:::

# The Möbius function and Möbius inversion

:::definition "moebius" (lean := "ArithmeticFunction.moebius")
The *Möbius function* $`\mu : \mathbb{N} \to \mathbb{Z}` is defined by $`\mu(1) = 1`, $`\mu(n) = (-1)^k` if $`n` is a product of $`k` distinct primes (squarefree), and $`\mu(n) = 0` if $`n` is divisible by the square of a prime.
:::

:::lemma_ "moebius-zeta" (lean := "ArithmeticFunction.moebius_mul_coe_zeta")
The Möbius function is the Dirichlet inverse of the constant function $`1`: for every $`n \ge 1`,
$$`\sum_{d \mid n} \mu(d) = [\,n = 1\,].`
:::

:::proof "moebius-zeta"
For $`n = 1` the sum is $`\mu(1) = 1`. For $`n > 1`, only the squarefree divisors contribute, since $`\mu` vanishes on any divisor divisible by the square of a prime ({uses "moebius"}[]). Writing $`n` with $`r \ge 1` distinct prime factors, the squarefree divisors are products of subsets of these primes, and a subset of size $`j` contributes $`(-1)^j`. Hence the sum is $`\sum_{j=0}^{r} \binom{r}{j} (-1)^j = (1 - 1)^r = 0`.
:::

:::theorem "moebius-inversion" (lean := "ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq")
*(Möbius inversion.)* Let $`f, g : \mathbb{N} \to R` be functions into a commutative ring. Then
$$`g(n) = \sum_{d \mid n} f(d) \quad\text{for all } n \ge 1`
holds if and only if
$$`f(n) = \sum_{d \mid n} \mu(n/d)\, g(d) \quad\text{for all } n \ge 1.`
:::

:::proof "moebius-inversion"
Both directions are the associativity of Dirichlet convolution combined with the identity $`\sum_{d \mid n} \mu(d) = [\,n = 1\,]` ({uses "moebius-zeta"}[]). If $`g = 1 * f` (convolution with the constant $`1`), then convolving with $`\mu` gives $`\mu * g = (\mu * 1) * f = f`, which is the inversion formula; the converse is symmetric.
:::

# Quadratic reciprocity

:::definition "legendre-symbol" (lean := "legendreSym")
For an odd prime $`p` and an integer $`a`, the *Legendre symbol* $`\left(\frac{a}{p}\right)` is $`0` if $`p \mid a`, $`+1` if $`a` is a nonzero quadratic residue modulo $`p`, and $`-1` if $`a` is a quadratic non-residue modulo $`p`.
:::

:::theorem "euler-criterion" (lean := "ZMod.euler_criterion")
*(Euler's criterion.)* For an odd prime $`p` and a nonzero residue $`a \in \mathbb{Z}/p\mathbb{Z}`, the element $`a` is a square if and only if
$$`a^{(p-1)/2} = 1.`
Consequently $`\left(\frac{a}{p}\right) \equiv a^{(p-1)/2} \pmod{p}`.
:::

:::proof "euler-criterion"
The multiplicative group of $`\mathbb{Z}/p\mathbb{Z}` is cyclic of order $`p - 1`. By Fermat's little theorem ({uses "fermat-little-units"}[]) every nonzero $`a` satisfies $`a^{p-1} = 1`, so $`a^{(p-1)/2} = \pm 1`. Picking a generator $`g`, write $`a = g^k`; then $`a^{(p-1)/2} = 1` iff $`(p-1) \mid k(p-1)/2` iff $`k` is even, which is exactly the condition for $`a` to be a square. The resulting value $`a^{(p-1)/2} \in \{\pm 1\}` is precisely the Legendre symbol $`\left(\frac{a}{p}\right)` ({uses "legendre-symbol"}[]), which records whether the nonzero $`a` is a quadratic residue.
:::

:::theorem "quadratic-reciprocity" (lean := "legendreSym.quadratic_reciprocity")
*(Law of quadratic reciprocity.)* For distinct odd primes $`p` and $`q`,
$$`\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\cdot\frac{q-1}{2}}.`
Thus $`\left(\frac{p}{q}\right) = \left(\frac{q}{p}\right)` unless both $`p` and $`q` are congruent to $`3 \pmod 4`, in which case the two symbols differ in sign.
:::

:::proof "quadratic-reciprocity"
By Euler's criterion ({uses "euler-criterion"}[]) each Legendre symbol is a power of the relevant residue, reducing the statement to counting. The standard route is Eisenstein's lattice-point argument: $`\left(\frac{q}{p}\right) = (-1)^{\sum_k \lfloor kq/p \rfloor}`, where the sum runs over $`k = 1, \dots, (p-1)/2`. The lattice points strictly under the line of slope $`q/p` inside the rectangle $`[0, p/2] \times [0, q/2]` split, by the symmetry $`(x,y) \mapsto ((p+1)/2 - x, (q+1)/2 - y)`, so that the two exponents sum to $`\frac{p-1}{2}\cdot\frac{q-1}{2}`, giving the reciprocity sign.
:::

:::lemma_ "legendre-neg-one" (lean := "legendreSym.at_neg_one")
*(First supplement.)* For an odd prime $`p`,
$$`\left(\frac{-1}{p}\right) = (-1)^{(p-1)/2} = \begin{cases} +1 & p \equiv 1 \pmod 4, \\ -1 & p \equiv 3 \pmod 4. \end{cases}`
:::

:::proof "legendre-neg-one"
By Euler's criterion ({uses "euler-criterion"}[]), $`\left(\frac{-1}{p}\right) \equiv (-1)^{(p-1)/2} \pmod p`. Both sides are $`\pm 1` and $`p > 2`, so the congruence is an equality. The case split follows from the parity of $`(p-1)/2`.
:::

:::lemma_ "legendre-two" (lean := "legendreSym.at_two")
*(Second supplement.)* For an odd prime $`p`,
$$`\left(\frac{2}{p}\right) = (-1)^{(p^2 - 1)/8} = \begin{cases} +1 & p \equiv \pm 1 \pmod 8, \\ -1 & p \equiv \pm 3 \pmod 8. \end{cases}`
:::

:::proof "legendre-two"
This is the Gauss-lemma computation for the Legendre symbol ({uses "legendre-symbol"}[]) at $`a = 2`. Gauss's lemma evaluates $`\left(\frac{2}{p}\right)` by counting how many of $`2, 4, \dots, p-1` exceed $`p/2` (when reduced to the range $`(-p/2, p/2)` they change sign); this yields the exponent $`(p^2-1)/8 \pmod 2`, whose value depends only on $`p \bmod 8` as displayed. Equivalently, by Euler's criterion ({uses "euler-criterion"}[]) the symbol equals $`2^{(p-1)/2} \bmod p`, and both routes give the same sign.
:::

# Sums of squares

:::theorem "two-square" (lean := "Nat.Prime.sq_add_sq")
*(Fermat's two-square theorem.)* A prime $`p` with $`p \not\equiv 3 \pmod 4` is a sum of two squares: there exist integers $`a, b` with
$$`p = a^2 + b^2.`
In particular every prime $`p \equiv 1 \pmod 4` is a sum of two squares.
:::

:::proof "two-square"
The case $`p = 2 = 1^2 + 1^2` is immediate, so assume $`p \equiv 1 \pmod 4`. By the first supplement ({uses "legendre-neg-one"}[]) the residue $`-1` is a quadratic residue mod $`p`, so there is an integer $`x` with $`x^2 \equiv -1 \pmod p`, i.e. $`p \mid x^2 + 1`. Working in the Gaussian integers $`\mathbb{Z}[i]`, this means $`p \mid (x + i)(x - i)` but $`p` divides neither factor, so $`p` is not a Gaussian prime; it factors as $`p = (a + bi)(a - bi)`, and taking norms gives $`p = a^2 + b^2`. (Equivalently, one runs Thue's pigeonhole argument on the lattice $`\{(u, v) : v \equiv xu \pmod p\}`.)
:::

:::theorem "four-square" (lean := "Nat.sum_four_squares")
*(Lagrange's four-square theorem.)* Every natural number $`n` is a sum of four squares: there exist integers $`a, b, c, d` with
$$`n = a^2 + b^2 + c^2 + d^2.`
:::

:::proof "four-square"
By Euler's four-square identity, the sums of four squares are closed under multiplication — the four-square analogue of the norm-multiplicativity that drives the two-square theorem ({uses "two-square"}[]) — so it suffices to treat $`n = 0, 1` and each prime $`p`. For an odd prime $`p`, the same kind of counting of quadratic residues that underlies the two-square case produces, by pigeonhole, $`x, y` with $`x^2 + y^2 + 1 \equiv 0 \pmod p`, so some multiple $`mp` with $`1 \le m < p` is a sum of four squares. A descent step then shows the least such $`m` must be $`1`: if $`m > 1` one constructs, from a representation of $`mp`, a representation of $`m'p` with $`0 < m' < m`, contradicting minimality. Hence $`p` itself is a sum of four squares.
:::
