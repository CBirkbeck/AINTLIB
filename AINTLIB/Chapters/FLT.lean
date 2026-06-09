import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fermat's Last Theorem and Regular Primes" =>

This chapter covers Fermat's Last Theorem: its statement, the cases that are fully formalised in mathlib, and the deeper material supplied by external Lean projects. Mathlib proves the equation $`a^n + b^n = c^n` has no positive solution for the exponents $`n = 4` (descent through the auxiliary equation $`a^4 + b^4 = c^2`) and $`n = 3` (descent in the Eisenstein integers $`\mathbb{Z}[\zeta_3]`), together with the reduction of the general theorem to odd prime exponents. Kummer's nineteenth-century theorem — Fermat's Last Theorem for *regular* primes, governed by the divisibility of Bernoulli numerators — is formalised in the flt-regular project, with the surrounding class-number and analytic theory (Kummer's criterion itself, Stickelberger, Herbrand, Thaine, the relative class-number formula, infinitely many irregular primes, and FLT for the exponent $`37`) in the KummerCriterion and flt-regular-bernoulli projects. The full theorem, via the Wiles–Taylor–Wiles modularity route, is the goal of the Imperial College FLT project. None of the external results is yet in mathlib.

Throughout, $`n, a, b, c` denote natural numbers (or integers as context demands), $`p` denotes a prime, $`\zeta_p` a primitive $`p`-th root of unity, $`K = \mathbb{Q}(\zeta_p)` the $`p`-th cyclotomic field, and $`K^+ = \mathbb{Q}(\zeta_p)^+` its maximal real subfield. The mathlib-backed nodes carry a `(lean := …)` reference naming the exact declaration; their proof sketches follow the argument that declaration actually uses. The external nodes are informal — the projects build against incompatible mathlib versions — and each records the declaration that formalises it, an exact-source permalink, and whether that formalisation is sorry-free or still in progress. The flt-regular, KummerCriterion, and Imperial FLT repositories are public; the flt-regular-bernoulli repository (which carries the Stickelberger, Herbrand, Thaine, Carlitz, and FLT-37 material) is, at the time of writing, private, and its links are given against its recorded commit for provenance even though they may not yet resolve publicly. Where a result also lives in the public KummerCriterion mirror, the permalink points there.

# Statement of Fermat's Last Theorem

:::definition "flt-with" (lean := "FermatLastTheoremWith")
Let $`R` be a semiring and $`n` a natural number. The *Fermat equation with exponent $`n` over $`R`* holds when the equation
$$`a^n + b^n = c^n, \quad a, b, c \in R,`
has no solution in which $`a`, $`b`, and $`c` are all nonzero. This is $`\texttt{FermatLastTheoremWith}\; R\; n`, unfolding to $`\forall a\,b\,c \in R,\ a \ne 0 \to b \ne 0 \to c \ne 0 \to a^n + b^n \ne c^n`.

The statement can fail for small exponents or non-discrete rings: $`\texttt{FermatLastTheoremWith}\; \mathbb{N}\; 2` is false ($`3^2 + 4^2 = 5^2`), and $`\texttt{FermatLastTheoremWith}\; \mathbb{R}\; 3` is false ($`1^3 + 1^3 = (2^{1/3})^3`).
:::

:::definition "flt-for" (lean := "FermatLastTheoremFor")
For a natural number $`n`, the *Fermat property for exponent $`n`* is the Fermat equation with exponent $`n` over the natural numbers ({uses "flt-with"}[]):
$$`\texttt{FermatLastTheoremFor}\; n \;=\; \texttt{FermatLastTheoremWith}\; \mathbb{N}\; n.`
Equivalently: there is no triple of positive naturals $`a, b, c` with $`a^n + b^n = c^n`.
:::

:::definition "fermat-last-theorem" (lean := "FermatLastTheorem")
*Fermat's Last Theorem* is the statement that the Fermat property ({uses "flt-for"}[]) holds for every exponent $`n \ge 3`:
$$`\texttt{FermatLastTheorem} \;=\; \forall n \ge 3,\ \texttt{FermatLastTheoremFor}\; n.`
For $`n = 1` and $`n = 2` it is false ($`1 + 1 = 2`; $`3^2 + 4^2 = 5^2`), so the bound $`n \ge 3` is sharp.
:::

# The exponent four: no right triangle with square hypotenuse

:::theorem "not-fermat-42" (lean := "not_fermat_42")
For nonzero integers $`a` and $`b` and any integer $`c`,
$$`a^4 + b^4 \ne c^2.`
In particular no right triangle with integer legs $`a^2, b^2` has a perfect-square hypotenuse, and there is no nontrivial solution of $`a^4 + b^4 = c^4`.
:::

:::proof "not-fermat-42"
This is Fermat's infinite descent, organised in mathlib around the predicate $`\texttt{Fermat42}\,a\,b\,c` ($`a, b \ne 0` and $`a^4 + b^4 = c^2`). Suppose a solution exists. Then `Fermat42.exists_pos_odd_minimal` produces a *minimal* one — minimising $`|c|` — that may be taken with $`a, b > 0`, $`a` odd, and $`c > 0`; minimality rests on well-ordering the natural number $`|c|`, and `coprime_of_minimal` shows a minimal solution has $`\gcd(a,b) = 1`.

`Fermat42.not_minimal` then derives a contradiction by producing a strictly smaller solution. Since $`a` is odd and $`\gcd(a,b)=1`, the triple $`(a^2, b^2, c)` is a primitive Pythagorean triple, so `PythagoreanTriple.coprime_classification'` parametrises it as $`a^2 = m^2 - n^2`, $`b^2 = 2mn`, $`c = m^2 + n^2` with $`m, n` coprime of opposite parity. Then $`(a, n, m)` is itself a primitive Pythagorean triple ($`a^2 + n^2 = m^2`), parametrised again as $`a = r^2 - s^2`, $`n = 2rs`, $`m = r^2 + s^2`. Feeding these into $`b^2 = 2mn = 4 m r s` shows $`m, r, s` are pairwise coprime with product a perfect square, hence each is (up to sign) a square; writing $`m = c_1^2`, $`r = a_1^2`, $`s = b_1^2` yields $`a_1^4 + b_1^4 = c_1^2` with $`|c_1| \le m < c`, contradicting minimality.
:::

:::theorem "flt-four" (lean := "fermatLastTheoremFour")
Fermat's Last Theorem holds for the exponent $`4`: the Fermat property ({uses "flt-for"}[]) holds at $`4`, so there are no positive naturals with $`a^4 + b^4 = c^4`.
:::

:::proof "flt-four"
Pass to the integers via `fermatLastTheoremFor_iff_int`. A solution $`a^4 + b^4 = c^4` reads as $`a^4 + b^4 = (c^2)^2`, which contradicts the impossibility of $`a^4 + b^4 = c'^2` for nonzero $`a, b` ({uses "not-fermat-42"}[]) with $`c' = c^2`. Mathlib's `fermatLastTheoremFour` is exactly this one-line reduction `apply not_fermat_42; rw [heq]; ring`.
:::

# The exponent three: descent in the Eisenstein integers

:::theorem "flt-three-case-1"
*(Case 1 for the exponent three.)* If $`a, b, c` are integers with $`3 \nmid abc`, then $`a^3 + b^3 \ne c^3`. Formalised in mathlib as `fermatLastTheoremThree_case_1`.
:::

:::proof "flt-three-case-1"
This case is elementary and is settled by congruences modulo $`9`. The key observation `cube_of_not_dvd` is that a cube coprime to $`3` is $`\equiv 1` or $`8 \pmod 9`: indeed the map $`\mathbb{Z}/9\mathbb{Z} \to \mathbb{Z}/3\mathbb{Z}` shows any $`n` with nonzero image cubes to $`1` or $`8`, checked by `decide`. If $`3 \nmid abc`, reduce the putative equality $`a^3 + b^3 = c^3` modulo $`9`: each of $`a^3, b^3, c^3` is $`1` or $`8`, and running through all eight combinations (`decide`) none satisfies $`a^3 + b^3 = c^3` in $`\mathbb{Z}/9\mathbb{Z}`. Hence no integer solution with $`3 \nmid abc` exists.
:::

:::theorem "flt-three" (lean := "fermatLastTheoremThree")
Fermat's Last Theorem holds for the exponent $`3`: the Fermat property ({uses "flt-for"}[]) holds at $`3`, so there are no positive naturals with $`a^3 + b^3 = c^3`.
:::

:::proof "flt-three"
Following Hindry's notes, mathlib reduces to coprime integer triples (`fermatLastTheoremWith_of_fermatLastTheoremWith_coprime`) and splits on whether $`3 \mid abc`. When $`3 \nmid abc`, Case 1 ({uses "flt-three-case-1"}[]) applies directly. The divisible branch reduces — after relabelling, since exactly one of $`a, b, c` is then a multiple of $`3` — to the case $`3 \mid c` only.

The hard case is treated by descent in the ring of integers $`\mathcal{O}_K = \mathbb{Z}[\zeta_3]` of $`K = \mathbb{Q}(\zeta_3)` ({uses "cyclotomic-extension"}[]), where $`\zeta_3` is a primitive cube root of unity and $`\lambda = \zeta_3 - 1`. Mathlib does not work with the bare equation but with the *generalised* equation $`a^3 + b^3 = u\,c^3` for a unit $`u \in \mathcal{O}_K^\times` (the predicate `FermatLastTheoremForThreeGen`); `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` shows that ruling out its nontrivial solutions suffices, because the descent cannot control the unit that appears. A `Solution'` is a tuple $`(a, b, c, u)` with $`c \ne 0`, $`\lambda \nmid a`, $`\lambda \nmid b`, $`\lambda \mid c`, $`\gcd(a,b) = 1`, and $`a^3 + b^3 = u\,c^3`; a `Solution` additionally has $`\lambda^2 \mid a + b`. The factorisation $`a^3 + b^3 = (a + b)(a + \zeta_3 b)(a + \zeta_3^2 b)` in $`\mathcal{O}_K`, together with unique factorisation in this PID, makes the three pairwise-coprime factors each a unit times a cube. The crucial unit input is `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent` — a special case of Kummer's lemma at $`p = 3` — which pins down the relevant units. Extracting cube roots yields a new `Solution` in which the multiplicity of $`\lambda` in $`c` has strictly dropped (`exists_Solution_multiplicity_lt`). As that multiplicity is a natural number, the descent terminates with a contradiction, so no `Solution` and hence no solution exists.
:::

# Reduction to prime exponents

:::lemma_ "flt-mono" (lean := "FermatLastTheoremWith.mono")
*(Monotonicity under divisibility.)* If $`m \mid n` and the Fermat equation with exponent $`m` holds over $`R` ({uses "flt-with"}[]), then it holds with exponent $`n`.
:::

:::proof "flt-mono"
Write $`n = m k`. A solution $`a^n + b^n = c^n` rewrites, via $`x^{mk} = (x^k)^m`, as $`(a^k)^m + (b^k)^m = (c^k)^m`, a solution at exponent $`m`. The bases $`a^k, b^k, c^k` are nonzero whenever $`a, b, c` are (a power of a nonzero element of a domain is nonzero), so the assumed result at exponent $`m` applies. This is mathlib's `FermatLastTheoremWith.mono`, proved by `pow_mul'` and `pow_ne_zero`.
:::

:::theorem "flt-odd-primes-suffice" (lean := "FermatLastTheorem.of_odd_primes")
It suffices to prove Fermat's Last Theorem for odd prime exponents: if {uses "flt-for"}[] holds for every odd prime $`p`, then {uses "fermat-last-theorem"}[] holds. The exponent-four ({uses "flt-four"}[]) and exponent-three ({uses "flt-three"}[]) cases above handle the remaining $`n` not covered by an odd prime.
:::

:::proof "flt-odd-primes-suffice"
Mathlib uses `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`: every $`n \ge 3` is either divisible by $`4` or divisible by some odd prime $`p`. In the first case the Fermat property at exponent $`4` ({uses "flt-four"}[]), and in the second the assumed property at the odd prime $`p`, transfers up to exponent $`n` by monotonicity under divisibility ({uses "flt-mono"}[]). In both branches `FermatLastTheoremWith.mono hdvd` reduces $`n` to the smaller exponent.
:::

# Bernoulli numbers

The flt-regular family of projects turns the arithmetic of regular primes into a finite, effective condition on Bernoulli numerators. We collect the Bernoulli-number facts they use. The classical Bernoulli numbers are in mathlib; the generalised numbers and their $`p`-adic congruences are developed in the KummerCriterion and flt-regular-bernoulli projects.

:::definition "bernoulli-number" (lean := "bernoulli")
The *Bernoulli numbers* $`B_0, B_1, B_2, \ldots \in \mathbb{Q}` are defined by the exponential generating function
$$`\frac{t}{e^t - 1} = \sum_{n \ge 0} B_n \frac{t^n}{n!},`
equivalently by the recursion $`\sum_{j=0}^{n}\binom{n+1}{j} B_j = [\,n = 0\,]`. Mathlib's `bernoulli` uses the convention $`B_1 = -\tfrac12` (so $`\frac{t}{e^t-1}` exactly). Thus $`B_0 = 1`, $`B_2 = \tfrac16`, $`B_4 = -\tfrac1{30}`, $`B_6 = \tfrac1{42}`, and $`B_n = 0` for every odd $`n \ge 3`. We write $`\operatorname{num}(B_{2k})` for the numerator of $`B_{2k}` in lowest terms; whether $`p` divides one of these numerators in *Kummer's range* $`1 \le k`, $`2k \le p - 3` is the data governing regularity.
:::

:::lemma_ "bernoulli-padic-integrality"
*($`p`-integrality below the boundary.)* For an odd prime $`p` and $`0 \le k < p - 1`, the Bernoulli number $`B_k` lies in $`\mathbb{Z}_p` ({uses "padic-integers"}[]); in particular $`p \nmid \operatorname{den}(B_k)`.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`bernoulli_mem_padicInt_of_lt_sub_one`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/KummerCongruence/BernoulliGeneralized.lean#L206) — sorry-free. The same result is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "bernoulli-padic-integrality"
Strong induction on $`k`. The base case is $`B_0 = 1 \in \mathbb{Z}_p`. For the step, the recursion $`\sum_{j=0}^{k}\binom{k+1}{j} B_j = 0` gives
$$`(k+1)\,B_k = -\sum_{j=0}^{k-1}\binom{k+1}{j}\,B_j.`
By the inductive hypothesis each $`B_j` ($`j < k`) is a $`p`-adic integer, and the binomial coefficients are integers, so the right-hand side lies in $`\mathbb{Z}_p`. Since $`k + 1 \le p - 1 < p`, the factor $`k + 1` is a $`p`-adic unit and may be divided out, placing $`B_k` in $`\mathbb{Z}_p`. The denominator statement is the corollary $`|B_k|_p \le 1`.
:::

:::lemma_ "von-staudt-clausen"
*(Von Staudt–Clausen at the boundary.)* For an odd prime $`p`,
$$`B_{p-1} + \frac1p \in \mathbb{Z}_p,`
so $`B_{p-1}` carries exactly one factor of $`p` in its denominator. This is the obstruction that makes the $`p`-integrality recursion break at $`k = p - 1`.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`bernoulli_pSubOne_add_inv_p_mem_padicInt`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/BernoulliGeneralized.lean#L535) — sorry-free.
:::

:::proof "von-staudt-clausen"
Specialise the recursion at $`n = p`: $`\sum_{k=0}^{p-1}\binom{p}{k} B_k = 0`. The top term is $`\binom{p}{p-1} B_{p-1} = p\,B_{p-1}`, and splitting off $`k = 0` (contributing $`B_0 = 1`) gives
$$`p\,B_{p-1} + 1 = -\sum_{k=1}^{p-2}\binom{p}{k} B_k.`
For $`1 \le k \le p - 2` each binomial $`\binom{p}{k}` is divisible by $`p`, and each $`B_k` is a $`p`-adic integer ({uses "bernoulli-padic-integrality"}[], since $`k < p - 1`). So the right-hand side is $`p` times an element of $`\mathbb{Z}_p`; dividing by $`p` in $`\mathbb{Q}_p` yields $`B_{p-1} + \tfrac1p \in \mathbb{Z}_p`.
:::

:::definition "generalised-bernoulli"
For a Dirichlet character $`\chi` modulo $`N` ({uses "dirichlet-character"}[]) valued in a $`\mathbb{Q}`-algebra, the *generalised Bernoulli numbers* $`B_{n,\chi}` are given by Washington's explicit formula
$$`B_{n,\chi} = N^{\,n-1}\sum_{a \in \mathbb{Z}/N\mathbb{Z}} \chi(a)\, B_n\!\Big(\frac aN\Big),`
with $`B_n(X)` the $`n`-th Bernoulli polynomial. They specialise to the classical numbers ({uses "bernoulli-number"}[]) at the trivial character ($`B_{n,\mathbf 1} = B_n`) and satisfy the parity law $`B_{n,\chi} = 0` unless $`\chi(-1) = (-1)^n`. The special values $`L(1-n,\chi) = -B_{n,\chi}/n` of Dirichlet $`L`-functions are governed by them; only $`B_{1,\chi}` for odd $`\chi` enters the relative class-number formula.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`BernoulliGen`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/KummerCongruence/BernoulliGeneralized.lean#L44) — sorry-free. The same definition is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::definition "gauss-sum" (lean := "gaussSum")
For a Dirichlet character $`\chi` modulo $`p` ({uses "dirichlet-character"}[]) and the additive character $`a \mapsto e^{2\pi i a/p}`, the *Gauss sum* is
$$`\tau(\chi) = \sum_{a \in \mathbb{Z}/p\mathbb{Z}} \chi(a)\, e^{2\pi i a / p} \in \mathbb{C}.`
For non-trivial $`\chi` it satisfies $`\tau(\chi)\,\tau(\bar\chi) = \chi(-1)\,p` and $`|\tau(\chi)|^2 = p`. The underlying `gaussSum` is mathlib's; the cyclotomic-field properties below are formalised in the flt-regular family.
:::

:::lemma_ "gauss-sum-norm"
*(The Gauss-sum norm relation.)* For a non-trivial Dirichlet character $`\chi` modulo $`p` ({uses "dirichlet-character"}[]),
$$`\tau(\chi)\,\tau(\bar\chi) = \chi(-1)\,p, \qquad |\tau(\chi)|^2 = p.`
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`gaussSum_mul_gaussSum_inv_stdAddChar`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/GaussSum/Basic.lean#L48) — sorry-free. The same result is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "gauss-sum-norm"
Expand the product $`\tau(\chi)\tau(\bar\chi) = \sum_{a,b}\chi(a)\bar\chi(b)\,e^{2\pi i(a+b)/p}` ({uses "gauss-sum"}[]). On the terms with $`b \ne 0` substitute $`a = tb`; the inner sum over $`b` then runs an additive character and vanishes unless $`t = -1`, leaving the surviving contribution $`\chi(-1)\,p`. Since $`\overline{\tau(\chi)} = \chi(-1)\,\tau(\bar\chi)`, the absolute-value identity $`|\tau(\chi)|^2 = \chi(-1)\,\tau(\chi)\tau(\bar\chi) = p` follows.
:::

# Regular primes and the cyclotomic ring of integers

:::definition "regular-prime"
An odd prime $`p` is *regular* if it does not divide the class number of the cyclotomic field $`K = \mathbb{Q}(\zeta_p)` ({uses "cyclotomic-extension"}[]) — equivalently, $`p` is coprime to $`\#\mathrm{Cl}(\mathcal{O}_K)` ({uses "class-group"}[]). In flt-regular this is `IsRegularPrime p`, defined as `IsRegularNumber p`, i.e. $`p.\texttt{Coprime}\,(\#\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)}))`. The smallest irregular primes are $`37, 59, 67, 101, 103, \ldots`. Regularity is the exact hypothesis under which Kummer's descent for Fermat's Last Theorem succeeds.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`IsRegularPrime`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/NumberTheory/RegularPrimes.lean#L32) — sorry-free.
:::

:::theorem "cyclotomic-ring-of-integers" (lean := "IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime")
Let $`p` be a prime and $`\zeta_p` a primitive $`p`-th root of unity. The ring of integers ({uses "ring-of-integers"}[]) of $`K = \mathbb{Q}(\zeta_p)` is the integral closure $`\mathbb{Z}[\zeta_p]`:
$$`\mathcal{O}_K = \mathbb{Z}[\zeta_p].`
For odd $`p` the power basis $`\{1, \zeta_p, \ldots, \zeta_p^{p-2}\}` has discriminant $`(-1)^{(p-1)/2}\, p^{\,p-2}` ({uses "discriminant"}[]).
:::

:::proof "cyclotomic-ring-of-integers"
Mathlib's `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime` is the prime case of the prime-power statement: $`\mathbb{Z}[\zeta_p]` is the integral closure of $`\mathbb{Z}` in $`K`. The inclusion $`\mathbb{Z}[\zeta_p] \subseteq \mathcal{O}_K` is clear since $`\zeta_p` is an algebraic integer; the reverse uses that $`\mathbb{Z}[\zeta_p]` already realises the integral closure (`isIntegralClosure_adjoin_singleton_of_prime`), an argument resting on the discriminant being a power of $`p` and the minimal polynomial $`\Phi_p` being Eisenstein at $`p`. The discriminant of the power basis is `IsCyclotomicExtension.Rat.discr_odd_prime'`, equal to $`(-1)^{(p-1)/2}\,p^{p-2}`, computed from $`\Phi_p'(\zeta_p)` and the norm $`N_{K/\mathbb{Q}}(1 - \zeta_p) = p`.
:::

# Kummer's lemma and Hilbert's theorems 90, 92, 94

:::theorem "hilbert-90" (lean := "groupCohomology.exists_div_of_norm_eq_one")
*(Hilbert's Theorem 90.)* Let $`L/K` be a finite cyclic Galois extension ({uses "is-galois"}[]) with $`\sigma` generating $`\mathrm{Gal}(L/K)`. If $`x \in L` has relative norm $`N_{L/K}(x) = 1`, then there is a unit $`y \in L^\times` with
$$`x = y / \sigma(y).`
Equivalently, the first Galois cohomology $`H^1(\mathrm{Gal}(L/K), L^\times)` is trivial.
:::

:::proof "hilbert-90"
Mathlib's `exists_div_of_norm_eq_one` proves the norm form directly. The construction is the Lagrange resolvent: from a norm-one $`x` one builds, via the auxiliary map `Hilbert90.aux` $`z \mapsto \sum_{i} (x\,\sigma(x)\cdots\sigma^{i-1}(x))\,\sigma^i(z)`, an element $`\beta = \mathrm{aux}\,z` that is nonzero for some $`z` (`aux_ne_zero`, using independence of the distinct automorphisms $`\sigma^i`) and satisfies $`\sigma(\beta)/\beta = x^{-1}`, so $`y = \beta` gives $`y/\sigma(y) = x`. The cohomological reformulation is `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`. The flt-regular project takes Hilbert 90 from mathlib (and its integral companion `exists_mul_galRestrict_of_norm_eq_one`) and builds its deeper Theorems 92 and 94 on top.
:::

:::theorem "hilbert-92"
*(Hilbert's Theorem 92.)* Let $`L/K` be a cyclic extension of number fields of prime degree $`\ell \ne 2`, with $`\sigma` generating $`\mathrm{Gal}(L/K)` ({uses "is-galois"}[]). Then there exists a unit $`\eta \in \mathcal{O}_L^\times` of relative norm $`N_{L/K}(\eta) = 1` that is *not* of the form $`\varepsilon/\sigma(\varepsilon)` for any unit $`\varepsilon \in \mathcal{O}_L^\times`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`Hilbert92`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/NumberTheory/Hilbert92.lean#L805) — sorry-free.
:::

:::proof "hilbert-92"
By Hilbert 90 ({uses "hilbert-90"}[]) every norm-one element is of the form $`\beta/\sigma(\beta)` for some $`\beta \in L^\times`; Theorem 92 asserts that this $`\beta` cannot always be taken to be a *unit*. The flt-regular proof is a rank computation on unit groups. Hilbert 91 (`Hilbert91`) constructs a *fundamental system of units* for the relative action: the Herbrand-quotient / `systemOfUnits.IsFundamental.existence` machinery shows the $`\mathbb{Z}[\mathrm{Gal}]`-module $`\mathcal{O}_L^\times` has relative rank $`\mathrm{rank}(\mathcal{O}_K^\times) + 1`. Comparing this with the rank available from norm-one units of the form $`\varepsilon/\sigma(\varepsilon)` (`Hilbert92_aux0`–`aux2`, using that $`L/K` is unramified at the infinite places for odd degree) leaves a norm-one unit unaccounted for, which is the required $`\eta`.
:::

:::theorem "hilbert-94"
*(Hilbert's Theorem 94.)* Let $`L/K` be an unramified cyclic extension of number fields of prime degree $`\ell \ne 2` ({uses "is-galois"}[]). Then there is a non-principal ideal $`I` of $`\mathcal{O}_K` whose extension $`I\mathcal{O}_L` is principal; consequently $`\ell \mid \#\mathrm{Cl}(\mathcal{O}_K)` ({uses "class-group"}[]).
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`dvd_card_classGroup_of_unramified_isCyclic`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/NumberTheory/Hilbert94.lean#L135) — sorry-free.
:::

:::proof "hilbert-94"
Apply Theorem 92 ({uses "hilbert-92"}[]) to obtain a norm-one unit $`\eta` that is not $`\varepsilon/\sigma(\varepsilon)`. By Hilbert 90 ({uses "hilbert-90"}[]) write $`\eta = \beta/\sigma(\beta)` with $`\beta \in \mathcal{O}_L` (clearing denominators). The principal ideal $`(\beta)` is $`\sigma`-stable, so it is the extension $`I\mathcal{O}_L` of an ideal $`I` of $`\mathcal{O}_K` (`comap_span_galRestrict_eq_of_cyclic`); this is `exists_not_isPrincipal_and_isPrincipal_map`. Were $`I` principal, $`\beta` would differ from a generator pulled up from $`K` by a unit, forcing $`\eta` into the forbidden form $`\varepsilon/\sigma(\varepsilon)` — contradiction. Hence $`I` is non-principal while $`I^\ell` is principal (`Ideal.isPrincipal_pow_finrank_of_isPrincipal_map`), so $`\ell` divides the class number.
:::

:::theorem "kummer-lemma"
*(Kummer's Lemma.)* Let $`p` be a regular prime ({uses "regular-prime"}[]) and $`u \in \mathbb{Z}[\zeta_p]^\times` a unit congruent to a rational integer modulo $`p`. Then $`u` is a $`p`-th power: there is a unit $`v` with $`u = v^p`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`eq_pow_prime_of_unit_of_congruent`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean#L49) — sorry-free.
:::

:::proof "kummer-lemma"
Suppose, for contradiction, that $`u` is not a $`p`-th power, and set $`L = K(u^{1/p})`, a cyclic degree-$`p` Galois extension of $`K = \mathbb{Q}(\zeta_p)`. The congruence $`u \equiv n \pmod p` forces, via $`u^{p-1} \equiv 1`, that $`(\lambda)^p \mid u^{p-1} - 1` for $`\lambda = \zeta_p - 1` (`zeta_sub_one_pow_dvd_norm_sub_pow`), and a different/ramification analysis (`KummersLemma.isUnramified`) shows $`L/K` is *unramified everywhere* — the prime $`(\lambda)` above $`p` does not ramify. Theorem 94 ({uses "hilbert-94"}[]), in the form `dvd_card_classGroup_of_unramified_isCyclic`, then gives $`p \mid \#\mathrm{Cl}(\mathcal{O}_K)`, contradicting regularity ({uses "regular-prime"}[]). Hence $`u` is a $`p`-th power. (At $`p = 3` this is the unit input `eq_one_or_neg_one_of_unit_of_congruent` used in the exponent-three descent, {uses "flt-three"}[].)
:::

# Fermat's Last Theorem for regular primes

:::theorem "flt-regular-case-one"
*(Case I.)* Let $`p` be an odd regular prime ({uses "regular-prime"}[]). Then $`x^p + y^p = z^p` has no solution in integers with $`p \nmid xyz`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`caseI`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/CaseI/Statement.lean#L256) — sorry-free.
:::

:::proof "flt-regular-case-one"
After the `CaseI.may_assume` normalisation (one may take $`p \ge 5`, $`a \not\equiv b \pmod p`, and $`\gcd\{a,b,c\} = 1`), the flt-regular proof works in $`\mathcal{O}_K = \mathbb{Z}[\zeta_p]` ({uses "cyclotomic-ring-of-integers"}[]). The factorisation $`(z)^p = \prod_{i=0}^{p-1}(x + \zeta_p^i y)` has pairwise-coprime factors, so unique factorisation in the Dedekind domain $`\mathcal{O}_K` makes each ideal $`(x + \zeta_p^i y)` a $`p`-th power $`\mathfrak{a}_i^p`. Since $`[\mathfrak{a}_i]^p = 1` in the class group ({uses "class-group"}[]) and $`p \nmid \#\mathrm{Cl}(\mathcal{O}_K)`, each $`\mathfrak{a}_i` is principal, giving $`x + \zeta_p^i y = u_i\,\alpha_i^p` with $`u_i` a unit. Because $`\alpha_i^p \equiv` a rational integer $`\pmod p`, comparing $`x + \zeta_p y` with a Galois conjugate modulo $`p` (`ex_fin_div`) produces a relation $`p \mid \sum_j f(a,b,k_1,k_2)_j\,\zeta_p^j` among the powers $`1, \zeta_p, \zeta_p^{2k}, \zeta_p^{2k-1}`; since these are part of an integral basis, `dvd_coeff_cycl_integer` forces $`p` to divide the coefficients, contradicting $`p \nmid xy`.
:::

:::theorem "flt-regular-case-two"
*(Case II.)* Let $`p` be an odd regular prime ({uses "regular-prime"}[]). Then $`x^p + y^p = z^p` has no solution in integers with $`p \mid xyz`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`caseII`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/CaseII/Statement.lean#L94) — sorry-free.
:::

:::proof "flt-regular-case-two"
This is the harder case, by infinite descent on the multiplicity of $`\lambda = \zeta_p - 1` (the prime above $`p`) in $`z`. After reducing — via $`p`'s primality, $`p \mid xyz` means $`p` divides exactly one of $`x, y, z`, and relabelling sends it to $`z` — flt-regular passes to the generalised equation over $`\mathcal{O}_K`,
$$`x^p + y^p + \varepsilon\,(\lambda^m z)^p = 0, \qquad \varepsilon \in \mathcal{O}_K^\times,\ \lambda \nmid x, y,`
and shows it has no solution (`not_exists_Int_solution'`, reducing through `not_exists_solution`). The induction step `exists_solution` factors $`x^p + y^p`, extracts pairwise-coprime ideals that are $`p`-th powers, and uses regularity (`isPrincipal_of_isPrincipal_pow_of_coprime`) to make them principal, $`x + \zeta_p^i y = (\text{unit})\cdot\alpha_i^p`. The resulting unit, being congruent to an integer modulo $`p`, is a $`p`-th power by Kummer's Lemma ({uses "kummer-lemma"}[]); absorbing it lets one extract a new solution with the $`\lambda`-multiplicity in $`z` strictly smaller. The descent on this natural number terminates, so no solution exists.
:::

:::theorem "flt-regular"
*(Fermat's Last Theorem for regular primes.)* Let $`p` be an odd regular prime ({uses "regular-prime"}[]). Then the Fermat property ({uses "flt-for"}[]) holds at the exponent $`p`: there are no positive integers $`x, y, z` with $`x^p + y^p = z^p`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular): [`flt_regular`](https://github.com/leanprover-community/flt-regular/blob/6ade127096647901d8d8804b187d1283577084bf/FltRegular/FltRegular.lean#L14) — sorry-free.
:::

:::proof "flt-regular"
Pass to integers (`fermatLastTheoremFor_iff_int`) and normalise to a coprime triple by dividing out the common gcd $`d` (`MayAssume.coprime`). Split on whether $`p \mid (a/d)(b/d)(c/d)`: the divisible branch is excluded by Case II ({uses "flt-regular-case-two"}[]) and the coprime-to-$`p` branch by Case I ({uses "flt-regular-case-one"}[]). This is precisely the body of `flt_regular`. Combined with the reduction of Fermat's Last Theorem to odd prime exponents ({uses "flt-odd-primes-suffice"}[]), it proves {uses "fermat-last-theorem"}[] for every regular prime exponent.
:::

# The class number splitting and Kummer's criterion

The arithmetic condition "$`p` regular" is converted into a finite Bernoulli computation by Kummer's criterion. The chain factors the class number as $`h = h^+ h^-`, gives an analytic formula for the relative part $`h^-`, and characterises $`p \mid h^+` via cyclotomic units. The KummerCriterion project assembles all of this into the final equivalence; the same results appear in flt-regular-bernoulli.

:::theorem "class-number-splitting"
Let $`p` be an odd prime, $`K = \mathbb{Q}(\zeta_p)` ({uses "cyclotomic-extension"}[]), and $`K^+` its maximal real subfield. Writing $`h = h(K)` and $`h^+ = h(K^+)` for the two class numbers ({uses "class-group"}[]), the extension-of-ideals map $`\mathrm{Cl}(\mathcal{O}_{K^+}) \to \mathrm{Cl}(\mathcal{O}_K)` is injective, so
$$`h^+ \mid h.`
The quotient $`h^- = h / h^+` is the *relative class number*.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`hPlus_dvd_h`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/TotallyRealSubfield/ClassGroup.lean#L245) — sorry-free. The same result is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "class-number-splitting"
This is Washington's Theorem 4.14 (Diekmann's Proposition 55). The extension $`\mathcal{O}_K / \mathcal{O}_{K^+}` is faithfully flat (`ringOfIntegers_faithfullyFlat_maximalRealSubfield`: it is finite projective and the spectrum map is surjective), so contraction recovers extension: $`(J\mathcal{O}_K) \cap \mathcal{O}_{K^+} = J`. It therefore suffices to show that an ideal $`I` of $`\mathcal{O}_{K^+}` with $`I\mathcal{O}_K` principal is itself principal. Write $`I\mathcal{O}_K = (a)`. Since $`I` comes from the real subfield, $`I\mathcal{O}_K` is fixed by complex conjugation, so $`(\bar a) = (a)`, whence $`\bar a = u\,a` for a unit $`u` with $`u\bar u = 1` (`conj_unit_mul_eq_one`). Such an antisymmetric unit of $`K` is a root of unity $`(-1)^k\zeta_p^n` (Kronecker's theorem). The factor $`-1` is excluded because the multiplicity of $`\lambda = \zeta_p - 1` in any descended generator is even (the prime below $`\lambda` ramifies with index $`2` in $`K/K^+`), so $`u = \zeta_p^n`; adjusting $`a` by $`\zeta_p^m` with $`2m \equiv n` produces a conjugation-fixed generator $`b`, which lies in $`\mathcal{O}_{K^+}` (`mem_ringOfIntegers_of_conj_eq_self`) and generates $`I`. Injectivity of `classGroupMap_injective` follows, and Lagrange's theorem for the finite class groups ({uses "class-group-finite"}[]) gives $`h^+ \mid h`.
:::

:::theorem "relative-class-number-formula"
With notation as above, the relative class number of $`\mathbb{Q}(\zeta_p)` is given by the analytic class-number formula
$$`h^- = 2p \prod_{\chi \text{ odd}} \left(-\tfrac12\, B_{1,\chi^{-1}}\right),`
the product running over the odd Dirichlet characters $`\chi` modulo $`p` ({uses "dirichlet-character"}[]), with $`B_{1,\chi^{-1}}` the generalised Bernoulli numbers ({uses "generalised-bernoulli"}[]).
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`hMinus_formula`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/HMinus/LValueReduction/Teichmuller.lean#L135) — sorry-free. The same result is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "relative-class-number-formula"
Factor the Dedekind zeta functions into Dirichlet $`L`-functions ({uses "dirichlet-lfunction"}[]): $`\zeta_K = \prod_{\chi} L(\cdot,\chi)` and $`\zeta_{K^+} = \prod_{\chi \text{ even}} L(\cdot,\chi)`, since the even characters are exactly those of $`\mathrm{Gal}(K^+/\mathbb{Q})`. Their quotient is $`\prod_{\chi\text{ odd}} L(s,\chi)`, holomorphic at $`s = 1`, so equals the ratio of residues of $`\zeta_K` and $`\zeta_{K^+}` there. The analytic class-number formula for each field, with the cyclotomic data $`w_K = 2p`, $`w_{K^+} = 2`, $`R_K = 2^{n-1}R_{K^+}`, $`|D_K| = p^n|D_{K^+}|` (where $`n = (p-1)/2`), turns the residue ratio into $`h^- = \frac{2p\,p^{n/2}}{(2\pi)^n}\prod_{\chi\text{ odd}}L(1,\chi)` ({uses "class-number-splitting"}[]). The odd special-value formula $`L(1,\chi) = \frac{\pi i\,\tau(\chi)}{p}\,B_{1,\chi^{-1}}` (from the functional equation, using $`L(0,\chi) = -B_{1,\chi}` and the Gauss sum $`\tau(\chi)`, {uses "gauss-sum"}[]) and the product of odd Gauss sums $`\prod_{\chi\text{ odd}}\tau(\chi) = i^n p^{n/2}` ({uses "gauss-sum-norm"}[]) collapse the analytic constants, leaving the displayed product of generalised Bernoulli factors.
:::

:::theorem "minus-class-number-criterion"
For an odd prime $`p`, the relative class number $`h^-` of $`\mathbb{Q}(\zeta_p)` satisfies
$$`p \mid h^- \iff \exists\, k,\ 1 \le k,\ 2k \le p - 3,\ \ p \mid \operatorname{num}(B_{2k}),`
the divisibility being by a numerator of a Bernoulli number ({uses "bernoulli-number"}[]) in Kummer's range.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`p_dvd_hMinus_iff_p_dvd_some_bernoulli`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/HMinus/HMinusCriterion.lean#L56) — sorry-free. The same result is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "minus-class-number-criterion"
Reduce the analytic formula ({uses "relative-class-number-formula"}[]) modulo $`p` in $`\mathbb{Z}_p` ({uses "padic-integers"}[]). Indexing the odd characters by powers $`\omega^j` of the Teichmüller character, the boundary character $`\omega^{p-2} = \omega^{-1}` carries the von Staudt–Clausen pole ({uses "von-staudt-clausen"}[]) but, after the explicit factor $`2p`, contributes a factor $`\equiv 1 \pmod p`. Each remaining odd factor $`-\tfrac12 B_{1,\omega^j}` is replaced, by the Kummer congruence $`B_{1,\omega^j} \equiv B_{j+1}/(j+1) \pmod p`, by $`-\tfrac12\,B_{j+1}/(j+1)`. In Kummer's range the denominators and $`-\tfrac12` are $`p`-adic units ({uses "bernoulli-padic-integrality"}[]), so the product is a non-unit exactly when some classical numerator $`\operatorname{num}(B_{2k})` is, after the reindexing $`j + 1 = 2k`.
:::

:::theorem "cyclotomic-units-saturation"
Let $`p` be an odd prime and let $`C^+ \le \mathcal{O}_{K^+}^\times` be the group of real cyclotomic units, generated by $`-1` and the units $`\varepsilon_a = \zeta_p^{1-a}\big(\tfrac{1-\zeta_p^a}{1-\zeta_p}\big)^2` ($`2 \le a \le (p-1)/2`). If $`p \nmid \operatorname{num}(B_{2k})` for every $`k` with $`1 \le k`, $`2k \le p - 3` ({uses "bernoulli-number"}[]), then
$$`p \nmid [\,\mathcal{O}_{K^+}^\times : C^+\,].`
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/CyclotomicUnits/UnitsReflection.lean#L118) — sorry-free. The same result is in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "cyclotomic-units-saturation"
The hypothesis is equivalent, by the Kummer-logarithm determinant criterion, to non-vanishing of $`\det M` for the *Kummer logarithm matrix* $`M` over $`\mathbb{F}_p`, whose $`p`-adic-logarithm entries factor as $`\operatorname{diag}(r_1,\ldots,r_g)\,V` with $`V` a Teichmüller–Vandermonde matrix and $`r_j` the Bernoulli row factor attached to $`B_{2j}/(2j)`. The Vandermonde determinant is nonzero (distinct nodes), so $`\det M \ne 0` exactly when every $`r_j \ne 0`, i.e. when every $`\operatorname{num}(B_{2j})` is prime to $`p` ({uses "bernoulli-padic-integrality"}[]). A nonzero determinant forces $`C^+` to be *exactly $`p`-saturated* in $`\mathcal{O}_{K^+}^\times`: an exponent relation $`(-1)^s\prod_a\varepsilon_a^{e_a} = y^p` reduces, after taking completed $`p`-adic logarithms, to $`M\,(e_a \bmod p) = 0`, so every $`e_a \equiv 0 \pmod p`, making the element already a $`p`-th power inside $`C^+`. A $`p`-saturated finite-index subgroup containing the ambient $`p`-torsion has index prime to $`p` (Cauchy's theorem on the quotient).
:::

:::theorem "kummer-criterion"
*(Kummer's criterion.)* An odd prime $`p` is regular ({uses "regular-prime"}[]) if and only if it divides no numerator of the Bernoulli numbers $`B_2, B_4, \ldots, B_{p-3}` ({uses "bernoulli-number"}[]):
$$`p \text{ regular} \iff \forall\, k,\ 1 \le k,\ 2k \le p - 3,\ \ p \nmid \operatorname{num}(B_{2k}).`
This converts the analytic condition "$`p \nmid h`" into a finite, effective Bernoulli computation.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`dvd_h_iff_exists_dvd_bernoulli_units`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/CyclotomicUnits/UnitsReflection.lean#L199) (the equivalence $`p \mid h \iff \exists k,\ p \mid \operatorname{num}(B_{2k})`) — sorry-free. The same result, in its `IsRegularPrime` form, is `BernoulliRegular.KummerCriterion` in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli).
:::

:::proof "kummer-criterion"
By definition $`p` is regular iff $`p \nmid h`, and $`h = h^+ h^-` ({uses "class-number-splitting"}[]). The plus-to-minus implication "$`p \mid h^+ \Rightarrow p \mid h^-`" is obtained on the unit side: if $`p \nmid h^-` then by the minus criterion ({uses "minus-class-number-criterion"}[]) all Bernoulli numerators in range are prime to $`p`, so cyclotomic-unit saturation ({uses "cyclotomic-units-saturation"}[]) gives $`p \nmid [\mathcal{O}_{K^+}^\times : C^+]`; Sinnott's prime-conductor index theorem $`p \mid [\mathcal{O}_{K^+}^\times : C^+] \iff p \mid h^+` then forces $`p \nmid h^+`. Hence $`p \mid h \iff p \mid h^-`, and combining with the minus criterion gives $`p \mid h \iff \exists k,\ p \mid \operatorname{num}(B_{2k})`. Negating both sides yields the stated equivalence.
:::

# Stickelberger's theorem and the Herbrand bridge

:::definition "stickelberger-element"
The *Stickelberger element* for the prime $`p` is
$$`\theta = \sum_{a \in (\mathbb{Z}/p\mathbb{Z})^\times} \Big\langle \frac ap \Big\rangle\, \sigma_a^{-1} \in \mathbb{Q}\big[(\mathbb{Z}/p\mathbb{Z})^\times\big],`
where $`\langle x\rangle = x - \lfloor x\rfloor` is the fractional part and $`\sigma_a` is the automorphism $`\zeta_p \mapsto \zeta_p^a` ({uses "dirichlet-character"}[]). Multiplying by an appropriate denominator gives the integral *Stickelberger ideal* $`I_\theta \subseteq \mathbb{Z}[(\mathbb{Z}/p\mathbb{Z})^\times]`.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`stickelbergerElement`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/Stickelberger.lean#L81) — sorry-free.
:::

:::theorem "stickelberger"
*(Stickelberger's theorem.)* For an odd prime $`p`, the integral Stickelberger ideal $`I_\theta` ({uses "stickelberger-element"}[]) annihilates the ideal class group ({uses "class-group"}[]) of $`\mathbb{Q}(\zeta_p)`: for any prime $`\mathfrak{l} \nmid p` and any $`\beta \in I_\theta`, the ideal $`\mathfrak{l}^\beta` is principal.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`stickelbergerCharacterCoefficientGroupRingTarget_annihilates_primeClass`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/Stickelberger/Annihilation.lean#L73) — sorry-free.
:::

:::proof "stickelberger"
The engine is the prime factorisation of a Gauss sum: for a non-trivial character $`\chi`, the principal ideal generated by $`\tau(\chi)` ({uses "gauss-sum"}[]) has its prime factorisation prescribed by the Stickelberger exponent $`\theta`. Since a principal ideal is trivial in the class group, the group-ring element $`\theta`, suitably integralised, annihilates the class of every prime $`\mathfrak{l}` above a rational prime $`\ell \ne p`. These prime classes generate the whole class group, so $`I_\theta` annihilates it entirely.
:::

:::theorem "herbrand-ribet"
*(Herbrand's theorem; the Ribet converse is the deep direction.)* Let $`\chi` be an odd Dirichlet character modulo $`p` ({uses "dirichlet-character"}[]). If the $`\chi`-eigenspace of the $`p`-part of the class group of $`\mathbb{Q}(\zeta_p)` ({uses "class-group"}[]) is non-trivial, then $`p \mid B_{1,\chi}` ({uses "generalised-bernoulli"}[]).
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`generalizedBernoulliPDivisible_of_nontrivial_oddComponent`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/Herbrand.lean#L75) — the Herbrand direction is sorry-free; the Ribet converse is not formalised.
:::

:::proof "herbrand-ribet"
Project the Stickelberger annihilation relation ({uses "stickelberger"}[]) onto the $`\chi`-eigenspace. There the Stickelberger element acts by the scalar $`B_{1,\chi}` up to a fixed nonzero normalising factor. A scalar that annihilates a non-trivial $`\mathbb{F}_p`-eigenspace must be divisible by $`p` — otherwise it would act invertibly and could not kill a nonzero element. Hence $`p \mid B_{1,\chi}`.
:::

# Thaine's theorem and the reflection route

:::theorem "thaine"
*(Thaine's theorem.)* For the maximal real subfield $`K^+ = \mathbb{Q}(\zeta_p)^+`, circular (cyclotomic) units produce annihilators of the class group $`\mathrm{Cl}(\mathcal{O}_{K^+})` ({uses "class-group"}[]): for every prime $`\ell \equiv 1 \pmod p` in a positive-density Chebotarev set (totally split in a suitable auxiliary field), a circular unit at $`\ell` yields such an annihilator, and these *Thaine auxiliary* primes form an infinite set avoiding any fixed finite set of bad primes.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`thaineAuxiliaryExistence_of_prime`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/Thaine/AuxiliaryPrimes.lean#L114) and [`infinite_setOf_thaineAuxiliary`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/Thaine/AuxiliaryPrimes.lean#L150) — sorry-free.
:::

:::proof "thaine"
Sinnott's and Washington's conventions for the group of circular units of $`K^+` coincide (`circularSubgroupKplus_eq_sinnott_eq_washington`), so either may be used ({uses "cyclotomic-units-saturation"}[]). For an auxiliary prime $`\ell \equiv 1 \pmod p`, the norm of a circular unit from $`\mathbb{Q}(\zeta_\ell)^+` down to $`K^+`, acted on by $`(\mathbb{Z}/\ell)^\times`, produces a group-ring element annihilating the relevant part of $`\mathrm{Cl}(\mathcal{O}_{K^+})`. Chebotarev density supplies infinitely many such $`\ell` outside any finite exclusion set, which is `infinite_setOf_thaineAuxiliary`.
:::

:::theorem "weak-reflection"
*(Reflection / Spiegelungssatz, unit-side form.)* For an odd prime $`p`, divisibility of the plus class number by $`p` implies divisibility of the relative class number by $`p`:
$$`p \mid h^+ \;\Longrightarrow\; p \mid h^-,`
via a non-trivial reflected eigencomponent in the minus class group. Conditionally on this principle, $`p \mid h` is again equivalent to $`p` dividing a Bernoulli numerator in Kummer's range, giving an alternative route to {uses "kummer-criterion"}[].
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion): [`weakReflection_dvd_hMinus_of_dvd_hPlus_units`](https://github.com/riccardobrasca/KummerCriterion/blob/88e6dd6748a1ba5baac97244aeb27b3e1a5e6286/KummerCriterion/CyclotomicUnits/UnitsReflection.lean#L189) — the unit-side bridge is sorry-free. The reflection route proper is developed in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (`weakReflection_componentNontrivial`), where the underlying one-sided Kummer–Furtwängler reciprocity (`Furtwaengler.oneSidedKummerPrincipalReciprocity_canonical`) remains in progress.
:::

:::proof "weak-reflection"
Write $`A = \mathrm{Cl}(\mathcal{O}_K)/p\,\mathrm{Cl}(\mathcal{O}_K)` with its action of $`\Delta = \mathrm{Gal}(K/\mathbb{Q}) \cong (\mathbb{Z}/p)^\times` ({uses "class-number-splitting"}[]). The reflection principle compares the $`i`-th and $`(1-i)`-th eigencomponents: a nonzero even component $`A_i` produces a locally-$`p`-th-power singular pseudo-unit $`\eta` with $`(\eta) = \mathfrak{b}^p`, whose $`p`-th-power residue symbol defines a nonzero character of $`A` supported on the reflected index $`1 - i`, so $`A_{1-i} \ne 0` (`weakReflection_componentNontrivial`). If $`p \mid h^+` but $`p \nmid h^-`, complex conjugation acts trivially on the minus side and no odd component can be nonzero, contradicting the reflected component built from the (necessarily even) nonzero component. The reciprocity input making the residue-symbol character well defined — the one-sided Kummer–Furtwängler principal reciprocity law $`(\alpha/(\beta))_p = (\beta/(\alpha))_p` — is the remaining undischarged piece, recorded as a named hypothesis rather than an axiom. In the main proof of Kummer's criterion ({uses "kummer-criterion"}[]) this route is bypassed in favour of the cyclotomic-unit index computation, but the unit-side bridge $`p \mid h^+ \Rightarrow p \mid h^-` is proved unconditionally.
:::

# Infinitely many irregular primes

:::lemma_ "full-divided-kummer"
*(Full divided Kummer congruence.)* Let $`p` be an odd prime and let $`m, n > 0` be even with $`m \equiv n \pmod{p-1}` and $`(p-1) \nmid n`. Then $`B_m/m \equiv B_n/n \pmod p` in $`\mathbb{Z}_p` ({uses "padic-integers"}[]) — a Kummer congruence for the divided Bernoulli numbers ({uses "bernoulli-number"}[]) with no upper bound on the exponents.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`bernoulli_div_sModEq_of_modEq_full`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/IrregularPrimes/KummerCongruenceFull.lean#L1586) — sorry-free.
:::

:::proof "full-divided-kummer"
A strengthened elementary Voronoi argument. The strong Faulhaber congruence $`\sum_{x=0}^{p-1} x^h - p B_h \in h p^2\mathbb{Z}_p` (for even $`h` with $`(p-1)\nmid h`) is proved from mathlib's Faulhaber formula by controlling every non-leading summand through von Staudt–Clausen denominator bounds ({uses "von-staudt-clausen"}[], {uses "bernoulli-padic-integrality"}[]). Substituting it into a higher-modulus Voronoi sum gives the strong Voronoi congruence $`(a^h - 1)\tfrac{B_h}{h} - a^{h-1}\sum_x x^{h-1}\lfloor xa/p\rfloor \in p\mathbb{Z}_p`. Choosing $`a` a primitive root makes $`a^h - 1` a $`p`-adic unit (as $`(p-1)\nmid h`), so dividing proves $`B_h/h \in \mathbb{Z}_p`. Applying the congruence to $`m` and $`n`: the factors $`a^m, a^n` agree because $`m \equiv n \pmod{p-1}`, and the floor sums agree modulo $`p` because their predecessor exponents are congruent, giving $`B_m/m \equiv B_n/n \pmod p`.
:::

:::theorem "infinitely-many-irregular-primes"
*(Carlitz.)* There are infinitely many irregular primes: the set $`\{\, p : p \text{ prime and not regular} \,\}` is infinite ({uses "regular-prime"}[]).
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`infinite_not_isRegularPrime`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/IrregularPrimes/Infinitude.lean#L266) — sorry-free.
:::

:::proof "infinitely-many-irregular-primes"
Carlitz's finite-set escape. Given a finite set $`S` of primes, set $`C = 2\,(\max(3, \sup S))!`, so $`q - 1 \mid C` for every prime $`q \in S`. Choosing $`t` with $`|B_M/M| > 1` for $`M = C\,2^t`, the reduced numerator of $`B_M/M` ({uses "bernoulli-number"}[]) has a prime divisor $`p`. Von Staudt–Clausen denominator control ({uses "von-staudt-clausen"}[]) shows $`p \notin S`: if $`p \in S` then $`p - 1 \mid M`, which forces $`p \nmid \operatorname{num}(B_M/M)`, a contradiction (this also gives $`p \ne 2`). The full divided Kummer congruence ({uses "full-divided-kummer"}[]) moves the witness $`B_M/M` to a Bernoulli number $`B_{m'}` in Kummer's range with the same numerator divisibility, so by Kummer's criterion ({uses "kummer-criterion"}[]) the new prime $`p` is irregular. Thus no finite set contains every irregular prime, and the set is infinite.
:::

# Fermat's Last Theorem for the exponent 37

:::theorem "flt-37"
*(Fermat's Last Theorem for the exponent $`37`, the smallest irregular prime.)* The Fermat property ({uses "flt-for"}[]) holds at $`p = 37`: $`a^{37} + b^{37} = c^{37}` has no solution in positive integers. Since $`37` is irregular, the argument uses Vandiver's parity criterion (Theorem III) in place of regularity.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli): [`fermatLastTheoremFor_thirtyseven_of_conclusion_and_vandiverLemma1`](https://github.com/CBirkbeck/flt-regular-bernoulli/blob/888f2259469123311de2bae85bd95a26f9b1ad2f/BernoulliRegular/FLT37/Final.lean#L251) — in progress: reduced to two named hypotheses (Mirimanoff–Bernoulli for Case I and the Lehmer–Vandiver descent lemma for Case II), with the input $`37 \nmid h^+` proved unconditionally.
:::

:::proof "flt-37"
The unique irregular index of $`37` is $`2k = 32`, so $`k = 16` is even and $`37 \equiv 1 \pmod 4`; thus the Vandiver III parity hypothesis holds at $`37` (`vandiverIIIHypothesis_thirtyseven`, by direct computation over Kummer's range using Kummer's criterion, {uses "kummer-criterion"}[]). Vandiver III splits — after the `MayAssume.coprime` reduction, exactly as in flt-regular's organisation ({uses "flt-regular"}[]) — into Case I ($`37 \nmid abc`) and Case II ($`37 \mid abc`).

*Case I* runs the Mirimanoff polynomials $`\varphi_n(t) = \sum_{j=1}^{p-1} j^{n-1} t^j` (with $`t = -a/b`) against Stickelberger's annihilator ({uses "stickelberger"}[]) and the $`p`-adic logarithm: the classical Mirimanoff–Bernoulli identity $`\varphi_n(t)\,B_{p-n} \equiv 0 \pmod p`, combined with the parity hypothesis (which excludes $`p \mid \operatorname{num}(B_{p-n})` when $`(p-n)/2` is odd), forces $`\varphi_n(t) \equiv 0` and hence the Bernoulli-divisibility conclusion that closes the case.

*Case II* is the Washington 9.4 / Lehmer–Vandiver descent, which needs $`37 \nmid h^+`. Here this is *not* assumed: it is proved unconditionally (`flt37_not_dvd_hPlus`) from Sinnott's index formula $`[\mathcal{O}_{K^+}^\times : C^+] = 2^{(p-3)/2} h^+` ({uses "cyclotomic-units-saturation"}[]) and a direct congruence check on $`B_{32} \bmod 37^2`. The descent itself runs on $`\sigma`-stable real cyclotomic data, factoring $`x^p + y^p` over the $`p`-th roots of unity and descending the $`\lambda`-adic exponent via a Cramér-style Fermat-like identity. The two cases reduce $`\mathrm{FLT}_{37}` to the explicit cyclotomic-integer hypotheses `MirimanoffBernoulliConclusion 37` (Case I) and `VandiverLemma1Thirtyseven` (Case II), whose discharge is the remaining work.
:::

# Reduction to modularity

The Imperial College FLT project formalises the Wiles–Taylor–Wiles route: a counterexample to Fermat's Last Theorem would build a Frey curve whose mod $`p` Galois representation is simultaneously irreducible (Mazur) and reducible (Wiles/Ribet), an impossibility. The top-level statement is reduced to these two inputs, which remain in progress.

:::definition "frey-curve"
A *Frey package* $`(a, b, c, p)` is a triple of nonzero integers with $`\gcd(a,b) = 1`, $`a \equiv 3 \pmod 4`, $`b \equiv 0 \pmod 2`, together with a prime $`p \ge 5`, such that $`a^p + b^p = c^p`. The associated *Frey curve* (Hellegouarch–Frey) is the elliptic curve ({uses "is-elliptic"}[]) over $`\mathbb{Q}` with Weierstrass equation ({uses "weierstrass-curve"}[])
$$`E : \quad Y^2 = X\,(X - a^p)(X + b^p),`
of discriminant $`\Delta = 16\,(abc)^{2p}` and $`j`-invariant $`j = 2^8(c^{2p} - (ab)^p)^3/(abc)^{2p}`. It is semistable, and a counterexample to Fermat's Last Theorem yields such a package and curve.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT): [`FreyPackage`](https://github.com/ImperialCollegeLondon/FLT/blob/6cffefeb368ca4cfabc907f86f96783a49ae4033/FLT/FreyCurve/FreyPackage.lean#L89) and [`freyCurve`](https://github.com/ImperialCollegeLondon/FLT/blob/6cffefeb368ca4cfabc907f86f96783a49ae4033/FLT/FreyCurve/FreyPackage.lean#L246) — sorry-free.
:::

:::definition "mod-p-galois-representation"
For an elliptic curve $`E` over $`\mathbb{Q}` and a prime $`p`, the absolute Galois group $`G_\mathbb{Q} = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})` ({uses "is-galois"}[]) acts on the $`p`-torsion $`E(\overline{\mathbb{Q}})[p]`, a two-dimensional $`\mathbb{F}_p`-vector space, giving the *mod $`p` Galois representation*
$$`\bar\rho_{E,p} : G_\mathbb{Q} \longrightarrow \mathrm{GL}_2(\mathbb{F}_p).`
The torsion points form an abelian group under the chord-and-tangent law ({uses "affine-points-abelian-group"}[]), on which the Galois action is by group automorphisms; its determinant is the mod $`p` cyclotomic character.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT): [`WeierstrassCurve.galoisRep`](https://github.com/ImperialCollegeLondon/FLT/blob/6cffefeb368ca4cfabc907f86f96783a49ae4033/FLT/EllipticCurve/Torsion.lean#L115) — the underlying torsion-module API is in progress.
:::

:::theorem "mazur-frey"
*(Mazur.)* For a Frey package and its Frey curve ({uses "frey-curve"}[]), the mod $`p` Galois representation ({uses "mod-p-galois-representation"}[]) $`\bar\rho` on the $`p`-torsion is *irreducible* (a simple $`\mathbb{F}_p[G_\mathbb{Q}]`-module): it has no $`G_\mathbb{Q}`-stable line.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT): [`Mazur_Frey`](https://github.com/ImperialCollegeLondon/FLT/blob/6cffefeb368ca4cfabc907f86f96783a49ae4033/FLT/FreyCurve/Contradiction.lean#L49) — in progress (`sorry`).
:::

:::proof "mazur-frey"
This rests on Mazur's theorem bounding the rational torsion of an elliptic curve over $`\mathbb{Q}` (order at most $`16`, and no point of prime order $`\ge 11`). If $`\bar\rho` were reducible it would have a stable line, hence a one-dimensional sub- or quotient-representation; analysing the possible characters (using that $`\det\bar\rho` is the cyclotomic character and the curve is semistable) would produce a rational point of order $`p \ge 5` of a kind Mazur's classification forbids. The supporting theory of torsion and isogenies is still being formalised, so the statement is currently a `sorry`.
:::

:::theorem "wiles-frey"
*(Wiles, Taylor–Wiles, Ribet.)* For a Frey package and its Frey curve ({uses "frey-curve"}[]), the mod $`p` Galois representation ({uses "mod-p-galois-representation"}[]) $`\bar\rho` is *not irreducible*.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT): [`Wiles_Frey`](https://github.com/ImperialCollegeLondon/FLT/blob/6cffefeb368ca4cfabc907f86f96783a49ae4033/FLT/FreyCurve/Contradiction.lean#L61) — in progress.
:::

:::proof "wiles-frey"
This is the deep half, the modularity route. The Frey curve's mod $`p` representation is *hardly ramified* (good reduction away from the primes dividing $`abc`, multiplicative reduction there with $`p \mid v_q(j)`). If $`\bar\rho` were irreducible, a modularity lifting theorem would make it modular, hence attached to a weight-$`2` newform of a level so small (after Ribet's level-lowering) that no such form exists. The Imperial project develops this through a general automorphy approach working directly with the $`p`-torsion; the modularity lifting input is still being formalised, so the statement reduces to in-progress automorphy results.
:::

:::theorem "flt-frey-reduction"
*(Reduction of Fermat's Last Theorem to modularity.)* {uses "fermat-last-theorem"}[] holds. Equivalently, there is no Frey package ({uses "frey-curve"}[]): a counterexample to Fermat's Last Theorem would yield a Frey curve whose mod $`p` Galois representation is simultaneously irreducible and not irreducible.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT): [`Wiles_Taylor_Wiles`](https://github.com/ImperialCollegeLondon/FLT/blob/6cffefeb368ca4cfabc907f86f96783a49ae4033/FLT/FreyCurve/Contradiction.lean#L83) — in progress; the top-level statement is reduced to the Mazur and Wiles inputs.
:::

:::proof "flt-frey-reduction"
Reduce to a prime exponent $`p \ge 5` ({uses "flt-odd-primes-suffice"}[], {uses "flt-four"}[], {uses "flt-three"}[]). A counterexample produces a Frey package and its Frey curve ({uses "frey-curve"}[]). Its mod $`p` representation $`\bar\rho` is irreducible by Mazur's theorem ({uses "mazur-frey"}[]) yet not irreducible by the Wiles–Taylor–Wiles modularity theorem ({uses "wiles-frey"}[]); the contradiction `FreyPackage.false` shows no Frey package exists. In the Imperial formalisation the top result `Wiles_Taylor_Wiles : FermatLastTheorem` is assembled from these two inputs (`apply Wiles_Frey; exact Mazur_Frey`), which remain to be discharged.
:::
