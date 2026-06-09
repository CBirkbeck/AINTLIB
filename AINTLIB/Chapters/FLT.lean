import Verso
import VersoManual
import VersoBlueprint

import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fermat's Last Theorem and Regular Primes" =>

This chapter covers the statement of Fermat's Last Theorem and the results about it that are currently formalised in Mathlib: the base cases $`n = 4` (via the auxiliary equation $`a^4 + b^4 = c^2`) and $`n = 3` (via descent in the Eisenstein integers $`\mathbb{Z}[\zeta_3]`), together with the reduction to odd prime exponents. The case of regular primes — Kummer's criterion via Bernoulli numbers — is supplied by the flt-regular and flt-regular-bernoulli projects (Phase 3). The full Fermat's Last Theorem, following the Wiles–Taylor strategy through modularity of elliptic curves, is the goal of the Imperial College FLT project (also Phase 3); neither is yet in Mathlib.

Throughout, $`n, a, b, c` denote natural numbers (or integers as context demands), $`p` denotes a prime, and we write $`a \mid b` for divisibility.

# Statement of Fermat's Last Theorem

:::definition "flt-with" (lean := "FermatLastTheoremWith")
Let $`R` be a semiring and $`n` a natural number. We say the *Fermat equation with exponent $`n$* holds over $`R$* if the only solutions to
$$`a^n + b^n = c^n, \quad a, b, c \in R`
are those in which at least one of $`a, b, c` is zero. This is denoted $`\texttt{FermatLastTheoremWith}\; R\; n`.

Note that the statement can fail for small or continuous rings: $`\texttt{FermatLastTheoremWith}\; \mathbb{N}\; 2` is false ($`3^2 + 4^2 = 5^2`), and $`\texttt{FermatLastTheoremWith}\; \mathbb{R}\; 3` is false ($`1^3 + 1^3 = (2^{1/3})^3`).
:::

:::definition "flt-for" (lean := "FermatLastTheoremFor")
For a natural number $`n`, the *Fermat property for exponent $`n`* is the assertion that the equation $`a^n + b^n = c^n` has no solution in positive natural numbers. Formally, $`\texttt{FermatLastTheoremFor}\; n` is the Fermat equation with exponent $`n` over $`\mathbb{N}` ({uses "flt-with"}[]), i.e. $`\texttt{FermatLastTheoremWith}\; \mathbb{N}\; n`.
:::

:::definition "fermat-last-theorem" (lean := "FermatLastTheorem")
*Fermat's Last Theorem* is the statement: for every natural number $`n \ge 3`, there are no positive natural numbers $`a, b, c` satisfying
$$`a^n + b^n = c^n.`
Equivalently, {uses "flt-for"}[] holds for every $`n \ge 3`.
:::

# Reduction to prime exponents

:::theorem "flt-odd-primes-suffice" (lean := "FermatLastTheorem.of_odd_primes")
It suffices to prove Fermat's Last Theorem for odd prime exponents: if {uses "flt-for"}[] holds for every odd prime $`p`, then {uses "fermat-last-theorem"}[] holds.
:::

:::proof "flt-odd-primes-suffice"
Every integer $`n \ge 3` either is divisible by $`4` or has an odd prime divisor $`p`. In the first case, a solution $`a^n + b^n = c^n` would yield a solution $`(a^{n/4})^4 + (b^{n/4})^4 = (c^{n/4})^4`, reducing to {uses "flt-four"}[]. In the second case, write $`n = p \cdot k`; then $`(a^k)^p + (b^k)^p = (c^k)^p` is a solution at the prime exponent $`p`. In both cases the assumed result for the smaller exponent applies via the monotonicity of the Fermat property under divisibility.
:::

# The case $`n = 4`: no right triangles with square hypotenuse

:::theorem "not-fermat-42" (lean := "not_fermat_42")
For nonzero integers $`a` and $`b`,
$$`a^4 + b^4 \ne c^2`
for any integer $`c`. In particular, no right triangle with integer legs has a perfect-square hypotenuse.
:::

:::proof "not-fermat-42"
The proof is an infinite descent on the magnitude of $`c`. Among all integer solutions with $`a, b \ne 0`, take a minimal one (minimising $`|c|`, say with $`a, b` positive and odd). One shows, via Pythagorean-triple analysis (the pair $`(a^2, b^2)` forms a Pythagorean triple with $`c`), that the minimal solution yields a strictly smaller solution, a contradiction. Concretely, if $`a^4 + b^4 = c^2` with $`\gcd(a,b)=1` and $`a` odd, then $`a^2, b^2, c` form a primitive Pythagorean triple; parametrising it shows $`b^2` is itself a sum of two fourth powers, giving a representation of a strictly smaller value of $`c`.
:::

:::theorem "flt-four" (lean := "fermatLastTheoremFour")
Fermat's Last Theorem holds for exponent $`4`: there are no positive natural numbers $`a, b, c` satisfying
$$`a^4 + b^4 = c^4.`
:::

:::proof "flt-four"
A solution $`a^4 + b^4 = c^4` with $`a, b, c \ne 0` would give $`a^4 + b^4 = (c^2)^2`, contradicting {uses "not-fermat-42"}[]. Hence no such solution exists.
:::

# The case $`n = 3`: descent in the Eisenstein integers

:::theorem "flt-three" (lean := "fermatLastTheoremThree")
Fermat's Last Theorem holds for exponent $`3`: there are no positive natural numbers $`a, b, c` satisfying
$$`a^3 + b^3 = c^3.`
:::

:::proof "flt-three"
This establishes the Fermat property ({uses "flt-for"}[]) at the exponent $`3`. The argument uses infinite descent in the ring $`\mathbb{Z}[\zeta_3]` of Eisenstein integers — the ring of integers of the cyclotomic field $`\mathbb{Q}(\zeta_3)` ({uses "cyclotomic-extension"}[]), where $`\zeta_3` is a primitive cube root of unity. One first handles *Case 1* (when $`3 \nmid abc`): the factorisation
$$`a^3 + b^3 = (a + b)(a + \zeta_3 b)(a + \zeta_3^2 b)`
in $`\mathbb{Z}[\zeta_3]` leads to a contradiction modulo $`9`, since the three factors are pairwise coprime and their product is a cube, forcing each to be a unit times a cube, but no Eisenstein integer is simultaneously a cube and congruent to the required residue modulo $`9`.

For *Case 2* (when exactly one of $`a, b, c` is divisible by $`3`, which is $`3 \mid c` after possible relabelling), one reduces to the *generalised equation* $`a^3 + b^3 = u \cdot c^3` where $`u` is a unit of $`\mathbb{Z}[\zeta_3]`. The same factorisation, combined with unique factorisation in $`\mathbb{Z}[\zeta_3]`, shows that each factor is (up to a unit) a perfect cube. Extracting cube roots yields a new triple $`(a', b', c')` with $`a'^3 + b'^3 = u' c'^3` and $`|c'| < |c|`. Since $`|c|` cannot decrease indefinitely among positive integers, no minimal solution exists, and the equation has no solutions.
:::

# Phase 3 (not yet in Mathlib)

The formalisation of Fermat's Last Theorem for regular primes via Kummer's criterion — which characterises *regular* primes $`p` by the condition that $`p` does not divide any of the Bernoulli numbers $`B_2, B_4, \ldots, B_{p-3}` — is being developed in the flt-regular and flt-regular-bernoulli projects, and is not yet part of Mathlib. The full proof of Fermat's Last Theorem via the Wiles–Taylor theorem (modularity of semistable elliptic curves over $`\mathbb{Q}`) is the goal of the Imperial College FLT project, also not yet in Mathlib.

The nodes below are *informal*: the external projects are built against incompatible Mathlib versions, so they carry no `(lean := …)` reference. Each records where the result is formalised and whether that formalisation is sorry-free or still in progress. They connect into the dependency graph through the Mathlib-backed nodes of this and earlier chapters.

## Bernoulli numbers and Gauss sums

:::definition "bernoulli-number"
The *Bernoulli numbers* $`B_0, B_1, B_2, \ldots \in \mathbb{Q}` are the rational coefficients in the exponential generating function
$$`\frac{t}{e^t - 1} = \sum_{n \ge 0} B_n \frac{t^n}{n!}.`
Thus $`B_0 = 1`, $`B_2 = \tfrac16`, $`B_4 = -\tfrac1{30}`, and $`B_n = 0` for every odd $`n \ge 3`. We write $`\operatorname{num}(B_{2k})` for the numerator of $`B_{2k}` in lowest terms; the divisibility of these numerators by a prime $`p` is the arithmetic data that governs Kummer's criterion.
:::

:::definition "generalised-bernoulli"
For a Dirichlet character $`\chi` modulo $`p` ({uses "dirichlet-character"}[]), the *generalised Bernoulli numbers* $`B_{n,\chi}` are defined by
$$`\sum_{a=1}^{p} \chi(a)\, \frac{t e^{at}}{e^{pt} - 1} = \sum_{n \ge 0} B_{n,\chi} \frac{t^n}{n!}.`
They specialise to the classical Bernoulli numbers ({uses "bernoulli-number"}[]) at the trivial character and encode the special values of Dirichlet $`L`-functions: $`L(1 - n, \chi) = -B_{n,\chi}/n`. Only the values $`B_{1,\chi^{-1}}` for odd $`\chi` enter the relative class-number formula.
:::

:::definition "gauss-sum"
For a Dirichlet character $`\chi` modulo $`p` ({uses "dirichlet-character"}[]) and the additive character $`a \mapsto e^{2\pi i a/p}`, the *Gauss sum* is
$$`\tau(\chi) = \sum_{a \in \mathbb{Z}/p\mathbb{Z}} \chi(a)\, e^{2\pi i a / p} \in \mathbb{C}.`
For non-trivial $`\chi` it satisfies $`\tau(\chi)\,\tau(\bar\chi) = \chi(-1)\,p` and $`|\tau(\chi)|^2 = p`.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "gauss-sum"
Expanding the product $`\tau(\chi)\tau(\bar\chi) = \sum_{a,b} \chi(a)\bar\chi(b)\, e^{2\pi i (a+b)/p}` and substituting $`a = tb` on the terms with $`b \ne 0`, the inner sum over $`b` vanishes unless $`t = -1`, leaving $`\chi(-1)\,p`. Since $`\overline{\tau(\chi)} = \chi(-1)\tau(\bar\chi)`, the absolute-value identity $`|\tau(\chi)|^2 = p` follows.
:::

## Fermat's Last Theorem for regular primes (flt-regular)

:::definition "regular-prime"
An odd prime $`p` is *regular* if it does not divide the class number of the cyclotomic field $`\mathbb{Q}(\zeta_p)` ({uses "cyclotomic-extension"}[]) — equivalently, $`p \nmid \#\mathrm{Cl}(\mathcal{O}_{\mathbb{Q}(\zeta_p)})` ({uses "class-group"}[]). The smallest irregular primes are $`37, 59, 67, 101, 103, \ldots`. Regularity is the precise hypothesis under which Kummer's nineteenth-century descent argument for Fermat's Last Theorem goes through.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::theorem "cyclotomic-ring-of-integers"
Let $`p` be an odd prime, $`\zeta_p` a primitive $`p`-th root of unity, and $`\lambda_p = 1 - \zeta_p`. Then the ring of integers ({uses "ring-of-integers"}[]) of $`K = \mathbb{Q}(\zeta_p)` is
$$`\mathcal{O}_K = \mathbb{Z}[\zeta_p] = \mathbb{Z}[\lambda_p],`
and the discriminant of the power basis $`\{1, \zeta_p, \ldots, \zeta_p^{p-2}\}` is $`(-1)^{(p-1)/2} p^{\,p-2}`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::proof "cyclotomic-ring-of-integers"
Since $`\zeta_p = 1 - \lambda_p` one has $`\mathbb{Z}[\zeta_p] = \mathbb{Z}[\lambda_p]`. The discriminant of the power basis equals $`(-1)^{(p-1)/2} N_{K/\mathbb{Q}}(\Phi_p'(\zeta_p))`, and the explicit value $`\Phi_p'(\zeta_p) = -p\zeta_p^{p-1}/\lambda_p` together with $`N_{K/\mathbb{Q}}(\lambda_p) = p` gives $`p^{p-2}` up to sign. As this discriminant is a power of $`p` and the minimal polynomial $`\Phi_p` is Eisenstein at $`p`, an integrality argument forces any $`x \in \mathcal{O}_K` into $`\mathbb{Z}[\zeta_p]`; the reverse inclusion is clear.
:::

:::theorem "hilbert-90"
*(Hilbert's Theorem 90.)* Let $`K/F` be a Galois extension ({uses "is-galois"}[]) of number fields with cyclic Galois group generated by $`\sigma`. If $`\alpha \in K` has relative norm $`N_{K/F}(\alpha) = 1`, then
$$`\alpha = \beta / \sigma(\beta)`
for some $`\beta \in \mathcal{O}_K`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::proof "hilbert-90"
For a suitable $`\gamma \in K`, the Lagrange resolvent $`\beta = \sum_{i=0}^{n-1} \sigma^i(\gamma) \cdot \alpha\,\sigma(\alpha)\cdots\sigma^{i}(\alpha)` satisfies $`\alpha\,\sigma(\beta) = \beta`, using $`N_{K/F}(\alpha) = 1`. The distinct automorphisms $`\sigma^i` are linearly independent, so $`\gamma` can be chosen with $`\beta \ne 0`; clearing denominators puts $`\beta` in $`\mathcal{O}_K`.
:::

:::theorem "kummer-lemma"
*(Kummer's Lemma.)* Let $`p` be a regular prime ({uses "regular-prime"}[]) and $`u \in \mathbb{Z}[\zeta_p]^\times` a unit congruent to a rational integer modulo $`p`. Then $`u` is a $`p`-th power: there is a unit $`v \in \mathbb{Z}[\zeta_p]^\times` with $`u = v^p`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::proof "kummer-lemma"
Suppose $`u` is not a $`p`-th power and set $`K = \mathbb{Q}(\zeta_p)`, $`L = K(u^{1/p})`, a cyclic degree-$`p` Galois extension. A ramification analysis at $`\lambda_p = 1 - \zeta_p` (using the relative different) shows $`(\lambda_p)` is unramified in $`L/K`. By Hilbert 90 ({uses "hilbert-90"}[]) applied to a norm-one unit produced by Hilbert's Theorem 92, one obtains $`\beta \in \mathcal{O}_L` with $`(\beta)` the extension of an ideal $`\mathfrak{b}` of $`\mathcal{O}_K`; if $`\mathfrak{b}` were principal the Theorem-92 unit would have the forbidden form $`v/\sigma(v)`, so $`\mathfrak{b}` is non-principal, yet $`\mathfrak{b}^p` is principal — forcing $`p \mid \#\mathrm{Cl}(\mathcal{O}_K)`, contradicting regularity.
:::

:::theorem "flt-regular-case-one"
*(Case I.)* Let $`p` be an odd regular prime ({uses "regular-prime"}[]). Then
$$`x^p + y^p = z^p`
has no solution in integers $`x, y, z` with $`p \nmid xyz`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::proof "flt-regular-case-one"
In $`\mathcal{O}_K = \mathbb{Z}[\zeta_p]` ({uses "cyclotomic-ring-of-integers"}[]), a solution factors as $`(z)^p = \prod_{i=0}^{p-1}(x + \zeta_p^i y)`. The ideals $`(x + \zeta_p^i y)` are pairwise coprime, so unique factorisation in the Dedekind domain $`\mathcal{O}_K` makes each $`(x + \zeta_p^i y) = \mathfrak{a}_i^p` for some ideal $`\mathfrak{a}_i`. Since $`[\mathfrak{a}_i]^p` is trivial in the class group ({uses "class-group"}[]) and $`p \nmid \#\mathrm{Cl}(\mathcal{O}_K)`, each $`\mathfrak{a}_i` is principal, giving $`x + \zeta_p^i y = u_i \alpha_i^p` with $`u_i` a unit. Comparing this with its complex conjugate modulo $`p` and using that $`\alpha_i^p` is congruent to a rational integer modulo $`p` yields a congruence among $`1, \zeta_p, \zeta_p^{2k}, \zeta_p^{2k-1}` whose coefficients are forced to be divisible by $`p`, contradicting $`p \nmid xy`.
:::

:::theorem "flt-regular-case-two"
*(Case II.)* Let $`p` be an odd regular prime ({uses "regular-prime"}[]). Then
$$`x^p + y^p = z^p`
has no solution in integers $`x, y, z` with $`p \mid xyz`.
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::proof "flt-regular-case-two"
This is the harder case, treated by infinite descent on the power of $`\lambda_p = 1 - \zeta_p` dividing $`z`. Generalising to the equation $`x^p + y^p + \varepsilon\,(1 - \zeta_p)^{pn} z^p = 0` over $`\mathcal{O}_K` with $`\varepsilon` a unit, the factorisation and coprimality analysis produces ideals that are $`p`-th powers; principality (from regularity) yields a unit relation to which Kummer's Lemma ({uses "kummer-lemma"}[]) applies, extracting $`p`-th roots and a new solution with a strictly smaller exponent $`n`. No minimal solution can exist, so there are none.
:::

:::theorem "flt-regular"
*(Fermat's Last Theorem for regular primes.)* Let $`p` be an odd regular prime ({uses "regular-prime"}[]). Then the Fermat property ({uses "flt-for"}[]) holds at the exponent $`p`: there are no positive integers $`x, y, z` with
$$`x^p + y^p = z^p.`
Formalised in [`flt-regular`](https://github.com/leanprover-community/flt-regular) (sorry-free).
:::

:::proof "flt-regular"
Any integer solution falls into one of two cases according to whether $`p \mid xyz`. The case $`p \nmid xyz` is excluded by Case I ({uses "flt-regular-case-one"}[]) and the case $`p \mid xyz` by Case II ({uses "flt-regular-case-two"}[]). Together with the reduction of Fermat's Last Theorem to odd prime exponents ({uses "flt-odd-primes-suffice"}[]), this proves {uses "fermat-last-theorem"}[] for every regular prime exponent.
:::

## Kummer's criterion (KummerCriterion / flt-regular-bernoulli)

:::theorem "class-number-splitting"
Let $`p` be an odd prime, $`K = \mathbb{Q}(\zeta_p)` the $`p`-th cyclotomic field ({uses "cyclotomic-extension"}[]), and $`K^+` its maximal real subfield. Writing $`h = h(K)` and $`h^+ = h(K^+)` for the two class numbers ({uses "class-group"}[]), the inclusion $`\mathcal{O}_{K^+} \subseteq \mathcal{O}_K` induces an injection of class groups, so
$$`h^+ \mid h.`
The quotient $`h^- = h / h^+` is the *relative class number*.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion) and [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "class-number-splitting"
Because $`\mathcal{O}_K` is faithfully flat over $`\mathcal{O}_{K^+}`, extension followed by contraction of ideals is the identity, so an ideal of $`\mathcal{O}_{K^+}` that becomes principal in $`\mathcal{O}_K` was already principal: if $`I\mathcal{O}_K = (a)`, then $`I\mathcal{O}_K` is fixed by complex conjugation, whence $`\bar a = u a` for a unit $`u` with $`u\bar u = 1`; such a unit is $`\pm \zeta_p^m`, and adjusting $`a` by a power of $`\zeta_p` produces a conjugation-fixed generator descending to $`\mathcal{O}_{K^+}`. Thus the class-group map is injective, and Lagrange's theorem for the finite class groups ({uses "class-group-finite"}[]) gives $`h^+ \mid h`.
:::

:::theorem "relative-class-number-formula"
With notation as above, the relative class number of $`\mathbb{Q}(\zeta_p)` is given by the analytic class-number formula
$$`h^- = 2p \prod_{\chi \text{ odd}} \left(-\tfrac12 B_{1,\chi^{-1}}\right),`
the product running over the odd Dirichlet characters $`\chi` modulo $`p` ({uses "dirichlet-character"}[]), with $`B_{1,\chi^{-1}}` the generalised Bernoulli numbers ({uses "generalised-bernoulli"}[]).
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion) and [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "relative-class-number-formula"
Factor the Dedekind zeta functions of $`K` and $`K^+` into Dirichlet $`L`-functions ({uses "dirichlet-lfunction"}[]) and compare their residues at $`s = 1` via the class-number formula. The even characters account exactly for the $`K^+` factor, so dividing $`h` by $`h^+` ({uses "class-number-splitting"}[]) leaves only the odd $`L(1, \chi)`. Substituting $`L(1,\chi)` in terms of $`B_{1,\chi^{-1}}` and a Gauss sum ({uses "gauss-sum"}[]), and cancelling the analytic constants against the product of Gauss sums over odd characters, leaves the displayed product of generalised Bernoulli factors.
:::

:::theorem "minus-class-number-criterion"
For an odd prime $`p`, the relative class number $`h^-` of $`\mathbb{Q}(\zeta_p)` satisfies
$$`p \mid h^- \iff \exists\, k,\ 1 \le k,\ 2k \le p - 3,\ \ p \mid \operatorname{num}(B_{2k}),`
the divisibility being by a numerator of a Bernoulli number ({uses "bernoulli-number"}[]) in Kummer's range.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion) and [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "minus-class-number-criterion"
Reduce the analytic formula ({uses "relative-class-number-formula"}[]) modulo $`p` in $`\mathbb{Z}_p` ({uses "padic-integers"}[]). Indexing the odd characters by powers $`\omega^j` of the Teichmüller character and using the congruence $`B_{1,\omega^j} \equiv B_{j+1}/(j+1) \pmod p`, each odd factor becomes $`-\tfrac12\, B_{j+1}/(j+1)`. The constant $`-\tfrac12` and the denominators are $`p`-adic units in range, so the product is divisible by $`p` exactly when some classical Bernoulli numerator $`\operatorname{num}(B_{2k})` is, after the reindexing $`j + 1 = 2k`.
:::

:::theorem "cyclotomic-units-saturation"
Let $`p` be an odd prime and let $`C^+ \le \mathcal{O}_{K^+}^\times` be the subgroup generated by $`-1` and the real cyclotomic units $`(1 - \zeta_p^a)/(1 - \zeta_p)` of $`K^+ = \mathbb{Q}(\zeta_p)^+`. If $`p \nmid \operatorname{num}(B_{2k})` for every $`k` with $`1 \le k` and $`2k \le p - 3` ({uses "bernoulli-number"}[]), then
$$`p \nmid [\,\mathcal{O}_{K^+}^\times : C^+\,].`
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion) and [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "cyclotomic-units-saturation"
The hypothesis is equivalent to non-vanishing of the determinant of the *Kummer logarithm matrix*, whose $`p`-adic-logarithm entries factor as a diagonal of Bernoulli factors times a Teichmüller–Vandermonde matrix; the Vandermonde determinant is a unit, so the determinant is nonzero precisely when every Bernoulli diagonal factor — that is, every $`\operatorname{num}(B_{2k})` mod $`p` — is nonzero. A nonzero determinant forces $`C^+` to be $`p`-saturated in $`\mathcal{O}_{K^+}^\times` (every plus-side unit that is a $`p`-th power already has all its cyclotomic-unit exponents divisible by $`p`), and a $`p`-saturated finite-index subgroup containing the ambient $`p`-torsion has index prime to $`p`.
:::

:::theorem "kummer-criterion"
*(Kummer's criterion.)* An odd prime $`p` is regular ({uses "regular-prime"}[]) if and only if it divides no numerator of the Bernoulli numbers $`B_2, B_4, \ldots, B_{p-3}` ({uses "bernoulli-number"}[]):
$$`p \text{ regular} \iff \forall\, k,\ 1 \le k,\ 2k \le p - 3,\ \ p \nmid \operatorname{num}(B_{2k}).`
This converts the analytic condition "$`p \nmid h`" into a finite, effective Bernoulli computation.
Formalised in [`KummerCriterion`](https://github.com/riccardobrasca/KummerCriterion) and [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "kummer-criterion"
By definition $`p` is regular iff $`p \nmid h`, and $`h = h^+ h^-` ({uses "class-number-splitting"}[]). The cyclotomic-unit saturation result ({uses "cyclotomic-units-saturation"}[]) together with Sinnott's prime-conductor index theorem $`p \mid [\mathcal{O}_{K^+}^\times : C^+] \iff p \mid h^+` shows that non-divisibility of all the Bernoulli numerators forces $`p \nmid h^+`; combined with the minus class-number criterion ({uses "minus-class-number-criterion"}[]) this gives $`p \mid h \iff \exists k,\ p \mid \operatorname{num}(B_{2k})`. Negating both sides yields the stated equivalence.
:::

## Stickelberger, Herbrand–Ribet, Thaine and reflection (flt-regular-bernoulli)

:::theorem "stickelberger"
*(Stickelberger's theorem.)* For an odd prime $`p`, the integral Stickelberger ideal $`I_\theta \subseteq \mathbb{Z}[(\mathbb{Z}/p\mathbb{Z})^\times]` attached to the Stickelberger element $`\theta = \sum_{a} \langle a/p\rangle\, \sigma_a^{-1}` annihilates the ideal class group ({uses "class-group"}[]) of $`\mathbb{Q}(\zeta_p)`: for any prime $`\mathfrak{l} \nmid p` and any $`\beta \in I_\theta`, the ideal $`\mathfrak{l}^\beta` is principal.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "stickelberger"
The principal ideal generated by a Gauss sum $`\tau(\chi)` ({uses "gauss-sum"}[]) has prime factorisation prescribed by the Stickelberger exponent $`\theta`. Since a principal ideal is trivial in the class group, the group-ring element $`\theta` (suitably integralised) annihilates the class of every prime $`\mathfrak{l}` above a rational prime $`\ell \ne p`. As these prime classes generate the whole class group, $`I_\theta` annihilates it entirely.
:::

:::theorem "herbrand-ribet"
*(Herbrand's theorem; the Ribet converse is the deep direction.)* Let $`\chi` be an odd Dirichlet character modulo $`p` ({uses "dirichlet-character"}[]). If the $`\chi`-eigenspace of the $`p`-part of the class group of $`\mathbb{Q}(\zeta_p)` ({uses "class-group"}[]) is non-trivial, then $`p \mid B_{1,\chi}` ({uses "generalised-bernoulli"}[]).
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (the Herbrand direction, sorry-free).
:::

:::proof "herbrand-ribet"
Project the Stickelberger annihilation relation ({uses "stickelberger"}[]) onto the $`\chi`-eigenspace, where $`\theta` acts by the scalar $`B_{1,\chi}` up to a nonzero normalising factor. A scalar that annihilates a non-trivial $`\mathbb{F}_p`-eigenspace must be divisible by $`p`; otherwise it would act invertibly and could not kill a nonzero element. Hence $`p \mid B_{1,\chi}`.
:::

:::theorem "thaine"
*(Thaine's theorem.)* For the maximal real subfield $`K^+ = \mathbb{Q}(\zeta_p)^+`, circular (cyclotomic) units produce annihilators of the class group $`\mathrm{Cl}(\mathcal{O}_{K^+})` ({uses "class-group"}[]): for every prime $`\ell` in a positive-density Chebotarev set ($`\ell \equiv 1 \pmod p` and totally split in a suitable auxiliary field), a circular unit at $`\ell` yields such an annihilator, and these *Thaine auxiliary* primes form an infinite set lying outside any fixed finite set of bad primes.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "thaine"
Sinnott's and Washington's conventions for the group of circular units of $`K^+` coincide ({uses "cyclotomic-units-saturation"}[]), so either may be used. For an auxiliary prime $`\ell \equiv 1 \pmod p`, the norm of a circular unit down from $`\mathbb{Q}(\zeta_\ell)^+` to $`K^+` produces, via the Galois action of $`(\mathbb{Z}/\ell)^\times`, an element of the group ring that annihilates the relevant part of $`\mathrm{Cl}(\mathcal{O}_{K^+})`. Chebotarev density supplies infinitely many such $`\ell` avoiding any finite exclusion set.
:::

:::theorem "weak-reflection"
*(Reflection / Spiegelungssatz, unit-side form.)* For an odd prime $`p`, divisibility of the plus class number by $`p` implies divisibility of the relative class number by $`p`:
$$`p \mid h^+ \;\Longrightarrow\; p \mid h^-,`
via a non-trivial reflected eigencomponent in the minus class group. Conditionally on this principle, $`p \mid h` is again equivalent to $`p` dividing a Bernoulli numerator in Kummer's range, giving an alternative route to {uses "kummer-criterion"}[].
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (the unit-side bridge is sorry-free; the underlying one-sided Kummer–Furtwängler reciprocity is in progress).
:::

:::proof "weak-reflection"
Write $`A = \mathrm{Cl}(\mathcal{O}_K)/p\,\mathrm{Cl}(\mathcal{O}_K)` with its action of $`\Delta = \mathrm{Gal}(K/\mathbb{Q}) \cong (\mathbb{Z}/p)^\times` ({uses "class-number-splitting"}[]). The reflection principle compares the $`i`-th and $`(1-i)`-th eigencomponents: a nonzero even component forces a nonzero odd reflected component, built from a locally-$`p`-th-power singular pseudo-unit $`\eta` with $`(\eta) = \mathfrak{b}^p` whose $`p`-th-power residue symbol defines a nonzero character of $`A` supported on the reflected index. If $`p \mid h^+` but $`p \nmid h^-`, complex conjugation acts trivially on the minus side, so no odd component can be nonzero — contradicting the reflected component produced from the (necessarily even) nonzero component. The reciprocity input that makes the residue-symbol character well defined is the one-sided Kummer–Furtwängler principal reciprocity law, which remains to be fully discharged.
:::

## Infinitely many irregular primes and FLT for p = 37 (flt-regular-bernoulli)

:::theorem "infinitely-many-irregular-primes"
*(Carlitz.)* There are infinitely many irregular primes: the set
$$`\{\, p \in \mathbb{N} : p \text{ prime and } p \text{ not regular} \,\}`
is infinite ({uses "regular-prime"}[]).
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (sorry-free).
:::

:::proof "infinitely-many-irregular-primes"
Given a finite set $`S` of primes, set $`C = 2\,(\max(3, \sup S))!`, so $`q - 1 \mid C` for every prime $`q \in S`. Choosing $`t` so that $`|B_M/M| > 1` for $`M = C\,2^t`, the reduced numerator of $`B_M/M` ({uses "bernoulli-number"}[]) has a prime divisor $`p`; von Staudt–Clausen denominator control shows $`p \notin S` (since $`q - 1 \mid M` would force $`q \nmid \operatorname{num}(B_M/M)`). A divided-Bernoulli Kummer congruence with no upper exponent bound moves the witness $`B_M/M` to a Bernoulli number in Kummer's range, so by Kummer's criterion ({uses "kummer-criterion"}[]) the new prime $`p` is irregular. Thus no finite set contains all irregular primes.
:::

:::theorem "flt-37"
*(Fermat's Last Theorem for the exponent $`37`, the smallest irregular prime.)* The Fermat property ({uses "flt-for"}[]) holds at $`p = 37`:
$$`a^{37} + b^{37} = c^{37}`
has no solution in positive integers. The argument uses Vandiver's parity criterion (Theorem III) rather than regularity, since $`37` is irregular.
Formalised in [`flt-regular-bernoulli`](https://github.com/CBirkbeck/flt-regular-bernoulli) (in progress).
:::

:::proof "flt-37"
The unique irregular index of $`37` is $`2k = 32`, so $`k = 16` is even and $`37 \equiv 1 \pmod 4`; thus Vandiver's Theorem III applies, reducing $`\mathrm{FLT}_{37}` to a first case ($`37 \nmid abc`) and a second case ($`37 \mid abc`). Case I runs the Mirimanoff polynomials $`\varphi_n(t) = \sum_j j^{n-1} t^j` against Stickelberger's annihilator ({uses "stickelberger"}[]) and the Bernoulli parity hypothesis. Case II is the Washington–Lehmer–Vandiver descent on $`\sigma`-stable real cyclotomic data, which requires $`37 \nmid h^+`; this last fact is proved *unconditionally* here from Sinnott's index formula ({uses "cyclotomic-units-saturation"}[]) and a direct congruence check on $`B_{32} \bmod 37^2`. The two cases are reduced to explicit cyclotomic-integer hypotheses at $`p = 37` (the Mirimanoff–Bernoulli conclusion and the case-II descent lemma) whose discharge is the remaining work.
:::

## Reduction to modularity (Imperial College FLT)

:::definition "frey-curve"
A *Frey package* $`(a, b, c, p)` is a triple of pairwise-coprime nonzero integers with $`a \equiv 3 \pmod 4`, $`b \equiv 0 \pmod 2`, together with a prime $`p \ge 5`, such that $`a^p + b^p = c^p`. The associated *Frey curve* (Hellegouarch–Frey) is the elliptic curve ({uses "is-elliptic"}[]) over $`\mathbb{Q}` given by the Weierstrass equation ({uses "weierstrass-curve"}[])
$$`E : \quad Y^2 = X\,(X - a^p)(X + b^p).`
A counterexample to Fermat's Last Theorem yields a Frey package, hence a Frey curve.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT) (sorry-free).
:::

:::definition "mod-p-galois-representation"
For an elliptic curve $`E` over $`\mathbb{Q}` and a prime $`p`, the absolute Galois group $`G_\mathbb{Q} = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})` ({uses "is-galois"}[]) acts on the $`p`-torsion $`E(\overline{\mathbb{Q}})[p]`, a two-dimensional $`\mathbb{F}_p`-vector space; the resulting representation
$$`\bar\rho_{E,p} : G_\mathbb{Q} \longrightarrow \mathrm{GL}_2(\mathbb{F}_p)`
is the *mod $`p` Galois representation* attached to $`E`. The torsion points form an abelian group under the chord-and-tangent law ({uses "affine-points-abelian-group"}[]), on which the Galois action is by group automorphisms.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT) (sorry-free).
:::

:::theorem "mazur-frey"
*(Mazur.)* For a Frey package and its Frey curve ({uses "frey-curve"}[]), the mod $`p` Galois representation ({uses "mod-p-galois-representation"}[]) $`\bar\rho` attached to the $`p`-torsion is *not reducible*: it has no $`G_\mathbb{Q}`-stable line.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT) (in progress).
:::

:::proof "mazur-frey"
This rests on Mazur's 1979 theorem bounding the torsion of an elliptic curve over $`\mathbb{Q}`: the rational torsion subgroup has order at most $`16`. Reducibility of $`\bar\rho` would produce, after analysis of the possible characters, a rational point of order $`p \ge 5` of a kind Mazur's classification forbids. A substantial amount of supporting theory is still to be formalised.
:::

:::theorem "wiles-frey"
*(Wiles, Taylor–Wiles, Ribet.)* For a Frey package and its Frey curve ({uses "frey-curve"}[]), the mod $`p` Galois representation ({uses "mod-p-galois-representation"}[]) $`\bar\rho` is *not irreducible* either.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT) (in progress).
:::

:::proof "wiles-frey"
This is the deep half — the modularity route. The Frey curve is *hardly ramified* in a precise sense, and an irreducible $`\bar\rho` would, by a modularity lifting theorem, be modular, forcing the Frey curve to correspond to a weight-2 newform of a level so small that no such form exists (Ribet's level-lowering). The Imperial project develops this through a general automorphy approach working with the $`p`-torsion directly. The modularity lifting input is still being formalised.
:::

:::theorem "flt-frey-reduction"
*(Reduction of Fermat's Last Theorem to modularity.)* {uses "fermat-last-theorem"}[] holds. Equivalently, there is no Frey package ({uses "frey-curve"}[]): a counterexample to Fermat's Last Theorem would yield a Frey curve whose mod $`p` Galois representation is simultaneously not reducible and not irreducible, which is impossible.
Formalised in [`FLT`](https://github.com/ImperialCollegeLondon/FLT) (in progress; the top-level statement is reduced to the Mazur and Wiles inputs).
:::

:::proof "flt-frey-reduction"
Reducing to a prime exponent $`p \ge 5` ({uses "flt-odd-primes-suffice"}[], {uses "flt-four"}[], {uses "flt-three"}[]), a counterexample produces a Frey package and its Frey curve ({uses "frey-curve"}[]). The attached mod $`p` representation $`\bar\rho` is either reducible or irreducible; but Mazur's theorem ({uses "mazur-frey"}[]) excludes the former and the Wiles–Taylor–Wiles modularity theorem ({uses "wiles-frey"}[]) the latter. This contradiction shows no Frey package exists, hence Fermat's Last Theorem holds. In the Imperial formalisation the top result `Wiles_Taylor_Wiles` is assembled from these two inputs, which remain to be discharged.
:::
