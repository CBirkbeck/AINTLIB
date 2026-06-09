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
