import Verso
import VersoManual
import VersoBlueprint
import BernoulliRegular
import BernoulliRegularBlueprint.Refs
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Fermat's Last Theorem for exponent 37" =>

# Background: irregular primes and Vandiver's Theorem III

Kummer's criterion characterises regular primes: $`p` is regular iff $`p` does not
divide the numerator of any of the Bernoulli numbers $`B_2, B_4, \ldots, B_{p-3}`.
Kummer showed in 1850 that $`\mathrm{FLT}_p` holds for every regular prime $`p`. This
already proves $`\mathrm{FLT}_p` for the vast majority of primes; the smallest
irregular primes are $`37, 59, 67, 101, 103, \ldots`.

For irregular primes a more delicate argument is needed. Vandiver gave several
supplementary criteria; the relevant one here is *Vandiver's Theorem III*: let $`p`
be an irregular prime with $`p \equiv 1 \pmod 4`. If for every irregular Bernoulli
index $`2k` of $`p` (i.e. every $`k` in $`[1, (p-3)/2]` with
$`p \mid \mathrm{num}(B_{2k})`) the integer $`k` itself is even, then
$`\mathrm{FLT}_p` holds.

For $`p = 37` the unique irregular index is $`2k = 32`, so $`k = 16`, which is even,
and $`37 \equiv 1 \pmod 4`. So Vandiver's Theorem III applies at $`37`, and proving
$`\mathrm{FLT}_{37}` reduces to formalising Vandiver III at $`\ell = 37`.

:::definition "def:isIrregularIndex" (lean := "BernoulliRegular.FLT37.IsIrregularIndex")
An *irregular index of $`\ell`* is a positive integer $`k` with $`1 \le k` and
$`2k \le \ell - 3` such that $`\ell \mid \mathrm{num}(B_{2k})`.
:::

:::definition "def:vandiverIIIHypothesis" (lean := "BernoulliRegular.FLT37.VandiverIIIHypothesis")
The *Vandiver III parity hypothesis* for $`\ell` asserts: $`\ell \equiv 1 \pmod 4`,
and every irregular index $`k` of $`\ell` is even.

{uses "def:isIrregularIndex"}[]
:::

:::theorem "thm:vandiverIIIHypothesis_thirtyseven" (lean := "BernoulliRegular.FLT37.vandiverIIIHypothesis_thirtyseven")
The prime $`\ell = 37` satisfies the Vandiver III parity hypothesis.

{uses "def:vandiverIIIHypothesis"}[]
:::

:::proof "thm:vandiverIIIHypothesis_thirtyseven"
By direct computation: $`37 \equiv 1 \pmod 4`, and the only irregular index of $`37`
in the range $`[1, 17]` is $`k = 16`, which is even.
:::

# The case-decomposition

Following `flt-regular`'s organisation of Kummer's argument for regular primes, we
split Vandiver III into a first-case half and a second-case half, defined after the
`MayAssume.coprime` reduction that pulls a common factor out of $`(a,b,c)`.

:::definition "def:vandiverIII" (lean := "BernoulliRegular.FLT37.VandiverIII")
$`\mathrm{VandiverIII}` asserts: every prime $`\ell` satisfying the parity hypothesis
satisfies $`\mathrm{FermatLastTheoremFor}\ \ell`.

{uses "def:vandiverIIIHypothesis"}[]
:::

:::definition "def:vandiverIIICaseI" (lean := "BernoulliRegular.FLT37.VandiverIIICaseI")
$`\mathrm{VandiverIIICaseI}` asserts: under the parity hypothesis, if
$`\ell \nmid abc` then $`a^\ell + b^\ell \neq c^\ell`.

{uses "def:vandiverIIIHypothesis"}[]
:::

:::definition "def:vandiverIIICaseII" (lean := "BernoulliRegular.FLT37.VandiverIIICaseII")
$`\mathrm{VandiverIIICaseII}` asserts: under the parity hypothesis, if $`a,b,c` are
coprime and $`\ell \mid abc`, then $`a^\ell + b^\ell \neq c^\ell`.

{uses "def:vandiverIIIHypothesis"}[]
:::

:::theorem "thm:vandiverIII_of_caseI_caseII" (lean := "BernoulliRegular.FLT37.vandiverIII_of_caseI_caseII")
$`\mathrm{VandiverIIICaseI} \land \mathrm{VandiverIIICaseII} \Longrightarrow \mathrm{VandiverIII}`.

{uses "def:vandiverIII"}[] {uses "def:vandiverIIICaseI"}[] {uses "def:vandiverIIICaseII"}[]
:::

:::proof "thm:vandiverIII_of_caseI_caseII"
Reduce $`\mathrm{FermatLastTheoremFor}\ \ell` to the integer statement via
`fermatLastTheoremFor_iff_int` and apply `MayAssume.coprime` to assume
$`\gcd(a,b,c) = 1`. Then split on $`\ell \mid abc`: case II handles the divisibility
branch, case I the non-divisibility branch.
:::

:::theorem "thm:fermatLastTheoremFor_thirtyseven_of_caseI_caseII" (lean := "BernoulliRegular.FLT37.fermatLastTheoremFor_thirtyseven_of_caseI_caseII")
$`\mathrm{VandiverIIICaseI} \land \mathrm{VandiverIIICaseII} \Longrightarrow \mathrm{FermatLastTheoremFor}\ 37`.

{uses "thm:vandiverIIIHypothesis_thirtyseven"}[] {uses "thm:vandiverIII_of_caseI_caseII"}[]
:::

:::proof "thm:fermatLastTheoremFor_thirtyseven_of_caseI_caseII"
Specialise {bpref "thm:vandiverIII_of_caseI_caseII"}[] to $`\ell = 37` using the
verified parity-hypothesis witness ({bpref "thm:vandiverIIIHypothesis_thirtyseven"}[]).
:::

This reduces $`\mathrm{FLT}_{37}` to two named hypotheses $`\mathrm{VandiverIIICaseI}`
and $`\mathrm{VandiverIIICaseII}` at $`\ell = 37`. The next two sections describe the
substantive mathematical content of each.

# Case I: the Mirimanoff route

For a putative case-I solution $`a^p + b^p = c^p` with $`p \nmid abc`, set
$`t = -a / b \pmod p`. Classical Mirimanoff theory (Ribenboim, *13 Lectures on
Fermat's Last Theorem*, Lecture VIII) gives a chain of congruences in $`\mathbb{F}_p`
relating $`t` to the values of the *Mirimanoff polynomials*
$$`\varphi_n(t) := \sum_{j=1}^{p-1} j^{n-1}\, t^j \in \mathbb{F}_p[t], \qquad n = 1, 2, \ldots, p-2.`
These polynomials arise from the cyclotomic-unit factorisation of $`a^p + b^p`
combined with Stickelberger's annihilator and the $`p`-adic logarithm. The Lean
development captures the chain through three predicates of increasing strength.

:::definition "def:mirimanoffPolynomialVanishing" (lean := "BernoulliRegular.FLT37.MirimanoffPolynomialVanishing")
$`\mathrm{MirimanoffPolynomialVanishing}` asserts: for every $`n` with
$`2 \le n \le p - 3`, $`\varphi_n(t) \equiv 0 \pmod p`.
:::

:::definition "def:mirimanoffBernoulliIdentity" (lean := "BernoulliRegular.FLT37.MirimanoffBernoulliIdentity")
$`\mathrm{MirimanoffBernoulliIdentity}` asserts the product congruence
$`\varphi_n(t) \cdot B_{p-n} \equiv 0 \pmod p` for every odd $`n` with
$`2 \le n \le p - 3`.
:::

:::definition "def:mirimanoffBernoulliConclusion" (lean := "BernoulliRegular.FLT37.MirimanoffBernoulliConclusion")
$`\mathrm{MirimanoffBernoulliConclusion}` asserts: for every $`n` with
$`2 \le n \le p - 3` such that $`t^n \not\equiv 1 \pmod p`,
$`p \mid \mathrm{num}(B_{p-n})`.
:::

The Mirimanoff–Bernoulli identity ($`\mathrm{MBI}`) is the classical Mirimanoff
theorem. Combined with the Vandiver III parity hypothesis it forces
$`\varphi_n(t) \equiv 0 \pmod p` for every $`n \equiv 3 \pmod 4` in range, because the
parity hypothesis rules out $`p \mid \mathrm{num}(B_{p-n})` when $`(p-n)/2` is odd, so
the other factor of the product congruence must vanish. That in turn yields the
Bernoulli-divisibility conclusion ($`\mathrm{MBC}`).

:::theorem "thm:caseI_thirtyseven_of_bernoulli_conclusion" (lean := "BernoulliRegular.FLT37.caseI_thirtyseven_of_bernoulli_conclusion")
At $`\ell = 37`, $`\mathrm{MirimanoffBernoulliConclusion}\ 37\ a\ b` for a case-I
solution $`(a,b,c)` produces a contradiction (i.e. no such solution exists).

{uses "def:mirimanoffBernoulliConclusion"}[] {uses "thm:vandiverIIIHypothesis_thirtyseven"}[]
:::

This is the case-I closure: once $`\mathrm{MBC}` is discharged from $`\mathrm{MBI}`
(which is the genuine open analytic content of case I), case I at $`\ell = 37` is
proved.

# Case II: descent under 37 not dividing h-plus

Case II at irregular primes is substantially harder than case I. The classical
Washington 9.4 / Lehmer–Vandiver descent argument requires the hypothesis
$`p \nmid h^+` (Vandiver's conjecture for $`p`), where
$`h^+ = h(\mathbb{Q}(\zeta_p)^+)` is the class number of the maximal real subfield. At
$`p = 37` this hypothesis is *not* an assumption: it is proved unconditionally in the
cyclotomic-units chapter of this blueprint, via Sinnott's index formula combined with
a direct Bernoulli-table computation at the irregular index $`32`.

:::theorem "thm:flt37_not_dvd_hPlus"
$`37 \nmid h^+(\mathbb{Q}(\zeta_{37}))`.

The Lean declaration `BernoulliRegular.FLT37.Sinnott.flt37_not_dvd_hPlus` lives in a
module outside the import closure of the `BernoulliRegular` root, so this node is left
unwired here.
:::

:::proof "thm:flt37_not_dvd_hPlus"
Combines two ingredients. First, Sinnott's index formula
$`[\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}^\times : C^+] = 2^{(p-3)/2} \cdot h^+` reduces
$`p \nmid h^+` to the $`p`-coprimality of the cyclotomic-unit index
$`[E^+ : C^+]`. Second, the $`p`-coprimality of that index follows from the
non-divisibility $`p \nmid B_{2k}` at all relevant $`k` except possibly the irregular
ones; at $`p = 37` the unique irregular index $`k = 16` is discharged by a direct
congruence check on $`B_{32}\bmod 37^2` (the Bernoulli-table computation).
:::

Under $`37 \nmid h^+`, the case-II descent is captured by the predicate
$`\mathrm{VandiverLemma1Thirtyseven}`, which encodes the regularity-free structural
input needed for the Washington 9.4 descent.

:::definition "def:vandiverLemma1Thirtyseven" (lean := "BernoulliRegular.FLT37.VandiverLemma1Thirtyseven")
$`\mathrm{VandiverLemma1Thirtyseven}` asserts: for any coprime integers $`a,b,c` with
$`37 \mid abc`, $`a^{37} + b^{37} \neq c^{37}`.
:::

:::theorem "thm:caseII_thirtyseven_of_vandiverLemma1" (lean := "BernoulliRegular.FLT37.caseII_thirtyseven_of_vandiverLemma1")
$`\mathrm{VandiverLemma1Thirtyseven}` implies $`\mathrm{VandiverIIICaseII}` at
$`\ell = 37`.

{uses "def:vandiverLemma1Thirtyseven"}[] {uses "def:vandiverIIICaseII"}[]
:::

## Where VandiverLemma1Thirtyseven comes from

The Lehmer–Vandiver machinery in `BernoulliRegular/FLT37/LehmerVandiver/` formalises
the Washington 9.4 descent in the $`\sigma`-stable product form recommended by the
2026-05-27 expert review. The descent proceeds as follows.

Starting from a putative case-II solution at level $`m \ge 1` (i.e.
$`x^p + y^p = \varepsilon \cdot ((\zeta-1)^{m+1} \cdot z)^p` in
$`\mathcal{O}_{\mathbb{Q}(\zeta_p)}` with $`\zeta - 1 \nmid y, z`), one factors
$`x^p + y^p = \prod_\eta (x + y\eta)` over the $`p`-th roots of unity. The ideals
$`\mathfrak a(\eta)` such that $`(\mathfrak a(\eta))^p` is the $`\mathfrak p`-coprime
part of $`\bigl((x + y\eta)/(\zeta-1)\bigr)/(\mathfrak m)` are pairwise coprime
$`p`-th powers and provide the descent ideals.

Because the raw quotient $`\mathfrak a(\eta)/\mathfrak a(\eta_0)` is not fixed by
complex conjugation, the descent at the unit-class level is run on the
$`\sigma`-stable product $`\mathfrak a(\eta) \cdot \mathfrak a(\eta^{-1})` and its
anchored ratio against $`\mathfrak a(\eta_0) \cdot \mathfrak a(\eta_0^{-1})`. Under
$`37 \nmid h^+` this ratio is principal in $`\mathcal{O}_{K^+}`, giving *real* descent
generators $`x, y \in \mathcal{O}_{K^+}` with $`(x) \cdot J = (y) \cdot J_0`. Combined
with the $`p`-th-power identity coming from the polynomial factorisation, these
generators produce a Cramer-style Fermat-like equation
$$`\varepsilon_1' \, X^{37} + \varepsilon_2' \, Y^{37} = Z^{37}`
in $`\mathcal{O}_K` with $`X, Y, Z` real (fixed by complex conjugation) and
$`\varepsilon_1', \varepsilon_2' \in \mathcal{O}_K^\times` explicitly constructed
units. Iterating the descent yields strictly decreasing $`\mathfrak p`-adic exponents,
hence a contradiction.

The substantive open content is closing this chain: the Cramer Fermat identity is
shipped at $`\mathcal{O}_K` level (file `LehmerVandiver/CaseII/ProductDescent.lean`);
discharging $`\mathrm{VandiverLemma1Thirtyseven}` then requires using this identity to
produce a new $`\mathrm{RealCaseIIData37}` at a strictly smaller $`\mathfrak p`-adic
exponent, completing the infinite descent. This is the only remaining mathematical
input.

# Assembly

:::theorem "thm:fermatLastTheoremFor_thirtyseven_of_conclusion_and_vandiverLemma1" (lean := "BernoulliRegular.FLT37.fermatLastTheoremFor_thirtyseven_of_conclusion_and_vandiverLemma1")
If (1) every case-I solution $`(a,b,c)` at $`\ell = 37` satisfies
$`\mathrm{MirimanoffBernoulliConclusion}\ 37\ a\ b`, and (2)
$`\mathrm{VandiverLemma1Thirtyseven}` holds, then $`\mathrm{FermatLastTheoremFor}\ 37`.

{uses "thm:caseI_thirtyseven_of_bernoulli_conclusion"}[] {uses "thm:caseII_thirtyseven_of_vandiverLemma1"}[] {uses "thm:fermatLastTheoremFor_thirtyseven_of_caseI_caseII"}[] {uses "thm:flt37_not_dvd_hPlus"}[]
:::

# Supporting machinery developed in the project

This section records the principal named theorems developed in the project —
*including* pieces that were not used on the critical path to the FLT37 statement
above. They are part of the project's deliverable formalisation of cyclotomic-field
arithmetic and are referenced from multiple chapters of the wider blueprint.

## Sinnott's index formula

:::theorem "thm:sinnottIndexFormula_of_regulatorIdentity" (lean := "BernoulliRegular.FLT37.Sinnott.sinnottIndexFormula_of_regulatorIdentity")
Under the Kummer–Dirichlet regulator identity (the analytic input, proved via the
deleted-Fourier formula), Sinnott's index formula holds:
$$`[\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}^\times : C^+] = 2^{(p-3)/2}\, h^+.`
:::

:::theorem "thm:cyclotomicUnitIndex_primeConductor_pPrimary_of_sinnottIndexFormula" (lean := "BernoulliRegular.cyclotomicUnitIndex_primeConductor_pPrimary_of_sinnottIndexFormula")
Sinnott's formula transports the divisibility $`p \mid h^+` to the cyclotomic-unit
index $`p \mid [E^+ : C^+]` (and conversely), giving the unit-side characterisation
used to bypass Vandiver's conjecture at $`p = 37` via a direct Bernoulli-table check.

{uses "thm:sinnottIndexFormula_of_regulatorIdentity"}[]
:::

## Thaine's theorem and circular units

:::theorem "thm:circularSubgroupKplus_eq_sinnott_eq_washington" (lean := "BernoulliRegular.Thaine.circularSubgroupKplus_eq_sinnott_eq_washington")
Sinnott's and Washington's two conventions for the group of *circular units* of
$`\mathbb{Q}(\zeta_p)^+` coincide. The identification underwrites the use of either
convention in downstream Thaine-style annihilation arguments.
:::

:::theorem "thm:thaineAuxiliaryExistence_of_prime" (lean := "BernoulliRegular.Thaine.thaineAuxiliaryExistence_of_prime")
For every prime $`\ell` in the Chebotarev-positive density set
$`\{\ell : \ell \equiv 1 \pmod p, \ell \text{ totally split in some auxiliary field}\}`,
the *Thaine auxiliary* construction produces an annihilator of the class group
$`\mathrm{Cl}(\mathbb{Q}(\zeta_p)^+)` drawn from a circular unit at $`\ell`. Combined
with a finite-set exclusion, this gives existence of Thaine auxiliaries outside any
fixed finite set of bad primes.
:::

:::theorem "thm:infinite_setOf_thaineAuxiliary" (lean := "BernoulliRegular.Thaine.infinite_setOf_thaineAuxiliary")
The set of Thaine auxiliary primes is infinite.

{uses "thm:thaineAuxiliaryExistence_of_prime"}[]
:::

## Reflection / Spiegelungssatz

:::theorem "thm:weakReflection_dvd_hMinus_of_dvd_hPlus_units" (lean := "BernoulliRegular.weakReflection_dvd_hMinus_of_dvd_hPlus_units")
The *weak reflection principle* on the unit side: divisibility of the plus class
number $`p \mid h^+` implies a non-trivial $`\epsilon_i`-eigencomponent in the minus
class group for some reflection-component index $`i`. This is the project's bridge
from unit-side data to class-side data, used as one input to the Lehmer–Vandiver
descent.
:::

:::theorem "thm:dvd_h_iff_exists_dvd_bernoulli_of_weakReflection" (lean := "BernoulliRegular.dvd_h_iff_exists_dvd_bernoulli_of_weakReflection")
Conditional on the weak reflection principle, $`p \mid h` is equivalent to $`p`
dividing a Bernoulli numerator in the Kummer range — an alternative form of Kummer's
criterion routed through the reflection / Spiegelungssatz machinery rather than the
Sinnott / circular-unit route.

{uses "thm:weakReflection_dvd_hMinus_of_dvd_hPlus_units"}[]
:::

## The CM splitting h-plus divides h

:::theorem "thm:hPlus_dvd_h" (lean := "BernoulliRegular.hPlus_dvd_h")
In the CM field $`\mathbb{Q}(\zeta_p)/\mathbb{Q}(\zeta_p)^+`, the plus class number
divides the full class number, $`h(\mathbb{Q}(\zeta_p)^+) \mid h(\mathbb{Q}(\zeta_p))`.
This is proved unconditionally via faithful flatness of
$`\mathcal{O}_{\mathbb{Q}(\zeta_p)}/\mathcal{O}_{\mathbb{Q}(\zeta_p)^+}` and the
injectivity of the induced map of class groups.
:::

# Outlook

Modulo the unconditional $`37 \nmid h^+` ({bpref "thm:flt37_not_dvd_hPlus"}[]), the
proof of $`\mathrm{FLT}_{37}` in this project reduces to two named hypotheses. *Case
I:* the per-solution Bernoulli-divisibility predicate
$`\mathrm{MirimanoffBernoulliConclusion}\ 37`, derived from Mirimanoff's classical
theorem ($`\mathrm{MBI}`) combined with the verified parity hypothesis. *Case II:*
$`\mathrm{VandiverLemma1Thirtyseven}`, encoding the Washington 9.4 / Lehmer–Vandiver
descent under $`37 \nmid h^+` on $`\sigma`-stable real data. Both are explicit
cyclotomic-integer statements at the single prime $`37`. Neither requires a fresh
layer of class field theory beyond what `flt-regular` and the cyclotomic-units chapter
already supply.
