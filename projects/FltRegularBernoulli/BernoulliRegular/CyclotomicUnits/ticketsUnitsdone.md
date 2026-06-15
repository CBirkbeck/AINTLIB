# Completed Cyclotomic-Unit Reflection Tickets

Moved from `ticketsUnits.md` after completion.

## Existing Inputs To Audit

### CU-01 - Audit the minus class-number criterion API

Status: done
Claimer: Riccardo
Started: 2026-05-16T04:33:06+02:00
Completed: 2026-05-16T04:35:58+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/HMinusCriterion.lean` with
`bernoulli_nonzero_of_not_dvd_hMinus`, the contrapositive form needed by the
unit route. The source theorem is generic for any
`[IsCyclotomicExtension {p} Q K] [IsCMField K]`, so the concrete model
`CyclotomicField p Q` is covered after installing the standard
`isCMField_of_cyclotomic` instance. No extra Nat/Int transport is needed:
`p_dvd_hMinus_iff_p_dvd_some_bernoulli` already states `hMinus` divisibility
over `Nat` and Bernoulli-numerator divisibility over `Int`.

Existing candidate:

```text
theorem p_dvd_hMinus_iff_p_dvd_some_bernoulli
    (hp_odd' : p != 2) :
    (p : Nat) | hMinus K <->
      exists k, 1 <= k /\ 2 * k <= p - 3 /\
        (p : Int) | (bernoulli (2 * k)).num
```

Deliverables:

1. Confirm the theorem is available for exactly the cyclotomic field model used
   by the unit route.
2. Add a corollary in the direction needed by the contrapositive:

```text
theorem bernoulli_nonzero_of_not_dvd_hMinus
    (hminus : not (p : Nat) | hMinus K) :
    forall k, 1 <= k -> 2 * k <= p - 3 ->
      not (p : Int) | (bernoulli (2 * k)).num
```

3. Record any transport needed between `Nat` divisibility and `Int`
   divisibility of Bernoulli numerators.

Expected difficulty: low if the existing theorem is already in the right
namespace and field model.

### CU-02 - Audit plus/minus class-number infrastructure

Status: done
Claimer: Riccardo
Started: 2026-05-16T04:36:29+02:00
Completed: 2026-05-16T04:37:08+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/ClassNumber.lean` with
`dvd_h_iff_dvd_hMinus_of_dvd_hPlus_imp`. The canonical API is `h K` and
`hPlus K` from `BernoulliRegular/TotallyRealSubfield/Basic.lean`, `hMinus K`
from `BernoulliRegular/TotallyRealSubfield/ClassGroup.lean`, and
`h_eq_hPlus_mul_hMinus` from the same class-group file. The helper proves that
a future units-route implication `(p : Nat) | hPlus K -> (p : Nat) | hMinus K`
is enough to replace the current reflection input in the internal Kummer
criterion reduction from total class number to relative class number.

Deliverables:

1. Identify the canonical `hPlus`, `hMinus`, and total class-number relation:

```text
h_eq_hPlus_mul_hMinus
```

or whatever exact theorem is currently available.

2. Check the final `KummerCriterion` proof can consume the units-route
   class-number criterion instead of `weakReflection_dvd_hMinus_of_dvd_hPlus`.
3. Record the exact file references and theorem names in this ticket.

Expected difficulty: low.

## Cyclotomic Units And The Real Unit Group

### CU-03 - Define real cyclotomic units

Status: done
Claimer: Riccardo
Started: 2026-05-16T04:38:38+02:00
Completed: 2026-05-16T04:39:42+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/Basic.lean`. The route-level
`realCyclotomicUnit` wraps the already proved `FLT37.realCyclotomicUnitPlusUnit`
in `(O KPlus)^*` for indices `2 <= a <= (p - 1) / 2`; the file proves the
range-coprimality lemma, the value/unit API, the algebra-map formula into
`O K`, the complex-conjugation fixedness statement, and membership of the image
in `realUnits K`.

Create `BernoulliRegular/CyclotomicUnits/Basic.lean`.

Mathematical definition:

For `2 <= a <= g = (p - 1) / 2`,

```text
eps_a = zeta_p^((1-a)/2) * (1 - zeta_p^a) / (1 - zeta_p).
```

The exponent `(1-a)/2` is modulo `p`.

Formalization choices:

1. Prefer a concrete cyclotomic model first, because the formula refers to a
   chosen primitive root `zeta_p`.
2. If generic `K` is required later, define the concrete objects first and
   transport through an `IsCyclotomicExtension` equivalence.
3. The real-subfield target can be either the existing maximal real subfield API
   or the fixed subring of complex conjugation. Choose the one already used by
   `hPlus`.

Deliverables:

```text
def realCyclotomicUnit (p a : Nat) : Units (ringOfIntegers KPlus)
```

with lemmas:

```text
realCyclotomicUnit_mem_real
realCyclotomicUnit_isUnit
realCyclotomicUnit_conj_eq_self
```

Proof notes:

1. `eps_a` is fixed by conjugation using
   `conj zeta_p = zeta_p^-1`.
2. It is a unit because `1 - zeta_p^a` and `1 - zeta_p` generate the same
   prime over `p` when `a` is prime to `p`.
3. For the range `2 <= a <= (p - 1) / 2`, `a` is automatically prime to `p`.

Expected difficulty: medium. The main risk is choosing the right field model.

### CU-04 - Define the real cyclotomic-unit subgroup CPlus

Status: done
Claimer: Riccardo
Started: 2026-05-16T04:40:34+02:00
Completed: 2026-05-16T04:42:31+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/Subgroup.lean` with `CPlus`,
the finite generator family `CPlusGenerator : Fin ((p - 3) / 2) -> (O KPlus)^*`,
membership lemmas for `-1` and the real cyclotomic-unit generators, the sign
subgroup `signSubgroupKplus`, its inclusion in `CPlus`, and the p-primary sign
factor lemma `prime_dvd_two_mul_iff_dvd` for odd primes.

Create `BernoulliRegular/CyclotomicUnits/Subgroup.lean`.

Define:

```text
def CPlus : Subgroup (Units (ringOfIntegers KPlus))
```

generated by `-1` and `realCyclotomicUnit p a` for `2 <= a <= (p - 1) / 2`.

Deliverables:

1. Membership lemmas for the generators.
2. A finite generator list indexed by `Fin r`, where `r = (p - 3) / 2`.
3. A torsion/signs lemma saying p-primary statements are unchanged after
   quotienting by the sign subgroup, because `p` is odd.

Expected difficulty: medium.

### CU-05 - Free-lattice index criterion

Status: done
Claimer: Riccardo
Started: 2026-05-16T04:43:12+02:00
Completed: 2026-05-16T04:44:18+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/FreeLattice.lean` with the
basis-dependent matrix criterion allowed by this ticket:
`intMatrix_index_not_dvd_iff_det_modP_ne_zero` and its reversed orientation.
It proves that an integral determinant is nonzero modulo `p` exactly when
`(p : Int)` does not divide the integral determinant; later concrete lattice
indices can use this after choosing bases.

This is pure algebra and should be proved independently of cyclotomic fields.

Statement:

For free abelian groups `N <= M` of the same finite rank and finite index,

```text
p not_dvd [M : N]
  <-> Function.Injective (N / pN -> M / pM).
```

Possible Lean statement:

```text
theorem finiteIndexSubgroup_not_dvd_index_iff_modP_injective
    {M : Type*} [AddCommGroup M] [Module Z M]
    [Module.Free Z M] [Module.Finite Z M]
    (N : AddSubgroup M) [Module.Free Z N] [Module.Finite Z N]
    (hfinite : N.index < infinity) :
    not p | N.index <->
      Function.Injective (modPMap N M p)
```

If this is too general, prove a basis-dependent matrix version first:

```text
theorem intMatrix_index_not_dvd_iff_det_modP_ne_zero
```

and use it for the concrete generated subgroup.

Expected difficulty: medium. This is a good early ticket because it is
independent of number theory.

## Analytic Cyclotomic-Unit Index

### CU-06 - Prove the p-primary cyclotomic-unit index theorem

Status: done
Claimer: Riccardo
Started: 2026-05-16T13:29:25+02:00
Reopened: 2026-05-16T15:27:00+02:00
Completed: 2026-05-16T17:55:07+02:00
Reason: Reopened because the previous closure only proved a conditional bridge
from `FLT37.Sinnott.KummerDirichletDeterminant`/`SinnottIndexFormula`. That is
useful infrastructure, but it is not the theorem in
`cyclotomic_units_weak_reflection.tex`.

TeX match required: `cyclotomic_units_weak_reflection.tex`, lines 151-177
define `C^+` using the normalized units `epsilon_a`, and lines 194-203 state
`[E^+ : C^+] = h^+` up to a power of `2`, hence for odd `p`,
`p | [E^+ : C^+] <-> p | h^+`.

Do not mark this ticket done until the Lean theorem is the TeX theorem itself:
the index subgroup must be the route's actual real cyclotomic-unit subgroup
`C^+` inside the full real unit group `E^+`, and the final theorem must have
no assumptions such as `hSinnott`, `hdet`,
`FLT37.Sinnott.KummerDirichletDeterminant`,
`FLT37.Sinnott.SinnottIndexFormula`, or any renamed package/source `Prop`.

Result: Done. The final theorem is
`BernoulliRegular.cyclotomicUnitIndex_primeConductor_pPrimary` in
`BernoulliRegular/CyclotomicUnits/NormalizedIndex.lean`:

```text
p | (normalizedCPlus hp_odd hp_three).index <-> p | hPlus K
```

for every odd prime `p`, with `hp_three` derived from primality and `p != 2`.
The theorem uses the normalized TeX subgroup `C^+`, not the old squared-family
proxy, and has no `SinnottIndexFormula`, `KummerDirichletDeterminant`, `hdet`,
or renamed source hypothesis. The `p >= 5` branch is CU-06b; the `p = 3`
branch is CU-06c. Built with `lake build BernoulliRegular`.

Create `BernoulliRegular/CyclotomicUnits/IndexFormula.lean`.

This is a hard analytic theorem. It must be a named theorem, not hidden inside
the weak-reflection proof.

Target statement:

```text
theorem cyclotomicUnitIndex_primeConductor_pPrimary
    (p : Nat) [Fact p.Prime] (hp_odd : p != 2) :
    (p : Nat) | indexOf CPlus EPlus <-> (p : Nat) | hPlus K
```

Equivalent nondivisibility form:

```text
theorem not_dvd_cyclotomicUnitIndex_iff_not_dvd_hPlus :
    not (p : Nat) | indexOf CPlus EPlus <->
      not (p : Nat) | hPlus K
```

Mathematical proof to formalize:

1. Define the real logarithmic regulator lattice.
2. Prove the regulator ratio equals the subgroup index.
3. Factor `zeta_KPlus(s)` into even Dirichlet `L`-series.
4. Use the analytic class number formula for `KPlus`.
5. Express `L(1, chi)` for even nontrivial `chi` by logarithms
   `log |1 - zeta_p^a|`.
6. Use the group determinant calculation to identify the cyclotomic-unit
   regulator with the same product of `L(1, chi)` factors.
7. Compare the two formulas. The discrepancy is a power of `2`, irrelevant for
   odd `p`.

Expected difficulty: very high. This is one of the two main hard inputs of the
route.

#### CU-06a - Conditional squared-family Sinnott bridge

Status: done
Claimer: Riccardo
Started: 2026-05-16T13:29:25+02:00
Completed: 2026-05-16T13:31:24+02:00
TeX audit: Not identical to the TeX theorem. This subtask is only a conditional
bridge for the existing squared-family Sinnott API, so it does not close
CU-06.
Result: Added `BernoulliRegular/CyclotomicUnits/IndexFormula.lean`. The file
defines the real cyclotomic-unit index subgroup used by the existing Sinnott
regulator API and proves
`cyclotomicUnitIndex_primeConductor_pPrimary_of_kummerDirichletDeterminant`,
plus the nondivisibility form. The hard analytic source is not hidden: the
theorem is explicitly conditional on the named input
`FLT37.Sinnott.KummerDirichletDeterminant`, and the proof removes the
`2^((p - 3) / 2)` normalization factor using `p != 2`.

#### CU-06b - Exact TeX cyclotomic-unit index theorem

Status: done
Claimer: Riccardo
Started: 2026-05-16T15:27:00+02:00
Completed: 2026-05-16T17:20:40+02:00
Goal: Prove the unconditional TeX theorem for the actual real
cyclotomic-unit subgroup `C^+` and full real unit group `E^+`:

```text
theorem cyclotomicUnitIndex_primeConductor_pPrimary
    (p : Nat) [Fact p.Prime] (hp_odd : p != 2)
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} Q K] [IsCMField K] :
    (p : Nat) | indexOf CPlus EPlus <-> (p : Nat) | hPlus K
```

Required source audit before completion:

1. The subgroup on the left is the TeX `C^+`, generated by `-1` and the real
   cyclotomic units, not merely the existing squared-family proxy unless an
   unconditional equality or odd-primary index equivalence with `C^+` is proved.
2. The regulator/index comparison uses the actual `C^+ <= E^+` inclusion and
   finite index, not a bundled source assumption.
3. The analytic class-number comparison is proved from concrete ingredients
   already in the repo, including the CU-08 deleted Fourier determinant, and
   does not assume any `SinnottIndexFormula`, `KummerDirichletDeterminant`, or
   equivalent named source `Prop`.

Former blocker: `BernoulliRegular/CyclotomicUnits/IndexFormula.lean` only
supplied the conditional bridge in CU-06a. This is now resolved for the
substantive `p >= 5` branch by
`BernoulliRegular/CyclotomicUnits/NormalizedIndex.lean`, which proves
`FLT37.Sinnott.KummerDirichletDeterminant` internally from the CU-08 deleted
Fourier determinant and then removes the squared-family proxy.

Former exactness blocker: the TeX group `C^+` is generated by `-1` and the
normalized real cyclotomic units `epsilon_a` from lines 151-177, while the
old Lean index bridge used the squared family. This is now resolved by
`NormalizedUnits.lean` and `NormalizedSubgroup.lean`: the normalized units are
descended to `(O KPlus)^*`, their squares are identified with the old
squared-family generators, and the relative quotient has 2-primary index.

Progress: 2026-05-16T16:04:57+02:00 - Added
`BernoulliRegular/CyclotomicUnits/IndexDeterminant.lean`. It proves the
matrix-level determinant source
`detASubBSqEqProdNontrivialQeSq_of_deletedFourier` from the CU-08 arbitrary
deleted-row Fourier determinant by identifying
`FLT37.Sinnott.sinnottMatrixA - FLT37.Sinnott.sinnottMatrixB`, after transpose
and reindexing, with
`deletedConvolutionMulMatrixAtReindexed`. This removes the old determinant
source proposition for the `p >= 5` squared-family branch. Built with
`lake build BernoulliRegular.CyclotomicUnits.IndexDeterminant` and
`lake build BernoulliRegular`.

P=3 audit: Closed directly in
`BernoulliRegular/CyclotomicUnits/NormalizedIndex.lean`. The theorem
`cyclotomicUnitIndex_primeConductor_pPrimary_of_eq_three` proves the same
index equivalence for `p = 3`: the cyclotomic ring of integers is a PID by
`IsCyclotomicExtension.Rat.three_pid`, hence `hPlus K = 1`, and the real unit
rank is zero, so Dirichlet's unit theorem plus the existing real torsion
calculation gives `normalizedCPlus = ⊤` and index `1`.

Resolved blockers for the substantive `p >= 5` branch:

1. The left-hand subgroup was the squared-family subgroup. To match the
   TeX theorem, define the normalized units
   `epsilon_a = zeta_p^((1-a)/2) * cyclotomicUnit a`, descend them to
   `(O KPlus)^*`, prove their squares are the existing
   `realCyclotomicUnitPlusUnit` generators, and prove the resulting index
   comparison is a power of `2`.
   Result: done in `NormalizedUnits.lean` and `NormalizedSubgroup.lean`.
2. The final theorem may only be named
   `cyclotomicUnitIndex_primeConductor_pPrimary` once (1) is proved and the
   source hypotheses are removed.
   Result: done in `NormalizedIndex.lean`.

TeX audit: Done for the substantive `p >= 5` branch. The Lean theorem
`BernoulliRegular.cyclotomicUnitIndex_primeConductor_pPrimary_of_five_le` in
`BernoulliRegular/CyclotomicUnits/NormalizedIndex.lean` has the normalized
TeX subgroup `normalizedCPlus = <-1, epsilon_2, ..., epsilon_g>` on the left:

```text
p | (normalizedCPlus hp_odd hp_three).index <-> p | hPlus K
```

It assumes only `[Fact p.Prime]`, the standard cyclotomic/CM field instances,
and `5 <= p`; it does not assume `SinnottIndexFormula`,
`KummerDirichletDeterminant`, or a renamed source package. The determinant
input is proved from `detASubBSqEqProdNontrivialQeSq_of_deletedFourier` in
`BernoulliRegular/CyclotomicUnits/IndexDeterminant.lean`, which in turn uses
the CU-08 deleted Fourier determinant. The transfer from the old squared
family to the normalized TeX subgroup is via the square identities in
`NormalizedUnits.lean`, the subgroup and 2-primary relative-index lemmas in
`NormalizedSubgroup.lean`, and the abstract odd-primary index transfer in
`IndexComparison.lean`. Built with `lake build BernoulliRegular`.

##### CU-06b1 - Record the normalized-unit strategy from the TeX note

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:28:52+02:00
Completed: 2026-05-16T16:30:44+02:00

Source: `BernoulliRegular/CyclotomicUnits/cu06b_normalized_cyclotomic_units.tex`.

Deliverable: keep the CU-06b implementation split aligned with the TeX proof:

1. Define the normalized units
   `epsilon_a = zeta_p^e * (1 - zeta_p^a) / (1 - zeta_p)`, with
   `2 * e = 1 - a mod p`, for `2 <= a <= (p - 1) / 2`.
2. Prove these elements are integral units in `K`, fixed by complex conjugation,
   and descend to `(O KPlus)^*`.
3. Define the normalized subgroup `C^+` generated by `-1` and the descended
   `epsilon_a`.
4. Identify `epsilon_a ^ 2` with the existing squared-family generators used
   by `realCyclotomicUnitPlusUnit`/`CPlus`.
5. Prove the squared-family subgroup is contained in normalized `C^+`.
6. Prove the relative quotient is killed by `2`; hence its relative index
   divides a power of `2`.
7. Use odd-prime subgroup-index arithmetic to transfer
   `p | [E^+ : C_sq^+]` iff `p | [E^+ : C^+]`.
8. Combine this transfer with the squared-family theorem to obtain the exact
   TeX theorem for normalized `C^+`, with no hidden source proposition.

Closure audit required: CU-06b may be marked `done` only after the Lean theorem
has normalized `C^+` on the left, assumes only the concrete TeX hypotheses
(`p >= 5` for the substantive branch), and contains no conditional
`SinnottIndexFormula`, `KummerDirichletDeterminant`, or renamed equivalent
source hypothesis.

Result: The TeX strategy is split into CU-06b2 through CU-06b7 below. The
split explicitly separates the abstract index transfer, normalized unit
construction, real-subfield descent, square comparison, 2-primary relative
index proof, and final exact theorem.

##### CU-06b2 - Odd-primary subgroup-index transfer

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:28:52+02:00
Completed: 2026-05-16T16:30:44+02:00

Goal: prove the abstract group-index lemma used in the TeX proof. If
`H <= K <= G`, the relative index `[K : H]` divides `2^r`, and `p` is an odd
prime, then

```text
p | [G : H] <-> p | [G : K].
```

In Lean terms, this should use `Subgroup.relIndex_mul_index` and contain no
cyclotomic assumptions.

Result: Added `BernoulliRegular/CyclotomicUnits/IndexComparison.lean` with
`subgroup_index_prime_dvd_iff_of_relIndex_dvd_two_pow`. The proof is purely
group-theoretic: it uses `Subgroup.relIndex_mul_index` and removes the relative
index by `prime_not_dvd_of_dvd_two_pow` for odd primes. Built with
`lake build BernoulliRegular.CyclotomicUnits.IndexComparison`.

##### CU-06b3 - Normalized cyclotomic unit in the full cyclotomic field

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:30:44+02:00
Completed: 2026-05-16T16:45:47+02:00

Goal: define the normalized element

```text
epsilon_a = zeta_p^e * (1 - zeta_p^a) / (1 - zeta_p)
```

for `2 <= a <= (p - 1) / 2` and `2 * e = 1 - a mod p`, prove it is a unit of
`O K`, and prove it is fixed by complex conjugation. This is exactly
Lemmas `ratio-unit` and `epsilon-real` in the TeX note.

TeX audit: This closes only the K-side part of the TeX construction. It proves
the quotient unit is a genuine unit by using `FLT37.cyclotomicUnitUnit`, proves
the canonical exponent congruence `2e = 1 - a mod p`, and proves the
conjugation-fixedness calculation explicitly. It does not close descent or
index comparison.

Result: Added `BernoulliRegular/CyclotomicUnits/NormalizedUnits.lean` with
`normalizedCyclotomicUnitKWithExponent`, canonical
`normalizedCyclotomicUnitExponent`, range wrapper
`normalizedCyclotomicUnitKOfRange`, and
`unitsComplexConj_normalizedCyclotomicUnitKOfRange`. Built with
`lake build BernoulliRegular.CyclotomicUnits.NormalizedUnits`.

##### CU-06b4 - Descent to the real subfield and normalized subgroup

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:38:00+02:00
Completed: 2026-05-16T16:45:47+02:00

Goal: descend the normalized units from `O K` to `(O KPlus)^*` and define the
TeX subgroup

```text
C^+ = <-1, epsilon_2, ..., epsilon_g> <= (O KPlus)^*.
```

The subgroup must be the normalized TeX subgroup, not the squared-family proxy.

TeX audit: The subgroup is the normalized TeX subgroup generated by `-1` and
the descended normalized units. It is deliberately named `normalizedCPlus` so
it is not confused with the older squared-family `CPlus` proxy.

Result: `NormalizedUnits.lean` now proves
`exists_normalizedCyclotomicUnitPlus` and packages
`normalizedCyclotomicUnitPlusUnit : (O KPlus)^*`. Added
`BernoulliRegular/CyclotomicUnits/NormalizedSubgroup.lean` with
`normalizedCPlus`, `neg_one_mem_normalizedCPlus`, and
`normalizedCPlusGenerator_mem`. Built with
`lake build BernoulliRegular.CyclotomicUnits.NormalizedSubgroup`.

##### CU-06b5 - Square identity with the existing squared-family generators

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:41:00+02:00
Completed: 2026-05-16T16:45:47+02:00

Goal: prove

```text
epsilon_a ^ 2 =
  zeta_p^(1-a) * ((1 - zeta_p^a) / (1 - zeta_p)) ^ 2
```

and identify the descended square with the existing
`realCyclotomicUnitPlusUnit`/`realCyclotomicUnit` generator. This is the bridge
between the normalized subgroup and the already implemented squared-family
subgroup.

TeX audit: The square identity is proved at the `O K` value level and then as
a descended unit equality in `(O KPlus)^*`; it is not assumed through the old
Sinnott source propositions.

Result: Added
`normalizedCyclotomicUnitKOfRange_sq_val_eq_realCyclotomicUnit` and
`normalizedCyclotomicUnitPlusUnit_sq_eq_realCyclotomicUnit` in
`NormalizedUnits.lean`. `NormalizedSubgroup.lean` proves
`normalizedCPlusGenerator_sq_eq_CPlusGenerator` and
`normalizedCPlusGenerator_sq_mem_CPlus`.

##### CU-06b6 - Squared subgroup has 2-primary relative index in normalized subgroup

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:43:00+02:00
Completed: 2026-05-16T16:52:00+02:00

Goal: prove `C_sq^+ <= C^+` and that every generator of `C^+ / C_sq^+` is
killed by `2`. Deduce `[C^+ : C_sq^+]` divides `2^r` for a concrete finite
rank `r` sufficient for the odd-primary transfer.

Progress: 2026-05-16T16:45:47+02:00 - Proved the subgroup inclusion
`CPlus_le_normalizedCPlus` in `NormalizedSubgroup.lean`: the old
squared-family subgroup is contained in the normalized TeX subgroup because
each old generator is the square of the corresponding normalized generator,
and `-1` is already a normalized generator. Remaining work is the finite
2-primary relative-index bound for
`CPlus.relIndex (normalizedCPlus hp_odd hp_three)`.

TeX audit: This matches Lemma `C-quotient-killed-by-two` and Proposition
`C-vs-Csq-p-primary` in `cu06b_normalized_cyclotomic_units.tex`. The Lean proof
does not assume a quotient/index package: it proves
`normalizedCPlus_sq_mem_CPlus`, hence every element of
`normalizedCPlus / CPlus` has square `1`; Schreier's
`card_dvd_exponent_pow_rank'` then gives
`CPlus.relIndex normalizedCPlus ∣ 2 ^ rank(...)`. The odd-primary transfer is
`CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd`. Built with
`lake build BernoulliRegular.CyclotomicUnits.NormalizedSubgroup`.

##### CU-06b7 - Final normalized p-primary index theorem

Status: done
Claimer: Riccardo
Started: 2026-05-16T16:52:00+02:00
Completed: 2026-05-16T17:20:40+02:00

Goal: combine CU-06b2 through CU-06b6 with the squared-family p-primary theorem
to prove the exact TeX theorem

```text
p | [E^+ : C^+] <-> p | h^+(K)
```

for prime `p >= 5`, with normalized `C^+` on the left and no hidden,
conditional, bundled, or postponed source assumption.

TeX audit: The final theorem is
`BernoulliRegular.cyclotomicUnitIndex_primeConductor_pPrimary_of_five_le` in
`BernoulliRegular/CyclotomicUnits/NormalizedIndex.lean`. It states exactly the
odd-primary TeX conclusion for the normalized subgroup:

```text
p | (normalizedCPlus hp_odd hp_three).index <-> p | hPlus K
```

The theorem has no source hypothesis. Internally,
`kummerDirichletDeterminant_of_deletedFourier` proves the old
`KummerDirichletDeterminant` package from the concrete CU-08 determinant,
then `cyclotomicUnitIndexSubgroup_eq_CPlus` audits that the existing
Sinnott-family subgroup equals the squared-family `CPlus`, and
`CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd` transfers from
`CPlus` to the normalized TeX `C^+` because the relative index is a power of
`2`. Built with `lake build BernoulliRegular`.

#### CU-06c - The finite `p = 3` branch

Status: done
Claimer: Riccardo
Started: 2026-05-16T17:55:07+02:00
Completed: 2026-05-16T17:55:07+02:00

Goal: close the `p = 3` branch of CU-06 without invoking the analytic
determinant/regulator machinery.

TeX audit: For `p = 3`, the generator range is empty and the real unit rank is
zero. Lean proves this branch in
`BernoulliRegular/CyclotomicUnits/NormalizedIndex.lean`:

```text
theorem cyclotomicUnitIndex_primeConductor_pPrimary_of_eq_three
```

The proof uses the concrete mathlib theorem
`IsCyclotomicExtension.Rat.three_pid` to get `h K = 1`, then
`hPlus_dvd_h` to get `hPlus K = 1`. On the unit side,
`CPlus_eq_top_of_eq_three` uses
`NumberField.Units.closure_fundSystem_sup_torsion_eq_top`, the rank formula
`Units.rank KPlus = 0`, and `torsionKplus_le_CPlus`; then
`normalizedCPlus_eq_top_of_eq_three` follows from
`CPlus_le_normalizedCPlus`. Thus both sides of the CU-06 equivalence are
literally divisibility of `1`; no source proposition or postponed assumption is
used.

The public theorem
`cyclotomicUnitIndex_primeConductor_pPrimary` now dispatches between this
`p = 3` proof and the `p >= 5` proof. Built with
`lake build BernoulliRegular`.

### CU-07 - Regulator-index algebra

Status: done
Claimer: Riccardo
Started: 2026-05-16T13:32:02+02:00
Completed: 2026-05-16T13:34:15+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/RegulatorIndex.lean` with
`regulator_subgroup_eq_index_mul_regulator`, a route-level rearrangement of
mathlib's `NumberField.Units.regOfFamily_div_regulator` for the subgroup
generated by a full-rank unit family plus torsion.

This is a subproject for CU-06 and can be done without analytic number theory.

Deliverables:

```text
theorem regulator_subgroup_eq_index_mul_regulator
```

for a full-rank finite-index subgroup of a totally real unit group, after
quotienting by torsion.

Expected difficulty: medium/high, depending on existing regulator APIs.

### CU-08 - Even L-value logarithm formula and group determinant

Status: done
Claimer: Riccardo
Started: 2026-05-16T13:34:58+02:00
Reopened: 2026-05-16T18:09:00+02:00
Completed: 2026-05-16T18:13:40+02:00
Reason: The previous closure was too coarse. CU-08 must be stated as the
exact analytic/regulator theorem from `cyclotomic_units_weak_reflection.tex`,
not merely as isolated helper lemmas or wrappers around old Sinnott source
`Prop`s.

Scope correction: CU-08 is the analytic and deleted-Fourier determinant core
used by the cyclotomic-unit index formula. The final normalized TeX subgroup
statement

```text
p | [EPlus : CPlus] <-> p | hPlus K
```

belongs to CU-06, where CU-08 is consumed together with the regulator/index
lemma and the normalized-subgroup comparison. CU-08 itself closes the
following self-contained mathematical package.

Mathematical formulation:

Let `p` be an odd prime, and for the substantive analytic branch assume
`p >= 5` (the case `p = 3` is handled separately in CU-06c). Let

```text
K = Q(zeta_p),        KPlus = Q(zeta_p + zeta_p^{-1}),
g = (p - 1) / 2,      r = g - 1 = (p - 3) / 2,
EPlus = O_{KPlus}^*.
```

For `2 <= a <= g`, define the normalized real cyclotomic unit

```text
epsilon_a = zeta_p^((1 - a) / 2) * (1 - zeta_p^a) / (1 - zeta_p) ∈ EPlus,
```

where `(1 - a) / 2` is taken modulo `p`. Let `CPlus` be the subgroup of
`EPlus` generated by `-1` and the units `epsilon_2, ..., epsilon_g`.

The CU-08 endpoint is the analytic regulator identity behind the
cyclotomic-unit index formula:

```text
Reg(CPlus)^2 = ((hPlus K : R) * Reg(EPlus))^2.
```

Equivalently, after choosing the positive regulator convention,

```text
Reg(CPlus) = (hPlus K : R) * Reg(EPlus),
```

and after the regulator/index lemma this gives

```text
[EPlus : CPlus] = hPlus K
```

up to only the standard `2`-power/sign conventions. For the weak-reflection
route, the required p-primary corollary is

```text
p | [EPlus : CPlus] <-> p | hPlus K.
```

CU-08 is the proof of this regulator identity from the analytic class-number
formula and the deleted Fourier determinant, not the p-adic saturation part.

Analytic side:

For every nontrivial even Dirichlet character `chi` modulo `p`, define

```text
D(chi) = sum_{a in (Z/pZ)^*} chi(a) * log |1 - zeta_p^a|.
```

The exact convention in the current Lean files is

```text
DirichletCharacter.LFunction chi 1 =
  gaussSum(chi^{-1})^{-1} * DirichletLogSum p chi^{-1}.
```

Using the factorization

```text
zeta_{KPlus}(s) = product_{chi even mod p} L(s, chi)
```

and the analytic class-number formula for `KPlus`, one obtains the squared
class-number/regulator formula

```text
(((hPlus K : C) * (Reg(EPlus) : C))^2)
  =
((product_{chi even, chi != 1} DirichletLogSum p chi^{-1})^2)
  / 2^(p - 3).
```

This theorem must be produced from the concrete `L(1, chi)` formula and the
class-number formula route; it is not allowed to assume a bundled
`SinnottAnalyticIdentity`, `SinnottRegulatorIdentity`, or
`KummerDirichletDeterminant`.

Lean result: this is done in
`BernoulliRegular/CyclotomicUnits/AnalyticCore.lean`:

* `even_LFunction_one_eq_gaussSum_inv_mul_DirichletLogSum` gives the even
  `L(1, chi)` formula in the `DirichletLogSum` convention.
* `DirichletLogSum_inv_ne_zero_of_even_nontrivial` and
  `DirichletLogSum_ne_zero_of_even_nontrivial` give the nonvanishing factors.
* `quotientEigenvalue_ne_zero_of_ne_one` gives nonvanishing of the nontrivial
  quotient eigenvalues.
* `evenFrobeniusDet_sq_eq_log_p_sq_mul_nontrivial_DirichletLogSum_sq` records
  the even Frobenius determinant identity in `DirichletLogSum` normalization.
* `hPlus_mul_regulator_sq_eq_DirichletLogSum` records the analytic
  class-number/regulator side with the same right-hand side.

Producer-path audit: these declarations use concrete theorems from
`BernoulliRegular/LValueAtOne/Even.lean`,
`BernoulliRegular/HMinus/LValueReduction/LValues.lean`,
`BernoulliRegular/HMinus/ClassNumberFormula.lean`, and the proved
`FLT37.Sinnott` analytic reductions. They do not assume
`SinnottAnalyticIdentity`, `SinnottRegulatorIdentity`, or
`KummerDirichletDeterminant`.

Deleted-Fourier determinant side:

Let

```text
H = (Z/pZ)^* / {±1},        e = identity of H,        H* = H \ {e}.
```

For `h ∈ H`, put

```text
q(h) = log |1 - zeta_p^a|,
```

where `a` is any representative of the class `h`; this is well-defined because
`|1 - zeta_p^a| = |1 - zeta_p^{-a}|`.

For a character `xi : H -> C^*`, define the even Fourier coefficient

```text
q_e(xi) = sum_{h in H} q(h) * xi(h)^{-1}.
```

For an arbitrary omitted real embedding `h0 ∈ H`, define the deleted
cyclotomic-unit logarithm matrix

```text
L_{h,k} = q(h * k) - q(h),
  h ∈ H \ {h0},     k ∈ H*.
```

This is exactly the real logarithm matrix

```text
L_{h,k} = log |sigma_h(epsilon_k)|
```

after indexing embeddings by `H` and indexing the cyclotomic units by
nonidentity classes `k ∈ H*`. The determinant identity to prove is

```text
det(L)^2 = (product_{xi != 1} q_e(xi))^2.
```

Equivalently, in the full Dirichlet-character normalization, because
`DirichletLogSum` sums over `(Z/pZ)^*` while `q_e` sums over the quotient
by `±1`, the same formula is

```text
det(L)^2 =
((product_{chi even, chi != 1} DirichletLogSum p chi^{-1})^2)
  / 2^(p - 3).
```

The proof must allow arbitrary omitted row `h0`; the omitted embedding in the
Dirichlet regulator need not be the identity embedding. Unsquared formulas may
contain the harmless sign from row order, the column inversion convention, and
the factor `product_{xi != 1} xi(h0)`, but after squaring these disappear.

Lean result: this is done in
`BernoulliRegular/CyclotomicUnits/DeletedFourier.lean` and
`BernoulliRegular/CyclotomicUnits/DeletedFourierCyclotomic.lean`:

* `det_deletedConvolutionMatrixOnNonidentity_eq_prod_erase` proves the
  identity-deleted `hk^{-1}` determinant formula.
* `det_deletedConvolutionMatrixAtReindexed_eq_charFactor_mul_prod_erase`
  proves the arbitrary omitted-row version with the character factor.
* `det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq`
  proves the squared `hk`-convention formula where the row-order, inversion,
  and character-factor signs disappear.
* `det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq`
  specializes the result to `CyclotomicEvenDelta p`.

Downstream consumption audit: CU-08 is not isolated scaffolding. It is consumed
in `BernoulliRegular/CyclotomicUnits/IndexDeterminant.lean`, where
`detASubBSqEqProdNontrivialQeSq_of_deletedFourier` proves the old determinant
source package from the concrete deleted-Fourier theorem. CU-06 then uses this
producer path to build `KummerDirichletDeterminant` internally; the old package
name appears only as a target being proved, not as an assumption.

Build audit: The CU-08 modules were rebuilt directly:

```text
lake build BernoulliRegular.CyclotomicUnits.AnalyticCore
lake build BernoulliRegular.CyclotomicUnits.DeletedFourier
lake build BernoulliRegular.CyclotomicUnits.DeletedFourierCyclotomic
lake build BernoulliRegular.CyclotomicUnits.IndexDeterminant
```

Result: CU-08 is done. The only stale item was the `AnalyticCore.lean`
docstring saying a matrix-restriction bridge remained; that bridge is a
downstream CU-06 bridge and is now supplied by `IndexDeterminant.lean`.

Expected difficulty: very high.

## Kummer's p-adic Logarithmic Determinant

### CU-09 - Local Artin-Hasse/Dwork uniformizer setup

Status: done
Claimer: Riccardo
Started: 2026-05-16T15:10:10+02:00
Completed: 2026-05-19T08:28:02+02:00
Result: Completed the corrected local Artin-Hasse/Dwork parameter route.
The final assembly theorem is
`DworkParameter.finalAssembly` in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`, collecting the
inverse-series construction, Artin-Hasse evaluation, conjugation sign,
uniformizer and ramification data, `Z_p[varpi]`, the fixed real even-power
basis, the corrected Eisenstein equation, and the Teichmuller-scaled
Artin-Hasse rewrite.
Progress: Added `BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`, exposing
the proved completed-local `lambda = zeta_p - 1` model, principal-unit
filtration, valuation-completion logarithm API, and global lambda-unit
valuation under cyclotomic-unit route names.
Progress: 2026-05-16T18:17:44+02:00 - Rewrote the mathematical target below
as a self-contained question, suitable for a strategy from someone who does
not have access to this repo.
Progress: 2026-05-16T21:53:52+02:00 - Added the corrected strategy from
`local_artin_hasse_uniformizer.tex`: the standard Artin-Hasse normalization
does not admit the originally requested triple identity package, so CU-09
should formalize the inverse Artin-Hasse/Dwork parameter package below.
Progress: 2026-05-16T22:08:50+02:00 - Formalized the route-level
Artin-Hasse inverse package in
`BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean` under
`PadicLogSetup.FormalDwork`: route aliases for `L_p`, `E_p`, `E_p - 1`, and
the inverse series `G_p`; integrality of `E_p - 1` and `G_p`; formal inverse
identities `(E_p - 1)(G_p(T)) = T` and `E_p(G_p(T)) = 1 + T`; the transported
integral-coefficient inverse identity; first-order truncations proving the
formal source of `G_p(T) == T mod T^2`; and the odd/sign identity
`E_p(-T) * E_p(T) = 1`, plus its `H_p = E_p - 1` form.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`.
Progress: 2026-05-16T22:10:49+02:00 - Added the algebraic corrected
Eisenstein helper
`FormalDwork.correctedPowEquation_of_logTail_eq_zero`, deriving
`varpi^(p - 1) = -p * (1 + tail)` from the linearized Artin-Hasse logarithm
equation, and the guard lemma
`FormalDwork.tail_eq_zero_of_logTail_eq_zero_of_pow_eq_neg`, showing that the
false exact equation `varpi^(p - 1) = -p` forces the higher tail to vanish.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`.
Blocker: The TeX strategy shows that the original simultaneous target
`E_p(varpi) = zeta_p`, `varpi^(p - 1) = -p`, and
`complexConjugation varpi = -varpi` is false for the standard Artin-Hasse
normalization. The formal inverse/sign part of the corrected package is now
proved. CU-09 remains blocked on the analytic/completion layer: constructing
the actual completed local element
`varpi = G_p(zeta_p - 1)`, proving `E_p(varpi) = zeta_p`,
`varpi == zeta_p - 1 mod (zeta_p - 1)^2`, the corrected Eisenstein equation
for that element, the induced conjugation sign, and the fixed-real-basis
theorem `Z_p[zeta_p]^+ = Z_p[varpi^2]`.

Split strategy from `local_artin_hasse_uniformizer.tex`:

Corrected target package:

```text
H(T) = E_p(T) - 1
G(T) = H(T)^(-1) for composition
lambda = zeta_p - 1
varpi = G(lambda)
```

The theorem to formalize is not the false package
`E_p(varpi) = zeta_p`, `varpi^(p - 1) = -p`, `c(varpi) = -varpi`.
For the standard Artin-Hasse normalization, the corrected theorem is:

```text
E_p(varpi) = zeta_p,
varpi == lambda mod lambda^2,
c(varpi) = -varpi,
varpi is a uniformizer,
lambda == varpi mod varpi^2,
O = Z_p[varpi],
O^+ = {x in O : c(x) = x} = Z_p[varpi^2],
```

and

```text
varpi^(p - 1)
  = -p * (1 + sum_{n >= 2} varpi^(p^n - 1) / p^n).
```

The sum in parentheses is a unit, is fixed by `c`, and is congruent to `1`
modulo `varpi^((p - 1)^2)`.

Do not close CU-09 until the producer path starts from the canonical
cyclotomic input `zeta_p` and constructs `varpi` in the local/completed ring.
A wrapper theorem assuming `varpi` with these properties is only downstream
infrastructure, not a completion of CU-09.

Dependency order:

```text
CU-09a -> CU-09b -> CU-09c
       -> CU-09d -> CU-09e -> CU-09f
       -> CU-09g
```

`CU-09a` is complete. `CU-09b` is the next blocker: it supplies the analytic
evaluation API that the later subtickets consume.

#### CU-09a - Formal Artin-Hasse inverse and false-normalization guard

Status: done
Claimer: Riccardo
Completed: 2026-05-16T22:10:49+02:00

TeX source: Sections 2, 3, and formalization-roadmap parts A, B, C.

File:

```text
BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean
```

Lean namespace:

```text
BernoulliRegular.CyclotomicUnits.PadicLogSetup.FormalDwork
```

Delivered route-level names:

```text
logSeries
expSeries
expMinusOneSeries
inverseSeries
```

Delivered theorems:

```text
expMinusOneSeries_isPIntegral
inverseSeries_isPIntegral
expMinusOneSeries_subst_inverse
expSeries_subst_inverse
expSeries_mapTo_subst_inverse
inverseSeries_trunc_two
expMinusOneSeries_trunc_two
logSeries_rescale_neg
expSeries_rescale_neg_mul_self
one_add_rescale_neg_expMinusOneSeries_mul_self
correctedPowEquation_of_logTail_eq_zero
tail_eq_zero_of_logTail_eq_zero_of_pow_eq_neg
```

Audit: this subticket proves only formal power-series and algebraic guard
facts. It does not assume a local `varpi` and does not hide the analytic
construction behind a package hypothesis.

Build audit:

```text
lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup
```

Result: done.

#### CU-09b - Evaluate `G(lambda)` in the completed local ring

Status: done
Claimer: Riccardo
Started: 2026-05-16T23:11:20+02:00
Completed: 2026-05-17T05:39:20+02:00
Progress: 2026-05-16T23:14:25+02:00 - Added
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean` with the first CU-09b
coefficient-map layer: `rIntegralRatToValuedCompletion`,
`rIntegralRatToValuedInteger`, the denominator/valuation lemmas proving
`p`-integral rational coefficients land in the lambda valued integer ring,
and the routed integral Artin-Hasse series `integralExpSeries` and
`integralInverseSeries`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-16T23:23:43+02:00 - Extended the CU-09b
approximation layer.  The file now proves the integral-coefficient identity
`integralExpSeries_subst_integralInverseSeries`, the two degree truncation
facts `integralInverseSeries_trunc_two` and `integralExpSeries_trunc_two`,
defines the finite approximants `dworkParameterApprox`, proves
`dworkParameterApprox_two`, and exposes the raw field-valued candidate
`dworkParameterFieldCandidate`.  This is useful infrastructure, but CU-09b is
not done: the remaining work is still the adic/convergent evaluation API in
the integer ring, quotient compatibility modulo powers of the maximal ideal,
and the final identity `E_p(G(lambda)) = zeta_p`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T01:11:17+02:00 - Built the honest lambda-adic
completion layer in `DworkParameter.lean`, using
`DworkCompleteIntegerRing p K = AdicCompletion (lambdaIdeal p K)
(ValuedIntegerRing p K)` instead of assuming that `ValuedIntegerRing p K`
already has the needed completeness API.  The finite inverse-series
approximants are now proved compatible modulo powers of `lambdaIdeal`, giving
`dworkParameter : DworkCompleteIntegerRing p K` as the Cauchy limit of
`dworkParameterApprox`.  The file proves
`dworkParameter_evalₐ`, `dworkParameter_evalₐ_two`, the finite quotient
identity `dworkParameter_eval_exp_mod`, and the specialized completed
Artin-Hasse evaluation identity
`dworkParameterExp_eq_zeta`, where `dworkParameterExp` is the limit of the
finite truncation evaluations of `E_p` at the Dwork approximants.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Superseded audit: at this point CU-09b was still open because the generic
completed power-series evaluation API and the uniqueness theorem
`dworkParameter_unique` were not yet proved.  They were completed in the final
CU-09b result below without replacing them by a bundled hypothesis or opaque
package.
Result: 2026-05-17T05:39:20+02:00 - Finished CU-09b in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean` without adding source
assumptions.  The file now proves the generic finite quotient evaluator
`evalIntegralPowerSeriesMod`, its transition compatibility
`evalIntegralPowerSeriesMod_factor_eq`, the completed evaluator
`evalIntegralPowerSeries`, and the coordinate theorem
`evalIntegralPowerSeries_evalₐ`.  It specializes this API to the constructed
Dwork parameter via `dworkParameter_eval_exp`, proves the congruence
`dworkParameter_sub_lambda_mem_sq`, and records construction uniqueness as
`dworkParameter_unique`: any completed element with the prescribed finite
inverse-series coordinates is equal to `dworkParameter`.
Audit: the producer path starts from the canonical cyclotomic `lambda`, the
proved `p`-integral Artin-Hasse coefficient map, finite quotient
compatibility, and `AdicCompletion.ext_evalₐ`.  No bundled completeness,
opaque package, extra axiom, or theorem with the desired conclusion as a
hypothesis is introduced.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

TeX source: Section 3, "The corrected Dwork parameter".

Goal: construct the actual local element

```text
varpi = G(zeta_p - 1)
```

from the canonical cyclotomic input, not from an existential or bundled
hypothesis.

Recommended file:

```text
BernoulliRegular/CyclotomicUnits/DworkParameter.lean
```

Recommended model choice:

Use `PadicLogSetup.ValuedIntegerRing p K` and
`PadicLogSetup.ValuedCompletion p K` first, because this is the model with the
field/DVR and trace API already exposed. Add a bridge to
`PadicLogSetup.LocalIntegerRing p K` only if later tickets actually need the
adic-completion principal-unit API.

Required infrastructure:

1. Define a coefficient map from the `p`-integral rational coefficient ring to
   the valuation-completion integer ring:

   ```text
   rIntegralRatSubring p ->+* ValuedIntegerRing p K
   ```

   The intended route is through the rational `p`-adic completion map already
   exposed by the Kummer-Artin-Hasse valuation files. The proof obligation is
   that coefficients whose denominators are prime to `p` land in the integer
   ring.

2. Build a generic evaluation lemma for `p`-integral power series at an
   element of the maximal ideal:

   ```text
   evalIntegralPowerSeries
     (F : Z_p-integral power series)
     (x : completed element with eval mod lambda = 0) :
       DworkCompleteIntegerRing p K
   ```

   Strategy: define it as the adic limit of truncations. For compatibility
   modulo `m^N`, the tail after degree `N` lies in `m^N` because the
   coefficients are integral and `x^n in m^n`.

3. Prove quotient compatibility:

   ```text
   evalIntegralPowerSeries F x == trunc N F evaluated at x  mod m^N.
   ```

   This is the central API needed to transfer formal identities into the
   complete local ring.

Deliverables:

```text
def dworkParameter (p : Nat) (K : Type*) : DworkCompleteIntegerRing p K

theorem dworkParameter_eval_exp :
  evalIntegralPowerSeries (expSeries p) (dworkParameter p K)
    = AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K)

theorem dworkParameter_sub_lambda_mem_sq :
  eval mod lambda^2 of
    dworkParameter p K - AdicCompletion.of lambda = 0

theorem dworkParameter_unique :
  any completed x with the prescribed finite inverse-series coordinates equals
  dworkParameter
```

Proof strategy for `dworkParameter_eval_exp`:

Use `FormalDwork.expSeries_mapTo_subst_inverse` in every finite quotient. The
left side is the quotient-compatible truncation of `E_p(G(lambda))`; the right
side is `1 + lambda`, which is `zeta_p`. Then use Hausdorffness of the
completion to conclude equality.

Proof strategy for `dworkParameter_sub_lambda_mem_sq`:

Use `FormalDwork.inverseSeries_trunc_two`: modulo `m^2`, evaluating `G` at
`lambda` is the same as evaluating `T` at `lambda`.

Expected difficulty: very high. This is the first genuinely analytic
completion step.

##### CU-09b-followup - Generic completed evaluation and uniqueness API

Status: done
Claimer: Riccardo
Started: 2026-05-17T05:39:20+02:00
Completed: 2026-05-17T05:39:20+02:00

Dependencies: the completed approximation layer of CU-09b.

Goal: upgrade the specialized `dworkParameterExp` construction to a reusable
completed power-series evaluation API, and prove the construction uniqueness
statement for the Dwork parameter.

Required theorems:

```text
evalIntegralPowerSeries_evalₐ :
  every finite quotient of the completed evaluation is the corresponding
  truncated quotient evaluation

dworkParameter_eval_exp :
  evalIntegralPowerSeries (expSeries p) (dworkParameter p K)
    = AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
        (valuedCyclotomicZetaInteger p K)

dworkParameter_unique :
  any completed element x with the prescribed finite inverse-series
  coordinates equals dworkParameter
```

Result: done in `DworkParameter.lean`.  The completed evaluator is produced
from compatible finite quotient evaluations.  The uniqueness theorem is the
inverse-limit uniqueness statement actually needed by the construction, not a
wrapped hypothesis and not an unproved injectivity assertion for `E_p`.

#### CU-09c - Corrected Eisenstein equation and tail unit

Status: done
Claimer: Riccardo
Started: 2026-05-17T13:04:10+02:00
Completed: 2026-05-18T11:29:43+02:00
Result: CU-09c is closed by subtickets CU-09c1 through CU-09c5.  The final
endpoint is
`DworkParameter.dworkParameter_pow_pred_eq_neg_p_mul_tailUnit` in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`, proving the completed
corrected Eisenstein equation
`varpi^(p - 1) = -p * artinHasseTailUnit(varpi)`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

Progress: 2026-05-17T13:11:13+02:00 - Added the honest finite-tail
algebra layer in `BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`:
`FormalDwork.artinHasseTailFinite`,
`FormalDwork.artinHasseTailUnitFinite`,
`FormalDwork.correctedPowEquation_of_logTailFinite_eq_zero`,
`FormalDwork.artinHasseTailFinite_eq_zero_of_logTailFinite_eq_zero_of_pow_eq_neg`,
and the integer valuation-index lemmas
`FormalDwork.artinHasseTailValuationIndex_two`,
`FormalDwork.artinHasseTailValuationIndex_succ_sub`,
`FormalDwork.artinHasseTailValuationIndex_lt_succ`, and
`FormalDwork.artinHasseTailValuationIndex_ge_sq`.  These formalize the
finite algebraic equation and the monotonicity estimate needed for the later
integrality/high-power proof.
Audit: this does not close CU-09c.  The completed source theorem
`artinHasseLog_eval_dworkParameter_eq_zero` still needs a non-`p`-integral
completed evaluator for `L_p(T)=sum T^(p^n)/p^n`, or an equivalent
formal-log bridge.  The CU-09b evaluator only applies to `p`-integral
coefficient series, so using it for `L_p` would hide exactly the missing
analytic source behind an assumption.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T14:49:38+02:00 - Added the finite-precision
obstruction guard in `BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`:
`FormalDwork.artinHasseTailFinite_two`,
`FormalDwork.artinHasseTailFinite_two_ne_zero_of_pow_eq_neg`, and
`FormalDwork.not_logTailFinite_two_eq_zero_of_pow_eq_neg`.  At precision
`N = 2`, the false exact normalization forces the Artin-Hasse tail to vanish
from the logarithmic equation while its unique term is nonzero.  Also corrected
the stale local-basis and implementation-checklist claims in
`BernoulliRegular/CyclotomicUnits/cyclotomic_units_weak_reflection.tex`, which
had incorrectly asked for one parameter satisfying both
`varpi^(p-1) = -p` and `E_p(varpi) = zeta_p`.
Audit: the Furtwängler finite Artin-Hasse/log stack has the right kind of
quotient-level denominator evaluator, but its inverse-parameter theorem in the
existing reflection setup identifies the finite Artin-Hasse log with
`Log_N(1 + pi)` and proves only that it is killed by multiplication by `p`.
That is not yet an equality to zero in the completed cyclotomic-unit model, so
the missing source theorem `artinHasseLog_eval_dworkParameter_eq_zero` remains
open.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T16:46:44+02:00 - Added the formal logarithm theorem
`FormalDwork.logOf_expSeries_eq_logSeries` in
`BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`.  This proves
`PowerSeries.logOf (E_p) = L_p` as a formal power-series identity over `ℚ`,
using `PowerSeries.logOf`, the formal derivative of `log(1 + X)`, and the
definition `E_p = exp(L_p)`.  This matches the intended proof route: evaluate
the formal identity at `varpi` first, then use the ordinary `p`-adic logarithm
only on the convergent principal unit `E_p(varpi) = zeta_p`.
Audit: mathlib/project APIs in this checkout do not yet expose an ordinary
`p`-adic logarithm on `LambdaValuedCompletion p K` or a theorem identifying
the analytic evaluation of `PowerSeries.logOf` at `E_p(varpi)` with that
ordinary logarithm.  The remaining formal source is therefore the local
analytic bridge: convergence of both evaluated series, compatibility of formal
`logOf` evaluation with the ordinary log on `1 + m`, and
`log(zeta_p) = 0`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`.
Progress: 2026-05-17T17:01:21+02:00 - Added the post-inverse formal
logarithm theorem `FormalDwork.logSeries_subst_inverse_eq_log` in
`BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`, proving
`L_p(G_p(T)) = log(1 + T)` purely in `ℚ[[T]]`.  This closes the remaining
formal composition step in the intended proof and reduces the zero statement
to evaluating the ordinary formal logarithm at `T = zeta_p - 1`.
Audit: this still does not close CU-09c.  A direct attempt to use mathlib's
topological `PowerSeries.aeval` on `ValuedCompletion p K` exposes the actual
missing interface: Lean has `UniformSpace`, `CompleteSpace`,
`IsTopologicalRing`, `Algebra ℚ`, and `Valued` instances for
`ValuedCompletion p K`, but it does not synthesize
`IsLinearTopology (ValuedCompletion p K) (ValuedCompletion p K)` or
`ContinuousSMul ℚ (ValuedCompletion p K)`.  The constructed
`DworkCompleteIntegerRing p K` also has no topological-space/uniform-space
instance.  Therefore the ordinary-log evaluation bridge still has to be
formalized explicitly; it cannot be discharged by the current power-series
evaluation API without adding new analytic/topological infrastructure.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T17:05:56+02:00 - Added the valuation-completion
cyclotomic identities `valuedCyclotomicZeta_eq_one_add_lambda` and
`valuedCyclotomicZeta_pow_eq_one` in
`BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`.  These are the
field-side facts needed by the ordinary-log endpoint: the evaluated
Artin-Hasse exponential lands at a principal unit `1 + lambda`, and that unit
is `p`-torsion.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T17:08:25+02:00 - Added the valuation and convergence
facts `valuedCyclotomicLambda_valuation`,
`valuedCyclotomicLambda_isTopologicallyNilpotent`, and
`valuedCyclotomicLambda_hasEval` in
`BernoulliRegular/CyclotomicUnits/PadicLogSetup.lean`.  This proves that
`zeta_p - 1` has lambda valuation `exp(-1)` in the valuation completion and
is a legitimate topologically nilpotent input for any future power-series
evaluation API.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T17:34:31+02:00 - Added the principal-ideal and
completion instances `DworkParameter.lambdaIdeal_fg` and
`DworkParameter.instIsAdicCompleteDworkCompleteIntegerRing` in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.  Thus the constructed
Dwork integer ring is now registered as complete for the lambda-adic
filtration, using the finitely generated principal ideal `(lambda)`.
Audit: I did not add a global `ContinuousSMul ℚ (ValuedCompletion p K)`
instance.  With Lean's standard real topology on `ℚ`, the algebra map
`ℚ -> ℚ_p`/the lambda completion is not continuous, so that instance would be
mathematically false.  The topological `PowerSeries.aeval` bridge therefore
remains open; the completed Dwork ring is now covered on the algebraic
adic-completeness side.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T17:47:37+02:00 - Added the valid adic-topology
instances for `DworkCompleteIntegerRing p K`: the completed lambda ideal
`DworkParameter.dworkCompleteLambdaIdeal`, the preferred `WithIdeal`
structure, the completed-ideal adic-completeness theorem
`DworkParameter.dworkComplete_isAdicComplete`, and the derived `T2Space` and
`CompleteSpace` instances.  These are the missing instances on the completed
integer-ring side and make the lambda-adic topology available to typeclass
search.
Audit: this still deliberately avoids any `ContinuousSMul ℚ` instance for the
valued field.  The remaining mathematical choice is whether CU-09c should be
finished through finite quotient logarithms in the completed integer ring, or
through an ordinary `p`-adic logarithm after constructing/using a field-valued
parameter and a field-side log API.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T18:11:38+02:00 - Added the structural endpoint needed
for the finite-quotient route in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`: the flatness instance
`DworkParameter.instFlatDworkCompleteIntegerRing`, the torsion-free instance
`DworkParameter.instIsTorsionFreeDworkCompleteIntegerRing`, the scalar
injectivity lemma `DworkParameter.dworkComplete_smul_eq_zero_of_ne_zero`, the
`p`-torsion elimination lemma
`DworkParameter.dworkComplete_natCast_p_nsmul_eq_zero`, and the inverse-limit
coordinate endpoint
`DworkParameter.dworkComplete_eq_zero_of_evalₐ_natCast_p_nsmul_eq_zero`.
This proves the completion-side statement that a compatible system of finite
quotient logarithm values killed by `p` vanishes in the limit.
Audit: this is valid structural infrastructure, not a closure of CU-09c.  The
remaining source theorem is still the quotient-compatible evaluator for the
full Artin-Hasse logarithm `L_p` at `dworkParameter p K`, together with finite
coordinate identities showing those coordinates are killed by `p`.  The
existing Furtwängler inverse-parameter finite-log theorem has the needed
shape, but its setup carries the different-prime hypothesis `ℓ ≠ p`; it is
therefore not directly instantiable for CU-09c's same-prime cyclotomic
parameter without an additional bridge or a same-prime specialization proof.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T18:44:12+02:00 - Added the same-prime lambda-adic
denominator layer in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The new ramification theorem
`DworkParameter.span_natCast_prime_eq_lambdaIdeal_pow_pred` proves
`(p) = lambda^(p-1)` in the valuation integer ring, and
`DworkParameter.exists_natCast_prime_pow_mul_eq_of_mem_lambdaIdeal_pow_mul_pred_add`
uses it to divide by `p^m` without leaving the ring.  This supports the
quotient-compatible full Artin-Hasse log terms
`DworkParameter.samePrimeFiniteArtinHasseLogTerm` and their finite sum
`DworkParameter.samePrimeFiniteArtinHasseLog`, plus the Dwork-parameter
specialization `DworkParameter.dworkParameterFiniteArtinHasseLog`.
The same commit also added the properness/nonunit facts
`DworkParameter.valuedCyclotomicLambdaInteger_not_isUnit`,
`DworkParameter.lambdaIdeal_ne_top`,
`DworkParameter.natCast_prime_mem_lambdaIdeal`, and
`DworkParameter.natCast_not_mem_lambdaIdeal_of_coprime`, giving the
prime-to-`p` denominator input for the ordinary finite-log side.
The term specification
`DworkParameter.samePrimeFiniteArtinHasseLogTerm_natCast_prime_pow_mul_eq_mk`
is the same-prime analogue of the old denominator evaluator: multiplying the
chosen term by `p^r` recovers `x^(p^r)` modulo `lambda^(N+1)`.
Also added the integer-ring torsion identity
`DworkParameter.valuedCyclotomicZetaInteger_pow_eq_one` and the corresponding
principal-unit coordinate zero
`DworkParameter.samePrimeFiniteLogPowCoord_prime_lambda`.
Audit: this removes the denominator/ramification blocker for the finite
quotient route, but it still does not close CU-09c.  The remaining theorem is
the same-prime finite-log comparison
`samePrimeFiniteArtinHasseLog(dworkParameterApprox_N) = Log_N(lambda)` and
the resulting quotientwise `p`-torsion.  This must be proved locally from the
lambda-adic finite-log algebra, not imported from the old `ℓ ≠ p`
Stickelberger bundle.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T19:22:38+02:00 - Added the same-prime ordinary
finite-log denominator evaluator in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.  The new quotient
inverse theorem `DworkParameter.quotient_mk_natCast_isUnit_of_coprime`
inverts natural numbers prime to `p` modulo `lambda^(N+1)` using Bezout
against `p^(N+1)` and the ramification identity `(p)=lambda^(p-1)`.  On top
of that, `DworkParameter.samePrimeFiniteLogTermCore`,
`DworkParameter.samePrimeFiniteLogTerm`, and
`DworkParameter.samePrimeFiniteLog` define the ordinary finite logarithm
`Log_N(1+x)=sum (-1)^(n+1)x^n/n` in the same-prime lambda-adic quotients.
The bridge theorem
`DworkParameter.samePrimeFiniteLogTermCore_natCast_mul_eq_mk` proves that
multiplication by the natural denominator recovers `x^n` in the quotient, and
`DworkParameter.samePrimeFiniteLogTerm_eq_zero_of_cutoff_le` proves the
cutoff tail vanishes.
Audit: this is the missing same-prime denominator/evaluator layer for the
ordinary finite logarithm.  It still does not close CU-09c: the remaining
proof is the same-prime homogeneous/additivity theorem showing
`Log_N((1+x)^p-1)=p • Log_N(x)`, specialized to
`x=lambda` and `(1+lambda)^p=1`, and then the formal comparison
`L_p(G_p(lambda))=Log_N(lambda)`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T19:31:27+02:00 - Extended the same-prime finite-log
algebra in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.  The
new theorem `DworkParameter.natCast_prime_ne_zero_valuedInteger` factors out
the nonzero-`p` proof in the valuation integer ring and is now reused by the
completion torsion-free endpoint.  The finite-log evaluator now proves
`DworkParameter.samePrimeFiniteLogTermCore_arg_zero`,
`DworkParameter.samePrimeFiniteLogTerm_arg_zero`, and
`DworkParameter.samePrimeFiniteLog_arg_zero`, so the zero principal-unit
coordinate has zero finite logarithm despite the noncanonical numerator
choices.  Added the homogeneous product-coordinate infrastructure
`DworkParameter.samePrimeFiniteLogProductCoord`,
`DworkParameter.samePrimeFiniteLogProductArgPoly`, and the coefficient order
lemmas for powers of that polynomial, plus
`DworkParameter.samePrimeFiniteLogPowCoord_mem_lambdaIdeal`.  The root of
unity endpoint is now formalized as
`DworkParameter.samePrimeFiniteLog_powCoord_prime_lambda_eq_zero`.
Audit: this is still local finite-log infrastructure.  The next missing
theorem is the same-prime analogue of finite-log additivity/power:
`samePrimeFiniteLog ((1+x)^n-1) = n • samePrimeFiniteLog x`, at least for
`n=p` and `x=lambda`.  That theorem is the honest replacement for the old
`ℓ ≠ p` bundle result.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T19:41:55+02:00 - Added the generic same-prime natural
denominator evaluator in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`:
`DworkParameter.samePrimeNatDivNumerator` and
`DworkParameter.samePrimeNatDivEval`.  This evaluates `z/n` in
`R/lambda^(N+1)` whenever `z` has enough lambda-adic order to cancel the
`p`-part of `n`, and inverts only `ordCompl[p] n` in the quotient.  The
new lemmas include denominator recovery
`DworkParameter.samePrimeNatDivEval_natCast_mul_eq_mk`, vanishing at high
order, uniqueness from a division specification, proof-independence for the
order input, and add/neg/scalar compatibility.  The ordinary finite-log term
core is now linked to this generic evaluator by
`DworkParameter.samePrimeFiniteLogTermCore_eq_samePrimeNatDivEval`.
Audit: this is the local replacement for the old `finiteLogNatDivEval`
machinery without any `ConcreteStickelbergerSetup` assumptions.  It prepares
the homogeneous additivity proof but does not by itself prove finite-log
additivity.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T19:51:19+02:00 - Added the degree-indexed same-prime
localized evaluator
`DworkParameter.samePrimeNatDivEvalAtDegree` and the localized-polynomial
finite-log expression
`DworkParameter.samePrimeFiniteLogLocalizedPolynomial` in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.  The at-degree API
includes high-cutoff vanishing and add/neg/scalar compatibility, matching
the part of the old homogeneous proof that is purely local denominator
bookkeeping.
Audit: the equality between the original finite-log sum and the localized
polynomial form still needs an optimized proof; the direct dependent
sum-congruence proof hits kernel reduction timeouts.  This is a performance
issue in the proof term, not a new mathematical assumption.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T20:27:48+02:00 - Split the remaining finite-quotient
route into focused same-prime subtickets below.  The next implementation
target is the degree-indexed core comparison
`DworkParameter.samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree`,
which should make the localized polynomial equality a small termwise proof.

##### CU-09c1 - Same-prime localized finite-log form

Status: done
Claimer: Riccardo
Started: 2026-05-17T20:27:48+02:00
Completed: 2026-05-17T20:30:34+02:00

Goal: prove
`DworkParameter.samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree`,
then use it to prove
`DworkParameter.samePrimeFiniteLog_eq_samePrimeFiniteLogLocalizedPolynomial`
without the earlier dependent sum-congruence timeout.

Result: done in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The same-prime finite-log core now compares directly with the degree-indexed
denominator evaluator through
`DworkParameter.samePrimeFiniteLogTermCore_eq_samePrimeNatDivEvalAtDegree`;
the localized-term and localized-polynomial equalities are proved termwise by
`DworkParameter.samePrimeFiniteLogTerm_eq_localizedTerm` and
`DworkParameter.samePrimeFiniteLog_eq_samePrimeFiniteLogLocalizedPolynomial`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09c2 - Same-prime localized summation block

Status: done
Claimer: Riccardo
Started: 2026-05-17T20:30:59+02:00
Completed: 2026-05-17T20:45:39+02:00

Goal: port the local coefficient-clearing and localized quotient-sum
vanishing block from `FiniteLogLocalized.lean` to the lambda-adic same-prime
setting in `DworkParameter.lean`, avoiding the old
`ConcreteStickelbergerSetup` assumptions.

Result: done in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The same-prime local denominator layer now includes natural-cast order
bookkeeping, quotient inverse multiplication, finite-sum compatibility,
right-denominator transport, common-denominator addition, factorial-weighted
order transport, and the two factorial-cleared Icc vanishing theorems:
`DworkParameter.samePrimeNatDivEval_sum`,
`DworkParameter.samePrimeNatDivEval_mul_denominator_right`,
`DworkParameter.samePrimeNatDivEval_add_common_denominator`,
`DworkParameter.samePrimeNatDivEval_factorial_weighted_mem`,
`DworkParameter.samePrimeNatDivEval_eq_factorial_denominator`,
`DworkParameter.samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_eq_zero`,
and
`DworkParameter.samePrimeNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_lambdaIdeal_pow`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09c3 - Same-prime finite-log additivity and power torsion

Status: done
Claimer: Riccardo
Started: 2026-05-17T20:46:15+02:00
Completed: 2026-05-17T21:21:15+02:00

Goal: prove the same-prime finite-log additivity/power-law endpoint needed
for `Log_N((1 + lambda)^p - 1) = p * Log_N(lambda)`, then combine with
`(1 + lambda)^p = 1` to show the finite-log coordinate of `lambda` is killed
by `p`.
Progress: 2026-05-17T21:00:24+02:00 - Ported the formal coefficient and
factorial-clearing half of the same-prime additivity proof in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.  The new lemmas prove
the formal product-coordinate coefficient identity over `ValuedCompletion p K`,
transport it back to `ValuedIntegerRing p K`, and turn it into fixed-degree
localized quotient vanishing via
`DworkParameter.samePrimeFiniteLogAdditivity_degree_sum_eq_zero`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Progress: 2026-05-17T21:13:01+02:00 - Completed the same-prime finite-log
additivity grid in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The port now includes `DworkParameter.samePrimeFiniteLogProductHomogeneousGrid`,
the degree-sum/grid rearrangement lemmas, and the endpoint
`DworkParameter.samePrimeFiniteLog_add_add_mul`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.
Result: done in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The power-coordinate law `DworkParameter.samePrimeFiniteLog_powCoord` now
specializes to the cyclotomic lambda coordinate, using
`DworkParameter.valuedCyclotomicZetaInteger_pow_eq_one`, to prove
`DworkParameter.samePrimeFiniteLog_lambda_p_nsmul_eq_zero` and the quotient
scalar form
`DworkParameter.samePrimeFiniteLog_lambda_natCast_p_mul_eq_zero`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09c4 - Same-prime Artin-Hasse comparison and completed vanishing

Status: done
Claimer: Riccardo
Started: 2026-05-17T21:22:02+02:00
Completed: 2026-05-18T09:00:18+02:00

Goal: prove the specialized same-prime Artin-Hasse comparison
`dworkParameterFiniteArtinHasseLog N =
samePrimeFiniteLog N valuedCyclotomicLambdaInteger`, prove compatibility of
these quotient coordinates, package them as a completed element, and apply
the existing completion-side torsion-free endpoint to get
`artinHasseLog_eval_dworkParameter_eq_zero`.

Result: done in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The finite Artin-Hasse log coordinates are now factor-compatible through
`DworkParameter.dworkParameterFiniteArtinHasseLog_factorPow`, assembled as
the completed element
`DworkParameter.artinHasseLog_eval_dworkParameter`, and killed exactly by
`DworkParameter.artinHasseLog_eval_dworkParameter_eq_zero` using the existing
completion-side `p`-torsion-free endpoint.  The producer path is the
same-prime finite-quotient comparison and finite-log torsion theorem, not the
old `ell != p` Stickelberger bundle and not a field-side ordinary-log
assumption.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09c5 - Corrected Eisenstein tail and unit

Status: done
Claimer: Riccardo
Started: 2026-05-18T09:00:58+02:00
Completed: 2026-05-18T11:25:15+02:00

Goal: define the infinite Artin-Hasse tail and tail unit as limits of the
finite tails, prove the required high-power bound from the existing
valuation-index lemmas, and pass the finite corrected equation to the
completed corrected Eisenstein equation.

TeX source: Section 4, "The false identity `varpi^(p-1) = -p`".

Dependencies: CU-09b.

Goal: prove the corrected replacement for the false equality:

```text
varpi^(p - 1)
  = -p * (1 + sum_{n >= 2} varpi^(p^n - 1) / p^n).
```

Progress: 2026-05-18T09:28:03+02:00 - Added the finite quotient corrected
tail layer in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The new definitions
`DworkParameter.samePrimeFiniteArtinHasseTailTerm`,
`DworkParameter.samePrimeFiniteArtinHasseTail`, and
`DworkParameter.samePrimeFiniteArtinHasseTailUnit` evaluate
`varpi^(p^r - 1)/p^r` in the same-prime lambda-adic quotients.  The theorem
`DworkParameter.samePrimeFiniteArtinHasseTailTerm_mul_left_eq_logTerm`
identifies multiplication by the parameter with the corresponding full
Artin-Hasse log term, and
`DworkParameter.samePrimeFiniteArtinHasseLog_eq_first_two_add_tail` splits
the finite Artin-Hasse log into the linear term, the `r = 1` term, and
`varpi * tail_N`.  Also added
`DworkParameter.dworkParameterFiniteArtinHasseLog_eq_zero`, the exact finite
coordinate consequence of the completed log vanishing.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

Progress: 2026-05-18T10:44:28+02:00 - Finished the completed same-prime
tail packaging in `BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.
The finite tail coordinates are now compatible via
`DworkParameter.samePrimeFiniteArtinHasseTailTerm_factorPow`,
`DworkParameter.samePrimeFiniteArtinHasseTail_factorPow`,
`DworkParameter.samePrimeFiniteArtinHasseTailUnit_factorPow`,
and the Dwork-specialized coordinate lemmas
`DworkParameter.dworkParameterFiniteArtinHasseTail_factorPow` and
`DworkParameter.dworkParameterFiniteArtinHasseTailUnit_factorPow`.
The completed objects are
`DworkParameter.artinHasseTail` and
`DworkParameter.artinHasseTailUnit`.  The high-power bound is
`DworkParameter.artinHasseTail_mem_dworkCompleteLambdaIdeal_pow`, and the
unit statement is `DworkParameter.artinHasseTailUnit_isUnit`.  Also added
`DworkParameter.artinHasseTailUnit_eq_one_add_artinHasseTail` and the
finite specialized corrected-log equation
`DworkParameter.dworkParameterFiniteArtinHasse_first_two_add_tail_eq_zero`.
Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

Result: closed internally in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`, without adding a
field bridge.  Added the completed lambda generator
`DworkParameter.dworkCompleteLambda`, principal-ideal identification
`DworkParameter.dworkCompleteLambdaIdeal_eq_span`, the factorization
`DworkParameter.dworkParameter_eq_dworkCompleteLambda_mul_unit`, and
non-zero-divisor lemmas
`DworkParameter.dworkCompleteLambda_mul_eq_zero` and
`DworkParameter.dworkParameter_mul_eq_zero`.  The finite corrected quotient
factor is
`DworkParameter.dworkParameterFinite_corrected_factor_eq_zero`; its completed
packaging is
`DworkParameter.dworkParameter_mul_pow_pred_add_p_mul_tailUnit_eq_zero`.
The final corrected Eisenstein endpoint is
`DworkParameter.dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`:

```text
varpi^(p - 1) = -p * artinHasseTailUnit(varpi).
```

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

#### CU-09d - Conjugation acts by sign on `varpi`

Status: done
Claimer: Riccardo
Started: 2026-05-18T11:30:39+02:00
Completed: 2026-05-18T14:40:09+02:00

Result: `DworkParameter.Conjugation.dworkCompleteComplexConj` is the lifted
completion automorphism induced by cyclotomic complex conjugation, it sends
`dworkCompleteLambda` to `dworkCompleteConjugateLambda`, and
`DworkParameter.Conjugation.dworkCompleteComplexConj_dworkParameter_eq_neg`
proves the completed sign identity `c(varpi) = -varpi`.

TeX source: Section 5, "Complex conjugation and the corrected parameter".

Dependencies: CU-09b.

Goal:

```text
c(varpi) = -varpi
```

Required formal-series theorem:

```text
G(-S / (1 + S)) = -G(S)
```

Strategy for the formal theorem:

1. Let `H(T) = E_p(T) - 1`.
2. Use CU-09a's sign identity to prove

   ```text
   H(-T) = -H(T) / (1 + H(T)).
   ```

   In ring form, avoid division where possible:

   ```text
   (1 + H(-T)) * (1 + H(T)) = 1.
   ```

3. Substitute `T = G(S)` and use `H(G(S)) = S`.
4. Apply uniqueness of the compositional inverse to get

   ```text
   G(-S / (1 + S)) = -G(S).
   ```

Required local-conjugation infrastructure:

1. Extend `ringOfIntegersComplexConj` or the existing cyclotomic automorphism
   action to the chosen local/completed ring.
2. Prove the canonical formula

   ```text
   c(lambda) = zeta_p^(-1) - 1
             = -lambda / (1 + lambda).
   ```

3. Prove evaluation commutes with conjugation for integral power series with
   rational coefficients.

Then:

```text
c(varpi)
  = c(G(lambda))
  = G(c(lambda))
  = G(-lambda / (1 + lambda))
  = -G(lambda)
  = -varpi.
```

Expected difficulty: high after CU-09b; medium if the completion action from
`Reflection.Local.DeltaAction` can be reused directly for the automorphism
corresponding to `-1 : (ZMod p)^*`.

##### CU-09d1 - Formal inverse-series sign identities

Status: done
Claimer: Riccardo
Started: 2026-05-18T11:30:39+02:00
Completed: 2026-05-18T12:17:12+02:00

Result: `PadicLogSetup.FormalDwork.inverseSeries_hasSubst`,
`PadicLogSetup.FormalDwork.inverseSeries_subst_expMinusOneSeries`,
`PadicLogSetup.FormalDwork.expMinusOneSeries_subst_neg_inverse_mul_one_add_X_eq_neg_X`,
and
`PadicLogSetup.FormalDwork.inverseSeries_subst_expMinusOneSeries_subst_neg_inverse`
prove the formal source identities needed for the conjugation calculation.
`DworkParameter.integralInverseSeries_subst_integralExpMinusOneSeries_subst_neg_inverse`
ports the final identity to the integral coefficient ring used by the Dwork
completion.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09d2 - Same-prime conjugate lambda in the Dwork completion

Status: done
Claimer: Riccardo
Started: 2026-05-18T11:30:39+02:00
Completed: 2026-05-18T12:17:12+02:00

Result: `DworkParameter.valuedCyclotomicConjugateLambdaInteger` and
`DworkParameter.dworkCompleteConjugateLambda` define the same-prime local
candidate for `zeta_p⁻¹ - 1`; the denominator-cleared identities
`DworkParameter.valuedCyclotomicConjugateLambdaInteger_mul_one_add_lambda`
and `DworkParameter.dworkCompleteConjugateLambda_mul_one_add_lambda` prove
`(zeta_p⁻¹ - 1) * (1 + lambda) = -lambda` in the valuation integer ring and
in the Dwork completion.  `DworkParameter.dworkConjugateParameter` then
evaluates the inverse series at this completed conjugate-lambda coordinate,
with quotient-coordinate theorem
`DworkParameter.dworkConjugateParameter_evalₐ`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09d3 - Extend conjugation to the Dwork parameter

Status: done
Claimer: Riccardo
Started: 2026-05-18T12:53:14+02:00
Completed: 2026-05-18T14:40:09+02:00

Goal: construct or reuse an honest complex-conjugation automorphism on
`DworkCompleteIntegerRing p K`, prove it sends `dworkCompleteLambda` to
`dworkCompleteConjugateLambda`, prove integral inverse-series evaluation
commutes with that automorphism, and conclude
`c(dworkParameter) = -dworkParameter`.

Audit: CU-09d1 and CU-09d2 do not close the parent ticket.  They avoid a
bundled conjugation hypothesis and leave the remaining bridge explicit.

Result: `DworkParameter.Conjugation.valuedIntegerComplexConj` constructs the
same-prime valuation-integer conjugation automorphism and
`DworkParameter.Conjugation.lambdaIdeal_map_valuedIntegerComplexConj` proves
it preserves the lambda ideal.  The DeltaAction lift gives
`DworkParameter.Conjugation.dworkCompleteComplexConj`, with quotient formula
`DworkParameter.Conjugation.evalₐ_dworkCompleteComplexConj`.
`DworkParameter.Conjugation.dworkCompleteComplexConj_dworkCompleteLambda`
identifies the conjugate lambda coordinate, and
`DworkParameter.Conjugation.dworkCompleteComplexConj_dworkParameter` proves
that inverse-series evaluation commutes with the automorphism.  Combined with
the existing `DworkParameter.dworkConjugateParameter_eq_neg_dworkParameter`,
`DworkParameter.Conjugation.dworkCompleteComplexConj_dworkParameter_eq_neg`
closes the target sign identity without a quotient-by-quotient sign wrapper.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

#### CU-09e - Uniformizer and local ring generation

Status: done
Claimer: Riccardo
Started: 2026-05-18T15:11:30+02:00
Completed: 2026-05-18T18:37:08+02:00

TeX source: Sections 3 and 6, "Uniformizer and congruence" and
"The ring `O` as `Z_p[varpi]`".

Dependencies: CU-09b, CU-09c.

Goals:

```text
varpi is a uniformizer,
lambda == varpi mod varpi^2,
O = Z_p[varpi],
1, varpi, ..., varpi^(p - 2) is a Z_p-basis of O.
```

Strategy:

1. From `varpi == lambda mod lambda^2`, write

   ```text
   varpi = lambda * u
   ```

   with `u` a unit. Since `lambda` already generates the maximal ideal, this
   proves that `varpi` is a uniformizer and `(varpi) = (lambda)`.
2. Convert the congruence from `mod lambda^2` to `mod varpi^2` using equality
   of principal ideals.
3. Prove `O = Z_p[varpi]`. There are two possible routes:
   - Use `zeta_p = E_p(varpi)` and prove the infinite Artin-Hasse evaluation
     lies in the closed subalgebra generated by `varpi`.
   - Or prove directly that `lambda` is in the closed subalgebra generated by
     `varpi`, using `lambda = H(varpi)` and the evaluation API from CU-09b.
4. Once `O = Z_p[varpi]`, prove the powers

   ```text
   1, varpi, ..., varpi^(p - 2)
   ```

   span. Linear independence follows because the local field has degree
   `p - 1` over `Q_p`.

Lean model warning:

This subticket has to choose an exact meaning of `Z_p[varpi]`. In the
valuation-completion model, prefer a subalgebra over `ℤ_[p]` or over the
integer ring of the rational `p`-adic completion, rather than an informal
notation. Record the chosen API here before proving the basis theorem.

Expected difficulty: very high because of the closed-subalgebra and local
degree/basis API.

Result: CU-09e is closed in the completed Dwork integer ring.  CU-09e1 proves
`(varpi) = (lambda)`, `lambda = varpi mod varpi^2`, `(p) = (varpi)^(p - 1)`,
and parameter regularity.  CU-09e2 chooses the concrete coefficient ring
`DworkParameter.RationalPadicIntegerRing`, proves exact surjectivity and
injectivity of `DworkParameter.dworkParameterPowerLinearMap`, constructs the
basis `DworkParameter.dworkParameterPowerBasis`, and proves
`DworkParameter.dworkParameterAdjoin_eq_top`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09e1 - Completed uniformizer and congruence

Status: done
Claimer: Riccardo
Started: 2026-05-18T14:47:46+02:00
Completed: 2026-05-18T14:51:47+02:00

Result: `DworkParameter.dworkParameterIdeal` records the principal completed
ideal generated by `varpi`.  `DworkParameter.dworkParameterIdeal_eq_dworkCompleteLambdaIdeal`
proves `(varpi) = (lambda)`, and
`DworkParameter.dworkCompleteLambda_sub_dworkParameter_mem_parameterIdeal_sq`
proves `lambda = varpi mod varpi^2`.  The exact ramification endpoint
`DworkParameter.span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred`
proves `(p) = (varpi)^(p - 1)` in the Dwork completion, and
`DworkParameter.dworkParameter_regular` packages the existing cancellation
theorem as parameter regularity.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part11`.

##### CU-09e2 - Integral `Z_p[varpi]` model and basis

Status: done
Claimer: Riccardo
Started: 2026-05-18T15:36:52+02:00
Completed: 2026-05-18T18:37:08+02:00

Goal: choose and implement the exact integral `Z_p` base-ring API for the
valuation/Dwork integer ring, then prove `O = Z_p[varpi]` and the basis
`1, varpi, ..., varpi^(p - 2)`.

Blocker: the current files have the field-side `Q_p` map
`Furtwaengler.KummerArtinHasse.lambdaValuedCompletionAlgebraPadic`, but not an
integral map from `Z_p` into `ValuedIntegerRing p K` or
`DworkCompleteIntegerRing p K` with the necessary integer-valued image theorem.
CU-09e2 should first add that model, then state `Z_p[varpi]` as an actual
subalgebra over that base ring.  It should not be closed by using the trivial
`ValuedIntegerRing`-algebra structure on the Dwork completion.

Progress: `DworkParameter.Part12` defines the coefficient ring
`RationalPadicIntegerRing`, proves the rational-completion map preserves
integrality, and installs the resulting algebras on `ValuedIntegerRing p K`
and `DworkCompleteIntegerRing p K`.  It also defines the actual
`dworkParameterAdjoin` object, the finite power expansion map
`dworkParameterPowerLinearMap`, and the basis/adjoin endpoint lemmas reducing
the remaining work to surjectivity and injectivity of that map.  The same file
ports Dwork-side parameter-ideal p-divisibility and `lambda^n = varpi^n`
modulo `varpi^(n+1)` control.  Remaining gap: quotient-level spanning and the
valuation-descent linear-independence proof.

Update: `DworkParameter.Part12` now proves the parameter-adic approximation
induction
`DworkParameter.dworkParameterPowerLinearMap_approx_of_residue_lift` and its
valued-integer bridge
`DworkParameter.dworkParameterPowerLinearMap_approx_of_valuedInteger_residue_lift`.
The residue-side support lemmas
`DworkParameter.mem_lambdaIdeal_iff_valuation_le_exp_neg_one` and
`DworkParameter.globalCyclotomicResidue_natCast_fin_surjective` are now in
place: the first identifies `lambdaIdeal` by valuation in the valued integer
ring, and the second proves that the global cyclotomic residue field is
represented by rational classes `0, ..., p - 1`.
The field-level approximation theorem
`DworkParameter.exists_global_fin_valuation_sub_le_exp_neg_one_of_valuation_le_one`
is also proved: any lambda-integral element of `K` is congruent modulo lambda
to one of those rational classes.  The completion lift
`DworkParameter.valuedInteger_residue_lift_rationalPadicInteger` proves the
same residue statement for arbitrary `ValuedIntegerRing p K` elements, and
`DworkParameter.dworkParameterPowerLinearMap_approx` packages the resulting
quotient-level spanning statement modulo every power of
`dworkParameterIdeal p K`.  The finite quotient form is recorded as
`DworkParameter.dworkParameterPowerLinearMap_quotient_surjective`.

Update: `DworkParameter.Part13` extracts the coherent one-step correction
from the quotient-spanning induction.  It defines
`DworkParameter.dworkParameterPowerApproxSeq` and
`DworkParameter.dworkParameterPowerApproxBlockSeq`, proves the recursive
corrections are supported in one coordinate and divisible by the predicted
power of `p`, and records the algebraic Cauchy congruence
`DworkParameter.dworkParameterPowerApproxBlockSeq_sub_mem_primeIdeal_pow_smul_top`.
The same file proves the Dwork-continuity estimate
`DworkParameter.dworkParameterPowerLinearMap_mem_parameterIdeal_pow_mul_pred_of_mem_primeIdeal_pow_smul_top`
and isolates the exact limit step as
`DworkParameter.dworkParameterPowerLinearMap_surjective_of_precomplete`: exact
surjectivity now follows from the remaining source-side theorem that the
finite coefficient module is precomplete for
`DworkParameter.rationalPadicPrimeIdeal`.

Result: `DworkParameter.Part13` now proves coefficient-ring
`p`-adic precompleteness from the concrete rational completion topology and
upgrades coherent approximation to the unconditional theorem
`DworkParameter.dworkParameterPowerLinearMap_surjective`.  `DworkParameter.Part14`
proves the valuation-descent kernel theorem
`DworkParameter.dworkParameterPowerLinearMap_kernel_mem_primeIdeal_pow_smul_top`,
the injectivity theorem
`DworkParameter.dworkParameterPowerLinearMap_injective`, the bijectivity theorem
`DworkParameter.dworkParameterPowerLinearMap_bijective`, and the basis endpoint
`DworkParameter.dworkParameterPowerBasis`.  Together with the earlier
`DworkParameter.dworkParameterAdjoin_eq_top`, this proves
`O = Z_p[varpi]` and the `1, varpi, ..., varpi^(p - 2)` basis in the chosen
local coefficient model.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part13`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part14`.

#### CU-09f - Fixed real subring and even-power basis

Status: done
Claimer: Riccardo
Started: 2026-05-18T21:31:44+02:00
Completed: 2026-05-18T21:31:44+02:00

TeX source: Section 7, "The fixed subring `O^+`".

Dependencies: CU-09d, CU-09e.

Goals:

```text
O^+ = {x in O : c(x) = x} = Z_p[varpi^2]

1, varpi^2, varpi^4, ..., varpi^(p - 3)
```

is a `Z_p`-basis of `O^+`.

Strategy:

1. From CU-09d, `c(varpi) = -varpi`, so `varpi^2` is fixed. This gives

   ```text
   Z_p[varpi^2] <= O^+.
   ```

2. From CU-09e, every element of `O` has a unique expansion

   ```text
   x = sum_{i=0}^{p-2} a_i * varpi^i.
   ```

3. If `c(x) = x`, then

   ```text
   sum_i a_i * ((-1)^i - 1) * varpi^i = 0.
   ```

   By linear independence, every odd coefficient satisfies `-2 * a_i = 0`.
   Since `p` is odd, `2` is a unit in `Z_p`, so all odd coefficients vanish.
4. Therefore every fixed element is a polynomial in `varpi^2`, and the even
   powers

   ```text
   varpi^0, varpi^2, ..., varpi^(p - 3)
   ```

   form the required basis.

Expected difficulty: medium/high after CU-09d and CU-09e. The mathematics is
straightforward; the risk is the exact module-basis API for the selected
`Z_p` model.

Result: `DworkParameter.Part15` defines
`DworkParameter.dworkFixedSubalgebra` for the completed complex-conjugation
fixed subring and `DworkParameter.dworkEvenParameterAdjoin` for
`Z_p[varpi^2]`.  It proves
`DworkParameter.dworkEvenParameterAdjoin_eq_fixed`, using the CU-09d theorem
`Conjugation.dworkCompleteComplexConj_dworkParameter_eq_neg` and the CU-09e
power-map injectivity to kill odd coefficients.  The even-power basis is
packaged as `DworkParameter.dworkFixedEvenPowerBasis`, indexed by
`DworkParameter.dworkEvenPowerIndex`, with basis values recorded by
`DworkParameter.dworkFixedEvenPowerBasis_apply`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part15`.

#### CU-09g - Teichmuller Artin-Hasse rewrite for later logarithm tickets

Status: done
Claimer: Riccardo
Started: 2026-05-18T21:59:52+02:00
Completed: 2026-05-19T08:28:02+02:00

TeX source: formalization follow-up in CU-09 and the final theorem package.

Dependencies: CU-09b, CU-09c, CU-09e.

Goal for later CU-10/CU-11:

```text
zeta_p^a = E_p(omega(a) * varpi)
```

for Teichmuller lifts `omega(a)`.

Strategy:

1. Define or reuse the Teichmuller lift in the selected local integer ring:

   ```text
   omega(a)^p = omega(a),
   omega(a) mod maximalIdeal = a.
   ```

2. Show the Artin-Hasse logarithm of `omega(a) * varpi` vanishes:

   ```text
   L_p(omega(a) * varpi)
     = omega(a) * L_p(varpi)
     = 0,
   ```

   because `omega(a)^(p^n) = omega(a)`.
3. Conclude `E_p(omega(a) * varpi)` is a `p`th root of unity in `U_1`.
4. Identify which root by first-order congruence:

   ```text
   E_p(omega(a) * varpi) - 1 == omega(a) * varpi mod m^2
   zeta_p^a - 1 == a * lambda mod m^2
   omega(a) * varpi == a * lambda mod m^2.
   ```

5. Use injectivity of the first graded map on `mu_p` or the existing
   principal-unit cotangent API to conclude equality.

Expected difficulty: high. This is the bridge from CU-09 into the logarithmic
determinant tickets.

Result: Completed in `DworkParameter.Part16` and `DworkParameter.Part17`.
The downstream rewrite theorem is
`DworkParameter.artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow`.

##### CU-09g1 - Rational-completion Teichmuller coefficients and first-order scaled parameter congruence

Status: done
Claimer: Riccardo
Started: 2026-05-18T21:59:52+02:00
Completed: 2026-05-18T21:59:52+02:00

Result: Added `BernoulliRegular/CyclotomicUnits/DworkParameter/Part16.lean`.
It defines the bundled-prime `PadicInt` bridge
`DworkParameter.padicIntToRationalPadicIntegerRingEquiv`, the transported
coefficient lift `DworkParameter.rationalPadicTeichmuller`, its residue and
power laws, the scaled parameter `DworkParameter.scaledDworkParameter`, and the
first-order congruence
`DworkParameter.scaledDworkParameter_sub_natCast_mul_lambda_mem_sq`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part16`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`.

##### CU-09g2 - Scaled Artin-Hasse log/exponential comparison

Status: done
Claimer: Riccardo
Started: 2026-05-18T22:02:24+02:00
Completed: 2026-05-18T22:09:55+02:00

Goal: prove the finite-coordinate and completed comparison needed for
`L_p(omega(a) * varpi) = omega(a) * L_p(varpi) = 0`, then build the completed
Artin-Hasse exponential at `omega(a) * varpi`.

Resolved note: this was not an instance issue.  The completed proof adds the
scaled finite-coordinate comparison directly by termwise homogeneity.

Result: Extended `DworkParameter.Part16` with valued Teichmuller coefficients,
scaled finite Dwork approximants, the termwise and finite-sum homogeneity
theorems
`DworkParameter.samePrimeFiniteArtinHasseLogTerm_teichmuller_mul` and
`DworkParameter.samePrimeFiniteArtinHasseLog_teichmuller_mul`, and the scaled
finite comparison
`DworkParameter.scaledDworkParameterFiniteArtinHasseLog_eq_teichmuller_mul`.
It packages the completed scaled log as
`DworkParameter.artinHasseLog_eval_scaledDworkParameter`, proves its quotient
coordinates and vanishing via
`DworkParameter.artinHasseLog_eval_scaledDworkParameter_eq_zero`, and defines
the completed scaled exponential
`DworkParameter.artinHasseExp_eval_scaledDworkParameter`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part16`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`;
`lake build BernoulliRegular`.

##### CU-09g3 - Identify the scaled Artin-Hasse value with `zeta_p^a`

Status: done
Claimer: Riccardo
Started: 2026-05-18T22:11:52+02:00
Completed: 2026-05-18T23:22:15+02:00

Goal: after CU-09g2, use the first-order congruence from CU-09g1 and the
principal-unit/root-of-unity uniqueness step to prove the final rewrite
`zeta_p^a = E_p(omega(a) * varpi)`.

Result: `DworkParameter.Part16` proves the precision-two comparison
`DworkParameter.artinHasseExp_eval_scaledDworkParameter_sub_zeta_pow_mem_sq`,
and `DworkParameter.Part17` upgrades it to the exact completed equality
`DworkParameter.artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part17`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`;
`lake build BernoulliRegular`.

###### CU-09g3a - First graded identification of the scaled Artin-Hasse value

Status: done
Claimer: Riccardo
Started: 2026-05-18T22:11:52+02:00
Completed: 2026-05-18T22:35:58+02:00

Result: Added the binomial first-order lemma, the congruence
`DworkParameter.valuedCyclotomicZetaInteger_pow_sub_one_sub_natCast_mul_lambda_mem_sq`,
the coefficient bridge
`DworkParameter.algebraMap_rationalPadicInteger_natCast_dworkComplete`, the
precision-two expansion of the scaled Artin-Hasse exponential, and the final
first-graded comparison
`DworkParameter.artinHasseExp_eval_scaledDworkParameter_sub_zeta_pow_mem_sq`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part16`.

###### CU-09g3b - Dwork principal-unit logarithm kernel uniqueness

Status: done
Claimer: Riccardo
Started: 2026-05-18T22:36:21+02:00
Completed: 2026-05-18T23:22:15+02:00

Goal: prove the Dwork-completion uniqueness step needed to upgrade
`DworkParameter.artinHasseExp_eval_scaledDworkParameter_sub_zeta_pow_mem_sq`
to the exact equality
`DworkParameter.artinHasseExp_eval_scaledDworkParameter p K a =
AdicCompletion.of (lambdaIdeal p K) (ValuedIntegerRing p K)
  (valuedCyclotomicZetaInteger p K ^ a.val)`.

Result: Added `DworkParameter.Part17`, with finite scaled exponential
representatives, quotient compatibility, finite logarithm vanishing for
`zeta_p^a - 1`, the lambda-adic induction
`DworkParameter.scaledDworkParameterExpApprox_sub_zetaPow_mem_pow_succ`, and
the exact equality
`DworkParameter.artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow`.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.DworkParameter.Part17`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`;
`lake build BernoulliRegular`.

#### CU-09h - Final assembly and audit

Status: done
Claimer: Riccardo
Started: 2026-05-19T08:24:27+02:00
Completed: 2026-05-19T08:28:02+02:00

Dependencies: CU-09b through CU-09g.

Create a final route theorem, probably in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean` or a short
`DworkParameterFinal.lean`, collecting the corrected local package:

```text
exists/def varpi from zeta_p
E_p(varpi) = zeta_p
varpi == lambda mod lambda^2
c(varpi) = -varpi
varpi is a uniformizer
lambda == varpi mod varpi^2
O = Z_p[varpi]
O^+ = Z_p[varpi^2]
even-power basis of O^+
corrected varpi^(p - 1) equation
Teichmuller rewrite zeta_p^a = E_p(omega(a) * varpi)
```

Closure audit:

1. Confirm every theorem is produced from canonical inputs
   `p`, `K`, `zeta_p`, and the standard Artin-Hasse series.
2. Confirm no theorem assumes a bundled `varpi` package, a named
   `DworkParameterPackage`, or an opaque source theorem that is part of CU-09.
3. Confirm the false equality `varpi^(p - 1) = -p` is not used downstream.
4. Record the exact theorem names consumed by CU-10 and CU-11.
5. Run:

   ```text
   lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup
   lake build BernoulliRegular.CyclotomicUnits.DworkParameter
   lake build
   ```

Parent CU-09 is done only after this audit is recorded.

Result: Added the wrapper theorem `DworkParameter.finalAssembly` in
`BernoulliRegular/CyclotomicUnits/DworkParameter.lean`.

Closure audit:

1. The final theorem is assembled from canonical inputs `p`, `K`,
   `zeta_p`, the route Artin-Hasse series `integralExpSeries`, and the
   formal inverse series through the existing definitions
   `DworkParameter.dworkParameter`, `DworkParameter.dworkParameterApprox`,
   `DworkParameter.dworkParameterExp`, and
   `DworkParameter.artinHasseExp_eval_scaledDworkParameter`.
2. No CU-09 endpoint is proved from a bundled `varpi` package, named opaque
   source package, or constructor hypothesis. `DworkParameter.finalAssembly`
   is only a conjunction of already proved concrete endpoint theorems.
3. The false equality `varpi^(p - 1) = -p` is not used downstream in the
   Dwork route. The remaining occurrences are explanatory text and guard
   lemmas in `PadicLogSetup.lean`; the active endpoint is the corrected
   theorem `DworkParameter.dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`.
4. The exact theorem names expected by CU-10 are
   `DworkParameter.dworkParameterPowerBasis`,
   `DworkParameter.dworkParameterPowerBasis_apply`,
   `DworkParameter.dworkFixedEvenPowerBasis`,
   `DworkParameter.dworkFixedEvenPowerBasis_apply`,
   `DworkParameter.dworkParameterAdjoin_eq_top`, and
   `DworkParameter.dworkEvenParameterAdjoin_eq_fixed`.
5. The exact theorem names expected by CU-11 are
   `DworkParameter.dworkParameter_eval_exp`,
   `DworkParameter.artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow`,
   `DworkParameter.dworkParameter_sub_dworkCompleteLambda_mem_sq`,
   `DworkParameter.dworkCompleteLambda_sub_dworkParameter_mem_parameterIdeal_sq`,
   and `DworkParameter.dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`.
6. Line-count audit: every Lean file under
   `BernoulliRegular/CyclotomicUnits/DworkParameter/` is below 1000 lines.

Build audit: `lake build BernoulliRegular.CyclotomicUnits.PadicLogSetup`;
`lake build BernoulliRegular.CyclotomicUnits.DworkParameter`;
`lake build`.

Expected difficulty: high after the preceding subtickets.

## Kummer's Logarithmic Matrix

### CU-10 - Define the Kummer logarithm coefficient matrix

Status: done
Claimer: Riccardo
Started: 2026-05-19T08:44:16+02:00
Completed: 2026-05-19T08:51:17+02:00
Result: Added `BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean` and
imported it from `BernoulliRegular.lean`. The file defines the fixed Dwork
logarithm-vector input `KummerLogVector`, the positive even row index
`kummerLogEvenPowerIndex`, coefficient extraction
`kummerLogCoeffLift`, mod-`p` reduction `kummerLogCoeff`, and the matrix
`kummerLogMatrix`. Theorems `kummerLogCoeffLift_eq_basis_repr`,
`kummerLogCoeff_eq_reduction`,
`dworkFixedEvenPowerBasis_kummerLogEvenPowerIndex`, and
`kummerLogColumn_evenPowerExpansion` record that the entries are exactly the
coordinates of the supplied fixed logarithm columns in the even-power Dwork
basis. The analytic construction of the actual cyclotomic-unit logarithm
columns is not hidden here; it remains the source calculation for CU-11.

Create `BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`.

For `2 <= a <= g`, define coefficients `c j a` by

```text
log(eps_a^(p-1)) = sum_{j=1}^r c_{j,a} * varpi^(2*j).
```

Deliverables:

```text
def kummerLogCoeff (p : Nat) (j a : Nat) : ZMod p
def kummerLogMatrix (p : Nat) : Matrix (Fin r) (Fin r) (ZMod p)
```

with a theorem linking the matrix entries to the p-adic logarithm expansion.

Proof notes:

1. `eps_a^(p-1)` is a principal p-adic unit because
   `eps_a == a mod varpi`.
2. The p-adic logarithm lies in the real part.
3. The trace-zero argument removes the constant term.

Expected difficulty: high.

### CU-11 - Coefficient congruence

Status: done
Claimer: Riccardo
Completed: 2026-05-20T23:00:22+01:00
Result: Closed by CU-11a through CU-11f.  The canonical final theorem is
`kummerLogCoeff_congr` in
`KummerLogFormalEvaluator/Coefficient.lean`, with concrete matrix endpoint
`concreteKummerLogMatrix ... j a =
  squaredKummerLogUnitFactor p (kummerLogRowIndex j) *
  bernoulliFactor p (kummerLogRowIndex j) *
  ((kummerLogColumnIndex a)^(2 * kummerLogRowIndex j) - 1)`.
The unit factor is nonzero by `squaredKummerLogUnitFactor_ne_zero`; the
normalized-family factor is exposed separately by `normalizedKummerLogCoeff_congr`.
Audit: The theorem is assembled from the concrete logarithm columns
`concreteKummerLogVector`, the normalization and Dwork Artin-Hasse bridges,
the explicit folded same-prime finite-log coefficient calculation, and the
formal Bernoulli coefficient theorem.  It does not assume a bundled Kummer
coefficient congruence or an opaque matrix-entry source theorem.
Cleanup: 2026-05-20T23:08:42+01:00 - Removed the obsolete raw low-degree
representative package from the failed finite-log quotient strategy, including
the old `kummerLogFormalLowDegreeRepresentative` and
`kummerLogFormalLinearCoeffModP` APIs and the consumer lemmas that depended on
the false quotient-equality target.  The live folded evaluator and final
`kummerLogCoeff_congr` endpoint are unchanged.

This is the central p-adic calculation.  The parent ticket is closed only
after CU-11a through CU-11f are done and the final congruence theorem is
assembled from their concrete outputs.

Target theorem:

```text
theorem kummerLogCoeff_congr
    (hj : 1 <= j) (hj' : 2 * j <= p - 3)
    (ha : 2 <= a) (ha' : a <= (p - 1) / 2) :
    kummerLogCoeff p j a =
      u p j *
      bernoulliFactor p j *
      ((teichmuller a)^(2*j) - 1)
```

where `u p j : ZMod p` is nonzero and
`bernoulliFactor p j` is the reduction of `B_(2j)/(2j)`.

Expected difficulty: very high. This is the other main hard input after the
index theorem.

#### CU-11a - Construct the logarithm columns

Status: done
Claimer: Riccardo
Started: 2026-05-19T10:21:04+02:00
Completed: 2026-05-19T20:12:18+01:00
Result: Constructed the concrete Kummer logarithm vector from the real
cyclotomic-unit columns. The endpoint is
`concreteKummerLogVector` in
`BernoulliRegular/CyclotomicUnits/KummerLogTrace.lean`, with coefficient
bridges `concreteKummerLogCoeffLift_eq` and
`concreteKummerLogCoeff_eq`, the concrete matrix wrapper
`concreteKummerLogMatrix`, and exact constant-row vanishing
`concreteKummerLogVector_constantCoeff_eq_zero`.
Audit: The producer path is concrete. CU-11a1 selects the real cyclotomic
unit column, CU-11a2 embeds it into the Dwork local integer ring, CU-11a3
proves the powered column is in the principal-unit log domain, CU-11a4 builds
the compatible finite same-prime logarithm coordinates and their completed
Dwork element, and CU-11a5 proves fixedness plus exact constant-coordinate
vanishing from the norm-one finite quotient trace theorem. No bundled
logarithm-vector source hypothesis is used.

Parent ticket for building the actual `KummerLogVector` consumed by CU-10
from the cyclotomic units:

```text
a |-> log(eps_a^(p - 1))
```

in the completed Dwork integer ring, and prove the columns lie in
`dworkFixedSubalgebra`.  Close this parent only after CU-11a1 through
CU-11a6 are done and the assembly audit records the concrete producer path.

Deliverables:

1. A concrete logarithm-column definition with column index
   `a : Fin (kummerLogRank p)`, matching the range
   `2 <= a <= (p - 1) / 2`.
2. A theorem identifying its even-power Dwork coordinates with the
   `kummerLogCoeffLift` API from `KummerLogMatrix.lean`.
3. A fixedness theorem using conjugation, so no odd Dwork powers occur.

Do not hide the p-adic logarithm construction behind a source hypothesis.

##### CU-11a1 - Index cyclotomic-unit columns

Status: done
Claimer: Riccardo
Started: 2026-05-19T10:21:04+02:00
Completed: 2026-05-19T10:23:07+02:00
Result: Added the column-indexed real cyclotomic-unit wrapper in
`BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`. The new API records
`kummerLogColumnIndex_eq_CPlusGeneratorIndex`,
`kummerLogColumnIndex_range`, `kummerLogRealCyclotomicUnit`,
`kummerLogRealCyclotomicUnit_eq_CPlusGenerator`,
`kummerLogRealCyclotomicUnit_val`, and
`algebraMap_kummerLogRealCyclotomicUnit`. This closes the indexing/range
bridge without adding any local logarithm or Dwork embedding.

Connect the Kummer matrix column index `a : Fin (kummerLogRank p)` with the
existing real cyclotomic unit range.

Deliverables:

1. A definition or theorem identifying the column integer as
   `kummerLogColumnIndex p hp_three a`.
2. Range proofs
   `2 <= kummerLogColumnIndex ... a` and
   `kummerLogColumnIndex ... a <= (p - 1) / 2` in the exact form needed by
   `realCyclotomicUnit`.
3. A wrapper for the selected real cyclotomic unit column, with no local
   logarithm or Dwork embedding yet.

##### CU-11a2 - Embed columns at the Dwork prime

Status: done
Claimer: Riccardo
Started: 2026-05-19T10:24:11+02:00
Completed: 2026-05-19T10:28:08+02:00
Result: Added the Dwork-prime embedding API in
`BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`. The selected column
now has `kummerLogValuedCyclotomicUnit : (ValuedIntegerRing p K)^*` and
`kummerLogDworkCyclotomicUnit : (DworkCompleteIntegerRing p K)^*`, with
coercion/power compatibility lemmas
`kummerLogValuedCyclotomicUnit_coe`,
`kummerLogValuedCyclotomicUnit_pow_coe`,
`kummerLogDworkCyclotomicUnit_coe`,
`kummerLogDworkCyclotomicUnit_coe_eq_global`, and
`kummerLogDworkCyclotomicUnit_pow_coe`. This embeds the selected real
cyclotomic-unit column into the same local completion as the Dwork parameter.

Map the selected real cyclotomic unit columns into the same completed local
integer ring used by the Dwork parameter.

Deliverables:

1. A concrete map from the cyclotomic-unit value to
   `DworkCompleteIntegerRing p K` or to the intermediate local integer ring
   already used by the Dwork completion.
2. Compatibility with multiplication and powers for the column units.
3. A theorem identifying the image of the selected column with the local
   expression later normalized in CU-11b.

##### CU-11a3 - Prove the principal-unit log-domain statement

Status: done
Claimer: Riccardo
Started: 2026-05-19T10:29:46+02:00
Completed: 2026-05-19T11:31:56+02:00
Result: Proved the local log-domain statements in
`BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`. The key congruence is
`kummerLogValuedCyclotomicUnit_sub_natCast_sq_mem_lambdaIdeal`, using the
existing FLT37 congruence
`realCyclotomicUnit k == k^2 mod (zeta_p - 1)`. The powered column is shown to
lie in `1 + lambdaIdeal` by
`kummerLogValuedCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal` and
`kummerLogValuedCyclotomicUnit_pow_pred_mem_lambdaPrincipalUnits`; the completed
Dwork versions are
`kummerLogDworkCyclotomicUnit_pow_pred_sub_one_mem_lambdaIdeal` and
`kummerLogDworkCyclotomicUnit_pow_pred_mem_lambdaPrincipalUnits`. The residue is
`a^2`, not `a`, matching the even Kummer matrix columns.

Prove that the local image of each column satisfies the principal-unit
condition needed to define the p-adic logarithm after raising to `p - 1`:

```text
eps_a^(p - 1) ∈ 1 + maximalIdeal
```

Deliverables:

1. The congruence `eps_a == a mod varpi` or an equivalent local statement.
2. The principal-unit theorem for `eps_a^(p - 1)`.
3. A reusable lemma stating that the chosen local logarithm construction is
   defined on these powers.

##### CU-11a4 - Define the completed logarithm column

Status: done
Claimer: Riccardo
Started: 2026-05-19T11:41:06+02:00
Completed: 2026-05-19T11:45:57+02:00
Result: Defined the completed local logarithm column in
`BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`. The finite log
argument is `kummerLogColumnFiniteLogArg`, with log-domain proof
`kummerLogColumnFiniteLogArg_mem_lambdaIdeal`. The quotient values are
`kummerLogColumnFiniteLog` and `kummerLogColumnCoord`, with compatibility
`kummerLogColumnFiniteLog_factorPow` and `kummerLogColumnCoord_factorPow`.
The completed Dwork element is `kummerLogCompletedColumn`, with quotient
evaluation lemmas `kummerLogCompletedColumn_evalₐ`,
`kummerLogCompletedColumn_evalₐ_succ`, and
`kummerLogCompletedColumn_evalₐ_succ_eq_samePrimeFiniteLog`.

Use CU-11a3 to define the completed local logarithm of each powered column.

Deliverables:

1. A definition of the Dwork-side logarithm column for
   `a : Fin (kummerLogRank p)`.
2. Proof that the value lies in `DworkCompleteIntegerRing p K`, not only in a
   surrounding field, or a precise bridge back into the integer ring if the log
   is first field-valued.
3. Compatibility lemmas for quotient-level coefficient extraction.

##### CU-11a5 - Prove conjugation fixedness and constant-term vanishing

Status: done
Claimer: Riccardo
Started: 2026-05-19T11:52:13+02:00
Progress: 2026-05-19T12:16:12+02:00 - Fixedness and the mod-`p` constant
row vanishing needed by the matrix reduction are proved in
`BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`. The exact
trace/augmentation constant-term theorem is split below as CU-11a5b because no
source theorem for that trace-zero step is currently present.
Completed: 2026-05-19T18:49:46+01:00
Result: Closed by CU-11a5a and CU-11a5b. The columns are conjugation-fixed,
belong to `dworkFixedSubalgebra`, have mod-`p` constant row vanishing in
`KummerLogMatrix.lean`, and now have exact constant coefficient zero via
`KummerLogTrace.kummerLogFixedColumn_constantCoeff_eq_zero`.

Show that the logarithm columns lie in the real/fixed part and have no
constant term in the even-power Dwork basis.

Deliverables:

1. Conjugation fixedness of each completed log column.
2. Membership in `dworkFixedSubalgebra p K`.
3. Vanishing of the constant even-power coordinate, using the trace-zero or
   augmentation argument needed for the positive-row expansion.

###### CU-11a5a - Fixed columns and mod-p constant row

Status: done
Claimer: Riccardo
Started: 2026-05-19T11:52:13+02:00
Completed: 2026-05-19T12:16:12+02:00
Result: Proved conjugation fixedness and fixed-subalgebra membership for the
completed Kummer log columns in
`BernoulliRegular/CyclotomicUnits/KummerLogMatrix.lean`. The main endpoint
names are `kummerLogCompletedColumn_complexConj`,
`kummerLogCompletedColumn_mem_fixedSubalgebra`, and `kummerLogFixedColumn`.
The finite-log naturality lemmas under local complex conjugation are packaged
as `Conjugation.samePrimeFiniteLog_quotientMap_complexConj` and its termwise
helpers. Also proved that the completed column lies in `dworkParameterIdeal`
and that the constant even-power coefficient is zero after reduction modulo
`p`, via `kummerLogFixedColumn_constantCoeff_mod_p_eq_zero`.

###### CU-11a5b - Exact trace/augmentation constant term

Status: done
Claimer: Riccardo
Started: 2026-05-19T17:24:43+01:00
Progress: 2026-05-19T18:08:54+01:00 - Added the full cyclotomic
lambda-adic Dwork action infrastructure in
`BernoulliRegular/CyclotomicUnits/DworkParameter/Part18.lean`, including
`Conjugation.dworkCompleteCyclotomicEquiv`,
`Conjugation.samePrimeFiniteLog_quotientMap_cyclotomic`, and the finite
product additivity theorem
`Conjugation.samePrimeFiniteLog_finsetProductCoord`. Added
`BernoulliRegular/CyclotomicUnits/KummerLogTrace.lean`, proving the honest
norm-one finite quotient trace source
`KummerLogTrace.sum_samePrimeFiniteLog_cyclotomic_kummerLogColumn_univ_eq_zero`
and its completed form
`KummerLogTrace.sum_dworkCompleteCyclotomicEquiv_kummerLogCompletedColumn_eq_zero`.
Completed: 2026-05-19T18:49:46+01:00
Result: Proved the cyclotomic action-on-parameter bridge
`Conjugation.dworkCompleteCyclotomicEquiv_dworkParameter` and its
power-expansion consequence
`Conjugation.dworkCompleteCyclotomicEquiv_powerLinearMap` in
`BernoulliRegular/CyclotomicUnits/DworkParameter/Part18.lean`. Extracted the
constant coefficient from the completed trace sum in
`BernoulliRegular/CyclotomicUnits/KummerLogTrace.lean`, with endpoint theorem
`KummerLogTrace.kummerLogFixedColumn_constantCoeff_eq_zero`.

Prove the exact constant coefficient vanishing in the fixed even-power basis,
not only its reduction modulo `p`.

Missing source step: an honest trace-zero or augmentation theorem for the
completed Kummer logarithm column, strong enough to rule out the possible
`p`-divisible constant coefficient left by membership in the Dwork parameter
ideal.

##### CU-11a6 - Assemble the `KummerLogVector`

Status: done
Claimer: Riccardo
Started: 2026-05-19T20:12:18+01:00
Completed: 2026-05-19T20:12:18+01:00
Result: Added `concreteKummerLogVector` as the actual
`KummerLogVector p K` consumed by the CU-10 matrix API, plus
`concreteKummerLogVector_apply`, `concreteKummerLogCoeffLift_eq`,
`concreteKummerLogCoeff_eq`, `concreteKummerLogMatrix`,
`concreteKummerLogMatrix_apply`, and
`concreteKummerLogVector_constantCoeff_eq_zero` in
`BernoulliRegular/CyclotomicUnits/KummerLogTrace.lean`.
Audit: The vector is assembled by applying `kummerLogFixedColumn` to each
column index. That fixed column is the completed same-prime finite logarithm
of `kummerLogValuedCyclotomicUnit^(p - 1)`, with fixedness and constant-term
vanishing already proved from the cyclotomic action and norm-one trace
calculation, not from an assumed source vector.

Package CU-11a1 through CU-11a5 as the actual logarithm-vector input for the
matrix API from CU-10.

Deliverables:

1. A definition of the concrete `KummerLogVector p K`.
2. Theorems identifying its coefficients with
   `kummerLogCoeffLift` and `kummerLogCoeff`.
3. A short audit recording that the vector is produced from the concrete local
   logarithm construction, not from a bundled source hypothesis.

#### CU-11b - Normalize the cyclotomic-unit logarithm

Status: done
Claimer: Riccardo
Started: 2026-05-19T22:16:23+01:00
Completed: 2026-05-19T22:16:23+01:00

Replace the logarithm of the unit power by the normalized quotient expression:

```text
log(eps_a^(p - 1))
  == log(a * (1 - zeta_p) / (1 - zeta_p^a))
```

in the quotient needed for mod-`p` coefficient extraction.

Deliverables:

1. Consume the principal-unit/log-domain theorem from CU-11a3.
2. A quotient-level logarithm equality with the normalized expression.
3. Compatibility with the concrete `KummerLogVector` column from CU-11a6.

Result: Added `KummerLogNormalization.lean`, with the normalized quotient
argument `kummerLogNormalizedQuotientFiniteLogArg`, the finite-log
normalization theorem
`kummerLogNormalizedUnitFiniteLog_eq_normalizedQuotientFiniteLog_modP`, the
column theorem
`kummerLogColumnFiniteLog_eq_two_nsmul_normalizedQuotientFiniteLog_modP`, and
the concrete-vector compatibility
`concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_normalizedQuotientFiniteLog`.
Audit: The proof uses the CU-11a principal-unit log-domain construction,
same-prime finite-log additivity, the proved zero logarithm of zeta powers,
and a local Frobenius congruence derived from
`span_natCast_prime_eq_lambdaIdeal_pow_pred`; no bundled source vector or
unproved normalization hypothesis is introduced.

#### CU-11c - Rewrite through the Dwork Artin-Hasse parameter

Status: done
Claimer: Riccardo
Started: 2026-05-19T22:38:56+01:00
Completed: 2026-05-19T22:38:56+01:00

Express the normalized quotient from CU-11b using the Dwork parameter:

```text
zeta_p = E_p(varpi)
zeta_p^a = E_p(omega(a) * varpi)
```

and rewrite the logarithm as the specialization of a formal Artin-Hasse
series in `T` and `X`.

Deliverables:

1. Use the CU-09 endpoint
   `artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow`.
2. Produce the formal/specialized expression

   ```text
   log(X * (E_p(T)-1)/(E_p(X*T)-1))
   ```

   at `T = varpi`, `X = omega(a)`.
3. Prove the coefficient comparison is compatible with the Dwork even-power
   basis used by CU-10.

Result: Added the Dwork Artin-Hasse normalization layer in
`KummerLogNormalization.lean`: the completed quotient denominator
`kummerLogDworkArtinHasseQuotientDenUnit`, the specialized denominator
identity
`kummerLogDworkArtinHasseQuotientDenUnit_mul_exp_sub_one`, the Dwork
specialized quotient argument
`kummerLogDworkArtinHasseNormalizedQuotientArg`, its mod-`p` representative
comparison
`kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_pow_pred`, and the
concrete-vector compatibility theorem
`concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_dworkArtinHasseSpecializedFiniteLog`.
Audit: The rewrite uses the CU-09 theorem
`artinHasseExp_eval_scaledDworkParameter_eq_zeta_pow`, the proved FLT37
cyclotomic-unit quotient identity, and the completed ramification bridge from
the Teichmuller scalar to the integral scalar; it does not assume a formal
coefficient source or bundle the Artin-Hasse specialization behind an opaque
hypothesis.

#### CU-11d - Prove the formal Bernoulli coefficient identity

Status: done
Claimer: Riccardo
Started: 2026-05-19T22:47:26+01:00
Completed: 2026-05-20T08:03:37+01:00
Result: Closed by CU-11d1 through CU-11d6 in
`KummerLogFormal.lean`. The final exported targets are
`formalKummerLogCoeffModP_eq_unit_mul_bernoulliFactor`,
`formalKummerLogCoeffModP_eval`, and
`formalKummerLogCoeffModP_unit_ne_zero`, with coefficient factors
`kummerLogUnitFactor` and `bernoulliFactor`.
Audit: The producer path is explicit: formal power-series normalization,
formal `PowerSeries.logOf`, coefficient extraction, formal rescaling by `X`,
and explicit numerator/denominator reduction modulo `p`. No bundled
coefficient congruence, analytic p-adic logarithm, or Teichmuller
specialization is used.

Parent ticket for the purely formal power-series calculation.  Close it only
after CU-11d1 through CU-11d6 are complete and the final coefficient theorem
has been assembled from their concrete outputs.

Target identity:

```text
coeff T^(2j) log(X * (E_p(T)-1)/(E_p(X*T)-1))
  = u_j * B_(2j)/(2j) * (X^(2j)-1) mod p.
```

Deliverables:

1. A formal coefficient theorem before specializing `X`.
2. An explicit unit factor `u p j : ZMod p` with proof `u p j != 0`.
3. A precise `bernoulliFactor p j` definition for the reduction of
   `B_(2j)/(2j)`.
4. No analytic p-adic-log assumptions; this ticket is purely formal
   power-series algebra plus Bernoulli-number reduction.

##### CU-11d1 - Define the formal Kummer logarithm series

Status: done
Claimer: Riccardo
Started: 2026-05-19T22:47:26+01:00
Completed: 2026-05-19T22:49:42+01:00
Result: Added `KummerLogFormal.lean` with
`formalArtinHasseNormalizedExpMinusOne`,
`formalArtinHasseScaledNormalizedExpMinusOne`, `formalKummerLogSeries`, and
the formal quotient theorem
`formalKummerQuotientUnit_mul_scaled_eq_normalized`.
Audit: The construction is internal to `PowerSeries (Polynomial ℚ)`, uses
`PowerSeries.rescale`, `PowerSeries.logOf`, and `PowerSeries.invOfUnit`, and
does not invoke any analytic `p`-adic logarithm or convergence result.

Create the formal two-variable expression whose coefficients are computed in
CU-11d:

```text
log(X * (E_p(T)-1)/(E_p(X*T)-1))
```

Deliverables:

1. A formal definition over a coefficient ring appropriate for reduction
   modulo `p`.
2. A theorem rewriting it into a difference of one-variable Artin-Hasse
   logarithm expressions after normalizing by `T`.
3. Proof that all manipulations in this ticket are formal power-series
   identities, not analytic p-adic-log statements.

##### CU-11d2 - Define Bernoulli and unit factors

Status: done
Claimer: Riccardo
Started: 2026-05-19T22:47:26+01:00
Completed: 2026-05-19T22:49:42+01:00
Result: Added `ratReductionZMod`, `bernoulliFactor`,
`kummerLogUnitFactor`, `kummerLogUnitFactor_ne_zero`,
`kummerLogUnitFactor_isUnit`, corrected the unit factor to
`-((2*j)!)^-1`, and added the denominator-unit lemmas
`two_mul_index_zmod_isUnit`, `factorial_two_mul_index_zmod_isUnit`,
`bernoulli_den_zmod_isUnit`, and `bernoulliFactor_denominators_isUnit`.
Audit: The Bernoulli denominator input is the existing proved theorem
`prime_not_dvd_bernoulli_den_of_lt_sub_one`, specialized under
`1 <= j` and `2 * j <= p - 3`. The factorial denominator is a unit because
`2*j < p`, proved via `Nat.Prime.dvd_factorial`; no denominator invertibility
is assumed as a new hypothesis.

Define the coefficient-side constants appearing in the final congruence.

Deliverables:

1. `bernoulliFactor p j : ZMod p`, representing the reduction of
   `B_(2*j)/(2*j)`.
2. `kummerLogUnitFactor p j : ZMod p`, or the final chosen name for
   `u p j`.
3. Theorems recording the denominator-invertibility hypotheses needed when
   `1 <= j` and `2 * j <= p - 3`.

##### CU-11d3 - Prove the basic Artin-Hasse coefficient formula

Status: done
Claimer: Riccardo
Started: 2026-05-19T23:03:28+01:00
Completed: 2026-05-19T23:03:28+01:00
Result: Proved the ordinary normalized exponential coefficient theorem
`coeff_logOf_formalExpNormalizedMinusOne_eq_bernoulli` and the same-prime
Artin-Hasse low-degree specialization
`coeff_logOf_formalArtinHasseNormalizedExpMinusOne_eq_bernoulli` in
`KummerLogFormal.lean`.
Audit: The proof is formal. It derives the coefficient of
`log((exp T - 1)/T)` from the Bernoulli power-series identity
`bernoulliPowerSeries_mul_exp_sub_one`, then transfers to Artin-Hasse below
degree `p` using the proved theorem
`artinHasseExpSeries_coeff_eq_inv_factorial_of_lt`. There is no
Teichmuller specialization and no analytic logarithm.

Compute the relevant coefficient of the normalized one-variable
Artin-Hasse logarithm series before inserting the factor `X`.

Deliverables:

1. A theorem for the coefficient of `T^(2*j)` in the normalized
   Artin-Hasse logarithm side.
2. A statement expressed in terms of Bernoulli numbers and the unit factor
   from CU-11d2.
3. No specialization to Teichmuller values.

##### CU-11d4 - Insert the formal scalar `X`

Status: done
Claimer: Riccardo
Started: 2026-05-20T07:58:07+01:00
Completed: 2026-05-20T08:00:46+01:00
Result: Added the formal rescaling coefficient lemma
`coeff_logOf_rescale_eq_pow_mul_coeff_logOf`, the scaled Artin-Hasse
specializations
`coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_pow_mul` and
`coeff_logOf_formalArtinHasseScaledNormalizedExpMinusOne_eq_bernoulli`, and
the difference formula
`coeff_formalKummerLogSeries_eq_neg_bernoulli_mul_X_pow_sub_one`.
Audit: The proof expands `PowerSeries.logOf` through the formal logarithm
sum and uses `PowerSeries.coeff_rescale`; no analytic logarithm,
Teichmuller specialization, or p-adic convergence input is used.

Transport the coefficient formula through the substitution `T |-> X*T`.

Deliverables:

1. Coefficient extraction lemmas for substituting `X*T`.
2. A theorem producing the factor `X^(2*j)` on the substituted side.
3. A difference formula giving the factor `X^(2*j) - 1`.

##### CU-11d5 - Reduce the coefficient identity modulo `p`

Status: done
Claimer: Riccardo
Started: 2026-05-20T07:58:07+01:00
Completed: 2026-05-20T08:00:46+01:00
Result: Added the chosen mod-`p` target
`formalKummerLogCoeffModP : Polynomial (ZMod p)`, the reduced coefficient
factor `reducedKummerLogCoeffFactor`, the denominator-unit package
`reducedKummerLogCoeffFactor_denominators_isUnit`, the nonzero unit theorem
`reducedKummerLogCoeffFactor_unit_ne_zero`, and the final target rewrite
`formalKummerLogCoeffModP_eq`.
Audit: The mod-`p` coefficient is defined by explicit numerator/denominator
reduction through `ratReductionZMod`, with denominator invertibility supplied
by the proved Bernoulli and factorial unit lemmas. No ring homomorphism
`ℚ -> ZMod p` is assumed.

Convert the rational/integral formal coefficient identity into the final
`ZMod p` identity.

Deliverables:

1. Reduction lemmas for Bernoulli factors and denominator inverses.
2. A mod-`p` coefficient theorem over `ZMod p[X]` or the chosen formal target.
3. A proof that the unit factor from CU-11d2 remains nonzero after reduction.

##### CU-11d6 - Assemble the unspecialized formal theorem

Status: done
Claimer: Riccardo
Started: 2026-05-20T08:02:49+01:00
Completed: 2026-05-20T08:03:37+01:00
Result: Added the final unspecialized mod-`p` theorem
`formalKummerLogCoeffModP_eq_unit_mul_bernoulliFactor`, the evaluation form
`formalKummerLogCoeffModP_eval` for later specialization of `X`, and the
exported nonzero unit theorem `formalKummerLogCoeffModP_unit_ne_zero`.
Audit: The theorem only packages the concrete outputs of CU-11d1 through
CU-11d5. The coefficient polynomial is the explicit reduced target built
from `kummerLogUnitFactor` and `bernoulliFactor`, whose denominator
invertibility is proved separately.

Combine CU-11d1 through CU-11d5 into the theorem consumed by CU-11e.

Deliverables:

1. The final unspecialized theorem:

   ```text
   coeff T^(2j) log(X * (E_p(T)-1)/(E_p(X*T)-1))
     = u p j * bernoulliFactor p j * (X^(2*j)-1)
   ```

2. The exported nonzero theorem for `u p j`.
3. A short audit confirming this theorem is derived from formal series
   algebra and Bernoulli reduction, not from a bundled congruence assumption.

#### CU-11e - Specialize at the Teichmuller column

Status: done
Claimer: Riccardo
Started: 2026-05-20T08:04:55+01:00
Completed: 2026-05-20T08:11:17+01:00
Result: Added `KummerLogCoefficient.lean` with the row index
`kummerLogRowIndex`, row-bound lemmas
`kummerLogRowIndex_one_le` and
`two_mul_kummerLogRowIndex_le_sub_three`, Teichmuller reduction lemmas
`rationalPadicIntegerToZMod_teichmuller_pow_sub_one` and
`rationalPadicIntegerToZMod_teichmuller_kummerLogColumnIndex`, the row
denominator/unit packages
`formalKummerLogCoeffModP_column_denominators_isUnit` and
`formalKummerLogCoeffModP_column_unit_ne_zero`, and the column-specialized
formal theorem
`formalKummerLogCoeffModP_eval_kummerLogColumnIndex`.
Audit: This is a specialization of CU-11d's explicit `ZMod p[X]` polynomial
at the residue of the Kummer column. It uses the proved Teichmuller residue
map and denominator-unit lemmas; no concrete matrix-entry comparison is
assumed.

Specialize the formal identity of CU-11d at

```text
X = omega(a)
```

for `2 <= a <= (p - 1) / 2`.

Deliverables:

1. Teichmuller reduction lemmas needed to rewrite
   `omega(a)^(2*j) - 1` in `ZMod p`.
2. A columnwise coefficient theorem matching the indices used by
   `kummerLogMatrix`.
3. A proof that all denominator factors used in the coefficient are invertible
   modulo `p` under `1 <= j` and `2 * j <= p - 3`.

#### CU-11f - Assemble the coefficient congruence

Status: done
Claimer: Riccardo
Started: 2026-05-20T08:04:55+01:00
Progress: 2026-05-20T08:11:17+01:00 - Added the formal right-hand side
`kummerLogCoeffCongrRhs`, the formal assembled congruence
`formalKummerLogCoeff_congr`, and the exported unit nonzero theorem
`kummerLogCoeffCongrRhs_unit_ne_zero` in `KummerLogCoefficient.lean`.
Progress: 2026-05-20T08:30:29+01:00 - Resolved the normalization factor:
`kummerLogUnitFactor` is the normalized-unit factor, while the current
concrete logarithm columns are the squared-family columns. Added
`squaredKummerLogUnitFactor`, `squaredKummerLogUnitFactor_ne_zero`,
`squaredKummerLogCoeffCongrRhs`, and
`formalSquaredKummerLogCoeff_congr` to record the exact extra factor `2`.
Split: 2026-05-20T08:49:04+01:00 - Split remaining work into CU-11f1 through
CU-11f4.
Completed: 2026-05-20T22:53:41+01:00
Result: Closed by CU-11f1 through CU-11f4.  The final concrete APIs are
`concreteSquaredKummerLogMatrixEntry_congr`,
`concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs`,
`concreteKummerLogMatrix_eq_two_mul_kummerLogCoeffCongrRhs`, and the
matrix-level wrapper
`concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs_matrix`.  The
normalized-family API is `normalizedKummerLogCoeff_congr`, with nonzero/unit
row factors supplied by `kummerLogCoeffCongrRhs_unit_ne_zero`,
`squaredKummerLogUnitFactor_ne_zero`, and
`squaredKummerLogUnitFactor_isUnit`.
Audit: The concrete bridge consumes
`concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_dworkArtinHasseSpecializedFiniteLog`,
the quotient coordinate API from CU-11f1, and the folded finite-log
coefficient theorem from CU-11f2.  No opaque congruence package or bundled
matrix-entry source hypothesis is used.

Combine CU-11a through CU-11e into the final theorem:

```text
theorem kummerLogCoeff_congr
    (hj : 1 <= j) (hj' : 2 * j <= p - 3)
    (ha : 2 <= a) (ha' : a <= (p - 1) / 2) :
    kummerLogCoeff p j a =
      u p j *
      bernoulliFactor p j *
      ((teichmuller a)^(2*j) - 1)
```

Deliverables:

1. The final matrix-entry congruence in the exact API needed by CU-13.
2. A theorem exposing `u p j != 0`.
3. A short audit in this ticket recording that the proof consumes the concrete
   logarithm columns and formal coefficient theorem, not an opaque bundled
   congruence hypothesis.

##### CU-11f1 - Quotient-coordinate extraction

Status: done
Claimer: Riccardo
Started: 2026-05-20T08:51:02+01:00
Completed: 2026-05-20T09:07:23+01:00
Result: Added the Dwork quotient-coordinate bridge in
`KummerLogCoefficient.lean`: coefficient differences modulo
`(dworkParameterIdeal)^(p - 1)` land in `rationalPadicPrimeIdeal`, hence
their `ZMod p` reductions agree in the Dwork power basis. Added the
fixed-even-basis transfer theorem and the `kummerLogEvenPowerIndex`
specialization needed by Kummer matrix rows.
Audit: The proof rewrites the modulus using the proved ramification theorem
`span_natCast_prime_dworkComplete_eq_parameterIdeal_pow_pred`, divides the
difference by the scalar `p`, and uses the already proved
`dworkParameterPowerBasis`/`dworkParameterPowerLinearMap_injective` package.
It does not introduce a new DVR, residue-degree, or power-basis source
hypothesis.

Prove the Dwork power-basis coefficient extraction theorem needed to read
mod-`p` coefficients from the quotient modulo `(varpi)^(p - 1) = (p)`.

Target shape:

```text
if x - y in (dworkParameterIdeal p K)^(p - 1),
then for every i : Fin (p - 1),
  rationalPadicIntegerToZMod p
    ((dworkParameterPowerBasis p K).repr x i)
  =
  rationalPadicIntegerToZMod p
    ((dworkParameterPowerBasis p K).repr y i).
```

Deliverables:

1. A theorem showing congruence modulo `(dworkParameterIdeal)^(p - 1)` is
   coefficientwise congruence modulo `p` in the Dwork power basis.
2. The fixed-even-basis corollary for `dworkFixedEvenPowerBasis` and
   `kummerLogEvenPowerIndex`.
3. An audit that the theorem uses the proved ramification identity
   `(p) = (varpi)^(p - 1)` and `dworkParameterPowerBasis`, not a new DVR
   source hypothesis.

##### CU-11f2 - Formal specialization matches finite Artin-Hasse coefficient

Status: done
Claimer: Riccardo
Started: 2026-05-20T09:11:11+01:00
Progress: 2026-05-20T09:25:50+01:00 - Added the finite quotient
coefficient infrastructure in `KummerLogCoefficient.lean`:
`dworkParameterQuotientCoeffModP`,
`valuedLambdaQuotientDworkCoeffModP`,
`valuedLambdaQuotientDworkCoeffModP_evalₐ`, and
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP`.  Also added the
compatibility rewrites from the formal target to `kummerLogCoeffCongrRhs`.
Split: 2026-05-20T09:25:50+01:00 - Split the remaining proof into the
representative-independent quotient-coordinate layer and the still-missing
formal-to-finite-Artin-Hasse evaluator.
Completed: 2026-05-20T22:35:15+01:00
Result: Closed by CU-11f2a and CU-11f2b.  The exported endpoints are
`kummerLogFormalEvaluator_coeff_eq` for the formal specialized coefficient
and `kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs` for
the assembled congruence right-hand side.

Connect the formal polynomial coefficient from CU-11d/e with the finite
Artin-Hasse logarithm quotient used by the Dwork-normalization theorem.

Target shape:

```text
the coefficient of varpi^(2*j) in
  kummerLogDworkArtinHasseSpecializedFiniteLog p K hp_three a
equals
  Polynomial.eval (kummerLogColumnIndex ... : ZMod p)
    (formalKummerLogCoeffModP p (kummerLogRowIndex ...)).
```

Deliverables:

1. A finite quotient coefficient theorem for the Dwork Artin-Hasse
   specialization.
2. Compatibility with `formalKummerLogCoeff_congr`.
3. No Teichmuller or Artin-Hasse specialization is hidden behind an opaque
   source theorem.

###### CU-11f2a - Quotient coefficient API for finite Dwork specialization

Status: done
Claimer: Riccardo
Started: 2026-05-20T09:11:11+01:00
Completed: 2026-05-20T09:25:50+01:00
Result: Added the representative-independent quotient coefficient maps
`dworkParameterQuotientCoeffModP` and
`valuedLambdaQuotientDworkCoeffModP`, the evaluation theorem
`valuedLambdaQuotientDworkCoeffModP_evalₐ`, the specialized finite
Artin-Hasse coefficient
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP`, and the formal
compatibility theorems
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs_of_eq_formal`
and
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal_iff_eq_congrRhs`.
Audit: The quotient maps are well-defined using the proved CU-11f1
coefficient congruence and the proved ideal transport from
`lambdaIdeal^(p - 1)` to `(dworkParameterIdeal)^(p - 1)`.  They do not assume
the desired Artin-Hasse coefficient formula.

###### CU-11f2b - Prove the formal-to-finite Artin-Hasse evaluator

Status: done
Claimer: Riccardo
Started: 2026-05-20T09:57:56+01:00
Progress: 2026-05-20T09:57:56+01:00 - Added the Dwork power-coordinate
API needed to consume a formal polynomial representative:
`dworkParameterPowerBasis_repr_powerLinearMap`,
`dworkParameterQuotientCoeffModP_mk_powerLinearMap`,
`valuedLambdaQuotientDworkCoeffModP_evalₐ_powerLinearMap`, additive
quotient-coordinate lemmas, monomial high/low degree readers,
`dworkParameterPowerLinearMap_of_polynomial_eval₂`,
`dworkParameterQuotientCoeffModP_mk_polynomial_eval₂_of_natDegree_lt`,
`valuedLambdaQuotientDworkCoeffModP_evalₐ_polynomial_eval₂_of_natDegree_lt`,
and the specialized bridge
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_of_evalₐ_polynomial_eval₂`.
Remaining: prove the actual formal normalized Artin-Hasse quotient evaluator
produces such a degree `< p - 1` polynomial representative with the formal
`formalKummerLogCoeffModP` coefficient.
Split: 2026-05-20T10:02:33+01:00 - Split the remaining evaluator into
CU-11f2b1 through CU-11f2b3 and added
`KummerLogFormalEvaluator.lean` as the dedicated file for this layer. The
file currently exports the proved consumer bridge
`kummerLogFormalEvaluator_coeff_eq_of_polynomialRepresentative`; the source
theorems constructing the representative are still open below.
Completed: 2026-05-20T22:33:37+01:00
Result: Closed by CU-11f2b1 through CU-11f2b3.  The final evaluator theorem is
`kummerLogFormalEvaluator_coeff_eq`, and the assembled congruence-RHS form is
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs`.

Prove the actual remaining equality:

```text
kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP ... j a =
  Polynomial.eval (kummerLogColumnIndex ... : ZMod p)
    (formalKummerLogCoeffModP p (kummerLogRowIndex ... j)).
```

This should be proved by evaluating the formal normalized Artin-Hasse quotient
`(E_p(T)-1)/T / ((E_p(XT)-1)/(XT))` at the Dwork parameter modulo
`(varpi)^(p - 1)`, then comparing the finite same-prime logarithm coefficient
with `PowerSeries.logOf` coefficient.  Do not replace this with a bundled
coefficient hypothesis.

####### CU-11f2b1 - Low-degree formal polynomial representative

Status: done
Claimer: Riccardo
Started: 2026-05-20T10:05:30+01:00
Progress: 2026-05-20T10:05:30+01:00 - Added the first formal evaluator API
in `KummerLogFormalEvaluator.lean`:
`coeff_formalKummerLogSeries_eq_one_sub_pow_mul_coeff_normalized`, proving
formally over `Polynomial ℚ` that the `T^d` coefficient is the normalized
one-variable Artin-Hasse logarithm coefficient multiplied by `1 - X^d`.
Completed: 2026-05-20T10:14:32+01:00
Result: Added the concrete even-row representative API in
`KummerLogFormalEvaluator.lean`:
`kummerLogFormalEvenRowCoeffLift`,
`kummerLogFormalEvenRowRepresentative`,
`kummerLogFormalEvenRowRepresentative_natDegree_lt`,
`kummerLogFormalEvenRowRepresentative_coeff_even`, and
`kummerLogFormalEvenRowRepresentative_coeff_even_modP`.
Audit: The coefficient lift is the Teichmuller lift in
`RationalPadicIntegerRing p` of the already proved `ZMod p` formal coefficient.
No map `ℚ → ZMod p` is introduced; the mod-`p` reduction theorem uses
`rationalPadicIntegerToZMod_teichmuller`, while the denominator work remains
the explicit CU-11d/CU-11e Bernoulli and factorial unit API.

Construct the degree `< p - 1` rational-padic polynomial representative for
the normalized Artin-Hasse logarithm after specializing the formal scalar at
the Kummer column.

Deliverables:

1. A polynomial `P : Polynomial (RationalPadicIntegerRing p)` depending on the
   column `a`.
2. A theorem `P.natDegree < p - 1`.
3. A row-coefficient theorem showing the reduction of the coefficient of
   `T^(2*j)` is
   `Polynomial.eval (kummerLogColumnIndex ... : ZMod p)
     (formalKummerLogCoeffModP p (kummerLogRowIndex ... j))`.
4. No fake ring hom `ℚ → ZMod p`; denominators must be handled by the already
   proved unit lemmas or by an explicit integral/rational-padic lift.

####### CU-11f2b2 - Finite logarithm equals the folded evaluator

Status: done
Claimer: Riccardo
Started: 2026-05-20T10:28:12+01:00
Progress: 2026-05-20T10:28:12+01:00 - Split after finding that
CU-11f2b1's even-row representative is not enough for a quotient equality:
the finite logarithm modulo `varpi^(p - 1)` also sees the linear term of the
normalized formal logarithm.
Progress: 2026-05-20T15:42:42+01:00 - Strategy corrected after the linear
coordinate obstruction.  The raw low-degree formal representative is not the
finite same-prime logarithm representative.  The missing contribution is the
single folded same-prime term `(U - 1)^p / p`, where
`U = A_p(varpi) / A_p(c * varpi)` and `c = omega a`.  Equivalently, if
`Y = U - 1 = varpi * Z` and `epsilon_varpi` is the ramification unit satisfying
`p * epsilon_varpi = varpi^(p - 1)`, the integral correction is
`epsilon_varpi * varpi * Z^p`.  CU-11f2b2 should now prove the folded
representative or the needed folded even-coordinate theorem, not equality with
`kummerLogFormalLowDegreeRepresentative`.

Prove that the same-prime finite logarithm of the normalized Dwork quotient
agrees modulo `varpi^(p - 1)` with the **folded** finite-log representative.
For

```text
U = A_p(varpi) / A_p(c * varpi),
Y = U - 1,
Y = varpi * Z,
p * epsilon_varpi = varpi^(p - 1),
```

the representative is

```text
sum_{n = 1}^{p - 1} (-1)^(n + 1) * Y^n / n
  + Y^p / p
```

or, integrally,

```text
sum_{n = 1}^{p - 1} (-1)^(n + 1) * Y^n / n
  + epsilon_varpi * varpi * Z^p.
```

This is the quotient-level form of the same-prime finite logarithm.  The old
target

```text
factorPow (kummerLogDworkArtinHasseSpecializedFiniteLog ...)
  =
eval_a (Polynomial.eval₂ ... dworkParameter
  (kummerLogFormalLowDegreeRepresentative ...))
```

is false and must not be used as an intermediate theorem.

Corrected deliverables:

1. A general folded same-prime finite-log expansion modulo `varpi^(p - 1)`,
   proving that all terms `n > p` vanish and that the only non-unit
   denominator term surviving is `Y^p / p`.
2. An integral rewrite of the correction term using the ramification unit
   `epsilon_varpi`, where `p * epsilon_varpi = varpi^(p - 1)`, together with
   the residue fact
   `epsilon_varpi ≡ -1 mod varpi` needed for the linear-coordinate
   cancellation.
3. A specialized folded representative for
   `kummerLogDworkArtinHasseNormalizedQuotientArg`, sourced from the normalized
   complete-ring identity
   `1 + Q_a(varpi) = A_p(varpi) / A_p(c * varpi)`.
4. A coordinate theorem for the even Kummer rows that includes the folded
   `Y^p / p` contribution.  Do not assume this correction vanishes in even
   rows; compute or prove the required cancellation explicitly.
5. The old raw representative may remain as a formal low-degree helper and as
   a guardrail, but it is not the finite-log representative.
Completed: 2026-05-20T22:30:05+01:00
Result: Closed by CU-11f2b2a, CU-11f2b2b, and CU-11f2b2c.  The final target
uses the folded same-prime finite-log representative, not the false raw
low-degree quotient equality, and exposes the unconditional even-row endpoint
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal`.

######## CU-11f2b2a - Add the raw low-degree formal representative

Status: done
Claimer: Riccardo
Started: 2026-05-20T10:28:12+01:00
Completed: 2026-05-20T10:30:48+01:00
Result: Extended `KummerLogFormalEvaluator.lean` with
`coeff_formalKummerLogSeries_one`,
`kummerLogFormalLinearCoeffModP`,
`kummerLogFormalLinearCoeffLift`,
`kummerLogFormalLowDegreeRepresentative`,
`kummerLogFormalLowDegreeRepresentative_natDegree_lt`,
`kummerLogFormalLowDegreeRepresentative_coeff_even`, and
`kummerLogFormalLowDegreeRepresentative_coeff_even_modP`. Added the consumer
theorem `kummerLogFormalEvaluator_coeff_eq_of_lowDegreeRepresentative`, which
would consume a quotient equality with this raw representative.  The later
guardrail theorem shows that such a quotient equality is false for the finite
same-prime logarithm, so this consumer is now diagnostic/formal
infrastructure rather than the live CU-11f2b2 endpoint.
Audit: The degree-one term is sourced from the formal theorem
`coeff_logOf_formalArtinHasseNormalizedExpMinusOne_one`, proved in
`KummerLogFormal.lean` by comparing the Artin-Hasse normalized series with the
ordinary normalized exponential below degree `p`. This only adds the missing
linear representative term and preserves the already proved even-row reduction
theorem. It does not assert the finite-log equality; that remains
CU-11f2b2b/CU-11f2b2c.

Extend the CU-11f2b1 representative by adding the degree-one coefficient of
the normalized Kummer logarithm, while preserving the even-row coefficient API.
This is now a raw formal low-degree helper, not the full finite-log quotient
representative.  It records the formal degree `< p - 1` coefficients and is
useful for row comparisons and for the guardrail theorem showing why the
finite representative must be folded.  The full CU-11f2b2 target must add the
same-prime correction `(U - 1)^p / p`.

Deliverables:

1. `kummerLogFormalLinearCoeffModP` and its rational-padic Teichmuller lift.
2. `kummerLogFormalLowDegreeRepresentative`.
3. Degree `< p - 1` and even-row coefficient/reduction theorems for the raw
   formal representative.

######## CU-11f2b2b - Compare the normalized quotient argument with the formal unit

Status: done
Claimer: Riccardo
Started: 2026-05-20T10:34:02+01:00
Completed: 2026-05-20T10:37:35+01:00
Result: Added the cleared-denominator Dwork specialization theorem
`kummerLogDworkArtinHasseNormalizedQuotientUnit_mul_scaled_eq_normalized` and
its finite quotient form
`kummerLogDworkArtinHasseNormalizedQuotientUnit_evalₐ_mul_scaled_eq_normalized`
in `KummerLogFormalEvaluator.lean`.
Audit: The proof uses the concrete Dwork quotient definition plus the proved
Artin-Hasse denominator identity
`kummerLogDworkArtinHasseQuotientDenUnit_mul_exp_sub_one`. It is the
specialized analogue of
`formalKummerQuotientUnit_mul_scaled_eq_normalized`, with the denominator
cleared; it does not assume the finite logarithm or coefficient comparison
still required in CU-11f2b2c.

Expose the quotient-level identity that evaluates the normalized
Artin-Hasse quotient unit at `dworkParameter`, specialized at the Kummer
column Teichmuller lift.

######## CU-11f2b2c - Prove the folded same-prime finite-log representative

Status: done
Claimer: Riccardo
Started: 2026-05-20T11:07:21+01:00
Progress: 2026-05-20T11:07:21+01:00 - Added the normalized complete-ring
Artin-Hasse factor API in `KummerLogNormalization.lean`:
`integralArtinHasseNormalizedExpMinusOneSeries`,
`integralExpMinusOneSeries_eq_X_mul_normalized`,
`artinHasseExp_eval_sub_one_eq_mul_normalized`,
`artinHasseNormalizedExpMinusOneEval_isUnit`, the complete-ring cancellation
theorem
`kummerLogDworkArtinHasseQuotientDenUnit_mul_normalized_eq_teich_mul_normalized`,
the product-form quotient identity
`kummerLogDworkArtinHasseNormalizedQuotientArg_add_one_mul_normalized_eq_normalized`,
and its finite quotient image
`kummerLogDworkArtinHasseNormalizedQuotientArg_evalₐ_add_one_mul_normalized_eq_normalized`.
Audit: The common `varpi = dworkParameter` factor is cancelled only in the
complete Dwork ring using `dworkParameter_regular`; the finite quotient theorem
is obtained afterward by applying `AdicCompletion.evalₐ`. This does not cancel
inside `R / (varpi^(p - 1))`.
Progress: 2026-05-20T11:26:53+01:00 - Added the quotient-coordinate
extensionality theorem `valuedLambdaQuotientDworkCoeffModP_ext` in
`KummerLogCoefficient.lean` and the evaluator reduction
`kummerLogFormalLowDegreeRepresentative_eval_eq_specializedFiniteLog_of_coeff`
in `KummerLogFormalEvaluator.lean`. The remaining proof obligation is now the
termwise coordinate theorem for the finite same-prime logarithm of the
normalized Artin-Hasse quotient; the quotient equality itself no longer needs
additional plumbing.
Progress: 2026-05-20T11:45:58+01:00 - Added the remaining formal-side
low-degree representative coordinate helpers in `KummerLogFormalEvaluator.lean`:
`kummerLogFormalLowDegreeRepresentative_coeff_one`,
`kummerLogFormalLowDegreeRepresentative_coeff_one_modP`, and
`kummerLogFormalLowDegreeRepresentative_coeff_eq_zero_of_ne_slots`. The finite
side still needs the normalized analogue of the Part5 homogeneous numerator
calculation; high same-prime logarithm terms such as `n = p` can contribute to
low Dwork coordinates after division by `p`, so a naive `n ≤ d` truncation is
not sound.
Progress: 2026-05-20T12:18:44+01:00 - Proved in
`KummerLogFormalEvaluator.lean` that the proposed full low-degree quotient
target with the formal linear term is not the finite-log representative:
`valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_linear_eq_zero`
shows the finite side has zero linear Dwork coordinate, while
`kummerLogFormalLinearCoeffModP_ne_zero` shows the added formal linear
coefficient is nonzero for every Kummer column when `p >= 5`. The explicit
guardrail theorem is
`kummerLogFormalLowDegreeRepresentative_eval_ne_specializedFiniteLog`. This
means CU-11f2b2c must use a corrected/folded representative for the finite
same-prime logarithm; the current `kummerLogFormalLowDegreeRepresentative`
cannot be the quotient equality target.
Progress: 2026-05-20T15:42:42+01:00 - Rewrote the target around the corrected
same-prime expansion.  For `U = A_p(varpi) / A_p(c * varpi)`,
`Y = U - 1 = varpi * Z`, the finite logarithm modulo `varpi^(p - 1)` is

```text
sum_{n = 1}^{p - 1} (-1)^(n + 1) * Y^n / n
  + Y^p / p
```

not the raw degree `< p - 1` truncation of the formal logarithm.  The folded
term rewrites integrally as
`epsilon_varpi * varpi * Z^p`, where
`p * epsilon_varpi = varpi^(p - 1)`, and its residue
`epsilon_varpi ≡ -1 mod varpi` cancels the raw formal linear coefficient.

Use the same-prime finite-log definitions termwise to prove the folded
representative theorem.  The proof must keep the order of operations straight:
expand the finite logarithm in the complete/integral setting, identify the
single surviving same-prime correction `Y^p / p`, rewrite that term using
ramification, and only then pass to the quotient modulo `varpi^(p - 1)`.

Mathematical spine:

1. For `Y ∈ varpi R`, the logarithm terms with `1 ≤ n ≤ p - 1` are integral
   because `n` is a `p`-adic unit.
2. The term `Y^p / p` has `varpi`-valuation at least `1`, hence survives
   modulo `varpi^(p - 1)`.
3. Every term `Y^n / n` with `n > p` has `varpi`-valuation at least
   `p` or higher after subtracting the possible `p`-adic denominator, and
   therefore vanishes modulo `varpi^(p - 1)`.
4. Writing `Y = varpi * Z` gives
   `Y^p / p = epsilon_varpi * varpi * Z^p`.
5. Since `epsilon_varpi ≡ -1 mod varpi`, the folded correction cancels the raw
   formal linear coefficient `(1 - c) / 2`; this agrees with the proved
   fixedness theorem showing the finite specialized log has zero linear Dwork
   coordinate.

Lean-facing targets:

```lean
samePrimeFiniteLog_eq_trunc_add_p_term_mod_varpi_pow_pred :
  samePrimeFiniteLog (1 + Y) =
    (sum n in Finset.Icc 1 (p - 1),
      (-1)^(n + 1) * Y^n / n) + Y^p / p
```

in `R / (varpi^(p - 1))`, under `Y ∈ (varpi)`.

```lean
samePrimeFiniteLog_p_term_eq_ramificationUnit_mul :
  Y = varpi * Z →
  Y^p / p = epsilon_varpi * varpi * Z^p
```

before reduction.

```lean
kummerLogFoldedRepresentative_linearCoeff_eq_zero :
  valuedLambdaQuotientDworkCoeffModP 1 foldedRepresentative = 0
```

for the specialized normalized quotient.

```lean
kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_folded_even :
  kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP ... j a =
    foldedEvenCoeff ... j a
```

followed by the comparison of `foldedEvenCoeff` with the Bernoulli/formal
right-hand side needed by CU-11f2b3.
Completed: 2026-05-20T22:28:41+01:00
Result: Closed by CU-11f2b2c1 through CU-11f2b2c4.  The final implementation
uses the folded same-prime finite-log representative, proves the `n = p`
ramification correction has zero even-row coordinate, identifies the unscaled
normalized even-row coefficient with the formal Bernoulli coefficient, and
provides the unconditional endpoint
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal`.

######### CU-11f2b2c1 - General folded finite-log expansion

Status: done
Claimer: Riccardo
Started: 2026-05-20T15:42:42+01:00
Completed: 2026-05-20T15:53:04+01:00
Result: Added the folded same-prime finite-log expansion theorem
`samePrimeFiniteLog_eq_sum_Icc_add_p_term_pow_pred` in
`BernoulliRegular/CyclotomicUnits/DworkParameter/Part16.lean`.  At precision
`lambda^(p - 1)`, it rewrites `samePrimeFiniteLog` as the sum of the ordinary
terms `1 <= n <= p - 1` plus the single folded same-prime term `n = p`.  The
tail theorem `samePrimeFiniteLogTerm_pow_pred_eq_zero_of_prime_lt` proves all
terms `n > p` vanish, using the arithmetic order bound
`pred_le_samePrimeFiniteLogTermOrder_of_prime_lt`.
Audit: This is a theorem in the existing `samePrimeFiniteLog` term API.  It
does not introduce an analytic logarithm, does not cancel `varpi` in the
finite quotient, and deliberately leaves the integral rewrite of the `n = p`
term as `Y^p / p` to CU-11f2b2c2.

Prove the general same-prime finite-log expansion modulo `varpi^(p - 1)` for
`Y ∈ varpi R`:

```text
log_fin(1 + Y)
  =
sum_{n = 1}^{p - 1} (-1)^(n + 1) * Y^n / n
  + Y^p / p
```

in the quotient.  The proof should be a valuation/truncation theorem: terms
`1 ≤ n ≤ p - 1` are the ordinary unit-denominator terms, `n = p` is the unique
surviving same-prime denominator term, and all `n > p` terms vanish modulo
`varpi^(p - 1)`.

Deliverables:

1. A theorem in the same-prime finite-log API, not a new analytic logarithm.
2. Explicit valuation lemmas for the `n > p` tail, including the case
   `p ∣ n`.
3. No quotient-level cancellation by `varpi`.

######### CU-11f2b2c2 - Ramification-unit form of the p-fold correction

Status: done
Claimer: Riccardo
Started: 2026-05-20T15:58:18+01:00
Completed: 2026-05-20T16:04:05+01:00
Result: Added the Dwork ramification unit API in
`BernoulliRegular/CyclotomicUnits/DworkParameter/Part11.lean`:
`dworkRamificationUnit`, `natCast_prime_mul_dworkRamificationUnit`,
`dworkRamificationUnit_mul_natCast_prime`,
`dworkRamificationUnit_add_one_mem_dworkParameterIdeal`,
`natCast_prime_mul_dworkRamificationCorrection`, and
`natCast_prime_mul_dworkRamificationCorrection_of_eq`.  Added the support
lemma `dworkRamificationCorrection_sub_linear_mem_parameterIdeal_sq`, which
shows that if `Z ≡ z0 mod varpi`, then the integral folded correction
`epsilon_varpi * varpi * Z^p` is congruent to `-z0^p * varpi` modulo
`varpi^2`.  The correction theorem
states that if `Y = varpi * Z`, then the integral element
`epsilon_varpi * varpi * Z^p` has product with `p` equal to `Y^p`, which is
the Lean-friendly form of `Y^p / p = epsilon_varpi * varpi * Z^p` before
passing to the finite quotient.
Audit: The source of the unit is the already proved corrected Dwork parameter
equation `dworkParameter_pow_pred_eq_neg_p_mul_tailUnit`; the unit is
`epsilon_varpi = -artinHasseTailUnit`.  The residue theorem follows from
`artinHasseTailUnit = 1 + artinHasseTail`,
`artinHasseTail_mem_dworkCompleteLambdaIdeal_pow`, and
`dworkParameterIdeal_eq_dworkCompleteLambdaIdeal`.  No new ramification
assumption or quotient-level cancellation is introduced.

Rewrite the correction term integrally.  If

```text
Y = varpi * Z,
p * epsilon_varpi = varpi^(p - 1),
```

then prove before passing to the quotient:

```text
Y^p / p = epsilon_varpi * varpi * Z^p.
```

Also expose the residue theorem:

```text
epsilon_varpi ≡ -1 mod varpi.
```

This residue sign is the mathematical source of the linear-coordinate
cancellation.

Deliverables:

1. A named ramification-unit definition or reuse of the existing quotient of
   `varpi^(p - 1)` by `p`.
2. The integral rewrite of `Y^p / p`.
3. The mod-`varpi` sign theorem for the Dwork/cyclotomic normalization.

######### CU-11f2b2c3 - Specialized folded normalized-quotient representative

Status: done
Claimer: Riccardo
Started: 2026-05-20T16:26:18+01:00
Progress: 2026-05-20T16:26:18+01:00 - Adjusted the route to keep the
ramification correction on the complete Dwork side before taking quotient
coordinates.  Added the complete-ring linearization helper
`dworkRamificationCorrection_sub_linear_mem_parameterIdeal_sq`, so the C3
linear cancellation can use `epsilon_varpi ≡ -1 mod varpi` without any
division by `p` or cancellation inside the finite quotient.
Completed: 2026-05-20T16:54:15+01:00
Result: Added the folded representative API in
`BernoulliRegular/CyclotomicUnits/KummerLogFormalEvaluator.lean`:
`samePrimeFoldedFiniteLogPowPred`,
`dworkParameterNormalizedFoldedFiniteLogApprox`,
`scaledDworkParameterNormalizedFoldedFiniteLogApprox`,
`kummerLogDworkArtinHasseSpecializedFoldedFiniteLog`,
`kummerLogDworkArtinHasseSpecializedFiniteLog_eq_folded`, and
`kummerLogDworkArtinHasseSpecializedFiniteLog_factorPow_eq_folded`.  Also
added `valuedLambdaQuotientDworkCoeffModP_specializedFoldedFiniteLog_linear_eq_zero`,
which transports the existing finite-side linear fixedness theorem across the
folded equality.
Audit: The folded equality is sourced from
`samePrimeFiniteLog_eq_sum_Icc_add_p_term_pow_pred` and the already proved
normalized complete-ring quotient bridge
`kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs`.
The proof does not cancel `lambda` or `varpi` in the finite quotient and does
not reuse the false raw low-degree representative equality.

Specialize CU-11f2b2c1 and CU-11f2b2c2 to

```text
U = A_p(varpi) / A_p(c * varpi),
Y = U - 1,
c = omega a.
```

The normalized complete-ring identity from CU-11f2b2b supplies this `U`; the
same-prime logarithm should be applied to `Y`, not to a denominator-cleared
expression.  The endpoint can be either a quotient equality with a folded
representative or a family of quotient-coordinate equalities.

Implementation route:

1. Work coordinate-first.  Introduce the specialized normalized finite-log
   argument `q = U - 1` on the valued side, but move the ramification
   correction through the Dwork evaluation/coordinate bridge before using the
   complete-ring correction lemmas.
2. Do not state a raw valued-side theorem equating the `n = p` term with the
   Dwork correction unless a valued-side ramification unit has first been
   defined.  The preferred Lean target is a Dwork-coordinate theorem for the
   image of the `n = p` term.
3. Extract `q = lambda * Z` from the principal-generator API only to feed the
   finite-log term construction.  Do not divide or cancel by `lambda` in the
   finite quotient.
4. Prove the first-order approximation
   `q - alpha * lambda ∈ lambda^2`, transport it to the corrected Dwork
   parameter, and then apply
   `dworkRamificationCorrection_sub_linear_mem_parameterIdeal_sq`.
5. Prove the linear coordinate in two pieces: the ordinary `n = 1` term gives
   `+alpha`, while the folded `n = p` correction gives `-alpha` after reducing
   `alpha^p = alpha` in the residue field.

Deliverables:

1. A definition or theorem naming the specialized folded representative.
2. A proof that its linear Dwork coordinate is zero, by combining the raw
   `(1 - c) / 2` linear term with the `Y^p / p` correction.
3. A theorem replacing the false raw equality target:
   the finite specialized log equals the folded representative modulo
   `varpi^(p - 1)`.

######### CU-11f2b2c4 - Folded even-row coefficient comparison

Status: done
Claimer: Riccardo
Started: 2026-05-20T16:54:15+01:00
Progress: 2026-05-20T16:54:15+01:00 - Added the folded-coordinate bridge
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_folded`, the
coordinate-first reduction
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_one_sub_pow_mul_unscaled`,
and the source-isolating handoff theorem
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal_of_unscaled`.
Progress: 2026-05-20T17:28:50+01:00 - Added concrete C4 support lemmas:
`dworkRamificationUnit_add_one_mem_dworkParameterIdeal_pow_tail`,
`pow_prime_sub_pow_mem_ideal_pow_pred_of_sub_mem`,
`dworkRamificationCorrection_sub_linear_mem_parameterIdeal_pow_pred`, the
approximant coordinate lemma
`valuedLambdaQuotientDworkCoeffModP_mk_dworkParameterApprox_pow_of_lt`, and
`dworkRamificationCorrection_evenCoeff_eq_zero_of_sub_residue`.  These prove
that the integral ramification-unit representative of the folded `n = p` term
has zero even Kummer coordinates once the divided argument is reduced to a
rational-padic residue lift, and that low powers of the finite Dwork
approximant have the expected single coordinate.
Completed: 2026-05-20T22:26:21+01:00
Result: Proved the unscaled normalized even-row source theorem
`valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal`
from concrete homogeneous finite-log inputs, including the rational
normalized Artin-Hasse Bernoulli coefficient bridge and the low-degree
ordinary-term regrouping.  Added the unconditional endpoint
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_formal`, which
feeds CU-11f2b3 without assuming the old false raw low-degree quotient
equality.

Compute the even Kummer-row coordinates of the folded representative and use
them to finish the finite-to-formal evaluator.  This is the practical endpoint
needed by CU-11f2b3 and CU-11f3.

Use the existing specialization factor theorem first:

```lean
valuedLambdaQuotientDworkCoeffModP_specializedFiniteLog_eq_one_sub_pow_mul_unscaled
```

This reduces the specialized column to the unscaled normalized finite-log
coordinate multiplied by `1 - c^i`.  The real C4 target should therefore be an
unscaled even-row theorem.

The `Y^p / p` correction should not be discarded by formal degree.  Prove its
effect by Dwork coordinates.  For even rows, the expected mechanism is that
`epsilon_varpi * varpi * Z^p` has only the linear coordinate at the precision
needed after `Z` is reduced modulo `varpi`; any even-row contribution must be
proved zero, or else included explicitly in the folded coefficient.  This is a
coordinate statement, not a truncation statement.

Implementation route:

1. Prove the unscaled even-row theorem first, with a target like
   `valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal`.
2. Expand the unscaled finite logarithm through the homogeneous normalized
   finite-log machinery already in `KummerLogNormalization.lean` and
   `DworkParameter/Part5.lean`.
3. Kill irrelevant slices by support and coordinate theorems, including a
   separate proof that the folded `n = p` correction has zero even-row
   coordinate.
4. Reinsert the specialized column factor `1 - c^i` using the existing
   `specializedFiniteLog_eq_one_sub_pow_mul_unscaled` theorem.
5. Finish with the formal specialization theorem from CU-11e and feed the
   resulting coefficient theorem into CU-11f2b3.

Deliverables:

1. A theorem giving
   `kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP ... j a` as a folded
   even coefficient.
2. A comparison of that folded even coefficient with the CU-11d/CU-11e formal
   Bernoulli coefficient target, without assuming the p-fold correction
   vanishes.
3. The final theorem needed to feed CU-11f2b3.

####### CU-11f2b3 - Assemble the formal-to-finite coefficient equality

Status: done
Claimer: Riccardo
Started: 2026-05-20T10:02:33+01:00
Progress: 2026-05-20T10:02:33+01:00 - Added
`KummerLogFormalEvaluator.lean` and the proved bridge
`kummerLogFormalEvaluator_coeff_eq_of_polynomialRepresentative`, which
combines the polynomial representative equality, the degree bound, and the
row coefficient theorem into the target CU-11f2b coefficient equality.
Completed: 2026-05-20T22:33:37+01:00
Result: Added the unconditional assembly theorem
`kummerLogFormalEvaluator_coeff_eq`, sourced from the folded finite-log/formal
coefficient theorem, and the congruence-RHS endpoint
`kummerLogDworkArtinHasseSpecializedFiniteLogCoeffModP_eq_congrRhs` for the
next concrete matrix-entry ticket.

Use CU-11f2b1 and CU-11f2b2 with the existing quotient-coordinate API to prove
the final equality stated in CU-11f2b.  After the CU-11f2b2c correction, this
assembly must consume folded even-coordinate theorems; it must not try to
recover the false quotient equality with
`kummerLogFormalLowDegreeRepresentative`.

##### CU-11f3 - Concrete squared-family matrix entry congruence

Status: done
Claimer: Riccardo
Started: 2026-05-20T22:42:03+01:00
Completed: 2026-05-20T22:45:04+01:00
Result: Added
`concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP` and the
CU-11f3 endpoint
`concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs`, assembling the
concrete squared-family matrix entry from the `2 •` concrete-vector identity,
the quotient coordinate API, and the CU-11f2 finite-log coefficient theorem.

Assemble the theorem for the currently implemented concrete logarithm columns,
which are squared-family columns.

Target shape:

```text
concreteKummerLogMatrix ... j a =
  squaredKummerLogCoeffCongrRhs p hp_three j a
```

Equivalently, the right-hand side has the factor
`squaredKummerLogUnitFactor = 2 * kummerLogUnitFactor`.

Deliverables:

1. Use `concreteKummerLogVector_evalₐ_pow_pred_eq_two_nsmul_dworkArtinHasseSpecializedFiniteLog`.
2. Use CU-11f1 and CU-11f2 to extract the row coefficient.
3. Export `squaredKummerLogUnitFactor_ne_zero`.

##### CU-11f4 - Normalized-family bookkeeping and final CU-11f API

Status: done
Claimer: Riccardo
Started: 2026-05-20T22:53:41+01:00
Completed: 2026-05-20T22:53:41+01:00
Result: Added final normalized and squared-family API wrappers:
`normalizedKummerLogCoeff_congr`,
`concreteKummerLogMatrix_eq_two_mul_kummerLogCoeffCongrRhs`,
`concreteSquaredKummerLogMatrixEntry_congr`, and
`concreteKummerLogMatrix_eq_squaredKummerLogCoeffCongrRhs_matrix`.  Added
determinant-stage unit helpers `two_zmod_isUnit_of_five_le`,
`squaredKummerLogUnitFactor_isUnit`, `two_pow_kummerLogRank_zmod_ne_zero`,
`two_pow_kummerLogRank_zmod_isUnit`, and
`matrix_det_two_smul_ne_zero_iff`, so the extra squared-family factor `2`
is explicitly harmless for determinant nonvanishing.

Expose both coefficient normalizations clearly for downstream determinant and
index arguments.

Deliverables:

1. The normalized formal coefficient theorem with unit
   `kummerLogUnitFactor = -((2*j)!)^-1`.
2. The squared-family concrete matrix theorem with unit
   `squaredKummerLogUnitFactor = 2 * kummerLogUnitFactor`.
3. A determinant-stage note/theorem that the extra column factor `2` is a unit
   modulo `p`, so it does not affect nonvanishing.
4. Mark CU-11f done only after the concrete API needed by CU-13 is available.

### CU-12 - Vandermonde matrix over ZMod p

Status: done
Claimer: Riccardo
Started: 2026-05-16T15:16:12+02:00
Completed: 2026-05-20T23:18:15+01:00
Result: The finite-field Vandermonde determinant input is proved in
`BernoulliRegular/CyclotomicUnits/Vandermonde.lean`.  The matrix is
`vandermondeTeichmullerEvenSubOneMatrix`, with nodes
`teichmullerEvenNode`; the support lemmas
`teichmullerEvenNode_injective` and `teichmullerEvenNode_ne_one` identify the
columns as distinct nontrivial even Teichmuller residues.  The endpoint is
`vandermonde_teichmuller_even_sub_one_det_ne_zero`.
Audit: The proof is finite-field linear algebra.  It rewrites the transpose as
a diagonal matrix with nonzero diagonal entries times a geometric-polynomial
evaluation matrix, then applies the ordinary Vandermonde determinant theorem.
No p-adic or cyclotomic-unit logarithm source is used.

This is a tractable finite-field ticket and should be done early.

Matrix:

```text
V_{j,a} = omega(a)^(2*j) - 1
```

for `1 <= j <= r` and `2 <= a <= g`.

Target:

```text
theorem vandermonde_teichmuller_even_sub_one_det_ne_zero :
    Matrix.det V != 0
```

Proof:

1. Put `x_a = omega(a)^2`.
2. Show the `x_a` for `2 <= a <= g` are the nontrivial quadratic residues,
   hence pairwise distinct and not equal to `1`.
3. If a linear relation among rows exists, the polynomial

```text
P(X) = sum_{j=1}^r d_j * (X^j - 1)
```

vanishes at every `x_a` and at `1`.
4. This gives at least `r + 1` distinct roots while `degree P <= r`, so
   `P = 0`; hence all coefficients are zero.

Expected difficulty: medium. This is independent of p-adic analysis.

### CU-13 - Kummer determinant theorem

Status: done
Claimer: Riccardo
Started: 2026-05-20T23:31:49+01:00
Completed: 2026-05-20T23:43:31+01:00
Result: Added `BernoulliRegular/CyclotomicUnits/KummerLogDeterminant.lean`.
The determinant factorization is
`concreteKummerLogMatrix_eq_diagonal_mul_vandermonde`, and its determinant
form is `concreteKummerLogMatrix_det_eq_prod_rowFactor_mul_vandermonde_det`.
CU-12 supplies `vandermonde_teichmuller_even_sub_one_det_ne_zero`, while CU-11
supplies `kummerLogCoeff_congr` and
`squaredKummerLogUnitFactor_ne_zero`.  The endpoint
`kummerLogMatrix_det_ne_zero_iff_bernoulli_nonzero` proves determinant
nonvanishing exactly equivalent to
`∀ j, 1 ≤ j → 2 * j ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli (2 * j)).num`.
Audit: The proof does not assume a bundled determinant or Bernoulli
nonvanishing package.  It factors the concrete matrix row-by-row, takes
determinants, cancels only nonzero finite-field units, and proves
`bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num` by clearing the concrete
rational denominator of `B_(2j)/(2j)` and using the already-proved denominator
unit facts.

Target:

```text
theorem kummerLogMatrix_det_ne_zero_iff_bernoulli_nonzero :
    Matrix.det (kummerLogMatrix p) != 0 <->
      forall j, 1 <= j -> 2 * j <= p - 3 ->
        not (p : Int) | (bernoulli (2 * j)).num
```

Proof:

1. Use CU-11 to factor the matrix modulo `p`:

```text
C = diag(u_j * B_(2j)/(2j)) * V
```

2. Use CU-12 to show `det V != 0`.
3. Since `u_j != 0` and `2j` is invertible modulo `p`, the determinant is
   nonzero exactly when all Bernoulli numerator factors are nonzero modulo `p`.

Expected difficulty: medium once CU-11 and CU-12 exist.

### CU-14 - Saturation from the logarithm determinant

Status: done
Claimer: Riccardo
Started: 2026-05-21T00:17:05+01:00
Completed: 2026-05-21T09:21:22+01:00
Split: 2026-05-20T23:58:00+01:00 - Split into CU-14a through CU-14f.
Adjusted: 2026-05-21T00:13:05+01:00 - Use integer exponents, exact
pth-power subgroups in a commutative group, and split out the missing local
log-domain lemma for arbitrary `EPlus` witnesses.
Result: Closed by CU-14a through CU-14f.  The endpoint
`cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero` is proved in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean` from the concrete Kummer
matrix determinant hypothesis, the completed-log relation, the finite-field
kernel equation, and the group-theoretic saturation criterion.  Verified with
`lake build`.

Target:

```text
theorem cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero :
    Matrix.det (kummerLogMatrix p) != 0 ->
      pSaturated CPlus EPlus p
```

Concrete statement:

If

```text
(-1)^s * prod_{a=2}^g eps_a^e_a in (EPlus)^p
```

then

```text
(e_a : ZMod p) = 0
```

for every `a`, where `s : Z` and `e_a : Z`.  Integer exponents are essential:
an arbitrary element of `CPlus` may use inverses of the generators.  The sign
exponent is harmless because `p` is odd, so every sign is itself a `p`th power:
`((-1)^s)^p = (-1)^s`.

Proof outline:

1. Raise the relation to the `(p - 1)`st power.
2. Take the p-adic logarithm.
3. The right side is divisible by `p`.
4. In the real basis, this gives

```text
C * e = 0 mod p.
```

5. If `det C != 0`, then `e = 0 mod p`.

Expected difficulty: high, mostly because of the local embedding/logarithm API.

Close CU-14 only after all subtickets below are done.  Do not replace any of
these steps by a bundled saturation or logarithm-relation hypothesis.

#### CU-14a - Define the saturation and generator-exponent API

Status: done
Claimer: Riccardo
Started: 2026-05-21T00:17:05+01:00
Completed: 2026-05-21T00:22:30+01:00
Result: Added `BernoulliRegular/CyclotomicUnits/Saturation.lean` with
`EPlus`, exact-image `pPowerSubgroup`, `pSaturated`, integer exponent products
for `CPlus`, the odd-prime sign pth-power lemma
`neg_one_zpow_mem_pPowerSubgroup_CPlus`, and the concrete criterion
`CPlus_pSaturated_of_generator_exponents_modP_zero`.  The criterion is proved
from subgroup closure induction, exact p-power witnesses, and
`ZMod` divisibility of integer exponents; it does not package an unproved
logarithm or determinant source.

Goal: expose the exact group-theoretic statement that CU-14 needs, before any
p-adic logarithms are used.

Definitions/theorems to add, probably in a new file
`BernoulliRegular/CyclotomicUnits/Saturation.lean`:

```text
def EPlus : Subgroup (O KPlus)^* := top

def pPowerSubgroup [CommGroup G] (H : Subgroup G) (p : Nat) : Subgroup G :=
  {x | exists y in H, y^p = x}

def pSaturated [CommGroup G] (H E : Subgroup G) (p : Nat) : Prop :=
  H <= E and H ∩ pPowerSubgroup E p <= pPowerSubgroup H p
```

Do not define `pPowerSubgroup` as the closure of pth powers.  In this
commutative unit group the pth-power image is already a subgroup, and CU-15
needs the exact image.

Then prove the finite-generator criterion for the concrete `CPlus`:

```text
theorem CPlus_pSaturated_of_generator_exponents_modP_zero
    (h : forall (s : Z) (e : Fin r -> Z),
      (-1)^s * prod a, (CPlusGenerator a)^(e a) in pPowerSubgroup EPlus p ->
      forall a, (e a : ZMod p) = 0) :
    pSaturated CPlus EPlus p
```

The statement may use the existing subgroup closure API instead of this exact
syntax, but it must explicitly handle the `-1` generator.  The sign should be
discharged here using oddness of `p`, not in the determinant argument.

Deliverables:

1. A concrete `EPlus`/top-subgroup name if one is not already available.
2. A concrete `pSaturated` definition or an adapter to an existing one.
3. A lemma reducing `pSaturated CPlus EPlus p` to mod-`p` vanishing of the
   integer exponents of `CPlusGenerator`.
4. A sign lemma for integer exponents:

```text
theorem neg_one_zpow_mem_pPowerSubgroup_CPlus
    (s : Z) :
    (-1 : (O KPlus)^*)^s in pPowerSubgroup (CPlus hp_three) p
```

using that `p` is odd.

#### CU-14b - Convert a pth-power relation to a completed logarithm relation

Status: done
Claimer: Riccardo
Completed: 2026-05-21T08:27:22+01:00
Result: Closed by CU-14b1 through CU-14b3.  The parent endpoint
`completedLog_relation_of_CPlus_product_mem_powers` is proved in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean`, with the supporting local
principal-unit domain theorem `EPlus_localImage_pow_pred_mem_logDomain` and
local p-power logarithm theorem `completedLog_pow_p_eq_p_smul`.
Audit: CU-14b3 is not a wrapper around a bundled logarithm relation.  It builds
the relation from the canonical `CPlusExponentProduct` input, maps real units
through `EPlus_completedLogDomainPowPred`, uses proved completed-log
additivity/integer-power lemmas and the CU-11 Kummer completed columns, and
uses `completedLog_pow_p_eq_p_smul` to produce the explicit `p`-multiple
witness in `dworkFixedSubalgebra p K`.  Verified no `sorry`/`admit` in
`LogDomain.lean` and verified with
`lake build BernoulliRegular.CyclotomicUnits.LogDomain` and `lake build`.

Goal: from a relation in the real unit group, derive the additive relation
among the completed logarithm columns.

Target shape:

```text
theorem completedLog_relation_of_CPlus_product_mem_powers
    (hpow :
      (-1)^s * prod a, (CPlusGenerator a)^(e a) = u^p) :
    sum a, (e a) • concreteKummerLogVector a
      is p-divisible in the completed Dwork fixed subalgebra
```

Here `s : Z`, `e : Fin r -> Z`, and the products use `zpow`.

The proof should:

1. Raise the unit relation to `p - 1`.
2. Prove that the local image of every `u^(p-1)` with `u : EPlus` lies in the
   principal-unit/log domain.
3. Use CU-11a/CU-11b log-domain results for each powered generator.
4. Use additivity of the completed p-adic logarithm on the relevant
   principal-unit subgroup.
5. Put the right-hand side in `p • _` because it is the log of a `p`th power.

This ticket is only the analytic logarithm relation.  It should not extract
Dwork coordinates and should not use determinant nonvanishing.

##### CU-14b1 - Principal-unit domain for arbitrary real units

Status: done
Claimer: Riccardo
Started: 2026-05-21T07:49:36+01:00
Completed: 2026-05-21T07:56:38+01:00
Result: Added `BernoulliRegular/CyclotomicUnits/LogDomain.lean` with
`EPlus_localImage_pow_pred_mem_logDomain`, proving the completed Dwork local
image of any real unit lies in `1 + lambda` after raising to `p - 1`.  The
proof factors through the cyclotomic lambda residue field and maps the result
to the valuation and Dwork completions.  Updated `BernoulliRegular.lean`.
Verified with `lake build`.

Goal: prove the local-domain lemma needed for the `EPlus` pth-power witness.

Target shape:

```text
theorem EPlus_localImage_pow_pred_mem_logDomain
    (u : (O KPlus)^*) :
    localImage(u)^(p - 1) is in 1 + lambdaIdeal
```

The proof should use that the residue field has characteristic `p` and every
nonzero residue class has order dividing `p - 1`.  This is the only part of
CU-14b involving an arbitrary unit rather than the concrete Kummer columns.

##### CU-14b2 - Logarithm of a pth power is p-divisible

Status: done
Claimer: Riccardo
Started: 2026-05-21T07:58:40+01:00
Completed: 2026-05-21T08:05:12+01:00
Result: Added the valued principal-unit completed logarithm domain and proved
`completedLog_pow_p_eq_p_smul` in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean`, using the same-prime finite
log product theorem and the compatible quotient coordinates.  Verified with
`lake build BernoulliRegular.CyclotomicUnits.LogDomain` and `lake build`.

Goal: for units already in the principal-unit domain, prove the completed log
of a pth power is a `p`-multiple.

Target shape:

```text
theorem completedLog_pow_p_eq_p_smul
    (hx : x in logDomain) :
    completedLog (x^p) = p • completedLog x
```

This should be a local p-adic logarithm theorem.  It must not be specialized
to cyclotomic generators.

##### CU-14b3 - Assemble the completed logarithm relation

Status: done
Claimer: Riccardo
Started: 2026-05-21T08:08:13+01:00
Completed: 2026-05-21T08:21:13+01:00
Result: Proved `completedLog_relation_of_CPlus_product_mem_powers` in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean`.  Added the completed-log
additivity, integer-power, real-unit local-domain, and CPlus exponent-product
bridges needed to turn a `pPowerSubgroup EPlus p` relation into a
`p`-divisible relation in `dworkFixedSubalgebra p K`.  Verified with
`lake build BernoulliRegular.CyclotomicUnits.LogDomain` and `lake build`.

Goal: combine CU-14b1, CU-14b2, CU-11a/CU-11b, and log additivity to prove
`completedLog_relation_of_CPlus_product_mem_powers`.

#### CU-14c - Extract the mod-p Kummer matrix kernel equation

Status: done
Claimer: Riccardo
Started: 2026-05-21T08:28:48+01:00
Completed: 2026-05-21T08:37:17+01:00
Result: Proved `concreteKummerLogMatrix_mulVec_exponents_eq_zero` in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean`.  Added the coordinate
helpers extracting each concrete matrix row from the completed-log linear
combination and showing every row coefficient vanishes modulo `p` for a
`p`-divisible fixed-subalgebra relation.  The proof uses the concrete
`concreteKummerLogVector`/`concreteKummerLogMatrix` APIs and fixed-basis
coordinate linearity only; it does not use determinant nonvanishing.  Verified
with `lake build BernoulliRegular.CyclotomicUnits.LogDomain` and `lake build`.

Goal: turn the completed logarithm relation from CU-14b into the finite-field
linear equation controlled by the concrete Kummer matrix.

Target shape:

```text
theorem concreteKummerLogMatrix_mulVec_exponents_eq_zero
    (hlog :
      sum a, (e a) • concreteKummerLogVector a is p-divisible) :
    concreteKummerLogMatrix hp_three hp_five *ᵥ
      (fun a => (e a : ZMod p)) = 0
```

Here `e : Fin r -> Z`; the scalar multiplication in the completed ring is
integer scalar multiplication, and the vector uses reduction `Z -> ZMod p`.

The proof should use the existing coordinate extraction API from CU-11f:

```text
concreteKummerLogMatrix_apply
concreteKummerLogCoeff_eq
valuedLambdaQuotientDworkCoeffModP_...
```

This ticket is where the phrase

```text
C * e = 0 mod p
```

becomes a Lean theorem.  It should not use determinant nonvanishing; it should
only prove the matrix-kernel relation.

#### CU-14d - Linear algebra: determinant nonzero kills the kernel

Status: done
Claimer: Riccardo
Started: 2026-05-21T09:04:16+01:00
Completed: 2026-05-21T09:06:27+01:00
Result: Added
`vector_eq_zero_of_det_ne_zero_of_mulVec_eq_zero` and
`exponents_modP_eq_zero_of_kummerLogMatrix_relation` in
`BernoulliRegular/CyclotomicUnits/KummerLogLinearAlgebra.lean`; the
determinant file imports this bridge for compatibility.
Audit: The generic lemma delegates directly to mathlib's proved
`Matrix.eq_zero_of_mulVec_eq_zero`; the Kummer lemma only applies it to the
concrete matrix relation and takes coordinates, with no cyclotomic-unit,
p-adic-logarithm, or Bernoulli source assumption.

Goal: prove the finite-field matrix fact needed by the final assembly.

Target shape:

```text
theorem vector_eq_zero_of_det_ne_zero_of_mulVec_eq_zero
    {M : Matrix ι ι (ZMod p)}
    (hdet : M.det != 0)
    (hv : M *ᵥ v = 0) :
    v = 0
```

or the exact equivalent available from mathlib, packaged for the Kummer
matrix:

```text
theorem exponents_modP_eq_zero_of_kummerLogMatrix_relation
    (hdet : (concreteKummerLogMatrix hp_three hp_five).det != 0)
    (hrel :
      concreteKummerLogMatrix hp_three hp_five *ᵥ
        (fun a => (e a : ZMod p)) = 0) :
    forall a, (e a : ZMod p) = 0
```

This is pure linear algebra over `ZMod p`; it should not mention cyclotomic
units, p-adic logarithms, or Bernoulli numbers.

#### CU-14e - Assemble exponent vanishing from determinant nonvanishing

Status: done
Claimer: Riccardo
Started: 2026-05-21T09:12:37+01:00
Completed: 2026-05-21T09:21:22+01:00
Result: Proved
`CPlusGenerator_exponents_modP_zero_of_kummerLog_det_ne_zero` in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean`.
Audit: The proof first invokes
`completedLog_relation_of_CPlus_product_mem_powers` on the actual
`CPlusExponentProduct` membership in `pPowerSubgroup EPlus p`, then uses
`concreteKummerLogMatrix_mulVec_exponents_eq_zero`, and only then applies
`exponents_modP_eq_zero_of_kummerLogMatrix_relation` with `hdet`.  It does not
assume subgroup-index nondivisibility or Bernoulli nonvanishing.

Goal: combine CU-14b, CU-14c, and CU-14d into the concrete exponent theorem
consumed by CU-14a.

Target shape:

```text
theorem CPlusGenerator_exponents_modP_zero_of_kummerLog_det_ne_zero
    (hdet : (concreteKummerLogMatrix hp_three hp_five).det != 0)
    (hpow :
      (-1)^s * prod a, (CPlusGenerator a)^(e a) in pPowerSubgroup EPlus p) :
    forall a, (e a : ZMod p) = 0
```

Here `s : Z`, `e : Fin r -> Z`, and the products use `zpow`.

This theorem should be the first place where the determinant hypothesis is
used in CU-14.  It still should not mention subgroup index nondivisibility;
that belongs to CU-15.

#### CU-14f - Final saturation theorem

Status: done
Claimer: Riccardo
Started: 2026-05-21T09:12:37+01:00
Completed: 2026-05-21T09:21:22+01:00
Result: Proved
`cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero` in
`BernoulliRegular/CyclotomicUnits/LogDomain.lean` by passing the CU-14e
exponent-vanishing theorem to
`CPlus_pSaturated_of_generator_exponents_modP_zero`.
Audit: The final proof consumes the determinant only as `hdet`; the logarithm
relation is produced by CU-14b from the actual unit relation; the sign
generator is handled in CU-14a; and no subgroup-index conclusion is included.

Goal: close the original CU-14 target by combining CU-14a and CU-14e.

Target:

```text
theorem cyclotomicUnits_pSaturated_of_kummerLog_det_ne_zero
    (hdet : (concreteKummerLogMatrix hp_three hp_five).det != 0) :
    pSaturated (CPlus hp_three) EPlus p
```

Audit required before marking done:

1. The proof consumes the concrete matrix determinant from CU-13 only through
   `hdet`; it does not assume Bernoulli nonvanishing directly.
2. The p-adic logarithm relation is produced by CU-14b from the actual unit
   relation, not from a bundled relation package.
3. The sign generator is handled by CU-14a.
4. No subgroup-index conclusion is included; CU-15 is responsible for turning
   saturation into `p ∤ index`.

## Saturation And Assembly

### CU-15 - Saturation implies p does not divide the cyclotomic-unit index

Status: done
Claimer: Riccardo
Started: 2026-05-21T09:31:37+01:00
Completed: 2026-05-21T09:45:24+01:00
Result: Added `BernoulliRegular.CyclotomicUnits.SaturationIndex`, proving the
finite-index saturation criterion
`subgroup_not_dvd_index_of_pSaturated_top_of_pow_eq_one_mem`, the concrete
finite-index audit `CPlus_index_ne_zero`, and the CU-15 endpoint
`not_dvd_index_of_pSaturated` for `CPlus ≤ EPlus`.
Verification: `lake build BernoulliRegular.CyclotomicUnits.SaturationIndex`;
`lake build BernoulliRegular`.

Target:

```text
theorem not_dvd_index_of_pSaturated :
    pSaturated CPlus EPlus p ->
      not (p : Nat) | indexOf CPlus EPlus
```

Proof:

Use CU-05. The saturation statement is exactly injectivity of
`CPlus / CPlus^p -> EPlus / EPlus^p` after quotienting away signs.

Expected difficulty: medium.

### CU-16 - Bernoulli nonvanishing implies index nondivisibility

Status: done
Claimer: Riccardo
Started: 2026-05-21T09:50:02+01:00
Completed: 2026-05-21T09:57:48+01:00
Result: Added `BernoulliRegular.CyclotomicUnits.UnitsReflection` with
`not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero`, composing CU-13,
CU-14, and CU-15.  The proof handles the `p = 3` case by `CPlus = ⊤` and
uses the Kummer-log determinant/saturation route for `5 ≤ p`.
Verification: `lake build BernoulliRegular.CyclotomicUnits.UnitsReflection`;
`lake build BernoulliRegular`.

Target:

```text
theorem not_dvd_cyclotomicUnitIndex_of_bernoulli_nonzero
    (hB : forall j, 1 <= j -> 2 * j <= p - 3 ->
      not (p : Int) | (bernoulli (2 * j)).num) :
    not (p : Nat) | indexOf CPlus EPlus
```

Proof:

CU-13 -> CU-14 -> CU-15.

Expected difficulty: low after dependencies.

### CU-17 - Contrapositive weak reflection

Status: done
Claimer: Riccardo
Started: 2026-05-21T09:50:02+01:00
Completed: 2026-05-21T09:57:48+01:00
Result: Added `not_dvd_hPlus_of_not_dvd_hMinus_units` in
`BernoulliRegular.CyclotomicUnits.UnitsReflection`, composing CU-01,
CU-16, `CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd`, and the
CU-06 p-primary index theorem for `normalizedCPlus`.
Verification: `lake build BernoulliRegular.CyclotomicUnits.UnitsReflection`;
`lake build BernoulliRegular`.

Target:

```text
theorem not_dvd_hPlus_of_not_dvd_hMinus_units
    (hminus : not (p : Nat) | hMinus K) :
    not (p : Nat) | hPlus K
```

Proof:

1. CU-01 gives Bernoulli nonvanishing from `hminus`.
2. CU-16 gives `p not_dvd [EPlus : CPlus]`.
3. CU-06 converts this to `p not_dvd hPlus K`.

Expected difficulty: low after dependencies.

### CU-18 - Weak reflection by contrapositive

Status: done
Claimer: Riccardo
Started: 2026-05-21T10:01:54+01:00
Completed: 2026-05-21T10:04:06+01:00
Result: Added `weakReflection_dvd_hMinus_of_dvd_hPlus_units` in
`BernoulliRegular.CyclotomicUnits.UnitsReflection`, proving the TeX
Section 668-713 plus/minus weak reflection statement by contraposition from
CU-17.  Audit: the Lean theorem assumes only the odd-prime/cyclotomic-field
typeclass setup already required by the route; it introduces no bundled,
postponed, or source-hypothesis assumption.
Verification: `lake build BernoulliRegular.CyclotomicUnits.UnitsReflection`;
`lake build BernoulliRegular`.

Target:

```text
theorem weakReflection_dvd_hMinus_of_dvd_hPlus_units
    (hplus : (p : Nat) | hPlus K) :
    (p : Nat) | hMinus K
```

Proof:

Use classical contrapositive and CU-17.

Expected difficulty: low after dependencies.

### CU-19 - Kummer criterion through the units route

Status: done
Claimer: Riccardo
Started: 2026-05-21T10:01:54+01:00
Completed: 2026-05-21T10:04:06+01:00
Result: Added `dvd_h_iff_exists_dvd_bernoulli_units` in
`BernoulliRegular.CyclotomicUnits.UnitsReflection`; the public
`BernoulliRegular.KummerCriterion` consumes it directly.  This matches the TeX
Kummer-criterion consequence in Section 717-770: use `h = hPlus * hMinus`,
CU-18, and the minus Bernoulli criterion.  Audit: the theorem uses the named
analytic inputs already exposed by the route and introduces no hidden,
bundled, postponed, or source-hypothesis assumption.
Verification: `lake build BernoulliRegular.CyclotomicUnits.UnitsReflection`;
`lake build BernoulliRegular`.

Target:

Prove the public theorem from the units-route class-number criterion:

```text
theorem KummerCriterion :
    IsRegularPrime p <->
      forall k, 1 <= k -> 2 * k <= p - 3 ->
        not (p : Int) | (bernoulli (2 * k)).num
```

Proof:

1. Use `h = hPlus * hMinus`.
2. Use CU-18 to replace `p | h` by `p | hMinus`.
3. Use CU-01.

Expected difficulty: low after CU-18.
