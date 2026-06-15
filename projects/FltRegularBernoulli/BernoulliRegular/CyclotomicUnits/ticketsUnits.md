# Cyclotomic-Unit Reflection Strategy

This is a parallel route to the plus/minus weak reflection theorem, based on
`BernoulliRegular/CyclotomicUnits/cyclotomic_units_weak_reflection.tex`.

The target is the implication

```text
(p : Nat) | hPlus K -> (p : Nat) | hMinus K
```

for `K = Q(zeta_p)`, with `p` odd prime. This route is weaker than the
componentwise reflection theorem: it does not prove
`weakReflection_componentNontrivial`. It is still enough for Kummer's
criterion, because the final argument only needs
`p | hPlus -> p | hMinus`.

The point of this route is that it avoids Hilbert symbols, class-field theory,
Chebotarev, Artin reciprocity, power reciprocity, and Kummer pairings on class
groups. The hard inputs are instead analytic class-number formula results and
Kummer's explicit p-adic logarithmic determinant for cyclotomic units.

Do not hide either hard input inside a package hypothesis. The two large inputs
must remain named theorems:

```text
cyclotomicUnitIndex_primeConductor_pPrimary
relativeClassNumberCriterion_bernoulli
```

The second one appears to already exist, essentially as
`p_dvd_hMinus_iff_p_dvd_some_bernoulli` in
`BernoulliRegular/HMinus/HMinusCriterion.lean`; it still needs an exact API
audit for this route.

## Ticket Closure Rule

A ticket may be marked `done` only after the Lean theorem is absolutely
identical to the corresponding statement in
`cyclotomic_units_weak_reflection.tex`, modulo unavoidable notation and
transport. It must have no extra conditional, hidden, bundled, postponed, or
source-hypothesis assumption.

Before changing `Status:` to `done`, audit the Lean statement against the TeX
file and record the matching TeX location, Lean theorem name, and the fact that
there are no hidden or postponed assumptions. Conditional bridges may be
recorded as completed subtasks, but they do not close the parent ticket.

## Final Shape

### CU-00 - Final plus/minus weak reflection by cyclotomic units

Status: done
Claimer: Riccardo
Started: 2026-05-18T14:47:46+02:00

Goal theorem, probably in a new file
`BernoulliRegular/CyclotomicUnits/WeakReflection.lean`:

```text
theorem weakReflection_dvd_hMinus_of_dvd_hPlus_units
    (p : Nat) [Fact p.Prime] (hp_odd : p != 2)
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} Q K] [IsCMField K] :
    (p : Nat) | hPlus K -> (p : Nat) | hMinus K
```

If the existing `hPlus`/`hMinus` API forces a more concrete cyclotomic field,
start with the concrete model and add transport later:

```text
theorem weakReflection_dvd_hMinus_of_dvd_hPlus_units_model :
    (p : Nat) | hPlus (CyclotomicField p Q) ->
      (p : Nat) | hMinus (CyclotomicField p Q)
```

Proof plan:

1. Prove the contrapositive:
   `not (p | hMinus K) -> not (p | hPlus K)`.
2. Use the minus class-number/Bernoulli criterion to get
   `p not_dvd numerator B_(2j)` for every `1 <= j <= (p - 3) / 2`.
3. Use Kummer's p-adic logarithmic determinant to prove the real cyclotomic
   units are p-saturated in the full real unit group.
4. Convert saturation to `p not_dvd [EPlus : CPlus]`.
5. Use the cyclotomic-unit index theorem
   `p | [EPlus : CPlus] <-> p | hPlus K`.

Dependencies:
CU-01, CU-02, CU-06, CU-13, CU-14, CU-15, CU-17.

## Saturation And Assembly

## Recommended Order

1. CU-01 and CU-02: audit existing class-number API.
2. CU-05 and CU-12: pure algebra/finite-field tickets, independent and useful.
3. CU-03 and CU-04: define the cyclotomic-unit objects.
4. CU-06: state the cyclotomic-unit index theorem as a named major target.
5. CU-09 through CU-13: p-adic determinant theorem.
6. CU-14 through CU-18: saturation and weak-reflection assembly.
7. CU-19: final Kummer criterion route.

## Route Risks

1. This route proves only the plus/minus weak reflection theorem. It does not
   prove the componentwise eigenspace theorem
   `weakReflection_componentNontrivial`.
2. The cyclotomic-unit index theorem is a serious analytic theorem. It should
   not be treated as a small local lemma.
3. The p-adic determinant calculation requires a careful local model for
   `Q_p(zeta_p)` and the Artin-Hasse/Dwork parameter. If the repo does not
   already have this infrastructure, CU-09 through CU-11 are substantial.
4. Generic `IsCyclotomicExtension` statements may cause transport overhead.
   Start concrete if necessary, then generalize.
5. Sign and torsion quotients are harmless for odd `p`, but they need explicit
   bridge lemmas to keep the index and saturation statements clean.

## Non-Goals

This strategy does not use or recreate:

1. Hilbert-symbol product formulas.
2. One-sided Kummer principal reciprocity.
3. Class-field theory or Chebotarev.
4. Kummer pairings on class groups.
5. Any bundled reflection package or hidden assumption.

The route is independent of the REF-21/REF-22 reciprocity strategy. Its
hard theorems are analytic and p-adic, not reciprocity-theoretic.
