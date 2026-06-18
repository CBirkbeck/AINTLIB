# Inventory: ./HasseWeil/Curves/ResidueFieldAtSmoothPoint.lean

**File purpose**: Builds an explicit `F`-algebra isomorphism `C.CR/M ≃ₐ[F] F` at smooth-point
maximal ideals over algebraically closed `F`, and assembles the full unconditional form of
T-II-2-009 (`exists_heightOneSpectrum_fiber_card_eq_sepDegree`). This is "Piece 9" in stream A's
assembly. The file is partial: `quotientAlgEquivBase` is the core contribution; the larger
`inertiaDeg_eq_one` path requires `hScalarTower` as an explicit hypothesis (the scalar-tower
instance gap is documented in the module docstring).

**Imports**: `HasseWeil.Curves.NormValuation`, `HasseWeil.Curves.CurveMap`,
`HasseWeil.Curves.GenericFiber`, `Mathlib.RingTheory.Finiteness.Quotient`

---

### `noncomputable def SmoothPlaneCurve.quotientAlgEquivBase`

- **Type**: `[IsAlgClosed F] → (C : SmoothPlaneCurve F) → {M : Ideal C.CoordinateRing} → M.IsMaximal → (letI : Field (C.CoordinateRing ⧸ M); F ≃ₐ[F] (C.CoordinateRing ⧸ M))`
- **What**: Constructs an explicit `F`-algebra isomorphism from `F` to the residue field
  `C.CoordinateRing ⧸ M` at any maximal ideal `M`, valid over any algebraically closed `F`.
- **How**: Applies `AlgEquiv.ofBijective` to the algebra map `Algebra.ofId F (C.CR ⧸ M)`,
  using `C.algebraMap_bijective_quotient_of_maximal hM` (from `NormValuation.lean`, which in
  turn invokes Zariski's lemma + algebraic closure).
- **Hypotheses**: `F` algebraically closed; `M` maximal in `C.CoordinateRing`.
- **Uses from project**: `SmoothPlaneCurve.algebraMap_bijective_quotient_of_maximal`
  (from `NormValuation.lean`)
- **Used by**: `quotientAlgEquivBase_apply` (L72), `residueFieldsAlgEquiv` (L100),
  `residueLinearEquiv` (L167–168 via `algebraMap_bijective_quotient_of_maximal`)
- **Visibility**: public
- **Lines**: 63–70 (body 2 lines)
- **Notes**: None.

---

### `@[simp] theorem SmoothPlaneCurve.quotientAlgEquivBase_apply`

- **Type**: `[IsAlgClosed F] → (C : SmoothPlaneCurve F) → hM : M.IsMaximal → (c : F) → C.quotientAlgEquivBase hM c = algebraMap F (C.CoordinateRing ⧸ M) c`
- **What**: States that `quotientAlgEquivBase` acts as the algebra map on elements — the
  `AlgEquiv` is definitionally the `algebraMap`.
- **How**: `rfl` — the definition of `AlgEquiv.ofBijective` makes this true by computation.
- **Hypotheses**: Same as `quotientAlgEquivBase`.
- **Uses from project**: `SmoothPlaneCurve.quotientAlgEquivBase`
- **Used by**: unused in file (tagged `@[simp]` for external use)
- **Visibility**: public
- **Lines**: 72–77 (proof 1 line)
- **Notes**: None.

---

### `noncomputable def SmoothPlaneCurve.residueFieldsAlgEquiv`

- **Type**: `[IsAlgClosed F] → (C₁ C₂ : SmoothPlaneCurve F) → hQ : Q.IsMaximal → hP : P.IsMaximal → (letI; letI; (C₂.CR ⧸ Q) ≃ₐ[F] (C₁.CR ⧸ P))`
- **What**: Any two residue fields of smooth plane curves over algebraically closed `F` are
  `F`-algebra isomorphic; both are isomorphic to `F` via `quotientAlgEquivBase`, so
  `(C₂.CR ⧸ Q) ≃ₐ[F] F ≃ₐ[F] (C₁.CR ⧸ P)`.
- **How**: Composes `(C₂.quotientAlgEquivBase hQ).symm` with `C₁.quotientAlgEquivBase hP`
  using `AlgEquiv.trans`.
- **Hypotheses**: `F` algebraically closed; `Q ⊆ C₂.CR`, `P ⊆ C₁.CR` maximal.
- **Uses from project**: `SmoothPlaneCurve.quotientAlgEquivBase`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 90–100 (body 3 lines)
- **Notes**: Dead-code candidate within this file; likely intended for external consumers of
  the residue-field iso.

---

### `noncomputable def LinearEquiv.ofBijectiveAlgebraMap`

- **Type**: `{R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] → Function.Bijective (algebraMap R S) → R ≃ₗ[R] S`
- **What**: Generic utility: promotes a bijective algebra map `R → S` to an `R`-linear
  equivalence `R ≃ₗ[R] S`.
- **How**: Applies `LinearEquiv.ofBijective` to the `Algebra.linearMap R S`.
- **Hypotheses**: `algebraMap R S` is bijective.
- **Uses from project**: none
- **Used by**: `CurveMap.CoordHom.residueLinearEquiv` (L179)
- **Visibility**: public
- **Lines**: 108–112 (body 1 line)
- **Notes**: Generic utility; likely a mathlib duplication candidate (`LinearEquiv.ofBijective`
  on `Algebra.linearMap` is a thin wrapper).

---

### `theorem algebraMap_residueField_injective`

- **Type**: `[IsAlgClosed F] → hQ : Q.IsMaximal → hP : P.IsMaximal → φ : CurveMap C₁ C₂ → coordHom : φ.CoordHom → hLies : P.LiesOver Q → Function.Injective (algebraMap (C₂.CR ⧸ Q) (C₁.CR ⧸ P))`
- **What**: The algebra map between residue fields of a `CoordHom` lying-over pair is
  injective, because both residue fields are fields (a ring hom from a field is injective).
- **How**: Uses `RingHom.injective` for the algebra map between fields (Mathlib's field-hom
  injectivity), invoked as `(algebraMap ...).injective`.
- **Hypotheses**: `F` algebraically closed; `Q`, `P` maximal; `P` lies over `Q` via `coordHom`.
- **Uses from project**: none (pure Mathlib)
- **Used by**: `CurveMap.CoordHom.residueLinearEquiv` (L178)
- **Visibility**: public
- **Lines**: 118–136 (proof 5 lines)
- **Notes**: None.

---

### `noncomputable def CurveMap.CoordHom.residueLinearEquiv`

- **Type**: `[IsAlgClosed F] → φ : CurveMap C₁ C₂ → coordHom : φ.CoordHom → hQ : Q.IsMaximal → hP : P.IsMaximal → hLies : P.LiesOver Q → hScalarTower : IsScalarTower F (C₂.CR ⧸ Q) (C₁.CR ⧸ P) → (letI; letI; (C₂.CR ⧸ Q) ≃ₗ[C₂.CR ⧸ Q] (C₁.CR ⧸ P))`
- **What**: Constructs a `(C₂.CR ⧸ Q)`-linear equivalence between the two residue fields,
  given that both maps to `F` are bijective (from `algebraMap_bijective_quotient_of_maximal`)
  and the algebra map between residue fields is injective (fields). Surjectivity is derived
  from the scalar tower: any `b : C₁.CR ⧸ P` has a preimage `c : F` (by `hFP.2`), and
  `algebraMap F (C₁.CR ⧸ P) c` factors through `C₂.CR ⧸ Q` via the scalar tower.
- **How**: Derives `h_surj` via `IsScalarTower.algebraMap_apply` and `hFP.2`; `h_inj` from
  `algebraMap_residueField_injective`; then calls `LinearEquiv.ofBijectiveAlgebraMap` with
  the assembled bijection.
- **Hypotheses**: `F` algebraically closed; `Q`, `P` maximal; `P` lies over `Q`; explicit
  `IsScalarTower F (C₂.CR ⧸ Q) (C₁.CR ⧸ P)`.
- **Uses from project**: `algebraMap_residueField_injective` (L178),
  `LinearEquiv.ofBijectiveAlgebraMap` (L179),
  `SmoothPlaneCurve.algebraMap_bijective_quotient_of_maximal` (via `NormValuation.lean`, L167–168)
- **Used by**: `CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed` (L208)
- **Visibility**: public
- **Lines**: 147–179 (proof 33 lines)
- **Notes**: Proof is 33 lines (just over 30-line threshold). The `hScalarTower` hypothesis is
  the gap identified in the module docstring — this scalar tower is not automatically derived
  from `coordHom.toAlgebra`.

---

### `theorem CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed`

- **Type**: `[IsAlgClosed F] → φ : CurveMap C₁ C₂ → coordHom : φ.CoordHom → hQ : Q.IsMaximal → hP : P.IsMaximal → hLies : P.LiesOver Q → hScalarTower : IsScalarTower F (C₂.CR ⧸ Q) (C₁.CR ⧸ P) → Ideal.inertiaDeg Q P = 1`
- **What**: For a lying-over pair of maximal ideals in smooth-curve coordinate rings over
  algebraically closed `F`, the inertia degree equals 1.
- **How**: Rewrites `Ideal.inertiaDeg` via `Ideal.inertiaDeg_algebraMap` (Mathlib), then uses
  `residueLinearEquiv.finrank_eq` to transport `finrank_self = 1` from `C₂.CR ⧸ Q` to
  `C₁.CR ⧸ P` without needing `Module.Finite`.
- **Hypotheses**: Same as `residueLinearEquiv`.
- **Uses from project**: `CurveMap.CoordHom.residueLinearEquiv` (L208)
- **Used by**: `CurveMap.CoordHom.ef_one_of_ram_one_and_algClosed` (L257)
- **Visibility**: public
- **Lines**: 187–210 (proof 24 lines)
- **Notes**: None.

---

### `theorem CurveMap.CoordHom.ef_one_of_ram_one_and_algClosed`

- **Type**: `[IsAlgClosed F] → φ → coordHom → hQ : Q.IsMaximal → hP : P.IsMaximal → hLies → hRamOne : ramificationIdx ... Q P = 1 → hScalarTower → ramificationIdx ... Q P * inertiaDeg Q P = 1`
- **What**: Atomic per-prime witness: combines a ramification = 1 hypothesis with the
  inertia = 1 conclusion to give `e * f = 1`.
- **How**: Derives `f = 1` from `inertiaDeg_eq_one_of_isAlgClosed`, rewrites with `hRamOne`
  and `h_f`, then closes with `one_mul`.
- **Hypotheses**: `F` algebraically closed; `P` lies over `Q`; ramification index = 1 (supplied);
  scalar tower hypothesis.
- **Uses from project**: `CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed` (L257)
- **Used by**: `CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional` (L393)
- **Visibility**: public
- **Lines**: 234–258 (proof 5 lines)
- **Notes**: None.

---

### `noncomputable def _root_.IsDedekindDomain.HeightOneSpectrum.under`

- **Type**: `{A B : Type*} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] → (P : HeightOneSpectrum B) → HeightOneSpectrum A`
- **What**: Contracts a height-one prime of `B` to a height-one prime of `A` via the
  algebra map's comap, provided `A` is nontrivial, `B` is a domain, and `B` is integral
  over `A`.
- **How**: Sets `asIdeal := P.asIdeal.under A`, proves it is prime via
  `Ideal.IsPrime.under A P.asIdeal`, and non-bottom via `Ideal.under_ne_bot A P.ne_bot`.
- **Hypotheses**: `A` nontrivial, `B` domain, `B` integral over `A`.
- **Uses from project**: none (pure Mathlib)
- **Used by**: `CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional`
  (L345, L374, L377)
- **Visibility**: public (`_root_`)
- **Lines**: 278–285 (body 3 lines)
- **Notes**: Placed in `_root_` namespace. Likely a mathlib duplication candidate or near-
  duplicate of Mathlib's `IsDedekindDomain.HeightOneSpectrum.comap`.

---

### `theorem CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional`

- **Type**: `[IsAlgClosed F] [C₂.toAffine.IsElliptic] [IsIntegrallyClosed C₂.CR] [IsIntegrallyClosed C₁.CR] → φ : CurveMap C₁ C₂ → coordHom : φ.CoordHom → hfin → hfinFF → hsep → htorsion → hfaithful → hessfin → hsepFF → ∃ Q : HeightOneSpectrum C₂.CR, (primesOverFinset Q.asIdeal C₁.CR).card = φ.separableDegree`
- **What**: Unconditional form of T-II-2-009: for a separable `CurveMap` with `CoordHom`
  pullback over algebraically closed `F`, there exists a height-one prime `Q` in `C₂` whose
  fiber cardinality in `C₁` equals `φ.separableDegree`.
- **How**: (1) Obtains finiteness of the bad (ramified) prime locus via
  `IsDedekindDomain.finite_ramified_primes`; (2) uses `C₂.heightOneSpectrum_infinite` to find
  a good `Q` not in the contracted bad locus (by contradiction + `Set.Finite.image`); (3)
  for each `P` above `Q`, uses `IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal` +
  `ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot` to get `e = 1`, then
  `ef_one_of_ram_one_and_algClosed` (with scalar tower from
  `Ideal.Quotient.isScalarTower_of_liesOver`) for `e * f = 1`; (4) applies
  `φ.exists_heightOneSpectrum_fiber_card_eq_sepDegree` from `GenericFiber.lean`.
- **Hypotheses**: `F` algebraically closed, `C₂` elliptic, both coordinate rings integrally
  closed, `φ` separable with module-finite/torsion-free/faithful/essentially-finite-type
  `CoordHom`, fraction-field algebra separable.
- **Uses from project**: `IsDedekindDomain.HeightOneSpectrum.under` (L345, L374, L377),
  `SmoothPlaneCurve.heightOneSpectrum_infinite` (L341, from `GenericFiber.lean`),
  `IsDedekindDomain.finite_ramified_primes` (L337, from `GenericFiber.lean`),
  `IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal` (L380, from `GenericFiber.lean`),
  `IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot` (L383, from `GenericFiber.lean`),
  `CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree` (L360, from `GenericFiber.lean`),
  `CurveMap.CoordHom.ef_one_of_ram_one_and_algClosed` (L393)
- **Used by**: unused in file (terminal theorem)
- **Visibility**: public
- **Lines**: 293–395 (proof 103 lines)
- **Notes**: `set_option maxHeartbeats 2000000` and `set_option synthInstance.maxHeartbeats 400000`
  at L287–288 with NO justifying comment. Proof is 103 lines (well over 30-line threshold).
  The file is not imported by any other Lean file in the project (only mentioned in comments).

---

## Summary

| Kind | Count |
|------|-------|
| noncomputable def | 5 |
| theorem / @[simp] theorem | 5 |
| instance | 0 |
| **Total** | **10** |

**Sorries**: none.

**Long proofs** (>30 lines): `residueLinearEquiv` (33 lines), `exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional` (103 lines).

**set_option maxHeartbeats**: line 287–288; value 2000000 (synthInstance 400000); NO comment.

**Unused in file**: `residueFieldsAlgEquiv`, `exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional`.

**keyApi** (used by 3+ others in this file): none reach the threshold.
