
## DS-HOPF-1 (2026-07-10, NEW-HOPF): RESOLVED same-day — flat_coinvariants instance-key plumbing
`HopfGaloisTheorem.lean`, `flat_coinvariants` — single sorry. Math complete
(`flat_of_forall_flat_extension` + `free_baseChange_of_surjective_galoisPrecursor`
both proven); blocker is aligning the `IsScalarTower C (Localization.AtPrime P)
(LocalPolynomialExtension _)` family's SMul-instance keys between the abstract
glue's frozen binder-keys and the consumer's constructible
`of_algebraMap_eq`-form (Ore-generic SMul vs `Algebra.toSMul`). Next probes:
(a) defeq-test Ore-key vs toSMul-key; (b) haveI-reseed at consumer with
glue-frozen keys via `fun P _ => by exact ...`; (c) if stuck: quantify the
localization family abstractly in the glue too.

## DS-HOPF-1 (2026-07-10, NEW-HOPF): RESOLVED same-day — flat_coinvariants instance-key plumbing
`HopfGaloisTheorem.lean`, `flat_coinvariants` — single sorry. Math complete
(`flat_of_forall_flat_extension` + `free_baseChange_of_surjective_galoisPrecursor`
both proven); blocker is aligning the `IsScalarTower C (Localization.AtPrime P)
(LocalPolynomialExtension _)` family's SMul-instance keys between the abstract
glue's frozen binder-keys and the consumer's constructible
`of_algebraMap_eq`-form (Ore-generic SMul vs `Algebra.toSMul`). Next probes:
(a) defeq-test Ore-key vs toSMul-key; (b) haveI-reseed at consumer with
glue-frozen keys via `fun P _ => by exact ...`; (c) if stuck: quantify the
localization family abstractly in the glue too.

DS-HOPF-1 RESOLUTION: split the glue — `flat_of_forall_flat_localized` (family-form,
Localization-canonical instances only) + `flat_localized_of_flat_extension` (single-P,
abstract E) — all expensive E-instances consumed at single-P sites where ambient
synthesis works (post `Subalgebra.instSMulSubtypeMem`-erasure). No sorry remains.

## DS4-ROUTE-BETA (2026-08-04): proved-but-unconsumed dead branch — post-merge dedup
Route β (descend the determinant model from a full-level cover) was built end to end and is
**axiom-verified**, but the route is **unsourced** and has been retired
(`.mathlib-quality/decomposition.md`). Its top results are **consumed nowhere outside their own
files**: `nonempty_weilPairing_of_cover_of_values`, `nonempty_weilPairing_of_fullLevel`,
`coverPairing`, `coverTriv`, `coverTrivReading`, `fullLevelPairing` + its det laws
(`WeilPairing/FullLevelPairing.lean`), and the supporting
`WeilPairing/{FactorRoot,FieldPairingValue,TorsionSqBaseChange,RootPowerPoints,ConstReading,
PairingTransport,DetCocycle}.lean`, `GroupScheme/{ConstSchemeSquare,LevelCoord}.lean`,
`ForMathlib/FactorIntegrallyClosed.lean`.

Not a blocker (no `sorry`), so **not** fleet-eligible as WIP — it is dedup/dead-code debt for
`/cleanup` once this branch merges to `main`. Worth keeping regardless of the route:
`constSchemeSigmaIso`, `levelCoord` + `eq_glSmul_of_levelCoord`,
`fullLevelHom_eq_constSchemeMap_comp`, `torsionSqBaseChangeIso`, `muNPointsEquiv_rootPower`,
`isIntegrallyClosed_quotient_minimalPrime` — all general-purpose. Also widened this window and
independently useful: `ΓSpecIso_hom_appTop_specMap_comp` (now `φ : R ⟶ R'`, was `R ⟶ R`).

## KM-SEESAW-DEDUP (2026-08-05): RESOLVED same-day — relocated, not duplicated
`ForMathlib/Seesaw.lean` needs the scalar tower `Γ(S,⊤) → κ(s) → K` for a field-valued point of an
affine `S`. It is **already proved** in the tree as the `private` pair `affineFieldFactor_isScalarTower`
/ `affineFieldFactor_residue_isScalarTower` (`EllipticCurve/PoleSheafBaseCechHigher.lean:55,84`) — pure
affine-scheme infrastructure, zero elliptic-curve content, made unreachable only by `private`.
**RESOLUTION (done):** both lemmas moved verbatim to the new public
`ForMathlib/AffineFieldPointTower.lean` (134 lines, no elliptic-curve content), `private` dropped;
`PoleSheafBaseCechHigher.lean` now imports it and still builds; `Seesaw.lean` cites it directly and its
stub leaf is gone. No proof body was copied.
