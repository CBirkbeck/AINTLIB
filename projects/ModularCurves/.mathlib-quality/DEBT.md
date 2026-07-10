
## DS-HOPF-1 (2026-07-10, NEW-HOPF): flat_coinvariants instance-key plumbing
`HopfGaloisTheorem.lean`, `flat_coinvariants` — single sorry. Math complete
(`flat_of_forall_flat_extension` + `free_baseChange_of_surjective_galoisPrecursor`
both proven); blocker is aligning the `IsScalarTower C (Localization.AtPrime P)
(LocalPolynomialExtension _)` family's SMul-instance keys between the abstract
glue's frozen binder-keys and the consumer's constructible
`of_algebraMap_eq`-form (Ore-generic SMul vs `Algebra.toSMul`). Next probes:
(a) defeq-test Ore-key vs toSMul-key; (b) haveI-reseed at consumer with
glue-frozen keys via `fun P _ => by exact ...`; (c) if stuck: quantify the
localization family abstractly in the glue too.

## DS-HOPF-1 (2026-07-10, NEW-HOPF): flat_coinvariants instance-key plumbing
`HopfGaloisTheorem.lean`, `flat_coinvariants` — single sorry. Math complete
(`flat_of_forall_flat_extension` + `free_baseChange_of_surjective_galoisPrecursor`
both proven); blocker is aligning the `IsScalarTower C (Localization.AtPrime P)
(LocalPolynomialExtension _)` family's SMul-instance keys between the abstract
glue's frozen binder-keys and the consumer's constructible
`of_algebraMap_eq`-form (Ore-generic SMul vs `Algebra.toSMul`). Next probes:
(a) defeq-test Ore-key vs toSMul-key; (b) haveI-reseed at consumer with
glue-frozen keys via `fun P _ => by exact ...`; (c) if stuck: quantify the
localization family abstractly in the glue too.
