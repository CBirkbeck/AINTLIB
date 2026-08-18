# Vendored: riemann-roch-function-fields

Source: https://github.com/vaca22/riemann-roch-function-fields (Apache-2.0, author Guanghao Li, 2026).
Vendored 2026-08-07 at the tip of `main` (mathlib v4.31.0), module paths rewritten
`RiemannRoch.*` → `ModularCurves.Vendored.RiemannRoch.*`, then bump-repaired to this workspace's
toolchain/mathlib. Original LICENSE preserved as `LICENSE.vendored`; per-file Apache headers untouched.
Consumed by `AP2-A1` (degree-one fibre cohomology): `riemann_roch` + `genus_eq_one` +
`zero_isCanonical_of_genus_eq_one` + `DegreeOneDictionary`.
