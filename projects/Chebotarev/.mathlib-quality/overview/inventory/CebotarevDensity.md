# Inventory: `CebotarevDensity.lean`

**Path**: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/Chebotarev/CebotarevDensity.lean`
**Lines**: 44 total.

## Declarations

**None.** This file is a pure top-level **module aggregator**. It contains only:

- `module` marker (line 1).
- 15 `public import` statements (lines 3–16) re-exporting the project's submodules:
  - `CebotarevDensity.Density`
  - `CebotarevDensity.CyclotomicNormResidue`
  - `CebotarevDensity.ForMathlib.CharacterOrthogonality`
  - `CebotarevDensity.ForMathlib.IdealCongruenceCount`
  - `CebotarevDensity.ForMathlib.LatticePointCount`
  - `CebotarevDensity.ForMathlib.LogOneDivSubOne`
  - `CebotarevDensity.ForMathlib.NormLeOneLipschitz`
  - `CebotarevDensity.FixedFieldDensity`
  - `CebotarevDensity.Frobenius`
  - `CebotarevDensity.ZetaProduct`
  - `CebotarevDensity.Cyclotomic`
  - `CebotarevDensity.Abelian`
  - `CebotarevDensity.Main`
  - `CebotarevDensity.NumberFieldEulerProduct`
- A module docstring (lines 18–44) describing the Chebotarev density theorem (conjugacy-class form, finite Galois extension of number fields), citing Sharifi *Algebraic Number Theory* §7.1–7.2 and the Stevenhagen–Lenstra appendix, and giving the module map. The main result `Chebotarev.chebotarev_density` lives in `CebotarevDensity.Main`, **not** in this file.

No `def`, `lemma`, `theorem`, `instance`, `structure`, `class`, `abbrev`, or `inductive` is declared here.

## File Summary

- **Total decls**: 0 (defs: 0 / lemmas+theorems: 0 / instances: 0).
- **Key API (used by ≥3 in-file)**: none — file has no declarations.
- **Unused decls**: none.
- **Decls with `sorry`**: none.
- **Decls with `set_option`**: none.
- **Proofs >50 lines (decompose-needed)**: none.
- **Proofs 30–50 lines**: none.
- **Role**: top-level umbrella file aggregating 15 submodules via `public import`. All actual Chebotarev declarations reside in the imported `CebotarevDensity/` modules (chiefly `Main`, `Abelian`, `Cyclotomic`, `ZetaProduct`, `Frobenius`, `Density`); inventory those files separately.
