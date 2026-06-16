# Development Plan: DUAL-DESCENT — the dual isogeny over the base field (symmetry of isogeny)

*Created 2026-06-17, dev/hasse-weil. Source reading (Silverman III.4.10–4.12, III.6.1–2) + project
dual-machinery audit + mathlib descent search done this session.*

## Goal

Discharge **`UniversalDualWitness F`** for a general perfect field `F` (the case that matters:
`ℚ` / characteristic 0): *every isogeny `φ : E₁ → E₂` over `F` has an `F`-rational dual*. This is
exactly **symmetry of `IsIsogenous`** over `F`, hence makes `IsogenyClass` an unconditional
equivalence relation/quotient and discharges the gate carried by the LMFDB label layer
(`IsogenyClassLabel.lean`).

Headline Lean target (the deliverable):
```
theorem universalDualWitness_of_charZero (F) [Field F] [DecidableEq F] [CharZero F] :
    UniversalDualWitness F
```
(char 0 ⟹ every isogeny separable ⟹ the Frobenius/inseparable case of Silverman III.6.1 never
arises; char 0 ⟹ `F` perfect. A `PerfectField`/separable-hypothesis variant is the natural
generalization but char 0 is the target and keeps the statement clean.)

## What Silverman actually proves (III.6.1) — the route this plan transcribes

- **Over `ℚ` (char 0) the dual is purely III.4.11.** `#ker φ = deg φ` (III.4.10c) ⟹ every kernel
  point has order dividing `m = deg φ` (Lagrange) ⟹ `ker φ ⊆ E₁[m] = ker[m]` ⟹ III.4.11 factors
  `[m]` through `φ`, and the factor **is** `φ̂`. No Frobenius/Verschiebung case (char 0).
- **III.4.11 is irreducibly a `K̄`-Galois argument** (Silverman p.74, verbatim: *"Since φ is
  separable, (III.4.10c) says that K̄(E₁) is a Galois extension of φ\*K̄(E₂). Then … every element
  of Gal(K̄(E₁)/φ\*K̄(E₂)) fixes ψ\*K̄(E₃) … by Galois theory there are field inclusions
  ψ\*K̄(E₃) ⊂ φ\*K̄(E₂) ⊂ K̄(E₁). Now (II.2.4b) gives a map λ …"*). The normality that makes it
  Galois is **automatic only over K̄** — the kernel translations `τ_T` (over *all* `K̄`-points of
  `ker φ`) realize the whole Galois group (III.4.10b). Over non-closed `F`, `F(E₁)/φ\*F(E₂)` need
  **not** be normal, so the argument does **not** run over `F` directly.
- **The dual is `F`-rational by an implicit descent.** Silverman never writes it (footnote 1, p.83:
  the standing *perfect-field* assumption). The argument: `φ̂` is the *unique* map with `φ̂∘φ=[m]`
  (III.6.1a, uniqueness via II.2.3 cancellation); for `σ ∈ Gal(K̄/F)`, `φ̂^σ ∘ φ = [m]^σ = [m]`
  (φ, [m] are `F`-rational), so `φ̂^σ = φ̂`, i.e. `φ̂` is Galois-invariant ⟹ defined over `F`
  (`F` perfect).

**So the formalization route = Silverman's actual route:** build `φ̂` over `K̄ = AlgebraicClosure F`
(we have this), then **descend it to `F` by uniqueness + Galois-invariance** (the new infrastructure).

## Mathlib + project inventory

| Piece | Status | Use |
|---|---|---|
| dual over `K̄` (alg. closed): `exists_dual_of_pullbackEvaluation_general` (KernelCountGeneral.lean:260) | HAVE (`[IsAlgClosed F]`) | step over `K̄`; pattern already used at `OneSubPullbackEvaluation.lean:374` |
| base-change `F → K̄`: `baseChangeIsogeny` + `baseChangeCoordHom` (BaseChange.lean:407/535) | HAVE (target `[IsAlgClosed L]`) | get `φ_K̄` + its CoordHom ⟹ `PullbackEvaluation` ⟹ K̄ dual |
| `factorThrough` (III.4.11 algebraic core) | HAVE, field-general (Dual.lean:81) | the factor map once the range inclusion holds |
| `hbase`/`reflects_ordAtInfty`, `hν` (`mulByIntBasepoint`) | HAVE, field-general | the non-`hincl` `HasDualWitness` fields are free |
| uniqueness of the dual (`compose_right_cancel`, II.2.3) | HAVE (CanonicalDual.lean) | DUAL-Q3 (Galois-invariance from uniqueness) |
| **Galois descent of an isogeny / CurveMap `K̄ → F`** | **MISSING — the crux** | DUAL-Q2 |
| mathlib `RingTheory/Flat/FaithfullyFlat/Descent.lean` | HAVE | a descent primitive for DUAL-Q2 |
| mathlib finite-Galois `fixedField`/`fixedField_top`/Krull topology (FieldTheory/Galois/Basic.lean, KrullTopology.lean) | HAVE | the fixed-field side of DUAL-Q1/Q2 |
| `IsogenyClassLabel` gate consumer | HAVE (this session) | DUAL-Q4 payoff |

**Decisive design choice — descend at a FINITE level.** `φ̂_K̄` is a finite amount of data, so it is
defined over a *finite* subextension `L/F` with `L/F` Galois; descent runs along the **finite**
`Gal(L/F)` (mathlib's `fixedField`/`IsGalois`/`FiniteDimensional` machinery), NOT the infinite
`Gal(K̄/F)`. This dodges Krull-topology / profinite descent and lands on mathlib's finite-Galois +
faithfully-flat-descent primitives.

## Decomposition (mirrors Silverman's implicit descent; DUAL-Q2 is the deep API gap)

- **DUAL-Q1 — the Galois action + fixed field.** For `E/F` with `K̄ = AlgebraicClosure F` (or a
  finite Galois `L/F`), the function field `K̄(E_K̄) = K̄ ⊗_F F(E)` (E geometrically integral over
  the perfect `F`), with the `Gal(K̄/F)`-action through the `K̄`-factor and **fixed field `F(E)`**.
  Sub-leaves: (a) the tensor identification `K̄(E_K̄) ≅ K̄ ⊗_F F(E)` (the project's
  `functionField_baseChange_tensorEquiv`, CurveMapBaseChange.lean:645 — HAVE); (b) the Galois action
  on `K̄ ⊗_F F(E)` via `Algebra.TensorProduct.map σ id`; (c) fixed field = `F(E)` (faithfully-flat /
  Galois descent of the tensor, mathlib `FaithfullyFlat/Descent.lean` + `fixedField`).
- **DUAL-Q2 — the descent principle (CRUX, API GAP).** A `Gal(L/F)`-equivariant `K̄`-algebra hom
  `ξ : K̄(E₂_K̄) → K̄(E₁_K̄)` restricts to its fixed fields, giving an `F`-algebra hom
  `F(E₂) → F(E₁)`; with the basepoint condition this is the pullback of an `EC.Isogeny` over `F`
  (II.2.4b at the `CurveMap` level). **This is new AG infrastructure.** Sub-leaves: (a) equivariant
  ⟹ preserves fixed subfields ⟹ restricts (mathlib `AlgHom`-on-fixedField); (b) the restricted hom
  is nonconstant / transcendence-degree-preserving ⟹ a `CurveMap` over `F` (basepoint via
  `reflects_ordAtInfty`); (c) the base-change of the descended map recovers `ξ` (round-trip).
  **Feasibility: the genuine wall.** mathlib has the descent *primitives* (faithfully-flat descent,
  finite-Galois fixed fields) but **no `CurveMap`/isogeny descent**; wiring is multi-hundred LOC and
  the round-trip (c) is fiddly. Honest classification: deep API gap, possibly `/expert-review`.
- **DUAL-Q3 — `φ̂_K̄` is Galois-equivariant.** From uniqueness: `φ̂_K̄^σ ∘ φ_K̄ = [m]_K̄` (φ, [m]
  are `F`-rational so `σ`-fixed under base change), and the dual over `K̄` is unique
  (`compose_right_cancel` / II.2.3), so `φ̂_K̄^σ = φ̂_K̄`. Leaf — composes HAVE pieces, modulo the
  Galois action on isogenies from Q1.
- **DUAL-Q4 — assembly.** base-change `φ` (HAVE) → `φ̂_K̄` over `K̄` (HAVE) → Q3 equivariance →
  Q2 descent to `φ̂` over `F` → it satisfies `φ̂∘φ=[m]` (round-trip Q2c + base-change faithful) →
  `HasDualWitness φ` → `UniversalDualWitness F` → `IsIsogenous.symm` → discharge the
  `IsogenyClassLabel` gate (drop `hw` from `index_unique`/`classLetter_eq_of_isogenous`).

## Generality

`[CharZero F]` for the headline (⟹ separable, ⟹ perfect; the target is ℚ). The descent
infrastructure (Q1/Q2) should be stated over a perfect field `F` with its algebraic/separable
closure where possible (reusable beyond char 0). `[DecidableEq F]` as the project's `Affine`/
`IsElliptic` layer requires.

## Honest feasibility verdict

The route is Silverman-faithful and the math is standard, but **DUAL-Q2 is genuine new
algebraic-geometry infrastructure** (Galois descent of a curve morphism), only *partially* supported
by mathlib (descent primitives yes; `CurveMap` descent no). This is the single largest remaining
piece in the project — realistically a multi-stage development, with Q2 the deep crux. Per AINTLIB
norms, the scaffold + tractable leaves (Q1 setup, Q3, Q4-assembly-modulo-Q2) go in now with `sorry`
at Q2's deep sub-leaves; Q2 may warrant an `/expert-review` question on the cleanest finite-Galois
descent formulation for function-field morphisms. **This is not a quick win — it is the proper,
honest path, and it is worth doing because it is the one thing standing between us and unconditional
isogeny symmetry (hence unconditional LMFDB isogeny-class labels).**
