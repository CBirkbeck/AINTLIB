# Inventory: ./HasseWeil/WeilPairing/Representation.lean

**File purpose**: Builds the mod-`ℓ` matrix representation `ρ_ℓ : End(E) → M₂(ZMod ℓ)` (Silverman III.7–8) on the `2`-dimensional `ZMod ℓ`-vector space `E[ℓ]`. For any additive endomorphism `ψ : E.Point →+ E.Point` (every isogeny — Frobenius, `[n]` — is one): restrict `ψ` to `E[ℓ]` as a `ZMod ℓ`-linear map (`torsionRestrict`), then take its matrix in the chosen `Fin 2`-basis (`rhoEll`). Provides the ring-hom-style identities (`map_mul`/`map_one`/`map_add`/scalar values) and the `det`/`trace` bridges to the basis-free linear-map invariants.

**Imports**: `HasseWeil.WeilPairing.TorsionModule`, `Mathlib.LinearAlgebra.Matrix.ToLin`, `Mathlib.LinearAlgebra.Determinant`, `Mathlib.LinearAlgebra.Trace`

**Namespace**: `HasseWeil.WeilPairing.TorsionGeometric` (re-opens `HasseWeil`). **Section variables**: `{F}[Field F][DecidableEq F](W)[IsElliptic](ℓ:ℕ)[Fact ℓ.Prime][IsAlgClosed F](hℓF:(ℓ:F)≠0)`. Sections: `TorsionRestrict` (`omit [IsAlgClosed F]`), `Rho`, `DetTrace`.

**Total declarations**: 15 (3 `noncomputable def`, 12 `theorem`, of which 2 `@[simp]`). **No `sorry`, no `set_option`.**

> **Live-path note**: Only **4** of the 15 declarations are on the live Hasse-bound path (consumed by `DetDeg.lean`, the matrix-determinant endgame): the two `def`s `torsionRestrict` and `rhoEll`, plus the lemmas `rhoEll_det` and `rhoEll_id`. The other 11 are either internal scaffolding for those four (`map_mem_torsion_ell`, `torsionRestrictHom`, `torsionRestrict_apply`) or are referenced **only by `RepresentationAxiomCheck.lean`** — a `#print axioms` audit file, not a proof. In particular the multiplicativity/additivity/scalar/trace API (`rhoEll_comp`, `rhoEll_add`, `rhoEll_mulByInt`, `rhoEll_zsmulAddGroupHom`, `rhoEll_trace`, and the `torsionRestrict_{comp,id,add,zsmul}` lemmas) is **not used by any live proof**; `DetDeg.lean` re-proves the scaling/subtraction variants it needs (`rhoEll_sub`, `rhoEll_zsmul`, `one_sub_rhoEll`, `smul_rhoEll_sub`) directly from `rhoEll`. So this file is *partially superseded*: its representation-ring API was built out in full (anticipating a trace-based endgame) but the shipped proof routes through determinants only.

---

## Declarations

### `theorem map_mem_torsion_ell`  (internal)
- **What**: An additive endo `ψ` preserves `E[ℓ]`: `ℓ•P=0 ⟹ ℓ•(ψP)=0`.
- **How**: `ℓ•ψP = ψ(ℓ•P) = ψ0 = 0` via `map_zsmul` and `mem_torsionSubgroup`.
- **Hypotheses**: `omit hℓ`, `omit [IsAlgClosed F]`; `(ψ)`, `hP:P∈E[ℓ]`.
- **Uses from project**: `mem_torsionSubgroup`, `torsionSubgroup`.
- **Used by (in file)**: `torsionRestrictHom`. **External**: none.
- **Visibility**: public (helper). **Lines**: 63–67.

### `noncomputable def torsionRestrictHom`  (internal)
- **What**: The restriction of `ψ` to `E[ℓ]` as an `AddMonoidHom E[ℓ] →+ E[ℓ]`.
- **How**: `(ψ.comp subtype).codRestrict _ (map_mem_torsion_ell …)`.
- **Uses from project**: `map_mem_torsion_ell`.
- **Used by (in file)**: `torsionRestrictHom_coe`, `torsionRestrict`. **External**: none.
- **Visibility**: public. **Lines**: 74–77.

### `@[simp] theorem torsionRestrictHom_coe`  (internal, unused)
- **What**: `(torsionRestrictHom W ℓ ψ P : E.Point) = ψ P`.
- **How**: `rfl`. **Hypotheses**: `omit hℓ`.
- **Used by**: nothing (no internal or external reference). **Visibility**: public `@[simp]`. **Lines**: 80–82.

### `noncomputable def torsionRestrict`  ★ live API
- **What**: The `ZMod ℓ`-**linear** restriction `E[ℓ] →ₗ[ZMod ℓ] E[ℓ]` of `ψ`.
- **How**: `(torsionRestrictHom W ℓ ψ).toZModLinearMap ℓ` — linearity is automatic because the `ZMod ℓ`-action on `E[ℓ]` is the natural-number `•`, with which every `AddMonoidHom` commutes (`ZMod.map_smul`, internal to `toZModLinearMap`).
- **Uses from project**: `torsionRestrictHom`.
- **Used by (in file)**: `torsionRestrict_apply/comp/id/add/zsmul`, `rhoEll`. **External**: `DetDeg.lean` (the pairing-scaling and det-degree proofs apply `torsionRestrict ψ` to torsion points directly).
- **Visibility**: public. **Lines**: 88–90.

### `@[simp] theorem torsionRestrict_apply`  (unused beyond simp)
- **What**: `(torsionRestrict W ℓ ψ P : E.Point) = ψ P`. **How**: `rfl`.
- **Used by**: nothing by name (a `simp` lemma; no explicit reference). **Visibility**: public `@[simp]`. **Lines**: 92–94.

### `theorem torsionRestrict_comp` / `torsionRestrict_id` / `torsionRestrict_add`
- **What**: `torsionRestrict` respects composition / identity / addition of the underlying `ψ`.
- **How**: `ext P; rfl` each (the coercion is definitional).
- **Uses from project**: `torsionRestrict`.
- **Used by (in file)**: `rhoEll_comp` / `rhoEll_id` / `rhoEll_add` respectively. **External**: none.
- **Visibility**: public. **Lines**: 97–110. **NOTE**: live externally only through `rhoEll_id` (the others' `rhoEll_*` consumers are axiom-check-only).

### `theorem torsionRestrict_zsmul`
- **What**: `torsionRestrict (zsmulAddGroupHom n) = (n : ZMod ℓ) • id` — multiplication-by-`n` restricts to the scalar `(n:ZMod ℓ)`.
- **How**: `LinearMap.ext`; `(n:ZMod ℓ)•P = n•P` on a `ZMod ℓ`-module via `Int.cast_smul_eq_zsmul`, then `rfl`.
- **Uses from project**: `torsionRestrict`, `zsmulAddGroupHom`.
- **Used by (in file)**: `rhoEll_zsmulAddGroupHom`. **External**: `RepresentationAxiomCheck.lean` only.
- **Visibility**: public. **Lines**: 115–121.

### `noncomputable def rhoEll`  ★ live API
- **What**: The matrix `ρ_ℓ(ψ) ∈ M₂(ZMod ℓ)` of `torsionRestrict ψ` in the basis `torsion_ell_basis`.
- **How**: `LinearMap.toMatrix (torsion_ell_basis …) (torsion_ell_basis …) (torsionRestrict W ℓ ψ)`.
- **Uses from project**: `torsion_ell_basis` (`TorsionModule.lean`), `torsionRestrict`.
- **Used by (in file)**: all `rhoEll_*`. **External**: `DetDeg.lean` (`rhoEll_det`, `rhoEll_sub`, `rhoEll_zsmul`, `one_sub_rhoEll`, `smul_rhoEll_sub`, `frob_det_data_of_weil_scaling` — i.e. **this is the live Frobenius `Matrix (Fin 2)(Fin 2)(ZMod ℓ)` object**).
- **Visibility**: public. **Lines**: 130–133.

### `theorem rhoEll_comp` (`map_mul`)
- **What**: `ρ_ℓ(ψ₁∘ψ₂) = ρ_ℓ(ψ₁)·ρ_ℓ(ψ₂)`. **How**: `torsionRestrict_comp` + `LinearMap.toMatrix_comp`.
- **Uses from project**: `rhoEll`, `torsionRestrict_comp`, `torsion_ell_basis`.
- **Used by**: `RepresentationAxiomCheck.lean` only. **Visibility**: public. **Lines**: 137–141. **NOT on live path.**

### `theorem rhoEll_id` (`map_one`)  ★ live API
- **What**: `ρ_ℓ(id) = 1`. **How**: `torsionRestrict_id` + `LinearMap.toMatrix_id`.
- **Uses from project**: `rhoEll`, `torsionRestrict_id`, `torsion_ell_basis`.
- **Used by (in file)**: none. **External**: `DetDeg.lean` (`one_sub_rhoEll`, `smul_rhoEll_sub`).
- **Visibility**: public. **Lines**: 145–147.

### `theorem rhoEll_add` (`map_add`)
- **What**: `ρ_ℓ(ψ₁+ψ₂)=ρ_ℓ(ψ₁)+ρ_ℓ(ψ₂)`. **How**: `torsionRestrict_add` + `map_add` (`LinearMap.toMatrix` is a `LinearEquiv`).
- **Used by**: `RepresentationAxiomCheck.lean` only. **Visibility**: public. **Lines**: 151–154. **NOT on live path** (DetDeg re-proves `rhoEll_sub` from scratch via `ext P; rfl` + `map_sub`).

### `theorem rhoEll_zsmulAddGroupHom`
- **What**: `ρ_ℓ(zsmulAddGroupHom n) = (n:ZMod ℓ)•1` (scalar matrices). **How**: `torsionRestrict_zsmul` + `map_smul` + `LinearMap.toMatrix_id`.
- **Used by (in file)**: `rhoEll_mulByInt`. **External**: `RepresentationAxiomCheck.lean` only. **Visibility**: public. **Lines**: 160–162.

### `theorem rhoEll_mulByInt`
- **What**: `ρ_ℓ((mulByInt W n).toAddMonoidHom) = (n:ZMod ℓ)•1`. **How**: its point map is `zsmulAddGroupHom n`, so = `rhoEll_zsmulAddGroupHom`.
- **Uses from project**: `rhoEll_zsmulAddGroupHom`, `mulByInt`.
- **Used by**: `RepresentationAxiomCheck.lean` only. **Visibility**: public. **Lines**: 166–168. **NOT on live path.**

### `theorem rhoEll_det`  ★ live API
- **What**: `det(ρ_ℓ(ψ)) = LinearMap.det (torsionRestrict ψ)` — the matrix det equals the basis-free linear-map det.
- **How**: `LinearMap.det_toMatrix (torsion_ell_basis …) (torsionRestrict …)`.
- **Uses from project**: `rhoEll`, `torsionRestrict`, `torsion_ell_basis`.
- **Used by (external)**: `DetDeg.lean` — **`det_rhoEll_eq_degree` rewrites with this; it is the single bridge that turns `deg ψ` into `det M` for the Frobenius matrix.** The most load-bearing lemma in the file.
- **Visibility**: public. **Lines**: 178–180.

### `theorem rhoEll_trace`
- **What**: `trace(ρ_ℓ(ψ)) = LinearMap.trace (ZMod ℓ) E[ℓ] (torsionRestrict ψ)`. **How**: `(LinearMap.trace_eq_matrix_trace …).symm`.
- **Uses from project**: `rhoEll`, `torsionRestrict`, `torsion_ell_basis`.
- **Used by**: `RepresentationAxiomCheck.lean` only. **Visibility**: public. **Lines**: 185–189. **NOT on live path** — the shipped Hasse argument uses determinants (`det M = q`, `det(1−M) = #E(𝔽_q)`, `det(rM−s1)`), not the trace.

---

## File Summary

**Role in cluster**: The **matrix layer** — converts the `ZMod ℓ`-vector-space `E[ℓ]` into a concrete `Matrix (Fin 2)(Fin 2)(ZMod ℓ)` representation `rhoEll` of endomorphisms, with the determinant bridge `rhoEll_det` that the Hasse endgame consumes. This is the cluster's terminal output toward `FrobMatrixData`/`HasseAssembly`.

**Live spine (4 of 15 decls)**: `torsionRestrict` → `rhoEll` → {`rhoEll_det`, `rhoEll_id`}, all consumed by `DetDeg.lean`. (Plus the internal scaffolding `map_mem_torsion_ell`, `torsionRestrictHom`, `torsionRestrict_id` feeding those.)

**Cleanup findings**:
- (a) **Unused-in-file**: `torsionRestrictHom_coe` and `torsionRestrict_apply` are `@[simp]` lemmas never referenced by name (kept for simp-normal-form; low value here since the coercion is `rfl`). Defensible to drop.
- (b) **Partially superseded API (the prompt's "dead" half)**: `rhoEll_comp`, `rhoEll_add`, `rhoEll_mulByInt`, `rhoEll_zsmulAddGroupHom`, `rhoEll_trace`, and `torsionRestrict_{comp,add,zsmul}` are referenced **only by the `#print axioms` audit `RepresentationAxiomCheck.lean`**, never by a proof. They were built for a (now-unused) trace-based / ring-homomorphism-based endgame; the shipped proof is determinant-only. If `RepresentationAxiomCheck.lean` is itself scaffolding, these ~7 lemmas are fully dead and could be deleted, or the file could be slimmed to the live four plus their helpers.
- (c) **Moral duplication with `DetDeg.lean`**: `DetDeg` re-derives `rhoEll_sub`, `rhoEll_zsmul`, `one_sub_rhoEll`, `smul_rhoEll_sub` itself (each `rw [rhoEll, …]` + `ext P; rfl`) rather than reusing `rhoEll_add`/`rhoEll_zsmulAddGroupHom`/`rhoEll_id` from here — so the additive/scalar API exists in two places with neither fully reused. Consolidating (have `DetDeg` import these, or move the four `DetDeg` variants here) would remove the redundancy. Note `rhoEll_id` *is* reused, so the split is inconsistent.
- (c′) **Hand-rolled vs mathlib — the modelling is good**: `rhoEll` is a genuine `LinearMap.toMatrix`, `torsionRestrict` is a genuine `ZMod ℓ`-`LinearMap` (via the idiomatic `toZModLinearMap`/`ZMod.map_smul` route), and det/trace use `LinearMap.det_toMatrix`/`trace_eq_matrix_trace`. The Frobenius action is a proper module endomorphism, not an ad-hoc matrix. **No remodelling needed** — the only issue is the unused breadth, not the design.
- (d) **Under-general**: `rhoEll` is defined on bare `AddMonoidHom`s (not `Isogeny`), which is correctly the most general input. Fine.
- **`sorry`/heartbeats**: none.
