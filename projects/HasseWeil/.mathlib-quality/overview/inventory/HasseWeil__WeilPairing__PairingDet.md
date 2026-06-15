# Inventory: ./HasseWeil/WeilPairing/PairingDet.lean

**Total lines:** 252  
**Declarations:** 11 (1 def, 10 theorems, 0 instances)  
**Sorries:** none  
**set_option maxHeartbeats:** none  

Module-level doc: "Route 2A — the Weil-pairing determinant identity (Silverman III.8.6, abstract finite-level core)." Pure linear algebra; no elliptic-curve imports beyond Mathlib.

---

## Declarations

---

### `def symJ`

- **Type**: `(F : Type*) [CommRing F] : Matrix (Fin 2) (Fin 2) F`
- **What**: Defines the standard 2×2 symplectic form matrix `J = [[0,1],[-1,0]]` over a commutative ring.
- **How**: Immediate matrix literal `!![0, 1; -1, 0]`.
- **Hypotheses**: `F` a commutative ring.
- **Uses from project**: []
- **Used by**: `transpose_mul_symJ_mul`, `det_eq_of_symplectic_adjoint`, `det_eq_of_symplectic_scaling`, `frob_det_data_of_scaling`, `det_smul_add_smul_one_eq`, `frob_det_data_of_adjoint_norm_trace`, `linearMap_det_eq_of_symplectic_scaling`, `frob_det_data_of_pairing_form`; also referenced from `Assembly.lean` and `DetDeg.lean`.
- **Visibility**: public
- **Lines**: 30 (1-line body)
- **Notes**: None.

---

### `theorem transpose_mul_symJ_mul`

- **Type**: `{F : Type*} [CommRing F] (φ : Matrix (Fin 2) (Fin 2) F) : φᵀ * symJ F * φ = φ.det • symJ F`
- **What**: The symplectic determinant identity: for any 2×2 matrix φ, `φᵀ J φ = (det φ) • J`.
- **How**: Direct computation: `fin_cases` on `i j : Fin 2`, then `simp` with `Matrix.det_fin_two` and `ring` to close each of the four entries.
- **Hypotheses**: `F` a commutative ring; `φ` an arbitrary 2×2 matrix.
- **Uses from project**: `symJ`
- **Used by**: `det_eq_of_symplectic_adjoint`, `det_eq_of_symplectic_scaling`
- **Visibility**: public
- **Lines**: 33–38 (6 lines)
- **Notes**: None.

---

### `theorem det_eq_of_symplectic_adjoint`

- **Type**: `{F : Type*} [CommRing F] {φ ψ : Matrix (Fin 2) (Fin 2) F} {d : F} (hadj : φᵀ * symJ F = symJ F * ψ) (hψφ : ψ * φ = d • 1) : φ.det = d`
- **What**: If ψ is the symplectic adjoint of φ (i.e., `φᵀ J = J ψ`) and `ψ φ = d • 1`, then `det φ = d`. This is the abstract matrix form of the adjoint + norm route to Silverman III.8.6.
- **How**: Chains `hadj` and `hψφ` to show `φᵀ J φ = d • J`; then applies `transpose_mul_symJ_mul` to get `(det φ) • J = d • J`; extracts the `(0,1)` entry to separate the scalars, closing by `simpa [symJ, Matrix.smul_apply]`.
- **Hypotheses**: `F` a commutative ring; φ has symplectic adjoint ψ (`hadj`); norm identity `hψφ`.
- **Uses from project**: `symJ`, `transpose_mul_symJ_mul`
- **Used by**: `det_smul_add_smul_one_eq`
- **Visibility**: public
- **Lines**: 43–52 (10 lines)
- **Notes**: None.

---

### `theorem det_eq_of_symplectic_scaling`

- **Type**: `{F : Type*} [CommRing F] {φ : Matrix (Fin 2) (Fin 2) F} {d : F} (hscale : φᵀ * symJ F * φ = d • symJ F) : φ.det = d`
- **What**: If the symplectic scaling `φᵀ J φ = d • J` holds, then `det φ = d`. This is the "additivity-free" form of Prop 8.6: each isogeny individually, no dual/adjoint needed.
- **How**: Rewrites `hscale` using `transpose_mul_symJ_mul` to get `(det φ) • J = d • J`, then extracts the `(0,1)` entry via `congrFun` and closes with `simpa [symJ, Matrix.smul_apply]`.
- **Hypotheses**: `F` a commutative ring; scaling hypothesis `hscale`.
- **Uses from project**: `symJ`, `transpose_mul_symJ_mul`
- **Used by**: `frob_det_data_of_scaling`, `linearMap_det_eq_of_symplectic_scaling`
- **Visibility**: public
- **Lines**: 69–74 (6 lines)
- **Notes**: This is the load-bearing residual interface that avoids dual additivity.

---

### `theorem frob_det_data_of_scaling`

- **Type**: `{F : Type*} [CommRing F] {M : Matrix (Fin 2) (Fin 2) F} {q dE r s D : F} (hπ : Mᵀ * symJ F * M = q • symJ F) (h1 : (1-M)ᵀ * symJ F * (1-M) = dE • symJ F) (hrs : (r•M - s•1)ᵀ * symJ F * (r•M - s•1) = D • symJ F) : M.det = q ∧ (1-M).det = dE ∧ (r•M - s•1).det = D`
- **What**: Packages the three det facts for the Frobenius matrix M (corresponding to π, 1−π, and r·π−s) directly from their per-isogeny symplectic scaling hypotheses.
- **How**: Immediate conjunction of three applications of `det_eq_of_symplectic_scaling`.
- **Hypotheses**: Three symplectic scaling conditions for M, 1−M, and r•M−s•1.
- **Uses from project**: `det_eq_of_symplectic_scaling`
- **Used by**: `Assembly.lean` (externally, via `frob_det_data_of_scaling`); unused within this file.
- **Visibility**: public
- **Lines**: 82–90 (9 lines)
- **Notes**: None.

---

### `theorem det_smul_add_smul_one_eq`

- **Type**: `{F : Type*} [CommRing F] {M Mhat : Matrix (Fin 2) (Fin 2) F} {q t : F} (hadj : Mᵀ * symJ F = symJ F * Mhat) (hnorm : Mhat * M = q • 1) (htr : M + Mhat = t • 1) (a b : F) : (a • M + b • 1).det = a^2 * q + a * b * t + b^2`
- **What**: Given Frobenius data (symplectic adjoint, norm, trace), computes `det(a•M + b•1) = a²·q + a·b·t + b²` for arbitrary scalars `a`, `b`. This is the Frobenius pencil determinant formula.
- **How**: Applies `det_eq_of_symplectic_adjoint` with adjoint `a•Mhat + b•1` (adjoint by linearity from `hadj`); the norm `(a•Mhat+b•1)(a•M+b•1) = (a²q + abt + b²)•1` is computed via `simp` with matrix algebra, `match_scalars`, and then substituting `hnorm`/`htr` with `module`.
- **Hypotheses**: Symplectic adjoint `hadj`, norm `hnorm`, trace `htr` of Frobenius M; scalars `a b : F`.
- **Uses from project**: `det_eq_of_symplectic_adjoint`, `symJ`
- **Used by**: `frob_det_data_of_adjoint_norm_trace`
- **Visibility**: public
- **Lines**: 110–129 (20 lines)
- **Notes**: None.

---

### `theorem frob_det_data_of_adjoint_norm_trace`

- **Type**: `{F : Type*} [CommRing F] {M Mhat : Matrix (Fin 2) (Fin 2) F} {q t : F} (hadj : Mᵀ * symJ F = symJ F * Mhat) (hnorm : Mhat * M = q • 1) (htr : M + Mhat = t • 1) (r s : F) : M.det = q ∧ (1-M).det = q+1-t ∧ (r•M - s•1).det = q*r^2 - t*r*s + s^2`
- **What**: Given the symplectic adjoint, norm π̂π = [q], and trace π+π̂ = [t] of the Frobenius matrix M, derives all three det facts needed by the Reduction/Assembly interface: `det M = q`, `det(1−M) = q+1−t` (= #E), and `det(r•M−s•1) = q·r²−t·r·s+s²`.
- **How**: Specialises `det_smul_add_smul_one_eq` at `(a,b) = (1,0)`, `(−1,1)`, `(r,−s)` for the three cases; uses `module` and `ring` to handle the scalar rearrangements.
- **Hypotheses**: Frobenius matrix data: symplectic adjoint `hadj`, norm `hnorm`, trace `htr`; pencil parameters `r s : F`.
- **Uses from project**: `det_smul_add_smul_one_eq`
- **Used by**: unused within this file (exposed externally as the adjoint-norm-trace route for callers who have trace data).
- **Visibility**: public
- **Lines**: 135–154 (20 lines)
- **Notes**: None.

---

### `theorem linearMap_det_eq_of_symplectic_scaling`

- **Type**: `{R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V] (b : Module.Basis (Fin 2) R V) (φ : V →ₗ[R] V) {d : R} (hscale : (LinearMap.toMatrix b b φ)ᵀ * symJ R * LinearMap.toMatrix b b φ = d • symJ R) : LinearMap.det φ = d`
- **What**: Lifts `det_eq_of_symplectic_scaling` from matrices to `LinearMap.det`: if the matrix of φ in basis b satisfies the symplectic scaling, then `LinearMap.det φ = d`.
- **How**: Rewrites via `LinearMap.det_toMatrix b φ` and delegates to `det_eq_of_symplectic_scaling`.
- **Hypotheses**: Basis `b` for a rank-2 module, symplectic scaling of the matrix of φ.
- **Uses from project**: `symJ`, `det_eq_of_symplectic_scaling`
- **Used by**: unused within this file (bridge to the module-level interface).
- **Visibility**: public
- **Lines**: 168–174 (7 lines)
- **Notes**: The doc-comment references `frob_det_data_of_scaling` as the matrix residual this bridges to.

---

### `theorem alternating_comp_eq_det_smul`

- **Type**: `{F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (b : Module.Basis (Fin 2) F V) (ω : V →ₗ[F] V →ₗ[F] F) (halt : ∀ x, ω x x = 0) (φ : V →ₗ[F] V) : ω (φ (b 0)) (φ (b 1)) = LinearMap.det φ * ω (b 0) (b 1)`
- **What**: The Λ² (exterior square) scaling identity for rank-2 modules over a field: any alternating bilinear form ω satisfies `ω(φ(b₀), φ(b₁)) = (det φ) · ω(b₀, b₁)` for any endomorphism φ.
- **How**: Expands φ(bⱼ) in the basis using `b.sum_repr` and `LinearMap.toMatrix_apply`; derives skew-symmetry `ω(b₁,b₀) = −ω(b₀,b₁)` from `halt` applied to `b₀+b₁`; then simplifies to get `(M₀₀·M₁₁ − M₀₁·M₁₀)·ω(b₀,b₁)` matching `Matrix.det_fin_two`.
- **Hypotheses**: `F` a field, rank-2 `F`-module `V` with basis `b`; alternating form `ω` (anti-symmetry from `halt`); arbitrary linear endomorphism `φ`.
- **Uses from project**: []  (uses only Mathlib: `Module.Basis`, `LinearMap.toMatrix`, `Matrix.det_fin_two`)
- **Used by**: `det_eq_of_alternating_scaling`
- **Visibility**: public
- **Lines**: 186–204 (19 lines)
- **Notes**: Requires `Field` rather than `CommRing` (for `Module.Basis` coefficient inference); longest non-trivial proof in the file.

---

### `theorem det_eq_of_alternating_scaling`

- **Type**: `{F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (b : Module.Basis (Fin 2) F V) (ω : V →ₗ[F] V →ₗ[F] F) (halt : ∀ x, ω x x = 0) (hnd : ω (b 0) (b 1) ≠ 0) (φ : V →ₗ[F] V) {d : F} (hscale : ∀ x y, ω (φ x) (φ y) = d * ω x y) : LinearMap.det φ = d`
- **What**: Module-level Silverman III.8.6: for a rank-2 space with a nondegenerate alternating form ω, if φ scales ω by d (i.e., `ω(φx,φy) = d·ω(x,y)`), then `LinearMap.det φ = d`. This is what the additivised Weil pairing discharges.
- **How**: Uses `alternating_comp_eq_det_smul` evaluated at the basis to get `(det φ)·ω(b₀,b₁) = d·ω(b₀,b₁)`, then cancels the nondegenerate factor `ω(b₀,b₁) ≠ 0` via `mul_right_cancel₀`.
- **Hypotheses**: Field `F`, rank-2 module with basis `b`, alternating form with `halt` and nondegeneracy `hnd`; scaling hypothesis `hscale`.
- **Uses from project**: `alternating_comp_eq_det_smul`
- **Used by**: `frob_det_data_of_pairing_form`; also referenced externally by `DetDeg.lean`.
- **Visibility**: public
- **Lines**: 210–217 (8 lines)
- **Notes**: The mathlib lemma `mul_right_cancel₀` is the key step.

---

### `theorem frob_det_data_of_pairing_form`

- **Type**: `{F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (b : Module.Basis (Fin 2) F V) (ω : V →ₗ[F] V →ₗ[F] F) (halt : ∀ x, ω x x = 0) (hnd : ω (b 0) (b 1) ≠ 0) (φ : V →ₗ[F] V) {q dE r s D : F} (hπ ...) (h1 ...) (hrs ...) : (toMatrix b b φ).det = q ∧ (1 - toMatrix b b φ).det = dE ∧ (r•toMatrix b b φ - s•1).det = D`
- **What**: The form-level packaging of all three Frobenius det facts: given the additivised Weil pairing (ω, alternating, nondegenerate) and per-isogeny scalings for π, 1−π, and rπ−s, proves `det(M) = q`, `det(1−M) = dE`, `det(r•M − s•1) = D`. This is the direct interface discharged by the AG Weil-pairing construction for `Reduction.frob_det_congruence`.
- **How**: Three-branch `refine ⟨?_,?_,?_⟩`. First branch applies `det_eq_of_alternating_scaling` directly. Second and third branches use `map_sub`/`map_smul`/`LinearMap.toMatrix_id` to rewrite `1 − toMatrix φ` and `r•M − s•1` as `toMatrix(id − φ)` and `toMatrix(r•φ − s•id)`, then apply `LinearMap.det_toMatrix` and `det_eq_of_alternating_scaling`.
- **Hypotheses**: Field, rank-2 module, nondegenerate alternating form, and three form-scaling hypotheses for the three isogenies.
- **Uses from project**: `det_eq_of_alternating_scaling`
- **Used by**: referenced externally by `DetDeg.lean`; unused within this file as a caller.
- **Visibility**: public
- **Lines**: 226–250 (25 lines)
- **Notes**: Proof >20 lines but under 30. Key Mathlib steps: `LinearMap.det_toMatrix`, `map_sub`, `map_smul`, `LinearMap.toMatrix_id`.

---

## Cross-reference summary

| Declaration | Used by (in this file) |
|---|---|
| `symJ` | `transpose_mul_symJ_mul`, `det_eq_of_symplectic_adjoint`, `det_eq_of_symplectic_scaling`, `det_smul_add_smul_one_eq`, `linearMap_det_eq_of_symplectic_scaling`, `frob_det_data_of_pairing_form` |
| `transpose_mul_symJ_mul` | `det_eq_of_symplectic_adjoint`, `det_eq_of_symplectic_scaling` |
| `det_eq_of_symplectic_adjoint` | `det_smul_add_smul_one_eq` |
| `det_eq_of_symplectic_scaling` | `frob_det_data_of_scaling`, `linearMap_det_eq_of_symplectic_scaling` |
| `det_smul_add_smul_one_eq` | `frob_det_data_of_adjoint_norm_trace` |
| `alternating_comp_eq_det_smul` | `det_eq_of_alternating_scaling` |
| `det_eq_of_alternating_scaling` | `frob_det_data_of_pairing_form` |

**Key API** (used by 3+ declarations in this file): `symJ` (8 references).
