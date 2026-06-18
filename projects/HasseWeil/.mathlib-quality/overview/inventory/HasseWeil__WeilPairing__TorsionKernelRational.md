# Inventory: ./HasseWeil/WeilPairing/TorsionKernelRational.lean

**File purpose**: Discharges the remaining two genuine-isogeny coherence inputs of the separable-kernel-torsor capstone for `φ = [ℓ]` over an algebraically closed `F = K̄`: the inverse-witness descent `hdesc_mulByInt` and the normality `h_normal_mulByInt` of `K(E)/[ℓ]*K(E)`. Both rest on **kernel-rationality** (Silverman III.4.10c): over `K̄`, every `K(E)`-point killed by `[ℓ]` descends to a `K̄`-rational `ℓ`-torsion point, because `[ℓ]Q=O ⟹ Ψ²_ℓ(x(Q))=0` and `Ψ²_ℓ` has coefficients in `K̄` (so splits), forcing `x(Q),y(Q) ∈ K̄`.

**Imports**: `HasseWeil.EC.SeparableKernelTorsor`, `HasseWeil.EC.GenericPointZsmul`, `Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.FieldTheory.Normal.Basic`, `Mathlib.FieldTheory.Extension`

**Namespace**: `HasseWeil`. **Section variables**: `{F} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.toAffine.IsElliptic]` (several decls re-declare `F`/`W` locally or take an extra `[IsAlgClosed F]`).

**Total declarations**: 12 (1 `private theorem`, 11 public `theorem`). **No `sorry` anywhere** (not in comments either). **Eight `set_option maxHeartbeats` blocks** (six at 2M, one 800k, one 1.6M).

---

## Declarations

### `theorem kernelOverKE_descends` (Silverman III.4.10c — the engine)
- **What**: Over `K̄`, every point `Q : (W_KE).Point` (coordinates in `K(E)`) with `ℓ•Q=0` descends to a `K̄`-rational `ℓ`-torsion point `k : E(K̄)` with `liftPointToKE W k = Q` and `ℓ•k=0`.
- **How**: case on `Q`. Zero ↦ `k=0`. For `Q=(X,Y)`: `ℓ•Q=0` forces the Jacobian `Z`-coord `ψ_ℓ(X,Y)=0` (contrapositive of `zsmul_affine_point_eq`, realigning the `DecidableEq` instance via `Subsingleton.elim`), hence `Ψ²_ℓ(X)=ψ_ℓ²=0` (`evalEval_ψ_sq`). Since `Ψ²_{W_KE,ℓ}=(Ψ²_{W,ℓ}).map i` (`map_ΨSq`) is the image of a poly over `K̄`, `IsAlgClosed.splits` + `Splits.mem_range_of_isRoot` (with `ΨSq_poly_ne_zero`) gives `X=i x₀`. The `Y`-descent uses the monic Weierstrass quadratic `T²+(a₁x₀+a₃)T−(…)` (monicity via `monic_X_pow_add`, root via `Affine.equation_iff`+`linear_combination`), again split over `K̄`. Reconstructs `k=some x₀ y₀` (nonsingularity via `baseChange_nonsingular`), `liftPointToKE_some`, and `ℓ•k=0` by injectivity of `liftPointToKE` (`Point.map_injective`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `hℓ:ℓ≠0`, `Q`, `hQ:ℓ•Q=0`.
- **Uses from project**: `W_KE`, `zsmul_affine_point_eq`, `evalEval_ψ_sq`, `ΨSq`, `map_ΨSq`, `ΨSq_poly_ne_zero`, `liftPointToKE{,_some}`, `instDecidableEqFunctionField`, `Affine.Point.map_injective`.
- **Used by (in file)**: `hdesc_mulByInt`.
- **Visibility**: public. **Lines**: 44–135 (>30-line proof). **`set_option maxHeartbeats 2000000`**.

### `theorem hdesc_mulByInt` (Silverman III.4.10c — `hdesc` for `[ℓ]`)  ★ live API
- **What**: For every `σ : AlgEquiv` of `K(E)/[ℓ]*K(E)`, the fibre `σ(P_gen) − P_gen` is an `F`-rational kernel point of `[ℓ]`. This is the capstone's `hdesc` input.
- **How**: the geometric action `g = zsmulAddGroupHom ℓ` has `g(P_gen)=some(mulByInt_x ℓ)(mulByInt_y ℓ)` (`zsmul_genericPoint_eq` + `mulByInt_pullback_{x,y}`, instance realignment via `Subsingleton.elim`). σ-equivariance is just `map_zsmul` for `Point.map σ`. Feeds the shipped `genericPointAct_mem_ker_g` to get `g(σP_gen)=g(P_gen)`, hence `ℓ•(σP_gen−P_gen)=0`, then `kernelOverKE_descends` produces `k`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `hℓ:ℓ≠0`.
- **Uses from project**: `mulByInt{,_x,_y,_apply,_pullback_x,_pullback_y}`, `zsmul_genericPoint_eq`, `genericPoint{,Act}`, `genericPointAct_mem_ker_g`, `liftPointToKE`, `kernelOverKE_descends`, `Isogeny.mem_kernel_iff`, `instDecidableEqFunctionField`.
- **Used by (external)**: `WeilPairing/PairingNondeg.lean` (and `TorsionCardEll.card_torsion_ell`).
- **Visibility**: public. **Lines**: 153–201 (>30-line proof). **`set_option maxHeartbeats 2000000`**.

### `private theorem algebraMapPoly_mem_adjoin_x_gen`
- **What**: `algebraMap F[X] K(E) p ∈ F⟮x_gen⟯` for any `p` (it equals `aeval x_gen p`).
- **How**: `x_gen = algebraMap F[X] _ X`, `Polynomial.induction_on'`, `aeval_mem_adjoin_singleton`.
- **Hypotheses**: `omit [IsElliptic] [DecidableEq F]`; `(p : F[X])`.
- **Uses from project**: `x_gen`.
- **Used by (in file)**: `adjoin_x_gen_y_gen_eq_top`.
- **Visibility**: **private**. **Lines**: 222–235.

### `theorem adjoin_x_gen_y_gen_eq_top`
- **What**: `K(E)` is generated over `F` by `{x_gen, y_gen}` (`IntermediateField.adjoin F {x_gen,y_gen} = ⊤`).
- **How**: every `z` is a ratio `algebraMap R r / algebraMap R s` (`IsFractionRing.div_surjective`); each `algebraMap R r` lies in `F⟮x_gen,y_gen⟯` via the rank-2 basis `{1, mk Y}` (`exists_smul_basis_eq`) → `r = p•1 + q•(mk Y)`, with `F[X]`-images in `F⟮x_gen⟯` (`algebraMapPoly_mem_adjoin_x_gen`) and `mk Y = y_gen` a generator; closure under `+,·,/`.
- **Hypotheses**: `omit [IsElliptic] [DecidableEq F]`.
- **Uses from project**: `x_gen`, `y_gen`, `algebraMapPoly_mem_adjoin_x_gen`, `Affine.CoordinateRing.{exists_smul_basis_eq,mk}`.
- **Used by (in file)**: `h_normal_mulByInt`.
- **Visibility**: public. **Lines**: 247–279. **`set_option maxHeartbeats 800000`**.

### `theorem zsmul_affine_point_eq_gen` (curve-general Jacobian division-poly coords)
- **What**: For an *arbitrary* elliptic `V/L` and a nonsingular `(x₀,y₀)` with `ψ_m(x₀,y₀)≠0`, `m•(x₀,y₀) = (φ_m/ψ_m², ω_m/ψ_m³)`. The curve-general form of `zsmul_affine_point_eq`.
- **How**: identical Jacobian↔affine route: `zsmul_eq_smulEval`, `Jacobian.nonsingular_of_Z_ne_zero`, `toAffineAddEquiv`/`toAffineLift`/`toAffine_of_Z_ne_zero`.
- **Hypotheses**: `{L} [Field L] [DecidableEq L] (V) [V.IsElliptic] (m:ℤ) {x₀ y₀}`, `h_ns`, `h_ψ_ne`.
- **Uses from project**: `smulEval`, `zsmul_eq_smulEval`, `Jacobian.*` mathlib API (`Point.fromAffine`, `toAffineAddEquiv`, `toAffineLift`, `nonsingular_of_Z_ne_zero`, `toAffine_of_Z_ne_zero`).
- **Used by (in file)**: `kernelDescends_general`.
- **Used by (external)**: `EC/MulByIntSamePlace.lean`, `WeilPairing/PairingNondeg.lean`.
- **Visibility**: public. **Lines**: 293–357 (>30-line proof).

### `theorem kernelDescends_general` (curve-general kernel-rationality)
- **What**: Same statement as `kernelOverKE_descends` but for an arbitrary `[Algebra F L]` with `[IsAlgClosed F]`, descending `Q : (W.map (algebraMap F L)).Point` along `Algebra.ofId F L`.
- **How**: verbatim the `kernelOverKE_descends` argument but with `zsmul_affine_point_eq_gen` and `Algebra.ofId F L` in place of the `K(E)`-specific maps; same `Ψ²`-splitting + Weierstrass-quadratic descent.
- **Hypotheses**: `{F}[Field F][DecidableEq F](W)[IsElliptic][IsAlgClosed F]{L}[Field L][DecidableEq L][Algebra F L]`, `(ℓ:ℤ)`, `hℓ`, `Q`, `hQ`.
- **Uses from project**: `zsmul_affine_point_eq_gen`, `evalEval_ψ_sq`, `ΨSq`, `map_ΨSq`, `ΨSq_poly_ne_zero`, `baseChange_nonsingular`, `Point.map{,_injective,_some,_zero}`.
- **Used by (in file)**: `sigma_genCoord_mem_range_proto`.
- **Visibility**: public. **Lines**: 361–438 (>30-line proof). **`set_option maxHeartbeats 2000000`**. **NOTE**: near-verbatim duplicate of `kernelOverKE_descends` (see findings).

### `theorem sigma_genCoord_mem_range_proto` (Silverman III.4.10c — the geometric heart)
- **What**: An `F`-embedding `g : K(E)→Ω` agreeing with a reference `ι` on the pullback range `[ℓ]*K(E)` sends `x_gen,y_gen` into `range ι`.
- **How**: `g(P_gen)`, `ι(P_gen)` are two `E(Ω)`-points with equal `[ℓ]`-image (σ fixes `[ℓ]*x_gen,[ℓ]*y_gen` via `mulByInt_pullback_{x,y}`+`hfix`), so their difference is a kernel point; `kernelDescends_general` makes it `F`-rational; then `g(P_gen)=ι(P_gen + lift k)` (`Point.map_map`, `Algebra.comp_ofId`), and reading coordinates (`map_some`, `some.inj`, ruling out the zero translate via `some_ne_zero`) gives membership.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `hℓ`, `{Ω}[Field Ω][DecidableEq Ω][Algebra F Ω]`, `ι g : K(E)→ₐ[F] Ω`, `hfix`.
- **Uses from project**: `genericPoint`, `zsmul_genericPoint_eq`, `mulByInt{,_pullback_x,_pullback_y}`, `kernelDescends_general`, `liftPointToKE`, `genericPoint_xOf_some`, `generic_nonsingular`, `baseChange_nonsingular`, `instDecidableEqFunctionField`.
- **Used by (in file)**: `mulByInt_genCoords_minpoly_splits`.
- **Visibility**: public. **Lines**: 450–525 (>30-line proof). **`set_option maxHeartbeats 2000000`**.

### `theorem root_minpoly_in_range_eval`
- **What**: A root `t` (in an alg-closed extension `A`) of `minpoly Kb a` is `ψ a` for some `Kb`-algebra hom `ψ : K→ₐ[Kb] A`.
- **How**: repackages mathlib's `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly` + `mem_rootSet_of_ne` + `aeval_def`.
- **Hypotheses**: distinct type vars `{Kb K A}` with field/algebra/`IsAlgClosed A`/`IsAlgebraic Kb K`; `(a:K)(t:A)`, `ht`.
- **Uses from project**: none (mathlib only).
- **Used by (in file)**: `minpoly_splits_of_algHom_image_mem`.
- **Visibility**: public. **Lines**: 531–539.

### `theorem minpoly_splits_of_algHom_image_mem`
- **What**: If every `Kb`-algHom image `ψ a` lands in `range jb` (where `jb : K↪A`, `A` alg-closed), then `minpoly Kb a` splits over `K`.
- **How**: `Splits.of_splits_map_of_injective` against `IsAlgClosed.splits`; each root `t` of the mapped minpoly is `ψ a` (`root_minpoly_in_range_eval`) hence in `range jb`.
- **Hypotheses**: distinct `{Kb K A}` field/algebra/`IsAlgClosed A`/`IsAlgebraic Kb K`; `(a)(jb)`, `hjb`, `hcompat`, `hmem`.
- **Uses from project**: `root_minpoly_in_range_eval`.
- **Used by (in file)**: `minpoly_gen_splits_of_mem_range`.
- **Visibility**: public. **Lines**: 545–560.

### `theorem minpoly_gen_splits_of_mem_range` (single-coordinate splitting)
- **What**: If every `[ℓ]*K(E)`-algHom image of `a∈{x_gen,y_gen}` into `Ω=AlgebraicClosure K(E)` lies in the canonical embedding's range, then `minpoly_{[ℓ]*K(E)}(a)` splits in `K(E)`.
- **How**: instantiates `minpoly_splits_of_algHom_image_mem` with base algebra `B = (mulByInt ℓ).toAlgebra` and `A=Ω`, supplied entirely with `@`-explicit instances to avoid the `Algebra K(E) K(E)` instance-shadowing between the pullback algebra and `Algebra.id`. Finite-dimensionality from `isogeny_finiteDimensional`; each `B`-algHom `ψ` is repackaged as an `F`-algHom `g` via `AlgHom.restrictScalars` (inline scalar tower `IsScalarTower.of_algHom`) and fed to `hmem`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `_hℓ`, `(a)`, `hmem`; conclusion under `letI := (mulByInt ℓ).toAlgebra`.
- **Uses from project**: `mulByInt`, `minpoly_splits_of_algHom_image_mem`, `isogeny_finiteDimensional`, `Isogeny.pullback`.
- **Used by (in file)**: `mulByInt_genCoords_minpoly_splits`.
- **Visibility**: public. **Lines**: 567–635 (>30-line proof). **`set_option maxHeartbeats 2000000`**. **NOTE: extremely instance-fragile (`@`-explicit throughout).**

### `theorem mulByInt_genCoords_minpoly_splits` (the deep residual, III.4.10c)
- **What**: The minimal polynomials over `[ℓ]*K(E)` of both `x_gen` and `y_gen` split in `K(E)`.
- **How**: combines `sigma_genCoord_mem_range_proto` (geometric range-control) with `minpoly_gen_splits_of_mem_range` (abstract splitting), once per coordinate.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `hℓ`.
- **Uses from project**: `minpoly_gen_splits_of_mem_range`, `sigma_genCoord_mem_range_proto`, `mulByInt`, `x_gen`, `y_gen`.
- **Used by (in file)**: `h_normal_mulByInt`.
- **Visibility**: public. **Lines**: 644–660. **`set_option maxHeartbeats 2000000`**.

### `theorem h_normal_mulByInt` (Silverman III.4.10c — `h_normal` for `[ℓ]`)  ★ live API
- **What**: `K(E)/[ℓ]*K(E)` is `Normal`. The capstone's `h_normal` input.
- **How**: algebraicity = finite-dimensionality (`isogeny_finiteDimensional` → `IsAlgebraic.of_finite`); `normal_iff.mpr`; every `z∈⊤=F⟮x_gen,y_gen⟯` (`adjoin_x_gen_y_gen_eq_top`), so `IntermediateField.splits_of_mem_adjoin` reduces splitting to the two generator minpolys (`mulByInt_genCoords_minpoly_splits`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `hℓ`; conclusion under `letI := (mulByInt ℓ).toAlgebra`.
- **Uses from project**: `mulByInt`, `isogeny_finiteDimensional`, `mulByInt_genCoords_minpoly_splits`, `adjoin_x_gen_y_gen_eq_top`, `x_gen`, `y_gen`.
- **Used by (external)**: `WeilPairing/PairingNondeg.lean` (and `TorsionCardEll.card_torsion_ell`).
- **Visibility**: public. **Lines**: 673–701. **`set_option maxHeartbeats 1600000`**.

---

## File Summary

**Role in cluster**: The **AG-heavy half** of the `#E[ℓ]=ℓ²` proof — Silverman III.4.10c kernel-rationality and normality. Supplies `hdesc_mulByInt` and `h_normal_mulByInt`, the two inputs `TorsionGeometric.lean` does not provide.

**Live spine (used downstream)**: `hdesc_mulByInt`, `h_normal_mulByInt` (→ `PairingNondeg`/`TorsionCardEll`), and `zsmul_affine_point_eq_gen` (→ `EC/MulByIntSamePlace`, `PairingNondeg`). The internal chain `kernelOverKE_descends`/`kernelDescends_general` → `sigma_genCoord_mem_range_proto` → `mulByInt_genCoords_minpoly_splits` is the engine.

**Cleanup findings**:
- (a) **Unused-in-file**: none (every decl feeds either `hdesc`/`h_normal` or an external consumer).
- (b) **Major duplication — `kernelOverKE_descends` vs `kernelDescends_general`**: these are two near-verbatim copies of the same Ψ²-splitting/Weierstrass-quadratic descent (one for `L=K(E)`, one for general `L`), both at 2M heartbeats. The `K(E)`-version is a special case `L=K(E)` of the general one; `kernelOverKE_descends` should be derivable from `kernelDescends_general` (≈90 lines saved). Likewise `zsmul_affine_point_eq_gen` is the curve-general form of the project's `zsmul_affine_point_eq` — verify the special version isn't now redundant.
- (c) **Hand-rolled vs mathlib**: `root_minpoly_in_range_eval` and `minpoly_splits_of_algHom_image_mem` are thin repackagings of `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly` and `Splits.of_splits_map_of_injective` — kept only to dodge same-type instance shadowing. The instance-juggling in `minpoly_gen_splits_of_mem_range` (fully `@`-explicit, an inline `IsScalarTower.of_algHom`) is the most fragile code in the cluster; a cleaner `Algebra`/`IsScalarTower` setup (or a dedicated `letI` discipline) would remove most `@`-annotations.
- (d) **Under-general**: `kernelOverKE_descends` is strictly less general than `kernelDescends_general` and could be deleted in favour of it.
- **Heartbeats**: six proofs at 2M, one 1.6M, one 800k — by far the heaviest file in the cluster. The instance realignments (`Subsingleton.elim` for `DecidableEq K(E)`) recur in 3+ proofs and are a candidate for a shared helper.
- **`sorry`**: none.
