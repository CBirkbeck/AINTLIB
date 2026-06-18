# Inventory: ./HasseWeil/WeilPairing/FrobeniusGenericCovariance.lean

**File**: `HasseWeil/WeilPairing/FrobeniusGenericCovariance.lean`
**Total declarations**: 6 (1 local instance, 1 noncomputable def, 4 theorems)
**Sorries**: none
**set_option maxHeartbeats**: none (only linter options set)

---

### `noncomputable local instance instDecEqACFGC`

- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides a `DecidableEq` instance for the algebraic closure `K̄` of a finite field `K`, needed throughout the section for point case splits and map computations.
- **How**: Directly via `Classical.decEq _` (classical decidability).
- **Hypotheses**: `K` is a field with `Fintype K` and `DecidableEq K`.
- **Uses from project**: none
- **Used by**: `frobFunctionFieldPointKbar`, `frobeniusGenericCovariance_tau_mapW`, `frobeniusGenericCovariance_lift_twist`, `frobeniusGenericCovariance_frob_tau_comm`, `frobeniusGenericCovariance_Kbar`, `mapTranslateGenericPoint_frobenius_Kbar` (implicit throughout section)
- **Visibility**: private (local)
- **Lines**: 88; proof length: 1 line
- **Notes**: Standard classical workaround. Marked `local` to avoid leaking into other files.

---

### `noncomputable def frobFunctionFieldPointKbar`

- **Type**:
  ```
  frobFunctionFieldPointKbar :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point
  ```
- **What**: Defines the geometric action of the `q`-power Frobenius on function-field points of `E_{K̄}`, typed via `Affine.Point.map` over the *base* curve `W : WeierstrassCurve 𝔽_q` to avoid the `K̄`-linearity diamond (the `q`-power is only `𝔽_q`-linear).
- **How**: Directly wraps `WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom K ...)`.
- **Hypotheses**: `W` is an elliptic curve over a finite field `K`, `W.baseChange K̄` is elliptic.
- **Uses from project**: `W_KE` (project abbreviation for function-field base change)
- **Used by**: `frobeniusGenericCovariance_lift_twist`, `frobeniusGenericCovariance_frob_tau_comm`, `frobeniusGenericCovariance_Kbar`, `mapTranslateGenericPoint_frobenius_Kbar`
- **Visibility**: public
- **Lines**: 97–101; definition (no proof body)
- **Notes**: The scalar-tower diamond (𝔽_q → K̄ → K̄(E)) means the codomain `W.baseChange (K̄(E))` is definitionally `W_KE (W.baseChange K̄)`. This typing is the key design choice enabling the rest of the file.

---

### `theorem frobeniusGenericCovariance_tau_mapW`

- **Type**:
  ```
  frobeniusGenericCovariance_tau_mapW (S : (W.baseChange K̄).toAffine.Point)
    (P : (W_KE (W.baseChange K̄)).toAffine.Point) :
    Affine.Point.map (W' := W.baseChange K̄) (translateAlgEquivOfPoint (W.baseChange K̄) S).toAlgHom P =
    Affine.Point.map (W' := W) ((translateAlgEquivOfPoint (W.baseChange K̄) S).toAlgHom.restrictScalars K) P
  ```
- **What**: Bridges the two `W'`-typings of the translation `τ_S`: the `K̄`-linear version `(W' := W.baseChange K̄)` equals the `𝔽_q`-restricted version `(W' := W)`, so that `τ_S` can be composed with the `𝔽_q`-typed `frobFunctionFieldPointKbar` at a uniform `W' := W`.
- **How**: Direct `cases P <;> rfl`; both typings act via the same underlying ring hom on coordinates, so the equality is definitional after a case split.
- **Hypotheses**: Same section hypotheses as above.
- **Uses from project**: `HasseWeil.translateAlgEquivOfPoint`
- **Used by**: `frobeniusGenericCovariance_Kbar` (twice, forwarding and back)
- **Visibility**: public
- **Lines**: 109–115; proof length: 1 line
- **Notes**: Tiny bridging lemma for the scalar-tower diamond. No heartbeats issue.

---

### `theorem frobeniusGenericCovariance_lift_twist`

- **Type**:
  ```
  frobeniusGenericCovariance_lift_twist (S : (W.baseChange K̄).toAffine.Point) :
    frobFunctionFieldPointKbar W (liftPointToKE (W.baseChange K̄) S) =
    liftPointToKE (W.baseChange K̄) (geomFrobeniusPointFun W S)
  ```
- **What**: The lift-twist fact: the function-field Frobenius `frobₗ` sends the constant lift `lift S` of a `K̄`-point `S` to the lift of its geometric Frobenius image `π̄ S = geomFrobeniusPointFun S`.
- **How**: Case split on `S`; zero case uses `geomFrobeniusPointFun_zero` and `map_zero`; `some` case rewrites with `geomFrobeniusPointFun_some`, `liftPointToKE_some`, `liftSomePoint`, then uses `FiniteField.coe_frobeniusAlgHom` and `map_pow` to identify `(algebraMap sx)^q = algebraMap (sx^q)`.
- **Hypotheses**: Same section hypotheses.
- **Uses from project**: `HasseWeil.liftPointToKE`, `HasseWeil.liftPointToKE_some`, `HasseWeil.liftSomePoint`, `geomFrobeniusPointFun` (from `FrobeniusFixedPoint.lean`), `geomFrobeniusPointFun_zero`, `geomFrobeniusPointFun_some`
- **Used by**: `frobeniusGenericCovariance_Kbar`
- **Visibility**: public
- **Lines**: 128–143; proof length: ~15 lines
- **Notes**: This is the heart of the `K̄`-vs-`𝔽_q` dichotomy. The key step is that `(algebraMap a)^q = algebraMap (a^q)` (ring hom preserves powers), realizing `frobₗ (lift S) = lift (π̄ S)` over `K̄`.

---

### `theorem frobeniusGenericCovariance_frob_tau_comm`

- **Type**:
  ```
  frobeniusGenericCovariance_frob_tau_comm (S : (W.baseChange K̄).toAffine.Point)
    (P : (W_KE (W.baseChange K̄)).toAffine.Point) :
    Affine.Point.map (W' := W) (τ_S.restrictScalars K) (frobFunctionFieldPointKbar W P) =
    frobFunctionFieldPointKbar W (Affine.Point.map (W' := W) (τ_S.restrictScalars K) P)
  ```
- **What**: The `q`-power Frobenius `frobₗ` commutes with the `𝔽_q`-restricted translation `τ_S` on function-field points of `E_{K̄}` (both typed via `W' := W`).
- **How**: Case split on `P`; zero case by `rfl`; `some (x, y)` case rewrites all four `Point.map`s via `Affine.Point.map_some`, then uses `Affine.Point.some.injEq` to reduce to coordinate equalities, which follow from `map_pow` applied to `translateAlgEquivOfPoint` (a ring hom commutes with `q`-powers: `τ_S(x^q) = (τ_S x)^q`).
- **Hypotheses**: Same section hypotheses.
- **Uses from project**: `HasseWeil.translateAlgEquivOfPoint`, `frobFunctionFieldPointKbar`
- **Used by**: `frobeniusGenericCovariance_Kbar`
- **Visibility**: public
- **Lines**: 153–180; proof length: ~27 lines
- **Notes**: Uses `AlgEquiv.toAlgHom_eq_coe` and `FiniteField.coe_frobeniusAlgHom` to normalize to the `(·^q)` lambda form before applying `map_pow`.

---

### `theorem frobeniusGenericCovariance_Kbar`

- **Type**:
  ```
  frobeniusGenericCovariance_Kbar (S : (W.baseChange K̄).toAffine.Point) :
    Affine.Point.map (W' := W.baseChange K̄) (translateAlgEquivOfPoint (W.baseChange K̄) S).toAlgHom
        (frobFunctionFieldPointKbar W (genericPoint (W.baseChange K̄))) =
    frobFunctionFieldPointKbar W (genericPoint (W.baseChange K̄)) +
      liftPointToKE (W.baseChange K̄) (geomFrobeniusPointFun W S)
  ```
- **What**: The main result of the file: the `q`-power Frobenius generic-point covariance over `K̄`. The function-field translation `τ_S` commutes with `frobₗ` at the generic point, with the twist that `frobₗ(lift S) = lift(π̄ S)`.
- **How**: Rewrites `τ_S` to the `W' := W` typing (`frobeniusGenericCovariance_tau_mapW`), commutes it past `frobₗ` (`frobeniusGenericCovariance_frob_tau_comm`), rewrites back, applies the master translation lemma `translateAlgEquivOfPoint_map_genericPoint` (from `SeparableKernelTorsor.lean`) to expand `Point.map τ_S P_gen = P_gen + lift S`, uses additivity of `frobFunctionFieldPointKbar` (`map_add`), then applies the lift-twist `frobeniusGenericCovariance_lift_twist`.
- **Hypotheses**: Same section hypotheses.
- **Uses from project**: `frobeniusGenericCovariance_tau_mapW`, `frobeniusGenericCovariance_frob_tau_comm`, `frobeniusGenericCovariance_lift_twist`, `HasseWeil.translateAlgEquivOfPoint_map_genericPoint` (from `SeparableKernelTorsor.lean`), `HasseWeil.genericPoint`, `HasseWeil.liftPointToKE`, `frobFunctionFieldPointKbar`, `geomFrobeniusPointFun`
- **Used by**: `mapTranslateGenericPoint_frobenius_Kbar`
- **Visibility**: public
- **Lines**: 194–205; proof length: ~11 lines
- **Notes**: The proof chain `tau_mapW → frob_tau_comm → tau_mapW⁻¹ → translateAlgEquivOfPoint_map_genericPoint → map_add → lift_twist` is clean and modular. This is the capstone of the "Wall B" resolution.

---

### `theorem mapTranslateGenericPoint_frobenius_Kbar`

- **Type**:
  ```
  mapTranslateGenericPoint_frobenius_Kbar (p r : ℕ) [Fact p.Prime] [CharP K p]
      [Fact (Fintype.card K = p ^ r)] :
    MapTranslateGenericPoint (W.baseChange K̄)
      (Isogeny.frobeniusIsog_baseChange_charP_pow p r W K̄)
      (frobFunctionFieldPointKbar W)
  ```
- **What**: Packages the Frobenius covariance `frobeniusGenericCovariance_Kbar` as a `MapTranslateGenericPoint` leaf, i.e., in the form consumed by `mapTranslateGenericPoint_add` for the `±π` component of `1 − π` and `rπ − s`.
- **How**: Introduces `S`, proves `hπ : φ.toAddMonoidHom S = geomFrobeniusPointFun W S` using `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (from `OneSubWitnesses.lean`) and the definition of `frobeniusHomBaseChange`, rewrites by `hπ`, and applies `frobeniusGenericCovariance_Kbar`.
- **Hypotheses**: In addition to section hypotheses: `p` is a prime, `K` has characteristic `p`, `#K = p^r`.
- **Uses from project**: `MapTranslateGenericPoint` (from `SeparableWitnesses.lean`), `Isogeny.frobeniusIsog_baseChange_charP_pow`, `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (from `OneSubWitnesses.lean`), `frobeniusHomBaseChange` (from `FrobMatrixData.lean`), `geomFrobeniusPointFun`, `frobeniusGenericCovariance_Kbar`, `frobFunctionFieldPointKbar`
- **Used by**: unused in this file (exported API for `MapTranslateGenericAdditive.lean` consumers)
- **Visibility**: public
- **Lines**: 218–232; proof length: ~14 lines
- **Notes**: Explicitly notes (in docstring) that Wall A (the opaque `baseChangePullback` conjugate at the generic point, `Φ`-generic-point compatibility) is **not** supplied here — it is the genuine residual. This declaration closes "Wall B" as proven for the Frobenius specifically.
