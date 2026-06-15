# Inventory: ./HasseWeil/WeilPairing/OneSubDualDivisor.lean

**File**: `HasseWeil/WeilPairing/OneSubDualDivisor.lean`
**Summary**: Builds the divisor-pushforward dual `δ = κ ∘ φ^* ∘ κ⁻¹` of a separable isogeny (Silverman III.6.1b) using only the multiplicity-free fibre pullback and the Abel–Jacobi isomorphism — no CoordHom, no characteristic polynomial — then specialises to `(1 − π)_{K̄}` to discharge `OneSubFrobeniusScaling` (leaf 2 of `FrobBaseChangeScalings`).

**Total declarations**: 13 (4 `noncomputable def`, 1 `noncomputable local instance`, 8 `theorem`/`@[simp] theorem`)

---

### `theorem picZeroIsoE_allChar_mk`

- **Type**: For a field `F` (algebraically closed, Dedekind, integrally closed coordinate ring), `W : Affine F` elliptic, and `D : ProjectiveDivisor.degZero`: `Curves.picZeroIsoE_allChar W (QuotientAddGroup.mk D) = Curves.projectiveDivisorSum W D.val`
- **What**: The forward map of the Abel–Jacobi isomorphism `κ : Pic⁰(E) ≅ E` on a `Pic⁰` class `[D]` is the group sum `σ D = projectiveDivisorSum D`.
- **How**: Proved by `rfl` — it is definitionally true by how `picZeroIsoE_allChar` is constructed.
- **Hypotheses**: `F` algebraically closed, `W.IsElliptic`, `IsDedekindDomain` and `IsIntegrallyClosed` on the coordinate ring.
- **Uses from project**: `Curves.picZeroIsoE_allChar`, `Curves.projectiveDivisorSum`
- **Used by**: `divisorPushforwardDual_comp` (line 293)
- **Visibility**: public
- **Lines**: 94–100; proof length: 1 line
- **Notes**: None

---

### `theorem degree_pullbackDivisor_single`

- **Type**: For surjective `f : E.Point →+ E.Point` with finite kernel, place `v`, and `n : ℤ`: `(pullbackDivisor f hf (Finsupp.single v n)).degree = (Nat.card f.ker : ℤ) * n`
- **What**: The degree of the multiplicity-free fibre pullback of a single-place divisor `n · (v)` equals `#ker(f) · n`.
- **How**: Chooses a preimage `P₀` of `v.toAffinePoint` via `hsurj`, then rewrites via `pullbackDivisor_single`, `degreeHom_apply`, `map_zsmul`, and `degree_pullbackDiv` (which sizes the fibre over a given preimage).
- **Hypotheses**: `f` surjective, finite kernel.
- **Uses from project**: `pullbackDivisor_single`, `Curves.ProjectiveDivisor.degreeHom_apply`, `degree_pullbackDiv`, `pullbackDivisorHom_apply`
- **Used by**: `degree_pullbackDivisor` (line 140)
- **Visibility**: public
- **Lines**: 119–128; proof length: ~5 lines
- **Notes**: None

---

### `theorem degree_pullbackDivisor`

- **Type**: For surjective `f : E.Point →+ E.Point` with finite kernel, `D : ProjectiveDivisor`: `(pullbackDivisor f hf D).degree = (Nat.card f.ker : ℤ) * D.degree`
- **What**: The full degree formula: the multiplicity-free fibre pullback multiplies every divisor degree by `#ker(f)`.
- **How**: `Finsupp.induction` on `D`, with the `zero` case by `simp` and the `single_add` case by `degree_pullbackDivisor_single` plus additivity of `degree`.
- **Hypotheses**: `f` surjective, finite kernel.
- **Uses from project**: `pullbackDivisorHom_apply`, `Curves.ProjectiveDivisor.degree_add`, `degree_pullbackDivisor_single`, `degree_single`
- **Used by**: `pullbackDegZero` (line 157), `pullbackDegZero_coe` is used internally; referenced in comment by `SeparableTransportBridge.lean`
- **Visibility**: public
- **Lines**: 132–141; proof length: ~8 lines
- **Notes**: None

---

### `noncomputable def pullbackDegZero`

- **Type**: `pullbackDegZero (f : E.Point →+ E.Point) (hf : Finite f.ker) (hsurj : Function.Surjective f) : ProjectiveDivisor.degZero →+ ProjectiveDivisor.degZero`
- **What**: Restricts `pullbackDivisor f hf` (the `ℤ`-linear fibre pullback) to the degree-zero subgroup `Div⁰(E)`, producing an `AddMonoidHom` on `Div⁰`.
- **How**: `AddMonoidHom.codRestrict` of `pullbackDivisorHom ∘ subtype`; the membership proof uses `degree_pullbackDivisor` to verify degree `0` is preserved.
- **Hypotheses**: `f` surjective, finite kernel.
- **Uses from project**: `pullbackDivisorHom`, `degree_pullbackDivisor`, `Curves.ProjectiveDivisor.mem_degZero`
- **Used by**: `pullbackDegZero_coe` (line 163–166), `pullbackPicZero` (line 227)
- **Visibility**: public
- **Lines**: 146–158; definition body: ~12 lines
- **Notes**: None

---

### `@[simp] theorem pullbackDegZero_coe`

- **Type**: `((pullbackDegZero W f hf hsurj D : degZero) : ProjectiveDivisor) = pullbackDivisor f hf (D : ProjectiveDivisor)`
- **What**: The coercion of `pullbackDegZero D` back to `ProjectiveDivisor` is simply `pullbackDivisor f hf D`.
- **How**: `rfl` — definitionally true.
- **Hypotheses**: Same as `pullbackDegZero`.
- **Uses from project**: `pullbackDivisor`, `pullbackDegZero`
- **Used by**: `pullbackPicZero` (line 234), `divisorPushforwardDual_comp` (line 295)
- **Visibility**: public (`@[simp]`)
- **Lines**: 160–167; proof length: 1 line
- **Notes**: None

---

### `theorem pullbackDivisor_mem_projPrincipal`

- **Type**: For `φ : Isogeny W W` with `[Finite φ.ker]`, `hproj : ProjOrdTransport φ`, and `D` in `projPrincipalSubgroup`: `pullbackDivisor φ.toAddMonoidHom inferInstance D ∈ projPrincipalSubgroup`
- **What**: The multiplicity-free fibre pullback of a principal projective divisor `div(h)` is again principal: `φ^*(div h) = div(φ^* h)`.
- **How**: Destructs the witness `h` for `D` being principal; supplies `φ.pullback h` as witness for the pullback; non-vanishing via `φ.pullback_injective`; the divisor identity uses `projectiveDivisorOf_pullback_eq_pullbackDivisor hproj h`.
- **Hypotheses**: `ProjOrdTransport φ`, finite kernel.
- **Uses from project**: `projectiveDivisorOf_pullback_eq_pullbackDivisor`, `φ.pullback_injective`
- **Used by**: `pullbackPicZero` (well-definedness proof, line 235)
- **Visibility**: public
- **Lines**: 187–198; proof length: ~8 lines
- **Notes**: The key use of `ProjOrdTransport` — it is what makes `φ^*` descend to `Pic⁰`.

---

### `noncomputable def pullbackPicZero`

- **Type**: `pullbackPicZero (φ : Isogeny W W) [Finite φ.ker] (hproj : ProjOrdTransport φ) (hsurj : Function.Surjective φ.toAddMonoidHom) : PicProj₀ →+ PicProj₀`
- **What**: The divisor pullback `φ^*` descended to `Pic⁰(E)`, well-defined because `φ^*` preserves principal divisors (by `ProjOrdTransport`).
- **How**: `QuotientAddGroup.lift` applied to `mk' ∘ pullbackDegZero`; the well-definedness proof uses `pullbackDivisor_mem_projPrincipal`.
- **Hypotheses**: `ProjOrdTransport φ`, surjective `φ`, finite kernel.
- **Uses from project**: `pullbackDegZero`, `pullbackDivisor_mem_projPrincipal`, `pullbackDegZero_coe`
- **Used by**: `pullbackPicZero_mk` (line 240–241), `divisorPushforwardDual` (lines 269)
- **Visibility**: public
- **Lines**: 217–235; definition body: ~18 lines
- **Notes**: None

---

### `@[simp] theorem pullbackPicZero_mk`

- **Type**: `pullbackPicZero W φ hproj hsurj (QuotientAddGroup.mk D) = QuotientAddGroup.mk (pullbackDegZero W φ.toAddMonoidHom inferInstance hsurj D)`
- **What**: The `Pic⁰`-pullback on a class `[D]` is the class of `pullbackDegZero D`.
- **How**: `rfl` — definitionally true from `QuotientAddGroup.lift`.
- **Hypotheses**: Same as `pullbackPicZero`.
- **Uses from project**: `pullbackPicZero`, `pullbackDegZero`
- **Used by**: `divisorPushforwardDual_comp` (line 292)
- **Visibility**: public (`@[simp]`)
- **Lines**: 237–242; proof length: 1 line
- **Notes**: None

---

### `noncomputable def divisorPushforwardDual`

- **Type**: `divisorPushforwardDual (φ : Isogeny W W) [Finite φ.ker] (hproj : ProjOrdTransport φ) (hsurj : Function.Surjective φ.toAddMonoidHom) : W.toAffine.Point →+ W.toAffine.Point`
- **What**: The dual point endomorphism `δ = κ ∘ (φ^* on Pic⁰) ∘ κ⁻¹` (Silverman III.6.1b), transported across the Abel–Jacobi iso. No coordinate-ring comorphism required.
- **How**: Composition of `(picZeroIsoE_allChar W).toAddMonoidHom` with `pullbackPicZero` with `(picZeroIsoE_allChar W).symm.toAddMonoidHom`.
- **Hypotheses**: `IsAlgClosed F`, `IsDedekindDomain` and `IsIntegrallyClosed` on coordinate ring, `ProjOrdTransport φ`, surjective `φ`, finite kernel.
- **Uses from project**: `Curves.picZeroIsoE_allChar`, `pullbackPicZero`
- **Used by**: `divisorPushforwardDual_comp` (line 285), `mkOneSubScalingDataConcrete_of_divisorDual` (lines 380–382); also used by `PencilDualDivisor.lean` and `OneSubProjOrdTransport.lean`
- **Visibility**: public
- **Lines**: 264–270; definition body: 3 lines
- **Notes**: Key API declaration — used by 3+ declarations (both within this file and externally in PencilDualDivisor and OneSubProjOrdTransport).

---

### `theorem divisorPushforwardDual_comp`

- **Type**: For `φ : Isogeny W W` with `hproj` and `hsurj`: `(divisorPushforwardDual W φ hproj hsurj).comp φ.toAddMonoidHom = (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom`
- **What**: The dual relation `δ ∘ φ = [#ker φ]` (Silverman III.6.2(a)): composing `δ` with `φ` gives the multiplication-by-`#ker` endomorphism, automatically from the fibre sum.
- **How**: Unfolds at a point `P` via `divisorPushforwardDual`, `mulByInt_apply`. Shows `κ⁻¹(f P) = mk ⟨kappaDivisor (f P), _⟩` by `rfl` (stored as `hsymm`). Applies `pullbackPicZero_mk`, `picZeroIsoE_allChar_mk`, `pullbackDegZero_coe`. Uses the σ-bridge `sigma_pullbackDivisor_kappaDivisor W φ.toAddMonoidHom inferInstance (P₀ := P) rfl` to conclude `σ(φ^*((fP)−(O))) = #ker(f) • P`. Final step: `natCast_zsmul`.
- **Hypotheses**: `IsAlgClosed F`, `IsDedekindDomain`, `IsIntegrallyClosed`, `ProjOrdTransport φ`, surjective `φ`, finite kernel.
- **Uses from project**: `divisorPushforwardDual`, `mulByInt_apply`, `Curves.picZeroIsoE_allChar`, `Curves.kappaDivisor`, `Curves.kappaDivisor_degree`, `pullbackPicZero_mk`, `picZeroIsoE_allChar_mk`, `pullbackDegZero_coe`, `sigma_pullbackDivisor_kappaDivisor`
- **Used by**: `mkOneSubScalingDataConcrete_of_divisorDual` (lines 383–385); also used by `PencilDualDivisor.lean`
- **Visibility**: public
- **Lines**: 278–297; proof length: ~19 lines
- **Notes**: This is the central theorem of the file. The σ-bridge (`sigma_pullbackDivisor_kappaDivisor`) makes the dual relation automatic — no characteristic polynomial needed.

---

### `noncomputable local instance instDecEqACDiv`

- **Type**: `DecidableEq (AlgebraicClosure K)` (via `Classical.decEq`)
- **What**: Provides classical decidable equality for the algebraic closure `K̄`, needed for downstream definitional machinery in the `Assemble` section.
- **How**: `Classical.decEq _`
- **Hypotheses**: None beyond type.
- **Uses from project**: None
- **Used by**: Implicitly used by `mkOneSubScalingDataConcrete_of_divisorDual` and `oneSubFrobeniusScaling_of_divisorDual` via `AlgebraicClosure K`
- **Visibility**: local
- **Lines**: 317; 1 line
- **Notes**: Standard classical instance boilerplate for algebraic closure.

---

### `noncomputable def mkOneSubScalingDataConcrete_of_divisorDual`

- **Type**: `mkOneSubScalingDataConcrete_of_divisorDual (hq : 2 ≤ Fintype.card K) (hdeg_eq : ...) (hproj : ...) (hsurj : ...) (hcomm' : ...) : OneSubScalingData W p r (AlgebraicClosure K) hq`
- **What**: Assembles the full `OneSubScalingData` bundle for `(1 − π)_{K̄}` using the divisor-pushforward dual `δ = divisorPushforwardDual` and dual relation `divisorPushforwardDual_comp` (σ-bridge, automatic), rather than the char-poly dual. The `hdc` field of the data is discharged automatically.
- **How**: Calls `mkOneSubScalingDataConcrete` with: finite kernel from `oneSubFrobeniusIsogBaseChange_finiteKer`, `hproj`, `δ = divisorPushforwardDual ...`, `hdc = divisorPushforwardDual_comp ...`, `hsurj`, `hkerdeg` from `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`, and `hcomm'`.
- **Hypotheses**: `K` finite field, `p` prime characteristic, `r` exponent, `hq : 2 ≤ #K`, V.1.3 degree identity `hdeg_eq`, `ProjOrdTransport`, surjectivity over `K̄`, translation covariance `hcomm'`.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`, `oneSubFrobeniusIsogBaseChange_finiteKer`, `mkOneSubScalingDataConcrete`, `divisorPushforwardDual`, `divisorPushforwardDual_comp`, `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`
- **Used by**: `oneSubFrobeniusScaling_of_divisorDual` (line 441)
- **Visibility**: public
- **Lines**: 339–389; definition body: ~50 lines (signature is very long due to `hcomm'` verbosity)
- **Notes**: Proof >30 lines (counting the `haveI` plus the `mkOneSubScalingDataConcrete` call). The long signature is driven entirely by the verbose `hcomm'` hypothesis spelling out the full translation covariance.

---

### `theorem oneSubFrobeniusScaling_of_divisorDual`

- **Type**: `oneSubFrobeniusScaling_of_divisorDual (hq : 2 ≤ Fintype.card K) (hdeg_eq : ...) (hproj : ...) (hsurj : ...) (hcomm' : ...) : OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq`
- **What**: Discharges `OneSubFrobeniusScaling` (leaf 2 of `FrobBaseChangeScalings`, the Weil-pairing scaling `e_ℓ((1−π)S,(1−π)T) = e_ℓ(S,T)^{deg(1−π)}`)) via the divisor-pushforward dual — no CoordHom, no characteristic polynomial.
- **How**: Single call to `oneSubFrobeniusScaling_of_data W p r (AlgebraicClosure K) hq` applied to the `OneSubScalingData` assembled by `mkOneSubScalingDataConcrete_of_divisorDual`.
- **Hypotheses**: Same as `mkOneSubScalingDataConcrete_of_divisorDual`.
- **Uses from project**: `oneSubFrobeniusScaling_of_data`, `mkOneSubScalingDataConcrete_of_divisorDual`
- **Used by**: `SeparableTransportBridge.lean` (line 349), `OneSubProjOrdTransport.lean` (line 114); **unused within this file** (dead-code candidate within file; the main export to other files)
- **Visibility**: public
- **Lines**: 408–441; proof length: 2 lines
- **Notes**: The long *signature* (lines 408–439) mirrors `mkOneSubScalingDataConcrete_of_divisorDual` exactly. Proof itself is trivial. This is the main export of the file.
