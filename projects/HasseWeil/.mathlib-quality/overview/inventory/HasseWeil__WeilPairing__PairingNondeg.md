# Inventory: ./HasseWeil/WeilPairing/PairingNondeg.lean

**File purpose**: Proves **nondegeneracy of the finite-level Weil pairing in the second slot** (Silverman III.8.1c): over `K̄`, if `e_ℓ(S,T) = 1` for all `S ∈ E[ℓ]` then `T = O`. The argument assembles four ingredients: (1) the single deep geometric input `[ℓ]` is surjective on `E(K̄)` (III.4.10b) via division polynomials; (2) injectivity of the divisor pullback `[ℓ]^*`; (3) Abel–Jacobi `(T) ∼ (O) ⟹ T = O` (III.3.3); (4) the Galois fixed-field step "every `[ℓ]^*K(E)`-automorphism is a translation" (III.4.10c) reusing the `SeparableKernelTorsor` torsor. This is one of the four core structural properties of `e_ℓ` (the others — bilinearity, alternating — are in `Pairing.lean`/`PairingProps.lean`); together they feed the det=deg residual in `DetDeg`.

**Imports**: `HasseWeil.WeilPairing.Pairing`, `HasseWeil.WeilPairing.PairingProps`, `HasseWeil.WeilPairing.DivisorPullback`, `HasseWeil.WeilPairing.TorsionCardEll`, `HasseWeil.EC.SeparableKernelTorsor`, `HasseWeil.Curves.MillerAllChar`

**Total declarations**: 7 `theorem`

**Module options**: `set_option linter.unusedSectionVars false`, `linter.unusedDecidableInType false`, `linter.style.longLine false`. No `sorry`, no `maxHeartbeats`.

**Standing hypotheses** (whole file): `{F : Type*} [Field F] [DecidableEq F]`, `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]`; the single `Nondeg` section additionally has `[IsAlgClosed F]`.

---

## Declarations

### `theorem mulByInt_point_surjective`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) : Function.Surjective (mulByInt W.toAffine ℓ).toAddMonoidHom`
- **What**: **`[ℓ] : E(K̄) → E(K̄)` is surjective** (Silverman III.4.10b: a nonzero isogeny is surjective on `K̄`-points). The one genuinely-geometric input of nondegeneracy.
- **How**: Elementary division-polynomial route. For `Q = (x_Q, y_Q)`, a preimage's `x`-coordinate is a root of the monic degree-`ℓ²` fibre polynomial `g := Φ_ℓ − x_Q·Ψ²_ℓ`, which splits over `K̄` (`IsAlgClosed.exists_root`). Monicity/degree from `leadingCoeff_Φ`, `natDegree_Φ`, `natDegree_ΨSq_le`, `Polynomial.natDegree_sub_eq_left_of_natDegree_lt`. A root `x₀` lifts to a curve point `(x₀, y₀)` (`exists_point_on_curve`); `Ψ²_ℓ(x₀) ≠ 0` is forced by coprimality `isCoprime_Φ_ΨSq` (so `ψ_ℓ(x₀,y₀) ≠ 0`). The forward formula `zsmul_affine_point_eq_gen` gives `x([ℓ]·(x₀,y₀)) = Φ_ℓ(x₀)/Ψ²_ℓ(x₀) = x_Q`, so by `Y_eq_of_X_eq` either `(x₀,y₀)` or `−(x₀,y₀)` is a preimage of `Q` (`negY_negY`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0` (and `[IsElliptic]` so `Δ ≠ 0`).
- **Uses from project**: `mulByInt` (mulByInt API; `mulByInt_apply`), `isCoprime_Φ_ΨSq`, `leadingCoeff_Φ`, `natDegree_Φ`, `natDegree_ΨSq_le`, `exists_point_on_curve`, `ΨSq_eval_eq_psi_sq`, `zsmul_affine_point_eq_gen`, `evalEval_φ_eq_Φ`, `Y_eq_of_X_eq`, `negY_negY` (division-polynomial / curve-arithmetic API)
- **Used by (within file)**: `pullbackDivisor_injective`. **Used by (project)**: `PicDualDivisorClassLemma`, `SeparableWitnesses`, `OneSubWitnesses`.
- **Visibility**: public
- **Lines**: 97–179, proof length: ~82 lines
- **Notes**: Proof >30 lines (the longest in the file). This is the load-bearing geometric fact; well-isolated as a single lemma.

### `theorem pullbackDivisor_injective`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] : Function.Injective (pullbackDivisor [ℓ] hker)`
- **What**: **The divisor pullback `[ℓ]^*` is injective** over `K̄`.
- **How**: At any place `w`, `pullbackDivisor_apply` reads `D` at the image place `(ℓ·w.toAffine).proj`. Since `[ℓ]` is surjective on points (`mulByInt_point_surjective`), every place `v` arises as such an image (taking `w = P.toProjectiveSmoothPoint` for a preimage `P`), so `pullbackDivisor [ℓ] D` determines every coefficient of `D`; concludes by `Finsupp.ext`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `Finite ker[ℓ]`.
- **Uses from project**: `mulByInt_point_surjective` (this file), `pullbackDivisor`, `pullbackDivisor_apply` (DivisorPullback), `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`, `Affine.Point.toAffinePoint_toProjectiveSmoothPoint`
- **Used by (within file)**: `weilPairing_nondegenerate`
- **Visibility**: public
- **Lines**: 192–209, proof length: ~13 lines
- **Notes**: File-internal-only (used only in the final assembly).

### `theorem eq_zero_of_kappaDivisor_principal`
- **Type**: `{T : W.toAffine.Point} (hT : (⟨W.toAffine⟩).ProjIsPrincipal (Curves.kappaDivisor W.toAffine T)) : T = 0`
- **What**: **Abel–Jacobi** (Silverman III.3.3): if `(T) − (O)` is principal then `T = O`.
- **How**: A principal degree-`0` divisor has trivial `σ`-image (group sum) — supplied by the all-characteristics `afInputs_allChar W.toAffine`'s vanishing field `h_van` applied to the principal divisor (with `principal_mem_degZero`); and `σ((T) − (O)) = T` (`projectiveDivisorSum_kappaDivisor`). So the vanishing rewrites to `T = 0`.
- **Hypotheses**: `[IsAlgClosed F]`; `(T) − (O)` principal.
- **Uses from project**: `Curves.kappaDivisor`, `Curves.projectiveDivisorSum`, `Curves.projectiveDivisorSum_kappaDivisor`, `afInputs_allChar`, `SmoothPlaneCurve.principal_mem_degZero` (Curves / PicZero chain)
- **Used by (within file)**: `weilPairing_nondegenerate`
- **Visibility**: public
- **Lines**: 221–229, proof length: ~6 lines
- **Notes**: File-internal-only.

### `theorem aut_eq_translate`
- **Type**: `(ℓ : ℤ) (hℓ0 : ℓ ≠ 0) (σ : AlgEquiv KE KE …[ℓ]-algebra…) : ∃ k, ℓ • k = 0 ∧ ∀ z, σ z = translateAlgEquivOfPoint W k z`
- **What**: **Every `[ℓ]^*K(E)`-automorphism of `K(E)` is a translation by an `ℓ`-torsion point** (the geometric content of `Aut(K(E)/[ℓ]^*K(E)) ≃ ker[ℓ]`, Silverman III.4.10c).
- **How**: Uses the covariance `hcov_mulByInt_of_xy` and the resulting `kernelTranslateForwardAut` (the torsor's forward map). The descent torsor `hdesc_mulByInt` supplies the kernel point `k = σ(P_gen) − P_gen` with `[ℓ]k = 0` (`Isogeny.mem_kernel_iff`). The forward automorphism `forward ⟨k,_⟩` acts on the generic point as `P_gen + lift k = genericPointAct σ` (`genericPointAct_kernelTranslateForwardAut`, `sub_add_cancel`); reading coordinate agreement on `x_gen, y_gen` (`genericPointAct_eq_some`) and extending to all of `K(E)` via `algHom_ext_x_y_gen`.
- **Hypotheses**: `[IsAlgClosed F]`, `ℓ ≠ 0`.
- **Uses from project**: `mulByInt` (`.toAlgebra`), `hcov_mulByInt_of_xy`, `hxy_mulByInt`, `kernelTranslateForwardAut`, `hdesc_mulByInt`, `Isogeny.mem_kernel_iff`, `genericPointAct`, `genericPointAct_kernelTranslateForwardAut`, `genericPointAct_eq_some`, `x_gen`, `y_gen`, `algHom_ext_x_y_gen`, `translateAlgEquivOfPoint` (SeparableKernelTorsor / generic-point API)
- **Used by (within file)**: `mem_pullback_range_of_translate_fixed`
- **Visibility**: public
- **Lines**: 243–273, proof length: ~26 lines
- **Notes**: File-internal-only. Reconstructs the surjectivity half of the torsion-torsor bijection.

### `theorem mem_pullback_range_of_translate_fixed`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) {g : KE} (hg : ∀ S, ℓ • S = 0 → translateAlgEquivOfPoint W S g = g) : ∃ h, (mulByInt W.toAffine ℓ).pullback h = g`
- **What**: **`g` fixed by all `ℓ`-translations lies in `[ℓ]^*K(E)`**: if `τ_S g = g` for every `S ∈ E[ℓ]` then `g = [ℓ]^* h`.
- **How**: Installs the Galois/finite-dimensional structure on `K(E)/[ℓ]^*K(E)` (`isogeny_finiteDimensional`, `Isogeny.isGalois_of_isSeparable_and_normal` from `mulByInt_isSeparable` + `h_normal_mulByInt`). By `aut_eq_translate`, every automorphism is a translation, so `g` is fixed by every `σ`; hence `g ∈ (⊥ : IntermediateField)` (`IsGalois.mem_bot_iff_fixed`), and `IntermediateField.mem_bot` gives `g = algebraMap (= [ℓ].pullback) h`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `mulByInt` (`.toAlgebra`, `.pullback`), `isogeny_finiteDimensional`, `Isogeny.isGalois_of_isSeparable_and_normal`, `mulByInt_isSeparable`, `h_normal_mulByInt`, `aut_eq_translate` (this file), `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_nondegenerate`
- **Visibility**: public
- **Lines**: 285–308, proof length: ~19 lines
- **Notes**: File-internal-only.

### `theorem pullbackDivisor_kappaDivisor`
- **Type**: `(ℓ : ℤ) [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] (T : W.toAffine.Point) : pullbackDivisor [ℓ] hker (kappaDivisor W.toAffine T) = pullbackDiv [ℓ] hker T − pullbackDiv [ℓ] hker 0`
- **What**: The fibre-pullback `[ℓ]^*` of the Abel–Jacobi divisor `(T) − (O)` equals the divisor of `g_T`, namely `[ℓ]^*(T) − [ℓ]^*(O)`.
- **How**: Unfolds `kappaDivisor` and pushes `pullbackDivisor` through the subtraction (`pullbackDivisorHom_apply`, `map_sub`, `pullbackDivisor_single`, `one_smul`), using `∞.toAffinePoint = O` (`toAffinePoint_infinity`) and the round-trip `toProjectiveSmoothPoint_toAffinePoint`.
- **Hypotheses**: `Finite ker[ℓ]`. (No `[IsAlgClosed F]` is used in the body — placed in the `[IsAlgClosed F]` section but the statement is characteristic-agnostic.)
- **Uses from project**: `pullbackDivisor`, `pullbackDivisorHom_apply`, `pullbackDivisor_single` (DivisorPullback), `pullbackDiv` (Pullback), `Curves.kappaDivisor`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`, `ProjectiveSmoothPoint.toAffinePoint_infinity`
- **Used by (within file)**: `weilPairing_nondegenerate`. **Used by (project)**: `OneSubDualDivisor`, `FrobMatrixData`, `PicDualDivisorClassLemma`, `HfactLemma`, `SeparableScaling`.
- **Visibility**: public
- **Lines**: 315–324, proof length: ~3 lines
- **Notes**: Body uses no `[IsAlgClosed F]`; could be moved/stated outside the `Nondeg` section (minor generalisation — see summary).

### `theorem weilPairing_nondegenerate`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) (h_deg : ∀ S, (hS : ℓ • S = 0) → weilPairing W ℓ hℓ S T hS hT = 1) : T = 0`
- **What**: **Nondegeneracy of the Weil pairing** (Silverman III.8.1c): if `e_ℓ(S,T) = 1` for every `S ∈ E[ℓ]`, then `T = O`.
- **How**: The hypothesis + `weilPairing_translate` give `τ_S g_T = g_T` for all `S ∈ E[ℓ]`, so `g_T = [ℓ]^* h` (`mem_pullback_range_of_translate_fixed`); `h ≠ 0` since `g_T ≠ 0`. Then `[ℓ]^*(div h) = div([ℓ]^* h) = div(g_T)` (`projectiveDivisorOf_pullback_eq_pullbackDivisor` via `projOrdTransport_mulByInt`) and `div(g_T) = [ℓ]^*((T)−(O))` (`weilFunction_divisor` + `pullbackDivisor_kappaDivisor`); injectivity of `[ℓ]^*` (`pullbackDivisor_injective`) yields `div h = (T) − (O)`, so `(T) − (O)` is principal and `T = O` by Abel–Jacobi (`eq_zero_of_kappaDivisor_principal`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`, and `e_ℓ(·,T) ≡ 1` on `E[ℓ]`.
- **Uses from project**: `mulByInt_ker_finite` (Pairing), `ProjOrdTransport`/`projOrdTransport_mulByInt`, `weilPairing_translate`, `mem_pullback_range_of_translate_fixed` (this file), `weilFunction`/`weilFunction_ne_zero`/`weilFunction_divisor` (Pairing), `projectiveDivisorOf_pullback_eq_pullbackDivisor` (DivisorPullback), `pullbackDivisor`, `pullbackDivisor_kappaDivisor`/`pullbackDivisor_injective`/`eq_zero_of_kappaDivisor_principal` (this file), `Curves.kappaDivisor`, `translateAlgEquivOfPoint`
- **Used by (within file)**: none. **Used by (project)**: `DetDeg` (the nondegeneracy input to det=deg / symplectic adjoint).
- **Visibility**: public
- **Lines**: 336–372, proof length: ~31 lines
- **Notes**: Proof slightly >30 lines (the final assembly).

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `mulByInt_point_surjective` | `pullbackDivisor_injective` (+ project: PicDualDivisorClassLemma, SeparableWitnesses, OneSubWitnesses) |
| `pullbackDivisor_injective` | `weilPairing_nondegenerate` |
| `eq_zero_of_kappaDivisor_principal` | `weilPairing_nondegenerate` |
| `aut_eq_translate` | `mem_pullback_range_of_translate_fixed` |
| `mem_pullback_range_of_translate_fixed` | `weilPairing_nondegenerate` |
| `pullbackDivisor_kappaDivisor` | `weilPairing_nondegenerate` (+ project: OneSubDualDivisor, FrobMatrixData, …) |
| `weilPairing_nondegenerate` | (project: DetDeg) |

**Key API** (live exports): `weilPairing_nondegenerate` (the file's headline result → DetDeg), `mulByInt_point_surjective` (the geometric input, reused by several scaling-witness files), `pullbackDivisor_kappaDivisor` (reused broadly).

## Notes / cleanup analysis

- **(a) Unused within file**: none truly dead. `pullbackDivisor_injective`, `eq_zero_of_kappaDivisor_principal`, `aut_eq_translate`, `mem_pullback_range_of_translate_fixed` are file-internal scaffolding for the final theorem; `mulByInt_point_surjective`, `pullbackDivisor_kappaDivisor`, `weilPairing_nondegenerate` are exported and used elsewhere.
- **(b) No scratch/superseded content** — every declaration is on the live nondegeneracy path. The file is well-factored: one lemma per conceptual step (geometry → divisor injectivity → Abel–Jacobi → Galois → assembly).
- **(c) mathlib-fit — POSITIVE**: correctly reuses mathlib's Galois API (`IsGalois`, `IsGalois.mem_bot_iff_fixed`, `IntermediateField.mem_bot`, `FiniteDimensional`) rather than hand-rolling. No custom nondegeneracy predicate — nondegeneracy is stated as the plain implication `(∀ S, e_ℓ(S,T)=1) → T=O`, which is appropriate (mathlib has no off-the-shelf "nondegenerate pairing on a finite torsion module" API that fits the `weilPairing`'s dependent-hypothesis signature).
- **(d) Moral duplication (cross-file)**: `mulByInt_point_surjective` here vs `Pairing.mulByEllTorsionHom_surjective` — two surjectivity facts about `[ℓ]`; the present one (full, via division polynomials) is strictly stronger and could in principle subsume the cardinality version used in `Pairing.lean` (see Pairing.md note (d)).
- **(e) Generalisation**: `pullbackDivisor_kappaDivisor` (L315) uses no `[IsAlgClosed F]` in its proof yet sits inside the `[IsAlgClosed F]` `Nondeg` section; it could be hoisted out of the section (or `omit`) to make the weaker hypothesis explicit. Cosmetic.
- **No `sorry`, no `maxHeartbeats`.** Long proofs: `mulByInt_point_surjective` (~82 lines), `weilPairing_nondegenerate` (~31 lines), `aut_eq_translate` (~26 lines).
