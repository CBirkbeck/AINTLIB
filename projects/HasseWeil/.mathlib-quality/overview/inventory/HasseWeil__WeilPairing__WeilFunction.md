# Inventory: ./HasseWeil/WeilPairing/WeilFunction.lean

**File purpose**: Step 1 of the Weil-pairing construction (Silverman III.8.1). Two distinct developments live here: (1) a **fibre-shift / translation-invariance** mini-API (`smul_add_torsion_eq_iff`, `fiberTranslateEquiv`) recording that translation by an `ℓ`-torsion point permutes the `[ℓ]`-fibre; (2) the **Abel–Jacobi divisor existence** machinery: the diagonal Weil divisor `D_T := ℓ(T) − ℓ(O)` with its degree/`σ` facts, the general Abel–Jacobi extraction `degree-0 + σ=O ⟹ principal` (`projIsPrincipal_of_degZero_of_sigma_eq_zero`), and the **fibre-difference** principality `pullbackDiv_sub_isPrincipal` that `Pairing.lean` actually uses to build `weilFunction`. As the cross-reference analysis shows, the diagonal `D_T` development (`weilDivisor` + `weilFunction_exists`) was the *original* existence route and is now **superseded** by the fibre-difference route; only `projIsPrincipal_of_degZero_of_sigma_eq_zero` and `pullbackDiv_sub_isPrincipal` are live.

**Imports**: `HasseWeil.Curves.PicZero`, `HasseWeil.Curves.MillerAllChar`, `HasseWeil.Curves.EffectiveSumReduce`, `HasseWeil.WeilPairing.Pullback`, `HasseWeil.WeilPairing.SigmaBridge`

**Total declarations**: 9 (1 `def`, 1 `noncomputable def`, 7 `theorem`)

**Module options**: `set_option linter.unusedSectionVars false`. No `sorry`, no `maxHeartbeats`.

**Standing hypotheses** (whole file): `{F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]`. The Abel–Jacobi theorems additionally require `[IsIntegrallyClosed (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing]`.

---

## Declarations

### `theorem smul_add_torsion_eq_iff`
- **Type**: `{ℓ : ℤ} {S : W.Point} (hS : ℓ • S = 0) (T Q : W.Point) : ℓ • (Q + S) = T ↔ ℓ • Q = T`
- **What**: **The `[ℓ]`-fibre is invariant under translation by `S ∈ E[ℓ]`**: for `ℓ•S = 0`, `ℓ•(Q+S) = T ↔ ℓ•Q = T`.
- **How**: `smul_add`, `hS`, `add_zero`.
- **Hypotheses**: `ℓ • S = 0`.
- **Uses from project**: none (pure smul algebra)
- **Used by (within file)**: `fiberTranslateEquiv`. **Used by (project)**: only referenced in a *comment* in `DivisorTranslate.lean` (no real use).
- **Visibility**: public
- **Lines**: 36–38, proof length: 1 line
- **Notes**: Used only to build `fiberTranslateEquiv` (itself dead — see below).

### `def fiberTranslateEquiv`
- **Type**: `{ℓ : ℤ} {S : W.Point} (hS : ℓ • S = 0) (T : W.Point) : {Q // ℓ • Q = T} ≃ {Q // ℓ • Q = T}`
- **What**: The `[ℓ]`-fibre over `T` maps to itself bijectively under `· + S` for `S ∈ E[ℓ]`. The geometric reason the pairing value `e_ℓ(S,T) = (τ_S^*g)/g` is constant.
- **How**: `Equiv.subtypeEquiv (Equiv.addRight S)` with the membership equivalence `smul_add_torsion_eq_iff`.
- **Hypotheses**: `ℓ • S = 0`.
- **Uses from project**: `smul_add_torsion_eq_iff` (this file)
- **Used by (within file)**: none. **Used by (project)**: only a *comment* in `DivisorTranslate.lean`.
- **Visibility**: public
- **Lines**: 44–46, proof length: 1 line
- **Notes**: **Dead declaration.** No real consumer anywhere; the actual translation-invariance used by the live pairing construction (`DivisorTranslate`, `projectiveDivisorOf_translate_weilFunction_div_eq_zero`) is proven by a different route and only *mentions* this equiv in a docstring. Removal candidate (together with `smul_add_torsion_eq_iff` if that lemma is not wanted standalone).

### `noncomputable def weilDivisor`
- **Type**: `(T : W.Point) (ℓ : ℤ) : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F)`
- **What**: **The diagonal Weil divisor** `D_T := ℓ·(T) − ℓ·(O)` (projective).
- **How**: `Finsupp.single T.proj ℓ − Finsupp.single O.proj ℓ`.
- **Hypotheses**: none.
- **Uses from project**: `Affine.Point.toProjectiveSmoothPoint`
- **Used by (within file)**: `degree_weilDivisor`, `sigma_weilDivisor`, `weilDivisor_sigma_eq_zero`, `weilFunction_exists`. **Used by (project)**: referenced in *comments/docstrings* of `DivisorTranslate` and `DivisorPullback` (`pullbackDivisor_weilDivisor` mentions it), but **not used as a term** by any live proof.
- **Visibility**: public
- **Lines**: 50–53, proof length: ~2 lines (def)
- **Notes**: Part of the superseded diagonal-divisor existence route (see summary (b)). Distinct from the fibre-difference `pullbackDiv [ℓ] T − pullbackDiv [ℓ] O` that `Pairing.weilFunction` actually uses.

### `theorem degree_weilDivisor`
- **Type**: `(T : W.Point) (ℓ : ℤ) : (weilDivisor T ℓ).degree = 0`
- **What**: `deg D_T = 0` (`ℓ − ℓ`).
- **How**: `degreeHom`/`map_sub` + `degree_single` (Pullback) twice + `sub_self`.
- **Hypotheses**: none (`[DecidableEq F]` omitted).
- **Uses from project**: `weilDivisor` (this file), `Curves.ProjectiveDivisor.degreeHom_apply`, `degree_single` (Pullback)
- **Used by (within file)**: `weilFunction_exists`. **Used by (project)**: none.
- **Visibility**: public
- **Lines**: 56–61, proof length: ~3 lines

### `theorem sigma_weilDivisor`
- **Type**: `(T : W.Point) (ℓ : ℤ) : Curves.projectiveDivisorSum W (weilDivisor T ℓ) = ℓ • T`
- **What**: `σ(D_T) = ℓ • T` (the group sum of the diagonal Weil divisor).
- **How**: `projectiveDivisorSum_sub` + `projectiveDivisorSum_single` twice + `toProjectiveSmoothPoint_toAffinePoint` + `smul_zero`/`sub_zero`.
- **Hypotheses**: none.
- **Uses from project**: `weilDivisor` (this file), `Curves.projectiveDivisorSum_sub`/`projectiveDivisorSum_single`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`
- **Used by (within file)**: `weilDivisor_sigma_eq_zero`. **Used by (project)**: none.
- **Visibility**: public
- **Lines**: 64–68, proof length: ~3 lines

### `theorem weilDivisor_sigma_eq_zero`
- **Type**: `(T : W.Point) (ℓ : ℤ) (hT : ℓ • T = 0) : Curves.projectiveDivisorSum W (weilDivisor T ℓ) = 0`
- **What**: For `T ∈ E[ℓ]`, `σ(D_T) = O` — the Abel–Jacobi prerequisite for `D_T` to be principal.
- **How**: `sigma_weilDivisor` then rewrite by `hT`.
- **Hypotheses**: `ℓ • T = 0`.
- **Uses from project**: `weilDivisor`, `sigma_weilDivisor` (this file), `Curves.projectiveDivisorSum`
- **Used by (within file)**: `weilFunction_exists`. **Used by (project)**: none.
- **Visibility**: public
- **Lines**: 73–75, proof length: 1 line

### `theorem projIsPrincipal_of_degZero_of_sigma_eq_zero`
- **Type**: `[IsIntegrallyClosed (⟨W⟩).CoordinateRing] (D : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F)) (hdeg : D.degree = 0) (hsig : Curves.projectiveDivisorSum W D = 0) : (⟨W⟩ : Curves.SmoothPlaneCurve F).ProjIsPrincipal D`
- **What**: **Abel–Jacobi extraction**: a degree-`0` projective divisor with `σ(D) = O` is principal.
- **How**: From `divZeroReduce_holds_allChar` (the all-characteristics `D ∼ (σD) − (O)`, axiom-clean, needing only `IsIntegrallyClosed` of the coordinate ring), specialised at `σD = O` where `(O) − (O) = 0` (`kappaDivisor_zero`); `simpa [ProjLinearlyEquiv]`.
- **Hypotheses**: `IsIntegrallyClosed` of the coordinate ring; `deg D = 0`; `σ D = O`.
- **Uses from project**: `Curves.divZeroReduce_holds_allChar`, `Curves.ProjectiveDivisor.mem_degZero`, `Curves.kappaDivisor_zero`, `Curves.SmoothPlaneCurve.ProjLinearlyEquiv`, `Curves.projectiveDivisorSum`
- **Used by (within file)**: `weilFunction_exists`, `pullbackDiv_sub_isPrincipal`. **Used by (project)**: `PicDualDivisorClassLemma`, `SeparableScaling`, `PairingProps` (`bilinDivisor_isPrincipal`).
- **Visibility**: public
- **Lines**: 87–95, proof length: ~4 lines
- **Notes**: **Live, broadly reused** — the general "degree-0 + σ=O ⟹ principal" Abel–Jacobi lemma. The key export of this file alongside `pullbackDiv_sub_isPrincipal`.

### `theorem weilFunction_exists`
- **Type**: `[IsIntegrallyClosed (⟨W⟩).CoordinateRing] (T : W.Point) (ℓ : ℤ) (hT : ℓ • T = 0) : (⟨W⟩ : Curves.SmoothPlaneCurve F).ProjIsPrincipal (weilDivisor T ℓ)`
- **What**: **The diagonal Weil function exists** (Silverman III.8.1): for `T ∈ E[ℓ]`, the divisor `ℓ(T) − ℓ(O)` is principal.
- **How**: `projIsPrincipal_of_degZero_of_sigma_eq_zero` applied to `weilDivisor T ℓ` with `degree_weilDivisor` and `weilDivisor_sigma_eq_zero`.
- **Hypotheses**: `IsIntegrallyClosed` coordinate ring; `ℓ • T = 0`.
- **Uses from project**: `projIsPrincipal_of_degZero_of_sigma_eq_zero`, `weilDivisor`, `degree_weilDivisor`, `weilDivisor_sigma_eq_zero` (this file)
- **Used by (within file)**: none. **Used by (project)**: none.
- **Visibility**: public
- **Lines**: 100–105, proof length: ~3 lines
- **Notes**: **Dead declaration** (no consumer anywhere). This is the *diagonal*-divisor existence statement; `Pairing.lean` builds `weilFunction` from the *fibre-difference* divisor via `pullbackDiv_sub_isPrincipal` instead. Superseded — removal candidate (along with the whole `weilDivisor` cluster it depends on).

### `theorem pullbackDiv_sub_isPrincipal`
- **Type**: `[IsIntegrallyClosed (⟨W⟩).CoordinateRing] (f : W.Point →+ W.Point) (h_ker : Finite f.ker) {T P₀ : W.Point} (hP₀ : f P₀ = T) (hann : Nat.card f.ker • P₀ = 0) : (⟨W⟩ : Curves.SmoothPlaneCurve F).ProjIsPrincipal (pullbackDiv f h_ker T − pullbackDiv f h_ker 0)`
- **What**: **The fibre-difference `g`-divisor is principal** (pairing step 3a): for an additive endomorphism `f` with finite kernel, a preimage `P₀` of `T`, and the annihilation `#ker(f)·P₀ = O`, the divisor `f*((T)) − f*((O))` is principal.
- **How**: `projIsPrincipal_of_degZero_of_sigma_eq_zero`: degree `#ker − #ker = 0` (via `degree_pullbackDiv` at `P₀` and at `0`), and `σ(f*((T)) − f*((O))) = #ker·P₀ = O` (via `sigma_pullbackDiv_sub` from `SigmaBridge`, rewritten by `hann`).
- **Hypotheses**: `IsIntegrallyClosed` coordinate ring; `f P₀ = T`; `#ker(f)·P₀ = O`.
- **Uses from project**: `projIsPrincipal_of_degZero_of_sigma_eq_zero` (this file), `pullbackDiv`/`degree_pullbackDiv` (Pullback), `Curves.ProjectiveDivisor.degreeHom_apply`, `Curves.projectiveDivisorSum_sub`, `sigma_pullbackDiv_sub` (SigmaBridge)
- **Used by (within file)**: none. **Used by (project)**: `Pairing.lean` (`weilFunction_isPrincipal` → defines `weilFunction`).
- **Visibility**: public
- **Lines**: 122–132, proof length: ~5 lines
- **Notes**: **Live, load-bearing** — this is the principality fact that the *actual* `weilFunction` rests on. Stated for a general `f` (good — instantiated at `[ℓ]` by `Pairing.lean`).

---

## Cross-reference summary

| Declaration | Used by (within file) | Used by (project) |
|---|---|---|
| `smul_add_torsion_eq_iff` | `fiberTranslateEquiv` | (comment only) |
| `fiberTranslateEquiv` | — | (comment only) — **dead** |
| `weilDivisor` | `degree_weilDivisor`, `sigma_weilDivisor`, `weilDivisor_sigma_eq_zero`, `weilFunction_exists` | (comment only) |
| `degree_weilDivisor` | `weilFunction_exists` | — |
| `sigma_weilDivisor` | `weilDivisor_sigma_eq_zero` | — |
| `weilDivisor_sigma_eq_zero` | `weilFunction_exists` | — |
| `projIsPrincipal_of_degZero_of_sigma_eq_zero` | `weilFunction_exists`, `pullbackDiv_sub_isPrincipal` | PicDualDivisorClassLemma, SeparableScaling, PairingProps |
| `weilFunction_exists` | — | — **dead** |
| `pullbackDiv_sub_isPrincipal` | — | Pairing |

**Key API** (live spine): `projIsPrincipal_of_degZero_of_sigma_eq_zero` (the general Abel–Jacobi extraction, reused widely) and `pullbackDiv_sub_isPrincipal` (the fibre-difference principality consumed by `Pairing.weilFunction`).

## Notes / cleanup analysis

- **(a/b) Superseded sub-route (the diagonal Weil divisor)**: `weilDivisor` (L50) and its dependent chain `degree_weilDivisor`, `sigma_weilDivisor`, `weilDivisor_sigma_eq_zero`, and the existence theorem `weilFunction_exists` (L100) have **no live consumers** — `weilDivisor` appears only in docstrings/comments elsewhere, and `weilFunction_exists` is used by nothing. This is the *original* "Weil function via `ℓ(T) − ℓ(O)`" existence route; the project ultimately builds `weilFunction` from the **fibre-difference** divisor (`pullbackDiv [ℓ] T − pullbackDiv [ℓ] O`, `pullbackDiv_sub_isPrincipal`), not from `weilDivisor`. **The entire `weilDivisor`/`weilFunction_exists` cluster (5 declarations) is a removal candidate** — keeping only `projIsPrincipal_of_degZero_of_sigma_eq_zero` and `pullbackDiv_sub_isPrincipal`. (Note: `weilDivisor` is referenced in a `DivisorPullback` docstring and the `pullbackDivisor_weilDivisor` lemma name there — those would need their prose updated, but no compile dependency.)
- **(b/c) Dead `fiberTranslateEquiv`**: `fiberTranslateEquiv` (L44) and its helper `smul_add_torsion_eq_iff` (L36) are an abandoned formalisation of the fibre-permutation intuition; only mentioned in a `DivisorTranslate` comment. The live translation-invariance is proved elsewhere. Removal candidates.
- **(c) mathlib-fit**: `weilDivisor` correctly uses `Finsupp.single`; `fiberTranslateEquiv` correctly uses `Equiv.subtypeEquiv`/`Equiv.addRight`. Nothing hand-rolled that mathlib provides — the issue is *deadness*, not mathlib-fit.
- **(e) Generalisation**: `projIsPrincipal_of_degZero_of_sigma_eq_zero` and `pullbackDiv_sub_isPrincipal` are stated at good generality (arbitrary divisor / arbitrary `f`); `weilDivisor`/`weilFunction_exists` are the specialised (and now unused) instances.
- **Net**: of 9 declarations, 2 are the live spine, 1 (`smul_add_torsion_eq_iff`) only feeds a dead def, and 6 form two dead/superseded sub-routes. This file is the strongest *deletion* opportunity in the cluster.
- **No `sorry`, no `maxHeartbeats`, no proof >30 lines.**
