# [a5] `locallyWeierstrass_quotientπ` — turnkey assembly plan (fable-P4, beastmode)

The KM 4.7 ⇐-engine's last leaf. **Every ingredient below is identified and (except the two
starred) landed + lake-verified.** Goal: `LocallyWeierstrass π' zero' hz` for the quotient curve
`E/G → X/G`, `X = Spec A` affine, `X/G = Spec Aᴳ`.

## Landed + verified (this session)
- **Algebraic descent** (`WeierstrassInvariant.lean`): `exists_coboundary` (non-abelian H¹ vanishing,
  Aᴳ local) → `exists_invariant_descent` (given `IsVCocycle C` + `haction`, produces `W₁` over Aᴳ with
  `W₁.map(Aᴳ↪A) = E⁻¹•W₀`). AXIOM-CLEAN.
- **a5-ii pointed iso** (`QuotientCurveModel.lean`): `projModelZero_baseChange_hom`,
  `cartesianIso_hom_π`, `cartesianIso_hom_zero`, `exists_vc_of_curveAction` — per-g extraction of `C_g`
  from `IsCurveAction` (cartesian+π+zero) via `pointedIso_exists_variableChange`.
- **Cocycle infrastructure**: `projModelBaseChange_comp` (WeierstrassModel.lean, functoriality),
  `projModelVCIso_map_hom`, `isIso_projModelBaseChange`, `isIso_specMap_toRingHom`,
  `map_toRingHom_mul`, `vc_mul_smul_eq` (cardinality half of cocycle).
- **Cocycle geometric half** (`isVCocycle_of_curveActionFamily`, hh): fully derived; being closed
  (background agent) — combines projModelVCIso_mul/_map_hom/_injective + baseChange_comp + hmul, β iso ⇒
  cancel_mono.

## Remaining assembly (all infra exists)
1. **`isVCocycle_of_curveActionFamily`** — cocycle from a family `act : G → (projModel W₀ ⟶ projModel W₀)`
   (hmul/hcart/hzero). [agent finishing hh]
2. **Transport (a5-P2)**: for `s : X/G`, get σ-stable affine `Ũ ⊆ X` over affine `U ∋ s`
   (`exists_isStableOpen_isAffineOpen_mem` / `localQuotient`); `C.localModel` restricted to `Ũ` gives
   `W₀` over `Γ(X,Ũ)` with chart iso `pullback C.π Ũ.ι ≅ projModel W₀` (via `LocallyWeierstrass` + shrink
   to stable, `LocallyWeierstrass.baseChange`-style). `MulSemiringAction G Γ(X,Ũ)` = `gammaMulSemiringAction hŨ`.
   Transport `σE.hom g|Ũ` through the chart iso ⇒ `act g` on `projModel W₀`; hcart/hzero from
   `IsCurveAction.cartesian`/`zero_equivariant` transported. Feed to (1) ⇒ cocycle `C_g`.
3. **Localization/spread (a5-P-loc)**: `exists_invariant_descent` needs `Γ(X,Ũ)ᴳ` local. Use
   `InvariantLocalization.lean` (`away`, `awayHom`, `mem_range_fixedPoints_awayMap_iff`,
   `fixedPoints_awayMap_injective`): work at `Localization.Away h` for `h ∈ Γ(X,Ũ)ᴳ`, `(A_h)ᴳ = (Aᴳ)_h`;
   the coboundary `E` + `W₁` spread from the local ring to a basic open `D(h)`. `U := D(h)`,
   `Γ(X/G,U) = (Aᴳ)_h`.
4. **fppf comparison (a5-P-fppf)**: `E/G|_U ≅ projModel W₁` over `U`. From `projModel_descentIso`
   (`projModel W₀ ≅ (projModel W₁)×_{Spec Aᴳ}Spec A`) + `isPullback_quotientπ` (`E ≅ (E/G)×_{X/G}X`) via
   `of_isPullback_of_descendsAlong` (mathlib `isomorphisms.DescendsAlong (Surjective⊓Flat⊓QuasiCompact)`;
   `X→X/G` is fppf via `epi_localQuotientπ`+`etale_quotientπ`). G-invariance of the comparison ⇐ a5-ii.
5. **Package**: assemble `⟨U, hsU, W₁, W₁.IsElliptic, e, heπ, hez⟩` into `LocallyWeierstrass`.

## Notes
- WeierstrassModel.lean edits verify ONLY via `lake build` (standalone `lean` mis-reports —
  section-local `GradedRing (homogeneousSubmodule (Fin 3) R)` instance).
- `SchemeAction`/`gammaMulSemiringAction`/`localQuotient` live in `AlgebraicGeometry` namespace
  (`ForMathlib/SchemeQuotient.lean`); not imported by QuotientCurveModel — the cocycle lemma takes the
  raw `act` family to stay decoupled.

## Update — verified scratch artifacts (ready to land) + refined transport structure
- **`exists_descended_model_of_curveActionFamily`** (cocycle→descent bridge): typechecks end-to-end
  (`combine_ready.lean`) — lands the moment `isVCocycle_of_curveActionFamily` compiles.
- **`SchemeAction.restrict`** (`restrict_ready.lean`, VERIFIED): restrict an action to a stable open
  → `SchemeAction G U.toScheme`; `hom g = (σ.hom g).resLE U U (hU.le_preimage g)`; fields via
  `resLE_comp_ι` + `cancel_mono U.ι`. Belongs in `SchemeQuotient.lean` (foundational — batch with
  the transport to avoid repeated downstream rebuilds).
- **Transport (a5-P2) refined**: the LocallyWeierstrass chart is `pullback C.π U.ι` (E over the base
  open U ⊆ X, U σ-stable), NOT an open subscheme of E. So the induced action is via
  `pullback.map (σE.hom g) ((σ.hom g).resLE U U _) …` using `IsCurveAction.π_equivariant`; then
  transport through the chart iso `pullback C.π U.ι ≅ projModel W₀` to get the raw `act` family
  (hmul from σE.hom_mul + pullback.map functoriality; hcart from `.cartesian`; hzero from
  `.zero_equivariant`). Base action = `gammaMulSemiringAction hU` on `Γ(X,U)`; its `toRingHom g`
  must match `Spec`-side of `(σ.hom g).resLE`/`isoSpec` (see `resLE_isoSpec_hom`,
  `specSMul_isoSpec_inv` in SchemeQuotient.lean).

## Session capstone target
Integrate the agent's `hh` → land `isVCocycle_of_curveActionFamily` + `exists_descended_model_of_curveActionFamily`.
That completes the **entire algebraic + cocycle spine** of KM 4.7 ⇐ (axiom-clean). The geometric
transport/localization/fppf/package (a5-P2..P6) is the honest next arc.
