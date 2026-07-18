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

## Update 2 — transport helpers LANDED (SchemeQuotient.lean, lake-verified)
`SchemeAction.transport` (iso conjugation), `SchemeAction.restrict` (→ U.toScheme via resLE),
`SchemeAction.pullbackChartAction` (induced action on `pullback π U.ι` via `pullback.map` of the
`π`-equivariant square). These are ALL the reusable transport infrastructure. The a5-P2 composite is
`(σE.pullbackChartAction hπ hU).transport chartIso : SchemeAction G (projModel W₀)` — its `hom g`
feeds `isVCocycle_of_curveActionFamily`. Remaining a5-P2 is engine-specific glue (no new helpers):
- **hcart/hzero** for the transported action: transport `IsCurveAction.cartesian`/`zero_equivariant`
  through `chartIso` (mathlib `IsPullback` iso-invariance) + the chart π-compat `heπ`.
- **base-map matching**: the transported base map = `Spec (gammaMulSemiringAction.toRingHom g)` via
  `resLE_isoSpec_hom` / `specSMul_isoSpec_inv` (SchemeQuotient.lean) — so `R := Γ(X,Ũ)` with its
  `gammaMulSemiringAction` is the `MulSemiringAction G R` the cocycle lemma needs.

## Cocycle status
`isVCocycle_of_curveActionFamily` (hh): bg agent one sorry from done — hΨ/hβ/hVC/hCurveOuter set up,
final `hcore` chain (projModelVCIso_mul + projModelVCIso_map_hom + hβ + hΨ g/h + hmul) in progress;
targeted hint sent. On completion → land it + `exists_descended_model_of_curveActionFamily`
(the algebraic+cocycle spine capstone).

## Update 3 — cocycle hh: down to ONE eqToHom-coherence sub-goal
`isVCocycle_of_curveActionFamily` proof is structurally complete (choose + hW + hΨ + hβ + hVC +
hCurveOuter + cancel_mono assembly all correct). The single remaining sub-goal is the `hcore` inner
step: `(projModelVCIso (C g * g•C h) Wgh).hom ≫ β_gh = eqToHom ≫ act (g*h)`, reduced (via
projModelVCIso_mul + hβ) to `(projModelVCIso (g•C h) Wgh).hom ≫ β_g^{Wh} ≫ β_h = eqToHom ≫ β_g ≫ act h`.
The ingredients — `projModelVCIso_map_hom (toRingHom g) (C h) Wh` (the middle), `hΨ h`, `hC h`, then
`hΨ g` + `hmul` for the outer — are ALL present and correct. The ONLY obstacle is an eqToHom SYNTACTIC
mismatch: `rw [← projModelVCIso_map_hom …]` won't fire because the goal's leading `eqToHom` (from
`projModelVCIso_mul`'s `by rw [mul_smul]`) differs syntactically from map_hom's (`by rw
[map_variableChange]`), though they are defeq (proof-irrelevant). Robust fixes to try:
`set Wg/Wh/Wgh` at proof top; or compose via `reassoc_of%` after `simp only [Category.assoc]` with
BOTH eqToHoms normalized; or prove the inner `key` with matching eqToHom by construction; or a single
`simp only [projModelVCIso_map_hom, hΨ, hC, hmul, eqToHom_trans, eqToHom_refl, Category.assoc,
Category.id_comp, Category.comp_id]` after projModelVCIso_mul. Background agent iterating on it.

## ============ PARKED (coordinator v10.8x dispatch, fable-P4) ============
Parked at clean boundary per fleet reprioritization to Y₁(N). The KM 4.7 engine serves Y(N)/Γ_H,
off the current critical path; the stitch resumes first on refocus. Nothing lost.

**BANKED, LANDED, AXIOM-CLEAN (committed):** the entire algebraic + cocycle spine of KM 4.7 ⇐ —
`exists_coboundary` → `exists_invariant_descent`; a5-ii pointed iso; `isVCocycle_of_curveActionFamily`
+ `exists_descended_model_of_curveActionFamily` (`[propext, Classical.choice, Quot.sound]`, NO
maxHeartbeats); `projModelBaseChange_comp`; the 3 `SchemeAction` transport helpers
(`transport`/`restrict`/`pullbackChartAction`, in SchemeQuotient.lean); EngineDescent imports the
capstone. Commit `194995f0b` is the capstone.

**BANKED, VERIFIED-BUT-UNLANDED (a5-banked/):**
- `curveAction_actionFamily-verified-statement.lean` — the a5-P2 transport lemma STATEMENT + `hmul`
  proven (hcart/hzero were `sorry`, agent was mid-proof). `TRANSPORT_SPEC.md` = the full hcart/hzero
  strategy (IsPullback.of_iso + resLE_isoSpec_hom; specSMul = Spec.map(ofHom toRingHom) defeq).
- `curveAction_actionFamily-agent-wip.lean` — the transport agent's in-progress hcart/hzero.
- `LOCALIZE_SPEC.md` + `localize-agent-wip.lean` — the a5-P-loc (invariant AtPrime localization +
  local descent + coefficient spread) strategy + agent WIP.

**ON REFOCUS — resume order:** (1) finish a5-P2 transport (hcart/hzero, banked statement + spec);
(2) a5-P-loc localized descent+spread (banked spec — needs AtPrime invariant-localization infra,
semilocal global model, two spreads); (3) a5-P-fppf (`of_isPullback_of_descendsAlong` +
`descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact` — verified to compose — +
`isPullback_quotientπ` + `projModel_descentIso`); (4) setup (`exists_mem_basicOpen_subset_of_stable`);
(5) top-level `locallyWeierstrass_quotientπ` assembly. Full architecture above.

## ============ UN-PARKED v10.94 — PHASE A IN FLIGHT ============
**Architecture of record:** Phase A = `locallyWeierstrass_quotientπ_of_globalModel` (the engine's
application supplies `φ : C.E ≅ projModel W₀` globally — the same hypothesis `exists_charts_of_globalModel`
already consumes; Hesse/Legendre models exist for the intended aux levels). Cleanly outside
[OWNER-FLW] (we never touch the fibrewise ⟷ LW comparison; strictly Weierstrass-model-side; noted
in EngineDescent's section docstring). The chartless boarded leaf consumes the FLW pin on landing
(fibrewise-ness of the quotient is easy from the cartesian square; the pin upgrades it) — cite,
never duplicate.

**Landed this arc (all lake-verified, committed):**
- `isStableOpen_top`, `ofHom_toRingHom_eq_appTop`, `hom_isoSpec_toRingHom` (base-matching),
  `isPullback_transport_globalModel`, `projModelZero_transport_globalModel`,
  `curveAction_actionFamily_of_globalModel`, `exists_cocycle_of_globalModel(')` — the a5-P2′
  global transport chained into the capstone, hΨ exposed against the concrete transport (944a2f96d,
  93628076c).
- `isVCocycle_of_curveActionFamily'` — capstone now exposes the hΨ link (needed: VariableChange
  stabilizers are nontrivial, so the link is not derivable downstream).
- `isIso_of_isPullback_of_fppf` (PullbackLocalAtTarget) + `fppf_invariantsπ` (SchemeActionFree) —
  the [a5-P-fppf] core (11ef2e0e4, cb31fae2a).
- `isUnit_subring_of_isUnit` + `isElliptic_of_map_isElliptic` (WeierstrassInvariant) — ellipticity
  descends (fixed-unit trick, no integrality).

**Interface decisions (binding):**
- The descent output MUST expose the coboundary identity `Cvc g = E * (g•E)⁻¹` (invariance of the
  comparison needs it; not derivable — stabilizers).
- STATEMENT FIX owed to the boarded [a5] leaf: `locallyWeierstrass_quotientπ` lacks the
  `hπ'c`/`hzero'c` compatibilities linking (π',zero') to the descended maps — false as stated for
  an arbitrary section-pair. Phase-A variant carries them; fix the leaf + call-site when closing.

**In flight (4 parallel agent blocks):**
- W1 localized descent + spread (+ coboundary exposure) — the a5-P-loc algebra.
- W2 `exists_quotientπ_lift_of_isOpenImmersion` (+ `epi_pullback_snd_quotientπ`) — restricted
  morphism descent, gluing `exists_invariantsπ_lift_of_isOpenImmersion` chart-wise.
- W5a `exists_quotientIsoSpec_top` — X/G ≅ Spec Γ(X,⊤)ᴳ compatibly with quotientπ (eqToHom
  ring-bridge along hVtop).
- W3 `descentComparison` (+ π/zero legs + G-invariance) — the abstract comparison; invariance via
  hE-collapse `Cvc g * (g•E⁻¹)⁻¹ = E`.

**Mine (after agents):** W4 (descended cmp's base change = the iso composite; cancel-epi +
isIso_of_isPullback_of_fppf), W5b (U' := qiso⁻¹(D(a)), Γ(X/G,U') ≅ (Aᴳ)_a via IsLocalization
uniqueness), W6 (top-level assembly; skeleton typechecks with all interfaces pinned —
tmp/toplevel.lean).

## W6 final route map (over Spec Aᴳ, via LocallyWeierstrass.of_iso — LANDED e873780bb)
Transport the LW goal along qiso (of_iso with eE = refl, eS = qiso; π'' := π' ≫ qiso.hom,
z'' := qiso.inv ≫ zero'). At a prime p of Aᴳ:
1. W1(p) ⟹ a ∉ p, W₁/(Aᴳ)_a, E', hW₁, coboundary.
2. Chart U := D(a); `IsLocalization.Away a Γ(Spec Aᴳ, D(a))` is a MATHLIB INSTANCE
   (AffineScheme.lean:645); W₁' := W₁.map (IsLocalization.algEquiv …).toRingHom;
   projModel-transport along ring equiv = isIso_projModelBaseChange.
3. Chart iso: `pullback (π'≫qiso.hom) (D a).ι ≅ (π'≫qiso.hom)⁻¹ᵁ(D a)` (mathlib
   pullbackRestrictIsoRestrict) ≪≫ asIso cmp, where cmp := W2-lift (j := that open's ι into E/G,
   Y := projModel W₁', f := the composite [restricted-quotient-square iso] ≫ [φ-restricted] ≫
   [projModel-basicOpen-restriction ≅ base change to A_a: isPullback_projModelBaseChange +
   D(f) ≅ Spec R_f] ≫ [descentComparison (W3)] ≫ [algEquiv transport]; invariance of f = W3's
   descentComparison_invariant + equivariance of the identification legs).
4. cmp iso (W4): restricted quotient square (paste isPullback_morphismRestrict around
   isPullback_quotientπ) + `pullback.snd ≫ cmp = f` (W2's compat) + f iso + cancel-epi ⟹ the
   base-changed square exhibits cmp's base change as an iso ⟹ isIso_of_isPullback_of_fppf
   (fppf leg: fppf_invariantsπ localized / base-change stability).
5. heπ/hez: descentComparison_π/_zero (W3 legs) threaded through the identifications; ellipticity:
   isElliptic_of_map_isElliptic + IsUnit-transport along the equivs.
