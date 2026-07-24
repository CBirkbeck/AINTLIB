# HANDOVER — Y(ρ̄) representability, mid-stream 3c (2026-07-24)

Branch `dev/modular-curves`, worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`.
Producer role: **prove theorems only** (no cleaning/golfing/bumping). Push with
`LEAN4_GUARDRAILS_BYPASS=1 git push origin dev/modular-curves`. `lake build` FROM REPO ROOT
only. Never `set_option maxHeartbeats`. Never `2>/dev/null` next to lake/lean. Commit per
green increment. Keep the sentinel `.mathlib-quality/beastmode_active` (repo root) updated.

---

## 0. THE TARGET (what the whole campaign is proving)

`yRho_representable` (YRho.lean:8593, currently `sorry`): for a mod-N Galois datum
`D : GaloisRepData N` (ρ̄ : Gal(ℚ̄/ℚ) → GL₂(ℤ/N) with **det ρ̄ = cyclotomic char**, plus a
pairing `p : V_ρ̄ × V_ρ̄ → μ_N`), the moduli of pairs `(E/T, α)` where
`α : E[N] ≅ V_ρ̄ ×_ℚ T` is an iso of group schemes **carrying the Weil pairing e_N to p**
is representable by a smooth affine ℚ-curve. `N` need NOT be prime (this is why everything
goes through the finite-étale-algebra ↔ continuous-Galois-set correspondence, not through
cyclotomic fields). det ρ̄ = χ is what makes Y(ρ̄) geometrically irreducible / gives the pairing.

**Construction shape** (confirmed with the user this session): Y(ρ̄) is **NOT** a quotient of the
full-level curve alone. It is `(Y_full × W) / GL₂(ℤ/N)` — a quotient of (full level N moduli) ×
(the frame torsor W). `W = wFrames D` = Isom((ℤ/N)²_const, V_ρ̄), a GL₂(ℤ/N)-torsor over Spec ℚ
whose ℚ̄-points are GL₂(ℤ/N) with Galois acting by left-mult through ρ̄. The dictionary
`(L, h) ↦ α` composes `E[N] ≅⁻¹(fullLevelIso L) (ℤ/N)²_T ≅(frame h) V_ρ̄×T`; the symplectic
condition becomes the "carve" `pairEZMap = frameDetMap` (Weil pairing of the level pair =
p(det frame)). GL₂ acts diagonally (γ·L on the level, h·γ on the frame) leaving α fixed
(T-EQ-2). Over ℚ̄ the torsor trivialises and Y(ρ̄) ≅ Y(N)_ℚ̄; only the ℚ-structure is twisted.

---

## 1. WHAT IS DONE (all green, pushed through `5be8723e4`)

Ordered chain: T-EQ-2 → T-EQ-3a → T-EQ-3b → T-EQ-3c-PIN → (3c-i in progress) → 3c → 3d → 3e →
**T-3E** closes `rhoLevel_relativelyRepresentable` (YRho.lean:8547) → YR-5/6/7 → `yRho_representable`.

- **T-EQ-2 COMPLETE** — `rhoLevelStructureOfFramed_glSmul` (YRho.lean ~6143): the GL₂-orbit
  descent (γ-translated framed pair gives the SAME ρ-structure). Geometric core axiom-clean.

- **T-EQ-3a** — descent toolkit collapsed onto mathlib `Sites/Fpqc.lean:110` (qc+flat+surjective
  ⟹ EffectiveEpi for schemes). Bonus `ForMathlib/AmitsurDescent.lean` (degree-≤1 Amitsur
  exactness) landed, off critical path.

- **T-EQ-3b COMPLETE** (`ModularCurve/RhoDescent.lean`, all green) — ρ-level-structure descent
  along finite étale qc-flat-surjective covers. `RhoLevelStructure.descend` + `pull_descend`.
  Covers `torsionMapOfEllHom`/`vRhoCoverPrj`; effective epis; `descTorsionHom/Inv/Iso`;
  `coord_descTorsionIso` bridge; F1 `descTorsion_coords_additive`, F2 `descTorsion_pairing_compat`,
  F3 `descTorsion_pairing_scheme` (W-generic via `cancel_epi` along the base-changed cover +
  `torsionPairEval_mapPoint` + `coordPairLift_descTorsionIso`).

- **T-EQ-3c-PIN COMPLETE** (`ModularCurve/RhoPairingBridge.lean`) — **the deepest dependency**,
  the "(vi)-bridge". `framedPinned_pairing_scheme` is now **UNCONDITIONAL**: the ρ-dictionary's
  morphism-level pairing hypothesis (`hsymp_scheme`) is discharged by the carve condition
  `pairEZMap = frameDetMap` alone. Chain: clopen decomposition of the torsion square
  (`torsionPairSquare_hom_ext`, via new public piece-API in `GroupScheme/MuN.lean`) → map-level
  symplectic formula (`torsionPairEval_comb`) → leg-unwind to the absolute frame
  (`framedPinned_leg_comb`, `frameSlotEval`) → Spec-collapses (`lift_pullbackSpecIso_hom`,
  `frameSlotEval_eq_Spec`, `pairSlot_vRhoPairingMap_eq_Spec`) → fiber-faithfulness
  (`finiteEtale_hom_ext_of_fiber`) → per-point correspondence descent (`pairSlot_hFE`) closing
  with `sympl_glSmul` + emod/toNat arithmetic.
  - **CENSUS**: `pairSlot_hFE`, `readCorrection_eq_refl` AXIOM-CLEAN [propext, Classical.choice,
    Quot.sound]; consumers carry only the expected DS4-register `sorryAx` (from `weilPairing`).
  - **STRUCTURAL DISCOVERY**: `readCorrection N = Equiv.refl` — the engine-era read-correction
    is provably vacuous (counit read ≡ concrete index read, unit-counit triangle). Reusable.

---

## 2. CURRENT IN-FLIGHT STATE — READ THIS FIRST

**The working tree is DIRTY and does NOT build.** `RhoPairingBridge.lean` has one in-flight
lemma `qbarRootsRead_classify` (line ~1785) that is BUILD-FAILING at its tail. Everything ELSE
in the tree is green and committed through `5be8723e4`.

The failing tail: I used `rootsOfUnity.coe_mkOfPowEq _ _` (it takes NO explicit args — it is
`↑↑(mkOfPowEq a h) = a`) and a stale `show`. **The fix I was mid-applying** (replace the tail of
`qbarRootsRead_classify`): the double-coe of `rootsSepQbarEquiv N (cycloAlgHomEquivRoots N Sep χ)`
reduces DEFINITIONALLY to `sepClosureQAlgEquiv (χ root)`, so replace the whole tail after
`rw [hpe]` with:

```lean
  rw [hpe]
  show sepClosureQAlgEquiv
    (χ (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))) =
    θ ((muNRootsAlgebraIso D).inv.hom.hom
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1)))
  show sepClosureQAlgEquiv (sepClosureQAlgEquiv.symm
    (θ ((muNRootsAlgebraIso D).inv.hom.hom
      (AdjoinRoot.root ((Polynomial.X : Polynomial ℚ) ^ N - 1))))) = _
  rw [AlgEquiv.apply_symm_apply]
```

If the first `show` fails on defeq (mkOfPowEq coe not reducing), fall back to
`rw [rootsOfUnity.coe_mkOfPowEq, rootsOfUnity.coe_mkOfPowEq]` (no args) after unfolding the two
Equiv applications with `show`/`simp only [rootsSepQbarEquiv, cycloAlgHomEquivRoots]`. First
action for the new worker: apply this fix, `lake build ModularCurves.ModularCurve.RhoPairingBridge`,
commit `qbarRootsRead_classify`.

The full `qbarRootsRead_classify` head + proof-body (everything ABOVE the tail) already builds —
it reduces the RHS of the DS3 bridge (below) to `θ(muNRootsAlgebraIso.inv(root))`.

`scratch_alg.lean` at repo root is an untracked scratch file — ignore or delete.

---

## 3. THE KEYSTONE: the DS3 bridge (`muNRootsRead ↔ correspondence`)

This is the single hard obstacle for 3c-i, and it is the crux of the whole "pointwise pairing"
story. Everything else in 3c-i/i-4/i-5 is assembly once this lands.

**Why needed**: `FramedSymp` / `PairingCompatAt` are ℚ̄-pointwise Weil-pairing statements. To
extract a ℚ̄ value from any morphism into `muNRootsScheme` you go through `muNRootsRead`, which is
defined via `muNPointsEquiv` (the μN GROUP scheme). But all our pairing computation lives on the
CORRESPONDENCE side (`qbarPointsRead`, which I built this session — generic ℚ̄-points read of a
correspondence spectrum). The bridge equating the two points-descriptions is unavoidable and is
the DS3-compatibility content that `muNSpecQIso` (T-CV-1 CLOSE) was built for but never had a
points-lemma proved for.

**Statement to prove** (the keystone; NOT yet written):
```lean
theorem muNRoots_correspondence_read (D : GaloisRepData N) [Fact (1 < N)]
    (φ : Spec (.of (AlgebraicClosure ℚ)) ⟶ muNRootsScheme D)
    (hφ : φ ≫ muNRootsSchemeπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom.hom
        (muNRootsRead D (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) φ hφ) =
      (((qbarPointsRead (muNRootsContAction D) ⟨φ, hφ⟩ :   -- subtype defeq: muNRootsScheme ≡ corrSpec, muNRootsSchemeπ ≡ corrSpecπ
        rootsOfUnity N (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
```

**Proof plan (FULLY worked out — both sides reduce to `θ(muNRootsAlgebraIso.inv(root))`):**
Let `θ := specPointsEquivAlgHom ℚ (muNRootsAlgebra D) (AlgebraicClosure ℚ) ⟨φ, hφ⟩`
(an ℚ-alg-hom `muNRootsAlgebra D →ₐ ℚ̄`; `θ.toRingHom = (Spec.preimage φ).hom` by the def).

- **RHS** = `qbarRootsRead_classify` (IN-FLIGHT lemma, apply §2 fix): reduces to
  `θ((muNRootsAlgebraIso D).inv.hom.hom (AdjoinRoot.root (X^N-1)))`. Uses `counit_read_comp_rootsIso`
  (already committed, 606d01e00) + factorisation via `hom_inv_id` + arrowCongr/sepClosure coe
  cancellation. DONE modulo the tail fix.

- **LHS** (`muNRootsRead_classify`, NOT yet written — the remaining ~80–120 lines): also reduces
  to `θ((muNRootsAlgebraIso D).inv.hom.hom (AdjoinRoot.root))`. The trace:
  1. `muNRootsRead D b φ hφ = (muNPointsEquiv (Spec ℚ) N b ⟨φ ≫ (muNSpecQIso D).inv, _⟩ : Γ(Spec ℚ̄))`
     (def of muNRootsRead).
  2. `(muNSpecQIso D).inv = (muNRootsSpecIso D).inv ≫ (muNSpecFieldIso ℚ N).inv` (rfl, .inv of a trans);
     `(muNRootsSpecIso D).inv = Spec.map (CommRingCat.ofHom (muNRootsAlgebraIso D).inv.hom.hom.toRingHom)`
     (rfl from the def, YRho.lean:1713). So `φ ≫ (muNSpecQIso D).inv = φ' ≫ (muNSpecFieldIso ℚ N).inv`
     where `φ' := φ ≫ Spec.map(ofHom(rootsAlgIso.inv.ring)) : Spec ℚ̄ ⟶ Spec(AdjoinRoot=cycloQuot)`.
     By `spec_preimage_comp` (committed): `(Spec.preimage φ').hom = (θ.comp rootsAlgIso.inv.hom.hom).toRingHom`
     i.e. φ' classifies `θ ∘ rootsAlgIso.inv : AdjoinRoot →ₐ ℚ̄`.
  3. Apply `muNPointsEquiv_coe` (committed, 345372eda):
     `muNRootsRead = ((φ' ≫ (muNSpecFieldIso ℚ N).inv) ≫ abs-snd).appTop.hom (ΓSpecIso(muNRing N)).inv(muNAbsGen N)`
     where `abs-snd = pullback.snd (terminal.from (Spec ℚ)) (terminal.from (muNAbs N))`.
  4. `comp_appTop` (mathlib Scheme.lean:389, `(f≫g).appTop = g.appTop ≫ f.appTop`): peel off φ'.
     The inner `((muNSpecFieldIso ℚ N).inv ≫ abs-snd).appTop.hom (ΓSpecIso(muNRing).inv (muNAbsGen))`:
     any morphism `Spec(AdjoinRoot) ⟶ Spec(muNRing)` equals `Spec.map` of its preimage, so use
     `specMap_appTop_gammaInv` (committed) + `muNSpecFieldIso_inv_snd_gen` (committed, 345372eda —
     tracks the generator to `AdjoinRoot.root`) ⟹ inner = `(ΓSpecIso(AdjoinRoot)).inv.hom (AdjoinRoot.root)`.
  5. So `muNRootsRead = φ'.appTop.hom ((ΓSpecIso(AdjoinRoot)).inv.hom (AdjoinRoot.root))`. Apply
     `(ΓSpecIso ℚ̄).hom.hom` and use `gammaSpec_read` (committed, φ' : Spec ℚ̄ ⟶ Spec(AdjoinRoot)):
     `= (Spec.preimage φ').hom (AdjoinRoot.root) = (θ ∘ rootsAlgIso.inv)(root) = θ(rootsAlgIso.inv(root))`. ∎

  ALL atoms for the LHS exist and are committed. This is careful term-mode plumbing (~100 lines),
  NOT new mathematics. Watch: `.appTop` composite order (`comp_appTop` reverses), and
  `ConcreteCategory.hom`/`.hom.hom` wrapper spellings — use the LSP `lean_goal` at each `refine`.

**Verify the defeq assumptions with a quick `example ... := rfl` probe before relying on them:**
`muNRootsScheme D ≡ corrSpec (muNRootsContAction D)`, `muNRootsAlgebra D ≡ corrAlgebra (muNRootsContAction D)`,
`muNRootsSchemeπ D ≡ corrSpecπ (muNRootsContAction D)`, `detFrameScheme D ≡ corrSpecMap (detFrameMor D)`,
`detCompScheme D ≡ corrSpecMap (detCompMor D)`, `wFrames D ≡ corrSpec (frameContAction D)`,
`wFramesPointsEquiv D ≡ qbarPointsRead (frameContAction D)`. (All should be rfl — the wrappers were
DESIGNED to make these hold; §4/§5 depend on them.)

---

## 4. REMAINING ROADMAP (after the keystone)

Board detail: `tickets.md`, section `[T-EQ-3c-i]` (5-leaf plan) and `[T-EQ-3 DECOMPOSITION v2]`
(~line 25517). Sentinel `.mathlib-quality/beastmode_active` has the running micro-state.

**3c-i (finish the pointwise transfer):** with the keystone, prove
`framedSymp_of_pairEZMap : hcond → FramedSymp` OR — cleaner, RECOMMENDED — build a
`RhoLevelStructure` constructor from `hcond` ALONE (no separate `hsymp`), deriving `pairing_compat`
(PairingCompatAt) from the already-proven `framedPinned_pairing_scheme` (`pairing_scheme` field):
  - LHS of PairingCompatAt via `torsionPairEval_read` (LANDED, PIN-1) = `weilPairingEval`.
  - RHS via the keystone + `qbarPointsRead_map` on `coordPairLift ≫ vRhoPairingMap`: note
    `vRhoPairingMap D ≡ pullbackVRhoIso.hom ≫ corrSpecMap (rhoPairMor D)` and `rhoPairMor` set-map is
    `uv ↦ p(ofAdd(u0·v1 − u1·v0))`, and the two coordPairLift components read to `coord x`, `coord y`
    (SAME decomposition as `pairSlot_hFE` — reuse that machinery). Gives `p(coord-wedge)` = RHS.
  This AVOIDS the frame-det ℚ̄ read entirely and gives a from-`hcond` constructor. Then for the
  3c descent-agreement reuse `framedTorsionIsoPinned_glSmul` (LANDED, axiom-clean) via
  `RhoLevelStructure.ext_torsionIso`.

  NOTE: `rhoLevelStructureOfFramed` (YRho.lean:6110) currently takes `hsymp : FramedSymp` AND
  `hsymp_scheme` as explicit hyps. `rhoLevelStructureOfFramed_glSmul` (T-EQ-2) is stated over it.
  Simplest: prove `framedSymp_of_pairEZMap` and keep using the existing constructor (then the
  frame-det ℚ̄ read IS needed — via keystone + `qbarPointsRead_map ×2` on
  `detFrameScheme ≫ detCompScheme`, det-map set = `A ↦ det A`, detComp set = `u ↦ p(ofAdd u)`).
  Either path works; the from-hcond constructor is less code but touches the constructor API.

**3c (sections → ρ-structures):** at `X := (T, sT, E)`, take
`pkgX := (nonempty_quotPkg (sympFramedAut D) (sympFramed_equivariantRelRepData D) X).some`
(GammaHRepresentability.lean:705). Given `h : T' ⟶ pkgX.Z₀` over `k`: cover
`c := pullback.snd pkgX.π h` (finite-étale-surjective by `QuotPkg.π_finite_etale_surjective` +
`sympFramedAut_freeAction`, base-changed); lift into `pkgX.d.Z`; `pkgX.d.eqv` reads a
`sympFramedProblem` VALUE whose `.property` IS `hcond` (check against `sympLocus_agree_iff_symp`,
YRho.lean:8319); apply the dictionary; double-pullback lifts differ by γ (torsor freeness) ⟹
agree by T-EQ-2 ⟹ descend via `RhoLevelStructure.descend` (T-EQ-3b). Well-definedness by
descend-uniqueness. `NIsInvertible T'' N` over ℚ: char-0 supply (see uses at
`sympFramed_equivariantRelRepData`, YRho.lean:8404, and `TorsionFibre.lean:46`).

**3d (ρ-structures → sections):** α ↦ étale-local trivialisation (`torsion_etaleLocal_triv`
LANDED, `GroupScheme/TorsionEtaleTriv.lean:328`) → local full-level L'' + local frame via
`frameEvalSliceInv` (YRho.lean:5136) → local Z₀-sections → glue along the cover (T-EQ-3b toolkit,
target Z₀). Orbit-uniqueness (two symp-framed lifts differ by γ = dictionary injectivity).

**3e + T-3E:** mutual-inverse (pointwise via the torsor + descend-uniqueness) + assembly ⟹
`rhoLevel_relativelyRepresentable` (YRho.lean:8547 sorry) via `nonempty_quotPkg` +
`QuotPkg.f₀_finite_etale`.

**YR-5/6/7 → yRho_representable (YRho.lean:8593 sorry):** the standard bootstrap
(`representable_of_affineOverEll_of_rigidNoeth` + rho-rigidity for N ≥ 3, Loeffler 3.8.3) —
same cascade already used for Y(N)/Y₁(N) in this project. NOT in scope: `yRho_geometricallyIrreducible`
(YRho.lean:8639), DS4-register closing, cleanup.

**Size estimate to `yRho_representable`:** ~1500–2500 lines, roughly one more marathon window.
The hardest single obstacle (the (vi)-bridge) is already behind us; the keystone above is the last
genuinely deep piece. The rest is assembly over landed machinery.

---

## 5. HARD-WON DISCIPLINE / GOTCHAS (do not relearn these the hard way)

- **whnf blowup on spelled-out correspondence types** — the #1 time sink. When a goal has a big
  spelled `(FiniteEtaleGalois.finiteEtaleEquivContAction ℚ).inverse.obj X`-style type, `rw`/`simp`
  hit 200k heartbeat whnf timeouts. FIX: introduce def-name wrappers (`corrAlgebra`, `corrSpec`,
  `corrSpecMap`, `qbarPointsRead` this session; `univPzx`-style earlier) so the elaborator whnf's
  ONCE not per-rewrite. This single trick unblocked i-1/i-2.
- **`rw` fails / kabstract "not type-correct under instances transparency"** on correspondence /
  scheme-iso goals → use term-mode `Eq.trans`/`congrArg` chains, or `show` to the exact defeq form
  then `rfl`/small rewrite. Many lemmas this session close with a final bare `exact rfl` or `rfl`
  where `simp`/`rw` choke (fiber.map of a composite is DEFINITIONAL — no `map_comp`+`comp_apply`
  needed; those metas whnf-explode, avoid them).
- **`set x` folds occurrences** — then `rw [lemma-about-x-unfolded]` fails to find the pattern.
  Use term-mode `congrArg`/`Eq.trans` instead of `rw` after a `set`.
- **`Subtype.ext` on `⟨_, proof⟩ = ?m`** needs the RHS element SPELLED (both subtype elements
  written out) — see the `hsub` idiom repeated throughout (e.g. `torsionPairEval_read`).
- **congrArg lambda binder metas** exploding `Scheme.Γ.obj ?m` → annotate the lambda's binder type
  fully (`fun (q : A ⟶ B) => ...`).
- **`Sigma.desc`/`Sigma.ι` ambiguous** (CategoryTheory vs Limits) → qualify `Limits.Sigma.desc`.
- **big `pE`-application goals in STATEMENT position whnf-choke** — obtain/generalize the inner
  point to an fvar FIRST (`obtain ⟨x'', rfl⟩ := ...`), then work on the fvar. Same for `mapPointEquiv`
  values: NEVER `let`-bind an `equiv.symm x`; always `obtain ⟨x'', hx''⟩ : ∃ …` (OPAQUE-fvar
  discipline). Let-bound equiv-values whnf-explode.
- **point_kill / cross-base binders** — keep test-scheme binders GENERIC (`{W : Scheme}`), not
  `Spec ℚ̄`-restricted; the restricted form makes `cancel_epi` covers unify-explode.
- **DS4-register honesty** — pairing-side consumers (anything through `weilPairingEval` /
  `weilPairing`) carry an EXPECTED `sorryAx` from the registered `weilPairing` (WeilPairing/Basic.lean
  DS4). This is the accepted register discipline, NOT a defect. Geometric/Spec/correspondence layers
  ARE axiom-clean [propext, Classical.choice, Quot.sound]; verify with `#print axioms` and report
  the sorryAx as expected. Closing DS4 is stream-C's job, not this proof's.
- **LSP for goal inspection, `lake build` FROM REPO ROOT as the final gate.** The LSP
  (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`) is the inner loop — use it to read
  exact goals before writing big term chains (saved many blind-build cycles this session). But
  `lake build` from repo root is the source of truth (the LSP can serve stale oleans after a
  dependency edit — force a `lake build` of the edited dependency + downstream before trusting green).
- **background builds**: `(lake build <mod> > logfile 2>&1; echo "EXIT:$?" >> logfile)` run in
  background, then poll `until grep -q EXIT logfile; do sleep 15; done`. NEVER `2>/dev/null` next to
  lake/lean (guardrail-blocked).

---

## 6. KEY FILE / LINE REFERENCES

- `ModularCurve/YRho.lean` (~8600 lines) — the spine. Targets: `rhoLevel_relativelyRepresentable`
  :8547, `yRho_representable` :8593. Structures: `RhoLevelStructure` :2173, `FramedSymp` :2075,
  `PairingCompatAt` :2114, `coord` :2095, `coordPairLift` :2134, `torsionPairEval` :2156.
  Dictionary `rhoLevelStructureOfFramed` :6110, `_glSmul` :6143. Carve `pairEZMap` :7665,
  `frameDetMap` :7688, `pairEZMap_read` :7727. Frame side `framedTorsionIsoPinned` :5388,
  `frameEvalSlice` :5120, `frameEvalSliceInv` :5136, `wFramesPointsEquiv` :449. Correspondence
  isos `muNRootsCorrespondenceIso` :1673, `muNRootsAlgebraIso` :1704, `muNRootsSpecIso` :1713,
  `muNSpecQIso` :1736, `cycloAlgHomEquivRoots` :1556, `rootsSepQbarEquiv` :1575. Reads
  `muNRootsRead` :6806, `muNRoots_hom_ext`, `muNRootsRead_pow` :6999, `muNRootsRead_congr` :7527.
  Quotient side `sympFramedProblem` :7966, `sympFramedAut` :8008, `sympFramedAut_freeAction` :8064,
  `sympFramed_equivariantRelRepData` :8404, `sympLocus_agree_iff_symp` :8319.
- `ModularCurve/RhoPairingBridge.lean` (~1830 lines, THIS session's file) — the (vi)-bridge +
  3c-i machinery. `framedPinned_pairing_scheme` (unconditional), `pairSlot_hFE`,
  `readCorrection_eq_refl`, `counit_read_comp_cvsIso`/`_rootsIso`, `pointsEquiv_fiber_unit`,
  `finiteEtale_hom_ext_of_fiber`, `qbarPointsRead` + `qbarPointsRead_map`, `corrAlgebra`/`corrSpec`/
  `corrSpecMap`, `gammaSpec_read`, `specMap_appTop_gammaInv`, `spec_preimage_comp`,
  `qbarRootsRead_classify` (IN-FLIGHT, §2 fix). NEXT: `muNRootsRead_classify` + keystone
  `muNRoots_correspondence_read` (§3).
- `ModularCurve/RhoDescent.lean` — T-EQ-3b (descent), all green.
- `GroupScheme/MuN.lean` — μN group scheme + constant scheme. Public piece-API
  (`locConstPiece`, `locConst_hom_ext`, `constMap_factor_of_le`), value-API (`muNAbsGen`,
  `muNPointsEquiv_coe`, `muNSpecFieldIso_inv_snd_gen`), `constSchemePointsEquiv` :383,
  `constSchemeMapAlong` :531, `isPullback_constSchemeMapAlong` :588.
- `Moduli/GammaHRepresentability.lean` — `QuotPkg` :689, `nonempty_quotPkg` :705,
  `QuotPkg.π_finite_etale_surjective` :718, `QuotPkg.f₀_finite_etale` :732.
- `ForMathlib/FiniteEtaleFundamentalGroup.lean` — `pointsEquivOfContAction` :383,
  `pointsEquivOfContAction_smul`, `finiteEtaleEquivContAction_functor_map_hom` :410;
  `pointsEquivOfContAction_map` (naturality) YRho.lean:549.
- `ForMathlib/EtaleSectionsCount.lean:298` — `specPointsEquivAlgHom` (ℚ̄-points ↔ AlgHoms;
  `.toFun = (Spec.preimage ·).hom`).
- mathlib: `Sites/Fpqc.lean:110` (EffectiveEpi), `Pullbacks.lean:719+` (`pullbackSpecIso` +
  `_inv_fst`/`_inv_snd`/`_hom_fst'`), `Scheme.lean:389` (`comp_appTop`), `:628`
  (`ΓSpecIso_naturality`), `:635` (`ΓSpecIso_inv_naturality`), `RingTheory/Etale/Finite.lean:118`
  (`FiniteEtale.fiber`).

---

## 7. FIRST FIVE ACTIONS FOR THE NEW WORKER

1. `git status` — confirm dirty `RhoPairingBridge.lean`. Apply the §2 tail fix to
   `qbarRootsRead_classify`, `lake build ModularCurves.ModularCurve.RhoPairingBridge`, commit+push.
2. Add the defeq `example … := rfl` probes from §3 (verify the wrapper defeqs hold). If any fails,
   the wrapper's carrier needs an ascription tweak — fix before building on it.
3. Write `muNRootsRead_classify` (§3 LHS trace) using the LSP to read goals at each step.
4. Combine into the keystone `muNRoots_correspondence_read`. Commit. Axiom-check.
5. Do 3c-i via the from-`hcond` constructor (§4, RECOMMENDED path), then start 3c-main.

Keep the sentinel updated each step; commit per green increment; push through the guardrail bypass.
