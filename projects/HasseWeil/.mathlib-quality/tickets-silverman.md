# Ticket Board — Silverman continuation

Plan: `.mathlib-quality/plan-silverman.md`. Per-leaf detail (Lean statements, source quotes, LOC):
`.mathlib-quality/develop/{isogeny-foundation,tate-module,formal-group-bridge}.md`.
Branch `silverman-development`. (Historical Hasse board: `tickets.md`, left as-is.)

## Summary
- Workstream 1 (Isogeny + III.4.8): 5 proof tickets + 2 cleanup. **PRIORITY.** ~300–550 LOC.
- Workstream 2 (Tate module III.7): 13 proof tickets + 3 cleanup. ~700–950 LOC.
- Workstream 3 (formal-group bridge): OPTIONAL, 3 tickets. Defer by default.
- Parallel capacity: ISO-L4 and TATE-L9 are dependency-free leaves; the two workstreams are
  independent (the Tate module does NOT need III.4.8) so W1 and W2 can run in parallel.

## Progress (2026-06-09)
- **W2 foundation DONE, axiom-clean** (commit `8457501`): TATE-L1/L2/L3 + TATE-L9
  (`HasseWeil/TateModule/{TorsionPow,PadicLimZMod}.lean`).
- **W2 Phase 1+2 DONE, axiom-clean** (commit `<tate2>`): TATE-L4 `torsion_ellPow_linearEquiv`
  (E[ℓⁿ]≅(ZMod ℓⁿ)², full ZMod-linear coherent route) + `torsion_ellPow_free`/`finrank_torsion_ellPow`,
  TATE-L5 `tateConn`, TATE-L6 `tateConn_castHom_compat`, TATE-L7 `tateConn_surjective`, and the
  COHERENCE `tateConn_tateBasis` (connecting square commutes — L10-ready). Files
  `HasseWeil/TateModule/{InverseSystem,TorsionPowStructure}.lean`. Reuses `mulByInt_point_surjective`.
- **W1 III.4.8 AXIOM-CLEAN ✓** (commits `7a04222`, `<ii>`): `HasseWeil/Curves/PushforwardDivisor.lean`
  + `HasseWeil/EC/IsogenyAG/GroupHom.lean`. `EC.Isogeny.addHomProperty` (Silverman III.4.8) +
  `pushforward_preserves_principal` + the sub-leaf (ii) `projectiveDivisorOf_pushforward_eq_pushforwardDivisorVal`
  (= II.3.6 `div(N_φ f)=φ_*(div f)`) ALL `[propext, Classical.choice, Quot.sound]`, NO sorryAx. (ii)
  proved via the global norm-balance route `m_Q^deg = ∏ relNorm(m_P')^{e}` + `Σe·f=deg` + `f=1`
  (NOT `relNorm_eq_pow_of_isMaximal`, which needs `PerfectField` — fails in char p). One scoped
  `maxHeartbeats 1600000` on the monolith (future cleanup: break it up, like the Hasse pass).
- **W2 Phase 3 DONE, axiom-clean** (commit `010e0f8`): TATE-L8 `tateModule` (hand-built inverse limit
  + ℤ_[ℓ]-module via PadicInt.toZModPow) + TATE-L10 `tateModuleEquiv` (**`T_ℓ(E)≅ℤ_ℓ²`**, Silverman
  III.7 Prop 7.1a). `HasseWeil/TateModule/TateModule.lean`. No sorry, no maxHeartbeats.
- **W1 ISO-L7 ENGINE DONE, axiom-clean** (commit `<l7>`): `addHomProperty_descend_of_baseChange`
  (`HasseWeil/EC/IsogenyAG/GroupHomDescend.lean`) descends K̄-level III.4.8 to K given a base-changed
  isogeny + compat. The full `addHomProperty_descend` carries **4 documented sorries = the
  `EC.Isogeny.baseChange` infra gap** (new ticket ISO-BC below).
- **[ISO-BC] (NEW, blocks full ISO-L7)**: build `EC.Isogeny.baseChange` (function-field pullback via
  `CoordHom.baseChangeAlgHom`+`IsFractionRing.liftAlgHom`; the HARD field `pullback_ordAtInfty_nonneg`
  = ramification e=1 at ∞ under base change, NOT covered by `ordAtInfty_functionFieldMap`) +
  `CoordHom.baseChange` (+compat) + `Module.Finite` base-change + point-map compatibility. Multi-hundred
  LOC. Detail in `GroupHomDescend.lean`'s 4 sorry docstrings.
- **W2 Phase 4 DONE, axiom-clean** (commit `<rho>`): TATE-L11 `galoisTorsionRestrict` (Galois action on
  E[ℓⁿ] via mathlib `Affine.Point.map σ`), L12 `galois_comm_tateConn`+`rhoTate` (action on T_ℓ),
  L13 `rhoTateHom` (**ρ_ℓ : (F≃ₐ[K]F) →* Aut(T_ℓ)**), L14 `rhoTateGL` (**ρ_ℓ → GL₂(ℤ_ℓ)**).
  `HasseWeil/TateModule/Representation.lean`. **THE TATE-MODULE CHAPTER IS COMPLETE** (T_ℓ≅ℤ_ℓ² + ρ_ℓ).
- **Isogeny-class layer STARTED** (commit `<ic>`): `HasseWeil/EC/IsogenyAG/IsogenyClass.lean` —
  `IsIsogenous := Nonempty (EC.Isogeny ·)` (Silverman III.4's relation), `IsIsogenous.refl`/`.trans`
  AXIOM-CLEAN, + the packaging `EllipticCurveOver`/`IsogenousCurves`/`isIsogenous_equivalence`/
  `isIsogenousSetoid`/`IsogenyClass` (= the LMFDB isogeny-class quotient). **Symmetry reduced to ONE gap**
  `IsogenyDual.exists_dual` (= the dual isogeny III.6.1 as an `EC.Isogeny`); `symm`/`equivalence`/`setoid`
  carry sorryAx only via it.
- **[ISO-DUAL] (NEW, the symm gap + key LMFDB piece)**: construct `EC.Isogeny.dual` (Silverman III.6.1).
  The repo's dual machinery (`divisorPushforwardDual`, `picDual`, `isogDual`) gives only a POINT MAP,
  never the function-field pullback (`CurveMap`) `EC.Isogeny` needs — and the point-map→pullback bridge is
  "unprovable" generically (Silverman p.81: "by no means clear that κ⁻¹∘φ*∘κ is an isogeny"). Two routes:
  kernel/quotient (III.4.12 + `QuotientCurve.lean`) or Pic⁰-upgrade-to-morphism (III.6.1b). Multi-hundred LOC.
- **NEXT OPEN**: ISO-DUAL (the dual III.6.1 → isogeny-class symmetry); ISO-BC (base-change for ISO-L7);
  conductor theory over ℚ (the big LMFDB-labels gap). Cleanup: wire `TateModule/*` + `IsogenyClass`/`GroupHom*`
  into root; break up the (ii) `maxHeartbeats` monolith. Optional: W3 formal-group bridge.

---

## Workstream 1 — Faithful Isogeny + III.4.8 (Silverman III.4, via III.3/III.6 Pic⁰)

### [ISO-L0] Minimal `EC.Isogeny → Basic.Isogeny` bridge (consolidation, no migration)
- **Status**: open · **File**: `HasseWeil/EC/IsogenyAG.lean` (or new `IsogenyAG/Bridge.lean`) ·
  **Depends on**: ISO-L6 · **Type**: def · **Parallel**: after L6
- **Statement**: `EC.Isogeny.toBasicIsogeny (φ) (cd) (h : φ.AddHomProperty cd) : HasseWeil.Isogeny W₁ W₂`
  := `{ pullback := φ.toCurveMap.pullback, toAddMonoidHom := φ.toAddMonoidHomOfWitness cd h }`.
- **Why**: makes `EC.Isogeny` canonical + feeds existing `Basic.Isogeny` consumers a faithful isogeny
  whose group-hom is now a THEOREM, **without** a repo-wide migration (full migration = deferred
  cleanup, high churn: `mulByInt`/`frobeniusIsog`/WeilPairing tree all use `Basic.Isogeny`).
- **Source**: III.4 (def, p.66). · **LOC** ~30. Detail: isogeny-foundation.md NEW-2.

### [ISO-L4] `h_pres`: `φ_*` preserves principal divisors (THE gap) ⚑
- **Status**: open · **File**: new `HasseWeil/Curves/PushforwardDivisor.lean` · **Depends on**: none
  (cites existing) · **Type**: theorem (with sub-leaf defs) · **Parallel**: yes (dependency-free)
- **Statement (target)**:
  ```lean
  theorem EC.Isogeny.pushforward_preserves_principal (φ : EC.Isogeny W₁ W₂)
      (cd : φ.toCurveMap.CoordHom) (D) (hD : D ∈ ⟨W₁⟩.projPrincipalSubgroup) :
      pushforwardProjectiveDivisor φ cd D ∈ ⟨W₂⟩.projPrincipalSubgroup
  ```
- **Proof route (Route 4b, source-faithful — Route 4a σ-criterion is CIRCULAR, do NOT use)**: via the
  norm conorm. Sub-leaves (state each `:= by sorry` first):
  1. `CurveMap.pushforwardDivisorVal φ D` — valuation-theoretic divisor pushforward (coeff at `Q` =
     `Σ_{P↦Q} coeff_P D`); NOT point-map-gated.
  2. `projectiveDivisorOf (φ.pushforward f) = φ.pushforwardDivisorVal (projectiveDivisorOf f)`  ⟸ the
     norm–conorm identity `div(N_φ f) = φ_*(div f)` (II.3.6). **Hardest sub-leaf** — `ord_Q(N_φ f) =
     Σ_{P↦Q} f_{P/Q}·ord_P(f)` via `Ideal.sum_ramification_inertia` (degree side already in
     `NormValuation.lean`) + `Algebra.norm`. So `pushforwardDivisorVal` of a principal divisor is
     principal *by construction*.
  3. `pushforwardProjectiveDivisor φ cd D = φ.pushforwardDivisorVal D` on principal `D` (fibre ↔
     image-point `= φP`; needs the fibre structure, NOT φ being a hom).
  4. `h_pres` falls out of (2)+(3).
- **Mathlib**: `Algebra.norm`, `Ideal.ramificationIdx`, `inertiaDeg`, `Ideal.sum_ramification_inertia`.
  **Project**: `CurveMap.pushforward` (=norm, `CurveMap.lean:257`), `NormValuation.lean`
  (`fiber_sum_divisorOf_algMap_eq_count_norm`, `divisorOf_algMap_degree_eq_natDegree_norm`),
  `PicZeroPushforward.lean` (`pushforwardProjectiveDivisor`), `OneSubDualDivisor.lean`
  (`divisorPushforwardDual` — code template). · **Source**: II.3.6 / II.3.7. · **LOC** ~250–450.
  Detail: isogeny-foundation.md LEAF4 + NEW-1.
- **Coordinate** the fibre-valuation lemmas with the dual-isogeny `pullbackDivisor` (mirror construction).

### [ISO-L6] Package the unconditional `AddHomProperty` (III.4.8 over `IsAlgClosed F`)
- **Status**: blocked(ISO-L4) · **File**: new `HasseWeil/EC/IsogenyAG/GroupHom.lean` ·
  **Depends on**: ISO-L4 · **Type**: theorem
- **Statement**: `theorem EC.Isogeny.addHomProperty (φ : EC.Isogeny W₁ W₂) (cd) [IsAlgClosed F]
  [IsDedekindDomain R₁] [IsDedekindDomain R₂] [IsIntegrallyClosed R₁] [IsIntegrallyClosed R₂] :
  φ.AddHomProperty cd`, + bundled `toAddMonoidHomOfWitness`.
- **Proof**: one-liner — `AddHomProperty_of_AFInputs φ cd (afInputs_allChar W₁) (afInputs_allChar W₂)
  principal_mem_degZero principal_mem_degZero (ISO-L4)`. (LEAF1/2/3 cited:
  `picZeroIsoE_allChar`, `picZeroOfPoint_pushforwardPicZero`, `AddHomProperty_of_picZero_witnesses` —
  all PROVEN.) · **Source**: III.4.8 (p.71). · **LOC** ~30. Detail: isogeny-foundation.md LEAF6.
- **DESIGN DECISION (DECIDED 2026-06-09 — divisor/σ-level primary)**: state III.4.8 primarily at the
  divisor/σ level (CoordHom-free) so it covers `[n]`/`1−π`; the `AddHomProperty cd` point-map form is a
  corollary where `cd` exists. This is the canonical III.4.8 API.

### [ISO-L7] Descend III.4.8 to a non-closed base field `K`
- **Status**: blocked(ISO-L6) · **File**: `HasseWeil/EC/IsogenyAG/GroupHom.lean` · **Depends on**:
  ISO-L6 · **Type**: theorem
- **Statement**: `AddHomProperty` (point-map form) for `φ : EC.Isogeny W W` over finite `K`, by
  base-changing to `K̄` + injective `Affine.Point.map`.
- **Proof**: `picZeroIsoE_allChar (W.baseChange (AlgebraicClosure K))` + `Affine.Point.map` injective
  AddMonoidHom restricting the K̄-hom to K. · **Source**: III.4.8 is geometric; K-statement is the
  restriction. · **LOC** ~60–120. Detail: isogeny-foundation.md LEAF7/NEW-3.
- **NOTE**: may share base-change infra with Workstream 2 (`Affine.Point.map` injectivity, Pic⁰
  base-change). `IsogenyBaseChange.lean` exists.

### [ISO-CLEANUP-1] `/cleanup` on `PushforwardDivisor.lean` + `GroupHom.lean`
- **Status**: blocked(ISO-L7) · **Depends on**: ISO-L4, ISO-L6, ISO-L7 · **Type**: cleanup
  (after the 3 W1 proof tickets; per cadence).

### [ISO-CLEANUP-2] final `/cleanup-all` for Workstream 1 + `#print axioms` check
- **Status**: blocked(ISO-CLEANUP-1) · **Type**: cleanup · verify III.4.8 theorems are axiom-clean
  (`[propext, Classical.choice, Quot.sound]`), no `sorryAx`.

---

## Workstream 2 — Tate module T_ℓ(E) ≅ ℤ_ℓ² + ρ_ℓ (Silverman III.7)

New files under `HasseWeil/TateModule/`: `TorsionPow.lean` (L1–L4), `InverseSystem.lean` (L5–L7),
`PadicLimZMod.lean` (L9), `TateModule.lean` (L8,L10), `Representation.lean` (L11–L14).

### Phase 1 — `E[ℓⁿ] ≅ (ℤ/ℓⁿ)²`  (file `TorsionPow.lean`)
- **[TATE-L1]** `((ℓ^n:ℕ):F) ≠ 0` — mathlib `pow_ne_zero`+`Nat.cast_pow`. open. ~5 LOC.
- **[TATE-L2]** `#E[ℓⁿ] = ℓ^{2n}` — instantiate general-ℤ `card_torsion_ell` (`TorsionCardEll.lean:71`)
  at `ℓⁿ`. dep L1. ~10 LOC.
- **[TATE-L3]** `Module (ZMod (ℓ^n)) E[ℓⁿ]` — mirror `torsion_ell_zmodModule` at exponent `ℓ^n`. dep
  L2. ~15 LOC.
- **[TATE-L4]** ⚑ `E[ℓⁿ] ≅ (ZMod ℓⁿ)²` (basis `Fin 2`) — **GENUINELY NEW, hardest of W2**. Over the
  *non-field* `ZMod(ℓⁿ)` cardinality does NOT pin the module; prove by **coherent induction** from
  `E[ℓ]≅(ZMod ℓ)²` + surjective `[ℓ]:E[ℓⁿ⁺¹]↠E[ℓⁿ]` (kernel `≅E[ℓ]`), lifting bases along `[ℓ]` (so
  L10 naturality holds by construction). dep L3. ~120–180 LOC. Source: Prop 7.1 + p.87. **Alt
  (lower-risk):** abstract-group iso `E[ℓⁿ]≃+(ZMod ℓⁿ)²` first, freeness as corollary.
- **[TATE-CLEANUP-1]** `/cleanup` `TorsionPow.lean`. dep L4.

### Phase 2 — inverse system  (file `InverseSystem.lean`)
- **[TATE-L5]** `tateConn n : E[ℓⁿ⁺¹] →+ E[ℓⁿ]` (`[ℓ]` restricted; well-def via `ℓⁿ·(ℓ·P)=0`). Mirror
  `Representation.torsionRestrictHom`. dep L3. ~25 LOC.
- **[TATE-L6]** `tateConn` is `ZMod.castHom`-semilinear. dep L5. ~30 LOC.
- **[TATE-L7]** `tateConn` surjective (OPTIONAL — only the ℓ-adic-topology remark; via existing `[ℓ]`
  surjectivity). dep L4. ~40 LOC (or 0 if skipped).

### Phase 3 — `T_ℓ ≅ ℤ_ℓ²`  (files `PadicLimZMod.lean`, `TateModule.lean`)
- **[TATE-L9]** `ℤ_[ℓ] ≃+* { compatible (ZMod ℓⁿ) sequences }` via `PadicInt.lift` (mathlib win,
  reusable, dependency-free). open, PARALLEL. ~90 LOC. Source: p.87.
- **[TATE-L8]** `tateModule` = `AddSubgroup` of `Π E[ℓⁿ]` of `tateConn`-compatible sequences + a
  `Module ℤ_[ℓ]` instance via `PadicInt.toZModPow` (no mathlib generic limit). dep L5,L6. ~150–220 LOC.
- **[TATE-L10]** `tateModule ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])` (Prop 7.1(a)) — transport per-`n` isos (L4)
  through the limit (L8) + L9. **Naturality** threads from L4's coherent bases. dep L4,L8,L9.
  ~120–180 LOC.
- **[TATE-CLEANUP-2]** `/cleanup` `TateModule.lean` + `PadicLimZMod.lean`. dep L8,L9,L10.

### Phase 4 — ρ_ℓ  (file `Representation.lean`)
- **[TATE-L11]** Galois action on `E[ℓⁿ]` (`Affine.Point.map σ` for `σ : F ≃ₐ[K] F`; torsion-preserving,
  `ZMod(ℓⁿ)`-linear). Generalize `Representation.map_mem_torsion_ell`. dep L3. ~30 LOC.
- **[TATE-L12]** action commutes with `tateConn`; assembles to `rhoTate σ : tateModule ≃ₗ tateModule`.
  dep L8,L11. ~70 LOC.
- **[TATE-L13]** `rhoTateHom : (F ≃ₐ[K] F) →* (tateModule ≃ₗ[ℤ_[ℓ]] tateModule)` (group hom). dep L12.
  ~40 LOC.
- **[TATE-L14]** (OPTIONAL) GL₂(ℤ_ℓ) form `rhoTateGL` via the L10 basis. dep L10,L13. ~50 LOC.
- **[TATE-CLEANUP-3]** final `/cleanup-all` for Workstream 2 + axiom check.
- **OUT OF SCOPE** (do NOT ticket): L15 continuity of ρ_ℓ; Thm 7.4 / Cor 7.5 (`Hom⊗ℤ_ℓ ↪ Hom(T_ℓ)`).

---

## Workstream 3 — Formal-group ↔ isogeny bridge (IV.1.4, IV.4.3) — OPTIONAL (deferred)

The two `FormalIsogenySeries.lean` sorries are non-load-bearing. Default action: leave deferred.
- **[BRIDGE-B2]** (the one with downstream value) `localExpand(addPullback_pair) = subst[f_α,f_β] F̂`
  (IV.1.4); also unblocks the V-side pole bound `addPullback_x_pair_x_ord_neg`. ~600–1200 LOC. Only
  pick up if the pole bound / fully-general IV.1.4 is wanted.
- **[BRIDGE-A]** (BRIDGE-001, IV.4.3 general) `curveFormalGroup` + `isogFormalHom` + A2 differential
  bridge; needs B2. A0 assoc ~250–500, A2 ~300–600.
- **[BRIDGE-C]** EDS Wronskian — OUT OF SCOPE (needs new mathlib Ward-formula API; bypassed by routeB).
- **Alt minimal close:** restate the two general sorries witness-parametrically (wrappers exist),
  delete the bare sorries. Detail: formal-group-bridge.md.

---

## Phase 5 — Dual completion / isogeny-class symmetry (Silverman III.4.10–4.12, III.6.1)
Full source-faithful decomposition: `.mathlib-quality/develop/dual-completion.md`. Goal: discharge
`EC.universal_dualGaloisData` (Dual.lean:461) → close `IsIsogenous.symm` / `isIsogenous_equivalence`,
by REUSING the existing Galois/kernel/fixed-field infra (NOT rebuilding). The dual = factor `[deg φ]`
through φ via III.4.11 (separable case).

### [DUAL-1] `ker φ ⊆ ker[deg φ]` for separable φ (Lagrange)
- Status: open · File: `EC/IsogenyAG/DualGalois.lean` · Depends on: none · Type: lemma (leaf) · LOC ~30
- Stmt: separable `φ`, `k ∈ ker φ` ⟹ `(deg φ) • k = 0`. REUSE `card_kernel_eq_degree_of_separable_concrete`
  + Lagrange (`orderOf_dvd_card`/`pow_card_eq_one`). Source: III.4.10c (p.73) + Lagrange.

### [BRIDGE-1] `EC.Isogeny.toBasicIsogeny` (now buildable via III.4.8)
- Status: open · File: new `EC/IsogenyAG/Bridge.lean` · Depends on: none · Type: def (leaf) · LOC ~25
- Stmt: `(φ : EC.Isogeny W₁ W₂) (cd) → HasseWeil.Isogeny W₁ W₂` :=
  `{pullback := φ.toCurveMap.pullback, toAddMonoidHom := φ.toAddMonoidHomOfWitness cd (φ.addHomProperty cd)}`.
  REUSE `addHomProperty` (done) + `toAddMonoidHomOfWitness`. Source: III.4.8 (p.71). Lets DUAL-2/3 name `ker φ`.

### [RAMI-1] `e_φ=1` (separable) ⟹ ∞-regularity reflection
- Status: open · File: `EC/IsogenyAG/Dual.lean` · Depends on: none · Type: lemma (leaf) · LOC ~50
- Stmt: separable `φ` ⟹ `0 ≤ ord_∞ g → 0 ≤ ord_∞(φ*g)`. REUSE `ramificationIndex_eq_one_of_separable_witnesses`
  + `ramificationIndex_mul_sepDegree_eq_degree_of_witnesses`; Frobenius case = `frobenius_reflects_ordAtInfty`.
  Source: III.4.10a (p.72–73, `e_φ(P)=deg_i φ` uniform).

### [DUAL-2] per-φ covariance `xy_family` for a general φ from `addHomProperty` ⚑ (the crux)
- Status: open · File: `EC/IsogenyAG/DualGalois.lean` · Depends on: BRIDGE-1 · Type: lemma · LOC ~80–150
- Stmt: a general `φ` (with CoordHom) satisfies the `xy_family` translation-covariance that
  `pullback_fieldRange_eq_fixedField_of_card_match_intrinsic` consumes. KEY: III.4.8 (`addHomProperty`,
  PROVEN) gives `φ(P+T)=φ(P)` for `T∈ker φ`, i.e. `φ∘τ_T=φ`; lift to `τ_T*∘φ*=φ*` (generic point). Source:
  III.4.10b proof (p.72) "`τ_T*(φ*f)=(φ∘τ_T)*f=φ*f`". **The genuine remaining content** (point→generic-pt lift).
- [CLEANUP-D1] Run /cleanup on DualGalois.lean — after DUAL-1/DUAL-2 (+ the existing decls there). Depends DUAL-2.

### [DUAL-3] `universal_dualGaloisData` for separable φ → isogeny-class symmetry (separable)
- Status: blocked(DUAL-1,DUAL-2,RAMI-1) · File: `EC/IsogenyAG/{Dual,DualGalois}.lean` · Type: theorem (internal) · LOC ~60
- Stmt: `EC.universal_dualGaloisData φ` for separable `φ`+CoordHom+`[Fintype F]`. Assemble
  `fixedField_hfix_of_xy_family_of_card` (REUSE) from DUAL-2+`#ker=deg`+DUAL-1; feed via
  `rangeIncl_of_fixedField` (REUSE) + RAMI-1. Closes `IsIsogenous.symm` for separable φ. Source: III.4.11 (p.73–74).

### [DUAL-4] general/inseparable φ via Frobenius factorization + Verschiebung — DEFERRED
- Status: deferred · `φ=φ_s∘Frob^r` (III.4.10a) + the Frobenius dual. Larger; out of this phase's core
  (DUAL-3 covers the separable case = the bulk + suffices for the separable isogeny-class relation).

### [CLEANUP-D2] final /cleanup on Dual.lean + DualGalois.lean + Bridge.lean + axiom check
- Status: blocked(DUAL-3) · verify the new dual decls axiom-clean; `universal_dual_witness`/`IsIsogenous.symm`
  axiom-clean for separable φ.

---

## Notes
- W1 and W2 are independent (Tate module does not use III.4.8) → can run in parallel.
- `IsAlgClosed F` couples ISO-L6/L7 and the Tate Galois layer to base-change infra — coordinate.
- After approval: `/beastmode` on `tickets-silverman.md`. Suggested first ticket: **ISO-L4** (the whole
  III.4.8 job) or **TATE-L9** (dependency-free mathlib win) in parallel.

---

## Phase 6 — THE DUAL ARC (2026-06-09/10) — status after commits 02ac7c9…55de460

DONE, all axiom-clean (8 commits):
- [RAMI] ord_∞∘φ* formula + e≥1 CoordHom-free (02ac7c9, 6f9a173): `reflects_ordAtInfty`
  UNCONDITIONAL; hnt/hramO eliminated everywhere. New mathlib-grade
  `ordAtInfty_eq_zero_of_isAlgebraic` + `CurveMap.isAlgebraic_toAlgebra`.
- [HGCOMM] generic-point covariance for GENERAL isogenies (07e0c08): engine
  `mapTranslateGenericPoint_of_pullbackEvaluation`; closed outright with a CoordHom over K̄.
- [FIXFIELD] Im(φ*)=Fix(ker φ) over ANY field (5d140da): PointFix's [Fintype F] was
  incidental; capstones dualGaloisData_of_coordHom / exists_dual_of_coordHom.
- [MULBYINT-BP] MulByIntBasepoint at FULL n≠0 incl p∣n (7d42a8a): [n] = witness-free
  EC.Isogeny; FIRST CONCRETE DUAL dualMulByInt ([ℓ]^ as a definition).
- [FROB-DUAL] dualFrobenius = Verschiebung as a definition, V∘π=[q] (1aac34e); no 2≤q gate.
- [FAITHFUL-COMP] [m·n]* multiplicativity field-general + HasMulByIntDualWitness.compose
  (0e0444b); field-general mulByIntSelfDualWitness ([ℓ]^=[ℓ], no IsAlgClosed).
- [REDUCTION] φ = φ_sep∘πʳ (q-power II.2.12) + the faithful [deg φ]-witness from the
  separable part's; Vᵣ∘πʳ=[qʳ]; capstone nonempty_hasDualWitness_of_frobeniusFactorization
  (55de460).

REMAINING (the genuine walls, in value order):
1. [WALL-III.4.10c] #ker = deg for GENERAL separable φ — the AG frontier the Hasse proof
   was engineered around; h_normal/hdesc are its witness form (division-poly-gated for [ℓ];
   provably circular from the fixed-field side). THE single mathematical wall left for the
   fully-general dual / isogeny-class symmetry. Candidate: /expert-review round 24.
2. [II.2.12-EXIST] FrobeniusFactorization existence (the canonical r + Im(φ*) ⊆ Im((πʳ)*))
   + separability of separablePart (EC FinDim + finSepDegree transport).
3. [TWIST] cross-curve Frobenius E → E^(p) (for deg_i = p^k not a q-power; confirmed absent).
4. [ISO-BC] EC.Isogeny.baseChange (K-descent of III.4.8); conductor over ℚ (far LMFDB gap).
5. Housekeeping: /cleanup cadence on the 8 new dual files; IsogenyClass.symm wiring of the
   new concrete instances.

---

## Phase 7 — ROUTE W (round-24 reviewer plan, APPROVED 2026-06-10)

Reviewer verdict (reply: `.mathlib-quality/expert-review/2026-06-10/reply.md`): route W is THE
road (no shortcut exists — Q2); different ideal is the tool; localized affine open, NO global
CoordHom; order W → G1+G2 → CANON-DUAL → III.6.2.

### [W-1] Localized Dedekind setup (NO global CoordHom)
A = 𝒪(U₂) (localization of C₂.CoordinateRing away from the finite bad set), B = integral
closure of A in K(E₁) along φ*. B Dedekind (Krull–Akizuki/mathlib), Module.Finite A B
(separable). Mostly mathlib instantiation.

### [W-2] a.e.-unramified via differentIdeal
Pure Dedekind-level: finite separable L/Frac(A) ⟹ 𝔇_{B/A} ≠ ⊥; ramified ⟹ P ∣ 𝔇; divisors
of a nonzero ideal finite ⟹ ramified A-primes (contractions) finite. Statement for W-3: for
all but finitely many maximal q ⊂ A, every P over q has e = 1.

### [W-3] The good-fibre count (after cleanup lands — wires into existing files)
Σe·f = deg (T3, localized) + f = 1 (K̄) + e = 1 (W-2) + place↔point dictionary ⟹
#φ⁻¹(Q) = deg φ for Q off the bad set; good set nonempty via infinite E(K̄) (ℓ-torsion).

### [W-4] Close the Wall + discharge the chain
T2 torsor transport ⟹ #ker φ = deg φ (separable). Then Im = Fix (T4) ⟹ normality (Artin)
⟹ h_normal; #Aut = deg = #ker + injectivity ⟹ hdesc; discharge universal_dualGaloisData
(separable case) ⟹ IsIsogenous.symm.

### [G1] ker d = K^p (p-basis/separating-parameter; x separates in all chars) + Im φ* ⊆ K^p
via dφ* = 0 ⟹ II.2.12 existence. [G2-TWIST] E^(p^k) explicit cross-curve package (6 items).
[CANON-DUAL] ∃! dual, BOTH compositions (φφ̂ = [deg] is NEW), deg φ̂ = deg φ,
all-witnesses-agree. [III.6.2] last.

### Phase 7 progress (2026-06-10)
- [W-1/W-2] DONE axiom-clean (commit f8bcacb): RamificationFinite.lean (pure AKLB different-
  ideal layer, exists_finite_ramification_locus) + GoodAffineLocus.lean (localized setup).
- [W-3] DONE axiom-clean (commit 78d04bb): GoodFiber.lean (II.2.6b: e=1 off finite locus,
  f=1 over K̄, prime↔point dictionary, exists_good_fiber_card_eq_degree) + KernelCount.lean —
  **card_kernel_eq_degree_of_separable_coordHom: #ker β = deg β for separable β with a
  global CoordHom + PullbackEvaluation over K̄. THE WALL IS CLOSED for that class.**
  Route simplifications: B-identification eliminated (F[C₁] IS the integral closure, standing
  IsIntegrallyClosed); coset transport replaced sepDegree witnesses.
- HONEST BOUNDARY: a separable isogeny with nontrivial AFFINE kernel has pullback poles at
  kernel points ⟹ no GLOBAL CoordHom; covering 1−π/rπ−s-type isogenies needs the LOCALIZED
  CoordHom variant of the dictionary (the reviewer's original W-1 shape) — named follow-up
  [W-3b]. [ℓ] itself already has its count (card_torsion_ell).
- NEXT: [W-4] cascade the count → h_normal (Im=Fix + Artin) → hdesc (counting) → discharge
  universal_dualGaloisData for the covered class → IsIsogenous.symm. Then [W-3b].

### [W-4] DONE axiom-clean (commit c5bdfdb, WallCascade.lean, 11 decls, 0 sorries)
FIELD-GENERAL CORES (inputs only {xy_family, #ker=deg} — no IsAlgClosed/Fintype, no hsep!):
isGalois_of_xy_family_card (Im=Fix + Artin IsGalois.of_fixed_field + ONE IsGalois.of_equiv_equiv
transport ⟹ Galois for β.toAlgebra: h_normal AND #Aut=deg in one shot),
normal_of_xy_family_card (h_normal IS A THEOREM), hdesc_of_xy_family_card (hdesc IS A THEOREM,
by counting: kernelTranslateForwardAut injective + card_aut_eq_degree_of_isGalois + the count
⟹ bijective ⟹ genericPointAct_kernelTranslateForwardAut). Payoff:
dualGaloisData/exists_dual_of_{pullbackEvaluation,coordHom}_unconditional + dualGaloisData_of_class.

### ⚠ APPLICABILITY AUDIT (orchestrator, 2026-06-10) — [W-3b] is the real remaining Wall content
A separable isogeny of degree > 1 has #ker = deg > 1 kernel points, all nonzero ones AFFINE,
and the pullback has poles there (ord_P(β*x) = e·ord_O(x) ≤ −2) ⟹ NO GLOBAL CoordHom exists.
So the W-3/W-4 *_coordHom class = isomorphisms + the abstract interface: the THEOREMS are
correct but the separable deg>1 instances need [W-3b]. THE DURABLE WINS: (a) the field-general
cores (apply to ANY isogeny once its count is known — e.g. [ℓ] via card_torsion_ell +
mulByInt_degree ⟹ [ℓ]'s h_normal/hdesc now follow from the cores, superseding the
division-poly TorsionKernelRational route); (b) all of GoodFiber/RamificationFinite (general).

### [W-3b] The localized dictionary (the genuine Wall for deg>1 separable) — route sketch
Without any global CoordHom: D := integralClosure (C₂.CR)_f K(E₁) (GoodAffineLocus instances).
KEY OBSERVATIONS: (1) x₁,y₁ ∈ D — their only pole is at O₁, which lies over the O₂-place
(the e≥1 ord formula), excised from U₂; Dedekind = ∩ localizations ⟹ membership. Hence
C₁.CR = F[x₁,y₁] ⊆ D and D is integral over C₁.CR. (2) Each maximal P of D over good q:
P ∩ C₁.CR is maximal (lying over) = m_{(a,b)} = a POINT; B_P ⊇ the point-DVR ⟹ EQUAL
(DVR maximality, the e≥1-lemma pattern) ⟹ P ↔ point injectively — NO curve-places
classification needed. (3) Residue realization: f=1 ⟹ ψ : D → K̄; (a,b) := (ψx₁,ψy₁)
satisfies Weierstrass; ψ∘β* on A = evaluation at Q ⟹ pullback-image of (a,b) is Q;
PullbackEvaluation coherence (choose Q avoiding bad-images) ⟹ STORED β(a,b) = Q.
⟹ #fibre(Q) ≥ #maximals over q = deg (Σef=deg + e=f=1). (4) The ≤ direction NOT from
the dictionary: #ker ≤ #Aut ≤ deg via the EXISTING injection kernelTranslateForwardAut +
Galois-theory card bound. (3)+(4) + torsor ⟹ #ker = deg. Pieces: GoodAffineLocus instances,
RamificationFinite (e=1 a.e.), residue-field=K̄ (f=1, GoodFiber pattern), DVR-maximality,
Dedekind-intersection membership (audit mathlib), PullbackEvaluation.

### ★★ [W-3b] DONE — THE WALL IS CLOSED (commit 7d9af4c) ★★
`card_kernel_eq_degree_of_separable` (KernelCountGeneral.lean): #ker β = deg β for ANY
separable Basic isogeny over K̄, witnesses exactly {bad finite, PullbackEvaluation} — no
CoordHom, no module-finiteness. III.4.10c closed for the genuine class. LocalizedDictionary.lean
(1040 lines): monic-minpoly integrality (x₁,y₁ ∈ D), ker-trick point realization (residueChar =
evalAt by same-kernel), new pure DVR lemma le_one_of_forall_le_one_mem_of_ne_top (absent from
mathlib), P ↦ point injective WITHOUT curve-places classification. CASCADE for the class:
normal/hdesc_of_separable_general (theorems), dualGaloisData/exists_dual_of_pullbackEvaluation_general
— **the separable dual is UNCONDITIONAL for the PullbackEvaluation class** (residuals {h_pb, hsep,
bad, hw}). Route W (rounds W-1→W-3b) executed end-to-end per the round-24 reviewer plan.

### NEXT (reviewer ordering): [G1] ker d = K^p + Im(φ*) ⊆ K^p (inseparable) → II.2.12 existence;
[G2-TWIST] E^(p^k) package; then [CANON-DUAL] (∃!, both compositions, deg φ̂ = deg φ,
all-witnesses-agree); [III.6.2] last. Also open: PullbackEvaluation instantiation for concrete
1−π/rπ−s (their OneSub residue machinery is EvaluatesTo-shaped); K̄→K descent layer; ISO-BC.

### [G1] DONE (commit e463755) + [G2] DONE (commit d3983d6) — both axiom-clean, 0 sorries
G1: ker d = K^p was ALREADY in GapQfKernel (kaehlerD_eq_zero_iff_mem_pth_powers, PerfectField);
corollary Im(φ*) ⊆ K^p for inseparable (both worlds, via unconditional T-II-4-004);
frobeniusFactorization_of_qStep (strong induction) ⟹ II.2.12 UNCONDITIONAL over 𝔽_p.
G2: the full twist package — iterateFrobeniusTwist laws, Δ-power ellipticity,
relativeFrobenius p E e : EC.Isogeny E E^(p^e) (NEW reusable builder EC.Isogeny.ofEquation),
deg = p^e FULLY PROVEN (imperfection tower on GapQfKernel's p-case), relativeFrobenius_add,
q-identification = DualReduction.frobeniusPower.

### ⚠ ORCHESTRATOR NOTE: G1's same-curve qStep hypothesis is FALSE over composite q
(e.g. [p] over 𝔽_{p²} has deg_i = p ∉ q-powers) — the GENERAL II.2.12 must be the TWISTED
factorization φ = φ_sep ∘ relativeFrobenius_{p^k} (cross-curve), now stateable with G2.

### [G3-FACTOR] DONE (commit 81482ad) — twisted II.2.12 + relative Verschiebung (TwistedFactorization.lean)
ALL of (a)-(d) landed; 0 sorries in file; build GREEN 8377. AXIOM-CLEAN: the whole of
(a)/(b)/(c) — incl. the BUNDLED twistedFrobeniusFactorization (φ = φs ∘ relFrob_{p^k}, φs
separable, every perfect char-p base), the two-curve G1 generalization (Layer 0:
finiteDimensional/degree_pos'/isSeparable_iff_algebra/kaehlerD engine/p-th powers — was
endo-only), reusable cross-curve Isogeny.factorThrough (basepoint DERIVED), congrSource cast
kit, the s∣k q-power corollary (frobeniusFactorization_of_twisted_sdvd; honest — divisibility
genuinely needed), prime-field re-derivation — AND the hypothesis-threaded (d):
hasDualWitnessRelativeFrobeniusOf/relativeVerschiebungOf with V̂∘Frob=[p^e] bundled +
finale nonempty_hasDualWitness_of_twisted_separable_witnessesOf, all threaded on ONE input
hinsep : ¬[p].IsSeparable. FINITE-base instantiations (_finite) AXIOM-CLEAN via RouteB
a_[p]=0. The ONLY 4 sorryAx decls = the general-base wrappers (mulByInt_p_not_isSeparable,
relativeVerschiebung(+compose), nonempty_..._witnesses) inheriting the STANDING EDS-Wronskian
leaf (omegaPullbackCoeff_mulByInt m≥5); RouteB/SilvermanIV14 are [Fintype]-sectioned (artifact,
not math) — de-Fintyping them would make (d) clean over every perfect base. GOLF (source-check
items, not done): II.2.12 one-step deg_i-exact form via separable-closure index squeeze
(would pin k = v_p(deg_i φ)); the p.82 Frobenius-dual trick ([p] = ψ∘Frob^e ⟹ Frob-hat).

### [G3-FACTOR-orig] (superseded by DONE above) general twisted II.2.12 + relative Verschiebung
(a) twistedFrobeniusFactorization: ∀ φ, ∃ k φ_sep separable, φ = φ_sep ∘ relFrob_{p^k}
(strong induction mirroring frobeniusFactorization_of_qStep, G1 p-step + factorThrough
cross-curve + G2 twist laws + deg bookkeeping). (b) q-power corollary recovers the
same-curve case. (c) STRETCH: hasDualWitness_relativeFrobenius (Im([p^e]*) ⊆ K^{p^e} from
iterated G1-step since v_p(deg_i [p^e]) ≥ e) ⟹ the relative Verschiebung; then arbitrary
dual = sep-part dual ∘ relative Verschiebung — FULLY GENERAL dual existence modulo only
the sep-part's {bad, hw}.

### SOURCE CHECK (Silverman III.6.1 proof, book pp. 81–82, read 2026-06-10) — G3 acceptance criteria
Silverman's actual route (the G3 brief deviated in two places; use these as acceptance/golf criteria):
1. II.2.12 is ONE-STEP, not an induction: 𝕂 := separable closure of ψ*K(C₂) in K(C₁);
   K(C₁)/𝕂 purely insep of degree q = deg_i ⟹ K(C₁)^q ⊆ 𝕂; [K(C₁):K(C₁)^q] = q = [K(C₁):𝕂]
   (have: finrank_KE_over_iterateFrobeniusRange) ⟹ 𝕂 = K(C₁)^q (index squeeze,
   IntermediateField.eq_of_le_of_finrank_eq') ⟹ ψ* image ⊆ Im(relFrob_q)*. deg_i-exact, free.
2. THE FROBENIUS-DUAL TRICK (Case 2, p.82): do NOT build the relative Verschiebung's range
   inclusion by hand. Factor [p] ITSELF: [p]*ω = pω = 0 ⟹ [p] inseparable (HAVE: a_[n]=n +
   unconditional isSeparable_iff_omegaPullbackCoeff_ne_zero) ⟹ II.2.12: [p] = ψ∘(Frob_p)^e,
   ψ separable, e ≥ 1 ("the Frobenius morphism does appear") ⟹ Frob_p-hat := ψ∘Frob_p^{e−1}.
3. Composition/uniqueness freebies (for CANON-DUAL): uniqueness by cancellation
   ((φ̂−φ̂′)∘φ=[0] ⟹ φ̂=φ̂′ via II.2.3); (ψφ)^ = φ̂ψ̂ from uniqueness; III.6.2(a) SECOND
   composition φ∘φ̂=[m] nearly free: (φ∘φ̂)∘φ = φ∘[m] = [m]∘φ (III.4.8!) + cancel φ
   (pullback injectivity). HONEST FLAG: III.6.2(c) dual ADDITIVITY is the hard one —
   Silverman gives char 0 only, punts arbitrary char to Exercise 3.31 (perfect-base footnote).

### B2: universal_dualGaloisData (ISO-DUAL/universal, 2026-06-10) — REFUTED + REWIRED
**Verdict (verified against the exact Lean statement):** `EC.universal_dualGaloisData :
∀ φ : Isogeny W₁ W₂, Nonempty (Isogeny.DualGaloisData φ)` (the last `sorry` of the EC dual
chain, `EC/IsogenyAG/Dual.lean` ~L472) is **FALSE**. The failing field is
`hfix : ∀ z, z ∈ Im(φ*) ↔ ∀ σ ∈ transAut, σ z = z` — an *exact* fixed-field equality with
`transAut` existentially chosen. For the `q`-power Frobenius `π` (`q = pⁿ = #K > 1`):
hfix-forward at `π* z = z^q` makes every `σ ∈ transAut` fix all `q`-th powers; char-`p`
rigidity (`(σz − z)^q = σ(z^q) − z^q = 0`) forces `σ = id`; hfix-backward then forces
`Im(π*) = K(E)` entire — contradicting `x_gen ∉ K(E)^p ⊇ K(E)^q`
(`GapQfKernel.x_gen_not_pth_power`). Sharper than the kernel-triviality framing: `transAut`
is existential, so the proof rules out *every* family, not just the (trivial, `π` injective
on points) kernel translations. `HasDualWitness π` is TRUE and realised (Verschiebung,
`hasDualWitness_frobenius` — the range inclusion `Im([q]*) ⊆ Im(π*)` needs no fixed-field
equality); only the Galois-data *route* to the universal witness is false. `DualGaloisData`
stays correct for separable `φ` (III.4.10c assumes separability) — all separable-class
dischargers untouched.
**Formal refutation shipped (axiom-clean, < 80 lines):** NEW
`EC/IsogenyAG/DualUniversal.lean` — `isEmpty_dualGaloisData_frobenius` (every curve over
every finite field; iterateFrobenius injectivity + `x_gen_not_pth_power`) +
`not_universal_dualGaloisData` (closed ¬∀ at `y² + y = x³` over `𝔽₂`, `IsElliptic` by
`decide`). Imported from the root.
**Rewiring:** `Dual.lean` — `universal_dualGaloisData` / `universal_dual_witness` /
`EC.exists_dual` DELETED, B2 verdict + pointers documented in-file;
`exists_dual_of_witness` (the axiom-clean III.4.11 factoring) unchanged.
`IsogenyClass.lean` — `IsogenyDual.exists_dual` now takes `Nonempty φ.HasDualWitness`; NEW
named gate `def UniversalDualWitness F : Prop`; `IsIsogenous.symm` →
`IsIsogenous.symm_of_witness` (per-pair) / `IsIsogenous.symm_of` (F-level);
`isIsogenous_equivalence` / `isIsogenousSetoid` / `IsogenyClass` gated on
`UniversalDualWitness F` (option 1, lighter; option 2 = witnessed-dual sub-class carrier
documented in the module docstring with its costs, not implemented). All rewired decls
`#print axioms = [propext, Classical.choice, Quot.sound]` — the EC dual chain is now
**0 sorries**. Stale prose mentions of the deleted names remain in
DualGalois/WallCascade/FrobeniusDual doc-comments (outside the B2 edit scope; harmless).
**Honest universal route (open, witness-gated):**
`nonempty_hasDualWitness_of_twisted_separable_witnessesOf` (`TwistedFactorization.lean`)
reduces `∀ φ` over a perfect char-`p` base to the separable side on Frobenius twists.
Discharged witness instances: `[ℓ]` (`mulByIntSelfDualWitness`), `π`
(`nonempty_hasDualWitness_frobenius`), `πʳ` (`frobeniusPowerMulByIntDualWitness`), relative
Frobenius/Verschiebung (`hasDualWitnessRelativeFrobeniusOf`), `1 − π` over `K̄`
(`exists_dual_oneSub`), the separable class over `K̄`
(`exists_dual_of_pullbackEvaluation_general`).
