# Decomposition — rectified Y₀/Y_H gates (v10.345 streams M1 + M2, M3 scoped)

*/develop, 2026-07-22, on dev/modular-curves @ ddba031ef. Companion to board amendment
v10.345-AMEND (tickets.md tail), which records WHY the handover's Gate 1/Gate 2 framing was
replaced (hbase false as stated; hH refutable at Borel; Loeffler 3.8.3 iff; KM 7.4.2/8.1).*

## Skeleton location (Step 2.5 — verified compiling)

- `ModularCurves/ForMathlib/RelativeInvariantSpec.lean` — M1, 17 sorried Props, defs real
  (`invariantsDiagram`, `invariantsDiagramMap`, `invariantsGlueData`, `relQuotient`,
  `relQuotientStruct`, `relQuotientπ`, hoisted `basePullback`).
  `lake build ModularCurves.ForMathlib.RelativeInvariantSpec` ✓ (sorry warnings only).
- `ModularCurves/Moduli/GammaHSemiBorel.lean` — M2, 16 sorried Props, `semiBorel` def real
  (carrier explicit; closure fields sorried).
  `lake build ModularCurves.Moduli.GammaHSemiBorel` ✓ (sorry warnings only).

Verified 2026-07-22 by own builds; no type errors; pre-existing warnings only
(InvariantTorsor unusedSectionVars).

## Prior-B2 consultation (Step 4.6)

`b2_log.jsonl` read (12 entries). Relevant matches: `gammaHNaive_relativelyRepresentable`
(2026-07-09, FALSE for H ≠ ⊥ — the naive global-H-orbit presheaf is not relatively
representable) and `gammaHNaive_representable_of_rigid` (2026-07-09/17, orbit presheaf is
not an fppf sheaf). **Addressed by design**: every new representability statement here is
about `qpd.prob` (the [GHC1] QUOTIENT problem with its couniversal property), never the
naive orbit presheaf; the M2 headline takes `qpd : QuotientProblemData` as an argument
exactly like the landed `gammaH_representable_of_orderOf`. No name- or shape-match with
any new leaf. `legendreDeltaGAction` B2s: untouched quarantined subtree, no interaction.

---

## M1 — the relative-affine quotient over an arbitrary base (Gate 1 rebuilt)

### Plain-English proof (Step 1; sources read this session, pages cited)

KM 7.1.3's quotient step reduces, for the free case, to the quotient of a relatively
affine scheme (KM print p. 190, verbatim):

> "By [De-Ga III, §2, 6.1], we know that if a finite group G operates freely and
> S-linearly on an affine S-scheme X, then the quotient X/G exists, X is a finite etale
> G-torsor over X/G, and the formation of X/G commutes with arbitrary base-change S′ → S."

The construction (De-Ga III §2 6.1 = SGA 3 V §4 shape): for `f : Z ⟶ S` affine with a
`G`-action over `S`, the quotient is the relative Spec over `S` of the invariant
subalgebra of `f_* 𝒪_Z`. Existence of the bare quotient (projection + structure map +
categorical universal property) needs no freeness — KM 7.1.3(1),(4),(5),(6) are stated
for arbitrary finite actions; the integrality of `Aᴳ ⊆ A` is KM print p. 193 (verbatim):

> "Visibly every element a of A is integral over Aᴳ, being a root of the Aᴳ-polynomial
> ∏_g (T − g(a))."

Freeness enters only in (2) (finite étale torsor) and (3c) (base change), whose
chart-level algebra ([A711-FP], [A711-BC], [GHB6-RING]) is PROVEN in the project.

In Lean, "relative Spec of a quasi-coherent algebra" is mathlib's
`relativeGluingData` engine (`Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean`
+ `RelativeGluing.lean`, stacks 01LH): a presheaf `F` on `S.AffineZariskiSite` with
structural map `α : 𝒪_S ⟶ F` that is `Coequifibered`
(`F(D_U(r)) = F(U)[1/α r]`, the iff `coequifibered_iff_forall_isLocalizationAway`)
glues to a scheme over `S` with affine charts `Spec F(U)`, cover, `toBase`, and
chart-pullback squares (`isPullback_natTrans_ι_toBase`). Mathlib's own
`Normalization.lean` (relative normalization = this engine at the integral-closure
presheaf) is the line-by-line template. We run the engine at the invariants presheaf
`U ↦ Γ(Z, f⁻¹U)ᴳ`; the Coequifibered condition is "localization of invariants =
invariants of the localization" for finite `G` — proven in
`ForMathlib/InvariantLocalization.lean`. The categorical quotient property against an
arbitrary target glues the chart-level `existsUnique_invariantsπ_lift`
(`ForMathlib/AffineQuotient.lean`, proven, SGA I V.1.1/Stacks 07S5-07S7 route per its
header) over the locally-directed cover.

### Leaves (skeleton decl = contract; file `ForMathlib/RelativeInvariantSpec.lean`)

- **M1.0** (leaf): `SchemeAction.isStableOpen_preimage` — `f⁻¹U` is stable under an
  action over `f`.
  - Discharge: project — inline in [GHB3]'s proof already (`GammaHRepresentability.lean:461-464`:
    `show (σ.hom g ≫ f) ⁻¹ᵁ US x = f ⁻¹ᵁ US x; rw [hover g]`); extraction, 3 lines.
  - Source: the stability observation in KM 7.1.1's closing sentence (G acts on the
    S-scheme 𝒫_{E/S}, so over each open of S).
  - Attacks: (1) edge U = ⊥/⊤: preimage stable trivially ✓; (2) hypothesis test: drops
    hover ⇒ false (translate an action not over f) — hover necessary and included via
    `include hover` ✓; (3) discharge attack: the quoted [GHB3] lines exist at the cited
    location (read this session) ✓. SURVIVED.

- **M1.1** (leaf): `SchemeAction.gamma_map_smul` — presheaf restriction along nested
  stable opens is `G`-equivariant.
  - Discharge: project pattern — `gammaMulSemiringAction_smul_def`
    (`SchemeQuotient.lean:166`) + `Scheme.Hom.appLE`-functoriality of `σ.hom g` (the
    same `appLE_comp_appLE` game as `gamma_appLE_invariant`, `SchemeActionFree.lean:207`,
    read this session). ≤ 15 lines.
  - Attacks: (1) shape check vs the localQuotientMap machinery (T-Q5 c-layer) which
    already restricts invariants between nested stable affines — consistent ✓;
    (2) edge: U = V gives `map (𝟙)` — both sides equal by `smul` ✓; (3) hidden
    assumption: none — stability of BOTH opens is carried. SURVIVED.

- **M1.2** (def + 3 Prop leaves): `invariantsDiagram` (functor laws `map_id`, `map_comp`,
  and the `MapsTo`-invariance hole inside `map`).
  - Discharge: M1.1 for the hole; functor laws mirror `normalizationDiagram.map_id/map_comp`
    (`Mathlib/AlgebraicGeometry/Normalization.lean:60-66`, read: `simp; rfl` + `rfl`
    after `Subtype`-ext). Subalgebra-valued maps compare by `Subtype.ext`.
  - Source: the qcoh-algebra presheaf of the De-Ga construction; mirror of
    normalizationDiagram (template file read this session).
  - Attacks: (1) type-check: COMPILES (the strongest attack passed — the map's
    site-≤ vs Opens-≤ mismatch was caught and fixed via `toOpens_mono` during
    skeleton build); (2) composition attack: does obj land in the same
    `FixedPoints.subalgebra ℤ … G` convention the chart layer uses? — YES, matched to
    `quotientDescRing`'s target (`SchemeActionFree.lean:225-231`) with the same
    stability-proof argument, so instances are definitionally shared ✓; (3) discharge:
    `RingHom.invariantsCorestrict` exists (`EtaleCancellation.lean:140`), signature
    verified by read ✓. SURVIVED.

- **M1.3** (leaf): `invariantsDiagramMap.naturality`.
  - Discharge: `Subtype.ext` + `Scheme.Hom.appLE`-naturality of `f` (mirror of
    `normalizationDiagramMap.naturality`, one line in the template:
    `ext x; exact Subtype.ext congr($(f.naturality i) x)`).
  - Attacks: (1) the app-component is `quotientDescRing` whose defining equation
    `ofHom_quotientDescRing_algebraMap` (`SchemeActionFree.lean:235`) makes the square
    commute after composing with the (injective) inclusion — standard corestriction
    naturality ✓; (2) edge: identity morphism ✓ by `map_id`; (3) drift: template line
    read verbatim this session ✓. SURVIVED.

- **M1.4** (leaf, THE algebra core): `coequifibered_invariantsDiagramMap`.
  - Lean: via `coequifibered_iff_forall_isLocalizationAway` (mathlib, signature read),
    reduce to: for `U` affine ⊆ S, `r : Γ(S,U)`:
    `IsLocalization.Away (quotientDescRing r) Γ(Z, f⁻¹(D_U r))ᴳ`.
  - Chart identifications: `f⁻¹U` affine (`IsAffineOpen.preimage`, used at
    `GammaHRepresentability.lean:465`), `f⁻¹(D_U r) = D_{f⁻¹U}(f♯r)`
    (`Scheme.preimage_basicOpen`), `Γ` of a basic open of an affine open is the away-
    localization (`IsAffineOpen.isLocalization_basicOpen`, used at `scratch`/mouth files).
  - Invariants core: "localization of invariants = invariants of the localization",
    finite `G`, invariant element — PROVEN:
    `mem_range_fixedPoints_awayMap_iff` + `fixedPoints_awayMap_injective` +
    `exists_fixed_mk'_eq_of_forall_awayHom_eq` (`ForMathlib/InvariantLocalization.lean:122-184`,
    decl list read this session). Repackage as the `IsLocalization.Away` triple
    (map_units: `α r` maps to a unit since `f♯r` is one and inclusion reflects/preserves
    units on invariants — surj/eq_iff from the two cited lemmas).
  - Source: KM Ch. 7 APPENDIX "BASE CHANGE FOR RINGS OF INVARIANTS" (print p. 215,
    TOC read) — the flat case ∗(A, G, B, B′) at B′ = localization; KM p. 193 (verbatim):
    "The question … is the question of the extent to which formation of rings of
    invariants commutes with extension of scalars." Localization is the flat case,
    unconditional for finite G.
  - Attacks: (1) counterexample search: |G| NOT invertible, action NOT free — does
    localization still commute? YES: `0 → Aᴳ → A ⟶ ∏_γ A` is a kernel and localization
    is exact; the project lemmas are stated `[Finite G]` with no freeness/invertibility
    (signatures read) ✓; (2) edge: `r = 0` — `D_U(0) = ⊥`, sections are the zero ring,
    localization at a nilpotent-image… `IsLocalization.Away 0` of the zero ring holds ✓;
    (3) drift: the mathlib iff's `letI` algebra structure is via `F.map`, matched by
    construction ✓; (4) discharge: all three InvariantLocalization citations exist at
    the cited lines (grep verified). SURVIVED.

- **M1.5** (defs, real, COMPILED): `invariantsGlueData`, `relQuotient`,
  `relQuotientStruct`, `relQuotientπ` — engine applications; no proof content beyond
  the compat hole in `relQuotientπ` (next leaf).
  - Attacks: (1) engine misuse: `relativeGluingData` requires exactly a Coequifibered α
    (mathlib def read) ✓; (2) `pullback₁`-cover chart maps mirror `toNormalization`
    (template read; same `pullbackRestrictIsoRestrict ≫ toSpecΓ ≫ Spec.map (val) ≫ cover.f`
    chain with `Subalgebra.val` for integralClosure ↦ FixedPoints) ✓ COMPILES. SURVIVED.

- **M1.6** (leaf): the glue-compat hole of `relQuotientπ` (charts agree on overlaps).
  - Discharge: mirror of `toNormalization`'s compat block (template read this session:
    rewrite through `Opens.toSpecΓ_SpecMap_presheaf_map_assoc`, `Spec.map_comp_assoc`,
    `colimit.w`); the only change is the algebra presheaf.
  - Attacks: (1) the template's proof is 10 lines and uses only naturality of the
    diagram (M1.2/M1.3) — no integral-closure-specific step (read line-by-line) ✓;
    (2) composition: `colimit.w` for OUR functor is the same shape ✓. SURVIVED.

- **M1.7** (leaf): `relQuotientπ_comp_relQuotientStruct` (`π ≫ f₀ = f`).
  - Discharge: chartwise via `Cover.hom_ext` over `pullback₁`-cover +
    `RelativeGluingData.ι_toBase` (mathlib, read) + `ofHom_quotientDescRing_algebraMap`
    (`SchemeActionFree.lean:235`, the triangle `desc ≫ incl = f.appLE`). Mirror:
    `toNormalization ≫ fromNormalization = f` is proven the same way in the template
    (`normalization` file region :180-200).
  - Attacks: (1) chart cover jointly epi ✓ (open cover); (2) the Spec-side triangle is
    exactly `Spec.map` applied to the cited project lemma ✓. SURVIVED.

- **M1.8** (leaf): `hom_comp_relQuotientπ` (invariance `σ.hom γ ≫ π = π`).
  - Discharge: chartwise: `σ.hom γ` restricts to each `f⁻¹U` (M1.0 stability) and on
    `Spec Γ(f⁻¹U)`-level is `Spec (γ♯)`; `γ♯` fixes the invariants pointwise, so
    `Spec(γ♯) ≫ Spec(val) = Spec(val)` — `Spec.map_comp` + the defining property of
    `FixedPoints.subalgebra`. Glue by cover-ext. (The affine-level fact is the
    `specSMul`-invariance used throughout `AffineQuotient.lean`.)
  - Attacks: (1) direction of `Spec.map` vs the action convention (`SchemeAction.spec`
    uses `specSMul`, `hom_mul` covariant — signature read) — the equivariance of
    `toSpecΓ` w.r.t. the restricted action is the one bridging step; it is the
    `gammaMulSemiringAction`-definition unfolding (`smul_def :166`) ✓; (2) edge γ = 1 ✓
    trivial. SURVIVED.

- **M1.9** (leaf): `isAffineHom_relQuotientStruct`.
  - Discharge: `IsAffineHom` is local at the target (mathlib `IsZariskiLocalAtTarget`);
    over each `U ∈ S.affineOpens`, `toBase⁻¹(U) = chart = Spec F(U)` affine
    (`toBase_preimage_eq_opensRange_ι`, mathlib, read).
  - Attacks: (1) the preimage lemma is per-chart-of-the-cover, and cover ranges =
    affine opens of S — covers S ✓ (`directedCover` is by ALL affine opens);
    (2) discharge names verified by read ✓. SURVIVED.

- **M1.10** (leaf): `isIntegralHom_relQuotientπ`.
  - Source: KM print p. 193 (verbatim above — `∏_g (T − g(a))`).
  - Discharge: chart bridge (M1.12) + affine-level: `A` integral over `Aᴳ` — mathlib
    `prod_X_sub_smul` (`Mathlib/Algebra/Polynomial/GroupRingAction.lean`; monic, kills
    `a`, coefficients invariant) — VERIFY exact name at execution; fallback 15-line
    direct proof from the KM polynomial. `IsIntegralHom` local at target.
  - Attacks: (1) needs NO freeness/finiteness of f ✓ KM states (4) unconditionally;
    (2) name risk flagged (execution verifies; not a plan-blocker). SURVIVED (with
    flagged verification).

- **M1.11** (leaf): `existsUnique_relQuotientπ_lift` — the categorical quotient
  property vs arbitrary `Y`.
  - Discharge: chart-level `existsUnique_invariantsπ_lift`
    (`ForMathlib/AffineQuotient.lean:519`, PROVEN — its header cites SGA I V.1.1;
    Stacks 07S5/07S7) transported through the chart bridge (M1.12), glued by
    `glueMorphismsOfLocallyDirected` (existence) + cover-ext with π-epi-on-charts
    (uniqueness; `epi_localQuotientπ`-analogue / `invariantsπ_hom_ext`
    `AffineQuotient.lean:243`).
  - Source: KM 7.1.3(1) (print p. 187, verbatim): "The quotient 𝒫/G exists … For any
    relatively representable 𝒫′, with trivial G-action, any G-equivariant map 𝒫 → 𝒫′
    factors uniquely through the projection 𝒫 → 𝒫/G" — the scheme-level engine behind
    it (its Construction-proof, p. 190).
  - Attacks: (1) glue-compat of the local lifts on overlaps: agreement holds after
    composing with the (epi) chart projections, then cancel — the same pattern as the
    current [GHB3] consumer's `existsUnique_quotientπ_lift` (T-Q5d, PROVEN) ✓;
    (2) counterexample search: categorical quotients of free finite actions vs
    non-free — the ∃!-property needs NO freeness at the affine level (AffineQuotient's
    lemma has no freeness hypothesis — signature read) ✓; (3) composition: Y arbitrary
    (not over S) — chart-level lemma is already stated vs arbitrary Y ✓. SURVIVED.

- **M1.12** (leaf): `isPullback_relQuotientπ_chart` — the chart bridge.
  - Discharge: `isPullback_natTrans_ι_toBase` (mathlib, read: charts of a
    RelativeGluingData are pullbacks) pasted with the `relQuotientπ`-chart triangle
    (`map_glueMorphismsOfLocallyDirected`) and `pullbackRestrictIsoRestrict`.
  - Attacks: (1) the four legs type-checked at skeleton time (COMPILES) ✓; (2) this is
    the exact transfer normalization uses for its `IsIntegralHom` instance (template
    :428 region) ✓. SURVIVED.

- **M1.13-15** (leaves, free case): `isFinite_relQuotientπ_of_free`,
  `etale_relQuotientπ_of_free`, `surjective_relQuotientπ_of_free`.
  - Discharge: chart bridge + affine-level free-action cores, ALL PROVEN:
    `isFreeAlgebraAction_of_free` (`SchemeActionFree.lean:58`),
    `Module.Finite/Projective.of_isFreeAlgebraAction` + `Algebra.Etale.of_isFreeAlgebraAction`
    (used at `EtaleCancellation.lean:170`, read), `fppf_invariantsπ`
    (`SchemeActionFree.lean:463`), surjectivity chartwise (integral + injective-on-
    invariants; the existing `quotientπ_surjective` chart core). Each property is
    local at the target.
  - Source: KM 7.1.3(2)/(4) via De-Ga III §2 6.1 (p. 190 quote above).
  - Attacks: (1) [A711-FP] history: `Algebra.Etale.of_isFreeAlgebraAction` was once
    sorried — verified NOW: used as an instance-argument in PROVEN
    `RingHom.invariantsCorestrict_etale` and the receipts are axiom-clean (v10.343
    census) ⟹ it is proven in-tree ✓ (grep + census); (2) locality: all three are
    `IsZariskiLocalAtTarget` in mathlib ✓. SURVIVED.

- **M1.16** (leaf): `exists_quotient_of_isAffineHom_rel` — the [GHB3]-shape package.
  - Assembly of M1.5/7/8/11: `⟨relQuotient, relQuotientπ, relQuotientStruct, M1.7,
    M1.8, M1.11⟩`. One-line-per-component assembly node.
  - Attacks: conclusion tuple diffed against `exists_quotient_of_isAffineHom`
    (:450-453) — IDENTICAL modulo the deleted instance (copied from the live file) ✓.

- **M1.17** (leaf): `exists_relQuotient_baseChange_of_free` — the [GHB5]-shape package.
  - Source: KM 7.1.3(3c) (print p. 188, verbatim): "there is a natural S-morphism
    (𝒫_{E/S})/G → (𝒫/G)_{E/S}, which is bijective on geometric points. It is an
    isomorphism if any of the following conditions hold: … c) G operates freely on 𝒫."
    + the p. 190 base-change clause of De-Ga III §2 6.1.
  - Discharge: mirror the CURRENT [GHB5] proof body (:565-660 read in part: πT :=
    `pullback.map`, invariance by `hom_ext`, universal property via the chart-level
    base-change) with the chart-level cores `exists_invariantsπ_lift_baseChange_of_free`
    (`AffineQuotient.lean:1153`, PROVEN) + `epi_pullback_snd_invariantsπ_of_free`
    (`AffineQuotient.lean:946`, PROVEN) transported through the chart bridge M1.12.
  - Attacks: (1) freeness genuinely needed (KM lists (c); the log's own docstring:
    "without freeness the statement is FALSE") — hypothesis carried ✓; (2) tuple diff
    vs :558-564 — identical modulo instance ✓; (3) the current GHB5 proof's only use
    of the diagonal was the concrete-atlas construction — the ported proof replaces
    exactly that ✓. SURVIVED.

### Consumer rewires (tickets; statements already in-tree are the contracts)

- **M1.R1**: `exists_quotient_of_isAffineHom` (GammaHRepresentability:445) — delete the
  diagonal instance; body := delegate to M1.16. Statement otherwise byte-identical.
- **M1.R2**: `quotientπ_finite_etale_surjective` (:484) — delete instance; body: the
  existing unique-iso comparison (:516-533) against `relQuotient` (M1.11/13/14/15).
- **M1.R3**: `exists_quotient_baseChange_of_free` (:545) — delete instance; body :=
  delegate to M1.17 (+ the same comparison-iso to align an arbitrary (π,f₀,hdesc)).
- **M1.R4**: delete `hbase` from `nonempty_quotPkg` (:749), `QuotPkg.*` threading
  (:733-3230), `exists_quotientProblemData` (:3184), `gammaH_relativelyRepresentable`
  (:3553); delete the hoisted `basePullback` copy (:288) and import
  `RelativeInvariantSpec`. Mechanical (hypothesis deletion strengthens statements).
  ALSO delete `isAffineHom_diagonal_terminalFrom_of_isAffineHom` consumers'
  plumbing at :756-829 where it only served hbase.

---

## M2 — semi-Borel hfree (Gate 2 rectified) + the Borel no-go

### Plain-English proof (Step 1)

**KM 7.4.2(3) (print p. 198, verbatim):**
> "The natural map [Γ(N)] → [Γ₁(N)], (P,Q) ↦ P identifies [Γ₁(N)] with the quotient of
> [Γ(N)] by the "semi-Borel" subgroup (1 *; 0 *) of GL(2, ℤ/Nℤ)."

**Loeffler Prop 3.8.3 (p. 19, verbatim):**
> "𝒫_H is rigid on Ell/R[1/6] if and only if the preimage in SL₂(ℤ) of H ∩ SL₂(ℤ/N)
> contains no elements of finite order (i.e. has no elliptic points and does not
> contain −1)."

For `H ≤ semiBorel`, the preimage of `H ∩ SL₂` lands in the preimage of
`{(1 b; 0 d)} ∩ SL₂ = {(1 b; 0 1)}`, i.e. in `Γ₁(N)` (upper form), torsion-free for
`N ≥ 4` — the 3.8.3 condition holds, so rigidity is TRUE; we prove it directly (no
char-0 lifting needed, unlike Loeffler's sketch for general H): a `γ`-twisted fixed
point `(gammaHAut γ)(e^* b) = b` untwists (γ acts by `glSmul γ⁻¹`, `gammaHAut_app_val`)
to `e^* b = glSmul γ b`; taking first components with `γ = (1 b'; 0 d)` (`glSmul`
convention `g•(P,Q) = (g₀₀P + g₁₀Q, g₀₁P + g₁₁Q)`, so the first output is
`1•P + 0•Q = P`) gives `pullSection e P = P`. Over `k̄` the section `P` of a naive full
level structure has exact order `N` (the structure pins a basis of `E[N](k̄) ≅ (ℤ/N)²`).
A base-identical iso fixing a point with multiples `1..N−1` nonzero is the identity —
the PROVEN keystone `aut_endo_eq_one_of_fixes_point` with `hbound` discharged by
`hbound_of_kvc` (exactly the Γ₁-closure route). Hence `e = refl`, contradiction: hfree
holds; `gammaH_rigidNoeth` + the engine conclude `P_H` representable.

**No-go**: for `−1 ∈ H` (Borel), rigidity is FALSE (3.8.3), and the old `hH` pin is
refutable by the witness `e = negIso` (`negIso² = refl` via `negHom_comp_negHom`;
`negIso ≠ refl` via T-H7c `mulByHom_neg_one_ne_id`; `orderOf(−1) = 2` for `N ≥ 3`).

### Leaves (file `Moduli/GammaHSemiBorel.lean`)

- **M2.1** `semiBorel` closure fields (3 sorried Props) + `mem_semiBorel_iff` (rfl ✓
  compiled). Discharge: 2×2 entry computation
  (`Matrix.GeneralLinearGroup.coe_mul/one/inv`-layer + `Matrix.mul_apply`,
  `Fin.sum_univ_two`; inverse via adjugate/2×2 inverse entries or
  `Matrix.nonsing_inv`-entry lemmas — small). Attacks: (1) closure truth: (1 b;0 d)(1 b';0 d')
  = (1, b'+bd'; 0, dd') ✓; inverse (1, −b d⁻¹; 0, d⁻¹) — entries: g⁻¹₀₀ = 1, g⁻¹₁₀ = 0 ✓
  by adjugate formula (det g = d unit) ✓; (2) convention drift: the carrier's
  `g 1 0 = 0` is the LOWER-LEFT entry per the project's `glSmul` reading (verified
  against `glSmul` source: first output uses `m 0 0`, `m 1 0`) ✓; (3) is this KM's
  semi-Borel? KM's (1 *; 0 *) with the (P,Q)γ = (aP+cQ, bP+dQ) right-action (KM 7.4.1
  read) — matches (a = g₀₀ = 1, c = g₁₀ = 0) ✓. SURVIVED.

- **M2.2** `EllipticCurve.glSmul_fst_of_mem_semiBorel`. Discharge: unfold `glSmul`
  (source read: first component `((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2`),
  rewrite entries by membership, `ZMod.val_one` (needs `1 < N`) + `ZMod.val_zero`,
  `one_smul`/`zero_smul`/`add_zero`. Attacks: (1) `N = 1` edge: `(1 : ZMod 1).val = 0`
  — hypothesis `1 < N` carried ✓; (2) `.val`-cast: the smul is via `(val : ℤ)` exactly
  as in glSmul ✓ (read); (3) none hidden. SURVIVED.

- **M2.3** `gammaFullNaive_fix_fst_of_le_semiBorel`. Discharge: untwist block copied
  from `gammaH_hfree_of_orderOf_absurd` (:862-874, read verbatim this session:
  `gammaHAut_app_val` + `glSmul_mul` + `mul_inv_cancel` + `glSmul_one` + the `inv_inv`
  coe lemma), then M2.2 at `γ` (membership from `hle γ.2`), then
  `congrArg (fun z => z.1.1)` (the `h1`-extraction pattern of
  `gammaFullNaive_twist_pow_refl` :767, read). NOTE the untwisted equation is
  `map e.op b = glSmul γ b`; its FIRST component is
  `pullSection e b.1.1 = (glSmul γ b).1.1 = b.1.1` — the functor's map-action on the
  pair is the `pullSection` pair (as consumed by twist_pow_refl's h1). Attacks:
  (1) twist direction: `gammaHAut_app_val` says γ acts by `glSmul (γ⁻¹)` (read :3418);
  untwisting multiplies by `glSmul ((γ⁻¹)⁻¹) = glSmul γ` on the LEFT of the fix — the
  exact 4 lines at :864-871 do this and land `glSmul γ (…) = …` with γ un-inverted;
  composing via glSmul_mul in the SAME order as :866 — result shape verified against
  the downstream consumer twist_pow_refl's hcon (which receives `E.glSmul γ (map e b) = b`
  post-cancel — CAREFUL at execution: the extraction wants `map e b = glSmul γ b`; from
  `glSmul γ⁻¹ (map e b) = b` apply `glSmul γ` to get `map e b = glSmul γ b` — one
  glSmul_mul step; the :866-871 block does the (γ⁻¹)⁻¹-coe bookkeeping); (2) edge
  γ = 1: conclusion still derivable (pullSection e P = P from plain fix) ✓ consistent;
  (3) b-components: `z.1.1` projection well-typed (b : FullLevelPt = Subtype of pair) ✓
  compiled. SURVIVED.

- **M2.4** `gammaFullNaive_fst_smul_ne_zero`. Discharge: the [GH2-core] geometric-fibre
  machinery: `torsion_geometricFibre_rank_two` (cited in [GH2]'s docstring :3427, read)
  pins `E.Point`-torsion at the k̄-point ≅ `(ℤ/N)²`; the naive full-level generation
  clause (`IsNaiveFullLevel`'s fibre clause, consumed the same way in `glSmul`'s
  membership proof, read :126-134) makes `(P,Q)` a generating pair, hence `P` a basis
  vector, hence of exact additive order `N` (a generating pair of `(ℤ/N)²` has both
  components of order `N`: if `aP = 0`, `0 < a < N`, then `|⟨P,Q⟩| ≤ a·N < N²`).
  Template: `gammaFullNaive_freeAction`'s proof ([GH2], same file) does exactly this
  identification. Attacks: (1) base = Spec k̄ itself so `t = 𝟙` — the fibre clause
  instantiates at any `t : T ⟶ base`; at `t = 𝟙` ✓; (2) `hinv` needed (char p | N
  would shrink E[N]) — carried ✓; (3) order argument: `|⟨P,Q⟩| ≤ ord(P)·ord(Q)` —
  standard, no gap ✓; (4) counterexample search: none (basis vectors have order N).
  SURVIVED.

- **M2.5** `gammaFullNaive_fix_fst_absurd`. Discharge: mirror
  `gammaOneDrinfeld_fix_absurd` (:1152-1290; route per its docstring, read: fixed
  section is `c`-fixed via `pullSection`/`lift_fst`, εO invertible from `e`, keystone
  kills) with: `hord` := M2.4 (naive supply — REPLACES the T-D6b Drinfeld boxes; this
  proof consumes NO Drinfeld machinery), keystone :=
  `aut_endo_eq_one_of_fixes_point` (`ExactOrderRigidity.lean:83`, read: takes ε pointed,
  P, hord, hfix, hbound), `hbound` := `hbound_of_kvc R N hN`-shape
  (`KeystoneGeometricPoint.lean`, "the literal hbound pin statements … dischargeable
  verbatim", header read; the Γ₁ closure consumes it at :180). Endgame: `εO = 𝟙` ⟹
  `e.hom.top = 𝟙` ⟹ `e = refl` (EllHom.ext + baseHom = 𝟙) ⟹ `hne` kills. Attacks:
  (1) hbound_of_kvc arity: stated for the GammaHMaster:1206/GammaHClosure:152 pin
  shapes — my keystone call must adapt its per-(k,E,ε) instance; the Γ₁ closure's
  discharge (:176-180) is the worked example to mirror ✓; (2) pointedness of εO: `e`'s
  `zero_w` gives `η ≫ ε = η` ✓ (same as Γ₁ case); (3) `hN : 4 ≤ N` propagates to the
  keystone's `N`-window and hbound's — same window as Y₁ (4 ≤ N) ✓; (4) char/j edge
  cases (j=0 char 2,3 exotic autos): the keystone route is counting-based ("NO Hasse,
  NO degree theory" — header read) and already carried Y₁ unconditionally; an exotic
  auto fixing an exact-order-N point would contradict it — consistent with the matrix
  check: an order-3 auto has char poly x²+x+1 with no eigenvalue 1 unless 3 ≡ 0, and
  even then the fixed vector cannot have exact order N (execution does not need this
  side-check; the keystone subsumes) ✓. SURVIVED.

- **M2.6** `gammaH_hfree_of_le_semiBorel` (assembly): M2.3 → M2.5. One-glue lemma.
  Attacks: statement diffed against `gammaH_rigidNoeth`'s hfree pin (:1033-1043) —
  IDENTICAL shape (copied) ✓.

- **M2.7** `gammaH_rigidNoeth_of_le_semiBorel` (assembly): `gammaH_rigidNoeth` (:1029,
  PROVEN) + M2.6. Needs `hN : 3 ≤ (N:ℤ)` from `4 ≤ N` (omega-cast). ✓.

- **M2.8** `gammaH_representable_of_le_semiBorel` (assembly): mirror
  `gammaH_representable_of_orderOf` (:1123-1138, read):
  `representable_of_affineOverEll_of_rigidNoeth qpd.prob qpd.affineOverEll
  qpd.affineOverEll.relativelyRepresentable (M2.7)`. Attacks: (1) `qpd.affineOverEll`
  is a field/derived-lemma of QuotientProblemData used by the orderOf version —
  same consumption ✓; (2) B2-log check: representability claimed for qpd.prob (the
  couniversal quotient problem), NOT the naive orbit presheaf — the 07-09/07-17 B2s
  do not apply ✓. SURVIVED.

- **M2.9** `orderOf_neg_one_gl`. Discharge: `orderOf_eq_prime`-shape: `(−1)² = 1` and
  `−1 ≠ 1` in `GL₂(ZMod N)` for `N ≥ 3` (entrywise: `(-1 : ZMod N) ≠ 1` since
  `2 ≢ 0 mod N`… (−1)=1 ⟺ N ∣ 2 ⟺ N ≤ 2). Attacks: (1) N = 2 edge: −1 = 1, order 1 —
  hypothesis `3 ≤ N` carried ✓; (2) `orderOf_eq_prime` exists (mathlib, standard) —
  verify name at execution (fallback: `orderOf_eq_of_pow_and_pow_div_prime` or direct).
  SURVIVED.

- **M2.10** `isoPow_negIso_two`. Discharge: `isoPow` unfolds (def :578) to
  `refl ≪≫ negIso ≪≫ negIso`-associativity; `Iso.ext` + `negHom_comp_negHom`
  (GammaH.lean:577, PROVEN, read). ✓.

- **M2.11** `negIso_ne_refl`. Discharge: `Iso.ext`-contrapositive:
  `negIso = refl → negHom.top = 𝟙 → mulByHom (−1) = 𝟙`, killed by
  `mulByHom_neg_one_ne_id` (GammaH.lean:613, PROVEN, read — needs only the geometric
  point `t`). Attacks: (1) `negIso.hom.top = mulByHom (−1)` — by def (read :565-575) ✓;
  (2) congrArg through Iso.hom/EllHom.top — plumbing only ✓. SURVIVED.

- **M2.12** `hH_refuted_of_neg_one_mem` (assembly): witness `⟨negIso, rfl-ish base,
  M2.11, ⟨⟨−1, hmem⟩, by rw [M2.9]; exact M2.10⟩⟩`. Attacks: (1) the ∃-statement is
  the literal negation-witness of the hH pin ∀-instance at (k,sm,E) — diffed against
  the pin (:1127-1134) ✓; (2) `negIso.hom.baseHom = 𝟙` — by def ✓. SURVIVED.

### Internal-node attacks (compositions)

- M1 chain (diagram → coequifibered → glued → π/f₀ → universal property → packages):
  could all leaves hold and `exists_quotient_of_isAffineHom_rel` still fail? The
  package is literally the tuple of the leaves — no composition risk beyond
  definitional alignment, which COMPILES. The genuinely composite nodes are M1.11 and
  M1.17 (glue-of-local-lifts): their risk is the overlap-agreement step, attacked
  above (epi-on-charts cancels; the same pattern is PROVEN in T-Q5d for the old
  construction — the argument transplants because both quotients have epi chart
  projections and unique local lifts).
- M2 chain: could M2.3 + M2.5 hold and M2.6 fail? M2.6's hypothesis set is the union;
  the only glue is `hle γ.2 : ↑γ ∈ semiBorel` — type-checks (compiled statement) ✓.
- Cross-stream: M2.8 consumes any `qpd`; M1 supplies it unconditionally later —
  independence verified (M2 buildable before M1 lands; headline closure ticket joins
  them afterward).

---

## M3 — Y₀(N) coarse scheme: AUDIT ONLY (gap list for a follow-on /develop)

Statement of record (KM 8.1.1 print p. 224, verbatim): "We define M(𝒫) as the quotient
scheme M(𝒫) = M(𝒫, δ)/G. The resulting R-scheme is clearly independent of the
auxiliary choice of δ (and so patches together). It 'exists' because M(𝒫, δ) is itself
affine." + KM 8.1.5 (p. 226): "M(𝒫)/G ≅ M(𝒫/G)." + Loeffler Def 3.6.2 (p. 17):
"Y₀(N) = Y₁(N)/(ℤ/N)ˣ (as a ℤ[1/N]-scheme)" and p. 18: "Fact: Y₀(N) is smooth over
ℤ[1/N]" (M4, parked).

Gap audit (verified against the tree):
1. **Representing-object extraction**: `ModuliProblem.Representable` is bare
   (`P.IsRepresentable`-shape, EllCategory.lean:208-229) — no landed API extracting THE
   representing `EllObj`/scheme with its universal structure. GAP: a
   `RepresentingData`-chooser + transport of the `gammaHAut`-action onto the
   representing scheme (the `[GHB1]`/`RepresentableAut` machinery exists for the
   relative level; absolute-level transport to `Aut(scheme)` needed).
2. **Absolute affineness of Y(N)**: `gammaFullNaive_affineOverEll` (GammaHClosure:104)
   is affine-over-Ell; "the representing scheme is an affine scheme" (KM's "M(𝒫,δ) is
   itself affine") is NOT landed. Route: Y(N) → (coarse j-line / a rigidified affine
   chart) finite/affine composition, or extract from the engine's construction. GAP.
3. **Quotient step**: once (1)+(2) land, `Y₀ := Spec Γ(Y(N))^Borel`-level quotient is
   the EXISTING affine machinery (`AffineQuotient.lean`) — no new engine needed (the
   M1 relative machinery covers it a fortiori at S = Spec ℤ[1/N]).
4. **Coarse k̄-points**: `qpd.geom_orbits/geom_surjective` (M1-unconditional at Borel)
   + the quotient's fibre=orbit description (`SpecGroupAction` layer) compose to
   KM 8.1.3.1's "M(𝒫)(k̄) = iso classes". Assembly-level, no new math expected.
5. **Smoothness /ℤ[1/N]** (M4): genuinely new (KM Ch. 8/10 or Loeffler's j(z),j(Nz)
   sketch). PARKED.

---

## Confidence gate (Step 5)

1. Every leaf discharged from mathlib (cited, signatures read this session) or project
   code (cited file:line, read), or explicitly the assembly of sibling leaves. The two
   flagged name-verifications (`prod_X_sub_smul`, `orderOf_eq_prime`) have in-plan
   fallbacks and do not gate the architecture. ✓
2. Skeleton compiles (both files, own builds, sorry-warnings only). ✓
3. Verbatim source quotes: KM p. 187/188/190/193/198/224/226 (page images read this
   session), Loeffler pp. 17-19 (read). Per-leaf quotes above. ✓
4. Adversarial blocks per leaf + internal nodes above (≥3 attacks each; the skeleton
   build itself was the live discharge-attack and caught one real defect —
   site-≤ vs Opens-≤). ✓
5. b2_log consulted; matches addressed by design (qpd.prob, not orbit presheaf). ✓
6. Tree mirrors the sources: M1 mirrors KM 7.1.3's Construction-proof + the mathlib
   normalization template (the template IS the source's construction in Lean form);
   M2 mirrors the landed Γ₁-closure chain (which mirrors KM 7.4.2(3)/Loeffler 3.8.3).
   LOC anchors: normalizationDiagram→toNormalization ≈ 200 lines mathlib for the
   template (read) ⟹ M1 defs+glue ≈ 300-450 project lines; the Γ₁ fix_absurd body
   ≈ 140 lines (read) ⟹ M2.5 ≈ 100-160 lines. ✓
7. Single-conclusion: free-case tuple split into three lemmas (M1.13-15); the two
   ∃-packages (M1.16/17) are marked assembly/package nodes matching the EXISTING
   in-tree consumer contracts (documented exception: shared-witness existential — the
   Z₀/π/f₀ witness is shared across clauses, per statement-splitting.md). ✓

**Feasibility**: every leaf is discharged from proven project code (InvariantLocalization,
AffineQuotient, SchemeActionFree, EtaleCancellation, ExactOrderRigidity,
KeystoneGeometricPoint, GammaHMaster) or read-verified mathlib API
(SmallAffineZariski/RelativeGluing/Normalization-template); no leaf requires new
mathematics beyond assembly. The plan deletes a false hypothesis (hbase) rather than
proving it, and replaces an impossible pin (hH at Borel) with the true rigidity input —
both moves grounded in KM/Loeffler verbatim. M1 is the largest engineering item
(template-mirroring + two consumer-body ports); M2 is a short arc reusing the Γ₁
endgame verbatim with a simpler (naive) order supply.
