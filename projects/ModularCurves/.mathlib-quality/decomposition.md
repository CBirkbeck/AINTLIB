# Decomposition for T-W7 — constructive group law + canonicity (adversarial pass)

**Mode:** `/develop --decompose` (adversarial), 2026-07-07. **Scope:** T-W7 only. The prior
whole-programme Phase-1 artifact (2026-07-05) is preserved verbatim as
`decomposition-2026-07-05-phase1.md`. **Verbatim source quotes** live in
`tw7-source-quotes.md` (locators into the regenerable text layers of the LOCAL-ONLY refs);
this file quotes the load-bearing lines inline and points at the quotes file otherwise, to
keep one canonical quote per passage.

## Skeleton location

Every leaf below exists as a `sorry`-bodied declaration in:

- `ModularCurves/EllipticCurve/PoleFiltration.lean` (lane P3 — 10 decls)
- `ModularCurves/EllipticCurve/ModelVariableChange.lean` (lanes P3/P5 — 6 decls)
- `ModularCurves/EllipticCurve/PointsDictionary.lean` (lane P2 — 8 decls)
- `ModularCurves/EllipticCurve/GroupLawConstruction.lean` (lanes P0/P1 — 32 decls)
- `ModularCurves/EllipticCurve/WeierstrassAtlasBundle.lean` (lane P5 — structure + 3 decls)
- `ModularCurves/EllipticCurve/Rigidity.lean` (lane P4 — def + 6 decls)
- `ModularCurves/EllipticCurve/GroupLawDescent.lean` (join — 9 decls; `toEllipticCurve` and
  its geometry-spec `toEllipticCurve_geom` are REAL — the assembly node already compiles by
  `rfl`)

plus the two pre-existing root targets in `GroupLaw.lean` (`abelEnrichment_exists`,
`abelEnrichment_unique`, both `sorry` since creation — unchanged).

`lake build ModularCurves.EllipticCurve.GroupLawDescent` (the top of the import chain)
**passes — "Build completed successfully (2969 jobs)"**, sorries only, no type errors,
2026-07-07. One pre-existing unrelated sorry in scope: `Point.asSection_zsmul`
(`GroupLaw.lean:268`, PARKED T-D6a-ii, other ticket).

## Result R-A (T-W7a): `abelEnrichment_exists`

### Plain-English proof (Step 1 prose; sources: reviewer round-1 reply §3, B–L, audit)

Let `G = (E, π, 0)` be locally Weierstrass over arbitrary `S`. (1) For every ring `R` and
elliptic `W/R`, the two Bosma–Lenstra addition laws — the bidegree-(2,2) polynomial triples
attached (Thm 2) to the lines `Z=0` and `Y=0` — are each regular on the open complement of
their exceptional divisor; the two exceptional divisors are disjoint over every field
(`O ∉ {Y=0}`), so the two opens cover `E ×_R E`; the laws agree on the overlap (both compute
the chord–tangent sum); gluing yields a morphism `m_W : E ×_R E → E` over `R`, and similarly
the (denominator-free, total) negation. (2) On field points, `m_W` computes mathlib's
`Point.add` through the (proven) dictionary. (3) Over the *universal* ring
`R_u = ℤ[a₁..a₆][Δ⁻¹]` — a domain — the atlas products are *reduced*, so two morphisms into
the (separated) model agreeing on all field-valued points are equal; each group axiom,
checked at field points, is mathlib's group axiom on `Point K`; hence the axioms hold for
the universal `m` as morphism identities. (4) For arbitrary `W/R`: `W` is the pushforward of
the universal curve along its classifying map (`Xᵢ ↦ aᵢ`, legal since `Δ ↦` unit), and `m_W`
is the base change of the universal `m` (the B–L coefficients enter polynomially —
naturality), so each axiom identity transports by base change. (5) Over `S`: choose a
bundled atlas; per chart the transported model law; on overlaps the two pointed chart
presentations differ by a *variable change* (comparison theorem — via the pole filtration:
a pointed iso preserves the affine part and the filtration; freeness of `F₂`/`F₃` forces
`x' ↦ αx+β`, `y' ↦ γy+δx+ε`, `α,γ` units, `α³=γ²` ⟹ `u = γ/α`), and the model law is
VC-equivariant (globally — proven over the universal VC-base domain by the same field-points
method), so the per-chart laws agree and glue. Axioms hold chart-locally (base change of the
universal identity — no flatness, no reducedness of `S`), hence globally (`Cover.hom_ext`).
Package as `GrpObj` + commutativity + unit-normalisation: `abelEnrichment_exists`.

### Attack log for the internal composition (R-A)

- [A] *Could the children hold and R-A fail?* The assembly consumes exactly: glued
  `mulHom`/`negHom` + Over-level axiom equations + unit-normalisation — the
  `GrpObj`/`IsCommMonObj` fields and `EllipticCurve`'s three extra fields, nothing else
  (verified against `GroupLaw.lean:51-59`; and `toEllipticCurve_geom` compiles by `rfl`
  already, so the record-shape composes). Composition gap checked: the Over-level axioms are
  stated for the *model* while the descent needs them for the *glued* structure — bridged by
  chart-locality of morphism equality (`Cover.hom_ext`, mathlib, verified round-1) + the
  chart-specs of the glued maps; recorded as `EllipticCurveGeom.grpObj`'s proof obligation.
  No missing child.
- [B] *Edge case the source doesn't discuss:* `S = ∅` — empty atlas index; everything
  degenerates consistently (`Cover.hom_ext` vacuous). No defect.
- [C] *Does the existence path secretly use reducedness/noetherianness of `S`?* Hypothesis
  sweep of the skeleton: reducedness appears ONLY as instances on the universal atlas
  (`PointsDictionary`); noetherian/connected ONLY in `Rigidity.lean` (canonicity). No leak.

### Leaves (statement + source + provability + attacks per leaf)

Skeleton pointers are file:line of the `sorry` declarations (lines as of this pass).

- **L-0a** (leaf, mathlib+small): `IsDomain WeierstrassAtlasRing` +
  `universalWeierstrass_Δ_ne_zero`.
  - Skeleton: `GroupLawConstruction.lean:49,42`.
  - Source: design (audit); discharge `IsLocalization.isDomain_localization` (mathlib,
    verified via `lean_local_search` → `Mathlib/RingTheory/Localization/Defs.lean`) +
    `MvPolynomial` domain instance; `Δ ≠ 0` by evaluation at `y² = x³ − x` over `ℚ`
    (`Δ = 64`).
  - Attacks attempted:
    - [1] Counterexample: could `Δ = 0` in `ℤ[a₁..a₆]` (trivialising the localization)?
      The evaluation witness refutes; no contradicting lemma found.
    - [2] Edge: characteristic-2 traps in the witness — avoided by evaluating over `ℚ`
      (this attack CHANGED the plan: the earlier draft left the target ring unspecified).
    - [3] Discharge: `isDomain_localization` needs `M ≤ nonZeroDivisors`; supplied by
      domain + `Δ ≠ 0`. Type-checked shape ✓.
    - Verdict: SURVIVED.

- **L-0b** (leaves ×5): `negModelHom` + `_π`, involution, `_zero`, `_specPoints`.
  - Skeleton: `GroupLawConstruction.lean:55,60,65,70,76`.
  - Source: Silverman III.2 (negation `(x,y) ↦ (x, −y−a₁x−a₃)`); projectivised
    `[X : −Y−a₁X−a₃Z : Z]`, a single bidegree-1 total triple; B–L p. 231 (coefficients
    polynomial ⟹ any ring; quotes file §B–L).
  - Lean ↔ source: negation stated on `projModel W` over any `R`;
    π-compat/involution/zero/points-spec one-conclusion-per-decl.
  - Discharge: construction via the `baseChangeGradedHom` template (project, PROVEN,
    `WeierstrassModel.lean:1657`); points-spec via the chart analysis of `projModel_points`
    (project, PROVEN).
  - Attacks attempted:
    - [1] Totality: the triple never all-vanishes on the curve (at `Z=0`: `[0:−Y:0]`,
      `Y ≠ 0` at `O`) — no hidden case split.
    - [2] Edge: 2-torsion (`y = negY x y`) — involution unaffected.
    - [3] Hypothesis-strength: `IsElliptic` NOT needed for the morphism — this attack
      CHANGED the plan: four of five statements weakened to arbitrary `W` (skeleton
      reflects it); kept only on `_specPoints` (dictionary).
    - [4] Source-drift: mathlib `negY = −y − a₁x − a₃` re-verified against the
      `AffinePointVariableChange` development.
    - Verdict: SURVIVED.

- **L-0c1** (leaves ×4): `blOpenZ`, `blOpenY`, `addOnZ`, `addOnY`.
  - Skeleton: `GroupLawConstruction.lean:90,97,104,110`.
  - Source claim (verbatim, B–L Thm 2, p. 230; quotes file): "the pair P₁, P₂ is exceptional
    for the addition law corresponding to (a:b:c) if and only if the difference P₁ − P₂ …
    lies on the intersection of E(K) and the line ax + by + cz = 0"; and p. 230–231: "This
    occurs for instance for the lines y = 0, z = 0".
  - Lean ↔ source match: the opens are the complements of the two named laws' exceptional
    divisors; the morphisms are the §5 triples restricted there.
  - Discharge: opens = complement of common vanishing of the three §5 polynomials;
    triple-on-open ⟹ morphism-to-Proj (repo chart machinery pattern). §5 formulas: local
    PDF; transcribe + CAS-verify at implementation (P1 gate, satisfied — paper acquired).
  - Attacks attempted:
    - [1] False-leaf: is one law secretly total (second unnecessary)? B–L Thm 1: NO — every
      law has nonempty exceptional divisor; two needed, two suffice.
    - [2] Scheme-vs-points: the triple-defines-morphism step is scheme-theoretic
      (basic-open cover); field points only *characterise* the locus — no reliance on
      points to define the map.
    - [3] Char 2/3: B–L's Thm 1/2 carry no characteristic hypothesis (long form, any
      field) — checked in the OCR text; F2(b) double-checks with the reviewer.
    - Verdict: SURVIVED.

- **L-0c2** (leaf): `blOpen_cover`.
  - Skeleton: `GroupLawConstruction.lean:118`.
  - Source (verbatim): B–L p. 230–231, "any two distinct lines in P²(k) that intersect
    outside E(k) give rise to a complete system of two addition laws on E"; the pair
    `{Y=0}, {Z=0}` meets at `(1:0:0)`, and `F(1,0,0) = −1` — never on the curve, any ring.
  - Lean ↔ source: `⊔ = ⊤` ⟺ no point lies in both exceptional loci; fibrewise over fields
    a common point needs `P₁−P₂ ∈ E ∩ {Z=0} ∩ {Y=0} = ∅` since `E ∩ {Z=0} = {O} ∌ {Y=0}`.
  - Attacks attempted:
    - [1] The fibrewise-to-global step: every point of the product lies in a fibre and is
      hit by a residue-field point — sound; recorded as the first proof step.
    - [2] Opens are point-determined — no scheme-density subtlety here (contrast i4).
    - [3] Is `E ∩ {Z=0} = {O}` set-level over any fibre? `Z=0` forces `X³ = 0` ⟹ `X = 0`
      topologically ✓ (nilpotents irrelevant at set level).
    - Verdict: SURVIVED.

- **L-0c3** (leaf): `addOn_agree`.
  - Skeleton: `GroupLawConstruction.lean:127`.
  - Source: B–L Thm 2 (both laws compute the sum where both are defined); scheme-level
    content = bihomogeneous identities modulo the two curve relations.
  - Attacks attempted:
    - [1] Nilpotent failure needs division — none: exact cofactor identities over
      `ℤ[a₁..a₆]`.
    - [2] Proportionality: morphisms to Proj agree via the 2×2-minor identities
      `ℓᵢℓ'ⱼ = ℓⱼℓ'ᵢ` mod relations, not literal triple equality — this attack CHANGED the
      ticket sketch (minor-form recorded).
    - [3] LOC estimate attack: sized by §5's actual display length (~1 page) — grounded.
    - Verdict: SURVIVED (with the minor-identities correction).

- **L-0c4** (leaves ×3): `mulModelHom`, `blOpenZ_ι_mulModelHom`, `blOpenY_ι_mulModelHom`.
  - Skeleton: `GroupLawConstruction.lean:136,141,146`.
  - Source: two-open glue; `Scheme.Cover.glueMorphisms`/`hom_ext` (mathlib, verified
    round-1) or direct opens-gluing.
  - Attacks attempted: [1] glueMorphisms wants pullback-overlaps vs our `homOfLE` form —
    bridge: intersections of opens are the pullbacks of the `ι`s; recorded. [2] glue pinned
    by the two restriction specs (the leaves) — consumers never see the cover choice.
    [3] Composition-check: `homOfLE ≫ ι` plumbing elaborates (skeleton compiles).
    Verdict: SURVIVED.

- **L-0d** (leaf): `mulModelHom_π`. Skeleton: `GroupLawConstruction.lean:154`.
  - Source: per-piece structure maps (coefficients in `R`) + cover ext.
  - Attacks: [1] per-piece + `hom_ext` ✓; [2] fst-vs-snd: either works; fst matches
    `pullback.condition` downstream; [3] discharge shape ≤ 3 pieces. SURVIVED.

- **L-0c6** (leaf, THE spec): `mulModelHom_specPoints`.
  - Skeleton: `GroupLawConstruction.lean:167`.
  - Source (verbatim, B–L §2 defn of addition law, bl.txt:133–146 area): the triples
    compute "the sum … in the abelian group E(K)"; mathlib side `Affine.Point.add`
    (`slope`/`addX`/`addY`).
  - Lean ↔ source: a pair of `Spec K`-points is lifted to the product, pushed through the
    glued morphism, compared through the FIXED dictionary with mathlib's `+`.
  - Attacks attempted:
    - [1] The prior-B2 trap (bare-cardinality equiv): the spec pins the actual map through
      the canonical `projModelPointsEquiv` — not an `∃`-equiv. Addressed by design.
    - [2] Edge cases: `P = Q`, `Q = −P`, `P = O` — glued morphism total; `Point.add`
      handles each; the legitimate case analysis happens HERE over a field (decidable),
      never in the scheme construction. (Elaboration surfaced mathlib's `[DecidableEq K]`
      gate on `Point.add` — added as an instance-argument, the pattern mathlib review
      recommends; NOT a global classical instance.)
    - [3] Hypothesis: `IsElliptic` genuinely needed (dictionary + nonsingularity).
    - [4] Source-drift: "addition law" is *defined* by computing the sum on an open — the
      spec IS the definition; no drift.
    - Verdict: SURVIVED.

- **L-0cnat** (leaf): `mulModelHom_map`.
  - Skeleton: `GroupLawConstruction.lean:179`.
  - Source (verbatim, B–L p. 231): "It will be seen that the coefficients of the
    Weierstrass equation for E enter polynomially into all formulae in Section 5. This
    implies that the same formulae can be used to perform the addition on elliptic curves
    over com[m]utative rings."
  - Discharge: per-piece `Proj.map`-functoriality — the repo's `projModelBaseChange`
    machinery is this exact pattern (PROVEN, `WeierstrassModel.lean:1692`); glue-compat.
  - Attacks attempted: [1] do the OPENS base-change? Exceptional loci cut by the same
    polynomials ⟹ preimage-compat; inner lemma recorded. [2] square orientation — the
    skeleton's original square was TRANSPOSED; caught by elaboration against
    `projModelBaseChange_π`, fixed with `.symm` (the skeleton earning its keep). [3]
    discharge `pullback.map` + piece-functoriality ≤ 3. SURVIVED.

- **L-0g** (leaves: 3 defs + 3 `_left` pins + 5 axiom equations):
  `mulOver`/`oneOver`/`invOver` (+`_left` each), `mulOver_assoc`, `oneOver_mulOver`,
  `mulOver_oneOver`, `mulOver_comm`, `invOver_mulOver`.
  - Skeleton: `GroupLawConstruction.lean:200-253`.
  - Source: reviewer round-1 §3 step 2; mathlib `Affine.Point.instAddCommGroup`
    (`Affine/Point.lean:768`, verified — with its `add_assoc`/`add_comm`/units) over
    `K`-fields; transport by L-0cnat along `classifyRingHom` (audit A6).
  - Lean ↔ source: stated as the `MonObj`/`GrpObj` field shapes in `Over (Spec R)`
    (assembly definitional); `_left` pins connect to the scheme construction.
  - Attacks attempted:
    - [1] Transport composition: base-changing an Over-equation needs naturality for BOTH
      sides — μ has L-0cnat; unit/inv need small naturality lemmas — CAUGHT and recorded in
      the 0g sketch (one-liners from `projModelZero_baseChange` ⓟ + neg-functoriality).
    - [2] Braiding-form of commutativity checked against mathlib's `IsCommMonObj` field
      shape.
    - [3] Edge `R = 0`: `Spec 0 = ∅`, all equations trivial.
    - [4] Hidden hypothesis: field-points ext consumes universal-ATLAS reducedness only;
      general-`R` statements carry none (transport does the work).
    - Verdict: SURVIVED.

- **L-0e** (leaves ×4): `isReduced_of_smoothOfRelativeDimension` + instances for
  `weierstrassAtlas`, `universalCurve`, the double and triple products.
  - Skeleton: `PointsDictionary.lean:63,67,72,76,81`.
  - Source: reviewer round-1 §Q4 (reducedness half — audit A5's simplification of the
    integrality requirement).
  - Attacks attempted: [1] false without reduced base (`Spec k[ε]`) — instances stated for
    the universal (domain) atlas only ✓. [2] engine generality: stated with
    `SmoothOfRelativeDimension` (what the repo supplies) — over-generality attack
    withdrawn. [3] instance discharge: products via base-change/composition stability
    (mathlib `MorphismProperty`, used in `GroupLaw.baseChange` ⓟ). Verdict: SURVIVED;
    engine's mathlib-availability = AG-2 (conditional gap, fallback named).

- **L-0f** (leaves ×2): `projModelPointsEquiv` + `_zero`.
  - Skeleton: `PointsDictionary.lean:30,37`.
  - Source: **project, PROVEN** — `projModel_points` (`WeierstrassModel.lean:1105`, T-A2e);
    the leaves are its choice-extraction + pointedness pin.
  - Attacks attempted:
    - [1] Prior-B2 shape-match (Step 4.6): the `isWeierstrassModel_unique` B2 turned on a
      bare `∃`-equiv. Choice-extraction gives NO naturality in `K` — consumer sweep: every
      consumer uses the SAME fixed equiv on both sides of its equation;
      choice-consistency suffices. NO inherited defect; future naturality-needing work must
      re-audit (note left).
    - [2] Discharge verification: `projModel_points` confirmed sorry-free (green build).
    - [3] Edge: `K` a field forces `1 ≠ 0` compatible with `Δ` unit ✓.
    - Verdict: SURVIVED.

- **L-ext** (leaf): `hom_ext_of_forall_specPoint`.
  - Skeleton: `PointsDictionary.lean:51`.
  - Source: audit A5 (field-points extensionality subsumes the generic-point route — the
    generic point is one of the field points).
  - Attacks attempted:
    - [1] False without reducedness: `Spec k[ε]` ⇉ `𝔸¹` differing by `ε` — hypothesis
      present; used ONLY over the universal atlas (docstring warns).
    - [2] False without separatedness: line-with-doubled-origin — hypothesis present.
    - [3] Scope-creep to general `S` — descent leaves do not cite it (checked).
    - Verdict: SURVIVED. Discharge: equalizer-closed + surjective-closed-immersion-onto-
      reduced-is-iso — names VERIFIED at the pin (coordinator §3 record, 2026-07-07):
      `isClosedImmersion_equalizer_ι_left` (Morphisms/Separated.lean, in `Over S`) ·
      `isIso_of_isClosedImmersion_of_surjective` (`[IsReduced]`) ·
      `Scheme.fromSpecResidueField`. **Scope guard (coordinator §2/§3)**: L-ext proves
      equality of EXISTING morphisms; it is NOT a discharge for T-W7.0c's c5 (on-curve =
      ideal membership) — c5 goes through the Jacobson-density bridge c5α (board).

- **L-0h** (leaf ×1 + P3-file leaves ×4): `mulModelHom_vc`; `projModelVCIso` + `_π`,
  `_zero`, `_mul`.
  - Skeleton: `GroupLawConstruction.lean:265`; `ModelVariableChange.lean:34,39,45,52`.
  - Source: reviewer round-1 §Q5 caveat 2 (global equivariance incl. infinity/diagonal/
    anti-diagonal — verbatim in `reply.md`); affine cocycle ⓟ DONE; Silverman III.3.1(b).
  - Attacks attempted: [1] equivariance stated against the same `pullback.map` plumbing the
    descent uses — inline squares elaborate (build-verified). [2] `(C•W).IsElliptic` taken
    as instance-argument (Δ scales by `u⁻¹²` — instance derivable later; no block).
    [3] cocycle via `eqToHom (mul_smul …)` — elaborates; `▸`-transport rejected by design.
    Verdict: SURVIVED.

- **L-1b** (leaves ×2, the comparison theorem): `pointedIso_exists_variableChange`,
  `projModelVCIso_injective`.
  - Skeleton: `ModelVariableChange.lean:66,79`.
  - Source: audit A1 (the dependency both reviewer replies missed); KM §2.2/Deligne-
    formulaire-style statement, proof re-derived uniformly: b1 pointed iso preserves
    `E∖O` (= the `Z`-chart, complement of the section); b2 preserves `F_n` (intrinsic via
    the section's ideal sheaf); b3 freeness forces the coordinate shape and `α³ = γ²`,
    `u := γ/α`; b4 affine determines projective (L-i4); b5 faithfulness.
  - Prior-B2: this IS fix-option (3) of the `isWeierstrassModel_unique` B2 — implemented
    WITHOUT the BB-RR the log predicted (pole filtration instead). Addressed by
    construction.
  - Attacks attempted:
    - [1] Circularity (the audit-A1 attack re-run): 1b depends only on P3 leaves — the
      dependency graph is acyclic (checked).
    - [2] Automorphism trap: "the `C` with `C•W' = W` is unique" is FALSE for special `W`
      (extra automorphisms); uniqueness is pinned by the INDUCED ISO — the two-leaf split
      (existence-with-pin + faithfulness) encodes exactly this; a naive `∃!C, C•W' = W`
      leaf was rejected by this attack.
    - [3] Transport form: `eqToHom (congrArg …)`-free statement via `∃ hW, e.hom = eqToHom
      (by rw [← hW]) ≫ …` — elaborates (build-verified); shared-witness `∃∧` documented
      (statement-splitting exception: the witness `C` is shared).
    - Verdict: SURVIVED.

- **L-P3** (leaves ×10, the filtration file): `coordX`/`coordY` (real defs),
  `poleOrderFiltration` + `_one`, `_two`, `_three`, `_mul_le`,
  `linearIndependent_one_coordX_coordY`, `projModel_globalSections_eq_baseRing`,
  `infChart_s_nonZeroDivisor`, `projModel_hom_ext_of_affine`,
  `locallyWeierstrass_pushforward_O_eq_O`.
  - Skeleton: `PoleFiltration.lean` (whole file).
  - Source: reviewer round-1 §Q2 (verbatim: prove `Γ(ProjModel(W), O) ≅ R` "directly, for
    every ring R and every elliptic Weierstrass equation W/R", universality "by applying
    the same theorem to `W.map (R → R')`, not by an abstract cohomology base-change
    theorem"); audit A3 (2-chart equalizer; normal form one-basis-element-per-pole-order;
    `x²y⁻¹` = the `H¹` witness in neither image; `A` free with `{xⁱ, xⁱy}` — mathlib
    `Affine.CoordinateRing` freeness; `B = R[t][s]/(monic-in-s)` free `{sᵉtᵏ}`;
    `s`-nonzerodivisor by McCoy).
  - Attacks attempted:
    - [1] Hypothesis-strength: `IsElliptic` NOWHERE needed in P3 — the chart rings are free
      with universal bases for arbitrary Weierstrass data; this attack CHANGED the plan
      (all P3 statements are Δ-free; simpler and stronger).
    - [2] Base-change trap (the reviewer's own catch, re-verified): equalizers/kernels
      don't commute with base change — the `Γ ≅ R` statement is per-ring; universality by
      instantiation only. The i5 sheaf statement quantifies over families, not base
      changes of a fixed proof.
    - [3] False-leaf check on `F₁ = R`: over a FIELD this is `l(O) = 1` (genus 1) — but the
      claim is Δ-free… for a SINGULAR cubic is there a pole-order-1 function? The normal
      form is pure monomial bookkeeping (never uses Δ); the "genus" reading is a red
      herring — the filtration is defined via the chart normal form, and `x²y⁻¹`'s
      exclusion is basis arithmetic. Statement survives as stated FOR THE FILTRATION AS
      DEFINED; the ticket notes the definitional pin (F via the section ideal on `D(u)`).
    - [4] `hom_ext_of_affine` false via nilpotents? — precisely the McCoy leaf's job; over
      any `R` the `s`-nonzerodivisor computation replaces density. (This is the i4 attack
      that killed naive `IsDominant` routes in the round-1 audit; re-run, still sound.)
    - [5] i5's `IsIso (π.app U)` for ALL opens vs affine-basis opens: sheaf-level iso is
      checkable on a basis (principal opens inside chart opens); the statement quantifies
      over all `U` — provable via basis + sheaf gluing; recorded.
    - Verdict: SURVIVED (with the Δ-free strengthening applied).

- **L-1a′/1a** (leaves ×3 + structure): `WeierstrassAtlasData` (real structure — compiles),
  `EllipticCurveGeom.atlas`, `classifyRingHom`, `universalWeierstrassLoc_map_classifyRingHom`.
  - Skeleton: `WeierstrassAtlasBundle.lean`.
  - Source: reviewer round-1 §Q5 caveat 3 (verbatim bundled-cover recommendation with the
    Lean-shaped sketch, `reply.md`/`reply2.md`); `IsLocalization.Away.lift` for the
    classifying map.
  - Attacks attempted: [1] bundle-vs-predicate drift: fields copied verbatim from
    `LocallyWeierstrass`'s ∃-body (side-by-side check against `Basic.lean:143-151` — the
    structure ELABORATES, proving the compat equations are well-typed). [2] universe: index
    by points of `S`, stays in `u`. [3] classify-spec: `map` acts on the five coefficients
    (`Xᵢ ↦ aᵢ`) — five coefficient equations, no Δ-inverse interference. SURVIVED.

- **L-desc** (leaves ×7 + 2 real): `negHom`(+π, zero), `mulHom`(+π), `grpObj`,
  `grpObj_isCommMonObj`, `grpObj_one_eq_zero`; REAL: `toEllipticCurve`,
  `toEllipticCurve_geom` (`rfl`, already compiled).
  - Skeleton: `GroupLawDescent.lean`.
  - Source: reviewer round-1 §3 step 3; glue over the atlas pullback cover; overlap = L-1b
    + L-0h.
  - Attacks attempted: [1] circularity re-check: acyclic (1b ← P3 only; 0h ← P1/P2 only).
    [2] assembly is `rfl` BY CONSTRUCTION — gate-grade evidence the record shape composes.
    [3] the pre-existing PARKED sorry (`Point.asSection_zsmul`) is downstream-only; nothing
    here consumes it. SURVIVED.

### R-A prior-B2 consultation (Step 4.6)

`b2_log.jsonl` (2 entries): entry 1 is pass-metadata (no lemma). Entry 2
(`isWeierstrassModel_unique`, 2026-07-07): name-match NONE among R-A leaves; shape-match
"points-equiv pins a model" → addressed at L-0f attack [1] and L-1b (which IS the b2's
fix-option (3), delivered BB-RR-free). CLEAN.

## Result R-B (T-W7b): canonicity, locally noetherian

### Plain-English proof (Step 1 prose; source: GIT pp. 115–117, read in full)

GIT Prop 6.1 (verbatim statement + 3-case proof in the quotes file, git.txt:4885–4932): with
`S` connected (chapter convention locally noetherian), `p : X → S` flat with
`H⁰(X_s) = κ(s)` — replaced here by universal `O`-connectedness, which is what case 1
actually consumes — and (case 2) a section plus `p` closed: if `f : X → Y` over `S`
collapses one fibre set-theoretically to a point, then `f = η∘p` for the section
`η = f∘e`. Case 1 (one-point base): `f = η∘p` topologically; the sheaf map
`o_Y → f_*o_X ≅ η_*(p_*o_X) ≅ η_*o_S` is "precisely the extra structure required" to make
`η` a scheme morphism. Case 2: `Z = (f, η∘p)⁻¹(Δ)` the largest closed subscheme of
agreement; case 1 over every Artinian subscheme `T ⊂ S` concentrated at `t` gives
`Z ⊇ p⁻¹(T)` scheme-theoretically; hence (Krull intersection in noetherian local rings +
coherence of `I_Z` + `p` closed) `Z ⊇ p⁻¹(U₀)`, `U₀ ∋ t` open; `U₁ = {t : p⁻¹(t) ⊆ Z} =
S ∖ p(X−Z)` is closed (`p` flat ⟹ open) and open, so connectedness gives `Z = X`. Case 3
(no section): fppf descent — never needed here (the zero section exists). Corollaries
(pp. 116–117): 6.2 (two morphisms into a group scheme agreeing on one fibre differ by
`(η∘p)·`; apply 6.1 to `f·g⁻¹`); 6.3 (`f(x,y) = g(x)·h(y)`, `Y` connected; apply 6.2 over
the base `Y`); 6.4 (pointed ⟹ homomorphism; apply 6.3 to `f∘μ`); 6.6 (**uniqueness of the
group structure with a given identity**; apply 6.4 to `1_X` with the two laws).

### Attack log (internal node R-B)

- [A] The round-2 audit attack re-run against the source: the neighbourhood factorization
  DOES globalize over nilpotents — by Artinian thickenings + Krull, NOT density (the gap in
  both reviewer replies; closed by transcription; audit A4 CLOSED).
- [B] Hypothesis honesty: locally-noetherian + connected genuinely used (Artinian
  subschemes; Krull; coherence; clopen). Componentwise reduction (loc-noeth ⟹ components
  clopen) recorded inside L-C3's sketch. The unrestricted `abelEnrichment_unique` remains
  gated on AG-1 (T-W7.8) — NOT a leaf of this pass.
- [C] Composition 6.4 → 6.6 for our record: the two structures share the zero section
  through `h`; C3's unit-compat hypothesis is supplied by `one_eq_zero` ×2 + `h`; 6.4's
  "any group scheme" instantiates at the second structure on the same object. Composes.

### Leaves

- **L-hyp** (def + leaf): `UniversallyOConnected` (real def) +
  `EllipticCurveGeom.universallyOConnected`. Skeleton: `Rigidity.lean:42,48`.
  - Source: GIT case 1 ("One checks that p_*(o_X) ≅ o_S", git.txt:4903); supplied by i5 +
    `LocallyWeierstrass.baseChange` ⓟ (PROVEN).
  - Attacks: [1] hypothesis-replacement drift: our hypothesis is STRONGER than GIT's
    fibrewise `H⁰` and is what case 1 consumes; free for our families; recorded honestly in
    the docstring. [2] quantifier shape covers the `Y`-side application (checked against
    L-R1's use). [3] discharge = i5 + ⓟ. SURVIVED.
- **L-R1** (leaf): `exists_unique_factor_of_isAffine`. Skeleton: `Rigidity.lean:58`.
  - Source: GIT case 1 ringed-space argument (verbatim quote).
  - Attacks: [1] false-leaf without hO (𝔸¹-counterexamples) — hypothesis load-bearing ✓.
    [2] `∃!` = shared-witness + uniqueness — documented exception (uniqueness consumed by
    glueing of local factors). [3] discharge: Γ-Spec adjunction + hO, ≤ 3 pieces. SURVIVED.
- **L-R1′** (leaf): `rigidity_of_subsingleton_base`. Skeleton: `Rigidity.lean:69`.
  - Source: GIT case 1 verbatim. Attacks: [1] one-point base via `∀ a b : S, a = b` — no
    extra sobriety assumptions (case 1 needs none). [2] the section hypothesis is in GIT's
    case-1 list ✓. [3] conclusion matches GIT's "there is a section η … such that f = η∘p"
    exactly (shared-witness `∃∧` documented). SURVIVED.
- **L-R2** (leaf): `rigidity` (GIT 6.1 case-2 form). Skeleton: `Rigidity.lean:85`.
  - Source: verbatim statement + proof (quotes file). Hypotheses map 1:1; separatedness of
    `q` is implicit in GIT (closed equalizer) — surfaced explicitly, honest strengthening
    of record.
  - Attacks: [1] the nilpotent-globalization attack: answered by the source's own
    mechanism — transcribed, not invented. [2] empty-fibre edge: irrelevant (section ⟹
    nonempty; proof needs nonemptiness nowhere else). [3] Krull-intersection mathlib name +
    [4] flat-⟹-open-map mathlib name: verify-at-impl (both classical; if either is absent
    it is a leaf-sized escalation, named in AG-2-style). SURVIVED with two named
    verify-at-impl discharges.
- **L-C3** (leaf): `isMonHom_of_one_comp_eq` (GIT 6.4; 6.2/6.3 internal).
  Skeleton: `Rigidity.lean:101`.
  - Source: Cor 6.2/6.3/6.4 verbatim. Internal chain recorded (6.2 via Hom-group `f·g⁻¹`;
    6.3 over base `Y`, `Y` connected — componentwise; sub-leaf: `E` connected when `S` is).
  - Attacks: [1] Over-language transcription type-checks (μ[A]/η[A]/GrpObj/IsSeparated —
    build-verified). [2] one-conclusion split (mul-compat only; unit-compat is the
    hypothesis; inv-compat formal) — documented. [3] connectedness placement settled by the
    source (along `Y`). SURVIVED.
- **L-C4** (leaf): `abelEnrichment_unique_of_isLocallyNoetherian`.
  Skeleton: `Rigidity.lean:114`.
  - Source (verbatim, GIT Cor 6.6 + proof): "X has only one structure of group scheme over
    S with the given identity e … Apply Corollary 6.4 to 1_X, with 2 different group laws
    considered on domain and image."
  - Attacks: [1] record-equality reduces to `grp`-field equality (rest Prop-valued) ✓.
    [2] the `h`-transport (cast along geometry-equality) is the only Lean-specific step —
    recorded. [3] prior-B2: no match. SURVIVED.

### R-B prior-B2 consultation

No name-match; no shape-match (the B2'd lemma is model-uniqueness-from-point-counts, not
group-law uniqueness). CLEAN.

## API gaps (each with sub-tree status)

- **AG-1 (= T-W7.8)**: arbitrary-`S` canonicity via EGA IV §8 spreading-out (Hom-descent
  along filtered colimits). NOT skeletonized — no source transcription of EGA IV 8.8.2 has
  been done and mathlib's approximation infra is in flux; skeletonizing it now would violate
  quote-or-delete. Status: OPEN, low priority; gates ONLY the unrestricted
  `abelEnrichment_unique` (which stays as the sorried statement of record); reviewer
  follow-up F1′ asks whether any downstream consumer needs it. FC Rem. 1.2(a) names the
  vehicle (quote in quotes file).
- **AG-2 (conditional)**: `isReduced_of_smoothOfRelativeDimension` if the mathlib search at
  implementation comes back empty — self-contained fallback via the repo's standard-smooth
  chart presentations (`locally_isStandardSmooth_…` ⓟ); escalate only on a confirmed gap.

## Confidence gate (Step 5)

1. Every leaf mathlib-discharged / project-discharged / explicit-gap: ✓ (two verify-at-impl
   discharge names inside L-R2, flagged; AG-1/AG-2 explicit).
2. Skeleton compiles: ✓ — `lake build` through `GroupLawDescent` (top of the chain):
   "Build completed successfully (2969 jobs)", sorries only.
3. Verbatim quote + Lean↔source match per leaf: ✓ (inline or via `tw7-source-quotes.md`).
4. Adversarial pass per leaf and internal node, ≥3 attacks, outcomes recorded: ✓ — and the
   pass CHANGED the plan in five places (L-0a witness ring; L-0b generality; L-0c3
   minor-identities; L-0cnat square orientation; L-0g unit/inv naturality; plus the
   `DecidableEq` surface at L-0c6). A pass that changes nothing wasn't adversarial.
5. Prior-B2 consulted: ✓ (one relevant entry; addressed at L-0f/L-1b; none unaddressed).
6. Tree mirrors the sources: ✓ — R-B mirrors GIT 6.1→6.2→6.3→6.4→6.6 verbatim; R-A mirrors
   the reviewer-reply spine with B–L (Thm 1/Thm 2/§5) as the construction source. LOC
   estimates only where source-anchored.
7. Single-conclusion leaves: ✓ (documented exceptions: two rigidity shared-witness
   `∃ sec, _ ∧ _`; one `∃!`; the comparison theorem's shared-witness `∃ C, ∃ hW, _`).

**REVIEW-PENDING:** none blocking T-W7a or T-W7b-loc-noeth (F1′/F2/F3 refine, don't gate).

---

## COORDINATOR-AUDIT ADDENDUM (2026-07-07T14:06Z, per the all-lanes directive)

- **L-ext discharge names, now execution-verified** (supersedes the "verify-at-impl" notes):
  `isClosedImmersion_equalizer_ι_left` (Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:273),
  `isIso_of_isClosedImmersion_of_surjective` (with `[IsReduced]` — hence L-ext is REDUCED-ONLY),
  `Scheme.fromSpecResidueField`. **L-ext must NOT be cited as the discharge for P1's c5**
  (coordinator §2-P1): an ext principle proves equality of existing morphisms; c5 must
  CONSTRUCT `addOnZ`/`addOnY` — the two new c5 leaves (factorization bridge;
  (2,2)-triple→morphism plumbing) are P1's to skeletonize.
- **L-R1′ NEAR-MISS (attack-log correction — the adversarial pass MISSED a dropped
  hypothesis).** The skeleton statement of `rigidity_of_subsingleton_base` as committed in
  `ba82784b` OMITTED GIT 6.1's constancy hypothesis ("If, for one point s ∈ S, f(X_s) is
  set-theoretically a single point") — over a one-point base the hypothesis is still needed:
  counterexample `f = 𝟙 (ℙ¹_k)` over `Spec k` (no factorization through a section). The
  original attack block claimed source-fidelity without re-checking the hypothesis list
  against the quote — a Step-4.5 attack-4 failure. Statement since corrected in-lane (P4).
  **Sweep order (open):** re-check every GIT-transcribed skeleton statement's hypothesis
  list verbatim against `tw7-source-quotes.md` (rigidity, C1–C4 forms) before proving into
  them; record per-leaf sweep outcomes here.
- **L-1b source status: DESIGN-DERIVED (downgraded from source-quoted).** 1b has no verbatim
  KM §2.2/Deligne-formulaire quote (KM is an image-only scan; the route was re-derived in
  audit A1). Per the directive it carries its own attack obligations: (1) the b2 bridge —
  the landed `poleOrderFiltration` is a MONOMIAL SPAN, which a ring iso does NOT preserve
  for free; the intrinsic (section-ideal) characterization is a REQUIRED new leaf gating all
  of 1b; (2) b3 is several hundred lines (unitness of α,γ; α³ = γ²; five coefficient
  equations), not bookkeeping; (3) skeleton decls for b1/b2-bridge/b3/b5 must exist before
  proving into 1b. Board updated accordingly (P3 lane).
- **L-0c1 discharge text STALE** (pre-dates the c5 reroute): the "repo Proj chart plumbing"
  one-liner is withdrawn; see the two new c5 leaves above (P1).
- **T-W7.8 relabel**: mathlib spreading-out EXISTS at the pin (`spread_out_of_isGermInjective`
  et al.) — AG-1 demoted from "genuine infra" to "thin wrapper; re-check at implementation".

### Attack-log addendum (lane P4 / fable-P4, 2026-07-07T14:25Z — coordinator §2)

- **L-R1′ NEAR-MISS (logged; new sweep rule)**: the committed skeleton statement of
  `rigidity_of_subsingleton_base` was FALSE — GIT case 1's collapse hypothesis ("`f(X_s)`
  is set-theoretically a single point") was dropped; counterexample `f = 𝟙 ℙ¹` over a
  field. Caught at implementation (103ae635); fixed by the STRONGER
  `rigidity_of_subsingleton_range` (any base, `Set.Subsingleton (Set.range f.base)`,
  separatedness dropped) + chart core `rigidity_of_range_le_affine` (3199e396). New rule:
  every GIT-transcribed leaf gets a hypothesis-by-hypothesis diff against its verbatim
  quote in `tw7-source-quotes.md` BEFORE proving.
- **Sweep of remaining GIT leaves (fable-P4, 2026-07-07T14:25Z)**: `rigidity` (r2) vs GIT
  Prop 6.1 — connected ✓ loc.noeth ✓ flat ✓ proper(-as-closed, case 2) ✓ section ✓
  separated target ✓ one collapsed fibre ✓; `UniversallyOConnected` replaces
  `H⁰(X_s) = κ(s)` (documented swap, audit A4). COMPLETE.
  `isMonHom_of_one_comp_eq` (C3) vs Cor 6.3/6.4: GIT's Cor 6.3 runs connectedness along
  the SECOND factor — needs `A` (not just `S`) connected componentwise: the sub-leaf
  **L-C2conn** ("`E` connected when `S` is": flat + proper + surjective + connected fibres
  + O-connected ⟹ connected total space; no single mathlib name) is REQUIRED and was
  unplanned — ticketed with the r2 4-leaf split. `abelEnrichment_unique_of_isLocallyNoetherian`
  (C4) vs Cor 6.6: packaging only; hypothesis-complete relative to C3. No other drops.
