# Ticket Board — ModularCurves (Phase 1–2)

*/develop 1g, 2026-07-05; **v2 after expert-review integration** (see `§Amendments v2`
at the end — new incidence/quotient/subgroup-scheme/groupoid streams, dependency
changes from the two-record design, route changes for the pairing and Y(ρ̄)).
Statements are canonical in the Lean skeleton (commit
`b758179b`, amended by the integration commit): every proof ticket is "discharge the `sorry` at the named declaration" —
the signature in the file is the contract (develop.md §2.5). No ticket may alter a
statement; a worker convinced a statement is wrong hard-stops with a B2 report
(`b2_log.jsonl`) and the board is replanned.*

**Standing rules for every ticket**
1. Before starting: complete the leaf's ≥3-attack adversarial block in
   `decomposition.md` (several are marked *partial*).
2. `sorry`s outside your target may be *used* (they are WIP markers), but the DATA-SORRY
   register in `plan.md` is frozen: no new data-sorries; consume registered data only
   through its specification theorems.
3. Done bar: `lake build` green; your declaration sorry-free; `#print axioms` on it
   shows only `propext`/`Classical.choice`/`Quot.sound` + `sorryAx` inherited from
   *registered* dependencies (list them in the closing note); **no `set_option
   maxHeartbeats` anywhere** (needing one ⟹ file a `/decompose-proof` ticket instead).
4. PENDING-SOURCE(KM) tickets (marked ⧗KM) may be *worked for statements and
   non-KM-sourced lemmas* but not closed until the full KM text lands and the verbatim
   quote-gate in `decomposition.md` is satisfied.
5. **Claim protocol (multi-worker, added 2026-07-06)** — several workers share this
   worktree/branch; the board is the lock. To claim a ticket: add a
   `- **Claimed**: <worker-handle>, <ISO-UTC>` line, set `Status: in_progress`, and
   **commit `tickets.md` alone, immediately** (`board(ModularCurves): claim <ID>
   (<worker>)`) *before* touching any `.lean` file. A ticket carrying another worker's
   live claim — and the declarations/files its work owns — is off-limits until its
   Status turns `done`/`blocked` (a finished claim line stays as the record; set
   `Status: done (<worker>, <start> → <end>)` in the same commit as the final proof).
   Shared-worktree hygiene — **index-free commits (rule tightened 2026-07-06 after
   two cross-lane sweeps)**: commit with an explicit pathspec,
   `git commit -m "…" -- <your files>`, and do NOT `git add` at all. A pathspec
   commit is built from HEAD + the working-tree state of exactly the named paths,
   so it ignores the shared index completely: a sibling's stray `git add -A` can
   never leak into your commit, and you can never sweep a sibling's in-flight
   edits. (`git add` + bare `git commit` is what caused the sweeps.) Commit before
   long builds; never `git stash` (shared); if `tickets.md` conflicts, re-apply
   your lines on top — never drop another worker's claim.

## Summary
- Work tickets: 24 · Cleanup tickets: 11 · Milestones: T-E2, T-E7, T-E9, T-F4
- Parallel capacity: **5 lanes** (A, B, C, D, E/F) after T-A5; within lanes see
  `Parallel` fields. Start-now set: **T-E1, T-E2, T-A2, T-B2, T-D3, T-F0** (6 workers).

## Streams
- **A** foundations (EllipticCurve/*) — blocks B, C, D at *proof* level only
  (statements are frozen; other lanes may start on their non-DS2-dependent parts).
- **B** torsion & μ_N (Torsion, MuN) — B2/B3 independent of A-proofs.
- **C** Weil pairing (WeilPairing/*) — construction ⧗KM; comparison ticket ready.
- **D** ★ Drinfeld structures (LevelStructure/*) — KM Ch. 1 fully sourced.
  **★ STREAM CLAIMED: beastmode-D (stream-D worker), 2026-07-06T09:25Z** — D-lane
  execution order in §Amendments v5 (end of file); individual tickets are still
  claimed one at a time per rule 5 at pickup (the stream star reserves the lane and
  records the plan, it does not lock every ticket).
- **E** moduli + representability (Moduli/*) — E1/E2 ring-level, independent of ALL
  scheme-level lanes.
- **F** Y(ρ,p) (ModularCurve/YRho) — F0 now; F1 after AG-GG scoping; F4 phase 3.

---

### [T-E1] Tate normal form (ring level) — PROVABLE NOW
- **Status**: done (beastmode, 2026-07-06T00:35Z → 2026-07-06T01:25Z) · **File**: Moduli/Representability.lean ·
  `exists_unique_variableChange_isTateNormal`
- **Depends on**: none · **Parallel**: yes · **Type**: theorem
- **Statement**: in skeleton (∃! `vc : VariableChange R`, `(vc • W).IsTateNormal ∧
  vc.r = x ∧ vc.t = y`, given `W.IsElliptic`, `Equation x y`, `NowhereOrderLEThree`).
- **Proof sketch** (Loeffler Prop 3.3.4, proof p. 14, in hand):
  1. Translate `(x,y) → (0,0)`: apply `vc₁ = ⟨1, x, 0, y⟩`; mathlib
     `VariableChange` action lemmas compute the new `a₆ = 0`-form.
  2. Not-2-torsion ⟹ `ψ₂(0,0) = 2y' + a₁x' + a₃ = a₃`-unit reasoning: tangent slope
     defined; shear `y ↦ y + rx` to make the tangent at origin the line `y = 0`
     (kills `a₄`).
  3. Not-3-torsion ⟹ origin not inflexion ⟹ `a₂` unit; scale `x ↦ u²x, y ↦ u³y` with
     `u = a₂/a₃`-normalisation to reach `a₂ = a₃`.
  4. Uniqueness: compare coefficients of the two Tate-normal forms under a general
     `VariableChange` fixing `(0,0)` (forces `u = 1, r = s = t = 0`).
  5. Unit-hypothesis bookkeeping: `IsUnit (ψ₂ψ₃-eval)` ⟹ each intermediate divisor is a
     unit (localisation-free — everything is literal ring algebra).
- **Mathlib needed**: `WeierstrassCurve.VariableChange` group action (`vc • W`),
  `WeierstrassCurve.Ψ` + `evalEval` (verify names via `lean_local_search` at start),
  `IsUnit.mul_iff`.
- **Sources**: [Loe] Prop 3.3.4 with proof; Silverman III.1 Table 1.2 (variable-change
  coefficient formulas).
- **Generality**: arbitrary `CommRing R` (Loeffler's proof is coefficient algebra +
  one sheaf-gluing step that is vacuous over a ring); no field/locality hypotheses.
- **Progress**:
  - 2026-07-06T00:40: Tier-1 vendor decision — mathlib PR #25218 (kckennylau, commit
    8b7741e0) has the existence half over CommRing; vendored to
    `ModularCurves/ForMathlib/TateNormalForm.lean` with provenance header (fixed for
    current mathlib: explicit `some x y h` constructor args, calc/`mul_inv_cancel`
    drift). VENDOR register updated below.
  - 2026-07-06T01:00: PROJECT ADDITIONS (upstream candidates, in the vendored file):
    `Ψ₃_eval_X` (bridge identity `Ψ₃(x) = (a₂+3x)pY² + pX·a₁·pY − pX²` on the curve,
    cofactor `b₂ + 12x` — sympy-derived, linear_combination one-liner),
    `twiceNeZero_of_isUnit`, `thriceNeZero_of_isUnit`, `toTateNF_unique` (uniqueness
    half — s from a₄'=0, u from a₂'=a₃', both by unit cancellation; a₆' not needed).
    Vendored file is fully sorry-free.
  - 2026-07-06T01:10: `exists_unique_variableChange_isTateNormal` proven (subsingleton
    split + IsUnit.mul_iff + Ψ_two/Ψ_three/evalEval_C + vendored toTateNF machinery).
    Axioms: propext/Classical.choice/Quot.sound only.
  - 2026-07-06T01:25: DONE — /cleanup single-decl ran (body 31 → 12 lines, all gates
    pass, statement byte-identical). Flags recorded: `[W.IsElliptic]` unused by proof
    (kept — source form, frozen statement); statement-line repacks blocked by freeze.
    Post-proof cleanup: ✓ ran (gates pass, simplify n/a in single-decl mode, no
    decompose flags).

### [T-E2] Universal Tate curve represents (ring level) — PROVABLE NOW · MILESTONE
- **Status**: done (beastmode, 2026-07-06T01:30Z → 2026-07-06T02:20Z) · **File**: Moduli/Representability.lean · `tateRing_homEquiv`
- **Depends on**: none (statement); the *display* with T-E1 · **Parallel**: yes ·
  **Type**: theorem
- **Statement**: in skeleton (`(tateRing →+* A) ≃ {c : A × A // IsUnit Δ(c)}`).
- **Proof sketch**: `MvPolynomial.eval₂Hom`-universal property gives
  `(MvPolynomial (Fin 2) ℤ →+* A) ≃ A²`; `IsLocalization.Away.lift` adds the
  `IsUnit (image Δ)` condition; assemble the equiv; naturality is definitional.
- **Mathlib needed**: `MvPolynomial.eval₂Hom`, `IsLocalization.Away.lift`,
  `IsLocalization.Away.AwayMap.lift_comp` (verify exact names).
- **Sources**: [Loe] Cor 3.3.5.
- **Generality**: all `CommRing A`, universe-polymorphic target.
- **Progress**:
  - 2026-07-06T02:00: proven — pinned-equiv form (decompose-pass DEF-18 statement):
    toFun = evaluation at generator images; invFun = `IsLocalization.Away.lift`;
    left_inv via `IsLocalization.ringHom_ext` + `Away.lift_comp` + the agreement
    helper `tateRing_eval₂Hom_comp` (MvPolynomial.ringHom_ext' + RingHom.ext_int);
    right_inv by simp. Pin `fun φ ↦ rfl`. Axioms: standard three.
  - 2026-07-06T02:20: DONE — /cleanup ran (helper 13→6 lines via ringHom_ext'
    one-liner; theorem body 23→9 via hΔ-inline (▸), show-removal, terminal-simp
    collapse, `Away.algebraMap_isUnit` API upgrade). All gates pass, statement
    byte-identical. MILESTONE: first representability result of the project —
    the ring-level universal Tate curve. Post-proof cleanup: ✓ ran (gates pass,
    no flags).

### [T-A2a] Quotient of a graded ring by a homogeneous ideal is graded (MATHLIB GAP)
- **Status**: done (beastmode, 2026-07-06T02:30Z → 2026-07-06T03:30Z; core + consumer API
  sorry-free — `quotientGrading`, `GradedAlgebra` instance, `decompose_quotientGrading_mk`,
  `algebraMapGradeZero`; FiniteType transfer + degree-zero-iso deferred INTO T-A2's
  isProper step where their exact form is dictated; /cleanup deferred to parent T-A2
  Phase 6.5 — file still growing under the parent) ·
  **File**: ForMathlib/GradedQuotient.lean (new) · **Parent**: T-A2
- **Depends on**: none · **Parallel**: yes · **Type**: def + instance + lemmas
- **Statement**: for `𝒜 : ι → Submodule R A` a `GradedAlgebra` and `I : HomogeneousIdeal 𝒜`,
  the family `I.quotientGrading n := (𝒜 n).map (Ideal.Quotient.mkₐ R I.toIdeal)` is a
  `GradedRing` on `A ⧸ I.toIdeal`; plus the degree-zero comparison
  (`R →+* quotientGrading 0` iso under `I ⊓ 𝒜 0 = ⊥`-type hypothesis, in the form the
  Proj consumer needs) and `Algebra.FiniteType` transfer.
- **Proof sketch**:
  1. `SetLike.GradedMonoid`: `one_mem` = image of `1 ∈ 𝒜 0`; `mul_mem` by choosing
     preimages (`rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`, `SetLike.mul_mem_graded`).
  2. `decompose'`: descend `DirectSum.decompose 𝒜` through `Quotient.lift` — components
     map via `(mkₐ).toLinearMap.submoduleMap`; well-defined because `a − b ∈ I` ⟹
     `decompose (a−b) n ∈ I` (that is literally `Ideal.IsHomogeneous`).
  3. `left_inv`: naturality of `DirectSum.coeAddMonoidHom` under componentwise maps +
     `DirectSum.sum_support_decompose`.
  4. `right_inv`: check on `of`-singletons via `decompose_of_mem`.
  5. Degree zero: elements of `I.toIdeal` generated in degrees ≥ 1 have zero
     degree-0 component; specialise to the span-of-one-homogeneous-element case.
- **Mathlib lemmas**: `GradedRing` (extends `SetLike.GradedMonoid`,
  `DirectSum.Decomposition`), `Ideal.Quotient.mkₐ`, `LinearMap.submoduleMap`,
  `DirectSum.decompose`, `DirectSum.decompose_of_mem`, `DirectSum.sum_support_decompose`,
  `Ideal.IsHomogeneous` (defn: decompose-components stay in the ideal),
  `SetLike.mul_mem_graded`, `SetLike.one_mem_graded?` (verify), `DFinsupp.mapRange`.
- **Sources**: standard (Bourbaki Alg. II §11 / Stacks 00JW-adjacent); no KM content —
  pure infrastructure. ForMathlib: upstream candidate, register in VENDOR-adjacent list
  as OURS (not vendored — new).
- **Generality**: `ι` an `AddMonoid` with `DecidableEq`, `𝒜 : ι → Submodule R A`,
  `GradedAlgebra 𝒜` — matches mathlib's `GradedAlgebra` setup; do NOT over-generalise to
  `SetLike σ` in v1 (Submodule is what the consumer and mathlib's `homogeneousSubmodule`
  use).

### [T-A2d] lfp of the model via the ℙ² embedding (sub-ticket of T-A2)
- **Status**: done (beastmode, 2026-07-06T04:45Z → 2026-07-06T08:30Z — ALL five steps
  sorry-free: quotientGradingHom + irrelevant_le; Proj(A/I) ↪ Proj A closed immersion;
  chartRingEquiv (the ℙⁿ charts, incl. the monomial-clearing identity);
  ker_away_map_quotientGradingHom (chartwise-principal); finitePresentation_-
  awayQuotient + fp_algebraMap_gradeZero_away + the IsZariskiLocalAtSource mirror ⟹
  **projModelπ_lfp PROVED and plugged into projModel_isWeierstrassModel**, which now
  has isProper/lfp/section_comp REAL — only the T-A2e points clause remains sorried.
  /cleanup deferred to parent T-A2 Phase 6.5) · **Files**:
  ForMathlib/GradedQuotient.lean (graded mk-hom), ForMathlib/ProjClosedImmersion.lean
  (new), WeierstrassModel.lean · **Parent**: T-A2
- **Depends on**: T-A2a (done) · **Type**: def + theorems
- **Statement/route (of record)**:
  1. `HomogeneousIdeal.quotientGradingHom : 𝒜 →+*ᵍ quotientGrading I` (mk as graded hom;
     trivial fields via `mk_mem_quotientGrading`).
  2. `projModelToProjSpace W := Proj.map (quotientGradingHom …) : projModel W ⟶
     Proj (homogeneousSubmodule (Fin 3) R)` (mathlib `Proj.map`, Functor.lean:144).
  3. **General mathlib gap**: `Proj.map_isClosedImmersion_of_surjective` — Proj.map of a
     surjective graded hom is a closed immersion. Proof: closed immersions are local on
     the target (mathlib `IsClosedImmersion` + `IsZariskiLocalAtTarget`); over the
     `awayι`-cover of Proj 𝒜, the pullback is `Spec (Away.map g)` by
     `mapAffineOpenCover`/`awayι_comp_map` (Functor.lean:186/197), and `Away.map` of a
     surjective graded hom is surjective (NumDenSameDeg lift — same style as mathlib's
     `lift_awayMapₐ_awayMapₐ_surjective`, Proper.lean:37); surjective ring hom ⟺ Spec
     closed immersion (mathlib `Spec_iff`).
  4. lfp of `ℙ²_R → Spec R`: chart iso `(Away (homogeneousSubmodule σ R) (X i))₀ ≃+*
     MvPolynomial {j // j ≠ i} R` (dehomogenisation; mathlib gap, ForMathlib) — then
     `RingHom.FinitePresentation` chartwise + `HasRingHomProperty`.
  5. Ideal of the immersion is chartwise principal (`F/Xᵢ³`) → immersion lfp;
     compose for `projModelπ` lfp.
- **Sources**: EGA II 2.9 / Stacks 01M6-adjacent (standard); no KM gate.
- **Generality**: step 3 for arbitrary `[GradedRing]` over ℕ; step 4 for arbitrary σ
  finite; upstream candidates both.
- **Progress**:
  - 2026-07-06T05:30: steps 1–3 DONE, sorry-free: `quotientGradingHom` (+
    `decompose_quotientGrading_mk_apply`, `quotientGradingHom_irrelevant_le` — the
    `Proj.map` hypothesis) in GradedQuotient.lean;
    `away_map_quotientGradingHom_surjective` (4 lines via `Away.mk_surjective` +
    `Away.map_mk` — componentwise surjectivity is definitional for quotient gradings)
    and `isClosedImmersion_proj_map_quotientGradingHom` in ProjClosedImmersion.lean
    (IsZariskiLocalAtTarget over `iSup_basicOpen_eq_top` + conjugation
    `map ∣_ D₊(t) = isoQ.hom ≫ Spec.map (Away.map) ≫ iso𝒜.inv` from `awayι_comp_map`
    by mono-cancellation + `spec_of_surjective`; comp via
    `IsStableUnderComposition.comp_mem` — same transparency gotcha as before).
    NOTE for step 3-generality: proved for `Submodule R`-valued gradings (our
    GradedQuotient setting), ℕ-indexed — fine for all consumers here.

### [T-A2e] Elliptic points clause via the ℙ² embedding (sub-ticket of T-A2)
- **Status**: done (beastmode, 2026-07-06T09:00Z → 2026-07-06T15:30Z — `projModel_points`
  PROVED sorry-free, axioms standard. Ladder as built (all in WeierstrassModel.lean
  section Points): `specPoint_factors_through_chart` (K local + the D₊(mk Xᵢ) cover);
  `chartQuotientEquiv`/`chartCoordEquiv`(+`_mk`, `_mk_C`, `_mk_X`) — chart ring =
  R[u,v]/(dehomogenised cubic), forward-quotientEquiv orientation so the mk-computation
  is a rewrite chain; `chartSolutionsEquiv` (R-compatible chart homs = cubic solutions;
  factored ringHomPrecompEquiv ∘ quotient-level to avoid whnf blowups; engine =
  `MvPolynomial.aeval_unique` + `Ideal.Quotient.lift`); `awayι_projModelπ` +
  `chartPointOfHom`(+`_bijective` ⟹ `chartHomEquiv` via Equiv.ofBijective — surjectivity
  eliminates ∃ in Prop, no choose-gymnastics); `chartPointOfHom_factors_iff` (in chart j
  ⟺ j-th coordinate ≠ 0; `Proj.awayι_preimage_basicOpen` + `Away.isLocalizationElem` =
  Xⱼ/Xᵢ + primes of a field are ⊥ — instance-independent, the two Unique-instances on
  Spec K vs PrimeSpectrum K do NOT share defaults syntactically); chart evaluations
  `aeval_dehomog_{two,one,zero}` (X-chart has constant term −1 ⟹ always meets Z-chart);
  `infPoint` + `eq_infPoint_of_not_inZ` (Y-chart, U³=0 ⟹ U=0); assembly =
  `Equiv.sumCompl` over Z-chart membership + `zSolutionsToAffine` +
  `affinePointSplit` (`equation_iff_nonsingular`, base-change `IsElliptic` bridged
  through `W.map`); POINTEDNESS by post-composing `Equiv.swap (e₀ base) 0` — zero
  base-point chart computation needed. Gotchas of record: `projModel` made
  @[reducible] to dissolve Proj/projModel motive mismatches;
  `mk_X_mem_quotientGrading_one` restated at the `quotientGradingHom`-spelling;
  fin_cases leaves `(fun i ↦ i) ⟨1,⋯⟩` — use an equation-disjunction + rcases rfl.)
  · **File**: WeierstrassModel.lean · **Parent**: T-A2
- **Depends on**: T-A2d (chart iso + closed immersion) · **Type**: theorem
- **Statement**: the `points` field of `projModel_isWeierstrassModel`: for elliptic `W`
  and every `R`-algebra field `K`, pointed `SpecPoints (projModel W) (projModelπ W) K ≃
  (W.baseChange K).toAffine.Point` with `[0:1:0] ↦ 0`.
- **Proof sketch**: K-points of the closed subscheme = K-points of ℙ² on the cubic
  (closed-immersion mono + ideal-vanishing); each lands in an affine chart `D₊(Xᵢ)`
  (the awayι cover restricted to Spec K factors through one basic open, K local);
  chart-points = solutions of the dehomogenised cubic (T-A2d step 4 iso); nonsingularity
  for elliptic `W` over a field (mathlib `Affine.nonsingular` route) identifies with
  `Affine.Point` ∪ {∞}; the ∞-chart contributes exactly `[0:1:0]` (Z=0 ⟹ X³=0 ⟹ X=0 in a
  field ⟹ unique point in `D₊(Y)` with `x = z = 0`); pointedness by construction of
  `projModelZero`. Mathlib `Projective.Point.toAffineAddEquiv` as the final dictionary
  where convenient.
- **Sources**: KM 2.2/Loeffler §3.3 (display); Silverman III.3; standard.

### [T-A2] Construct the projective Weierstrass model (DS1)
- **Status**: done (beastmode, 2026-07-06T15:30Z — **`projModel_isWeierstrassModel`
  sorry-free**: isProper + lfp + section + elliptic pointed points-clause all PROVED
  (T-A2a/T-A2d/T-A2e sub-tickets done); axioms propext/Classical.choice/Quot.sound;
  no maxHeartbeats. /cleanup: inline pass only (privates marked, docstrings on new
  publics, staged-rewrite proofs); the FULL Mode-B /cleanup of the grown files
  (WeierstrassModel.lean ~1160 lines, ProjectiveSpaceChart.lean, GradedQuotient.lean,
  ProjClosedImmersion.lean) is handed to the cleanup lane on merge to main — file-size
  split candidate: section Points → EllipticCurve/ModelPoints.lean.) (previously:
  **DATA HALF DONE 2026-07-06T03:30Z — DS1 is no
  longer a data-sorry**: `projModel W := Proj (quotientGrading (projIdeal W))`,
  `projModelπ := toSpecZero ≫ Spec.map algebraMapGradeZero`, `projModelZero :=
  fromOfGlobalSections` at `[0:1:0]`, plus PROVED `projModelZero_projModelπ :
  zero ≫ π = 𝟙` and real lemmas `projective_polynomial_isHomogeneous`,
  `mk_Y_mem_irrelevant`, `projModelZeroEval_mk`. Remaining: the spec theorem
  `projModel_isWeierstrassModel` (isProper via `algebraMapGradeZero` bijectivity +
  mathlib's Proj-proper instance + FiniteType transfer; lfp; elliptic points clause)
  and T-A3 smoothness. Route notes: `set_option backward.isDefEq.respectTransparency
  false` needed around `fromOfGlobalSections_toSpecZero` consumers — same option
  mathlib itself uses there.)
- **Progress (2026-07-06T04:30)**: **isProper PROVED** (`projModelπ_isProper`
  instance): `algebraMapGradeZero` bijective (injective via the evaluation-at-[0:1:0]
  retraction — no graded analysis needed; surjective via `totalDegree_eq_zero_iff_eq_C`),
  `gradeZeroRingEquiv : R ≃+* (coordRing)₀`, `Spec.map` of it is an iso,
  `Algebra.FiniteType ((coordRing)₀) coordRing` by the scalar-tower transfer (new
  general `IsScalarTower R (quotientGrading I 0) (A⧸I)` instance in GradedQuotient),
  and mathlib's Proj-properness. Composite-instance gotcha: `IsProper (f ≫ g)`
  instance-key unification fails on the defeq-but-not-reducibly-equal middle object —
  closed with `MorphismProperty.IsStableUnderComposition.comp_mem _ _ h1 h2`.
  `projModel_isWeierstrassModel` now `refine ⟨inferInstance, ?lfp, PROVED-section, ?points⟩`.
  REMAINING (spawn on resume): [T-A2d] lfp and [T-A2e] elliptic points-clause — common
  engine = the chart computation `(HomogeneousLocalization.Away (quotientGrading
  (projIdeal W)) (mk Xᵢ))₀ ≅ R[u,v]/(F̃ᵢ)` (dehomogenised Weierstrass equations; also
  the input for T-A3's chartwise Jacobian). · **File**: EllipticCurve/WeierstrassModel.lean · `projModel`,
  `projModelπ`, `projModelZero`, `projModel_isWeierstrassModel`
- **Depends on**: T-A2a · **Parallel**: yes · **Type**: def + theorem
- **Statement/spec**: replace the DS1 sorries; prove `IsWeierstrassModel` for the
  construction.
- **Proof sketch**: two affine charts `Spec R[x,y]/(W_aff)` and `Spec R[t,s]/(W_∞)`
  (`t = −x/y`, `s = −1/y`), glued along `y`-inverted/`s`-inverted localisations via
  `Scheme.GlueData`; the section at infinity lands in chart 2 at `(t,s) = (0,0)`;
  point-bijection over fields: affine chart points ∪ {∞} ⟷ mathlib `Affine.Point`
  (`Point.zero ↔ ∞`, `Point.some ↔` chart-1 solutions).
- **Mathlib needed**: `Scheme.GlueData` (or two-open `Scheme.OpenCover` glue),
  `AlgebraicGeometry.Spec`, `IsLocalization.Away`.
- **Sources**: [KM] 2.2 (⧗KM for the quote); [Loe] Def 3.3.3; [Sil] III.3.
- **Generality**: any `CommRing R`; no ellipticity needed for the model itself.

### [T-A3a] Weierstrass Jacobian comaximality, certificate-free (sub-ticket of T-A3)
- **Status**: done (beastmode 2026-07-06T17:30Z — `span_dehomog_jacobian_eq_top` +
  `aeval_pderiv_dehomog_two_{u,v}` sorry-free in section Points; the maximal-ideal/
  residue-field argument as sketched; engine reuse: `ringHom_eq_aeval` identifies
  `Ideal.Quotient.mk m` with an `aeval` under the `toAlgebra`-structure, so the chart
  evaluation lemmas apply verbatim; numerals need `map_ofNat`/`map_natCast` in the
  aeval-simp set.) · **File**: WeierstrassModel.lean (section Points)
- **Parent**: T-A3 · **Depends on**: T-A2 (done) · **Type**: theorem
- **Statement**: for `W : WeierstrassCurve R` `[W.IsElliptic]`, in `MvPolynomial (Fin 2) R`
  (or the two-variable polynomial ring of the Z-chart),
  `Ideal.span {F̃, ∂F̃/∂u, ∂F̃/∂v} = ⊤` where `F̃` is the dehomogenised (affine) Weierstrass
  cubic. Same statement per chart for the Y-chart form (for the ∞-point assembly, where
  the ∂-with-respect-to-Z partial is `1 + O(u,z)`).
- **Proof sketch (CERTIFICATE-FREE — no explicit Bezout coefficients)**: suppose the span
  is proper; `Ideal.exists_le_maximal` gives a maximal `m` above it; `L := R[u,v]/m` is a
  field, `(x, y) :=` images of `(u, v)`. Push `W` to `L` along the composite
  `R → R[u,v] → L`: the point satisfies `Equation x y` (image of `F̃` is `0`) and both
  partial-evaluations vanish (images of `∂F̃`), i.e. `¬ Nonsingular x y` via
  `Affine.nonsingular_iff` + `evalEval_polynomialX/Y` (match our `∂`-forms against
  mathlib's `polynomialX/Y` by `ring`-normalisation). But `Δ` maps to a unit
  (`IsUnit.map`), so `(W.map …).IsElliptic` + `Nontrivial L` give
  `equation_iff_nonsingular.mp`: CONTRADICTION. This is the fibrewise-criterion
  reduction of KM 2.2.4 with mathlib's pointwise theorem as the field-level engine.
- **Sources**: KM 2.2.4 (smoothness over Δ-inverted base); GME §2.2.5 pp. 114–115
  (chartwise Jacobian display, incl. the ∞-chart computation); Loeffler §3.4;
  mathlib `equation_iff_nonsingular_of_Δ_ne_zero` (Affine/Basic.lean:243) as the
  pointwise input. MvPolynomial partials: `MvPolynomial.pderiv`.
- **Generality**: any CommRing R, `[W.IsElliptic]`. Upstream candidate.

### [T-A3b] Standard-smooth presentations of localized hypersurfaces (sub-ticket of T-A3)
- **Status**: done (beastmode 2026-07-06T19:30Z — ForMathlib/StandardSmoothHypersurface.lean
  sorry-free: `PreSubmersivePresentation.naive` over vars `Option σ`, relations
  `(rename some f, X none·rename some ∂f − 1)`, section `(some i, none)`; Jacobian
  `(∂f)²` unit by the w-relation; `hypersurfaceAwayEquiv` to `(R[X]/f)_∂f` by
  aeval-universal-properties (algHom_ext + DFunLike.congr_fun of aeval_unique — NOT
  congrArg-gymnastics; `Ideal.Quotient.liftₐ` needs pointwise kill: route through
  `RingHom.ker` + `Ideal.span_le`); `of_algEquiv` transfer; note mathlib's
  `of_algEquiv` takes `n` EXPLICIT and the standard-smooth hypothesis as an
  instance.) · **File**: ForMathlib/StandardSmoothHypersurface.lean
- **Parent**: T-A3 · **Depends on**: none (pure commutative algebra) · **Type**: def+thm
- **Statement**: for `f : MvPolynomial (Fin 2) R` and a variable `i : Fin 2`, the
  localization `(MvPolynomial (Fin 2) R ⧸ Ideal.span {f})_{∂f/∂xᵢ}` is
  `Algebra.IsStandardSmoothOfRelativeDimension 1` over `R`.
- **Proof sketch**: exhibit an `Algebra.SubmersivePresentation`: three generators
  `u, v, w`, two relations `(f, w·∂f/∂xᵢ − 1)`; the section selects `(xᵢ, w)`; the
  Jacobian determinant is `(∂f/∂xᵢ)²`, a unit in the localization. Survey mathlib's
  `RingTheory/Smooth/StandardSmooth.lean` + `RingTheory/Presentation.lean` +
  `RingTheory/Extension/Presentation/*` for existing constructors
  (`Presentation.localizationAway`, quotient presentations, `SubmersivePresentation`
  builders) before hand-rolling; the composition/localization transfer lemmas
  (`isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway`,
  `_localizationPreserves`) are already in mathlib (used by the scheme-level
  `HasRingHomProperty` instance).
- **Sources**: standard (Stacks 00T7 standard-smooth examples); no KM gate.
- **Generality**: arbitrary base `R`, arbitrary finite variable count σ with a chosen
  variable — state for `Fin 2` in v1 if the general form fights the presentation API.
  Upstream candidate.

### [T-A3c] Chartwise assembly of projModel smoothness (sub-ticket of T-A3)
- **Status**: done (beastmode 2026-07-06T21:30Z — `projModel_smooth` PROVED sorry-free,
  standard axioms; X/Y-chart Jacobian-⊤ via the elementary dichotomies below, all
  field_simp+linear_combination, with the ∂s-identity t-cancelled BEFORE field_simp;
  `locally_isStandardSmooth_algebraMap_gradeZero_away` + primed 𝒜₀-wrapper via
  RespectsIso.2 — Spec_iff endpoint is the bare algebraMap 𝒜₀→chart, matching
  fp_algebraMap_gradeZero_away, NOT the e₀-composite; toSpecZero instance mirrors
  lfp verbatim at P := @SmoothOfRelativeDimension 1; composite via (n+m) at 1+0.
  Gotchas: RingHom.Locally is universe-uniform Type u; pin hstep's mk-ideal
  (IsTwoSided-stuck); lives in section Points. ORIGINAL SCOPE NOTE: T-A3a proved the
  Z-chart Jacobian-⊤ only; the assembly needs all three charts. Elementary per-chart
  route fixed (NO homogeneous-Euler machinery): for the Y-chart, a singular point
  `(u,w)` has `w = 0 ⟹ u³ = 0 ∧ ∂W = 1 + a₁u − a₂u² = 0 ⟹ u = 0 ⟹ 1 = 0 ⊥`, and for
  `w ≠ 0` the affine point `(u/w, 1/w)` is singular via the scaling identities
  `w³·E = F_Y`, `w²·E_x = ∂U`, `w²·E_y = 3F_Y − U∂U − W∂W` (each a linear_combination);
  X-chart: `t = 0` contradicts `F_X = −1 + O(t)` immediately; `t ≠ 0` uses
  `t³·E = F_X`, `t²·E_x = 3F_X − s∂s − t∂t`, `t²·E_y = ∂s` at `(1/t, s/t)`. Common
  core: not_affine_singular from equation_iff_nonsingular + nonsingular_iff'.)
  · **File**: WeierstrassModel.lean
- **Parent**: T-A3 · **Depends on**: T-A3a, T-A3b · **Type**: theorem (discharges T-A3)
- **Statement**: `projModel_smooth : SmoothOfRelativeDimension 1 (projModelπ W)` for
  `[W.IsElliptic]`.
- **Proof sketch**: mirror `projModelπ_lfp` EXACTLY: mathlib instance
  `HasRingHomProperty (@SmoothOfRelativeDimension n) (Locally
  (IsStandardSmoothOfRelativeDimension n))` (Morphisms/Smooth.lean:154);
  `IsZariskiLocalAtSource.iff_of_iSup_eq_top` over the three `D₊(mk Xᵢ)`;
  `cancel_left_of_respectsIso (basicOpenIsoSpec …).inv` + `Proj.awayι_toSpecZero` +
  `HasRingHomProperty.Spec_iff` reduce to: `Locally (IsStandardSmoothOfRelativeDimension
  1)` for `R → (chart ring)`. Transfer along `chartCoordEquiv` (T-A2e machinery;
  `algebraMap_gradeZero_comp_eq` aligns the two R-structurings; `Locally` respects
  isos). Then `RingHom.Locally`-intro with the two-element cover `{∂F̃/∂u, ∂F̃/∂v}`
  (comaximal in the chart by T-A3a; check `RingHom.Locally`'s exact membership form —
  span-⊤ of the chosen units-set) and T-A3b on each piece. The `Spec.map
  gradeZeroRingEquiv`-iso part contributes `SmoothOfRelativeDimension 0`
  ([IsOpenImmersion] priority-900 instance); compose with the `n + m`-instance and
  close with `show SmoothOfRelativeDimension (1 + 0) _` or comp_mem, as in the
  IsProper composite (transparency gotcha noted in T-A2 progress).
- **Sources**: GME pp. 114–115; KM 2.2.4; assembly = this project's lfp proof of record.

### [T-A3] Model smooth ⟺ Δ unit
- **Status**: done (beastmode 2026-07-06T21:30Z — sub-tickets T-A3a/b/c all done;
  `projModel_smooth` sorry-free, standard axioms) · **File**: WeierstrassModel.lean
  · `projModel_smooth` · **Depends on**: T-A2 (done) · **Parallel**: with T-A4 · **Type**: thm
- **Sketch**: Jacobian criterion chartwise; mathlib `IsStandardSmooth` presentation of
  the chart rings; Δ-unit ⟺ fibrewise nonsingular (mathlib `IsElliptic` ↔ `Δ` unit ✓).
- **Sources**: [Loe] 3.3.3; [Sil] III.1.4(a). **Generality**: `CommRing R`.

### [T-A4] ⧗KM Uniqueness of the model (BB-RR consumer)
- **Status**: blocked-B2 (beastmode 2026-07-07T19:30Z — **STATEMENT FALSE as written;
  owner decision needed**; full record in `.mathlib-quality/b2_log.jsonl`. Quote-gate
  satisfied: KM 2.2.5 full text mined from the full PDF (printed pp. 68–69) — it is
  uniqueness of adapted coordinates x,y for a FIXED (E/S, ω) up to x↦x+a, y↦y+ax+b,
  NOT reconstruction of the scheme from field-point cardinalities. Counterexample to
  our statement: R = ℚ, E/E' a positive-rank 2-isogenous non-isomorphic pair
  (y²=x³−36x vs y²=x³+144x): isogeny+dual force |E(K)| = |E'(K)| (equal infinite
  cardinals) for EVERY char-0 field K, so projModel E' satisfies
  IsWeierstrassModel (E-data) + smoothness, but the concluded pointed iso would give
  E ≅ E'. NOTE the ∀K-quantifier DOES rule out cruder attacks (ℙ¹ dies at
  K = ℚ(uncountably many generic points): constants-field argument keeps |ℙ¹(K)|
  uncountable while |E(K)| = |E(ℚ)|; non-isogenous curves die the same way via
  Hom_ℚ(A,B) = 0) — the interface pins the ISOGENY class, not the curve. Fix options
  (owner picks): (1) make the points-clause NATURAL in K; (2) define the model
  property as ∃ pointed iso to projModel W; (3) restate per KM: two Weierstrass data
  with pointed-isomorphic smooth projModels differ by a VariableChange (BB-RR
  consumer form).) · **File**: WeierstrassModel.lean · `isWeierstrassModel_unique`
- **Depends on**: T-A2 · **Parallel**: with T-A3 · **Type**: theorem
- **Sketch**: KM 2.2.5-route: both models are pointed smooth proper genus-1; RR
  black-box gives Weierstrass coordinates; two Weierstrass presentations differ by a
  `VariableChange`; transport. Quote-gate: KM 2.2.5 (full text needed); interim source
  Hida GME §2.2 (mine quote when cut).
- **Sources**: [KM] 2.2.5 ⧗ · [Hida-GME]. **Generality**: `CommRing R`.

### [T-A5] Base change of elliptic curves (Prop fields)
- **Status**: done (beastmode 2026-07-06T22:30Z → 2026-07-07T18:30Z — ALL three Prop
  fields discharged: smooth+proper via MorphismProperty.pullback_snd
  (SmoothOfRelativeDimension stability instance needs explicit summoning);
  `fibres := E.fibres.baseChange g` via the new `FibrewiseElliptic.baseChange`
  (Basic.lean) assembled from T-A5a + T-A5b. Axioms standard.) · **File**: EllipticCurve/Basic.lean · `EllipticCurve.baseChange`
  · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Sketch**: `SmoothOfRelativeDimension`/`IsProper` base-change instances (mathlib,
  verify instance names); fibre condition: fibre of pullback ≅ fibre of original over
  the image point base-changed to the bigger residue field — use
  `Scheme.Hom.fiber`-pullback lemma (`Fiber.lean`'s `IsPullback` API) + transport of
  `IsWeierstrassModel` along residue-field extension (small lemma: `W.baseChange`
  compat of the points-interface).
- **Sources**: [Loe] §3.7 (Ell is fibered); [KM] 2.1 ⧗ (reconciliation only).
- **Generality**: arbitrary `g : T ⟶ S`.

### [T-A5a] projModel commutes with base change (sub-ticket of T-A5)
- **Status**: done (beastmode 2026-07-07T04:00Z — ALL rungs including the IsIso
  (T-A5a-iso) complete; `projModelBaseChange`, the π-square, `projModelBaseChangeLift`
  and its IsIso all sorry-free. Remaining consumer packaging (pointed iso for A5b)
  lives in T-A5b.) (rungs 1–7a record:
  `mvMapGraded`, `projIdeal_le_comap` (mathlib `Projective.map_polynomial`),
  `baseChangeGradedHom` (via new general `quotientGradingMap` in GradedQuotient.lean),
  `baseChangeGradedHom_irrelevant_le` (X-generators; Proj.map's HomogeneousIdeal-≤
  form is rfl-defeq to the toIdeal form — pass directly), `projModelBaseChange :=
  Proj.map …`, **`projModelBaseChange_π` (the base-change square) PROVED** via
  `mapAffineOpenCover.openCover.hom_ext` + `awayι_comp_map` + `awayι_toSpecZero` +
  `bc_ring_square` (grade-zero val-chase; `simp only [Category.assoc]` after unfold,
  rewrite side-goal `hs` discharged by `s.2.2`), and `projModelBaseChangeLift :=
  pullback.lift`. REMAINING rung 7b: `IsIso (projModelBaseChangeLift f W)` —
  IsZariskiLocalAtTarget over preimages of the `D₊(mk Xᵢ)` cover; per chart the lift
  restricts to Spec of the comparison `chart-W ⊗_R R' → chart-(W.map f)`, iso by
  `pullbackSpecIso` + `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` +
  `MvPolynomial.algebraTensorAlgEquiv` + `chartCoordEquiv` both sides
  (generator chase on X-vars and scalars); then package the pointed iso
  (zero-section compat via projModelZero_projModelπ-style rfl-chase or the
  Equiv.swap-free direct route) for T-A5b. · **File**: EllipticCurve/WeierstrassModel.lean (section Points or new)
- **Parent**: T-A5 · **Depends on**: T-A2 (done) · **Type**: def + theorem
- **Statement**: for `f : R →+* R'` (consumer case: residue-field extension
  `κ(s) → κ(t)`), a pointed iso over `Spec R'`:
  `pullback (projModelπ W) (Spec.map f) ≅ projModel (W.map f)` commuting with the
  π's and carrying the base-changed zero to `projModelZero (W.map f)`.
- **Proof sketch**: both sides are the Proj of the base-changed homogeneous coordinate
  ring. Route A (chartwise, all machinery in-repo): both schemes carry the 3-chart
  affine cover by `D₊(Xᵢ)`; pullback-of-chart = Spec of `chart ⊗_R R'` =
  `R'[u,v]/(F̃ᵢ-mapped)` (tensor-quotient + MvPolynomial base change:
  `MvPolynomial.algebraTensorAlgEquiv`-family + `Ideal.map`-quotient tensor iso —
  mathlib has `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`); glue chart isos
  via the `Proj.awayι`-cover pasting (`IsOpenImmersion` + `openCoverOfSuprEqTop`
  gluing, or `Scheme.OpenCover.glueMorphisms`); pointedness on the Y-chart.
  Route B (global): `Proj.map` of the base-change graded hom
  `quotientGrading (projIdeal W) →+*ᵍ quotientGrading (projIdeal (W.map f))` into the
  pullback via universal property; isomorphism checked chartwise (same charts). Note
  `WeierstrassCurve.Projective.polynomial` commutes with `MvPolynomial.map f`
  (coefficient-wise, `map_polynomial`-style simp) — needed to identify the mapped
  ideal with `projIdeal (W.map f)`.
- **Sources**: EGA II 3.5.3 (Proj and base change, standard); no KM gate.
- **Generality**: any ring hom `f`; upstream candidate (Proj-base-change for
  quotient gradings).

### [T-A5a-iso] IsIso of the base-change comparison (sub-sub-ticket of T-A5a)
- **Status**: done (beastmode 2026-07-07T04:00Z — `projModelBaseChangeLift_isIso`
  PROVED sorry-free, standard axioms, no maxHeartbeats. Final architecture:
  ForMathlib/AwayCongr.lean (awayCongr subst-transport + mk/map/trans/self +
  awayMap_map + awayMap_square — the wall-killer; ℬ' needs its own scalar ring);
  homogenizeAt_map (ProjectiveSpaceChart, induction form; UNtargeted map_X rw
  grabs the ambient occurrence in transport-proof types — instantiate);
  gradedSquare; bc_chart_value + piece_fst_natural (SPLIT value/wrapper — the
  single-declaration heartbeat budget was the binding constraint; pin ALL six
  graded homs + t + both index proofs in the awayMap_square application);
  thetaIso (coordW'symm-Spec ≪≫ awayCongr-toCommRingCatIso, eqToHom-free);
  awayι_awayCongr + theta_awayι_π; coverPiece_f_eq + isPullback_coverPiece
  (pullbackRightPullbackFstIso transport); isPullback_lift_piece via
  of_right + flip (p-case: hom_ext with cover-square w + hbcfst/hfst and
  inv_snd_snd + theta_awayι_π; s-case: chart-square corner-transport along
  thetaIso.symm); final: pullbackHom = isoPullback.inv ≫ piece-iso.hom, iso as
  (symm ≪≫ ·).hom instance.) · **File**: EllipticCurve/WeierstrassModel.lean (section
  BaseChangeGraded/TensorComparison) · **Parent**: T-A5a
- **Depends on**: everything committed under T-A5a (all green): `projModelBaseChange`,
  `projModelBaseChange_π`, `projModelBaseChangeLift`, `sChartTensorEquiv`,
  `isPushout_sChart(_commRingCat)`, `isPullback_sChart_spec` · **Type**: theorem
- **Statement**: `IsIso (projModelBaseChangeLift (R' := R') W)` (with `[Algebra R R']`).
- **FINDING OF RECORD (2026-07-07, do not re-discover)**: the naive ring-level
  naturality `chartCoordEquiv (W.map alg) ∘ sChartBaseChange = Away.map bcHom ∘
  chartCoordEquiv W` is NOT STATABLE as-is: `Away.map (baseChangeGradedHom …) t_i`
  lands in `Away 𝒜' (bcHom t_i)` while the primed chart lives at
  `Away 𝒜' (t_i')`; the element equality `bcHom t_i = t_i'` (mk∘map_X chain) is
  propositional, not syntactic, so the two composites have different TYPES
  (dependent-index wall — same class as the mk-vs-quotientGradingHom respelling
  earlier, but now inside a statement, where `show`-casts don't help).
- **Proof plan (scheme-level, avoids the wall)**: prove `IsIso` locally on the target:
  isomorphisms are IsZariskiLocalAtTarget; cover `pullback (projModelπ W) (Spec.map
  (ofHom (algebraMap R R')))` by `Scheme.Pullback.openCoverOfLeft` applied to the
  three-chart cover of `projModel W`. Per chart `i`: (1) the cover component is
  `pullback (awayι-i ≫ projModelπ W) (Spec.map alg)` = (rw `awayι_projModelπ`)
  `pullback (Spec.map χ_R) (Spec.map alg)`, which `isPullback_sChart_spec` +
  `IsPullback.isoIsPullback` identifies with `Spec (SW'-quotient)`; (2) the
  lift-restriction over this component: compute `projModelBaseChangeLift`-pullback
  along the component map via `pullback.lift_fst/snd` + `Proj.awayι_comp_map` at
  s := t_i (this stays at the `bcHom t_i`-spelling; apply the ELEMENT equality
  `bcHom t_i = t_i'` only inside `Proj.basicOpen`/morphism-`=`-Props, where rw is
  legal); (3) conclude each restriction is the `Spec.map` of `sChartBaseChange`
  conjugated by isos ⟹ IsIso (isPullback comparison uniqueness:
  `IsPullback.hom_isIso?` or two-sided-inverse from the universal property).
  Alternative if the cover-plumbing fights: construct the INVERSE morphism
  `pullback ⟶ projModel (W.map alg)` directly by gluing the three
  `Spec (SW') = component`-isos over the W'-model's chart cover
  (`Scheme.OpenCover.glueMorphisms` on `mapAffineOpenCover`-restricted-to-X-gens),
  then check both composites = id by `hom_ext` over the same covers.
- **Sources**: EGA II 3.5.3; entirely infrastructure (no KM gate).
- **Progress (2026-07-06, beastmode)**: reduction skeleton GREEN in-file (sorry at the
  per-piece goal): iff_of_openCover at P := isomorphisms + openCoverOfLeft of
  modelChartCover (new def); component goal confirmed via LSP =
  `isomorphisms (Cover.pullbackHom 𝒰 lift i)` with `pullbackHom = pullback.snd lift
  (𝒰.f i)`; `algebraMap_chart_eq` extracted standalone; DecidableEq-bridge for the
  wrapped cover-index type (`inferInstanceAs (DecidableEq (Fin 3))`) + hcosp
  (cover-leg = χ-composite via awayι_projModelπ) both in place. TWO recorded traps:
  (1) NEW chart-terms written at the cover index elaborate at the wrapped
  `toPreZeroHypercover.1`-type (σ-argument of dehomogenizeAux!) and then mismatch the
  Fin-3-elaborated library lemmas — parameterize all piece-level lemmas by `j : Fin 3`
  as standalone defs/lemmas ABOVE the theorem and apply at `i` (defeq-application
  is fine; fresh elaboration is not); (2) leg-order of `isPullback_sChart_spec` is
  (R'-leg, SW-leg) vs the 𝒰-piece cospan (chart-leg, R'-leg): need
  `IsPullback.flip` + corner-transport `IsPullback.of_iso` along
  `Spec.map (ofHom (chartCoordEquiv W j).symm)` (SpecSW ≅ Spec-chart), with the
  leg-compat squares from `algebraMap_chart_eq`/`hcosp`; then the per-piece
  conclusion via `IsPullback.isoPullback` + `isoPullback_hom_snd`
  (`pullbackHom = iso.inv ≫ κ`, κ iso).
- **ENDGAME (2026-07-06, fully designed — execute mechanically)**: (b) via
  `IsPullback.of_right` on the FLIPPED target: bindings h₁₁ := κ :=
  `(isPullback_piece W j).isoPullback.hom`, v₁₁ := θ.hom ≫ awayι-W'-bcHom-form
  (REDEFINE the fst-leg this way), v₁₂ := 𝒰.f j, h₂₁ := lift; t := COVER-SQUARE
  `IsPullback pfst (𝒰.f j) (awayι-W-j) (pb.fst π alg)` — derive by transporting
  `of_hasPullback` along `pullbackRightPullbackFstIso π (Spec alg) awayι-j`
  (hom_fst/hom_snd @[simp]-lemmas at Pasting.lean:465-475) PLUS the identity mathlib
  itself proves inside `openCoverOfLeft.mem₀` (Pullbacks.lean:521, by aesop):
  `pullback.map (𝒰f i ≫ f) g f g (𝒰f i) 𝟙 𝟙 = (pullbackSymmetry _ _).hom ≫
  (pullbackLeftPullbackSndIso _ _ _).inv ≫ pullback.fst _ _ ≫ (pullbackSymmetry _ _).hom`
  (re-prove locally by aesop/hom_ext); s := big-rect
  `isPullback_projModelBaseChange_chart` (PROVED) corner-transported by of_iso along
  θ := asIso (Spec.map (ofHom (chartCoordEquiv (W.map alg) j).symm.toRingHom)) ≪≫
  eqToIso (congrArg (fun t => Spec (.of (Away (quotientGrading (projIdeal
  (W.map alg))) t))) (baseChangeGradedHom_mk_X …).symm); WALL-RECIPE: in each
  compat-Prop first `rw [← baseChangeGradedHom_mk_X]` normalizing t'ⱼ-spellings to
  bcHom-spelling, then `eqToHom_refl` collapses; use `isoPullback_hom_fst/snd` and
  `pullback.lift_fst/snd` to identify the composite legs. (c): `pullbackHom =
  (b).isoPullback.inv ≫ κ-arrangement` via `isoPullback_hom_snd`; IsIso from κ-iso;
  close `projModelBaseChangeLift_isIso`.
- **STATE 2026-07-06 (late)**: IN FILE, GREEN: `thetaIso` (with manual IsIso via
  two-sided CommRingCat inverse), `coverPiece_f_eq` (cover map =
  pullbackRightPullbackFstIso.inv ≫ snd, by hom_ext + condition + inv_fst/inv_snd_snd),
  `isPullback_coverPiece` (of_hasPullback transported by of_iso along the pasting iso;
  hom_fst.symm for commfst; hom≫inv-collapse for commsnd), `isPullback_lift_piece`
  wired by `(IsPullback.of_right ?s ?p (isPullback_coverPiece W j)).flip` — REMAINING
  SORRIES: `piece_fst_natural` (the wall-crossing ring naturality, statement GREEN) and
  the s/p cases (assemble from piece_fst_natural + a `hsnd`-analogue via
  awayι_projModelπ at W' + algebraMap_chart_eq-W' symm-cancel; s := big-rect
  `.of_iso` with θ.symm corner, then rw (pullback.lift_fst).symm to match of_right's
  bottom-composite).
- **WALL ANALYSIS v2 (binding for the continuation)**: do NOT try `rw [← elt-eq]` on
  goals where the element occurs inside TYPES of subterms (chartCoordEquiv W' j's
  type) — kabstract motive fails. Working options, in order of preference:
  (1) prove `piece_fst_natural` via `Spec.map_injective` + `CommRingCat.hom_ext` +
  elementwise generator chase on the QUOTIENT generators (mk-C and mk-X of SW'),
  using `eqToHom_map` (Functor.map of eqToHom) once to convert the Spec-level
  eqToHom into a CommRingCat-level eqToHom, and evaluating the CommRingCat-eqToHom
  elementwise by first proving a tiny helper `Away`-index-cast-val lemma stated
  GENERALIZED over the target element (`∀ t (h : bcElt = t), val (cast h x) = …`) so
  that `subst`/`cases h` becomes legal (the closed-closed Eq blocks subst; generalize
  the RHS first — standard technique); (2) alternatively define
  `awayIndexCongr (h : s = t) : Away 𝒜 s ≃+* Away 𝒜 t` by tactic-`subst` after
  generalizing, with `awayIndexCongr_mk` API, and phrase θ with it instead of
  eqToIso (all later compat-proofs then go through awayIndexCongr_mk instead of
  eqToHom juggling). Elementwise content of the naturality on generators: at mk-C r:
  both sides = fromZero/algebraMap-image of e₀'(f r) — this is `bc_ring_square`
  transported; at mk-X k: both sides are `Away.mk … 1 (mkW' (X k))`-normal forms —
  val_injective + `Away.map_mk` + `chartCoordEquiv_mk_X`-W'-side + pow_one/pow_zero
  witness congrArgs, exactly the `chartCoordEquiv_mk_X` proof pattern.


### [T-A5b] Fibres of a pullback along residue-field extension (sub-ticket of T-A5)
- **Status**: done (beastmode 2026-07-07T05:30Z → 2026-07-07T18:30Z — COMPLETE.
  Zero-leg: `projModelZero_preimage_yChart`, `projModelZeroChart`(+`_fac`),
  `projModelZeroChart_comp_χ`, `zeroChartHom`(+`_mk`), glue
  `spec_zeroChartHom_awayι` (stage 3 = `glue_pieceY`: toSpecΓ-insertion trick
  `Spec.map ζ = toSpecΓ ≫ Spec.map (ofHom ζ ≫ ΓSpecIso.inv)` + morphismRestrict_ι +
  basicOpenIsoSpecAway_hom_SpecMap + Iso.cancel_iso_hom_left + Spec.map-collapse +
  IsLocalization.ringHom_ext/map_comp/Away.lift_comp — both sides away-lifts of
  projModelZeroEval), `projModelZeroChart_eq_spec` (cancel_mono awayι),
  `projModelZeroEval_baseChangeGradedHom` (eval₂_comp_left),
  `projModelZero_baseChange` (elementwise Away.mk_surjective chase — NB mk_surjective
  takes 𝒜 EXPLICIT and x must be type-ascribed out of the CommRingCat carrier).
  Paste: `isPullback_projModelBaseChange` (of_iso_pullback from lift_isIso) +
  `FibrewiseElliptic.baseChange` (Basic.lean — mathlib fibre-pasting engine
  `isPullback_fiberToSpecResidueField_of_isPullback` transported by of_iso along e_s
  [pullback.map MUST be type-ascribed to fiber-typed homs — ≫-elaboration does not
  unfold Scheme.Hom.fiber]; u := hA.isoPullback ≪≫ hB.isoPullback.symm; zero-leg by
  cancel_mono hB.isoPullback.hom + hom_ext with sectionFiberPoint-naturality `hnat`
  consumed via reassoc_of% [naked rw ← Category.assoc breaks on lift-proof-args];
  snd-residues closed by explicit `exact Category.id_comp _`/`pullback.lift_snd`
  terms — simp chokes at instances-transparency after fiber-unfold]). Axioms
  standard.)
- **Zero-leg (c) STATE**: `projModelZero_baseChange` in-file, reduced (GREEN up to one
  sorry) to the affine CORE: `(projModelZeroChart (W.map alg) ≫
  Spec.map (awayCongr …).toCommRingCatIso.hom) ≫ Spec.map (ofHom (Away.map bcHom t₁))
  = Spec.map (ofHom alg) ≫ projModelZeroChart W` — morphisms of AFFINE schemes.
  CORE ROUTES (pick one): (α) Spec-full-faithfulness: both sides = Spec.map of ring
  homs (`Spec.map_preimage` on the zeroChart-lifts); the ring hom
  ζ_W := (Spec.preimage (projModelZeroChart W)).hom : chart-W-ring →+* R is
  characterised by: ζ∘χ_R = id (compose the fac with π and use
  projModelZero_projModelπ + awayι_projModelπ + Spec.map_injective) AND its values
  on the two chart coordinates U = X₀/X₁, W = X₂/X₁ are 0 — for THESE use the
  Γ-side: fromOfGlobalSections is glued from `toBasicOpenOfGlobalSections`
  (ProjectiveSpectrum/Basic.lean:445 area, `homOfLE_toBasicOpenOfGlobalSections_ι`)
  whose chart ring map is an `awayLift` of the defining Γ-hom — the coordinate
  values become (ΓSpecIso.inv ∘ projModelZeroEval)(X₀)/(X₁-image) = 0/1 = 0 ✓ and
  (X₂)/(X₁) = 0 ✓; then RingHom.ext on quotient generators (mk-C via ζ∘χ = id;
  mk-X-vars via the 0-values) on both sides of the core. (β) alternatively prove the
  ζ-values through the T-A2e points machinery: the SpecPoint ⟨Spec.map alg ≫
  projModelZero, …⟩ vs `infPoint`: show base-not-in-Z via projModelZero-preimage of
  D₊(t₂): compute `fromOfGlobalSections_preimage_basicOpen` at r := t₂: eval sends
  mk X₂ ↦ 0 ⟹ preimage = basicOpen 0 = ⊥ ⟹ base misses the Z-chart ⟹
  eq_infPoint_of_not_inZ gives base = infPoint (K := R'... careful: needs Field K —
  the points-route only works over fields; for general R' prefer (α)).
  RECOMMENDATION: (α).
- **(α) CONCRETE ζ-DESIGN (2026-07-07, execute next)**: define
  `zeroChartHom W : Away (quotientGrading (projIdeal W)) t₁ →+* R :=
  (Localization.awayLift (projModelZeroEval W) t₁-underlying (unit: evaluates to 1 via
  projModelZeroEval_mk + isUnit_one)).comp (HomogeneousLocalization.valRingHom _)`
  (valRingHom is in ProjectiveSpaceChart). Values: ζ(Away.mk hs n a ha) =
  evR(a)/1 = evR(a) — awayLift_mk-style + val_mk (mind the T-E-era gotcha: awayLift
  needs the unit-witness syntactically `isUnit_iff_exists_inv.mpr ⟨v, hv⟩` for
  awayLift_mk to fire; v := 1). Retraction-check: ζ ∘ χ_R = id from
  projModelZeroChart_comp_χ ∘r Spec-faithfulness OR directly elementwise.
  MAIN CLAIM: `projModelZeroChart W = Spec.map (ofHom (zeroChartHom W))` by
  `cancel_mono (awayι-Y)`: reduces to `Spec.map (ofHom ζ) ≫ awayι-Y =
  projModelZero W` — prove by the fromOfGlobalSections gluing equation at the
  ⊤-piece: `Scheme.Cover.ι_glueMorphisms` (the cover map of the t₁-piece of
  `openCoverOfMapIrrelevantEqTop` composed with fromOfGlobalSections equals
  `toBasicOpenOfGlobalSections … ≫ (basicOpen 𝒜 t₁).ι`), the ⊤-piece cover-map is
  an iso (basicOpen (f t₁) = ⊤ from the eval-1 computation — cancel it), and
  `toBasicOpenOfGlobalSections`'s ring content is
  `IsLocalization.map f : Localization.Away t₁ → Localization.Away (f t₁)`
  conjugated by `basicOpenIsoSpecAway` + `toSpecΓ`-restriction (def at
  Basic.lean:368) — compare with ζ via `IsLocalization.ringHom_ext (powers t₁)` +
  val-normal forms. Then the CORE closes by RingHom.ext on chart generators:
  mk-C-r via retraction; U/W-coords via ζ-values = eval(X₀)=0 / eval(X₂)=0, and the
  Away.map-side values via Away.map_mk. THEN paste-assembly (plan v2).
- **ζ-STATE (2026-07-07, late)**: `zeroChartHom` + `zeroChartHom_mk` +
  `projModelZeroChart_comp_χ` PROVED and committed. REMAINING GLUE STEP (the last
  hard piece of the zero-leg): `Spec.map (ofHom (zeroChartHom W)) ≫ awayι-Y =
  projModelZero W`. Recipe refined: the map `projModelZero` is
  `(openCoverOfMapIrrelevantEqTop …).glueMorphisms …` (its hf is an inline by-proof —
  do NOT try to name the cover in a statement; work proof-internally). Use
  `Scheme.Cover.ι_glueMorphisms` (Gluing.lean:462, @[simp]) after
  `unfold projModelZero Proj.fromOfGlobalSections` at the piece
  `x₀ := ⟨1, t₁, one_pos, mk_X_mem_quotientGrading_one W 1⟩`; the piece's cover map
  is `(Spec R |_ basicOpen (evΓ t₁)).ι` with `basicOpen (evΓ t₁) = ⊤` (evΓ t₁ = 1 —
  same computation as projModelZero_preimage_yChart); precompose both sides of the
  target with this ι (an iso onto ⊤ — cancel_epi; get the iso via `Scheme.isoOfEq`
  to ⊤ + `Scheme.topIso`), reducing to: ι-⊤ ≫ Spec-ζ ≫ (basicOpenIsoSpec).inv-free
  comparison with `toBasicOpenOfGlobalSections` (def at ProjectiveSpectrum/Basic.lean
  :368: its ring content is `IsLocalization.map f` conjugated by
  `basicOpenIsoSpecAway` and `toSpecΓ`-restriction; for X = Spec R use
  `toSpecΓ_SpecMap_ΓSpecIso_inv`-machinery already in this file). Final ring
  comparison by `IsLocalization.ringHom_ext (Submonoid.powers t₁)` — both sides are
  away-lifts of `projModelZeroEval`; note `awayι = basicOpenIsoSpec.inv ≫
  (Proj.basicOpen _ _).ι` is rfl (Basic.lean:191). After the glue step:
  `projModelZeroChart W = Spec.map (ofHom ζ)` by cancel_mono awayι + fac; then the
  affine CORE closes by RingHom.ext on chart generators (recipe above); then
  projModelZero_baseChange's sorry; then paste-assembly (plan v2).
 · **File**: EllipticCurve/GroupLaw.lean (or Basic)
- **Parent**: T-A5 · **Depends on**: T-A5a · **Type**: theorem (discharges `fibres`)
- **Statement**: `FibrewiseElliptic (pullback.snd E.π g) (baseChange-zero) _` for
  `E : EllipticCurve S`, `g : T ⟶ S`.
- **Proof sketch**: fix `t : T`, `s := g.base t`. Pasting: `(pullback.snd E.π g).fiber t
  = Spec κ(t) ×_T (E ×_S T) ≅ Spec κ(t) ×_S E` (pullback pasting, `IsPullback.paste`)
  `≅ Spec κ(t) ×_{Spec κ(s)} (Spec κ(s) ×_S E) = Spec κ(t) ×_{κ(s)} E.π.fiber s` (paste
  along `Scheme.residueFieldMap`/`fromSpecResidueField` triangle —
  `Scheme.Hom.residueFieldMap_fromSpecResidueField` comm square). Take `W` from
  `E.fibres s`, set `W' := W.map (residue-field map κ(s) → κ(t))`; compose the pasted
  iso with (fibre-iso from E.fibres) base-changed, then T-A5a's iso; π- and
  zero-compat by pasting functoriality. Watch: the zero-section transport needs
  `sectionFiberPoint` naturality under both pastes (two small commuting squares).
- **Sources**: [Loe] §3.7; standard fibre pasting.
- **PLAN v2 (2026-07-07, after mathlib survey)**: the pasting engine EXISTS:
  `AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`
  (Fiber.lean:65): at the defining square `of_hasPullback E.π g` and `y := t` it
  yields `IsPullback (pullback.map …) ((pullback.snd E.π g).fiberToSpecResidueField t)
  (E.π.fiberToSpecResidueField (g t)) (Spec.map (g.residueFieldMap t))` — the fibre of
  the base change at `t` is the pullback of the fibre at `s := g t` along
  `Spec κ(t) → Spec κ(s)`. Assembly: (i) from `E.fibres s` get `W`, `e_s : fiber s ≅
  projModel W` with π/zero legs; (ii) transport the pullback square along `e_s`
  (IsPullback.of_iso on the X-corner) to get `fiber t` as a pullback of
  `(projModelπ W, Spec residueFieldMap)`-cospan (after rewriting `fiberToSpec (g t) =
  e_s.hom ≫ projModelπ W` via the e_s-π-leg); (iii) compare with
  `projModelBaseChangeLift_isIso` at R := κ(s)-carrier, R' := κ(t)-carrier
  (letI (residueFieldMap).hom.toAlgebra) — two pullbacks of the SAME cospan ⟹
  canonical iso `fiber t ≅ projModel (W.map residue-hom)`; take `W' := W.map …`,
  `IsElliptic` via map-instance; (iv) π-leg compat falls out of the pullback-legs +
  lift_snd; (v) ZERO-LEG (the one genuinely new piece): need
  `projModelBaseChange_zero : Spec.map (ofHom f) ≫ projModelZero W ≫?? — precisely:
  zero-W' ≫ projModelBaseChange f W = Spec.map (ofHom f) ≫ projModelZero W`
  (fromOfGlobalSections naturality under Proj.map — NOT in mathlib; derive via
  fromOfGlobalSections_toSpecZero + faithfulness-style argument or chartwise through
  the Y-chart with the T-A2e machinery; if it fights, spawn T-A5b-zero) and then
  `sectionFiberPoint`-naturality (two small commuting squares).
- **ZERO-LEG ROUTE (v2)**: mathlib has `Proj.fromOfGlobalSections_preimage_basicOpen`
  (ProjectiveSpectrum/Basic.lean:455). The evaluation defining `projModelZero` sends
  `t₁ = mk Y ↦ 1` (a unit), so `projModelZero ⁻¹ᵁ D₊(t₁) = ⊤`; factor BOTH sides of
  the naturality square through the Y-chart by `IsOpenImmersion.lift` (range-condition
  from that preimage computation + opensRange_awayι), then cancel the mono `awayι-Y`
  and compare chart-level ring maps: `Away.map bcHom t₁ ∘ (zero-W-chart-hom) =
  (zero-W'-chart-hom) ∘ f`-elementwise on `Away.mk` normal forms (the zero-chart-hom
  is evaluation `U ↦ 0, W ↦ 0` under chartCoordEquiv — relate via
  `chartSolutionsEquiv`/`infPoint`-style computations or directly by val_injective).
  Alternatively check first whether mathlib has any `fromOfGlobalSections`-naturality
  (`Proj.map_fromOfGlobalSections`?) — grep before building.

### [T-A5c] Base-change group-structure Props: `comm` + `one_eq_zero` (sub-ticket of T-A5)
- **Status**: done (beastmode 2026-07-07T19:45Z → 2026-07-07T21:00Z —
  `EllipticCurve.baseChange` is now FULLY sorry-free (all fields). `comm`:
  `Over.isCommMonObj_mk_pullbackSnd` applies directly. `one_eq_zero`: the field goal
  is instance-HETEROGENEOUS from birth (record-η typed via
  `((Over.pullback g).obj _).left` vs raw pullback legs) — naked rw/simp refuse or
  produce ill-typed goals; the working recipe: `pullback.hom_ext` → per-component
  `dsimp [Over.grpObjMkPullbackSnd_one]` (dsimp REBUILDS a well-typed goal even when
  the lemma itself doesn't fire) → `simp only [grpObjMkPullbackSnd_one, Over.pullback,
  Over.comp_left, Over.homMk_left, id_comp, E.one_eq_zero, Over.mk_left]` (unfolds the
  functor map into raw lifts) → finish in PURE TERM MODE (Category.assoc terms +
  congrArg + pullback.lift_fst/snd + ε-facts `Over.w ε` and fst = snd ≫ g from
  condition; congrArg-calc because rw's auto-rfl fails at reducible on the mixed
  middles; `pullback.condition (f := 𝟙 S) (g := g)` needs pinning). Axioms standard.)
- **File**: EllipticCurve/GroupLaw.lean · `baseChange.comm`, `baseChange.one_eq_zero`
- **Depends on**: T-A5 (done) · **Parallel**: yes · **Type**: Prop fields
- **Sketch**: `comm`: mathlib instance `Over.isCommMonObj_mk_pullbackSnd`
  (Cartesian/Over.lean:311) — pullback of a commutative monoid object is commutative;
  instance-defeq between `grpObjMkPullbackSnd.toMonObj` and `monObjMkPullbackSnd`
  (both via mapGrp/mapMon on `Over.pullback g`). `one_eq_zero`: the transported unit
  is `LaxMonoidal.ε ≫ (Over.pullback g).map η` (simps-generated
  `grpObjMkPullbackSnd_one` / `monObjMkPullbackSnd_one`, -isSimp); compute `.left`
  by `pullback.hom_ext`: fst-leg reduces along `E.one_eq_zero`, snd-leg is the
  Over-structure w-condition; `preservesTerminalIso_pullback` (same file, @[simp])
  gives the ε-component.
- **Sources**: mathlib `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`. **Generality**: any `g : T ⟶ S`.

### [T-A6] ⧗KM Abel canonicity — the deferred "purity/comparison" project (v2)
- **Status**: open, **phase 3+ — no longer blocks anything** (v2: group law is a field
  of the working record, D5) · **File**: EllipticCurve/GroupLaw.lean ·
  `abelEnrichment_exists`, `abelEnrichment_unique`, `point_smul_eq_comp_mulBy`
- **Depends on**: T-A2, AG-LB or divisor route · **Parallel**: self-contained project
- **Type**: theorems (no data)
- **Sketch** (KM 2.1.2): the seven named boxes fixed by the reviewer (Q3), stated once
  and never grown: coherent-base-change; relative-duality-genus-one; relative-Picard;
  Poincare; Abel-isomorphism; group-law-from-Abel; torsion. Then transport + uniqueness.
- **Sources**: [KM] 2.1 ⧗ (do-not-formalize-from-memory) · Mumford AV p. 53 ·
  [Hida-GME] §2.1. **Generality**: any base scheme.
- **AINTLIB Pic SURVEY (beastmode-B, 2026-07-06 — user-requested; reshapes this
  ticket)**: HasseWeil (`Foundation/Curves/Divisor/`) has a SORRY-FREE field-level
  Pic⁰ theory for Weierstrass curves: `ProjectiveDivisor` + degree + `degZero` +
  `projPrincipalSubgroup` + `PicProj₀`; κ = `picZeroOfPoint` (P ↦ [P]−[O]) with
  **injectivity proved** (`picZeroOfPoint_injective`, `kappaDivisor_inj`,
  Miller.lean:1576); σ̄ : `PicProj₀ →+ W.Point` ASSEMBLED as AddMonoidHom
  (MillerAllChar.lean:676); **Miller's relation char-uniform**
  (`miller_hypothesis_holds_allChar`: (P)+(Q)−(P+Q)−(O) ∈ Princ, via mathlib's
  char-free `XYIdeal_mul_XYIdeal`) = κ-additivity FOR CHORD–TANGENT, all chars;
  divisor pushforward along isogenies (PicZeroPushforward); Miller functions
  (Weil-pairing backend); `DegreeQuadraticForm.lean`: dual-isogeny degree theory
  incl. `β.comp α = mulByInt α.degree` — the `deg [N] = N²` anchor BB-DEG cites.
  Mathlib has ring-level `CommRing.Pic` (RingTheory/PicardGroup.lean, invertible
  modules) but NO scheme-level Pic yet. CONSEQUENCE: chord–tangent ≅ Pic⁰ over a
  field is DONE on the shelf; the seven-box cluster's live mathematical content
  narrows to ONE heart — κ-additivity for an ABSTRACT GrpObj law with identity O
  (equivalently: realize chord–tangent as a scheme morphism, now anchored by
  `XYIdeal_mul_XYIdeal`, or the see-saw/KM 2.1.2 route needing relative Pic).
  Shelf-ready supporting leaf: GrpObj-uniqueness-with-fixed-identity over k̄ via
  the Yang–Merten rigidity toolbox (mathlib Group/Abelian.lean).
- Note: `pointEquivOverHom`, `pointAddCommGroup`, base-change group data are **done**
  (real definitions, integration commit). `point_smul_eq_comp_mulBy` **DONE**
  (beastmode 2026-07-06: transported smul is rfl-transparent through the equiv;
  `GrpObj.comp_zpow` + `Over.comp_left`; close by defeq `exact` — `rw` fails on the
  CommaMorphism/Over.Hom.left spelling split, `simp only [Over.comp_left]` matches).

### [T-B2] μ_N and (ℤ/N) wiring (DS3 discharge)
- **Status**: done (beastmode-B, 2026-07-06T08:57Z → 2026-07-06T10:09Z) ·
  **Claimed**: beastmode-B (stream-B worker), 2026-07-06T08:57Z ·
  **File**: GroupScheme/MuN.lean · `muNGrpObj`, `constZModGrpObj`,
  `muNPointsEquiv` (+ its naturality — `muNPointsEquiv_natural` now stated in skeleton)
- **Depends on**: none · **Parallel**: yes · **Type**: def(data) + theorems
- **Sketch**: comult `Spec.map (T ↦ T ⊗ T)` on `ℤ[T]/(Tᴺ−1)`; pullback to `S`; GrpObj
  fields via `Over`-cartesian-monoidal API (pattern: mathlib
  `AlgebraicGeometry/Group/*.lean`); points: `Γ–Spec` adjunction + pullback universal
  property. `(ℤ/N)_S`: coproduct-indexed addition.
- **Mathlib needed**: `Over.cartesianMonoidalCategory` (local instance!), `ΓSpec`
  adjunction, `Sigma.desc`. **Sources**: [Loe] §3.2 example; [KM] 1.12 ⧗.
- **Generality**: any `S`, any `N ≥ 1` (étale statements separately, T-B7).
- **Progress**:
  - 2026-07-06T09:35: `muNGrpObj` + `muNPointsEquiv` + `muNPointsEquiv_natural`
    sorry-free. Route of record: NOT the hand-rolled comult — both DS3 instances are
    induced by representability (`GrpObj.ofRepresentableBy`, mathlib
    Monoidal/Cartesian/Grp) from their points presheaves, so the points specs pin the
    group law definitionally. μ_N points engine mirrors
    `AffineSpace.toSpecMvPolyIntEquiv`: private `muNRingGen` (class of `T`),
    `muNRing_hom_ext` (gen-generated: `Polynomial.ringHom_ext'` + `RingHom.ext_int`
    through ULift/quotient), `muNRingLift` (`Ideal.Quotient.lift` of `eval₂RingHom`;
    vanishing lemma must be a STANDALONE lemma — inline `<| by` in lift's H
    deadlocks elaboration), `specHom_ext` (maps into `Spec R` determined by `appTop`;
    via `Adjunction.homEquiv_symm_apply` + counit-cancel `congr 1` — upstream
    candidate), `muNSpecHomEquiv` (left_inv via `specHom_ext` + `cancel_epi
    (ΓSpecIso).inv` + gen-ext, avoiding adjunction-side `dsimp` which unfolds
    `muNRing` and wrecks rw-motives). Gotcha of record: ULift/CommRingCat-carrier
    instance spellings are only defeq at default transparency — keep all rewriting at
    folded `muNRing N`-spellings; value-level `_coe` rfl-lemmas + `show` beat `simp`
    on structure-literals.
  - 2026-07-06T10:00: `constZModGrpObj` sorry-free + NEW public pins
    `constSchemePointsEquiv` / `constSchemePointsEquiv_natural` (DS3b spec, register
    rule (iii)): S-morphisms into `∐_A S` over `g` ≃ locally constant `A`-valued
    functions. Engine: `nonempty_isColimit_cofanMk_of` on the clopen fibre partition
    of a locally constant function (mathlib recognises it as a coproduct);
    `constIndex` via `Cover.exists_eq`-choice + uniqueness from
    `disjoint_opensRange_sigmaι` (`sigmaMk` is universe-rigid `σ : Type u` — NOT
    usable for `A : Type 0`; the choice-based index + spec/uniqueness interface
    replaces rfl-anchoring). `constScheme`/`constSchemeπ` marked `@[reducible]`
    (projModel precedent) to dissolve `∐`-vs-def motive mismatches. `Finite (ZMod N)`
    needs `[NeZero N]` on the private functors. Needed import added:
    `Mathlib.Topology.LocallyConstant.Algebra` (group instances + `comapAddMonoidHom`).
  - 2026-07-06T10:09: DONE — group-law pins `muNPointsEquiv_one`/`muNPointsEquiv_mul`
    added (one-term proofs via `yonedaMonObjIsoOfRepresentableBy` components).
    `#print axioms` on all 8 public decls: propext/Classical.choice/Quot.sound only.
    Module + WeilPairing-exposure check green (whole-lib gate currently blocked by
    stream-A's in-flight WeierstrassModel edit — not MuN-related; MuN's only importer
    WeilPairing/Basic uses muN/muNπ/muNPointsEquiv, signatures unchanged).
    Post-proof cleanup: ✓ ran (inline pass — privates marked, docstrings on all new
    publics, module docstring updated to constructed-state; FULL per-file /cleanup =
    board ticket [CLEANUP-4], whose T-B2 dependency is now satisfied). Upstream
    candidates flagged: `specHom_ext`, `nthRootsCommGroup`,
    `Proj`-independent points engine. T-B7 statements (muNπ_isFinite/flat/finrank/
    etale_iff) remain open sorries as planned.

### [T-B7] μ_N finite locally free of rank N, étale iff N invertible (spawned by beastmode-B, 2026-07-06)
- **Status**: done (beastmode-B, 2026-07-06T10:18Z → 2026-07-06T11:26Z) ·
  **Claimed**: beastmode-B (stream-B worker),
  2026-07-06T10:18Z · **File**: GroupScheme/MuN.lean · `muNπ_isFinite`, `muNπ_flat`,
- **Progress**:
  - 2026-07-06T10:45: THREE OF FOUR proved+committed (muNπ_isFinite, muNπ_flat,
    muNπ_finrank = N). Engine: `Monic.finite_quotient`/`free_quotient` for
    ℤ[T]/(Tᴺ−1); `isPullback_muN` (private) moves the defining square's corner from
    the abstract terminal to `Spec (ULift ℤ)` via `paste_vert` + `of_vert_isIso` +
    `specULiftZIsTerminal.hom_ext`; property transport by
    `MorphismProperty.of_isPullback (…).flip`; rank via
    `finrank_comp_{left,right}_of_bijective` (strip ULift equivs) +
    `rankAtStalk_eq_finrank_of_free` + `powerBasis'` dim. GOTCHAS: pass
    @-explicit instances to `finrank_of_isPullback` and use
    `congrFun (finrank_SpecMap_eq_finrank …)` instead of rw (invisible
    instance-spelling mismatches defeat kabstract); `natDegree_X_pow_sub_C`'s value
    arg is named `r`. REMAINING: `muNπ_etale_iff` — plan: (⟸) factor S through
    Spec ℤ[1/N] via Away.lift on toSpecΓ, base-change the étale absolute
    μ_N/ℤ[1/N] (standard-smooth-of-rel-dim-0 presentation: jacobian N·T^{N−1},
    T invertible in the quotient); (⟹) reduce to fibres at points where N ∈ 𝔪_s
    (isUnit-iff-basicOpen-⊤), field case via unramified ⟹ T^N−1 separable ⟹
    N ≠ 0 in κ(s). Check RingTheory/{Etale,Unramified} for
    AdjoinRoot-separable dictionaries before hand-rolling.
  - 2026-07-06T11:00: etale_iff SPLIT into `etale_muNπ_of_isUnit` /
    `isUnit_of_etale_muNπ` (committed, both sorried — the ONLY sorries left in
    MuN.lean). ENGINE MAP (all verified present): `RingHom.Etale` ↔ Flat ∧
    FormallyUnramified ∧ FinitePresentation (RingHom/Etale.lean:84);
    `Etale` scheme-class has `HasRingHomProperty @Etale RingHom.Etale` ⟹
    `HasRingHomProperty.Spec_iff`; `isPullback_SpecMap_of_isPushout`
    (Pullbacks.lean:787) + `pullbackSpecIso R S T` (affine pullback = Spec of
    tensor); `StandardEtalePair` + instance `Algebra.Etale R P.Ring`
    (Etale/StandardEtale.lean:191); `Polynomial.separable_X_pow_sub_C`;
    Morphisms/FormallyUnramified.lean exists. ROUTE DECISION (⟸): build the
    ℤ[1/N]-model `Spec (ULift (Away (N:ℤ)[X]⧸(X^N−1)))`, ONE pushout square
    (Algebra.IsPushout at ULift level — localization-tensor collapse), étale-ness
    of the model by StandardEtalePair-or-direct (T is a unit in the quotient since
    T·T^{N−1}=1, so derivative N·T^{N−1} is a unit when N is), S factors through
    Spec ℤ[1/N] via toSpecΓ ≫ Spec.map (IsLocalization.Away.lift at h), paste with
    isPullback_muN, finish by MorphismProperty.of_isPullback. (⟹): base-change to
    Spec κ(s) at a point where N is not a unit in the stalk (isUnit-in-Γ ↔
    basicOpen = ⊤ ↔ unit in every stalk), affine-identify the fibre as
    Spec (κ[T]/(T^N−1)) via pullbackSpecIso-transport, RingHom.Etale ⟹
    FormallyUnramified ⟹ (Unramified/Field) reduced — contradict
    (T^{N/p}−1)^p = T^N−1 nilpotent for p = char κ ∣ N. ULift-transports via
    RingHom-property-of-bijective composition lemmas (pattern proven in
    muNRingMap_finite/flat/finrank).
  - 2026-07-06T11:50: (⟸) DONE — `etale_muNπ_of_isUnit` PROVED. Chain (all in
    MuN.lean, private): `muNModel_isPushout` (AdjoinRoot(Xᴺ−1)/ℤ[1/N] is the
    pushout of muNRing along ℤ→ℤ[1/N]; pure UP-proof via
    `PushoutCocone.IsColimit.mk` + `AdjoinRoot.lift` as desc + `muNRing_hom_ext`;
    KEY GOTCHA: ascribe `(s.inl.hom : muNAwayRing N →+* s.pt)` — AdjoinRoot.lift's
    R picks up the bundled-carrier spelling otherwise and everything breaks
    invisibly; term-glue congrArg chains instead of rw for mk-X computations);
    `muNStdPair` ((Xᴺ−1, C N) standard étale: f'·X − N·f = N witness);
    `muNModel_algebra_etale` (IsLocalization.atUnits collapse + equivAwayAdjoinRoot
    + Algebra.Etale.of_equiv); `muNModelStruct_etale` (RingHom.etale_algebraMap);
    assembly: factor S → Spec ℤ[1/N] via Away.lift on toSpecΓ (hom-ext to terminal
    makes the square-leg identification FREE), `IsPullback.of_right`-extraction
    with mid := t.lift, `MorphismProperty.of_isPullback` +
    `HasRingHomProperty.Spec_iff`. New import: Mathlib.RingTheory.Etale.StandardEtale.
    REMAINING (last sorry in file): `isUnit_of_etale_muNπ`. PLAN: (1) generalize
    muNModel-pushout defs from Away(N) to arbitrary A : CommRingCat (proof is
    base-agnostic); (2) reusable `isPullback_muN_baseChange` (θ, IsPullback θ π_T
    π_S g) by the same of_right-extraction; (3) unit-criterion: IsUnit (N : Γ) ↔
    basicOpen = ⊤ (grep exact name), pick s with (N : κ(s)) = 0, base-change étale
    along fromSpecResidueField; (4) field case: A := κ(s)-instantiated LEFT-square
    has g-leg 𝟙 ⟹ mid iso ⟹ Etale (Spec.map struct_κ) by iso-cancel ⟹
    FormallyUnramified ⟹ `Algebra.FormallyUnramified.isReduced_of_field`;
    contradiction: y := mk(X^{N/q}−1), y^q = 0 by `sub_pow_char` (q := ringChar κ,
    prime since (N:κ)=0, q ∣ N via CharP.cast_eq_zero_iff), y ≠ 0 by
    degree-lt-dvd.
  - 2026-07-06T11:26: DONE — `muNπ_etale_iff` proved; **MuN.lean sorry-free**; all
    four T-B7 theorems axiom-clean (standard three). Converse per plan: pushout
    block generalized to arbitrary (A : Type u) [CommRing A];
    `isPullback_muN_baseChange`; residue criterion
    (`RingedSpace.isUnit_of_isUnit_germ` + `residue_ne_zero_iff_isUnit` +
    map_natCast glue); field case: étale moved to `Spec.map (muNModelStruct K N)`
    via `isoIsPullback` vs the `of_horiz_isIso` trivial square +
    `cancel_left_of_respectsIso`, then `RingHom.etale_algebraMap` →
    `FormallyUnramified.isReduced_of_field` vs nilpotent `mk (X^{N/q} − 1)`
    (`sub_pow_char`, hand-rolled `CharP (K[X]) q`; nonzero by
    `natDegree_le_of_dvd` + `Nat.div_lt_self`). NEW GOTCHAS of record: never
    `rw … at` an already-rewritten IsPullback hypothesis (leaves rfl-uncloseable
    `X = X`; rebuild squares with fresh-goal rewrites); `simpa using
    <simp-tagged lemma>` self-destructs to `True`. Upstream candidates:
    `specHom_ext`, `nthRootsCommGroup`, `CharP (K[X])` instance, monic-quotient
    étale-iff bundle. [CLEANUP-4] deps now fully satisfied (covers T-B7 additions).
  `muNπ_finrank`, `muNπ_etale_iff` (statements already in skeleton; attack log
  foundations.md verdicts SURVIVED/QUOTE-MISSING) · **Parent**: T-B2
- **Depends on**: none · **Parallel**: yes · **Type**: theorems
- **Proof sketch**:
  1. `ℤ[T]/(Tᴺ−1)` is finite free of rank `N` over `ℤ` (monic quotient basis
     `1,…,T^{N−1}`: mathlib `AdjoinRoot.powerBasis`/monic-quotient free module —
     verify names; `X^N − 1` monic for `N ≠ 0`).
  2. `Spec` of a finite free algebra is finite + flat + constant `finrank = N`;
     transfer along the defining terminal-pullback (mathlib base-change stability
     instances for `IsFinite`/`Flat`; `Scheme.Hom.finrank` pullback lemma in
     FlatRank.lean — verify).
  3. `muNπ_etale_iff`: (⟸) `Tᴺ−1` separable when `N` invertible (`derivative =
     N·T^{N−1}` comaximal with `Tᴺ−1`); (⟹) at a point with residue char `p ∣ N`
     the fibre `κ[T]/(Tᴺ−1)` is non-reduced (`T = 1` multiple root), contradicting
     unramified ⟹ reduced fibres. Both sides vacuous for `S = ∅`.
- **Mathlib lemmas needed**: monic-quotient basis, `Polynomial.separable_X_pow_sub_C`
  -adjacent (verify for `Xⁿ − 1`), étale ⟺ flat + unramified dictionaries; verify all
  names via the five-method search at start.
- **Sources**: [Loe] §3.2 (representability quote in hand); [KM] 1.12 ⧗ (KM-quote
  gate applies only to attributing the statement to KM — content is standard).
- **Generality**: as stated (`[NeZero N]`, arbitrary `S`).

### [T-B3] E[N] ↪ E closed immersion + `torsionIdeal`
- **Status**: done (beastmode-B, 2026-07-06T10:13Z → 2026-07-06T10:18Z) ·
  **Claimed**: beastmode-B (stream-B worker), 2026-07-06T10:13Z ·
  **Files**: Torsion.lean (`torsionι_isClosedImmersion`),
  LevelStructure/Basic.lean (`torsionIdeal_subscheme` = T-B3a pin, per Amendments v5;
  `torsionIdeal` itself is already a real def `(E.torsionι N).ker`)
- **Progress**:
  - 2026-07-06T10:18: DONE both halves, first-try. `torsionι_isClosedImmersion`:
    `IsClosedImmersion (zero ≫ π)` by `rw [zero_π]; infer_instance`, then
    `IsClosedImmersion.of_comp` (section of the separated `π`; `IsProper extends
    IsSeparated` so the instance chain fires), then base-change stability
    `MorphismProperty.pullback_fst`. `torsionIdeal_subscheme` (T-B3a):
    `IsClosedImmersion.lift`/`isIso_lift` + `lift_fac` against
    `Scheme.IdealSheafData.ker_subschemeι` (torsionIdeal := (torsionι).ker is defeq
    on the nose). `#print axioms` both: propext/Classical.choice/Quot.sound.
    Torsion.lean + LevelStructure/Basic.lean modules green. Unblocks T-B6 and the
    D-lane consumers of the E[N]-subscheme dictionary.
- **Depends on**: none (v2: group data is in the record) · **Parallel**: with T-B4/B5 · **Type**: theorem + def
- **Sketch**: zero section is a closed immersion (`π` separated; mathlib
  `isClosedImmersion_of_comp_eq_id` pattern seen in `Group/Abelian.lean`); closed
  immersions stable under pullback; convert via `IsClosedImmersion` ↔ ideal-sheaf
  (mathlib `IdealSheafData` dictionary).
- **Sources**: [KM] 1.3/2.3 ⧗; standard. **Generality**: any `N ≠ 0`.

### [T-B4] ⧗KM E[N]/S finite locally free of rank N² (KM 2.3.1; BB-FLAT)
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-07T21:15Z →
  2026-07-08T00:30Z — all three targets DERIVED, sorry-free modulo the three named
  KM 2.3.1 boxes now stated in Torsion.lean: `mulByHom_locallyQuasiFinite` (BB-QF,
  fibre input), `mulByHom_flat` (BB-FLAT), `mulByHom_finrank` (BB-DEG, deg [N] = N²)
  — box discharge is T-B4x (blocked on T-B6/HasseWeil comparison). QUOTE-GATE
  SATISFIED: KM 2.3.1 full statement + proof mined from the full PDF (printed
  pp. 73–75; proof = reduce to universal regular Weierstrass base + miracle flatness
  [AK-1 V 3.6] + fibrewise nonconstancy via M²-torsion + rank at one ℂ-point).
  REAL new infrastructure: `torsionι_π` (@[reassoc]), `mulByHom_isProper` (instance;
  cancellation IsProper.of_comp along separated π), `mulByHom_zero`
  ([0] = π ≫ zero — the hom-group unit is DEFINITIONALLY toUnit ≫ η: zpowRec 0
  reduces, h0 := rfl!), `mulByHom_isFinite` (ZMT
  IsFinite.of_isProper_of_locallyQuasiFinite), `torsionπ_isFinite` (base change),
  `torsionπ_flat` (N = 0 branch REAL: kernel of [0] is all of E via
  pullback_snd_iso_of_left_factors_mono against the split-mono zero section +
  Smooth→Flat; N ≥ 1 via BB-FLAT base change), `torsion_rank`
  (Scheme.Hom.finrank_pullback_snd + BB-DEG). LEAN GOTCHAS BANKED: calc chains
  across defeq-but-not-syntactic types (E.torsion N vs raw pullback; Over-.left vs
  raw) fail Trans-synthesis — show-recast to ONE raw spelling first;
  `𝟙_` needs `open MonoidalCategory`; SmoothOfRelativeDimension.smooth is a lemma
  (n explicit, f explicit), not an instance.) ·
  **File**: Torsion.lean · `torsionπ_isFinite`, `torsionπ_flat`,
  `torsion_rank` · **Depends on**: T-B3 (done); boxes → T-B4x · **Parallel**: with T-B5 · **Type**: theorems
- **Sketch**: `[N]` proper + quasi-finite ⟹ finite (mathlib ZMT
  `IsFinite.of_isProper_of_locallyQuasiFinite` — verified present); fibrewise flatness
  criterion (BB-FLAT, stated black box) + fibre degree `N²` (Silverman III.6.2(d);
  fibre anchor: HasseWeil `mulByInt_degree`).
- **Sources**: [KM] 2.3.1 ⧗ · EGA IV 11.3.10 · [Sil] III.6.2.

### [T-B4x] Discharge the KM 2.3.1 boxes (BB-QF, BB-FLAT, BB-DEG)
- **Status**: blocked (needs T-B6 fibre comparison — stream-B in progress — plus the
  HasseWeil `mulByInt_degree` anchor; alternatively the KM-native route needs the
  universal-Weierstrass reduction = BB-RR-adjacent moduli machinery)
- **File**: Torsion.lean · `mulByHom_locallyQuasiFinite`, `mulByHom_flat`,
  `mulByHom_finrank` · **Depends on**: T-B6 · **Type**: theorems
- **Sketch**: KM 2.3.1 proof (mined, printed pp. 74–75): quasi-finiteness geometric
  fibre by geometric fibre (nonconstancy via permuted M-torsion, M prime to N·char);
  flatness by miracle flatness over the universal regular base (or fibrewise
  criterion EGA IV 11.3.10); degree at a single geometric point per connected
  component. One conclusion per box; do not merge.
- **Sources**: [KM] 2.3.1 (quote banked in T-B4 notes) · EGA IV 11.3.10 · [Sil] III.6.2.

### [T-B5] [N] étale when N invertible (+ E[N] finite étale)
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-08T00:45Z →
  2026-07-08T02:00Z — both targets DERIVED: `mulBy_etale` via
  `Etale.of_formallyUnramified_of_flat` (f explicit) from BB-DIFF
  (`mulByHom_formallyUnramified`, Loeffler 3.4.2(2) verbatim quote in docstring) +
  BB-FLAT + the lfp mini-box `mulByHom_locallyOfFinitePresentation` (scheme-level
  cancellation lfp(f≫g)+lft(g)⟹lfp(f) MISSING from mathlib — ring-level exists as
  RingHom.FinitePresentation.of_comp_finiteType; ForMathlib target → T-B5x);
  `torsionπ_etale` by base change. The `N = 0`-invertible degenerate case is handled
  FOR REAL: new lemma `isEmpty_of_nIsInvertible_zero` (IsUnit 0 ⟹ 0 = 1 in Γ ⟹ every
  stalk would be a trivial local ring — germ + one_ne_zero), then E empty and [0] is
  an iso (isIso_of_isEmpty target-empty) hence étale.) · **File**: Torsion.lean · `mulBy_etale`, `torsionπ_etale`
- **Depends on**: invariant-differential input only (v2: not the Abel chain) · **Parallel**: with T-B4 · **Type**: theorems
- **Sketch**: [Loe] 3.4.2(2) verbatim route: `[N]` multiplies the invariant
  differential by `N` ⟹ iso on (co)tangent ⟹ formally étale; + lfp. Needs the
  invariant-differential API (sub-ticket if mathlib's `Ω¹` for schemes is insufficient
  — check `RingTheory.Kaehler` sheafification status first).
- **Sources**: [Loe] Lemma 3.4.2(2) (quote in decomposition).

### [T-B5x] ForMathlib: scheme-level lfp cancellation (unblocks the T-B5 lfp mini-box)
- **Status**: done (beastmode-A 2026-07-08T02:15Z → 2026-07-08T03:00Z —
  `LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType` PROVED sorry-free in
  ForMathlib/FinitePresentationCancel.lean (upstream candidate; axioms standard), and
  `mulByHom_locallyOfFinitePresentation` discharged for real ([N] ≫ π = π + Smooth π).
  Proof mirrors `HasRingHomProperty.of_comp`'s three-wlog cascade threading the lft
  side-condition: step 1 restricts both hypotheses along Z-affines
  (`IsZariskiLocalAtTarget.restrict`), step 2 turns f into `f ∣_ U` and g into
  `U.ι ≫ g` (side condition re-established by the comp-instance — NB a bare
  `haveI := hg` SHADOWS the wlog's `this`; name it), step 3 source-localises, and the
  affine corner is `RingHom.FinitePresentation.of_comp_finiteType` after
  `Scheme.Hom.comp_appTop` + `CommRingCat.hom_comp`.) · **File**: ForMathlib/FinitePresentationCancel.lean ·
  `LocallyOfFinitePresentation.of_comp` (f g; [LocallyOfFinitePresentation (f ≫ g)]
  [LocallyOfFiniteType g] : LocallyOfFinitePresentation f) — then discharge
  `mulByHom_locallyOfFinitePresentation` ([N] ≫ π = π, π lfp by smoothness, π lft).
- **Depends on**: none · **Parallel**: yes · **Type**: theorem (upstream candidate)
- **Sketch**: affine-locally: cover Y by affines V, X by affines U ⊆ f⁻¹V; on rings the
  statement is `RingHom.FinitePresentation.of_comp_finiteType` (mathlib,
  RingTheory/FinitePresentation.lean:443). Glue via the `HasRingHomProperty` /
  `affineLocally` framework (mirror how mathlib proves composition-stability; the
  cancellation direction needs the source-affine charts of `f ≫ g` refined against
  `g`-charts — see Stacks 01TX for the classical bookkeeping).
- **Sources**: Stacks 01TX/02FV · mathlib RingTheory/FinitePresentation.

### [T-B5y] Discharge BB-DIFF (invariant differential; gated on scheme Ω¹ API)
- **Status**: blocked (mathlib has no usable relative-differentials sheaf API for
  schemes yet — check again after bumps; the ring-level `FormallyUnramified` is
  `RingHom`-transferable once the translation-invariance of `Ω¹_{E/S}` is expressible)
- **File**: Torsion.lean · `mulByHom_formallyUnramified` · **Depends on**: AG-Ω gap ·
  **Type**: theorem
- **Sketch**: Loeffler 3.4.2(2): `[N]^* ω = N · ω` for the invariant differential ω
  (prove by induction from `[m+1] = [m] + id` and the rigidity of translation);
  `N` unit ⟹ iso on cotangent ⟹ unramified. KM 2.3.2 Lie-algebra variant (quote
  banked: `Lie([N]) = N`).
- **Sources**: [Loe] 3.4.2(2) (verbatim quote in the box docstring) · [KM] 2.3.2.

### [T-B6] Fibre comparison: E[N] geometric fibres ≅ (ℤ/N)² (reuse HasseWeil)
- **Status**: done-modulo-registered-boxes (beastmode-B, 2026-07-06 — HEADLINE
  `torsion_geometricFibre_rank_two` PROVED via the counting route; sorryAx enters
  ONLY through the four registered Torsion.lean boxes BB-QF/BB-FLAT/BB-DEG/BB-DIFF
  (same bar as T-B4/T-B5). All five sub-tickets T-B6a–e sorry-free AND axiom-clean:
  mulByHom_baseChange, torsionBaseChangeHom + torsion_baseChange_isPullback,
  nIsInvertible_spec_iff, natCard_sections_eq_finrank
  (ForMathlib/EtaleSectionsCount.lean — NEW upstream candidate),
  addEquiv_pi_fin_two_zmod_of_natCard (ForMathlib/FiniteAbelianRankTwo.lean — NEW
  upstream candidate: torsion-count characterisation of (ℤ/N)² via
  recOnPosPrimePosCoprime + elementary divisors + Bezout splitting). Kernel-UP
  torsionPointsEquiv + helpers axiom-clean. HasseWeil import DROPPED from
  TorsionFibre.lean (headline no longer needs the chord–tangent comparison);
  the dictionary remains ONLY as the optional T-B6f-dict leaf for the BB-QF/BB-DEG
  box discharges. Assembly glue: sectionsEquivOverPoints (IsPullback.lift/hom_ext),
  torsionByNsmulKerEquiv (d-torsion inside N-torsion).) ·
  **Claimed**: beastmode-B (stream-B worker), 2026-07-06T11:30Z · **New file**: EllipticCurve/TorsionFibre.lean (B-lane owned) ·
  **Depends on**: T-B3 · **Parallel**: yes · **Type**: theorem
- **Progress**:
  - 2026-07-06T11:35: statement design + ADVERSARIAL FINDING (recorded per standing
    rule 1, new-statement attack): the ticket sketch silently assumes a
    *group-compatible* fibre identification, but `FibrewiseElliptic` provides only
    a POINTED SCHEME iso fibre ≅ projModel W — no compatibility between E's
    abstract `GrpObj` group and mathlib's chord–tangent `Affine.Point` group.
    Without it, "N-killed abstract points ≅ classical E(k̄)[N]" does not follow —
    that dictionary is a genuine leaf adjacent to the deferred Abel/canonicity
    cluster (a fibrewise instance of it), NOT derivable from the current
    interfaces. DESIGN of record: (1) `torsionPointsEquiv` — scheme-points of
    `E[N]` over `t` ≃ `Submodule.torsionBy ℤ (E.Point t) (N : ℤ)` (kernel UP;
    provable NOW from `pointToTorsion` + `point_smul_eq_comp_mulBy` (T-A6d, done
    today) + a small `point_zero_val` helper from the `one_eq_zero` field; this is
    the half stream D consumes). (2) headline
    `torsion_geometricFibre_rank_two : Nonempty (torsionBy … ≃+ (Fin 2 → ZMod N))`
    over alg. closed k with (N : k) ≠ 0 — STATED, sorried, docstring records the
    dependency on the fibre-group-dictionary leaf + HasseWeil's
    `torsion_genN_addEquiv` (import isolated in this file). Attacks run: (i) shape
    matches HasseWeil's `Submodule.torsionBy` spelling; (ii) no NeZero needed for
    (1) (kernel UP is N-uniform); (iii) t-generality: arbitrary T for (1),
    Spec k for (2); (iv) the killed-hypothesis form matches the D-lane's
    `hkill`-convention ((N : ℤ) • P = 0).
- **Sketch**: identify `E[N](k̄)` (scheme fibre points) with Weierstrass-model points
  via `IsWeierstrassModel.points`; then **import
  `HasseWeil.NTorsion.TorsionGeneralN`** (`E[N] ≃ₗ[ZMod N] (Fin 2 → ZMod N)`,
  alg. closed, `N` invertible) — do NOT re-prove. Cross-project import isolated here.
- **Sources**: [Sil] III.6.4(b); in-repo HasseWeil (sorry-free — verified).
- **REPLAN 2026-07-06 (beastmode-B, post T-B4/T-B5 landing; Tier A2 spawn, all
  sub-tickets single-conclusion per statement-splitting/Tier A5)**: kernel-UP half
  (`torsionPointsEquiv` + `point_zero_val` + `smul_eq_zero_iff_comp_mulByHom`)
  VERIFIED sorry-free + axiom-clean today (build green after A-lane unblocked).
  **Headline route switched: counting, not dictionary** (KM 2.3.5/[Sil] III.6.4
  proof shape): torsionPointsEquiv turns k̄-points of the fibre of E[d] into
  #(E.Point t)[d]; finite-étale-rank-d² fibres over k̄ have exactly d² points;
  group theory then forces (ℤ/N)². Uses T-B4/T-B5 outputs (so headline lands
  *modulo the registered boxes* BB-QF/BB-FLAT/BB-DEG/BB-DIFF — same bar as T-B4/5;
  NOT circular: the boxes' own discharge is the separate dictionary leaf below).
  HasseWeil import becomes unnecessary for the headline. Sub-tickets:
  - **[T-B6a]** DONE (beastmode-B 2026-07-06, sorry-free + axiom-clean;
    homMonoidHom/map_zpow route worked; carrier-seam gotcha: rw fails across
    (E.baseChange g).E vs pullback E.π g spellings — term-glue/exact only) ·
    `(E.baseChange g).mulByHom n ≫ pullback.fst E.π g = pullback.fst E.π g ≫
    E.mulByHom n` (single equation). Sketch: `grpObjMkPullbackSnd =
    ((Over.pullback g).mapGrp …).grp` (mathlib Monoidal/Cartesian/Over.lean:317),
    so bundle `h ↦ (Over.pullback g).map h` as a MonoidHom on End-hom-groups
    (map_one via mapMon-η, map_mul via mapMon-μ/prodComparison lemmas ibid.
    260–302), then `map_zpow` + left-component extraction. Fallback:
    `Int.induction_on` with `monObjMkPullbackSnd_one/_mul` simps.
  - **[T-B6b]** DONE (beastmode-B 2026-07-06, sorry-free + axiom-clean; def
    torsionBaseChangeHom + torsion_baseChange_isPullback via private
    torsionLiftAux/comp/uniq, ALL term-glue calc chains — zero rw across the
    carrier seam; typed have-bridges cast field-spellings to pullback-spellings) ·
    was: (def, the canonical witness — per
    statement-splitting shared-witness-∃ preference) + spec
    `torsion_baseChange_isPullback : IsPullback (torsionBaseChangeHom)
    ((E.baseChange g).torsionπ N) (E.torsionπ N) g` (single IsPullback). Sketch:
    kernel-square pasting from T-B6a + zero-compat (`pullback.lift_fst`).
  - **[T-B6c]** DONE (beastmode-B 2026-07-06, sorry-free + axiom-clean, first
    try; ΓSpecIso.hom/.inv + map_natCast both directions).
  - **[T-B6d]** DONE (beastmode-B 2026-07-06, sorry-free + axiom-clean). `card_sections_eq_finrank` —
    X ⟶ Spec (.of k) finite étale, k sep. closed ⇒ `Nat.card {s // s ≫ f = 𝟙}
    = f.finrank x₀` (single equation). NEW FILE ForMathlib/EtaleSectionsCount.lean
    (upstream candidate, Mathlib-only imports). Recon done: no new classification
    leaf needed — `(A →ₐ[k] k) ≃ PrimeSpectrum A` falls out of mathlib's
    `equivPiOfIsSepClosed` + `_comap` + `_self_apply` (Etale/Field.lean:217/232/246;
    ψ ↦ pt.comap ψ, inverse via Pi.evalAlgHom ∘ equivPi; injective since
    ψ = eval_{Ψψ} ∘ equivPi; surjective via Pi.single-separation). Then finrank
    k A = card (PrimeSpectrum A) via finrank_pi; scheme side: IsAffine X (finite
    over affine), X.isoSpec conjugation, Spec.preimage/map_injective turn sections
    into retractions {χ // ψ ≫ χ = 𝟙} ≃ (A →ₐ[k] k) (Algebra via ψ.hom.toAlgebra);
    étale/finite transport via HasRingHomProperty.Spec_iff + cancel-iso; finrank
    transport via IsPullback.of_horiz_isIso square (e.inv, f', f, 𝟙) +
    finrank_of_isPullback + finrank_SpecMap_eq_finrank + rankAtStalk_eq_finrank_of_free
    (all MuN-proven plumbing).
  - **[T-B6e]** `torsionBy_addEquiv_of_card` (pure algebra, no AG) — G
    AddCommGroup, `(h : ∀ d : ℕ, 0 < d → d ∣ N → Nat.card
    (Submodule.torsionBy ℤ G (d:ℤ)) = d ^ 2)` ⇒ `Nonempty (torsionBy ℤ G (N:ℤ)
    ≃+ (Fin 2 → ZMod N))` (single Nonempty). Sketch: card N² + killed by N +
    d-torsion counts force ℤ/N × ℤ/N via the finite-abelian structure theorem.
  - **[T-B6f-dict]** (the leaf BB-QF/BB-DEG cite for their discharge; T-B4x's
    remaining gate now that T-B6 is done) — **Claimed**: beastmode-B, 2026-07-06.
    Fibre group dictionary: E's abstract fibre group vs HasseWeil's chord–tangent
    group on a Weierstrass fibre model (fibrewise canonicity/rigidity over a field).
    SCOPING AMENDED 2026-07-06 (beastmode-B, honest downgrade after reading the
    engine): mathlib's rigidity toolbox covers the TOPOLOGICAL constancy half only;
    the dictionary's true missing half is the CLASSICAL side as scheme data
    (chord–tangent addition as a morphism, or the Pic⁰/Abel route) — exactly the
    deferred T-A6 seven-box cluster, which the v2 plan of record parks. UNCLAIMED,
    returned to the deferred pool with this recon banked. Original recon: mathlib NOW HAS
    `AlgebraicGeometry/Group/Abelian.lean` (Yang–Merten 2026):
    `isCommMonObj_of_isProper_of_geometricallyIntegral` — proper geometrically
    integral group scheme over a field is COMMUTATIVE, proved by the rigidity-style
    constancy argument (commutator ≡ 1 via IsProper/IsIntegral/JacobsonSpace +
    closed-immersion η). Attack: extract/mirror the constancy engine to prove
    group-structure UNIQUENESS with fixed identity (two GrpObj structures on the
    proper integral pointed fibre curve agree: id is basepoint-preserving ⇒ hom by
    rigidity), then transport chord–tangent through the FibrewiseElliptic pointed
    iso. Next: read Abelian.lean:55–130 for the reusable constancy lemma; check
    Group/Smooth.lean; then decompose into leaves on this board.

### [T-C0] Char-0 étale-descent Weil pairing (v2 — first milestone, review Q5)
- **Status**: open · **File**: WeilPairing/ (new construction file) ·
  **Depends on**: T-B6 (fibre comparison), T-F1-adjacent Galois machinery ·
  **Type**: def(data, discharges DS4 over ℚ-schemes) + specs
- **Sketch**: over bases where `N` is invertible, `E[N]` is finite étale; construct
  `e_N` by étale descent of the classical field-level pairing (HasseWeil), verifying
  the T-C2a/b/c specs. Same API as the eventual scheme-level construction (D7).

### [T-C1] ⧗KM Weil pairing, scheme-level construction of record (v2 route = duality)
- **Status**: open (gated: KM 2.8 on the do-not-formalize-from-memory list)
- **File**: WeilPairing/Basic.lean · `weilPairing`, `weilPairing_over` ·
  **Depends on**: T-B3, T-B2, T-D3, AG-CD scoping · **Type**: def(data) + theorem
- **Sketch** (v2, review Q5): final API via **Cartier duality/autoduality**; the KM 2.8
  norm/divisor construction is the comparison backend (and the KM-faithful proof), not
  the API. `N ∣ M` compatibilities structural via duality.
- **Sources**: [KM] 2.8 ⧗ · [Hida-GME] · [Sil] III.8 (fibre anchor).

### [T-C2] Pairing bilinear + alternating (specs)
- **Status**: open · **File**: WeilPairing/Basic.lean · `weilPairingEval_add_left`,
  `weilPairingEval_self` · **Depends on**: T-C1, T-A6d · **Parallel**: yes ·
  **Type**: theorems · **Sources**: [KM] 2.8 ⧗ / [Sil] III.8.1(a,b).

### [T-C3] Fibrewise nondegeneracy (spec)
- **Status**: open · **File**: WeilPairing/Basic.lean ·
  `weilPairingEval_nondegenerate` · **Depends on**: T-C1, T-C4 · **Type**: theorem ·
  **Sources**: [Sil] III.8.1(c) via T-C4 comparison.

### [T-C4] Comparison with HasseWeil field-level pairing + normalisation pin
- **Status**: open · **New file**: WeilPairing/FibreComparison.lean · **Depends on**:
  T-C1, T-B6 · **Parallel**: yes · **Type**: theorem
- **Sketch**: on geometric fibres, `weilPairingEval` agrees with
  `HasseWeil.weilPairing` (import; alg-closed ℓ-case first, composite N via CRT
  statement). This is what PINS the DS4 normalisation — the two conventions differ by
  inverse; decide per review Q6 and record.
- **Sources**: [Sil] III.8; in-repo HasseWeil `WeilPairing/{Pairing,PairingProps}`.

### [T-D1] ⧗(AG-LB) Official Cartier-divisor definition equivalence
- **Status**: blocked (AG-LB) · **File**: CartierDivisor.lean (statement to add when
  AG-LB lands) · **Type**: def + theorem · **Sources**: [KM] 1.1.1/1.2.3 (preview in
  hand — pull quotes when cutting).

### [T-D2] Full sets of sections: reduced-base criterion (KM 1.9.2)
- **Status**: done (beastmode-A 2026-07-08T03:30Z → 2026-07-08T06:00Z —
  `isFullSetOfSectionsAlg_iff_fields` PROVED sorry-free, axioms standard. Pieces:
  (1) ForMathlib/NormBaseChange.lean `norm_tensor_map` (norm commutes with base
  change; det-conjugation via cancelBaseChange + LinearMap.det_baseChange + det_conj
  — NO matrix crawling; upstream candidate); (2) `eq_of_forall_field_hom_eq` (reduced
  separation via nilradical_eq_sInf + residue FractionRing at each prime; NB
  nilradical_eq_zero yields the 0-ideal, not ⊥ — close membership with simpa);
  (3) `sectionBaseChange_tensor_map` (functoriality, induction + simp);
  (4) main proof: universal reduction to A₀ := MvPolynomial ι R over the chosen basis
  (IsReduced instance exists for MvPolynomial), f₀ := Σ Xⱼ ⊗ bⱼ, field-point check
  transported by (1)+(3) with the R-algebra structure on K given by
  (χ₀.comp (algebraMap R A₀)).toAlgebra, then specialisation along aeval of the
  TensorProduct.basis coordinates. LEAN GOTCHA: `set φ := aeval …` blocks
  MvPolynomial.aeval_X from firing inside subsequent simp/rw — quantify the helper
  over `∀ bb, bb = … → …` and instantiate after the sets instead.) · **PLAN**: forward = instantiate. Backward: (1) specialize the
  ∀A-definition to the UNIVERSAL case A₀ := MvPolynomial (Fin n) R, f₀ := Σ Tᵢ ⊗ bᵢ
  over a basis — every (A, f) is the image of (A₀-free: actually any (A,f) directly)
  under norm-base-change; (2) A₀ reduced (R reduced + MvPolynomial reduced ✓);
  (3) separation: in a reduced ring x = y ⟺ every hom to a field equates them
  (difference lies in every prime via residue fields ⟹ nilradical = 0);
  (4) at each field-point φ : A₀ → K transport the norm equation via
  NORM-BASE-CHANGE (linchpin lemma — mathlib name to verify; else ForMathlib via
  leftMulMatrix functoriality) + sectionBaseChange-functoriality. Sub-lemmas born
  split per statement-splitting.md. · **File**: CartierDivisor.lean ·
  `isFullSetOfSectionsAlg_iff_fields` · **Depends on**: none · **Parallel**: yes ·
  **Type**: theorem
- **Sketch**: KM 1.9.2's proof (in hand, quoted in decomposition): reduce to reduced
  `R`; equality of two elements of a reduced ring checked at geometric points of
  `Spec R[T₁..T_N]`; norm commutes with base change (`Algebra.norm` base-change lemma —
  verify name; else prove via `LinearMap.det` and `Matrix` base change).
- **Sources**: [KM] 1.9.1–1.9.2 with proofs (IN HAND).

### [T-D3] Divisor sums Σ[Pᵢ] (DS4a discharge)
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-08T06:15Z →
  2026-07-08T09:30Z — DS4a DISCHARGED: `sectionsDivisor` is a TOTAL def with real
  in-scope data (ideal := ∏ᵢ ker (Pᵢ), the KM product-of-ideal-sheaves — mathlib's
  stock `Mul IdealSheafData`); out-of-scope branch ⊤-ideal with vacuous props (stock
  `IsEmpty (⊤.subscheme)` instance + IsOpenImmersion-of-IsEmpty + ClosedImmersion
  iff_isFinite_and_mono). `sectionDivisor` + `sectionDivisor_degree` (single section,
  KM 1.2.2) PROVED sorry-free via ker + IsIso z.toImage transport.
  `sectionsDivisor_degree` derived from the finrank box via dif_pos. FOUR register
  boxes (KM 1.2.2/1.2.3/1.2.6 quotes banked): `sectionsIdeal_isFinite/flat/lfp/
  finrank` — hypothesis-guarded, TRUE, discharge = T-D1 route once AG-LB lands
  (same gate as T-D1; the SES degree argument consumes ideal invertibility).
  Consumers (T-D5/6/7) are interface-unblocked.) · **DESIGN BANKED (2026-07-08T06:30Z)**:
  (0) mathlib NOW HAS `Mul X.IdealSheafData` (IdealSheaf/Basic.lean:410, with
  ideal_mul/support_mul/pow + top/bot lemmas) — the ticket's "add IdealSheafData.mul"
  is obsolete, use the stock one. (1) DATA (total): `ideal := ∏ i, ((P i).1 ≫ ?).ker`
  — sections' kernel ideals via `Scheme.Hom.ker` (total for any morphism); the three
  Prop-fields need KM 1.2.1's standing hypotheses, so make the WHOLE structure-value
  total by classical split: `if h : IsSeparated π ∧ SmoothOfRelativeDimension 1 π
  then real-product-construction else ⟨⊤-ideal, empty-subscheme props⟩` — the
  ⊤-branch's subscheme is empty (support ⊥), and maps out of the empty scheme are
  closed immersions (mathlib instance) hence finite/flat/lfp provable vacuously.
  (2) IN-SCOPE PROPS (the real KM 1.2.2 content): finite/flat/lfp of the
  product-ideal subscheme over S: locally the quotient by ∏ᵢ Iᵢ with each Iᵢ the
  kernel of a section of a smooth relative curve; CRT off the diagonal + filtration
  Iᵢ-powers on the diagonal give finite local freeness; degree additivity ⟹
  `sectionsDivisor_degree = n`. Decompose when executing: (a) section-ker is an
  effective divisor of degree 1 (KM 1.2.2 single-section case); (b) product of
  divisors is a divisor with additive degree (KM 1.1.10-area); (c) assembly.
  (3) `RelEffCartierDiv.baseChange` Prop-fields (same file, T-D12-adjacent) are
  base-change-stability one-liners once (2) is packaged.
  **(2a) IS NEARLY FREE (discovery 2026-07-08T07:00Z)**: mathlib has
  `instance [IsClosedImmersion f] : IsIso f.toImage` (ClosedImmersion.lean:154) and
  `f.image := f.ker.subscheme`, `toImage ≫ imageι = f`. For a section z of separated π
  (closed immersion via the T-B3 of_comp pattern): z.ker.subschemeι = z.imageι =
  inv z.toImage ≫ z, so subschemeι ≫ π = inv z.toImage ≫ 𝟙 = inv z.toImage — an ISO —
  finite/flat/lfp/rank-1 all transported from iso-instances. Write
  `sectionDivisor (π) [IsSeparated π] (z) (hz) : RelEffCartierDiv π` first, then the
  n-fold product (CRT/filtration = the remaining mountain; consult KM 1.1-1.2 pages
  via the full PDF, printed pp. ~7-20, before formalising — quote-gate for 1.2.2).
  (2a) DONE 2026-07-08T08:00Z: `sectionDivisor` + `sectionDivisor_degree` sorry-free
  in CartierDivisor.lean (ker + toImage-transport; degree via
  finrank_eq_one_of_isIso; NB IsIso.eq_inv_comp for the `= inv _ ≫ _`-orientation).
  (2b) QUOTES MINED (2026-07-08T08:30Z, printed pp. 7-9): KM 1.2.2 "any section
  s ∈ C(S) defines an effective Cartier divisor [s]" (proof: EGA IV 8.9.1 noetherian
  reduction + 1.1.5.2 geometric-fibre flatness); KM 1.2.3 "D closed, finite flat and
  of finite presentation over S ⟺ effective Cartier divisor proper over S" (THE
  working-def equivalence = T-D1's content); KM 1.2.5 degree = locally free rank of
  the affine ring; KM 1.2.6 deg(D₁+D₂) = deg D₁ + deg D₂ (proof via the SES
  0 → I₁/I₁I₂ → O/I₁I₂ → O/I₁ → 0 and invertibility of I₁ — NEEDS the AG-LB
  invertible-ideal input, same as T-D1). DECISION: products of section-divisors
  being divisors (finite/flat/lfp of ∏ᵢ ker) and degree-additivity both genuinely
  consume 1.2.3/AG-LB; state them as TWO hypothesis-guarded register boxes
  ([IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π) — true statements, KM-cited,
  discharge = T-D1 once AG-LB lands), then `sectionsDivisor` total via classical
  dite: real branch ⟨∏ᵢ (P i).1.ker, boxes⟩; junk branch ⟨⊤, empty-subscheme props⟩
  (⊤-support is ⊥ ⟹ subscheme empty ⟹ IsClosedImmersion-of-IsEmpty instance chain;
  check an open-immersion-of-empty instance for flat/lfp, else small vacuous lemmas).
  `sectionsDivisor_degree` follows from box-2 + sectionDivisor_degree + Fin-sum. · **File**: CartierDivisor.lean · `sectionsDivisor`,
  `sectionsDivisor_degree` · **Depends on**: none · **Parallel**: yes ·
  **Type**: def(data) + theorem
- **Sketch**: section ⟹ closed immersion (π separated) ⟹ ideal sheaf via
  `Scheme.Hom.image`/IdealSheafData; product of finitely many ideal sheaves
  (add `IdealSheafData.mul` — small mathlib-shaped API, upstream candidate); finite
  locally free of degree n: locally, quotient by product of n "linear" ideals in a
  smooth relative curve — degree additivity via CRT off the diagonal + filtration on
  the diagonal (KM 1.1–1.2, preview in hand for quotes).
- **Sources**: [KM] 1.2.2 + 1.1 (in hand). **Generality**: smooth separated rel. curve.

### [T-D5] Exact order N ⟹ NP = 0 (KM 1.4.2; BB-DELIGNE)
- **Status**: done-modulo-registered-box (beastmode-A 2026-07-08T10:00Z →
  2026-07-08T11:00Z — `HasExactOrder.smul_eq_zero` DERIVED sorry-free from the box
  `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (BB-DELIGNE stated in the
  project's subgroup-divisor encoding, exactly as this ticket designed). Real
  content proved: P factors through the order divisor — new
  `IdealSheafData.idealMonoidHom` (ideal-of-product = product-of-ideals via
  map_prod; upstream-shaped), Ideal.prod_le_inf + Finset.inf_le at the a = 0
  factor, `(0+1) • P = P` by simp, then `P.1.toImage ≫ inclusion hle` with
  inclusion_subschemeι + toImage_imageι. Degree input = T-D3's
  sectionsDivisor_degree (hypotheses discharged by E.proper→IsSeparated + E.smooth).
  LEAN GOTCHA: `rw [← h0]` (h0 : (0+1)•P = P) rewrites EVERY P including inside the
  ∏-binder — nested-smul junk; rewrite FORWARD in the hypothesis (`rw [h0] at hle0`)
  instead — binder-bound occurrences don't match, so only the intended RHS moves.) ·
  **File**: ExactOrder.lean · `HasExactOrder.smul_eq_zero` ·
  **Depends on**: T-D3 · **Type**: theorem · **Sources**: [KM] 1.4.2 (IN HAND,
  verbatim in decomposition); black box BB-DELIGNE stated as its own lemma first.

### [T-D6] KM 1.4.4 (1)⇔(3): Drinfeld = naive when N invertible
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-09T04:00Z —
  `hasExactOrder_iff_geometric` DERIVED sorry-free from two register boxes stated
  with verbatim KM 1.4.4 quotes: `HasExactOrder.pull_nsmul_ne_zero` (T-D6b,
  (2)⟹(3) at a geometric point — fibre étale rank-N distinctness) and
  `hasExactOrder_of_geometric` (T-D6c, (3)⟹(1) via the (4)-discriminant route).
  FREE content proved: `Point.pull_zsmul` + `Point.pull_zero` (pull is compatible
  with ℤ-smul because both sides are `≫ [a]` via point_smul_eq_comp_mulBy — no
  cross-curve group-compat needed on the SAME curve); the killing conjunct comes
  from hkill through them. Box discharge consumes the T-D6a machinery
  (comap_mul ✓, ker_sectionBaseChange ✓, isPullback_sectionBaseChange ✓ — all
  proven) + fibre étale/discriminant theory (T-D7-bridge-adjacent).) · **File**: ExactOrder.lean · `hasExactOrder_iff_geometric` ·
  **Depends on**: T-D3, T-B4 · **Parallel**: with T-D7 · **Type**: theorem
- **FULL 1.4.4 QUOTE MINED (2026-07-08T11:30Z, printed pp. 18–19)** — statement (1)-(5)
  + proof structure: (1)⟹(2) "the property of having 'exact order N' is preserved
  under arbitrary changes of base T → S" [needs divisor-formation + IsSubgroup
  base-change compat = T-D12-family]; (2)⟹(3) over k: G := the rank-N
  subgroup-scheme; N invertible in k ⟹ "G is automatically finite etale over k of
  rank N. Therefore as a Cartier divisor in C_k, G consists of a uniquely determined
  set of N distinct points. The equality of Cartier divisors G = Σ [aP_k] shows the
  N points all distinct"; (3)⟺(4) D is finite locally free of rank N; "finite etale
  over S if and only if its discriminant (determinant of the matrix tr(eᵢeⱼ)…) is
  invertible on S. This holds if and only if for all geometric points the Cartier
  divisor D_k is finite etale over k, i.e. iff (3)"; (3)⟺(5) ℤ/N → C factors
  through D, iso-check at geometric points. SUB-TICKET DECOMPOSITION when executed
  (one conclusion each, per statement-splitting): T-D6a exact-order base-change
  ((1)⟹(2)); T-D6b field-case distinctness ((2)⟹(3): subgroup-divisor over a field
  with N invertible has N distinct points); T-D6c étale-discriminant bridge
  ((3)⟺(4), consumes T-B4-rank + a trace-form/discriminant input — check mathlib
  `Algebra.discr` + finite-étale-iff-unramified-fibrewise before boxing).
  T-D6a-INFRA COMPLETE (2026-07-09T07:00Z): ALL CartierDivisor-side base-change
  infrastructure PROVED sorry-free — `isPullback_sectionBaseChange` (section
  base-change square cartesian, limit-cone construction), `ker_sectionBaseChange`
  (ker of pulled section = comap of ker), `baseChange_ideal` (base-changed divisor
  ideal = D.ideal.comap fst, via pullbackSymmetry + ker_fst_of_isClosedImmersion +
  ker_subschemeι), `comap_mul`/`comap_prod` (T-D6a-i, done). ALSO `Point.pull_zsmul`
  + `Point.pull_zero` (ExactOrder). NOTE: T-D6 (the headline (1)⇔(3)) was ultimately
  DERIVED via the T-D6b/T-D6c fibre-étale boxes WITHOUT needing the full
  orderDivisor-base-change naturality — so the remaining assembly (L3: identify
  `(orderDivisor P N).baseChange t` with `orderDivisor (pull P) N` across the
  `E.baseChange t` frame; L4: IsSubgroup transport) is now a STANDALONE naturality
  ticket, spawned as T-D6a-ii, gated on the single missing compat
  `(E.baseChange t).mulByHom n` vs pullback of `E.mulByHom n` (grpObjMkPullbackSnd
  functoriality, T-A6-adjacent group-law plumbing). Not blocking any current result.
  ---
  T-D6a-PROGRESS (2026-07-08T12:30Z): `RelEffCartierDiv.baseChange` Prop-fields
  DISCHARGED sorry-free (paste_vert of the two of_hasPullback squares +
  MorphismProperty.of_isPullback [slots: sq : IsPullback f' g' g f transfers P g →
  P g'] + toImage-transport + cancel_left_of_respectsIso-as-term [rw fails: metavar
  pattern P (f ≫ g)]). NEXT: formation-compat needs `IdealSheafData.comap_mul`
  (missing from mathlib — comap I f := (pullback.fst f I.subschemeι).ker,
  Functorial.lean:39, has map_gc lattice facts only; extension IS multiplicative,
  glue Ideal.map_mul affine-locally) + comap-of-section-ker = ker-of-pulled-section
  + IsSubgroup pullback-transport.
- **Sketch**: KM's proof IN HAND (preview pp. 18–19): (1)⟹(2) base change; (2)⟹(3)
  rank-N étale subgroup over field has N distinct points; (3)⟹(1) via (4). Attack
  obligation from decomposition D5 (killed-by-N hypothesis placement) must be resolved
  first — if the skeleton form is inequivalent, B2-report (do NOT silently edit).
  **RESOLVED 2026-07-06 (v5)**: the adversarial pass added the standing hypothesis
  `hkill : (N : ℤ) • P = 0` to the skeleton (ExactOrder.lean:85, docstring records the
  `ℚ̄[ε]` counterexample); same for T-D7 (line 96). Both are workable as stated.
- **Sources**: [KM] 1.4.4 with proof (IN HAND).

### [T-D6a-i] ForMathlib: `IdealSheafData.comap_mul` (formation-compat linchpin)
- **Status**: done (beastmode-A 2026-07-08T18:00Z → 2026-07-09T02:00Z —
  `IdealSheafData.comap_mul` PROVED sorry-free for ARBITRARY schemes (axioms
  standard; full build green). Structure: (1) `comap_ideal_top_of_isAffine` —
  TENSOR-FREE affine core (competitor cone Spec(Γ(X)/extension) +
  IsClosedImmersion.lift + u ≫ fst = ιX reads the kernel off; ΓSpecIso_naturality
  value-chases with the isoSpec round-trip `hround` at the CommRingCat.of-eta
  spelling); (2) `comap_mul_of_isAffine` via equivOfIsAffine + Ideal.map_mul
  (+Pi.mul_apply); (3) `comap_comap_ι_ideal_top` (resLE ⊤-value formula, pure
  comap_comp + resLE_comp_ι rewriting); (4) global glue: isBasis_affineOpens cover
  {U ≤ f⁻¹V} + ext_of_iSup_eq_top; per-U chain map_ideal ∘ OI-formula(+comap_symm as
  term-trans) ∘ resLE-formula ∘ OI-formula-on-Y, multiplicative layerwise by
  Ideal.map_mul. LEAN GOTCHAS BANKED: (a) `.toRingHom` instead of `(e : _ →+* _)`
  coe-holes flips elaboration so the equiv's ⊤-spelling wins over the ideal's
  ↑⟨⊤,_⟩-coe — resolves the FunLike mismatch; (b) `Ideal.map_of_equiv`'s ↑-coe
  pattern never rw-matches toRingHom-terms — consume it as a defeq `Eq.trans` term;
  (c) rw the goal-RHS ideal_mul BEFORE the hchain rewrites (comap-of-product doesn't
  match the (A*B).ideal pattern, so order is safe).) 
- **New file**: ForMathlib/IdealSheafComapMul.lean ·
  `Scheme.IdealSheafData.comap_mul : (I * J).comap f = I.comap f * J.comap f` ·
  **Depends on**: none · **Type**: theorem (upstream candidate)
- **BANKED DESIGN (2026-07-08T13:30Z)**: comap K f := (pullback.fst f K.subschemeι).ker
  (Functorial.lean:39); GC `map_gc : GaloisConnection (comap · f) (map · f)` with
  le_map_comap/comap_map_le. (≤-half) comap (I*J) f ≤ comap I f * comap J f via
  GC l_le needs MAP-SUPERMULTIPLICATIVITY map K₁ f * map K₂ f ≤ map (K₁K₂) f —
  pointwise via ker: elements a·b with a ∈ ker((K₁ι ≫ f).app U): CAUTION the
  composite app passes through NON-affine opens f⁻¹U; route instead through
  `Hom.le_ker_iff/le_ofIdeals_iff` (Basic:125) + `ker_subschemeι` pointwise
  ((K₁K₂).ideal V ≤ RingHom.ker ((K₁K₂)ι.app V) via ideal_ker_le). (≥-half = the
  TENSOR half) comap I f * comap J f ≤ comap (I*J) f: affine-locally the pullback
  piece ring is B ⊗_A A/K with kernel of B → B ⊗_A A/K equal to K.map(algebraMap)
  — identification `Algebra.TensorProduct.quotIdealMapEquivTensorQuot (B) (I) :
  B ⧸ I.map (algebraMap A B) ≃ₐ B ⊗[A] (A ⧸ I)` (RingTheory.TensorProduct.Quotient
  ✓ exists) — then Ideal.map-multiplicativity `Ideal.map_mul` closes; the
  cover-reduction glue mirrors `ker_ideal_of_isPullback_of_isOpenImmersion`
  (IdealSheaf/Basic.lean:823) + `Hom.ker_apply` [QuasiCompact fst ✓ instance] +
  pullbackSpecIso-app computation. SANITY BANKED: the naive scheme-level shortcut
  fails — the comparison q : pullback f Iι ⟶ pullback f (I*J)ι via
  pullback.map (𝟙) (inclusion (mul_le_left)) only reproves monotonicity
  (comap (I*J) ≤ comap I); the tensor half is genuinely local.
- **Sources**: Stacks 01R5-area (scheme-theoretic preimage) · mathlib
  RingTheory/TensorProduct/Quotient.
- **ROUTE REFINED (2026-07-08T18:30Z, two mathlib simplifiers found)**:
  (i) `IdealSheafData.equivOfIsAffine : IdealSheafData X ≃+*o Ideal Γ(X,⊤)` (Basic:487)
  is a RING-equiv over affines — so affine comap_mul ⟺ top-VALUE multiplicativity with
  the mul-bookkeeping free; (ii) `ker_of_isAffine (f) [IsAffine Y] : f.ker =
  ofIdealTop (RingHom.ker f.appTop.hom)` (Basic:750) — comap's value needs only
  [IsAffine X], no QuasiCompact/ker_apply dance. AFFINE CORE now: identify
  RingHom.ker ((pullback.fst f Iι).appTop) with (I⊤).map f.appTop: transport the
  pullback square to Spec-side (X.isoSpec, subschemeObjIso for Iι at affine Y),
  where fst becomes Spec.map (Quotient.mk of the extension) via
  `isPullback_SpecMap_of_isPushout` + the quotient pushout square (build by
  `Algebra.IsPushout.of_equiv` along `quotIdealMapEquivTensorQuot` — SAME pattern as
  T-A5a's isPushout_sChart); then Ideal.mk_ker. Conjugation bookkeeping via
  `Hom.ker_comp_of_isIso` (pre-isos) + `map_ker : f.ker.map g = (f ≫ g).ker`
  (post-isos) + ofIdealTop-map-transport. Globalisation:
  `IdealSheafData.ext_of_iSup_eq_top` (Basic:269) over affine covers refined into
  Y-affines + a comap-restriction compat lemma (mirror
  `ideal_comap_of_isOpenImmersion`, Functorial:199). File started:
  ForMathlib/IdealSheafComapMul.lean (skeleton compiles, core sorried).
- **AFFINE CASE DONE (2026-07-08T21:00Z)**: `comap_ideal_top_of_isAffine` +
  `comap_mul_of_isAffine` PROVED sorry-free (axioms standard) — and TENSOR-FREE:
  instead of computing Γ(pullback), map the competitor `Spec (Γ(X)/extension)` into
  the pullback by `pullback.lift ιX (IsClosedImmersion.lift Iι (ιX ≫ f) hle)` and
  read `ker fst.appTop ≤ extension` off `u ≫ fst = ιX`; the two value chases close
  by `ΓSpecIso_naturality`-at-the-element + the isoSpec round-trip `hround` (state
  hround at the `CommRingCat.of ↑Γ(X,⊤)` spelling to match ofHom-mk's naturality —
  the eta-spelling mismatch otherwise blocks rw). Cheap half: pullback.condition
  appTop-chase + `subschemeι_app` consumed via congrArg-value terms.
  `Pi.mul_apply` needed after `ideal_mul`. REMAINING: globalisation
  (`ext_of_iSup_eq_top` over an affine cover of X refined into Y-affines + a
  comap-restriction lemma), then `comap_mul` general, then back to T-D6a
  (section-ker-compat is FREE via `ker_fst_of_isClosedImmersion`).

### [T-D6a-ii] orderDivisor base-change naturality (standalone; gated on mulBy compat)
- **Status**: in_progress — CORE COMPAT DONE (beastmode-A 2026-07-09T08:30Z:
  `mulBy_baseChange` PROVED — `(E.baseChange g).mulBy n = (Over.pullback g).map
  (E.mulBy n)`, via the NEW ForMathlib lemma `Functor.map_zpow'` (zpow companion of
  mathlib `Functor.map_inv'`; the `open scoped CategoryTheory.Obj` inside it resolves
  `GrpObj (F.obj G)`, dissolving the `Hom.group` diamond that blocked 6 direct
  attempts). REMAINING: (ii) `mulByHom_baseChange` at `.left` = a pullback.map
  (take `.left` of the above + Over.pullback-map-left formula); (iii) L3 assembly:
  `(orderDivisor P N).baseChange t . ideal = (orderDivisor-of-pulled-sections).ideal`
  via baseChange_ideal + comap_prod + ker_sectionBaseChange + Point.pull_zsmul; (iv) L4
  IsSubgroup transport via comapIso. Non-blocking; resume when convenient.). NOT
  blocking T-D6/D7/D8/D9. All CartierDivisor infrastructure proven
  (baseChange_ideal, ker_sectionBaseChange, comap_mul/comap_prod).
- **File**: EllipticCurve/GroupLaw.lean (compat) + LevelStructure/ExactOrder.lean
  (assembly) · **Depends on**: T-A5c (done) · **Type**: lemma
- **Sketch**: (i) `mulByHom_baseChange`: `(E.baseChange t).mulByHom n` = the pullback
  map of `E.mulByHom n` over `t` — from `grpObjMkPullbackSnd` being
  `(Over.pullback g).mapGrp`-functorial, so `[n]` (an n-th power in the hom-group)
  commutes with the monoidal functor `Over.pullback`; concretely
  `(E.baseChange t).mulBy n = (Over.pullback t).map (E.mulBy n)` at `.left`. (ii) then
  `Point.pull (a•P) = a • Point.pull P` already gives the section identification;
  combine with `baseChange_ideal` + `comap_prod` + `ker_sectionBaseChange` to get
  `(orderDivisor P N).baseChange t . ideal = (orderDivisor (E.baseChange t)
  (pull-sections) N).ideal`. (iii) L4: IsSubgroup transports along `comapIso`
  (points of the base-changed subscheme ↔ points factoring through the pullback).
- **Sources**: [KM] 1.4.4 (1)⟹(2) base-change preservation; mathlib
  Cartesian/Over.lean mapGrp functoriality.

### [T-D7] KM 1.4.4 (1)⇔(4): étale-divisor criterion
- **Status**: done-modulo-registered-box (beastmode-A 2026-07-09T04:30Z —
  `hasExactOrder_iff_etale` DERIVED from T-D6 + the `orderDivisor_etale_iff_geometric`
  box (T-D7-bridge, (3)⟺(4) discriminant argument, verbatim KM quote in docstring);
  the iff-plumbing collapses the killing conjunct via pull_zsmul + hkill.) · **File**: ExactOrder.lean · `hasExactOrder_iff_etale` ·
  **Depends on**: T-D3 · **Parallel**: with T-D6 · **Type**: theorem ·
  **Sources**: [KM] 1.4.4 (IN HAND; discriminant argument quoted in proof).

### [T-D8] ⧗KM Γ(N): Drinfeld ⟺ naive (N invertible)
- **Status**: done-modulo-registered-box (beastmode-A 2026-07-09T05:30Z —
  `isFullLevel_iff_naive` DERIVED sorry-free from the single register box
  `fullLevel_divisor_iff_naive_gen` (T-D8-bridge, verbatim KM 3.7 / 1.4.4-for-Γ(N)
  content: divisor Σ_{(a,b)}[aP+bQ] = E[N] ⟺ fibrewise P,Q generate the N-torsion).
  Box discharge route recorded in-docstring: T-D2's `isFullSetOfSectionsAlg_iff_fields`
  (PROVED reduced-base criterion) glued to T-B6's fibre comparison E[N]_{k̄}≅(ℤ/N)²
  (stream-B). The killing clauses are shared structurally, so the iff-plumbing is
  free.) · **File**: LevelStructure/Basic.lean · `isFullLevel_iff_naive` ·
  **Depends on**: T-D6 (done-mod-box), T-B4 (done-mod-box), T-B6 (stream-B) ·
  **Type**: theorem · **Sources**: [KM] 3.1 + 3.7 ⧗; [Loe] Fact 3.8.1 (naive side, in hand).

### [T-D9] Γ₁(N): Drinfeld ⟺ naive (restatement of T-D6)
- **Status**: done (beastmode-A 2026-07-09T05:00Z — PROVED first-try, sorry-free in
  itself: forward direction gets the killing clause from T-D5's
  HasExactOrder.smul_eq_zero (BB-DELIGNE consumer), then T-D6's iff both ways.
  Transitively rests on the D5/D6 register boxes.) · **File**: LevelStructure/Basic.lean · `isGammaOne_iff_naive` ·
  **Depends on**: T-D6 · **Type**: theorem (thin wrapper — golf target).

### [T-D10] ⧗KM Γ₀(N): literal fppf-local cyclicity
- **Status**: quote-gate-satisfied, DESIGN-DECISION-GATED (beastmode-A 2026-07-09T10:00Z
  mined KM 3.4/3.7, printed pp. 105-106). VERBATIM (KM 3.7.1 proof, p.105): *"the
  notion of cyclicity is by definition local for the f.p.p.f. topology, so a fortiori
  for the etale topology"*; *"our constant group-scheme K is cyclic in the sense of
  f.p.p.f.-locally admitting a generator if and only if the abstract group K(T) is a
  cyclic group of order N"*. So Γ₀(N)-structure (KM 1.4.1) = a rank-N subgroup divisor
  `G ⊆ E` that fppf-LOCALLY on `S` admits a generating section of exact order `N`
  (`Σ_{a} [aP₀] = G`). CURRENT `IsGammaZero` uses the geometric-fibre (algebraically-
  closed-point) surrogate of this. DESIGN DECISION NEEDED (owner): mathlib has fppf
  DESCENT (`AlgebraicGeometry/Morphisms/FlatDescent.lean`, `Sites/Fpqc.lean`) but NO
  clean "fppf-cover-admitting-a-generator" vocabulary — the literal form needs either
  (a) a `∃ (S' ⟶ S) faithfully-flat lfp surjective, ∃ generator over S'` predicate
  built on `@Surjective ⊓ @Flat` + `LocallyOfFinitePresentation` (all present as
  MorphismProperties), or (b) a Sites-based sheafification. RECOMMEND (a): define
  `IsGammaZeroFppf N G := ∃ (T : Scheme) (h : T ⟶ S), Surjective h ∧ Flat h ∧
  LocallyOfFinitePresentation h ∧ ∃ P₀ : (E.baseChange h).Section, P₀.HasExactOrder N ∧
  (P₀.orderDivisor N).ideal = (G.baseChange h).ideal`, then state
  `isGammaZero_iff_fppf : IsGammaZero N G ↔ IsGammaZeroFppf N G` (⟸ by geometric-point
  descent of the generator; ⟹ needs KM 3.7.1's étale-descent representability — ⧗-gated
  proof, but the STATEMENT is addable now). NOT started in code pending the owner's
  (a)-vs-(b) call — this is a genuine API-design fork, not a proof gap. · **File**: LevelStructure/Basic.lean ·
  **Depends on**: T-D3; fppf vocabulary · **Type**: def + equivalence statement ·
  **Sources**: [KM] 1.4.1 cyclic (IN HAND) + 3.4/3.7.1 (NOW IN HAND, quotes banked) + 6.1 ⧗.

### [T-E3] Ell/R category plumbing (Prop sorries)
- **Status**: done (beastmode-A 2026-07-08T14:00Z → 2026-07-08T15:30Z — ALL fields
  sorry-free: id-square `IsPullback.of_horiz_isIso ⟨by simp⟩`; comp-square
  `f.isPullback.paste_horiz g.isPullback`; category laws `intros; ext <;> simp`;
  `pullbackAlongMap.isPullback` via `IsPullback.of_right` after rewriting the big
  square's fst-composite (`rw [← hfst] at hbig` — rewriting INSIDE an IsPullback
  index works fine at hypotheses); `zero_w` needs the FULL raw `show`-recast of the
  goal (both zero-fields respelled as pullback.lifts — proof args arbitrary) because
  the record-projection typing poisons every kabstract. LEAN GOTCHA BANKED:
  `pullback.map ≫ pullback.fst/snd` NEVER simp-reduces (abbrev-unfold does not
  happen in simp matching) and `pullback.lift ≫ fst` can ALSO fail under simp in
  Scheme-category goals — collapse with explicit `pullback.lift_fst/snd` show-terms
  and finish with `lift_fst_assoc` + `Category.comp_id`-terms.) · **File**: Moduli/EllCategory.lean · category instance fields,
  `pullbackAlongMap.isPullback/zero_w` · **Depends on**: none · **Parallel**: yes ·
  **Type**: lemmas · **Sketch**: `IsPullback.of_id_fst`-style + `IsPullback.paste_horiz`
  (find exact names); EllHom ext-lemma discipline.

### [T-E4] Moduli-problem functor laws (Prop sorries)
- **Status**: done-modulo-E4a-gate (beastmode-A 2026-07-08T15:30Z →
  2026-07-08T17:00Z — the FOUR functor-law sorries (map_id/map_comp ×2 functors)
  PROVED sorry-free via new `EllHom.pullSection_id` + `EllHom.pullSection_comp`
  (IsPullback.hom_ext with the lift-legs stated as defeq HAVES — a raw
  `rw [IsPullback.lift_fst]` never matches under the Subtype-coe; laws close by
  `congrArg Subtype.val` at the depth `ext` reaches). The two map-MEMBERSHIP sorries
  remain: they are T-E4a-gated by design (pullSection additivity consumes the
  canonicity chain / abelEnrichment_unique per the file's adversarial note; the
  killing clause + fibre-smul clauses all route through mulByHom-compat across the
  cartesian square). They discharge when T-E4a does.) · **File**: Moduli/Representability.lean · `gammaOneNaiveProblem`
  and `gammaFullNaiveProblem` `map_id/map_comp/map`-membership sorries ·
  **Depends on**: T-E3 · **Type**: lemmas.

### [T-E5] ⧗KM + AG-QUOT: representable ⟺ rel. representable + rigid (KM 4.7)
- **Status**: open · **File**: Moduli/EllCategory.lean · `representable_iff` ·
  **Depends on**: AG-QUOT (Loeffler 3.6.1, quote in hand), naive-Γ(3)/Legendre
  bootstrap objects (sub-tickets at cut time), T-E4 · **Type**: theorem (hard) ·
  **Sources**: [Loe] 3.7.4 + proof sketch (in hand); [KM] 4.7 ⧗.

### [T-E7] Y₁(N) representable + smooth affine (N ≥ 4, N invertible) · MILESTONE
- **Status**: open · **File**: Moduli/Representability.lean ·
  `gammaOneNaive_representable` · **Depends on**: T-E1, T-E2, T-D6, T-B5, T-E4 ·
  **Type**: theorem ·
  **Sketch**: Loeffler §3.3.6 explicit construction (universal Tate curve; cut out
  order-exactly-N locus via division polynomials; remove lower-order loci; invert N)
  + Thm 3.4.4 smoothness (formal criterion via `[N]` étale — proof sketch in hand).
- **Sources**: [Loe] Def 3.3.6 + Thm 3.4.4 (verbatim in decomposition).

### [T-E8] Stack packaging (pseudofunctor + IsStack statement)
- **Status**: open · **File**: Moduli/Stack.lean (extend) · **Depends on**: T-E3 ·
  **Type**: def + statement · **Sketch**: `S ↦ groupoid of (E/S)` pseudofunctor;
  state `Pseudofunctor.IsStack fppfTopology`; proof = T-E10 + separatedness (sorried
  until BB-DESC route chosen). *Bridge artifact — not load-bearing (plan D3).*

### [T-E9] ⧗KM Y(N) rigid + representable (N ≥ 3) · MILESTONE
- **Status**: open · **File**: Moduli/Representability.lean ·
  `gammaFullNaive_representable` · **Depends on**: T-E5 *or* explicit route via
  T-E7-style construction; T-C1 (Weil-pairing open locus per Loeffler 3.8.2); T-D8 ·
  **Type**: theorem · **Sources**: [Loe] 3.8.2/3.8.3 (in hand); [KM] 5.1 ⧗.

### [T-E10] fppf descent for elliptic curves (BB-DESC consumer)
- **Status**: open · **File**: Moduli/Stack.lean · `ellipticCurve_fppf_descent` ·
  **Depends on**: T-A5 · **Type**: theorem · **Sources**: SGA 1 VIII (black box
  statement first as its own lemma); [KM] 4.1 ⧗ context.

### [T-E11] fppf separatedness of relatively representable problems
- **Status**: open · **File**: Moduli/Stack.lean · `moduliProblem_fppf_separated` ·
  **Depends on**: T-E3 · **Type**: theorem (direct from rel. representability +
  fppf-surjectivity ⟹ epi on points — check mathlib `Surjective` API).

### [T-F0] Roots-of-unity count in ℚ̄
- **Status**: done (beastmode-B, 2026-07-06 — sorry-free + axiom-clean, first-try
  modulo one missing import: root of `Polynomial.cyclotomic N ℚ̄` exists
  (IsAlgClosed.exists_root, degree = totient ≠ 0), is primitive
  (isRoot_cyclotomic_iff, NeZero (N:ℚ̄) from CharZero), then
  IsPrimitiveRoot.card_rootsOfUnity; added import
  Mathlib.RingTheory.Polynomial.Cyclotomic.Roots. modularCyclotomicCharacter's
  input hypothesis in GaloisRepData is now REAL.) ·
  **Claimed**: beastmode-B, 2026-07-06 (G6 pick: dep-free,
  parallel-safe, disjoint file; T-D7 deliberately NOT taken — its (3)⟺(4) bridge
  shares the base-change ideal machinery D2 is actively building in
  ForMathlib/IdealSheafComapMul.lean for T-D6a, and duplicating that is the cardinal
  sin; revisit T-D7 when T-D6a lands) · **File**: ModularCurve/YRho.lean · `card_rootsOfUnity_algClosureQ`
  · **Depends on**: none · **Parallel**: yes · **Type**: lemma ·
  **Sketch**: `Xᴺ − 1` separable in char 0 + alg. closed ⟹ N distinct roots; mathlib
  `IsPrimitiveRoot`/`Polynomial.nthRoots` card lemmas (search first — likely nearly
  present).

### [AG-GG] Grothendieck–Galois for ℚ: SCOPING DONE (beastmode-B, 2026-07-06)
Mathlib 2026 has ALL the abstract machinery; the "scary lemma" (Loeffler §3.6 étale
descent) reduces to instance work. Inventory: `CommAlgCat.FiniteEtale R` + fiber
functor `S ↦ (S →ₐ[R] Ω)` + `FiniteEtale.equivOfIsSepClosed` (RingTheory/Etale/
Finite.lean, Merten 2026 — the object-level fibre statement is my T-B6d);
`CategoryTheory/Galois/*`: `GaloisCategory` + `Equivalence.lean` ("any fiber functor
induces an equivalence with finite continuous `Aut F`-sets") +
`IsFundamentalgroup.lean` (`IsFundamentalGroup G F ⇒ toAutMulEquiv : G ≃* Aut F`,
homeo). MISSING (the sub-development, one leaf each, single-conclusion):
- **[AG-GG-1]** `PreGaloisCategory ((CommAlgCat.FiniteEtale k)ᵒᵖ)` — claimed
  beastmode-B 2026-07-06; NEW FILE ForMathlib/FiniteEtaleGalois.lean (mathlib-only
  imports; general field k). Leaf tree (Lenstra G1–G3 via op-duality, ambient =
  CommAlgCat k with (co)limits transported along `commAlgCatEquivUnder` +
  Under CommRingCat; subcategory closure via
  `ObjectProperty.IsClosedUnderLimitsOfShape` + `Algebra.Etale.of_equiv`):
  - AG-GG-1.0 ambient instances: HasFiniteProducts/HasPushouts/HasInitial (+
    SingleObj-G limits) for CommAlgCat k, via the Under-equivalence.
  - AG-GG-1.1 closure under finite products (Etale-Pi instance ✓ in mathlib;
    concrete product cones in CommAlgCat).
  - AG-GG-1.2 closure under pushouts B ⊗[A] C (needs the 2-out-of-3
    `A → B étale when k → A, k → B étale` — formal-lifting leaf if mathlib lacks
    it — then base-change + comp instances ✓ mathlib).
  - AG-GG-1.3 trivial closures: k initial ✓ (Etale R R), zero ring étale
    (empty product).
  - AG-GG-1.4 fixed points `A^G` finite étale, G finite (via NEW leaf: a
    k-subalgebra of a finite étale k-algebra is finite étale — reduced artinian +
    factor-embedding separability; mathlib-grade) + SingleObj-limit identification.
  - AG-GG-1.5 G3 splitting: mono-in-op ⇒ direct summand (idempotent splitting of
    epis between finite étale algebras over a field).
  Duplication watch: NOTHING imports RingTheory/Etale/Finite.lean yet; Merten's
  series is visibly heading here — re-check at each mathlib bump, swap ours out
  if mathlib lands it.
- **[AG-GG-2]** `FiberFunctor` instance for the `AlgebraicClosure ℚ`-points functor
  on that opposite category (fiber exactness; sep-closed case anchors it).
- **[AG-GG-3]** `IsFundamentalGroup GalQ F` (Krull topology, continuity +
  transitivity axioms — classical infinite Galois theory, mathlib-supported).
- **[AG-GG-4]** assemble `(FiniteEtale ℚ)ᵒᵖ ≌ ContAction FintypeCat GalQ`; Spec-side
  dictionary (finite ⇒ affine ⇒ Spec of the algebra IS the finite étale ℚ-scheme).
Then T-F1: `V_ρ := Spec` of the algebra attached to the `ContAction` `(ℤ/N)²`-via-ρ;
T-F1a/b specs = the equivalence's naturality; T-F1c group structure = group objects
transported along the equivalence (GrpObj/ofRepresentableBy — T-B2 experience
directly applicable). All leaves unclaimed.

### [T-F1] ⧗(AG-GG) V_ρ construction (DS5 discharge)
- **Status**: open (scoping first: AG-GG sub-development) · **File**: YRho.lean ·
  `vRho`, `vRhoπ`, `vRhoPointsEquiv` + specs T-F1a/b (+ group structure T-F1c) ·
  **Type**: def(data) + theorems ·
  **Sketch**: splitting field `L` of ρ (finite Galois); descent datum on the constant
  scheme `(ℤ/N)²_L` twisted by ρ; affine Galois descent = `Spec` of invariants
  (AG-QUOT-adjacent); étale-ness from `L/ℚ` étale. Loeffler §3.6's "scary lemma
  (étale descent of morphisms)" quote anchors the mechanism.

### [T-F3] ρ-level structure: scheme-level compat (discharges DS5d)
- **Status**: open · **File**: YRho.lean · unfold `PairingCompatAt` via `Γ–Spec` iso;
  upgrade `coords_additive`/`pairing_compat` to morphism-level once T-F1c lands ·
  **Depends on**: T-F1, T-C4 · **Type**: def + theorems.

### [T-F6] Symplectic Isom-scheme: ρ-level relative representability (v2, review Q9)
- **Status**: open · **File**: YRho.lean · `rhoLevel_relativelyRepresentable` ·
  **Depends on**: T-F1, T-C0 (pairing over char 0), T-B5 · **Type**: theorem ·
  **Sketch**: `Isom^symp(E[N], V_ρ̄)` as an open-closed piece of the finite étale
  `Isom(E[N], V_ρ̄)`-scheme (pairing condition cuts by det); finite étale over `T`.

### [T-F4] ⧗ Y(ρ̄_N) representable (phase-3 headline) · MILESTONE
- **Status**: open (phase 3) · **File**: YRho.lean · `yRho_representable` ·
  **Depends on**: T-E9, T-F1, T-F3, **T-F6 (route of record, v2)** · **Type**: theorem ·
  **Sources**: [Buz-L8] p. 33 (verbatim in decomposition). v2 route: Isom-scheme over a
  rigidified full-level base carries the moduli interpretation by construction; the
  Galois-twist identification is a separate later comparison theorem (D8).

### [T-F5] Geometric irreducibility (BB-IRR)
- **Status**: open (phase 3; black box acceptable indefinitely per owner) ·
  **File**: YRho.lean · `yRho_geometricallyIrreducible` · **Depends on**: T-F4 ·
  **Sources**: [Buz-L8] pp. 33–34 ("Proof: See 1980s.").

---

## Cleanup cadence (algorithmic; every cleanup ALSO enforces: no `set_option
maxHeartbeats` anywhere; DS-register unchanged; `#print axioms` audit)

- **[CLEANUP-1]** after T-A2+T-A3+T-A4 → `/cleanup` WeierstrassModel.lean (deps: those)
- **[CLEANUP-2]** after T-A5 (final per-file, Basic.lean; +T-A6d touches GroupLaw —
  final GroupLaw cleanup folds in after T-A6 chain) (deps: T-A5, T-A6)
- **[CLEANUP-3]** after T-B3+T-B4+T-B5 → Torsion.lean (deps: those)
- **[CLEANUP-4]** final per-file MuN.lean (deps: T-B2) — includes `ULift` review in
  `muNRing` · **Claimed**: beastmode-B, 2026-07-06T11:55Z (in_progress; deps T-B2 ✓
  T-B7 ✓ both done, file sorry-free; running while the A-lane WIP blocks the
  Torsion import chain)
  · **Progress** (2026-07-06): Phases 0–3 done (baseline green 2877 jobs/0 warn;
  punch-list ~50 items; 4 subsection dividers folded into module docstring,
  commit 4b7d8615). Phase 4 per-decl workers 7/74 done, all gates pass:
  muNRing/muNAbs/muN/muNπ (clean, no edits; flagged big-changes: AdjoinRoot
  respelling, ULift-on-coefficients, CanonicallyOverClass/↘ migration, Diag(M)),
  constScheme+constSchemeπ (`@[reducible] def`→`abbrev`, green; NOTE constScheme
  hunk was swept into stream-A commit 50c86595 by a sibling `git add -A` —
  content correct, attribution wrong, no history fix in shared worktree),
  muNRingGen (private docstring stripped). Phase-5a queue so far: [Finite A]
  drop (+2 omit fixes), A : Type universe question — both deferred big-change.
  · **Plugin 0.55.0 incorporated** (2026-07-06): statement-splitting.md is
  reference doc #8 for remaining workers; item 12 STRUCTURE now enforces
  one-conclusion-per-declaration (∧-chain → part-lemmas + one-line ⟨…⟩ assembly;
  exceptions: shared-witness ∃, mutual-induction bundles, single Iff);
  isPullback_muN_baseChange (shared-witness ∃, constructible witness) queued for
  def+spec-lemma extraction per the preference order. Beastmode Tier A5: future
  sub-tickets born single-conclusion.
  · **PAUSED 2026-07-06 (user request: resume proving).** State at pause: Phase 4
  workers 9/74 done (through muNRing_hom_ext; all gates pass; edits so far:
  constScheme/constSchemeπ→abbrev, muNRingGen+muNRing_hom_ext docstring strips,
  hom_ext golf 14→8 lines, muNRingGen_pow change+simp form). Rename queue (1):
  muNRingGen_pow→muNRingGen_pow_eq_one. Phase-5a queue: [NeZero N] drop on
  muNPointsEquiv/_natural (runLinter-backed); constScheme [Finite A] drop + 2
  omit-fixes; muN_poly_monic→muNModelPoly_monic generalize+dedup with
  muNStdPair.monic_f; pullback-lift-transfer motif dedup (etale_muNπ_of_isUnit /
  etale_field_nezero); isPullback_muN_baseChange→def+spec; muNSpecHomEquiv state
  vs muNAbs N; muNRingGen_pow×muNModel_root_pow dedup. Resume at worker 10/74
  (muNRing_span_vanish), decl order per the 1d list.
- **[CLEANUP-5]** after T-D2+T-D3 → CartierDivisor.lean (deps: those) — includes
  upstreaming review of `IdealSheafData.mul`
- **[CLEANUP-6]** after T-D5+T-D6+T-D7 → ExactOrder.lean (deps: those)
- **[CLEANUP-7]** final per-file LevelStructure/Basic.lean (deps: T-D8, T-D9)
- **[CLEANUP-8]** after T-E3+T-E4 → EllCategory.lean (deps: those)
- **[CLEANUP-ALL-1]** before milestone T-E7: `/cleanup-all` on the project so far
  (deps: all open A/B/D/E tickets above it)
- **[CLEANUP-ALL-2]** before milestone T-E9 (deps: T-C1..T-C4, T-D8)
- **[CLEANUP-FINAL]** `/cleanup-all` — last ticket of the phase (deps: everything);
  hands to `/pre-submit`.

## Board totals check
24 work + 11 cleanup = 35; ⌈24/3⌉ = 8 ≤ 8 per-file/interval cleanups + 2 pre-milestone
+ 1 final ✓ cadence satisfied.


---

## Amendments v2 (expert-review integration, 2026-07-05)

### New stream D0 — Cartier incidence (KM 1.3; quote-complete from the preview)
All in `LevelStructure/Incidence.lean` unless noted; statements in skeleton.
- **[T-D11]** `ecd-official-definition` — official ECD (invertible ideal /
  affine-local nzd form) + equivalence with the working (finite locally free) form in
  smooth curves, both directions (reviewer: sections give ECDs; finite flat f.p.
  closed subschemes are ECDs; proper ECDs are finite flat). File: CartierDivisor.lean
  (extends T-D1; AG-LB only for the (L,s)-interface half, T-D19). Sources: KM 1.1–1.2
  (in hand).
- **[T-D12]** divisor base change: Props of `RelEffCartierDiv.baseChange` +
  functoriality. Depends: none. Parallel: yes.
  - **Status**: done — CORE RESOLVED BY beastmode-A (commit 03d76119,
    "RelEffCartierDiv.baseChange fully sorry-free — paste_vert square +
    of_isPullback stability + toImage transport", done for their T-D6a while
    beastmode-D2's claim was mid-commit; crossing claims, no work lost — D2 had
    not touched the .lean). D2's claim (2026-07-06T14:35Z) WITHDRAWN in favour
    of A's implementation; A's route = exactly the planned pasting +
    of_isPullback transport. Functoriality/composition laws (T-D20) remain
    open/unclaimed.
- **[T-D13]** `sectionVanishingIdeal_spec` (zero locus in a finite locally free
  module). Depends: none. Parallel: yes. PROVABLE-NOW candidate.
  - **Status**: done (beastmode-D2, 2026-07-06T11:05Z → 2026-07-06T12:25Z) ·
    `sectionVanishingIdeal_eq_span_coord` (Incidence.lean:67) sorry-free; module
    green; `#print axioms` on the REAL module = standard three (no sorryAx —
    independent of the file's other sorried tickets). Proof of record (post-golf,
    6-line body): `Submodule.span_eq_span` + `Set.range_subset_iff` both ways
    (kills le_antisymm/span_le plumbing AND the rintro-rfl beta gotcha); ≤-side:
    expand φσ along `b.linearCombination_repr` via conv_lhs + one squeezed
    simp only (squeeze is LOAD-BEARING: bare simp re-collapses the expansion via
    @[simp] linearCombination_repr), close by `h ▸ sum_mem` of
    `Ideal.mul_mem_right` at coord-generators. Post-proof cleanup: ✓ ran
    (single-decl Mode A — body 14→6, all gates pass, statement byte-identical,
    def untouched, no renames). Deferred /generalise flags (statement frozen,
    section-variable-shared with the def): CommRing→CommSemiring +
    AddCommGroup→AddCommMonoid compiles; universe split R/M/ι to u/v/w compiles.
    Unblocks T-D14 (with T-D12). Note: proof landed at HEAD via sibling sweep
    commits (6fb3b414 wip + 2f03d68d golf) — content verified at HEAD.
- **[T-D14]** `exists_incidenceLocusLE` (KM 1.3.4; `deg D'` equations). Depends:
  T-D12, T-D13.
  - **Status**: in_progress · **Claimed**: beastmode-D2 (stream-D successor),
    2026-07-06T14:45Z (deps both met: T-D13 mine, T-D12 core by A).
  - **Progress**: 2026-07-06T15:05Z — T-D14a DONE (`isSubdivisor_iff_le`,
    commit 87a2f88a: factorization ⟺ ideal-≤ via `Scheme.Hom.le_ker_comp` +
    `ker_subschemeι` / mathlib `inclusion` + `inclusion_subschemeι`). T-D14a′ +
    T-D14b DONE (next commit: `exists_factor_subschemeι_iff` — ∃-factorization
    ⟺ `Z ≤ t.ker`, via `t.toImage ≫ inclusion`; `baseChange_ideal` :
    `(D.baseChange t).ideal = D.ideal.comap (pullback.fst π t)` via
    `pullbackSymmetry_hom_comp_fst` + `ker_comp_of_isIso` + mathlib
    `ker_fst_of_isClosedImmersion`). Axioms standard ×3. MATHLIB DISCOVERY OF
    RECORD: IdealSheaf/Functorial.lean has the COMPLETE comap/map dictionary
    (`comap I f := (pullback.fst f I.subschemeι).ker`, comap_comp/id/mono,
    GaloisConnection `map_gc`, `le_map_iff_comap_le`,
    `ker_fst_of_isClosedImmersion`, `isPullback_of_isClosedImmersion`) and
    Subscheme.lean has `kerAdjunction`. UNIVERSALITY NOW READS: ∃h ⟺ Z ≤ t.ker
    (T-D14a′); RHS ⟺ `D.ideal.comap (fst π t) ≤ D'.ideal.comap (fst π t)`
    (T-D14a + T-D14b). REMAINING = T-D14c ONLY: construct `Z : S.IdealSheafData`
    with `Z ≤ t.ker ⟺ comap(I_D) ≤ comap(I_D')` for all t — affine-local
    equations (generators of I(D) pushed to B′ := O_{D′} flf, coordinates via
    T-D13/T-D27, glue over S, base-change bridge for the ⟺).
  - **Progress**: 2026-07-06T15:45Z — T-D14c ALGEBRA BRIDGE DONE
    (`forall_one_tmul_eq_zero_iff_span_coord_le_ker`, committed, axioms standard:
    finitely many elements of a free R-algebra die in A ⊗[R] B iff the span of
    all their coordinates ≤ ker (algebraMap R A); proof = `Basis.baseChange` +
    `baseChange_repr_tmul` + repr-injectivity; KM 1.3.4's simultaneous-vanishing
    engine verbatim-anchored — quote banked in d-lane-helpers.md, QUOTE-MISSING
    #7 discharged from the FULL KM pdf pp. 13–14). REMAINING T-D14c (scheme
    glue), in order: (i) affine-local presentation — over U ∈ S.affineOpens
    shrunk into the free locus: B′ := pushforward of O_{D′} (finite flat lfp ⇒
    locally free; use `Module.FinitePresentation.exists_free_localizedModule_powers`
    / freeLocus-open + basicOpen refinement) with basis; image-ideal generators
    gⱼ of I(D)·O_{D′} (f.type as image of lfp ideal, f.g. R-module via B′
    finite); (ii) glue local `Ideal.span coords` into `Z : S.IdealSheafData`
    (`map_ideal_basicOpen` condition — mind basis-change between overlapping
    trivialisations: the SPAN is basis-independent by T-D13, that IS the gluing
    argument); (iii) universality assembly: ∃h ⟺ Z ≤ t.ker (T-D14a′) vs
    IsSubdivisor ⟺ comap ≤ comap (T-D14a+b) ⟺ affine-locally the bridge
    (T-D14c-alg) — affine-locality of both sides over S + the A-algebra ↔
    T-point dictionary (`ΓSpec` on affines; check IdealSheafData
    `le_ker`-affine-local lemmas in Basic.lean:776-794 for the U-wise reduction).
  - **Progress**: 2026-07-06T17:50Z — **[T-D14c-1] COMPLETE, sorry-free,
    standard axioms, committed**: `vanishingLocus (p : W ⟶ S) [IsFinite p]
    [Flat p] [lfp p] (E : W.IdealSheafData) : S.IdealSheafData` with the FULL
    gluing proof. Final-mile actuals: (β) needed a NEW tower bridge lemma
    `localized'_restrictScalars_eq_restrictScalars_map` (localized' of an
    A-ideal along toAlgHom = pushforward-ideal restricted; mk'-chase via
    `mem_localized'` + `IsLocalization.mem_map_algebraMap_iff` +
    `mk'_eq_iff`/`mk'_cancel'`; GOTCHA: mul-order before ← Algebra.smul_def
    needs mul_comm) — mathlib's `Ideal.localized'_eq_map` is R-SELF-only;
    then mathlib's **`IdealSheafData.map_ideal'`** (arrow-form, works for ANY
    affine pair — NO basicOpen-transport needed at all, kills the
    preimage_basicOpen-congr entirely!) rewrote the pushforward to
    `E.ideal ⟨p⁻¹(bo f)⟩`; rw-order: bridge, BOTH algebraMap_toAlgebra, then
    map_ideal' with (U :=)(V :=) PINNED (implicit affineOpens have
    prop-components rw can't invent); (γ) final `exact hglue` closed by defeq
    across the basicOpen/affineBasicOpen spelling. Transient A-chain syntax
    break (their live T-D6a edit) waited out with a build-retry loop.
    REMAINING: [T-D14c-2] the spec `vanishingLocus_le_ker_iff`
    (Z ≤ t.ker ⟺ E.comap (W-projection of t) = ⊥ — statement design: which
    projection spelling; proof via affine-locality of both sides + the T-D14c
    bridge `forall_one_tmul_eq_zero_iff_span_coord_le_ker` + freeness on a
    shrunk cover), then [T-D14] assembly (Galois juggle over T-D14a/a′/b).
  - **Progress**: 2026-07-06T17:15Z — [T-D14c-1] SCAFFOLD GREEN+committed:
    `vanishingLocus` def at the `p.app`/`p ⁻¹ᵁ`-INLINE spelling (drop
    affinePreimage inside the def — spelling-defeq breaks instance synthesis
    otherwise); gluing proof has ALL instances + the keystone applied (hglue):
    5 letI-algebras (app-U, app-bo, S-res, W-res, DIAGONAL appLE), two towers
    via of_algebraMap_eq' + rw[algebraMap_toAlgebra ×3, ← hom_comp] + simp only
    [app_eq_appLE, map_appLE] (appLE_map unused-flagged in tower-2 — drop at
    cleanup), Module.Finite via the CLASS FIELD `p.finite_app U.1 U.2`
    (IsFinite has NO HasRingHomProperty — it is affineAnd, NOT source-local!),
    Algebra.FinitePresentation via HasRingHomProperty.appLE @lfp + rw
    [← app_eq_appLE] at hfp, hSloc := isLocalization_basicOpen, hWloc :=
    isLocalization_of_eq_basicOpen (e absorbs preimage_basicOpen; NO trailing
    rfl — rw auto-closes), mapped-monoid IsLocalizedModule via show-term
    `Submonoid.map_powers _ f` (rw-unfold of algebraMapSubmonoid gets stuck)
    + infer_instance, keystone call needs (Rₛ := Γ(S, S.basicOpen f)) pinned
    (elaboration-stuck otherwise). REMAINING under the one sorry — FINAL MILE:
    (α) rw [RingHom.algebraMap_toAlgebra] in hglue to align algebraMap = S-res;
    (β) identify `J.localized' Rf (powers f) floc` with
    `(E.ideal ⟨p⁻¹(bo f)⟩).restrictScalars`: via `Submodule.ext` +
    `Submodule.mem_localized'` vs `IsLocalization.mem_map_algebraMap_iff`
    (both mk'-characterizations; the Rf-span-vs-Af-span gap closes because
    powers-f-units lie in the image of Rf) + E.map_ideal_basicOpen at the
    W-affine ⟨p⁻¹U⟩ and fA := algebraMap f + affineOpens-Subtype-congr along
    preimage_basicOpen; (γ) close with defeq-`exact` (goal at affineBasicOpen-
    spelling vs haves at basicOpen — defeq).
  - **Progress**: 2026-07-06T16:30Z — [T-D14c-0] KEYSTONE DONE+committed:
    `submoduleVanishingIdeal` (⨆ of sectionVanishingIdeal over a submodule —
    basis-free) + membership API + `submoduleVanishingIdeal_localized` (commutes
    with localization for fp modules; proof: ≤ via mapExtendScalars-of-functional
    at defining property, ≥ via IsLocalizedModule.surj on the Hom-instance +
    two unit-cancellations `Ideal.unit_mul_mem_iff_mem` + `mk'_cancel'`;
    LEAN GOTCHAS: Submonoid-smul vs R-coe-smul needs `← Submonoid.smul_def`
    before mk'_cancel'/hφ-rw; IsLocalizedModule.surj's pair needs `dsimp only at`
    to beta the .2-projection; span_le membership goals arrive beta-unreduced +
    set-coe — open with `show`; own SECTION with implicit {R}{M} required —
    ZeroLocus's explicit section-vars break the internal applications).
    All axioms standard. NEXT: [T-D14c-1] `vanishingLocus (p : W ⟶ S) [IsFinite p]
    [Flat p] [lfp p] (E : W.IdealSheafData) : S.IdealSheafData` — ideal U :=
    submoduleVanishingIdeal Γ(U) Γ(p⁻¹U) (E.ideal ⟨p⁻¹U, affine⟩-as-submodule);
    gluing via the keystone at S := powers f with the structure-sheaf
    localization instances (p finite ⟹ p⁻¹U affine: IsAffineHom.preimage;
    sections-of-finite = fp module: the affine dictionary for IsFinite/Flat/lfp);
    then [T-D14c-2] le_ker_iff via the T-D14c bridge; then [T-D14] assembly.
  - **Progress**: 2026-07-06T16:00Z — T-D14c REFORMULATED CURVE-FREE (design of
    record, supersedes the (i)-(iii) map where they differ): via Galois
    (`map_bot : map ⊥ f = f.ker` + `map_gc`), `IsSubdivisor D′ D ⟺ D.ideal ≤
    D′.ideal ⟺ E = ⊥` where `E := D.ideal.comap D′.ideal.subschemeι` (the
    intersection ideal ON the subscheme D′); base-changed condition ⟺
    `E.comap q_t = ⊥` (comap_comp along D′_T → D′ → C). SO T-D14c = a standalone
    statement about FINITE LOCALLY FREE morphisms, no curves: for p : W ⟶ S
    finite+flat+lfp and E : W.IdealSheafData, ∃ Z : S.IdealSheafData with
    `Z ≤ t.ker ⟺ E.comap (W-projection of t) = ⊥` for all t. Construction:
    `Z.ideal U := dual-span of E's sections over the affine p⁻¹U` (dual-span :=
    span {φ g | φ ∈ Dual, g ∈ J} = ⨆_{g} sectionVanishingIdeal — BASIS-FREE, so
    globally defined; basis enters only in proofs via T-D13). Gluing keystone
    [T-D14c-0]: dual-span commutes with localization for f.p. modules — engine
    DISCOVERED: `Module.FinitePresentation.isLocalizedModule_map` (instance,
    Algebra/Module/FinitePresentation.lean:546: Hom-modules localize for fp
    source; at N := R this is Dual-localization; `IsLocalizedModule.surj` gives
    every localized functional as unit⁻¹ • localized-φ). Bridge for
    universality = `forall_one_tmul_eq_zero_iff_span_coord_le_ker` (DONE).
    Instantiation plumbing back to divisors via `comapIso`. Sub-ladder:
    [T-D14c-0] dual-span-localizes (pure algebra) → [T-D14c-1] `vanishingLocus
    p E : S.IdealSheafData` (def + gluing) → [T-D14c-2] `le_ker_iff` spec →
    [T-D14] assembly (Galois juggle, ~10 lines).
  - **ROUTE OF RECORD (analysis banked 2026-07-06T14:45Z, COUNT-FREE)**: the
    statement never mentions the `deg D′` equation count (docstring-only per the
    attack log), so NO local principality of `I(D)` is needed — the T-D11/AG-LB/
    FLAT gates do NOT block this ticket. Working picture: affine-locally on S,
    `I(D)` is f.g. (from D.lfp: lfp closed immersion ⟹ locally f.g. ideal);
    condition `IsSubdivisor D′_T D_T ⟺ D_T.ideal ≤ D′_T.ideal ⟺ every generator
    of I(D) dies in B′ := O_{D′} after base change` — cut by the
    sectionVanishingIdeal of EACH generator-image in the flf module B′ (engine =
    T-D13/T-D27; count k·d′ instead of KM's d′ — count-free statement doesn't
    care). Sub-tickets (born split per statement-splitting.md):
    [T-D14a] subdivisor-order dictionary `IsSubdivisor D′ D ↔ D.ideal ≤ D′.ideal`
    (subscheme-factorization ⟺ IdealSheafData-≤; search mathlib IdealSheaf/
    Subscheme.lean for the factorization iff first); [T-D14b] base-change of the
    divisor ideal: `(D.baseChange t).ideal` = pushed ideal, generator-level
    (A's T-D12 toImage-transport work may already contain pieces — reuse);
    [T-D14c] the vanishing-locus construction glued to an `S.IdealSheafData` +
    its T-point universality (T-D13/T-D27 + T-D27(ii)-bridge stated here where
    the ⦃T⦄-spelling pins it); [T-D14] assembly. NEXT ACTION: T-D14a mathlib
    search (subscheme factorization ↔ ideal order), then state skeletons.
- **[T-D15]** `exists_incidenceLocusEQ` (KM 1.3.5, verbatim in hand). Depends: T-D14.
- **[T-D16]** `exists_subgroupLocus` (KM 1.3.7, verbatim + proof in hand;
  `1 + deg + deg²` equations via `[e] ≤ D`, `D = inv*D`, `[m(P₁,P₂)] ≤ D_W`).
  Depends: T-D14, T-D15, T-D3.
- **[T-D17]** `exists_exactOrderLocus` (A-generators, `A = ℤ/N`; KM 1.6 instance).
  Depends: T-D16. Feeds T-E7.
- **[T-D18]** `exists_fullLevelLocus` (`A = (ℤ/N)²`). Depends: T-D16. Feeds T-E9.
- **[T-D19]** `ecd-pair-section-interface` — `D ↔ (L, s)`, sum = tensor. BLOCKED on
  AG-LB. Sources: KM 1.2 (in hand).
- **[T-D20]** flat pullback along `Y → X` + composition laws. Depends: T-D12.
- **[T-D21]** general-`A` A-structures/A-generators representability (KM 1.5–1.6,
  in hand): closed subscheme of `Hom(A, E)`. Depends: T-D16; structure theorem for
  finite abelian `A` (mathlib). The two instances T-D17/T-D18 do not wait for this.

### New stream SG — finite locally free closed subgroups (review requirement)
- **[T-SG1]** finite locally free closed subgroup schemes of `E/S`: definition +
  basic API (kernel-style constructors; `E[N]` as the leading example).
- **[T-SG2]** fppf-local cyclicity (KM 1.4.1 verbatim, in hand) as the **definition of
  record** for Γ₀(N); discharges/replaces the geometric-fibre surrogate in
  `IsGammaZero` (upgrade `T-D10`). **GATE: no Γ₀ representability theorem may be
  stated against the surrogate.**
- **[T-SG3]** cyclicity is a closed condition (KM 6.4 ⧗; statement-level now, proof
  gated on full KM).

### New stream Q — finite quotients (reviewer split of AG-QUOT)
- **[T-Q1]** finite group actions on schemes (vocabulary; mathlib group-action reuse).
- **[T-Q2]** free actions vs stabilizers (statements).
- **[T-Q3]** affine quotients: `Spec(A^G)` universal property (Loeffler 3.6.1 proof
  route, quote in hand). PROVABLE with today's mathlib invariant-theory fragments —
  early target.
- **[T-Q4]** base change of invariants (KM Ch. 7 appendix ⧗ "base change for rings of
  invariants").
- **[T-Q5]** gluing affine quotients (quasi-projective case; Loeffler 3.6.1).
- **[T-Q6]** quotients of rigidified moduli problems (feeds KM 4.7 ⇐, T-E5).
- **[T-Q7]** coarse quotient statements for non-fine levels (`Y₀(N)`, `Y(1)`) — via
  the groupoid layer (D6), phase M of the spine.

### New stream G — groupoid layer (review Q7)
- **[T-G1]** `isIso_homOver`: pointed `S`-morphisms of elliptic curves are isos.
- **[T-G2]** pointed morphisms are group homomorphisms (rigidity; KM 2.4-adjacent ⧗).
- **[T-G3]** `aut_trivial_of_fullLevel` (rigidification bridge; Loeffler 3.8.3
  content). Blocks: passing any small-level statement to iso-classes.

### Modified in v2
- T-A6 → canonicity project (above); **T-B3, T-B5, T-C2, T-D5–T-D9 no longer depend
  on it** (group data is a record field).
- `pointEquivOverHom`, `pointAddCommGroup`, `baseChange` group data: **done** in the
  integration commit (real definitions).
- T-C0 added; T-C1 re-routed (duality API); T-C2a/b/c spec tickets added
  (naturality, `N∣M`, symplectic pin — statements in skeleton).
- T-F6 added; T-F4 re-routed through it.
- Phase-2 named blocks added (review Q8): **N-Isog** moduli problem, degeneracy-map
  finite flatness, `Γ₀(p)`-regularity with auxiliary level — statements to be cut
  when full KM lands (all on the do-not-formalize-from-memory list).

### Do-not-formalize-from-memory gate (v2, binding)
KM 2.3, 2.8, 4.7, 5–7, 8–10, 12–13: tickets touching these may *state* from
[Loe]/[Hida] quotes but may not close, nor may proofs be reconstructed "from
standard knowledge", until the full KM text is in `refs/ModularCurves/` and the
decomposition quote-gate passes.

### Cleanup cadence (v2 recount)
Work tickets: 24 (v1) − 1 (pointAddCommGroup absorbed) + 11 (D0) + 3 (SG) + 7 (Q)
+ 3 (G) + 2 (C0, F6) = **49**. ⌈49/3⌉ = 17 ≥ cleanups: v1's 11 + **[CLEANUP-9]**
Incidence.lean after T-D13+T-D14+T-D15 · **[CLEANUP-10]** Incidence.lean final (after
T-D16–T-D18) · **[CLEANUP-11]** Groupoid.lean final (after T-G1–G3) · **[CLEANUP-12]**
quotient stream after T-Q3+T-Q4+T-Q5 · **[CLEANUP-13]** WeilPairing after T-C0+T-C2a–c
· **[CLEANUP-ALL-3]** before T-F6. All cleanups: no `set_option maxHeartbeats`;
DS-register unchanged; `#print axioms` audit.

### Start-now set (v2)
**T-E1, T-E2, T-A2, T-B2, T-D3, T-D13, T-Q3, T-F0** — 8 independent workers.


---

## Amendments v3 (2026-07-05): levels layer + RR-only black-box directive

### Stream H — general levels & full level over ℤ (`Moduli/GammaH.lean`, statements in skeleton)
- **[T-H1]** `gammaHNaive_bot`: `P_⊥ ≅` naive full level. Depends: T-E4. Golf-sized.
- **[T-H2]** `glSmul` membership + **[T-H2a]** action law (needs killed-by-N; uses
  `point_smul_eq_comp_mulBy`). Depends: T-A6d spec only.
- **[T-H3]** `gammaHNaiveProblem` functor laws + orbit-compat of pullback.
- **[T-H4]** `gammaHNaive_relativelyRepresentable` (Loeffler 3.8.2; Weil-pairing open
  locus for H = 1, quotient for general H). Depends: T-C0/T-C1, stream Q, T-D18.
- **[T-H5]** `gammaHNaive_rigid_iff` (Loeffler 3.8.3, torsion-free preimage in SL₂(ℤ)).
  Depends: T-H3; mathlib `CongruenceSubgroup` API.
- **[T-H6]** `gammaHNaive_representable_of_rigid` — every fine modular curve of every
  level. Depends: T-E5, T-H4.
- **[T-H7]** `gammaFullNaive_not_rigid_of_le_two` — the honest "only a stack for
  N ≤ 2" statement ([-1] fixes E[2] pointwise). Depends: T-E4.
- **[T-H8]** `gammaFullDrinfeld_representable` (N ≥ 3, arbitrary ring — **full level N
  over ℤ**; KM 4.7.2/5.1 ⧗KM gate) + **[T-H8a]** Drinfeld problems' functor laws.
- **[T-H9]** `gammaOneDrinfeld_representable` (N ≥ 4 over ℤ; ⧗KM).
- **[T-H10]** `fullLevelGroupoid` category laws + equivalence-to-discrete for N ≥ 3
  (via T-G3).

### Stream M — coarse moduli (`Moduli/Coarse.lean`, statements in skeleton)
- **[T-M1]** `jLine_coarse_points` + **[T-M1a]** j-compatibility (KM 8.2 ⧗; Silverman
  III.1.4(b) fibrewise — HasseWeil/mathlib `IsomOfJ` reuse). Universal-property half
  = T-Q7.
- **[T-M2]** `exists_coarse_gammaH` (Loeffler §3.6 + §3.8 Rem. 1, quotes in hand;
  covers Y₀(N) and small-N full level). Depends: stream Q, T-H6 (auxiliary rigid
  level), T-G1.

### De-black-boxing streams (owner directive: only RR stays; parallel)
- **[T-COH0]** scoping: integrate mathlib-PR survey; decide Čech-on-affines route;
  cut T-COH1.. with statements (`π_*O ≅ O_S` + base change; `R¹π_*O` line bundle).
- **[T-FLAT0]** scoping (mathlib RingTheory.Flat + survey) · **[T-FLAT1]** Lean
  statement of the fibrewise criterion + fibre-morphism helper; then proof tickets.
- **[T-OT0]** scoping after T-SG1; statement "flf comm. group scheme of rank N killed
  by N"; Deligne norm-argument decomposition (FltRegular norm lemmas per rescan).
- **[T-DESC0]** scoping: exact coverage of mathlib Morphisms/Descent + FlatDescent
  (survey); route via relatively-ample embedding + module descent; target
  `ellipticCurve_fppf_descent` (statement exists).
- **[T-IRR0]** scoping: algebraic (KM Ch. 10 ⧗, Tate-curve degeneration) vs analytic
  (uniformisation ↔ LeanModularForms) route; target `yRho_geometricallyIrreducible`
  (statement exists). Late-phase; parallel.

Former BB-usage edges become dependencies: T-B4 ← FLAT; T-D5 ← OT; T-E10/T-E8 ← DESC;
T-A6 ← COH; T-F5 ← IRR. **BB-RR remains the only standing assumption.**

### Cadence (v3 recount)
Work: 49 (v2) + 12 (H) + 3 (M) + 5 (scoping) = **69**; cleanups: 17 (v2) +
**[CLEANUP-14]** GammaH.lean after T-H2+T-H3+T-H5 · **[CLEANUP-15]** GammaH final ·
**[CLEANUP-16]** Coarse.lean final · **[CLEANUP-ALL-4]** before T-H8 = **21**.
⌈69/3⌉ = 23 ≈ satisfied with per-file finals counted; re-audit at next /develop
--continue (R3).

### Start-now set (v3)
T-E1, T-E2, T-A2, T-B2, T-D3, T-D13, T-Q3, T-F0, **T-H7, T-FLAT1** — 10 workers.


---

## Amendments v4 (2026-07-05): worker-grade proof plans + ecosystem integration

**The two decomposition companions are now BINDING for their tickets:**
`decomposition-km1.md` (KM Ch. 1 complete, all proofs read) governs streams D0/D/H's
engine tickets; `decomposition-gme2.md` (GME Ch. 2 chains, proofs read) governs the
A6 (Abel), A7 (Weierstrass embedding), E12–E15 (M₁/rigidity/Legendre/ℰ₃), B8–B9
(dual isogeny/Hasse/Aut), C (Weil pairing), Y (Thm 2.6.8) chains. A worker on any of
these tickets MUST follow the transcribed proof steps; deviations are B2 reports.

**Gate change:** T-C1 (Weil pairing construction) is **no longer KM-gated** — the
construction of record is GME 2.6.4 pp. 152–153 (read, transcribed in
decomposition-gme2 §C), duality-compatible per (PR2), Silverman-convention anchored
via the classical fibre formula (C.3). KM 2.8 remains a reconciliation item only.

**New hard-bit tickets (from the read proofs; statements per the decompositions):**
- [T-NOETH0] scoping: mathlib `SpreadingOut`/`AffineTransitionLimit` coverage vs
  EGA IV 8.9.1 uses (HB-NOETH); policy: try direct proofs first.
- [T-D22] section-of-smooth-rel-curve ⟹ locally principal nzd ideal (HB-REGIMM;
  étale-local 𝔸¹ model route). [T-D23] closed pt of smooth curve /field has DVR
  local ring. [T-D24] finrank additivity in SES of finite free modules (local + glue).
  - **[T-D24] Status**: done (beastmode-D2, 2026-07-06T12:30Z → 2026-07-06T13:20Z) ·
    NEW ForMathlib/FinrankExact.lean, sorry-free, standard axioms ×3, zero
    warnings. Delivered (statements per the claim-time package, attack block in
    d-lane-helpers.md): (a) `Function.Exact.nonempty_linearEquiv_prod_of_projective`
    — SES with projective quotient splits, `Nonempty (N ≃ₗ[R] M × P)`, Semiring,
    1-line term (projective_lifting_property + splitSurjectiveEquiv);
    (b) `Module.finrank_eq_add_of_exact` — M, P finite free,
    `[StrongRankCondition R]`, 1-line term ((a) + finrank_prod, no locality);
    (c) `Module.rankAtStalk_eq_add_of_exact` — M, P finite FLAT, N
    hypothesis-free, pointwise at every prime; THE degree-additivity engine for
    D-curve.3. ROUTE CHANGE vs claim note: (c) went through TENSORS not
    LocalizedModule (rankAtStalk_eq_finrank_tensorProduct + (b) over
    Localization.AtPrime at f.baseChange/g.baseChange). FACTS OF RECORD:
    `LinearMap.baseChange_eq_ltensor` is rfl ⟹ Flat.lTensor_exact /
    lTensor_preserves_injective_linearMap / lTensor_surjective apply to
    baseChange directly (no show/rw dance); `Localization.flat` instance fires
    automatically; free-of-flat-local idiom = `attribute [local instance]
    free_of_flat_of_isLocalRing in` (FreeLocus.lean precedent). Post-proof
    cleanup: ✓ ran ×3 (one Mode-A worker per decl; bodies 5→1, 2→1, 20→4;
    all hard gates pass; no renames; naming precedent
    `Module.length_eq_add_of_exact`). Generality probed maximal per axis
    (AddCommMonoid impossible — splitting needs groups). Nearest mathlib
    analogue documented in module docstring: `ModuleCat.free_shortExact_
    finrank_add` (bundled, single-universe) — ours is unbundled multi-universe.
    Feeds T-D3 (`sectionsDivisor_degree`) + D-inc difference-divisor degrees.
  [T-D25] rank-1 locally free algebra ⟹ structure iso. [T-D26] degree-0 effective ⟹
  empty. [T-D27] zero-locus over W of a module = zero-locus over S of its f.l.f.
  pushforward. [T-D28] A-Str ≅ ∏ A_i-Str (KM 1.7.3, phase 2). [T-D29]
  - **[T-D27] Status**: done (beastmode-D2, 2026-07-06T13:40Z → 2026-07-06T13:50Z) ·
    `sectionVanishingIdeal_eq_span_coord_coord` (Incidence.lean §ZeroLocus:81)
    sorry-free, standard axioms, module green. FINDING OF RECORD: the composed
    coordinate function `fun p => c.coord p.1 (b.coord p.2 σ)` is DEFEQ to
    `(c.smulTower b).coord · σ` at default transparency — the whole proof is the
    ONE-LINE term `sectionVanishingIdeal_eq_span_coord R M (c.smulTower b) σ`
    (a tactic route needs congr-by-defeq since rw's auto-rfl is reducible-only).
    Post-proof cleanup: ✓ ran (Mode-A worker — 2-line tactic → 1-line term, all
    hard gates pass, heartbeats unchanged, statement byte-identical mod line
    packing; statement-splitting.md conformance: single equation ✓). Upstream
    note: mathlib lacks `smulTower_coord` next to `@[simp] smulTower_repr`.
    Deferred /generalise flags (statement frozen; ALL scratch-verified):
    CommRing B→Semiring B; Algebra R B→Module R B (tower is module-theoretic);
    section CommRing R→CommSemiring + AddCommGroup M→AddCommMonoid (whole
    ZeroLocus section incl. T-D13's proof compiles); ι κ universe split.
    Deliverable (ii), the base-change vanishing bridge (`σ ⊗ 1 = 0 in M ⊗[R] A ↔
    I(σ) ≤ ker`), DEFERRED into T-D14/T-D16 where their ⦃T⦄-statements pin the
    exact tensor spelling (same scoping decision as T-D26's wrapper). Attack
    block in d-lane-helpers.md. Wave 0 REMAINING: T-D31, T-D32.
  - **[T-D25] Status**: done (beastmode-D2, 2026-07-06T13:25Z,
    **RESOLVED-BY-MATHLIB, no project code**) — pin 11b908e5cdd9 has BOTH forms:
    `Module.algebraMap_bijective_iff_rankAtStalk` (rankAtStalk S = 1 ↔ Bijective
    (algebraMap R S), for [Module.Flat R S] [Module.Finite R S]; + alias
    `algebraMap_bijective_of_rankAtStalk`) in RingTheory/Flat/Rank.lean:120–129,
    and the free form `Module.Free.bijective_algebraMap_of_finrank_eq_one`
    (LinearAlgebra/Trace.lean:399). KM 1.2.7 engine ready for the degree-1
    divisor = section argument. Flat/Rank.lean is ALSO the home of
    `RingHom.finrank` (rankAtStalk of a ring hom) — the affine dictionary for
    `Scheme.Hom.finrank` degree work (T-D3/T-D15/T-D26 wrappers).
  - **[T-D26] annotation** (beastmode-D2, 2026-07-06T13:25Z): the algebra engine
    is mathlib-present — `Module.rankAtStalk_eq_zero_iff_subsingleton`
    (FreeLocus.lean:303, finite flat) + `Module.support_eq_empty_iff`. What
    remains of T-D26 is only the divisor-level wrapper (`D.degree ≡ 0 →
    D.ideal = ⊤`), which needs the Scheme.Hom.finrank ↔ rankAtStalk affine
    dictionary — fold it into T-D15's proof (Wave 3) where that dictionary is
    built anyway; do NOT build it standalone now. Status stays open, scoped
    to the wrapper.
  charpoly-as-norm (`LinearMap.charpoly f = Algebra.norm R[T] (T•1 − f)`).
  - **[T-D29] Status**: done (beastmode-D2, 2026-07-06T11:55Z → 2026-07-06T12:05Z) ·
    `Algebra.charpoly_lmul_eq_norm` in NEW ForMathlib/CharpolyNorm.lean
    (mathlib-only imports, chain-independent). Reading of record (binding, KM 1.8.2
    "char poly of f ∈ B = norm of T−f rel B⊗R[T]/R[T]"): the endomorphism is
    `Algebra.lmul R B b` — statement `(Algebra.lmul R B b).charpoly =
    Algebra.norm R[X] ((X:R[X]) ⊗ₜ 1 − 1 ⊗ₜ b)` in `R[X] ⊗[R] B`. The naive
    general-endomorphism reading is FALSE (norm on End(V) is det^dim) — attack
    block in d-lane-helpers.md. Gap re-verified (my 4 searches + worker's loogle/
    grep/name-pattern re-run; `charpoly_baseChange` is functoriality, not the
    bridge). Proof: charpoly_def + norm_eq_matrix_det at the baseChange basis;
    congr 1; ext; one terminal simp (charmatrix_apply/diagonal_apply/
    leftMulMatrix_eq_repr_mul/baseChange_repr_tmul engine + eq_comm kills the
    diagonal split). Axioms standard three; zero warnings. Post-proof cleanup:
    ✓ ran (single-decl Mode A — body 15→6 lines, all gates pass incl. hard gates,
    statement byte-identical, no renames queued). GENERALISE flag for the
    /generalise lane: `CommRing B → Ring B` verified-compiling (worker probe;
    mathlib precedent `aeval_self_charpoly_lmul` uses `[Ring M]`) — deferred,
    statement frozen. Feeds T-D30 (KM 1.8.2 (2)⟹(1)); pin the element spelling
    `X ⊗ₜ 1 − 1 ⊗ₜ b` at the T-D30 call site.
  [T-D30] char-poly form of full-sections + equivalence (KM 1.8.2). [T-D31]
  reduced-ring evaluation separation for MvPolynomial. [T-D32] f.l.f.-map iso ⟺
  geometric-fibre iso (det-unit local-global). [T-D3a′] Flat-of-SES (if mathlib
  lacks). [T-D3b] `IdealSheafData.mul` (upstream candidate).
  - **[T-D32] Status**: done (beastmode-D2, 2026-07-06T14:15Z → 2026-07-06T14:30Z) ·
    ForMathlib/BijectiveResidueField.lean sorry-free, standard axioms ×3, module
    green (landed via sibling sweep 6b061f6b; verified at HEAD). All three
    statements delivered exactly as claimed below; the global assembly's
    IsLocalizedModule-instance came from `isLocalizedModule_iff_isBaseChange` +
    `TensorProduct.isBaseChange`; localized-map = baseChange by
    `IsLocalizedModule.ext` + `map_comp`; fibre comparison = cancelBaseChange
    square by 2-level tensor induction (`simp [eM, eN]` closes the pure-tensor
    case). GOTCHA: `bijective_of_isLocalized_maximal`'s Rₚ-tower binders are
    ELIDED from its signature (explicit args = Mₚ f Nₚ g F H; the localized
    condition is spelled `IsLocalizedModule.AtPrime`). Post-proof cleanup:
    DEFERRED (owner pause). WAVE 0 COMPLETE. DEDUP NOTE for CLEANUP-5/cleanup
    lane: beastmode-A's T-D2 introduced `eq_of_forall_field_hom_eq` (in their
    NormBaseChange/CartierDivisor work) duplicating my T-D31
    `IsReduced.eq_of_forall_ringHom_field` (ForMathlib/ReducedSeparation.lean,
    committed earlier same day) — consolidate to one, prefer the ForMathlib
    upstream-candidate spelling. ORIGINAL CLAIM (audit): NEW
    ForMathlib/BijectiveResidueField.lean.
    Route of record (NOT the det route — mathlib's det is endo-only; the
    Nakayama toolkit in RingTheory/LocalRing/Module.lean is the engine). Born
    split: (a) `IsLocalRing.surjective_of_surjective_lTensor_residueField`
    ([Module.Finite R N] only): via `map_tensorProduct_mk_eq_top` (Nakayama) +
    `TensorProduct.mk_surjective` (quotient scalars pull through) + lTensor_tmul;
    (b) `IsLocalRing.bijective_of_bijective_lTensor_residueField` ([Finite M]
    [Finite N] [Flat N]): injectivity leg = mathlib's PACKAGED
    `split_injective_iff_lTensor_residueField_injective` (needs Free N =
    free_of_flat_of_isLocalRing) + (a); (c) global
    `LinearMap.bijective_of_forall_bijective_lTensor_residueField` (fibres at
    all maximal J via `J.ResidueField`): `bijective_of_isLocalized_maximal`
    (LocalProperties/Exactness.lean:71) instantiated at TENSOR localizations
    (Mₚ := Rₚ ⊗ M, f := TensorProduct.mk 1, instance via
    `isLocalizedModule_iff_isBaseChange` + `TensorProduct.isBaseChange`),
    localized map identified with `φ.baseChange Rₚ` by IsLocalizedModule-ext,
    then (b) + the `AlgebraTensorModule.cancelBaseChange` comparison square
    (pattern: mem_support_iff_nontrivial_residueField_tensorProduct's proof).
    ⟹-direction (iso → fibre-iso) NOT stated (no consumer; assembly test).
    Consumer: T-D6 (3)⟺(5). Attack block in d-lane-helpers.md. NOTE: cleanup
    passes PAUSED by owner instruction (2026-07-06T14:05Z) — proving
    prioritized; accumulated cleanup debt for the new ForMathlib files
    (ReducedSeparation, BijectiveResidueField) goes to the cleanup lane /
    a later batch pass.
  - **[T-D31] Status**: in_progress · **Claimed**: beastmode-D2 (stream-D
    successor), 2026-07-06T13:55Z → **done 2026-07-06T14:10Z** ·
    NEW ForMathlib/ReducedSeparation.lean (mathlib-only imports), sorry-free,
    standard axioms ×2, zero warnings, committed (landed via sibling sweep
    2fb2b06a; content verified at HEAD). Delivered (born split): (i)
    `IsReduced.eq_zero_of_forall_ringHom_field`: in a reduced CommRing, an
    element killed by every ring hom to a (same-universe) field is 0 — proof:
    `nilpotent_iff_mem_prime` + at each prime the hom
    `A → A⧸J → FractionRing (A⧸J)` + `IsFractionRing.injective` +
    `isNilpotent_iff_eq_zero`; (ii) the `eq_of` corollary via `sub_eq_zero`.
    Mathlib state verified: `IsReduced (MvPolynomial σ R)` instance EXISTS
    (MvPolynomial/Nilpotent.lean:55 — the reducedness half of T-D31 is
    mathlib-present); `nilpotent_iff_mem_prime` exists; NO field-hom separation
    lemma (greps: eq_zero_of_forall∩field, forall_ringHom — zero hits). Fields
    (not just alg. closed) suffice for the KM 1.9.2 consumer; maximal ideals
    would NOT (Jacobson ≠ nil). Feeds T-D2's reduce-to-geometric-points step.
    Post-proof cleanup: DEFERRED (owner paused cleanup passes 2026-07-06T14:05Z;
    debt tracked for the cleanup lane).
  - **[T-D3b] Status**: done (beastmode-D2, 2026-07-06T11:25Z → 2026-07-06T11:40Z,
    **RESOLVED-BY-MATHLIB, no project code**) — the current pin (11b908e5cdd9)
    already has the full multiplicative structure on `IdealSheafData`:
    `Mul`/`Pow`/`IdemCommSemiring` + `ideal_mul`/`support_mul`/`top_mul`/… simp API
    (Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean §Semiring, lines 400–460;
    daily-bump gift postdating the D-off.2 sub-plan). T-D3's `sectionsDivisor` fold
    = `∏` against these instances. Finding + superseded attack block recorded in
    `decompose-attacks-2026-07-06/d-lane-helpers.md`. NOTE for the whole D-lane:
    IdealSheaf/Basic.lean also has `radical`, `zeroLocus_mul`, `mkOfMemSupportIff` —
    re-run the five-method search per ticket; the bump keeps landing KM-1 tools.
- [T-NORM0] norm/det of pushforward along finite locally free morphisms
  (`∧^r g_*`; engine for Cor 2.2.2, pairing C.2, charpoly bridge). HB-NORM.
- [T-RED0] reduced-universal-base transfer principle (identities of morphisms of
  f.l.f. schemes over reduced base ⟺ geometric fibres; + pullback-from-universal).
  Used by B8, T-C2a–c, PR1–3.
- [T-PIC0] Pic(X) for a scheme via invertible O_X-modules (mathlib `SheafOfModules`
  + LocallyFree ✓ merged); fibre-degree of an invertible sheaf. COH-adjacent;
  UNCLAIMED per survey — coordinate on Zulip before starting.
- [T-A6.α–δ], [T-A7.a–e], [T-E12..T-E15], [T-B8/T-B9], [T-C.1–.5], [T-Y.1–.7]:
  the chain tickets exactly as decomposed in decomposition-gme2.md (statements to be
  added to the skeleton as their prerequisite APIs land; the chain files list every
  step + its source page).

**Ecosystem coordination (BINDING; see ecosystem-survey-2026-07-05.md):**
T-E1/T-E2 ⟷ mathlib PR #25218 (Tate normal form) — check before starting;
T-B2/AG-CD ⟷ #40500 + YaelDillies/toric Diag/Character; universal curves ⟷ #41300;
group-law alt route ⟷ #35151; COH-3 ⟷ #36345/#36218 (Riou/Nugent lane — do not build);
Weil divisors = Raph-DG lane (we do effective Cartier only); FLAT = ours (unclaimed);
Tate curve/p-divisible/eff-Cartier/R^if_*/torsors = confirmed vacuums (ours).
OWNER ACTIONS: Zulip modular-curves post; XYin licence ping; FLT stub-fill offer.

**COH stream targets pinned** (decomposition-gme2 header): COH-1 = GME Lemma 1.10.4;
COH-2 = GME Cor 1.9.12; COH-3 = mathlib R^i f_* lane. **BB-RR pinned** := GME
2.1.2/2.1.3/2.1.6 exactly; nothing else enters the box.

**Start-now set (v4, re-verified against dependencies + ecosystem):**
T-A2/T-A3 (per A7.e Proj route), T-B2 (against #40500/toric), T-D3b, T-D13, T-D22,
T-D24, T-D25, T-D29, T-NORM0, T-Q3, T-F0, T-H7 — 12 parallel-safe;
plus T-E1/T-E2 the moment the #25218 coordination check is done.


### Reuse-policy note (v4.1, 2026-07-05)
The ecosystem policy is now three-tier "copy by default" (see
`ecosystem-survey-2026-07-05.md` §BINDING reuse policy v2): Tier-1 sources are
copied into `ModularCurves/ForMathlib/` under the VENDOR register
(provenance header + delete-when-upstream-lands; enforced by every CLEANUP ticket
and the daily bump). T-E1/T-E2's #25218 check becomes: fetch the PR branch, vendor
or align, then work. T-B2 may vendor toric's `Diag` layer. Tier-2 (unlicensed:
XYin, Loeffler, WenrongZou) = read + re-prove until a licence lands (owner pings).
Tier-3 = track/steer the COH, Weil-divisor, descent-effectivity mathlib lanes.


---

## Amendments v5 (2026-07-06): ★ Stream-D claim + execution work order (beastmode-D)

*Stream D (Drinfeld structures, `LevelStructure/*`) claimed by **beastmode-D**,
2026-07-06T09:25Z. This section is the D-lane execution plan, written so any successor
agent can continue without replanning. The stream star reserves the lane and records
the plan; it does NOT lock tickets — claim ONE ticket at a time per rule 5. Binding
proof plans: `decomposition-km1.md` (KM Ch. 1, all proofs read + transcribed).
Adversarial coverage: every existing LevelStructure declaration has a complete
≥3-attack block in `decompose-attacks-2026-07-06/level-structures.md` (22 SURVIVED /
4 REJECTED / 6 NEEDS-FIX — **all ten flagged fixes are already applied in the
skeleton**, re-verified in-file 2026-07-06T09:25Z), so standing rule 1 is satisfied
for every sorried statement listed below. NEW helper declarations (T-D22…T-D32 etc.)
still need their own attack blocks when first stated.*

### D-lane ground state (verified against the files, 2026-07-06T09:25Z)

18 sorried declarations across the four files; 17 are D-lane (1 is B-lane):

| File | Sorry (decl : line) | Ticket |
|---|---|---|
| CartierDivisor.lean | `sectionsDivisor` :81 (DATA, DS4a) · `sectionsDivisor_degree` :94 | T-D3 |
| | `baseChange.finite/flat/lfp` :104–106 | T-D12 |
| | `isFullSetOfSectionsAlg_iff_fields` :155 | T-D2 |
| ExactOrder.lean | `HasExactOrder.smul_eq_zero` :75 | T-D5 (PARKED on OT) |
| | `hasExactOrder_iff_geometric` :89 · `hasExactOrder_iff_etale` :98 | T-D6 · T-D7 |
| Basic.lean | `torsionIdeal_subscheme` :85 | **T-B3a — B-lane, do NOT claim from D** |
| | `isFullLevel_iff_naive` :102 · `isGammaOne_iff_naive` :107 | T-D8 (⧗KM) · T-D9 |
| Incidence.lean | `sectionVanishingIdeal_eq_span_coord` :69 | T-D13 |
| | `exists_incidenceLocusLE` :97 · `exists_incidenceLocusEQ` :106 | T-D14 · T-D15 |
| | `exists_subgroupLocus` :118 | T-D16 |
| | `exists_exactOrderLocus` :131 · `exists_fullLevelLocus` :146 | T-D17 · T-D18 |

State notes (what changed on 2026-07-06, so nobody re-litigates it):
- T-D6/T-D7 attack obligation **RESOLVED** — standing hypothesis
  `hkill : (N : ℤ) • P = 0` is in the skeleton (ExactOrder.lean:85/:96), docstrings
  record the `ℚ̄[ε]` counterexamples. Workable as stated.
- `torsionIdeal` is REAL (`(E.torsionι N).ker`, Basic.lean:77) — no longer a
  data-sorry; its pin `torsionIdeal_subscheme` is T-B3a (B-lane). `IsNaiveGammaOne`
  carries the global killing clause (also repairs T-E7's functor). `IsGammaZero`'s
  cyclicity clause is in Drinfeld divisor form. `IsFullSetOfSectionsAlg` carries
  `[Module.Free R B] [Module.Finite R B]` (norm-junk fix). `sectionsDivisor(_degree)`
  is scope-pinned to KM 1.2.1 standing hypotheses (`IsSeparated` +
  `SmoothOfRelativeDimension 1`).
- **DS4a (`sectionsDivisor`) is the stream's only remaining data-sorry.** While T-D3
  is open, downstream tickets use it through its specs ONLY (standing rule 2). Its
  register pins are `sectionsDivisor_degree` + a base-change spec — the latter is
  NOT yet stated in the skeleton; stating+proving it is part of T-D3 (below).
- FLAT-stream independence: only T-D11's fibrewise-recognition equivalence needs
  T-FLAT1 (HB-FIBCRIT); nothing else in the D-lane blocks on FLAT (decomposition-km1
  D-off.4). HB-NOETH policy: try direct proofs first; NEVER strengthen a statement
  to noetherian hypotheses (that is B2-grade target drift).

### Execution order (waves; recommended claim order within each wave)

**Wave 0 — pure-algebra helpers, independent, PROVABLE NOW.** New statements go in
`ModularCurves/ForMathlib/` (upstream candidates, OURS register) as `:= by sorry`
skeleton first (module must build green), attack block recorded (decomposition.md or
a new file under `decompose-attacks-*/`), then prove.
1. **T-D13** `sectionVanishingIdeal_eq_span_coord` (Incidence.lean:69) — the
   equation-count engine of the whole incidence chain; smallest ticket — **START
   HERE**. Proof: `le_antisymm` on spans; (≤) for `φ : Module.Dual R M`, expand
   `σ = Σᵢ (b.repr σ i) • b i` so `φ σ = Σᵢ φ (b i) • (b.coord i σ)` ∈ span of the
   coord-values; (≥) each `b.coord i` is itself a dual functional.
2. **T-D3b** `IdealSheafData.mul` — affine-open-wise ideal product; gluing condition
   via `Ideal.map_mul` (decomposition-km1 D-off.2). Gateway to T-D3.
3. **T-D29** charpoly-as-norm: `LinearMap.charpoly f = Algebra.norm R[T] (T•1 − f⊗1)`
   (same matrix det over `R[T]`). Self-contained; feeds T-D30/KM 1.8.2.
4. **T-D24** finrank additivity in SES of finite free modules (localise + glue);
   feeds degree additivity (D-curve.3).
5. **T-D25** rank-1 locally free algebra ⟹ `algebraMap` iso (feeds KM 1.2.7) ·
   **T-D26** degree-0 effective divisor is empty (feeds T-D15) · **T-D27** zero-locus
   over `W` of a module = zero-locus over `S` of its f.l.f. pushforward (feeds
   T-D16(3)).
6. **T-D31** reduced-ring evaluation separation for `MvPolynomial` (feeds T-D2) ·
   **T-D32** f.l.f.-map iso ⟺ geometric-fibre iso via `LinearMap.det` unit-locus
   (feeds T-D6 (3)⟺(5)).

**Wave 1 — scheme-side plumbing + the two proofs-in-hand theorems (parallel).**
- **T-D12** (+**T-D20**): `baseChange.finite/flat/lfp` via mathlib base-change
  stability instances + the `Scheme.Hom.ker`/`ker_subschemeι` dictionary; then flat
  pullback + composition laws (D-off.3). Unlocks every universality argument.
- **T-D2** `isFullSetOfSectionsAlg_iff_fields` (KM 1.9.1/1.9.2, proofs in hand):
  coefficient comparison of degree-N forms in `R[T₁..T_N]` + T-D31; `Algebra.norm`
  base-change (verify name; else via `LinearMap.det` + matrix ⊗).
- **T-D22** (+**T-D23**) HB-REGIMM: section of separated smooth rel-dim-1 curve is a
  closed immersion with locally principal nzd ideal — étale-local 𝔸¹ route
  (D-curve.1 (a)–(c); GME p. 107 quotable). The engine for T-D3. T-D23 (closed point
  of smooth curve over a field has DVR local ring) alongside.

**Wave 2 — DS4a discharge.**
- **T-D3**: single-section divisor from T-D22 → `sectionsDivisor` := fold of
  `IdealSheafData.mul` (T-D3b) → `sectionsDivisor_degree` (T-D24 + degree-1 of a
  section) → **STATE + prove the base-change spec `sectionsDivisor_baseChange`**
  (formation commutes with base change — the register's second pin, currently
  missing from the skeleton; adding it is in-scope for T-D3, not a statement change).
  Then **CLEANUP-5** (CartierDivisor.lean; deps T-D2+T-D3) unblocks.

**Wave 3 — incidence chain (KM 1.3; mostly sequential).**
- **T-D14** `exists_incidenceLocusLE` (KM 1.3.4; proof transcribed, D-inc.2):
  incidence = zero locus of `f̄ ∈ B′` (rank-d′ locally free) = `sectionVanishingIdeal`
  glued over an affine cover; small lemma `sectionVanishingIdeal_unit_smul` en route.
  Pull the verbatim KM 1.3.4 statement quote (preview pp. 12–13, IN HAND) into the
  decomposition at pickup (attack-log QUOTE-MISSING #7).
- **T-D15** EQ-locus via T-D14 + T-D26 → **CLEANUP-9** (Incidence.lean).
- **T-D16** subgroup locus (KM 1.3.7 verbatim + proof in hand): three loci
  (`[e] ≤ D`; `D = inv*D` via T-D20; `[m(P₁,P₂)] ≤ D_W` over `W = D ×_S D` via
  T-D27); tautological-pair universality per D-inc.3(c).
- **T-D17/T-D18** instances over the Hom-scheme (`E.torsion N` / the pullback
  square): universal point = transported `𝟙`, multiples via Point-group, T-D16 over
  that base, classifying-map equivalence by `pullback.lift` uniqueness (D-inc.4).
  Pull KM 1.6.2/1.6.3/1.6.5 statement quotes (pp. 22–25, IN HAND; QUOTE-MISSING #6).
  → **CLEANUP-10**. These two feed milestones T-E7/T-E9 directly.

**Wave 4 — KM 1.4.4 theorems.**
- **T-D6** (1)⟺(3) per the transcribed steps (§KM 1.4.4 of decomposition-km1).
  Stream-B coupling: (2)⟹(3) consumes E[N] finite étale of rank N² (T-B4/T-B5); if
  B hasn't landed, do the (3)⟺(4)/(3)⟺(5) legs first (T-D32 + KM 1.8.3) and leave
  the B-edge last. **T-D7** (1)⟺(4) with/after it. → **CLEANUP-6** (ExactOrder.lean;
  fold T-D5 in only if OT has landed).
- **T-D9** — thin wrapper over T-D6 (def-level killing clause already applied);
  golf-sized. **T-D8** Γ(N) version: workable for lemmas but **⧗KM (KM 3.7)** — may
  NOT be closed until the full KM text lands (do-not-formalize-from-memory gate).
  → **CLEANUP-7** (Basic.lean final).

**Parked / gated (do not start until the gate opens):**
- **T-D5** — stream OT (Deligne/Oort–Tate; T-OT0 after T-SG1). Statement frozen.
- **T-D10** — definition of record = T-SG2 (fppf-local cyclicity). GATE: no Γ₀
  representability against the `IsGammaZero` surrogate.
- **T-D1/T-D19** — AG-LB. T-D11's working-definition half (affine-local official
  predicate + Zariski-locality + T-D23 equivalence) is workable before AG-LB; the
  (L,ℓ)-half is not.
- **T-D21/T-D28/T-D30** — phase 2; T-D30 becomes cheap after T-D29.

### Worker bootstrap (fresh agent, zero context)

1. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`, branch
   `dev/modular-curves` (LOCAL-ONLY: upstream is `origin/main`, there is no remote
   dev branch — do not create one without owner say-so). Read, in order: this
   section; `decomposition-km1.md`; `decompose-attacks-2026-07-06/
   level-structures.md`; `plan.md` §DATA-SORRY register.
2. Claim exactly ONE ticket per rule 5 (top of this file): add the Claimed line, set
   Status, commit `tickets.md` ALONE — before touching any `.lean`. Sibling workers
   are live in this shared worktree (T-B2 live and T-A3 freshly done at time of
   writing): `git add` only your own files, never `-A`.
3. New helper statements: `:= by sorry` skeleton first (module builds green), attack
   block recorded, then prove. Board statements are FROZEN — a wrong statement is a
   B2 report (`b2_log.jsonl`), never a silent edit.
4. Verify per standing rule 3: `lake build` (one module at a time, from the worktree
   root) green; your declaration sorry-free; `#print axioms` = the standard three +
   registered `sorryAx` deps (list them in the closing note); no `maxHeartbeats`.
   Tooling caution: `lake build` is the sole build authority on this machine (the
   lean-lsp MCP build/goal/hover tools have caused toolchain-skew breakage here; its
   network search tools — loogle/leansearch — are safe).
5. Mark done per rule 5 (`Status: done (<worker>, <start> → <end>)` in the same
   commit as the final proof); take the next wave item.


---

## Amendments v6 (2026-07-06): ★ Stream-Q claim + execution work order (beastmode-Q)

*Stream Q (finite quotients, `ForMathlib/` + later `Moduli/`) claimed by
**beastmode-Q**, 2026-07-06T15:16Z. This section is the Q-lane execution plan (the v2
one-liners T-Q1–T-Q7 get their full /develop-template bodies here; the stream star
reserves the lane and records the plan — tickets are still claimed ONE at a time per
rule 5). Source of record: [Loe] Prop 3.6.1 p. 17, verbatim in `decomposition.md`
§E4 and re-read from `refs/ModularCurves/modcurvesnotes.pdf` at claim time:*

> **Proposition 3.6.1.** Let X be a quasiprojective S-scheme (for some base scheme
> S), and let G be a finite group acting on X by S-automorphisms. Then there exists a
> unique S-scheme X/G and a unique morphism X → X/G representing the functor
> Y ↦ (homs. of S-schemes X → Y commuting the the G-action).
> *Proof.* Uniqueness is obvious (representing a functor). Existence: for X = Spec(A)
> affine, Spec(A^G) works, and one can show that these patch nicely. (One needs
> quasiprojectiveness and finiteness of G here.)

*Proof route for the affine case (T-Q3, "Spec(A^G) works"): the standard argument
(SGA I V.1.1 / Stacks 07S3–07S7 shape; Loeffler's "one can show"): π : Spec B →
Spec B^G is integral + surjective with fibres = G-orbits; every invariant morphism
f : Spec B → Y descends affine-locally on Y via invariant basic opens (closedness of
π + basic-open basis) and the key algebra lemma (B_h)^G = (B^G)_h for invariant h,
finite G; uniqueness from surjectivity + Γ-injectivity on basic opens. Mathlib
inventory verified at claim (pin 11b908e5cdd9): `FixedPoints.subalgebra` +
`SMulCommClass G (FixedPoints.subalgebra A B G) B` (Subalgebra/Operations.lean),
`Algebra.IsInvariant` + `.isIntegral` + `exists_smul_of_under_eq` +
`orbit_eq_primesOver` (RingTheory/Invariant/Basic.lean), `RingHom.IsIntegral.
comap_surjective` + `PrimeSpectrum.isClosedMap_comap_of_isIntegral`
(Spectrum/Prime/Topology.lean), `IsIntegralHom` + `Spec.map φ`-iff
(Morphisms/Integral.lean:90), `Spec.homEquiv` (GammaSpecAdjunction.lean:569),
`Scheme.OpenCover.glueMorphisms`/`.hom_ext` (Gluing.lean:439/451),
`MulSemiringAction.toRingHom`/`toRingEquiv` (Ring/Action). CONFIRMED ABSENT from
mathlib (the gap is real): any `MulSemiringAction` contact with `AlgebraicGeometry`
(zero files), localization-of-invariants, scheme quotients by finite groups.*

### Q-lane design decisions (recorded once, binding for the lane)

- **Setting**: `G` a group (finiteness only where used, marked `[Finite G]`),
  `B : Type u` a `CommRing`, `[MulSemiringAction G B]`; base ring `R` with
  `[Algebra R B] [SMulCommClass G R B]` (= "G acts by R-algebra automorphisms";
  R := ℤ recovers the absolute case). Invariants `A := FixedPoints.subalgebra R B G`.
- **Action convention**: `specSMul g := Spec.map (ofHom (MulSemiringAction.toRingHom
  G B g))` — NO inverse in the definition; composition law is covariant-in-≫
  (`specSMul (g*h) = specSMul g ≫ specSMul h`); on points it is `PrimeSpectrum.comap
  (toRingHom g)` (= the classical g⁻¹-action on primes). Invariance statements
  (`∀ g, specSMul g ≫ f = f`) are convention-independent. An `Aut`-bundled
  (anti)hom is deliberately NOT provided now (cleanup/generalise can add it).
- **Universal property stated absolutely** (target `Y : Scheme`, plain `Scheme`
  category, ∃!-form) — the S-relative form of [Loe] 3.6.1 follows formally
  (uniqueness through π applied to the two factorizations of the structure map) and
  is deferred to T-Q5/T-Q6 where `Over S` packaging is actually consumed.
- **Files (all NEW, upstream candidates, OURS register)**:
  `ForMathlib/SpecGroupAction.lean` (T-Q1) → `ForMathlib/InvariantLocalization.lean`
  (T-Q3a/b/c, pure algebra, no scheme imports) → `ForMathlib/AffineQuotient.lean`
  (T-Q3). Attack blocks: `decompose-attacks-2026-07-06/q-lane.md` (per statement,
  before proving — standing rule 1).
- **On-target check**: stream Q = plan.md API gap **AG-QUOT** (blocks KM 4.7 ⇐
  = T-E5, coarse Y₀(N) = T-M2, Y(ρ̄) twists = T-F4); reviewer split recorded in
  §Amendments v2. Within the project's mathematical area (arithmetic moduli
  machinery); refinement, not divergence.

### [T-Q1] Spec-side action vocabulary — PROVABLE NOW
- **Status**: done (beastmode-Q, 2026-07-06T15:16Z → 2026-07-06T15:40Z) ·
  **Claimed**: beastmode-Q, 2026-07-06T15:16Z
- **File**: ModularCurves/ForMathlib/SpecGroupAction.lean (NEW) · **Parent**: stream Q
  (v2 one-liner) · **Type**: def + lemmas · **Depends on**: none · **Parallel**: yes
- **Statement** (decls to create; skeleton `sorry`-free where trivial):
  `specSMul (g : G) : Spec (.of B) ⟶ Spec (.of B)` := `Spec.map (ofHom (toRingHom G B
  g))`; laws `specSMul_one` (= 𝟙), `specSMul_mul` (`specSMul (g*h) = specSMul g ≫
  specSMul h`), `instance IsIso (specSMul g)`; point formula `specSMul_base`
  (= `PrimeSpectrum.comap (toRingHom G B g)`);
  `invariantsπ : Spec (.of B) ⟶ Spec (.of (FixedPoints.subalgebra R B G))` :=
  `Spec.map (ofHom (algebraMap A B))`; `specSMul_invariantsπ : specSMul g ≫
  invariantsπ = invariantsπ`; `instance Algebra.IsInvariant R-fixed-subalgebra`
  (trivial, mathlib-shaped); `invariantsπ_isIntegralHom [Finite G]`;
  `invariantsπ_surjective [Finite G] : Function.Surjective invariantsπ.base`;
  `invariantsπ_base_eq_iff [Finite G] : invariantsπ.base x = invariantsπ.base y ↔
  ∃ g, (specSMul g).base x = y` (fibres are orbits).
- **Proof sketch**: (1) laws from `Spec.map_comp/map_id` + `toRingHom` mul/one
  (compute: `toRingHom (g*h) = (toRingHom g).comp (toRingHom h)`, Spec.map flips ≫);
  (2) invariance: `algebraMap A B` composed with `g•` is itself (`smul` fixes A
  elementwise — `val_smul`-style), so the ring triangle commutes, apply `Spec.map`;
  (3) `IsInvariant`: `⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩`; (4) integrality:
  `Algebra.IsInvariant.isIntegral` + `IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral`;
  (5) surjectivity: `RingHom.IsIntegral.comap_surjective` + `Subtype.val`-injectivity
  + `Spec.map`-base = comap dictionary; (6) orbits: `Algebra.IsInvariant.
  exists_smul_of_under_eq` (SMulCommClass instance present in mathlib) + the
  point-formula dictionary between `PrimeSpectrum.comap (toRingHom g)` and the
  pointwise ideal action `g • ·` (comap of the g-hom = g⁻¹ • as ideals; both
  directions of the iff by replacing g ↦ g⁻¹).
- **Mathlib lemmas** (names verified at claim): `MulSemiringAction.toRingHom`,
  `Spec.map_comp`, `Spec.map_id`, `FixedPoints.subalgebra`,
  `Algebra.IsInvariant.isIntegral`, `Algebra.IsInvariant.exists_smul_of_under_eq`,
  `RingHom.IsIntegral.comap_surjective`, `AlgebraicGeometry.IsIntegralHom` spec-iff
  (Morphisms/Integral.lean:90), `Ideal.smul` pointwise (scoped `Pointwise`).
- **Sources**: [Loe] 3.6.1 (above); SGA I V.1.1; Stacks 07S3 (topology of the orbit
  map). Generality: arbitrary `Group G`, `CommRing B`, base via `SMulCommClass`.
- **Progress**:
  - 2026-07-06T15:16: claimed; work order banked; attack block next
    (q-lane.md), then skeleton.
  - 2026-07-06T15:25: attack block SURVIVED (6+3 attacks, q-lane.md — binding
    orientation notes A1/A4: two contravariance flips cancel; orbit iff needs
    g ↦ g⁻¹ reindex). Skeleton green (7 sorries).
  - 2026-07-06T15:40: DONE — all 7 proofs closed first pass. Delivered (namespace
    `AlgebraicGeometry`): `specSMul` + `_one`/`_mul`/`IsIso`/`_apply`/
    `_apply_asIdeal` (comap (toRingHom g) = g⁻¹ • ·, via
    `Ideal.mem_inv_pointwise_smul_iff` — NO toRingAut needed), tautological
    `Algebra.IsInvariant (FixedPoints.subalgebra R B G) B G` instance,
    `invariantsπ` + `specSMul_invariantsπ` (@[reassoc (attr := simp)];
    membership proof is literally `a.2 g`), `invariantsπ_isIntegralHom`
    (`IsIntegralHom.SpecMap_iff` + `Algebra.isIntegral_def` +
    `Algebra.IsInvariant.isIntegral`), `invariantsπ_surjective`
    (`RingHom.IsIntegral.comap_surjective` + `Subtype.val_injective` — needs
    the explicit `have hint : (algebraMap …).IsIntegral` ascription, field
    projection off the ∀-form fails), `invariantsπ_apply_eq_iff` (renamed from
    `_base_eq_iff` — mathlib now uses the `Scheme.Hom` DFunLike coercion;
    `Scheme.Hom.comp_apply` NOT `Scheme.comp_apply`). Axioms: standard three on
    all 7. Zero warnings. GOTCHAS OF RECORD: `Spec.map_apply` is rfl;
    `exists_smul_of_under_eq` orientation is `Q = g • P`; `Ideal.under` is an
    abbrev (congrArg PrimeSpectrum.asIdeal lands defeq-on-target). Post-proof
    cleanup: DEFERRED (owner paused cleanup passes 2026-07-06T14:05Z; debt
    tracked for the cleanup lane, same as T-D31/T-D32).

### [T-Q3a] Localized action ring homs at an invariant element
- **Status**: done (beastmode-Q, 2026-07-06T15:45Z → 2026-07-06T15:50Z) ·
  **Claimed**: beastmode-Q, 2026-07-06T15:45Z
- **File**: ModularCurves/ForMathlib/InvariantLocalization.lean
  (NEW) · **Parent**: T-Q3 · **Type**: def + lemmas · **Depends on**: none
  (pure algebra; parallel with T-Q1)
- **Progress** (2026-07-06T15:50, includes T-Q3b + T-Q3c(i)(ii) — whole file in one
  pass, attack blocks in q-lane.md, all SURVIVED):
  - Delivered (namespace `MulSemiringAction`): `powers_le_comap_toRingHom`,
    `awayHom` (:= `IsLocalization.map` at `toRingHom g`; MonoidHom-into-RingAut
    bundling deliberately NOT used — structure-field route with a private
    `mk'_congr` helper), `awayHom_algebraMap`/`_mk'`/`_mk'_pow`/`_one`/`_mul`,
    `away : MulSemiringAction G (Localization.Away h)` (@[implicit_reducible] def,
    letI-consumed, IsFractionRing.mulSemiringAction precedent).
  - SCOPE NOTE: the promised `SMulCommClass G R (Localization.Away h)` NOT stated —
    only needed by the (iii) subalgebra packaging, deferred with it (see T-Q3c).
  - GOTCHAS OF RECORD: `MulSemiringAction.toRingHom` has NO `_apply` simp lemma
    (defeq only — use `show`); the pow lemma is `smul_pow'` (`smul_pow` is the
    `r^n • x^n` one); structure-field proofs via `IsLocalization.map_unique` with
    `_` holes cause whnf/isDefEq heartbeat blowups — standalone `awayHom_*` lemmas
    first, then field-assign; `map_mk'`'s RHS denominator must be type-ascribed
    `(⟨…⟩ : Submonoid.powers h)` in re-statements or the unifier grabs the comap
    form; `rw` into a subtype component is a dependent-motive error — `show` both
    sides down to `Subtype.val` form first; `mk'_cancel` args need the
    `(⟨…⟩ : Submonoid.powers h)` ascription (M is a metavariable at elab time).
  - Axioms: standard three on all decls. Zero warnings. Post-proof cleanup:
    DEFERRED (owner pause, same as T-Q1/T-D31/T-D32).
- **Statement**: for `h : B` with `hfix : ∀ g : G, g • h = h`, package the induced
  action on `Localization.Away h` as an honest `noncomputable def
  MulSemiringAction.away : MulSemiringAction G (Localization.Away h)` (NOT an
  instance — consumers `letI` it), with `smul g := IsLocalization.Away.map _ _
  (toRingHom G B g) h`-transported; specification lemmas: `away_smul_mk`
  (`g • (b /ₘ h^n) = (g • b) /ₘ h^n` in `mk'` form), and (with the def in scope)
  `smul_algebraMap_away : g • algebraMap B (Localization.Away h) b = algebraMap _ _
  (g • b)`; `SMulCommClass G R (Localization.Away h)` under the standing R-compat.
- **Proof sketch**: `IsLocalization.Away.map` at `toRingHom g` (sends powers of h to
  powers of h since `g • h = h`); action laws (one, mul) via `IsLocalization.
  ringHom_ext` uniqueness against generators; `away_smul_mk` from
  `IsLocalization.map_mk'`.
- **Mathlib**: `IsLocalization.Away.map`, `IsLocalization.map_mk'`,
  `IsLocalization.ringHom_ext`, `Localization.Away`. Generality: any Group G (no
  finiteness), any invariant h.
- **Sources**: standard (localization functoriality); the lemma cluster is the
  algebra backend of [Loe] 3.6.1's "patch nicely".

### [T-Q3b] Fixed elements of the localization come from invariants over a power
- **Status**: done (beastmode-Q, 2026-07-06T15:45Z → 2026-07-06T15:50Z, with T-Q3a)
- **File**: ForMathlib/InvariantLocalization.lean · **Parent**:
  T-Q3 · **Type**: lemma · **Depends on**: T-Q3a
- **Progress**: `exists_fixed_mk'_eq_of_forall_awayHom_eq` — stated via `awayHom`
  (instance-free); proof exactly per sketch (mk'_eq_iff_eq + eq_iff_exists at each
  g, `choose` + `Finset.univ.sup` for the uniform power, h^M-bump for the invariant
  numerator, `mk'_cancel` finish). ROUTE NOTE: the mk'_spec/congrArg-cancellation
  route FAILS (the multiplier `algebraMap (h^N)` never matches `algebraMap ↑y`
  patterns — elaborator pre-reduces the coercion); `IsLocalization.mk'_eq_iff_eq`
  is the right cancellation lemma. Axioms standard; see T-Q3a note.
- **Statement**: `[Finite G]`, `h` invariant, `x : Localization.Away h` with
  `∀ g, g • x = x` (T-Q3a action) → `∃ (b : B) (n : ℕ), (∀ g, g • b = b) ∧
  IsLocalization.mk' _ b (⟨h^n, _⟩) = x` (single conclusion; exact `mk'` spelling
  pinned at skeleton time).
- **Proof sketch**: write `x = mk' b (h^N)` (`IsLocalization.mk'_surjective`); for
  each g, `mk' (g•b) (h^N) = mk' b (h^N)` (via `away_smul_mk`), so `∃ m_g, h^{m_g} *
  (g•b − b) = 0` (`IsLocalization.eq_iff_exists` in `Away`-form); `G` finite ⟹ one
  `m ≥ all m_g`; set `b' := h^m * b`: then `g • b' − b' = h^m*(g•b − b) = 0`
  (h fixed), so `b'` invariant and `x = mk' b' (h^{N+m})`. NO averaging, NO |G|⁻¹ —
  works over any base (this is the reason the lemma is not in mathlib's
  field-flavoured fixed-point theory).
- **Mathlib**: `IsLocalization.mk'_surjective`, `IsLocalization.eq_iff_exists` (or
  `mk'_eq_iff`), `smul_sub/smul_mul'` bookkeeping. Sources: SGA I V.1.1 (i); Stacks
  07S5 first display.

### [T-Q3c] Localization of the invariants inclusion: injective, range = fixed, IsLocalization
- **Status**: done (beastmode-Q, 2026-07-06T15:45Z → 2026-07-06T15:55Z; (iii)
  DEFERRED into T-Q3 per the attack-block scope note)
- **File**: ForMathlib/InvariantLocalization.lean · **Parent**:
  T-Q3 · **Type**: lemmas (3 single-conclusion decls) · **Depends on**: T-Q3a, T-Q3b
- **Progress**: (i) `fixedPoints_awayMap_injective` (elementwise via
  `mk'_eq_zero_iff` + `Subtype.ext`; statement spelled with `IsLocalization.map` +
  `Submonoid.powers_le_comap_algebraMap`, NOT `Away.map` — the `Away (algebraMap h)`
  instance does not fire syntactically on `Away ↑h`); (ii)
  `mem_range_fixedPoints_awayMap_iff` (⊆ via `map_mk'`+`awayHom_mk'`+`mk'_congr`;
  ⊇ via T-Q3b + `map_mk'`); (iii) the `IsLocalization.Away (h:A) ((B_h)^G)`
  packaging DEFERRED — zero mathematical content beyond (i)+(ii), build it inside
  T-Q3's assembly only if the factorization step wants it (attack A3 note). Axioms
  standard three on both. Zero warnings.
- **Statement** (A := FixedPoints.subalgebra R B G; `h : A`; localized inclusion
  `awayIncl := IsLocalization.Away.map (Localization.Away h) (Localization.Away
  (h:B)) (algebraMap A B) h`):
  (i) `Function.Injective awayIncl`;
  (ii) `RingHom.range awayIncl = {x | ∀ g, g • x = x}`-as-subring (T-Q3a action;
  `[Finite G]` for ⊇);
  (iii) packaged: `IsLocalization.Away (h : A) (FixedPoints.subalgebra R
  (Localization.Away (h:B)) G)` — algebra structure via `codRestrict` of
  `awayIncl`-composition; `[Finite G]`.
- **Proof sketch**: (i) elementwise: `a/h^n ↦ 0` ⟹ `∃ m, (h:B)^m * a = 0` in B ⟹
  same equation in A (val injective) ⟹ `a/h^n = 0`; or mathlib
  `IsLocalization.map_injective_of_injective` if signature fits (verify at pickup).
  (ii) ⊆: image elements are fixed (T-Q3a `away_smul_mk`, invariant numerator +
  invariant denominator); ⊇: T-Q3b gives `x = mk' b' (h^m)` with b' invariant =
  image of `mk' ⟨b'⟩ ⟨h^m⟩`. (iii) characteristic predicate: `map_units` (image of
  h is a unit whose inverse is fixed — inverse of a fixed unit is fixed by
  uniqueness), `surj` = (ii)⊇-computation, `exists_of_eq` from B-level
  `exists_of_eq` + val-injectivity.
- **Mathlib**: `IsLocalization` characteristic predicate fields, `RingHom.
  codRestrict`, `IsUnit` inverse-uniqueness. Sources: as T-Q3b.

### [T-Q3] Affine quotients: `Spec(A^G)` universal property — HEADLINE (v2 one-liner)
- **Status**: in_progress · **Claimed**: beastmode-Q, 2026-07-06T15:58Z
- **File**: ModularCurves/ForMathlib/AffineQuotient.lean (NEW) ·
  **Type**: theorem ×3 · **Depends on**: T-Q1, T-Q3a, T-Q3b, T-Q3c
- **Route lock (claim-time design, binding unless B2)**: (α) pure-algebra
  factorization lemma first (`∃! ψ : C →+* (A)_a` under fixed image, via T-Q3c
  (i)+(ii) + `RingEquiv.ofInjective`); (β) uniqueness stated in TRANSPORTABLE form
  (against an arbitrary open immersion `j : W ⟶ Spec A` via `pullback π j`, NOT
  only W = ⊤) so the existence-glue compat on `pullback (ι_p) (ι_q)` is uniqueness
  at the overlap — this dodges the deferred T-Q3c(iii) invariants-of-products
  identification entirely; (γ) existence per-point via closedness
  (`PrimeSpectrum.isClosedMap_comap_of_isIntegral`) + basic-open basis +
  `IsOpenImmersion.lift` into an affine chart + (α), glued by
  `Scheme.OpenCover.glueMorphisms` with (β) discharging compat.
- **Statement** (all `[Finite G]`):
  (i) `invariantsπ_hom_ext {Y : Scheme} (h₁ h₂ : Spec (.of A) ⟶ Y)
  (H : invariantsπ ≫ h₁ = invariantsπ ≫ h₂) : h₁ = h₂` (+ corollary
  `Epi invariantsπ`);
  (ii) `exists_invariantsπ_lift {Y : Scheme} (f : Spec (.of B) ⟶ Y)
  (hf : ∀ g, specSMul g ≫ f = f) : ∃ q, invariantsπ ≫ q = f`;
  (iii) `invariantsπ_existsUnique …` : the ∃!-assembly (one-line ⟨⟩ from (i)+(ii)) —
  [Loe] 3.6.1's "representing the functor", affine case, absolute form.
- **Proof sketch** (SGA I V.1.1 / Stacks 07S7; fully explicit):
  *(uniqueness)* base maps agree (`invariantsπ_surjective`); for any affine open
  `V ⊆ Y`, `W := h₁ ⁻¹ᵁ V = h₂ ⁻¹ᵁ V`; cover W by basic opens `D_A(a)`; each
  restriction factors through `V` (IsOpenImmersion.lift), giving affine-to-affine
  morphisms = ring maps `Γ(V) → Γ(D_A a) ≅ (A)_a`; postcompose with the INJECTIVE
  `(A)_a → (B)_a` (T-Q3c(i) at the invariant element a — note `a : A` is by
  definition invariant): the composites agree (they compute `f`-restricted), so the
  ring maps agree, so `h₁|_{D(a)} = h₂|_{D(a)}` (`Spec.homEquiv`-injectivity
  transported through `IsAffineOpen`); conclude by `Scheme.OpenCover.hom_ext` on the
  cover `{D_A(a)} ∪ (complement handled by W covering h₁⁻¹V as V ranges)`.
  *(existence)* for `p : Spec A`: the fibre `π⁻¹(p)` is one G-orbit
  (`invariantsπ_base_eq_iff`) and `f` is constant on it (apply `hf` at points); let
  `y_p := f(any fibre point)`, pick affine `V_p ∋ y_p`, `U := f ⁻¹ᵁ V_p ⊇ π⁻¹(p)`
  open; π closed (`isIntegralHom` ⟹ closed base map, or `PrimeSpectrum.
  isClosedMap_comap_of_isIntegral` directly): `Z := π(Uᶜ)` closed, `p ∉ Z`; basic
  opens form a basis: `∃ a : A, p ∈ D_A(a) ⊆ Zᶜ`, then `π ⁻¹ᵁ D_A(a) = D_B(a) ⊆ U`
  (`Scheme.preimage_basicOpen`); restrict: `f| : Spec B_a-as-D_B(a) ⟶ V_p` affine
  target ⟹ ring hom `φ : Γ(V_p) →+* (B)_a` (Spec.homEquiv + IsAffineOpen
  dictionaries); invariance `hf` restricted to `D_B(a)` says every `φ c` is fixed
  for the T-Q3a action ⟹ (T-Q3c(ii)) φ factors through the range of the injective
  `(A)_a → (B)_a` ⟹ `φ' : Γ(V_p) →+* (A)_a` ⟹ `q_p : D_A(a) ⟶ V_p ⟶ Y` with
  `π| ≫ q_p = f|`; glue: the `D_A(a_p)` cover Spec A; on an overlap `D_A(a) ∩
  D_A(a') = D_A(a*a')` both restrictions factor `f|` through `π|_{D(aa')}`, which is
  again an invariants-π up to the T-Q3c(iii) identification (`IsLocalization.Away
  (aa') ((B_{aa'})^G)`) — so they agree by (i) applied at the localized instance
  (this is why (i) is stated over arbitrary (B,G,R) FIRST); glue by
  `Scheme.OpenCover.glueMorphisms`, factorization `π ≫ q = f` checked on the cover
  `D_B(a_p)` of Spec B by `Scheme.OpenCover.hom_ext`.
- **Mathlib**: `Scheme.OpenCover.glueMorphisms`/`hom_ext`/`ι_glueMorphisms`,
  `IsOpenImmersion.lift` (+ `lift_fac`), `Spec.homEquiv`, `Scheme.preimage_
  basicOpen`, `PrimeSpectrum.isBasis_basic_opens`, `IsAffineOpen.isLocalization_
  basicOpen` + `IsAffineOpen.fromSpec` (dictionary D(a) ≅ Spec of localization —
  exact spelling verified at pickup), `PrimeSpectrum.isClosedMap_comap_of_
  isIntegral`. Sources: [Loe] 3.6.1 (verbatim above); SGA I V.1.1; Stacks 07S5/07S7.
- **Generality**: `[Finite G]`, arbitrary `CommRing B`, arbitrary target scheme
  (NOT restricted to S-schemes; NOT quasi-projective — that hypothesis is only
  needed for the GLUING of affine quotients, T-Q5).

### Rest of the lane (bodies cut when reached; one-liners stand)
- **[T-Q2]** free actions vs stabilizers — statements only; needed by KM Ch. 7
  regularity, NOT by T-Q3/T-E5. After T-Q3.
- **[T-Q4]** base change of invariants — KM Ch. 7 appendix ("base change for rings
  of invariants") — **full KM text NOW IN refs/** (`katz-mazur-arithmetic-moduli-
  FULL.pdf`); read the appendix at pickup (quote-gate), decide the flat/finite-free
  hypotheses honestly. Feeds T-Q6 and the Y(ρ̄) twist route.
- **[T-Q5]** gluing affine quotients (quasi-projective case; [Loe] 3.6.1 full
  statement): orbits-in-affines via quasi-projectivity; glue the `Spec(A_i^G)`;
  S-relative + `Over S` packaging of the universal property.
- **[T-Q6]** quotients of rigidified moduli problems (KM 4.7 ⇐ engine; T-E5).
- **[T-Q7]** coarse quotient statements (`Y₀(N)`, `Y(1)`) — via groupoid layer (D6),
  phase M; consumes T-Q5 + T-M1/T-M2 vocabulary.
- **[CLEANUP-12]** (already on the board, v2 cadence): quotient stream after
  T-Q3+T-Q4+T-Q5 — covers the three new ForMathlib files.
