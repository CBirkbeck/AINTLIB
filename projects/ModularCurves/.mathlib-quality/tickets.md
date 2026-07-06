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
- **Status**: open · **File**: WeierstrassModel.lean · `isWeierstrassModel_unique`
- **Depends on**: T-A2 · **Parallel**: with T-A3 · **Type**: theorem
- **Sketch**: KM 2.2.5-route: both models are pointed smooth proper genus-1; RR
  black-box gives Weierstrass coordinates; two Weierstrass presentations differ by a
  `VariableChange`; transport. Quote-gate: KM 2.2.5 (full text needed); interim source
  Hida GME §2.2 (mine quote when cut).
- **Sources**: [KM] 2.2.5 ⧗ · [Hida-GME]. **Generality**: `CommRing R`.

### [T-A5] Base change of elliptic curves (Prop fields)
- **Status**: in_progress (beastmode 2026-07-06T22:30Z — smooth+proper DONE via
  MorphismProperty.pullback_snd (SmoothOfRelativeDimension stability instance needs
  explicit summoning); `fibres` remains: sub-tickets T-A5a (projModel base-change,
  the real content) + T-A5b (fibre pasting) spawned with sketches) · **File**: EllipticCurve/Basic.lean · `EllipticCurve.baseChange`
  (three Prop sorries) · **Depends on**: none · **Parallel**: yes · **Type**: lemma
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
- **Status**: open · **File**: EllipticCurve/GroupLaw.lean (or Basic)
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
- **Status**: open · **File**: Torsion.lean · `torsionπ_isFinite`, `torsionπ_flat`,
  `torsion_rank` · **Depends on**: T-B3; fibrewise degree input (HasseWeil/mathlib
  fibre theory) · **Parallel**: with T-B5 · **Type**: theorems
- **Sketch**: `[N]` proper + quasi-finite ⟹ finite (mathlib ZMT
  `IsFinite.of_isProper_of_locallyQuasiFinite` — verified present); fibrewise flatness
  criterion (BB-FLAT, stated black box) + fibre degree `N²` (Silverman III.6.2(d);
  fibre anchor: HasseWeil `mulByInt_degree`).
- **Sources**: [KM] 2.3.1 ⧗ · EGA IV 11.3.10 · [Sil] III.6.2.

### [T-B5] [N] étale when N invertible (+ E[N] finite étale)
- **Status**: open · **File**: Torsion.lean · `mulBy_etale`, `torsionπ_etale`
- **Depends on**: invariant-differential input only (v2: not the Abel chain) · **Parallel**: with T-B4 · **Type**: theorems
- **Sketch**: [Loe] 3.4.2(2) verbatim route: `[N]` multiplies the invariant
  differential by `N` ⟹ iso on (co)tangent ⟹ formally étale; + lfp. Needs the
  invariant-differential API (sub-ticket if mathlib's `Ω¹` for schemes is insufficient
  — check `RingTheory.Kaehler` sheafification status first).
- **Sources**: [Loe] Lemma 3.4.2(2) (quote in decomposition).

### [T-B6] Fibre comparison: E[N] geometric fibres ≅ (ℤ/N)² (reuse HasseWeil)
- **Status**: in_progress · **Claimed**: beastmode-B (stream-B worker),
  2026-07-06T11:30Z · **New file**: EllipticCurve/TorsionFibre.lean (B-lane owned) ·
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
- **Status**: open · **File**: CartierDivisor.lean ·
  `isFullSetOfSectionsAlg_iff_fields` · **Depends on**: none · **Parallel**: yes ·
  **Type**: theorem
- **Sketch**: KM 1.9.2's proof (in hand, quoted in decomposition): reduce to reduced
  `R`; equality of two elements of a reduced ring checked at geometric points of
  `Spec R[T₁..T_N]`; norm commutes with base change (`Algebra.norm` base-change lemma —
  verify name; else prove via `LinearMap.det` and `Matrix` base change).
- **Sources**: [KM] 1.9.1–1.9.2 with proofs (IN HAND).

### [T-D3] Divisor sums Σ[Pᵢ] (DS4a discharge)
- **Status**: open · **File**: CartierDivisor.lean · `sectionsDivisor`,
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
- **Status**: open · **File**: ExactOrder.lean · `HasExactOrder.smul_eq_zero` ·
  **Depends on**: T-D3 · **Type**: theorem · **Sources**: [KM] 1.4.2 (IN HAND,
  verbatim in decomposition); black box BB-DELIGNE stated as its own lemma first.

### [T-D6] KM 1.4.4 (1)⇔(3): Drinfeld = naive when N invertible
- **Status**: open · **File**: ExactOrder.lean · `hasExactOrder_iff_geometric` ·
  **Depends on**: T-D3, T-B4 · **Parallel**: with T-D7 · **Type**: theorem
- **Sketch**: KM's proof IN HAND (preview pp. 18–19): (1)⟹(2) base change; (2)⟹(3)
  rank-N étale subgroup over field has N distinct points; (3)⟹(1) via (4). Attack
  obligation from decomposition D5 (killed-by-N hypothesis placement) must be resolved
  first — if the skeleton form is inequivalent, B2-report (do NOT silently edit).
  **RESOLVED 2026-07-06 (v5)**: the adversarial pass added the standing hypothesis
  `hkill : (N : ℤ) • P = 0` to the skeleton (ExactOrder.lean:85, docstring records the
  `ℚ̄[ε]` counterexample); same for T-D7 (line 96). Both are workable as stated.
- **Sources**: [KM] 1.4.4 with proof (IN HAND).

### [T-D7] KM 1.4.4 (1)⇔(4): étale-divisor criterion
- **Status**: open · **File**: ExactOrder.lean · `hasExactOrder_iff_etale` ·
  **Depends on**: T-D3 · **Parallel**: with T-D6 · **Type**: theorem ·
  **Sources**: [KM] 1.4.4 (IN HAND; discriminant argument quoted in proof).

### [T-D8] ⧗KM Γ(N): Drinfeld ⟺ naive (N invertible)
- **Status**: open · **File**: LevelStructure/Basic.lean · `isFullLevel_iff_naive` ·
  **Depends on**: T-D6, T-B4, T-B6 · **Type**: theorem ·
  **Sources**: [KM] 3.1 + 3.7 ⧗; [Loe] Fact 3.8.1 (naive side, in hand).

### [T-D9] Γ₁(N): Drinfeld ⟺ naive (restatement of T-D6)
- **Status**: open · **File**: LevelStructure/Basic.lean · `isGammaOne_iff_naive` ·
  **Depends on**: T-D6 · **Type**: theorem (thin wrapper — golf target).

### [T-D10] ⧗KM Γ₀(N): literal fppf-local cyclicity
- **Status**: open (statement to add) · **File**: LevelStructure/Basic.lean ·
  **Depends on**: T-D3; fppf vocabulary · **Type**: def + equivalence statement ·
  **Sources**: [KM] 1.4.1 cyclic (IN HAND) + 3.4 ⧗ + 6.1 ⧗.

### [T-E3] Ell/R category plumbing (Prop sorries)
- **Status**: open · **File**: Moduli/EllCategory.lean · category instance fields,
  `pullbackAlongMap.isPullback/zero_w` · **Depends on**: none · **Parallel**: yes ·
  **Type**: lemmas · **Sketch**: `IsPullback.of_id_fst`-style + `IsPullback.paste_horiz`
  (find exact names); EllHom ext-lemma discipline.

### [T-E4] Moduli-problem functor laws (Prop sorries)
- **Status**: open · **File**: Moduli/Representability.lean · `gammaOneNaiveProblem`
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
- **Status**: open · **File**: ModularCurve/YRho.lean · `card_rootsOfUnity_algClosureQ`
  · **Depends on**: none · **Parallel**: yes · **Type**: lemma ·
  **Sketch**: `Xᴺ − 1` separable in char 0 + alg. closed ⟹ N distinct roots; mathlib
  `IsPrimitiveRoot`/`Polynomial.nthRoots` card lemmas (search first — likely nearly
  present).

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
- **[T-D13]** `sectionVanishingIdeal_spec` (zero locus in a finite locally free
  module). Depends: none. Parallel: yes. PROVABLE-NOW candidate.
  - **Status**: in_progress · **Claimed**: beastmode-D2 (stream-D successor),
    2026-07-06T11:05Z · target `sectionVanishingIdeal_eq_span_coord`
    (Incidence.lean:69) per §Amendments v5 Wave 0.
  - **Progress**: 2026-07-06T11:20Z — proof WRITTEN + verified green standalone
    against mathlib (le_antisymm; ≤: expand φσ along `b.linearCombination_repr` +
    `map_sum`, termwise `Ideal.mul_mem_right` of coord-generators; ≥: `b.coord i`
    is a functional; gotcha: rintro-rfl leaves beta-unreduced membership — `show φ σ ∈ _`).
    Module gate + #print axioms PENDING: Incidence's import chain passes through
    stream-A's in-flight WIP (ProjectiveSpaceChart.lean heartbeat-timeout mid-edit,
    working tree only — NOT the committed baseline). Close-out on next A-green;
    meanwhile continuing Wave 0 with T-D3b (chain-independent ForMathlib).
- **[T-D14]** `exists_incidenceLocusLE` (KM 1.3.4; `deg D'` equations). Depends:
  T-D12, T-D13.
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
  [T-D25] rank-1 locally free algebra ⟹ structure iso. [T-D26] degree-0 effective ⟹
  empty. [T-D27] zero-locus over W of a module = zero-locus over S of its f.l.f.
  pushforward. [T-D28] A-Str ≅ ∏ A_i-Str (KM 1.7.3, phase 2). [T-D29]
  charpoly-as-norm (`LinearMap.charpoly f = Algebra.norm R[T] (T•1 − f)`).
  - **[T-D29] Status**: in_progress · **Claimed**: beastmode-D2 (stream-D
    successor), 2026-07-06T11:55Z · new file ForMathlib/CharpolyNorm.lean
    (mathlib-only imports). Reading of record (binding, KM 1.8.2 "char poly of
    f ∈ B = norm of T−f rel B⊗R[T]/R[T]"): the endomorphism is `Algebra.lmul R B b`
    — statement `(Algebra.lmul R B b).charpoly = Algebra.norm R[X]
    (X ⊗ₜ 1 − 1 ⊗ₜ b)` in `R[X] ⊗[R] B`. The naive general-endomorphism reading
    is FALSE (norm on End(V) is det^dim) — attack block in d-lane-helpers.md.
    Gap re-verified (4 searches; `charpoly_baseChange` exists but is functoriality,
    not the bridge). Proof scratch-verified green.
  [T-D30] char-poly form of full-sections + equivalence (KM 1.8.2). [T-D31]
  reduced-ring evaluation separation for MvPolynomial. [T-D32] f.l.f.-map iso ⟺
  geometric-fibre iso (det-unit local-global). [T-D3a′] Flat-of-SES (if mathlib
  lacks). [T-D3b] `IdealSheafData.mul` (upstream candidate).
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
