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
4. **⚡ KM SOURCE GATE LIFTED 2026-07-08** — the full Katz–Mazur text is now in
   `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`. ⧗KM tickets are **dispatchable and
   may be CLOSED** (don't idle "waiting for KM"). When you close one, READ the cited KM pages and
   quote them verbatim (page + section) in the decl/ticket; do NOT prove from memory. A ⧗KM ticket
   may still be blocked by a *non-KM* gate (deferred T-A6 Abel dictionary, T-Q2/SGA-III, D2's
   flatness/depth domain) — re-check its other `Depends on:`. See the "Katz–Mazur source gate —
   LIFTED" section below for the binding wording.
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
   **THIRD SWEEP INCIDENT (2026-07-07T20:03Z, recorded by coordinator-P1)**: commit
   `2de9271b` (P3/beastmode-A) swept the P1 lane's in-flight
   `EllipticCurve/AdditionLawField.lean` (a broken mid-iteration snapshot) and
   `GroupLawConstruction.lean` alongside its own PoleFiltration.lean — a bare-index
   commit, not a pathspec commit. No build damage (the swept file was not yet imported
   by the root module; HEAD carries the corrected version via `91f9499e`), but this is
   the exact failure mode this rule exists to stop. beastmode-A: switch to
   `git commit -- <your files>`, no `git add`, effective immediately.
   **FOURTH SWEEP INCIDENT (2026-07-07T20:34Z, coordinator-P1)**: commit `552a037c`
   (P3/beastmode-A again, 27 minutes AFTER the third-incident instruction above) swept
   P1's in-flight `AdditionLawOnCurve.lean`. Same pattern, same session; the board note
   alone is not reaching it. ESCALATED TO OWNER: the beastmode-A session needs the
   pathspec-commit instruction pasted directly into it (and/or a pre-commit guard).
   No build damage (file not yet root-imported at 552a037c; HEAD corrected via 217f7aba).
   **SEVENTH SWEEP (2026-07-08T09:12Z, coordinator-P1)**: `a4756384` (beastmode-A b2-γ)
   swept P1's in-flight `AdditionChartLadder.lean` mid-iteration. HEAD corrected via
   `cfae244c`. Count now 7 (see also #6 at 98f06d8c, logged by fable-P4). Owner action
   still pending: paste the pathspec-commit instruction into the beastmode-A session.

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
- **Status**: RE-FROZEN v9 (2026-07-07, owner-approved) — WORKABLE (no longer blocked).
  New statement = **G-torsor form**: the sheaf of Weierstrass presentations of E is a torsor
  under `G = VariableChange` (affine group scheme); after a Hodge/conormal `ω`-trivialization the
  remaining changes are the `u=1` subgroup. Lean **consumes the group-action/torsor statement,
  NOT a coordinate formula**. See **Amendments v9 §v9.4**. ── Prior blocked-B2 record retained
  for the counterexample rationale: (beastmode 2026-07-07T19:30Z — **STATEMENT FALSE as written;
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
  2026-07-07T00:30Z — all three targets DERIVED, sorry-free modulo the three named
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
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-07T00:45Z →
  2026-07-07T02:00Z — both targets DERIVED: `mulBy_etale` via
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
- **Status**: done (beastmode-A 2026-07-07T02:15Z → 2026-07-07T03:00Z —
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
- **Status**: done (beastmode-A 2026-07-07T03:30Z → 2026-07-07T06:00Z —
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
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-07T06:15Z →
  2026-07-07T09:30Z — DS4a DISCHARGED: `sectionsDivisor` is a TOTAL def with real
  in-scope data (ideal := ∏ᵢ ker (Pᵢ), the KM product-of-ideal-sheaves — mathlib's
  stock `Mul IdealSheafData`); out-of-scope branch ⊤-ideal with vacuous props (stock
  `IsEmpty (⊤.subscheme)` instance + IsOpenImmersion-of-IsEmpty + ClosedImmersion
  iff_isFinite_and_mono). `sectionDivisor` + `sectionDivisor_degree` (single section,
  KM 1.2.2) PROVED sorry-free via ker + IsIso z.toImage transport.
  `sectionsDivisor_degree` derived from the finrank box via dif_pos. FOUR register
  boxes (KM 1.2.2/1.2.3/1.2.6 quotes banked): `sectionsIdeal_isFinite/flat/lfp/
  finrank` — hypothesis-guarded, TRUE, discharge = T-D1 route once AG-LB lands
  (same gate as T-D1; the SES degree argument consumes ideal invertibility).
  Consumers (T-D5/6/7) are interface-unblocked.) · **DESIGN BANKED (2026-07-07T06:30Z)**:
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
  **(2a) IS NEARLY FREE (discovery 2026-07-07T07:00Z)**: mathlib has
  `instance [IsClosedImmersion f] : IsIso f.toImage` (ClosedImmersion.lean:154) and
  `f.image := f.ker.subscheme`, `toImage ≫ imageι = f`. For a section z of separated π
  (closed immersion via the T-B3 of_comp pattern): z.ker.subschemeι = z.imageι =
  inv z.toImage ≫ z, so subschemeι ≫ π = inv z.toImage ≫ 𝟙 = inv z.toImage — an ISO —
  finite/flat/lfp/rank-1 all transported from iso-instances. Write
  `sectionDivisor (π) [IsSeparated π] (z) (hz) : RelEffCartierDiv π` first, then the
  n-fold product (CRT/filtration = the remaining mountain; consult KM 1.1-1.2 pages
  via the full PDF, printed pp. ~7-20, before formalising — quote-gate for 1.2.2).
  (2a) DONE 2026-07-07T08:00Z: `sectionDivisor` + `sectionDivisor_degree` sorry-free
  in CartierDivisor.lean (ker + toImage-transport; degree via
  finrank_eq_one_of_isIso; NB IsIso.eq_inv_comp for the `= inv _ ≫ _`-orientation).
  (2b) QUOTES MINED (2026-07-07T08:30Z, printed pp. 7-9): KM 1.2.2 "any section
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
- **Status**: done-modulo-registered-box (beastmode-A 2026-07-07T10:00Z →
  2026-07-07T11:00Z — `HasExactOrder.smul_eq_zero` DERIVED sorry-free from the box
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
- **Status**: done-modulo-registered-boxes (beastmode-A 2026-07-07T04:00Z —
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
- **FULL 1.4.4 QUOTE MINED (2026-07-07T11:30Z, printed pp. 18–19)** — statement (1)-(5)
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
  T-D6a-INFRA COMPLETE (2026-07-07T07:00Z): ALL CartierDivisor-side base-change
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
  T-D6a-PROGRESS (2026-07-07T12:30Z): `RelEffCartierDiv.baseChange` Prop-fields
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
- **Status**: done (beastmode-A 2026-07-07T18:00Z → 2026-07-07T02:00Z —
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
- **BANKED DESIGN (2026-07-07T13:30Z)**: comap K f := (pullback.fst f K.subschemeι).ker
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
- **ROUTE REFINED (2026-07-07T18:30Z, two mathlib simplifiers found)**:
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
- **AFFINE CASE DONE (2026-07-07T21:00Z)**: `comap_ideal_top_of_isAffine` +
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
- **Status**: DONE — axiom-clean (beastmode-A 2026-07-08, commit 8f17a574): L3 `Section.orderDivisor_baseChange` (order divisor natural in base) + L4 `RelEffCartierDiv.IsSubgroup.baseChange` (subgroup-divisors base-change stable, via `Point.baseChangeEquiv` + NEW ForMathlib `exists_factor_comap_iff` comapIso factoring dictionary, commit e890e777) + headline `Section.HasExactOrder.baseChange` (KM 1.4.4 (1)⟹(2) exact-order preservation). All `#print axioms` = [propext, Classical.choice, Quot.sound]. Earlier progress: (beastmode-A 2026-07-07T08:30Z:
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
- **Status**: done-modulo-registered-box (beastmode-A 2026-07-07T04:30Z —
  `hasExactOrder_iff_etale` DERIVED from T-D6 + the `orderDivisor_etale_iff_geometric`
  box (T-D7-bridge, (3)⟺(4) discriminant argument, verbatim KM quote in docstring);
  the iff-plumbing collapses the killing conjunct via pull_zsmul + hkill.) · **File**: ExactOrder.lean · `hasExactOrder_iff_etale` ·
  **Depends on**: T-D3 · **Parallel**: with T-D6 · **Type**: theorem ·
  **Sources**: [KM] 1.4.4 (IN HAND; discriminant argument quoted in proof).

### [T-D8] ⧗KM Γ(N): Drinfeld ⟺ naive (N invertible)
- **Status**: done-modulo-registered-box (beastmode-A 2026-07-07T05:30Z —
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
- **Status**: done (beastmode-A 2026-07-07T05:00Z — PROVED first-try, sorry-free in
  itself: forward direction gets the killing clause from T-D5's
  HasExactOrder.smul_eq_zero (BB-DELIGNE consumer), then T-D6's iff both ways.
  Transitively rests on the D5/D6 register boxes.) · **File**: LevelStructure/Basic.lean · `isGammaOne_iff_naive` ·
  **Depends on**: T-D6 · **Type**: theorem (thin wrapper — golf target).

### [T-D10] ⧗KM Γ₀(N): literal fppf-local cyclicity
- **Status**: STATEMENT DONE, proof ⧗-gated (beastmode-A 2026-07-07T10:30Z —
  `IsGammaZeroFppf` def + `isGammaZero_iff_fppf` statement ADDED and building green in
  LevelStructure/Basic.lean, discharging the ticket's "def + equivalence statement"
  deliverable. Implemented design option (a): fppf cover = `Function.Surjective h.base
  ∧ Flat h ∧ LocallyOfFinitePresentation h` + a generating `(E.baseChange h).Section`
  of exact order N whose orderDivisor ideal = G.baseChange ideal. The iff PROOF stays
  a registered WIP sorry — it is KM 3.7.1's étale-descent representability argument
  (⧗ do-not-formalize-from-memory; ⟸ descends a generator to geometric points, ⟹ needs
  the constant-E[N] reduction + étale descent). Formerly:) quote-gate-satisfied,
  DESIGN-DECISION-GATED (beastmode-A 2026-07-07T10:00Z
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
- **Status**: done (beastmode-A 2026-07-07T14:00Z → 2026-07-07T15:30Z — ALL fields
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
- **Status**: done-modulo-E4a-gate (beastmode-A 2026-07-07T15:30Z →
  2026-07-07T17:00Z — the FOUR functor-law sorries (map_id/map_comp ×2 functors)
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

### [T-E5] representable ⟺ rel. representable + rigid (KM 4.7) — DECOMPOSED 2026-07-08
- **Status**: open (decomposed; leaves below) · **File**: Moduli/EllCategory.lean ·
  `representable_iff` · **Depends on**: T-E5a–T-E5e · **Type**: theorem (hard) ·
  **Sources**: [KM] SCHOLIE 4.7.0 + engine p. 112 + Appendix A.4 (**READ 2026-07-08,
  verbatim in `.mathlib-quality/km47-source-quotes.md`; docstring carries the quotes**);
  [Loe] 3.6.1/3.7.1–3.7.4.
- **⚠️ STATEMENT MISMATCH — FLAGGED, NOT FIXED** (dispatch v10.4: "statement mismatch ⟹
  flag, don't fix"; the earlier T-Q6e note called it and deferred the decision here).
  KM 4.7.0 reads *"Let 𝒫 be relatively representable **and affine over** (Ell); then a
  necessary and sufficient condition that 𝒫 be representable is that 𝒫 be rigid."* Our
  statement (= Loeffler 3.7.4 verbatim) has no affineness. It is **load-bearing three
  times** in KM's own proof: p. 112 (`𝕸(𝒫,δ)` affine over affine `𝕸(δ)` ⟹ *absolutely*
  affine); p. 113 (*"Because `𝕸(𝒫,δ)` is affine, the quotient `𝕸(𝒫,δ)/G` exists"* — a free
  finite-group quotient of a general scheme is only an algebraic space, cf. Hironaka);
  p. 114 (α_univ descends *"because 𝒫 is relatively affine"*, SGA I VIII 7.8). Loeffler's
  own quotient input (Prop 3.6.1) is stated only for **quasiprojective** `X`, so his sketch's
  "take invariants" step tacitly assumes what his 3.7.4 omits. ⟹ **the Lean statement is
  supported by neither source's proof.**
  - **OWNER DECISION REQUESTED** (fable-P4 recommendation = **(a)**):
    (a) add affine-over-`Ell` to the **⇐ direction only** — costless downstream: every
        consumer (KM 4.7.1/4.7.2, [Loe] 3.8.2, T-E7/T-E9/T-H4/T-H6) is *affine and étale*
        over `Ell`;
    (b) weaken to quasi-projective-over-`Ell` and pay for [Loe] 3.6.1 in that generality
        (⟹ T-Q5 must deliver the quasi-projective gluing, not just the affine case);
    (c) keep the general statement ⟹ algebraic spaces ⟹ **out of scope** (absent from
        mathlib).
- **Leaves** (Tier A5 split; each single-conclusion):
  - **[T-E5a]** `representable ⟹ rigid` — KM 4.4, [Loe] Exercise (1). Free-ish: a fixed
    point of `Aut(E/S)` on `P(E/S)` contradicts the universal property's uniqueness clause.
  - **[T-E5b]** `representable ⟹ relatively representable` — **NOT free** (KM leaves it
    implicit in 4.3; Loeffler asserts it inside 3.7.4). Needs the `Isom`-scheme of the
    universal curve: `T ↦ 𝒫(E_T/T) ≅ Hom_{Ell}(E_T/T, E_univ/𝕸(𝒫))`, to be exhibited as an
    `S`-scheme. Own gap ticket if the `Isom`-scheme is missing (it is: mathlib has no
    `Isom`-scheme for elliptic curves).
  - **[T-E5c]** the KM engine, `ℤ[1/N]`-half — **already exists** as
    `representable_of_rigid_of_torsor` (Moduli/QuotientProblem.lean, sorried = **T-Q6e**).
    T-E5 must not re-derive it; it must *instantiate* it twice.
  - **[T-E5d]** instantiation at `(N, δ, G) = (3, naive level 3, GL₂(𝔽₃))` — consumes
    **T-E15**; unblocked.
  - **[T-E5e]** instantiation at `(N, δ, G) = (2, Legendre, GL₂(ℤ/2) × {±1})` — consumes
    **T-E14**, hence **blocked on [T-E-OMEGA]**.
  - **[T-E5f]** "recollement": the two representing objects agree over `ℤ[1/6]` by rigidity
    (the unique isomorphism), glue to one over `ℤ` (KM p. 111). Consumes T-E5d + T-E5e.
- **NOT needed on this route**: `𝒫̃` (KM A.4.1.1) and Prop A.4.2. They are the *alternative*
  ⇐ route ("𝒫̃ representable + rigid ⟹ 𝒫 representable", KM A.4.1.2 = [Loe] Exercise (2)),
  which merely *moves* the difficulty into proving `𝒫̃` representable. Gabber's
  counterexample (KM A.4.1.3, verbatim in the quotes file) proves `𝒫̃` is a strictly weaker
  object than `𝒫` — so it is genuinely a second definition, not a synonym. Cut only on demand.

### [T-E-OMEGA] the invariant differential `ω_{E/S}` — GAP TICKET (cut 2026-07-08, fable-P4)
- **Status**: open, unclaimed · **File**: new `EllipticCurve/InvariantDifferential.lean` ·
  **Blocks**: T-E12, T-E13, T-E14 ⟹ T-E5e ⟹ T-E5f ⟹ **the `ℤ[1/2]`-half of KM 4.7** ·
  **Type**: def + 3 lemmas (a bounded sub-stream, not a leaf)
- **The gap (verified 2026-07-08, fable-P4)**: KM's Legendre problem (4.6.2, verbatim)
  quantifies over *"an `S`-basis `ω` of `ω_{E/S}`"*, and `ω_{E/S}` exists **neither in
  mathlib** (`Mathlib/AlgebraicGeometry`, 45 files: no `Ω¹`, no cotangent complex, no
  relative differentials for schemes) **nor in this repo** (every `omega` hit is the
  tactic). This is *not* a data-sorry: no decl was emitted (see `Moduli/Bootstrap.lean`).
- **Plan terminating in a proof** (per v10.8 RR-only): do **not** wait for scheme-level
  `Ω¹`. Our `EllipticCurveGeom` is *locally Weierstrass* (T-A8), so define `ω_{E/S}` as the
  line bundle glued from the atlas with the classical local basis
  `dx / (2y + a₁x + a₃)`, whose transition under a variable change `(u, r, s, t)` is
  multiplication by `u` — **the cocycle is already proven**: `T-W7.1a` (atlas +
  `classifyRingHom`) and `T-W7.mvc` (`projModelVCIso` + `_mul`, the cocycle identity,
  axiom-clean). Steps: (i) `def invDiffLineBundle` via `Scheme.Cover.glueMorphisms`-style
  gluing over the atlas (or as an invertible sheaf given by the `u`-cocycle); (ii)
  `invertible` + rank 1; (iii) `basis_iff_unit`; (iv) base-change compatibility
  (mirror `LocallyWeierstrass.baseChange`). Est. 400–700 lines. **Sources**: KM 2.2 / 4.6.2;
  GME 2.2.
- **ALTERNATIVE that dodges `ω` entirely (recorded, owner's call)**: KM's engine needs *some*
  `δ` over `ℤ[1/2]` satisfying axioms 1–2. Take `δ = ` **naive level 4**, `G = GL₂(ℤ/4)`
  (`E[4]` is finite étale when `2` is invertible; bases of `E[4]` form a `GL₂(ℤ/4)`-torsor;
  rigid since `N ≥ 3`). This replaces "Legendre + `ω`" by "one more explicit affine model"
  (`Y(4)/ℤ[1/2]`, reachable from `ForMathlib/TateNormalForm.lean`). Trade: T-E-OMEGA
  (400–700 lines, reusable everywhere — Hodge bundle, modular forms) **vs** an explicit
  `Y(4)` model (~T-E15-sized, single-use). Recommendation: **do T-E-OMEGA** — the Hodge
  bundle `ω` is needed by the modular-forms stream regardless.

### [T-E12] `M₁ = Spec ℤ[1/6, g₂, g₃, Δ⁻¹]` represents `(E, ω)` (GME Thm 2.2.3)
- **Status**: open, **blocked on [T-E-OMEGA]** · **File**: Moduli/Bootstrap.lean (no decl
  yet — see its header) · **Type**: def + theorem · **Sources**: GME Thm 2.2.3; KM 2.2.
- **Body** (from `decomposition-gme2.md` §E12, fully explicit): `P₁ : S ↦ [(E, ω)]` is
  represented over `ℤ[1/6]` by `M₁ = Spec ℤ[1/6, g₂, g₃, Δ⁻¹]`; proof = A7 uniqueness of
  `(g₂, g₃)` given `ω`; universal curve `y² = 4x³ − g₂x − g₃`.

### [T-E13] `Aut_S(E, ω) = {1}` — the rigidity engine (GME Cor 2.2.4)
- **Status**: open, **blocked on [T-E-OMEGA]** · **File**: Moduli/Bootstrap.lean · **Type**:
  theorem (short) · **Depends on**: T-E12 · **Sources**: GME Cor 2.2.4.
- **Body**: one-liner from T-E12's representability ("two distinct identifications
  `φ*(𝐄, ω) ≅ (E, ω)`"). **Do NOT re-derive rigidity from scratch** (dispatch v10.4): the
  proven canonicity chain in `EllipticCurve/Rigidity.lean` — in particular C3′
  `isMonHom_of_one_comp_eq'` (a pointed morphism of group objects is a homomorphism) — is
  the intended engine wherever this argument needs "an automorphism fixing the zero section";
  import it.

### [T-E14] the Legendre bootstrap object `M'₂` over `ℤ[1/2]` (GME Ex. 2.2.1 / KM 4.6.2)
- **Status**: open, **blocked on [T-E-OMEGA]** · **File**: Moduli/Bootstrap.lean · **Type**:
  def + 2 theorems (KM engine axioms 1 & 2) · **Depends on**: T-E-OMEGA, T-E13 ·
  **Sources**: KM 4.6.2 + 2.2.9 (verbatim in the quotes file); GME Ex. 2.2.1 (p. 117).
- **Body**: over `ℤ[1/2]` normalise `y² = x³ + a₂x² + a₄x + a₆`, `i(x, y) = (x, −y)` gives
  `[−1]`; `E[2] − {0} ≅ Spec(A[X]/(F))` free of rank 3; `E[2]` is étale (distinct roots by
  smoothness); the problem `P'₂` (pairs `P, Q ∈ E[2] − 0` with `x(P) = 0`, `x(Q) = 1`, plus
  the `ω`-datum) is represented by `M'₂ = Spec ℤ[1/2, λ, (λ(λ−1))⁻¹]`, universal curve with
  `P = (0,0,1)`, `Q = (1,0,1)`, `ω = dX/Y`. Engine axiom 2: `δ_{E/S}` is a finite étale
  `GL₂(ℤ/2) × {±1}`-torsor (KM 4.6.2 verbatim).

### [T-E15] the naive level 3 bootstrap object `ℰ₃` over `ℤ[1/3]` (GME Ex. 2.2.2 / AME 2.2.10)
- **Status**: open, **UNBLOCKED**, unclaimed · **File**: `Moduli/Bootstrap.lean`
  (**skeleton landed 2026-07-08, builds green**: `naiveLevelThree_representable_by_affine`
  = engine axiom 1, `naiveLevelThree_relativelyRepresentable_finiteEtale` = engine axiom 2)
  · **Type**: 2 theorems · **Depends on**: T-B5 (E[3] finite étale), stream C (Weil pairing,
  for the `Isom`-scheme cut) · **Sources**: KM Ex. 2.2.2 (book pp. 117–118), AME 2.2.10.
- **Body**: `[N]*ω = λω` with `λ = N` at flex points ⟹ `[3]` étale over `ℤ[1/3]` (the
  `[N]*ω = Nω` trick — **also the proof core of T-B5**); `ℰ₃` represented over `ℤ[1/3]` by
  `Spec ℤ[1/3, β, γ][((a₁³ − 27a₃)a₃)⁻¹] / (β³ − (β+γ)³)` with `a₁ = 3γ − 1`,
  `a₃ = −3γ² − β − 3βγ`, `P = (0,0)`, `Q = (γ, β+γ)`. A T-E1-style `VariableChange`
  gymnastics ticket, fully explicit. **Note**: proving this by KM 4.7.2 would be circular —
  4.7.2 *consumes* this object. Prove by hand.

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
- **Status**: open (v2 = `levelledCurve_descent_of_torsor`, `sorry`) · **File**:
  Moduli/Stack.lean · **Depends on**: T-A5 · **Type**: theorem · **Sources**: GME
  Lemma 2.6.7; SGA 1 VIII; [KM] 4.1 ⧗ context.
- **DESC engine LANDED (beastmode-DESC, 2026-07-07, axiom-clean):** the
  descent-of-morphisms half is done — `descend_hom_of_effectiveEpi` +
  `moduliProblem_fppf_descent` (gluing half; with the proven `moduliProblem_fppf_separated`
  ⟹ **relatively representable moduli problems are fppf sheaves**). Built on mathlib
  `Sites/Fpqc` `EffectiveEpi`/`Subcanonical` — the T-E8 descent-data vocabulary is NOT
  needed for the single-cover gluing.
- **Remaining gating (why `levelledCurve_descent_of_torsor` is still `sorry`):** needs to
  *produce the curve* `E/T` (object descent), gated on ONE of {T-E9 representability
  [E-stream, sorried] · relative Proj + QC-sheaf descent + relatively-ample [ABSENT from
  mathlib, each B3-scale — see T-DESC0] · T-Q2 SGA-III quotient charts [plan-deferred]},
  PLUS **T-G3 rigidity** (`aut_trivial_of_fullLevel`, sorried) for the strict cocycle.
  The morphism-descent engine + representability (T-E9) would assemble it cleanly; the
  object-descent-from-scratch route is B3-scale. Not dispatchable in DESC alone.

### [T-E11] fppf separatedness of relatively representable problems
- **Status**: done (beastmode-A 2026-07-07T12:00Z — `moduliProblem_fppf_separated` PROVED sorry-free, axioms standard. Formal proof from RelativelyRepresentable naturality + Equiv.injective + Flat.epi_of_flat_of_surjective [Stacks 02VW, present in mathlib] + cancel_epi. The PENDING-SOURCE note concerned statement justification only; the committed statement proves cleanly.) · **File**: Moduli/Stack.lean · `moduliProblem_fppf_separated` ·
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
  - AG-GG-1.0 DONE (2026-07-06): HasFiniteLimits/HasFiniteColimits +
    HasColimitsOfShape (SingleObj G) for CommAlgCat k via commAlgCatEquivUnder;
    gotchas: SingleObj G : Type 0 ALWAYS (universe-shrink via
    hasColimitsOfSizeShrink needed for u > 0); Under-side SingleObj colimits via
    Under.forget creating CONNECTED colimits (IsConnected (SingleObj G) ✓ mathlib).
  - AG-GG-1.1 DONE: finite products (pointwise Pi-algebras; Fan.IsLimit.mk;
    subcategory homs are ObjectProperty.homMk-wrapped — hom_ext takes P explicitly,
    use the ext TACTIC which chains all three @[ext] lemmas).
  - AG-GG-1.3a DONE: k initial (hasInitial_of_unique; hom-subsingleton from
    AlgHom.commutes).
  - AG-GG-1.2 DONE: pushouts = tensor B ⊗[A] C; étale vertex via mathlib's
    OWN 2-of-3 `Algebra.Etale.of_restrictScalars k A C` (no new lemma needed!) +
    Etale.baseChange + Etale.comp; Module.Finite via of_restrictScalars_finite +
    base_change + trans; IsColimit cribbed from CommRingCat.pushoutCoconeIsColimit
    (productMap f' g' over the span-algebraized base, restrictScalars k;
    A-AlgHoms from k-AlgHoms with letI toAlgebra-of-composite; term-glue map_mul
    in the induction — rw across the wrapper seam fails); HasPushouts via
    diagramIsoSpan (NOT .symm — hasColimit_of_iso eats G ≅ F).
  - AG-GG-1.1 closure under finite products (Etale-Pi instance ✓ in mathlib;
    concrete product cones in CommAlgCat).
  - AG-GG-1.2 closure under pushouts B ⊗[A] C (needs the 2-out-of-3
    `A → B étale when k → A, k → B étale` — formal-lifting leaf if mathlib lacks
    it — then base-change + comp instances ✓ mathlib).
  - AG-GG-1.3 trivial closures: k initial ✓ (Etale R R), zero ring étale
    (empty product).
  - AG-GG-1.4 HEARTS DONE (2026-07-06): `isSeparable_of_etale` (every element of
    a finite étale k-algebra is separable — classification equiv + Finset of
    DISTINCT component-minpolys, separable_prod' with
    Irreducible.coprime_iff_not_dvd + eq_of_monic_of_associated, annihilator
    divides) and `etale_subalgebra` (subalgebra of finite étale over a field is
    étale — IsReduced-transfer, IsArtinianRing.equivPi + FormallyEtale.pi_iff +
    of_isSeparable per residue field, minpoly-divides through Quotient.mkₐ;
    minpoly.algHom_eq needs **B.val** — B.subtype dot-resolves to the SUBSEMIRING
    RingHom and silently poisons unification). Both sorry-free, mathlib-grade
    upstream candidates. 1.4 CATEGORICAL PART ALSO DONE (2026-07-06):
    actionFixedPoints (direct fixed-set Subalgebra — no MulSemiringAction
    packaging needed since etale_subalgebra eats ANY subalgebra) + cone + IsLimit
    (AlgHom.codRestrict lift; naturality-hom needs `show ⋆ ⟶ ⋆ from h`
    elaboration-forcing; const-id side closes by DEFEQ exact, simpa breaks) ⇒
    HasLimitsOfShape (SingleObj H) (FiniteEtale k) for ANY monoid H. 1.4 ✓ DONE.
  - AG-GG-1.5 (G3 splitting) ATTACK PLAN (only remaining leaf before assembly):
    mono-in-op = subcategory-epi π : Y ⟶ X; (i) π surjective: X' := range
    (étale by etale_subalgebra); X étale over X' (of_restrictScalars) ⇒ faithfully
    flat ⇒ AlgHom-to-k̄ extension X' → X surjective on fibres; counting
    (natCard_algHom_eq_finrank!) forces dim X' = dim X else two k̄-homs agree on
    range and land in a common finite subextension W ∈ FiniteEtale k, refuting
    epi; (ii) splitting: ker π idempotent-generated in artinian reduced Y ⇒
    Y ≅ X × Z via CRT-pair (e, 1-e), Z étale via classification/quotient.
    Then ASSEMBLY: PreGaloisCategory ((FiniteEtale k)ᵒᵖ) from op-duality
    instances + hand-rolled (SingleObj G)ᵒᵖ ≌ SingleObj Gᵐᵒᵖ.
  - AG-GG-1.5 ✓ DONE (2026-07-06, beastmode-B): part (i) epi⇒surjective —
    `natCard_algHom_sepClosure` (# homs into SeparableClosure = finrank, via
    liftEquivRight base change + natCard_algHom_eq_finrank) + `surjective_of_epi`
    (PIGEONHOLE against the range subalgebra — counting both X and X' kills the
    faithful-flatness step entirely; two k̄-homs agreeing on the range land in
    W := g₁.range ⊔ g₂.range, finite via productMap_range, a FIELD via
    isField_of_isIntegral_of_isField', étale via minpoly.algHom_eq W.val ⇒
    contradicts Epi via cancel_epi). Part (ii): `etale_of_isSeparable` core
    refactored out of etale_subalgebra (finite + reduced + separable elements ⇒
    étale); `etale_quotient` (every ideal complemented by semisimplicity
    (IsArtinianRing.isSemisimpleRing_of_isReduced), complement ⇒ RADICAL by the
    i·j = 0 trick + 2^k-descent induction, quotient reduced via
    isRadical_iff_quotient_reduced, separability descends through mkₐ);
    `monoInducesIsoOnDirectSummand_op` (CRT AlgEquiv.ofBijective on
    π.prod(mkₐ J) — inj: ker ⊓ J = ⊥; surj: Bezout e + f = 1;
    BinaryFan.isLimitMk + BinaryFan.IsLimit.op — NOT bare hlim.op which grabs
    the generic Cone.op). ASSEMBLY ✓ DONE: `singleObjOpEquiv`
    ((SingleObj M)ᵒᵖ ≌ SingleObj Mᵐᵒᵖ — map_id/map_comp rfl, Iso.refl units,
    functor_unitIso_comp := Category.id_comp explicitly since 1·1 isn't rfl;
    disambiguate MulOpposite.unop vs Quiver.Hom.unop or metavars poison the
    functor literal) + op-duality instances (hasTerminal_op_of_hasInitial,
    hasPullbacks_opposite, hasFiniteCoproducts_opposite,
    hasColimitsOfShape_op_of_hasLimitsOfShape with C pinned explicitly) ⇒
    **instance PreGaloisCategory (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ for ANY
    field k** — hasQuotientsByFiniteGroups field must be given explicitly
    (`fun G _ _ => inferInstance`); the Pi-typed default infer_instance can't.
    Axiom-clean: all four theorems + instance probe = propext/choice/Quot.sound.
    NOTE for probes: FiniteEtale has TWO universes — `FiniteEtale ℚ` without
    `.{0}` leaves a metavar head and synthesis silently fails.
  Duplication watch: NOTHING imports RingTheory/Etale/Finite.lean yet; Merten's
  series is visibly heading here — re-check at each mathlib bump, swap ours out
  if mathlib lands it.
- **[AG-GG-2]** `FiberFunctor` instance — RESTRUCTURED 2026-07-06 (beastmode-B) around
  a DISCOVERY: mathlib's RingTheory/Etale/Finite.lean ALREADY HAS the functor —
  `CommAlgCat.FiniteEtale.fiber R Ω : (FiniteEtale R)ᵒᵖ ⥤ FintypeCat` (Hom into Ω,
  Fintype instances included), `fiberIsoBaseChangeFiber : fiber R Ω ≅
  (baseChange R S).op ⋙ fiber S Ω`, and for Ω sep-closed `fiber Ω Ω` is an
  **IsEquivalence** (fiberIsoFiniteSpec + equivOfIsSepClosed). DO NOT REBUILD THESE.
  Consequence: F := fiber k (SeparableClosure k) factors through the equivalence, so
  every FiberFunctor axiom reduces to an exactness property of
  `baseChange k Ω : FiniteEtale k ⥤ FiniteEtale Ω` (equivalence-part preserves and
  reflects everything; transport along the natiso + composition instances).
  Leaves (new file ForMathlib/FiniteEtaleFiberFunctor.lean):
  - AG-GG-2a preserves initial: Ω ⊗[k] k ≅ Ω (TensorProduct.rid; trivial).
  - AG-GG-2b preserves tensor pushouts: Hom_Ω(Ω⊗(B⊗[A]C), T) equiv-chase via
    liftEquivRight + raw TensorProduct.lift UP (NOT the categorical UP — T-as-k-alg
    is not finite over k, so use mathlib algebra-level UP).
  - AG-GG-2c preserves finite products: Algebra.TensorProduct.piRight (exists,
    RingTheory/TensorProduct/Pi.lean, finite ι).
  - AG-GG-2d preserves op-epis = monos: mono ⇒ injective in FiniteEtale k via the
    KERNEL-PAIR SUBALGEBRA P := {(x,y) : j x = j y} ⊆ A × A (étale by
    etale_subalgebra! two projections equalized by j ⇒ equal ⇒ diagonal);
    then flat transfer (Ω free/flat over k: rTensor preserves injective) ⇒ mono.
  - AG-GG-2e preserves SingleObj-G limits (fixed points): Ω ⊗ A^G ≅ (Ω⊗A)^G —
    A^G = ker δ for the SINGLE map δ : A → ∏_{g∈G} A, a ↦ (g·a − a)ᵍ; flat base
    change preserves kernels; piRight matches targets. THE one real math lemma.
  - AG-GG-2f reflects isos: counting — Fi bijective ⇒ finrank equal (via
    natCard_algHom_sepClosure both sides); injectivity: else factor through
    A/ker (etale_quotient) with strictly smaller finrank, contradicting card;
    surjectivity: range subalgebra + Submodule.finrank_lt. NO flatness needed.
    (Alternatively faithfully-flat; counting is self-contained.)
  - AG-GG-2g transport plumbing: per-axiom op-conversion (walkingCospanOpEquiv,
    singleObjOpEquiv from AG-GG-1, Discrete PEmpty self-dual), composition
    instances (equivalence auto-preserves), preservation-along-natIso ⇒
    `instance : PreGaloisCategory.FiberFunctor (fiber k (SeparableClosure k))`.
  Universe note: fiber k Ω lands in FintypeCat.{u} for k Ω : Type u ✓.
  ✓✓ AG-GG-2 COMPLETE (2026-07-06, beastmode-B) — ALL leaves done, axiom-clean
  (`probe_fiberfunctor`: propext/choice/Quot.sound). File
  ForMathlib/FiniteEtaleFiberFunctor.lean (~700 lines). Per-leaf landing notes:
  - 2a: rid + preservesInitial_of_iso; `baseChangeU` abbrev pins baseChange's FREE
    object-universe (else it leaks as u_1 into every statement — max u u vs u).
  - 2c: piRight needs [Fintype ι][DecidableEq ι] in STATEMENTS (Finite+classical
    haveI inside proofs); uniq via `baseChangePi_hom_ext` (hom-level ext through
    piRight-injectivity) — CommAlgCat.hom_ofHom does NOT fire across the mapCone
    carrier spelling, so never rw on the wrapped lift.
  - 2b: isColimitMapCoconePushoutCoconeEquiv (root Limits ns, NOT PushoutCocone.*)
    + isColimitAux'; desc := liftEquivRight of productMap over the letI-algebra;
    ALL map_* steps as term-glue (rw pattern-unify trips on InducedCategory
    carriers); s.inl-commutes gives algebraMap-tmul identities.
  - 2d: kernel-pair equalizer P ⊆ Π(Fin 2) A is étale (etale_subalgebra!), two
    evals equalised ⇒ mono injective; ![x,y]-eval is rfl (exact h, simpa breaks);
    lTensor_preserves_injective_linearMap + ConcreteCategory.mono_of_injective +
    faithful-ι mono_of_mono_map.
  - 2e: Merten's Flat/Equalizer.lean has THE toolkit (eqLocus_lTensor_eq,
    tensorKerEquiv); fixed points = eqLocus(actionDelta, actionDiag); membership
    transfer via TensorProduct.piRightHom components (hcomp-lemmas MUST be hoisted
    before rintro ⟨x,hx⟩ — induction reverts hx into the motive otherwise);
    fullyqualify TensorProduct.AlgebraTensorModule.lTensor (open scoped ≠ open);
    bijectivity proofs INLINE in AlgEquiv.ofBijective (standalone lemma statements
    re-elaborate the AlgHom type and get stuck on Algebra k ?m).
  - 2f: counting reflection — ker = ⊥ via factor-through-quotient card equality +
    injective_iff_surjective_of_finrank_eq_finrank + Ideal.mk_ker; range = ⊤ via
    Submodule.finrank_lt; Ideal.Quotient.lift_mk needs h.toRingHom explicit.
  - 2g: transport names: preserves(Co)LimitsOfShape_of_equiv (NOT _of_equivalence),
    preservesLimitsOfShape_op takes J-THEN-F explicit (`_ _`), Discrete.opposite,
    walkingCospanOpEquiv, singleObjOpEquiv (AG-GG-1), Finite Gᵐᵒᵖ via
    Finite.of_equiv G MulOpposite.opEquiv; epis: op-side hand-lemma via
    unop_mono_of_epi + preservesMonomorphisms + op_epi_of_mono.
- **[AG-GG-3]** `IsFundamentalGroup Gal(k̄/k) (fiber k k̄)` — SCOPED 2026-07-06
  (beastmode-B), file ForMathlib/FiniteEtaleFundamentalGroup.lean. Mathlib gives the
  topology side FREE: `separableClosure.isGalois` [Normal on AlgebraicClosure] ⇒
  IsGalois k (SeparableClosure k) ⇒ `CompactSpace Gal(K/k)` (Galois/Profinite:329) +
  IsTopologicalGroup (KrullTopology). Fiber topology: `scoped instance : TopologicalSpace
  (F.obj X) := ⊥` in CategoryTheory.PreGaloisCategory scope (Galois/Topology:57) —
  open scoped it. The class (IsFundamentalgroup.lean:231): extends IsNaturalSMul +
  transitive_of_isGalois + continuous_smul + non_trivial'. Leaves:
  - 3a MulAction σ • x := σ.toAlgHom.comp x + IsNaturalSMul (comp-assoc, rfl-ish).
  - 3d connected ⇒ field: A ≠ 0 (else X initial-op via terminal = empty-product
    vertex, subsingleton carrier); m₀ maximal; mkₐ surjective ⇒ epi (ConcreteCategory
    epi_of_surjective + faithful-ι reflects) ⇒ op-mono into X; A⧸m₀ étale
    (etale_quotient) nonzero-field ⇒ non-initial ⇒ IsConnected.noTrivialComponent ⇒
    iso ⇒ IsField A transported along the CRT-free RingEquiv.
  - 3e transitive on Galois X: [IsGalois X ⇒ IsConnected X] ⇒ A field (3d, letI
    h.toField); x y : A →ₐ Ω; χ := ofInjectiveField-y ∘ (ofInjectiveField-x).symm on
    fieldRanges; σ := χ.liftNormal Ω (Normal k Ω from IsGalois); liftNormal_commutes
    gives σ ∘ x = y.
  - 3c ContinuousSMul on discrete fibers: stabilizer {σ | σ∘x = x} = fixingSubgroup
    of x.range-promoted-to-IntermediateField (range is a FIELD: f.d. domain in Ω —
    part-(i)-W trick isField_of_isIntegral_of_isField'; inverse-closure from
    IsField-inverses via Subalgebra.toIntermediateField); f.d. ⇒
    IntermediateField.fixingSubgroup_isOpen (KrullTopology:173); {σ | σ•x = y} =
    preimage of stabilizer under continuous left-mul by σ₀⁻¹ (nonempty case);
    Continuous into ⊥-topology finite target via per-point preimages open.
  - 3f non_trivial: σ fixing all fibers: at X := op (of k ↥(adjoin k {ω}))
    (étale: intermediate of separable is separable + of_isSeparable; f.d.: ω
    integral) with point (adjoin).val: σ ω = ω for all ω ⇒ σ = 1.
  Then `instance : IsFundamentalGroup (fiber k (SeparableClosure k)) Gal` and via
  mathlib toAutMulEquiv/toAutHomeo the identification with Aut F = π₁.
  ✓✓ AG-GG-3 COMPLETE (2026-07-06, beastmode-B) — all leaves + GaloisCategory
  instance, axiom-clean. File ForMathlib/FiniteEtaleFundamentalGroup.lean. Landing
  notes: (3a) fiber elements are NOT functions syntactically — `let x' : A →ₐ[k] Ω
  := x` (tactic-let keeps defeq; `have` loses it and breaks σ • x goals); action
  instance MUST be parameterized over general Ω — a SeparableClosure-headed
  MulAction instance gets isDefEqStuck at unification (Field-instance chains).
  (3d) `Fin 0 → k` is the subsingleton terminal (PLift bumps universes — avoid);
  FormallyEtale of it via the Pi-INSTANCE (pi_iff's family arg is explicit, awkward).
  (3e) AlgEquiv.ofInjectiveField lands in .range (Subalgebra) — its Algebra/
  IsScalarTower instances suffice for liftNormal, NO IntermediateField promotion
  needed; letI Field from isField_of_isIntegral_of_isField'. (3c) fixingSubgroup
  membership needs IntermediateField.mem_fixingSubgroup_iff (defeq intro fails);
  coset-openness via preimage under continuous_const.mul continuous_id.
  (3f) adjoin.finiteDimensional + isSeparable_tower_bot_of_isSeparable.
  CRITICAL DOWNSTREAM PROTOCOL: at CONCRETE k (e.g. ℚ) the topology/fundamental
  instances DON'T synthesize (mathlib's separableClosure instances are keyed on
  ↥(separableClosure F E), the abbreviation SeparableClosure unifies stuck, and
  the stuck-exception ABORTS search). Register two one-liners before use:
    instance : CompactSpace (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
      compactSpace_galSepClosure ℚ
    noncomputable instance : ... := isFundamentalGroup_galSepClosure (k := ℚ)
  (named bridges also exported: isSepClosure/isGalois/normal/isSepClosed/
  isSeparable_sepClosure). Probe at ℚ axiom-clean with this protocol.
- **[AG-GG-4]** 4a ✓✓ DONE (2026-07-06, beastmode-B):
  **`finiteEtaleEquivContAction k : (FiniteEtale k)ᵒᵖ ≌ ContAction FintypeCat
  (SeparableClosure k ≃ₐ[k] SeparableClosure k)`** — THE GALOIS CORRESPONDENCE,
  axiom-clean, any field k. mathlib's functorToContAction is already an equivalence
  given our GaloisCategory + FiberFunctor instances; composed with
  ContAction.resEquiv along new `toAutContinuousMulEquiv` (bundles toAutMulEquiv +
  toAut_isHomeomorph; the ▸-cast needs a `show Continuous ⇑e.symm` first).
  Consumers: `open scoped FintypeCatDiscrete` (HasForget₂ FintypeCat TopCat is
  scoped there; without it even statements fail).
  REMAINING 4b: Spec-side dictionary (finite étale algebra ↔ finite étale ℚ-scheme
  via Spec/Γ — affineness from finiteness) — the bridge from V_ρ-as-algebra to
  V_ρ-as-scheme for T-F1.
Then T-F1: `V_ρ := Spec` of the algebra attached to the `ContAction` `(ℤ/N)²`-via-ρ;
T-F1a/b specs = the equivalence's naturality; T-F1c group structure = group objects
transported along the equivalence (GrpObj/ofRepresentableBy — T-B2 experience
directly applicable). All leaves unclaimed.

### [T-F1] ⧗(AG-GG) V_ρ construction (DS5 discharge)
- ✓✓ **LANDED GREEN + AXIOM-CLEAN** (2026-07-06, beastmode-B): YRho.lean builds;
  `#print axioms` on vRho / rhoContAction / vRhoπ_finite_etale =
  propext/choice/Quot.sound ONLY — the whole AG-GG tower under V_ρ is sorry-free.
  T-F1a (finite étale) PROVED. **T-F1b COMPLETE (2026-07-07)**: `vRhoPointsEquiv`
  (one-term assembly: specPointsEquivAlgHom ∘ arrowCongr-bridge ∘
  pointsEquivOfContAction) AND `vRhoPointsEquiv_equivariant` (three-layer chase;
  seams: state the L1-translation lemma ∀-the-triangle-proof — re-elaborating the
  concrete subtype proof at the carrier spelling breaks rw; rhoContAction must be
  abbrev like rhoAction; Equiv.trans-applied goals need Eq.trans-of-congrArgs, not
  rw; counit equivariance = pointsEquivOfContAction_smul from Action.Hom.comm +
  ConcreteCategory.comp_apply). All axiom-clean. Remaining: T-F1c group structure.
  **T-F1c PLAN (banked 2026-07-07, beastmode-B)** — new file ModularCurve/VRhoGroup.lean:
  - F1c-1: `rhoSqContAction D` (carrier (Fin 2 → ZMod N) × (Fin 2 → ZMod N), diagonal
    ρ-action, continuity by the same coset argument) + `rhoAddMor : rhoSqContAction D ⟶
    rhoContAction D` (v,w ↦ v+w; equivariant since ρ σ is LINEAR — mulVec distributes)
    + zero/neg morphisms from the point-object.
  - F1c-2: rhoSqContAction ≅ categorical product (rhoContAction D) ⨯ (rhoContAction D)
    in ContAction (BinaryFan.IsLimit or transport from Action-products; check whether
    ContAction has/creates binary products — the full subcategory is closed under them:
    product action of continuous actions is continuous, same discrete-rng proof).
  - F1c-3: transport along (finiteEtaleEquivContAction ℚ).inverse: comultiplication
    `vRhoAlgebra D →ₐ[ℚ] (algebra of the square)` + identify the square's algebra with
    a pushout/tensor via the equivalence's product-preservation
    (equivalences preserve limits; PreservesLimitPair.iso) + my spanPushoutCocone.
  - F1c-4: Spec-side: `vRhoAdd : pullback (vRhoπ D) (vRhoπ D) ⟶ vRho D` via
    pullbackSpecIso (AlgebraicGeometry/Pullbacks:719) on the tensor; unit/inv/assoc
    laws by transport (or GrpObj-packaging via Functor.mapGrp if the monoidal
    plumbing on ContAction is available — check CartesianMonoidalCategory instances
    for Action FintypeCat / ContAction; grep came up EMPTY in Action/Monoidal.lean,
    so plan for hand-rolled BinaryFan routes as in AG-GG-1).
  - F1c-5 (spec): through vRhoPointsEquiv, vRhoAdd is coordinatewise addition on
    (ℤ/N)² — the morphism-level upgrade T-F3 wants for coords_additive.
  **F1c PROGRESS (2026-07-07, beastmode-B)**: F1c-1 ✓ GREEN (VRhoGroup.lean:
  rhoSqAction/rhoSqContAction + rhoAddMor/rhoZeroMor/rhoNegMor — equivariance from
  linearity, continuity by the coset argument; pointAction continuity via PUnit-eta
  rfl). F1c-2 ✓ GREEN (rhoSqIsProduct: BinaryFan.isLimitMk; uniq needs ext +
  congrFun-at-inaccessible — the ext-chain descends through Prod and funext).
  F1c-3 ForMathlib-half ✓ GREEN (FiniteEtaleGalois.lean TensorCoproduct section:
  tensorObj/tensorBinaryCofan(IsColimit)/tensorBinaryFanOpIsLimit — Etale.baseChange
  arg order is Etale N (N ⊗ M); never elaborate a fresh `*` between cone-leg factors
  across the const-functor carrier spelling — rw the factors in place).
  F1c-3 ✓ COMPLETE + **F1c-4 ✓ vRhoAdd GREEN, AXIOM-CLEAN** (2026-07-07):
  `vRhoSqAlgebraIso` (isLimitOfPreserves + postcomposeHomEquiv-along-pairComp +
  conePointUniqueUpToIso against tensorBinaryFanOpIsLimit — first-try green, op-unop
  eta bridges the pair diagrams); `vRhoComulHom` (unop of iso.inv ≫ inverse.map
  rhoAddMor); `vRhoAdd : pullback (vRhoπ D) (vRhoπ D) ⟶ vRho D` via
  AlgebraicGeometry.pullbackSpecIso (vRhoπ is definitionally Spec.map of the
  structure algebraMap, so the iso applies verbatim; qualify Spec.map).
  F1c REMAINING: zero/neg scheme-morphisms (same pattern: inverse.map rhoZeroMor/
  rhoNegMor, the point-object's algebra ≅ ℚ via the terminal identification),
  group laws (assoc/unit/inv — transport or direct via the equivalence's
  faithfulness), F1c-5 points-spec (vRhoAdd through vRhoPointsEquiv is coordinate
  addition — via pointsEquivOfContAction-naturality on rhoAddMor).
  (superseded planning note below:) the transport iso `(finiteEtaleEquivContAction ℚ).inverse.obj
  (rhoSqContAction D) ≅ Opposite.op (tensorObj (vRhoAlgebra D) (vRhoAlgebra D))` via
  isLimitOfPreserves inverse (rhoSqIsProduct D) vs tensorBinaryFanOpIsLimit +
  IsLimit.conePointUniqueUpToIso (pair-diagram seam: the two fans live over
  `pair X Y ⋙ inverse` vs `pair (op ..) (op ..)` — bridge with Discrete-pair natIso /
  Cones.postcompose, the standard Discrete.natIso plumbing). Then F1c-4 Spec-side
  (pullbackSpecIso) + comultiplication := inverse.map (rhoAddMor D), and F1c-5. Final seam notes in commit eab704fb
  (Filter.mem_map; intermediateFieldMap-f.d.-transport; open-scoped-Pointwise ABOVE
  docstring; **rhoAction must be abbrev** — structure projections don't reduce at
  instance-search transparency; coset endgame at Action-smul via ρτ = 𝟙 + map_id).
- **PROGRESS** (beastmode-B, 2026-07-06): **DS5 DATA-SORRY DISCHARGED** — `vRho`/`vRhoπ`
  are now REAL DEFINITIONS in YRho.lean via the completed AG-GG correspondence:
  `vRhoAlgebra D := ((finiteEtaleEquivContAction ℚ).inverse.obj (rhoContAction D)).unop`,
  `vRho D := Spec (.of (vRhoAlgebra D))`. Pieces landed: `sepClosureQAlgEquiv`
  (char-0: separableClosure = ⊤ via eq_top_iff + isSeparable_of_perfectField —
  needs `haveI := AlgebraicClosure.isAlgebraic ℚ` first, it does NOT synthesize
  bare), `galSepMulEquivGalQ := AlgEquiv.autCongr` + Krull-continuity
  (`continuous_of_continuousAt_one` on the toMonoidHom + `krullTopology_mem_nhds_one_iff`
  both sides, transporting fixing subgroups along `E.map e.symm.toAlgHom`),
  `galSepContinuousMulEquivGalQ` (compact-to-T2: `Continuous.homeoOfEquivCompactToT2`
  INLINE — a `have hh :=` loses defeq and the invFun-coercion mismatches;
  `haveI : T2Space GalQ := krullTopology_t2` needs the IsAlgebraic haveI),
  `rhoAction` (End-fields need `FintypeCat.homMk` + `FintypeCat.hom_ext _ _ fun v =>`;
  bare `ext` finds no @[ext] lemma for `End (FintypeCat.of _)`), `rhoAction_ker_open`
  (preimage of D.ker_open), `rhoAction_isContinuous` (discrete-rng + union of left
  cosets of the open kernel; `DiscreteTopology` haveI := ⟨rfl⟩ on the forget₂-TopCat
  carrier), `rhoContAction`, and **T-F1a PROVED** (2 lines: `IsFinite.SpecMap_iff` +
  `RingHom.finite_algebraMap`; `HasRingHomProperty.Spec_iff (P := @Etale)` +
  `RingHom.etale_algebraMap` — object-property instances fire). Also landed
  `pointsEquivOfContAction` (ForMathlib/FiniteEtaleFundamentalGroup, GREEN): the
  correspondence counit as an Equiv of finite sets — the T-F1b core.
  **BUILD PENDING**: sibling beastmode-A's T-A8a WIP in EllipticCurve/Basic.lean is
  transiently red (uncommitted working-tree edits); YRho imports it. Background
  watcher armed; on green: one `lake build ModularCurves.ModularCurve.YRho` iteration,
  then commit + axiom-check probe (remember the two concrete-ℚ instance registrations
  are IN the file already).
  **T-F1b REMAINING** (chain designed): {h // triangle} ≃ (A →ₐ[ℚ] ℚ̄) via
  Spec.preimage-bijection (EtaleSectionsCount pattern), ≃ (A →ₐ[ℚ] SepCl) via
  `AlgEquiv.arrowCongr` along `sepClosureQAlgEquiv.symm`, then DEFEQ to the fiber of
  `inverse.obj (rhoContAction D)` (op-unop eta), then `pointsEquivOfContAction`, then
  carrier-defeq to `Fin 2 → ZMod N`. Equivariance spec (vRhoPointsEquiv_equivariant)
  after. v8 review checked: T-F* stays on the spine, COH non-blocking, no impact.
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
  - **Claimed**: beastmode-D2, 2026-07-07T05:50Z. Status: in-progress. Quote-gate ✓
    KM 1.1.1 verbatim read at claim (p. 3): "By an effective Cartier divisor D in
    X/S we mean a closed subscheme D ⊂ X such that: D is flat over S; the ideal
    sheaf I(D) ⊂ O_X is an invertible O_X-module … When S is affine, say
    S = Spec(R), it means that we can cover X by affine opens Uᵢ = Spec(Aᵢ) …
    such that D ∩ Uᵢ is defined in Uᵢ by one equation fᵢ = 0 … Aᵢ/fᵢAᵢ is flat
    over R; fᵢ is not a zero-divisor in Aᵢ." SCOPE: (1) `IsOfficialCartier` as a
    2-field Prop structure — global flatness of the subscheme over S (KM clause 1)
    + affine-local principal-nzd ideal (KM's affine unpacking, decoupled: given the
    covering, per-chart quotient-flatness ⟺ global flatness); invertible-MODULE
    interface stays T-D19 (AG-LB). (2) Zariski-locality plumbing as needed by
    consumers. (3) THE MEAT — `RelEffCartierDiv.isOfficial` : working ⟹ official
    for smooth separated rel-dim-1 C/S, attempting an HB-NOETH-FREE route (vs KM
    1.2.3's noetherian reduction): ideal is loc. fg (lfp closed immersion via
    cancellation against smooth), fibre-generator at x ∈ D from DVR stalks of the
    fibre curve (x is closed in its fibre since D_s is finite; T-D23 REVIVES as
    sub-ticket if mathlib lacks smooth-over-field ⟹ DVR stalks — fallback route =
    T-D22's étale-over-𝔸¹ + Jacobi–Zariski toolkit), then Nakayama-spread f from
    the fibre (I/(f) fg + vanishes on fibre) and nzd-spread by S-flatness of A/I
    (T-D22's torsion-free technology). Sections-give-ECDs = corollary (also =
    T-D22 directly). (4) Converse (official + proper-over-S ⟹ working) statement +
    ZMT attempt (`IsFinite.of_isProper_of_locallyQuasiFinite` PRESENT per
    decomposition); register/park if the fibre-finiteness leg (dim-0 + finite-type
    ⟹ finite) is heavy. If (3)'s Nakayama-spread genuinely needs noetherian input,
    REGISTER a box for exactly that step, never silently weaken.
  - **Progress** (2026-07-07T06:40Z): skeleton green (def + isOfficial + lfp/isFinite
    legs + toRelEffCartierDiv assembly). ROUTE REFINED after probing: WAVE-1
    (delegated, in flight) = ForMathlib/PrincipalMaximalDVR.lean — nontrivial
    noetherian local + maximalIdeal = span{nzd non-unit} ⟹ IsDomain + DVR (Krull
    intersection + order-extraction; `IsDiscreteValuationRing.TFAE` confirmed in
    mathlib). WAVE-2 (next, ForMathlib/StandardSmoothStalkDVR.lean) = fibre-side ring
    theory for std-smooth-1 over a field k: thm-A `Localization.AtPrime q` is a DVR
    given I ≤ q with Module.Finite k (A⧸I) (route: Ω free rank 1
    (rank_kaehlerDifferential) + span_range_derivation coordinate-extraction ⟹ dg
    generates Ω on an away-shrink ⟹ Jacobi–Zariski (mirror in-file
    kerPrincipalAux_nzd lines ~589-608: H1Cotangent.exact_δ_mapBaseChange/exact_map_δ)
    ⟹ FormallySmooth k[X] + fp-of-away ⟹ Smooth ⟹ flat (`Algebra.Smooth.flat` ✓
    instance) ⟹ π := q₀-generator-image nzd; m = q₀O via `Algebra.Etale.
    iff_exists_algEquiv_prod` (RingTheory/Etale/Field.lean ✓ EXISTS) on the étale
    fibre; field-case killed by k[X] ↪ O torsion-free vs O = localization of the
    fin-dim A/I (`IsArtinianRing` loc-is-quotient) — NOTE Localization.AtPrime is NOT
    fp, so Smooth.flat applies only at away-level, then localize); thm-B I·O_q ≠ ⊥
    (Artinian-DVR contradiction); thm-D f ∈ nonZeroDivisors A whenever
    Module.Finite k (A⧸span{f}) — KEY SIMPLIFICATION: nzd is stalk-local, and at each
    maximal m the thm-A dichotomy + fin-dim contradictions close both branches — NO
    reducedness, NO Ass-theory needed. WAVE-3 = scheme assembly in CartierDivisor.lean
    (chart opener = hsm.exists_isStandardSmoothOfRelativeDimension per in-file
    pattern; I fg via `Algebra.FinitePresentation.ker_fG_of_surjective` ✓ mathlib;
    fibre comparison I⊗κ ↪ A⊗κ from D.flat chart-form Tor-vanish; Nakayama-spread at
    O_x + fg-support; T-FLAT1 slicing BOX registered for the total-space nzd step —
    ADVERSARIAL: naive noetherian-free local slicing is FALSE (M = m over a rank-1
    non-discrete valuation ring, u = 0: M/mM = 0 vacuously regular, M ≠ 0), so the
    box carries fp hypotheses honestly (EGA IV 11.3.10 nzd part)). WAVE-4: lfp leg
    (principal ⟹ fg ⟹ fp quotient); isFinite leg AT RISK — decomposition's claim
    "mathlib ZMT IsFinite.of_isProper_of_locallyQuasiFinite PRESENT" is STALE/WRONG
    (searched: absent; mathlib has IsFinite = IsIntegralHom ⊓ LocallyOfFiniteType,
    affine-over-S is the hard part) — park-eligible per claim scope.
  - **BOX REGISTERED** (2026-07-07T07:20Z; SOURCE/TICKET RECONCILED 2026-07-07T14:40Z):
    `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` (CartierDivisor.lean, tag
    T-FLAT1-SLICE) — fp+flat hypotheses, ∀-field-fibre form (deliberately: what thm-D
    supplies uniformly AND the easiest-to-discharge shape — a future discharge proves
    the residue-field form and specializes). Falseness-without-fp counterexample in the
    docstring. Sole permitted consumer: RelEffCartierDiv.isOfficial.
    **THIS IS A SUB-INSTANCE OF THE EXISTING FLAT STREAM `T-FLAT1`** (the fibre-by-fibre
    flatness criterion): specifically the *regular-element-by-fibres* companion, sibling
    of HB-FIBCRIT (KM 1.1.5.1 = the coherent-sheaf version). SOURCE CORRECTION: the
    docstring's "EGA IV 11.3.10" tag is a pointer, NOT a source I hold — EGA and
    Altman-Kleiman [A-K 1, V 3.6] (KM's actual citation) are NOT in refs/, and KM only
    CITES the criterion without proof. Do NOT try to fetch EGA: (a) unavailable locally,
    (b) unnecessary. The mathematically-standard, mathlib-aligned reference is the
    **local criterion of flatness by fibres** (Stacks Tag 00MH / 051C — regular-element
    form). MATHLIB SURVEY (2026-07-07): NO Tor in RingTheory, NO local-criterion lemma
    (`localCriterion` empty) — genuinely absent, a real ~100-200-line development, not a
    name-lookup. BUT the **equational criterion of flatness** IS present
    (`Mathlib/RingTheory/Flat/EquationalCriterion.lean`: `isTrivialRelation_of_sum_smul_
    eq_zero`), giving a **Tor-FREE proof route**: for `f·a = 0` in the fp flat A, the
    relation `f·a = 0` is a trivial relation (equational criterion on A flat/R), factor
    `a = Σ cⱼ zⱼ` with `Σ f cⱼ = 0`; the flatness of `A/fA` forces (via the same criterion
    on the quotient) the `cⱼ` into `fA`, and the fibrewise-nzd hypothesis at each residue
    field collapses `a`'s image to 0 in every fibre; fp + fibrewise-zero + the
    isSMulRegular/torsion-free toolkit (`Flat/TorsionFree.lean` `isSMulRegular_of_
    nonZeroDivisors`, `IsSMulRegular.of_flat`) closes `a = 0`. DISCHARGE = a proper
    T-FLAT1 proof-ticket (below); NOT started (isOfficial's ⇐-completeness does not
    block on it — the working definition is primary). WAVE-1 DONE
    (delegate, first-try, axiom-clean): ForMathlib/PrincipalMaximalDVR.lean —
    `IsLocalRing.exists_eq_pow_mul_unit_of_maximalIdeal_eq_span` (public
    order-extraction), `IsDomain.of_maximalIdeal_eq_span_nonZeroDivisor`,
    `IsDiscreteValuationRing.of_maximalIdeal_eq_span`; deltas: Nontrivial redundant
    (IsLocalRing extends it), ¬IsUnit redundant, TFAE 0↔4 route; Krull intersection
    = `Ideal.iInf_pow_eq_bot_of_isLocalRing` (Filtration.lean:431). GAP CONFIRMED:
    mathlib has NO principal-max⟹DVR without a priori IsDomain. WAVE-2 dispatched
    (StandardSmoothStalkDVR.lean, delegate in flight): thm-AB
    `exists_span_nonZeroDivisor_map_localizationAtPrime` + thm-D
    `mem_nonZeroDivisors_of_finite_quotient`. WAVE-3 core designed (chart-ring
    level): fibre-stalk generator f CHOSEN IN THE IMAGE OF I by valuation-Nakayama
    (span{ι(i)} + m·IO = IO for some i, else IO = m·IO = 0 contra nzd), then
    I/(f) fg + fibre-vanishing ⟹ M_q = pM_q ⊆ m M_q ⟹ Nakayama ⟹ away-shrink
    r ∉ q with I_r = (f); box-input fibrewise-nzd = thm-D at every κ(p')
    ((A_r/I_r)⊗κ finite via IsArtinianRing.localization_surjective). Scheme glue:
    chart opener hsm.exists_isStandardSmoothOfRelativeDimension; Γ-dictionary for
    subscheme quotients per sectionsIdealAux/toSpecΓ_naturality pattern.
  - **isFinite leg: PARK DECISION** (2026-07-07T07:50Z): mathlib HAS
    `IsFinite f ↔ IsProper f ∧ IsAffineHom f` (Morphisms/Proper.lean:93), so the
    KM 1.2.3 (⇒) leg reduces EXACTLY to affineness of a proper locally-quasi-finite
    morphism = Zariski's Main Theorem (EGA IV 8.11.1) — genuinely absent from
    mathlib and its own project. `IsOfficialCartier.isFinite` stays a sorried
    producer-WIP (statement frozen, correct); `toRelEffCartierDiv` assembled
    against it. NOT a register box (no downstream consumer needs it; the working
    def is primary — the ⇒ direction is review-completeness only). Candidate
    future ForMathlib target: ZMT for schemes. Wave-3a prompt banked
    (scratch wave3a-prompt.md) incl. the localization-transitivity fix: O =
    AtPrime(q/pA) of A/pA via submonoid-composition, making the fibre-vanishing ⟹
    M_q = 0 Nakayama transfer sound; fibre-injectivity route = equational
    criterion (Flat/EquationalCriterion.lean) for I ∩ pA = pI, then κ = Frac(R/p)
    localization transport.
  - **WAVE-2 DONE** (beastmode-D2, 2026-07-07T09:30Z — Opus 4.8 salvage):
    ForMathlib/StandardSmoothStalkDVR.lean PROVED, both consumer theorems
    (`exists_span_nonZeroDivisor_map_localizationAtPrime`,
    `mem_nonZeroDivisors_of_finite_quotient`) axiom-clean (standard three), 594
    lines. NOTE: the two Fable-5 delegates (wave-2 + wave-3a) BOTH died mid-run on
    a usage-credit wall; wave-2's delegate had written a coherent 594-line draft
    before dying (build-broken, ~10 localized errors). Per salvage protocol I
    preserved (scratchpad/wave2-crashed-594.lean) and REPAIRED in place rather than
    discarding: the Jacobi-Zariski core (H1Cotangent.exact_δ_mapBaseChange/
    exact_map_δ), away-localization std-smooth transport
    (`IsStandardSmoothOfRelativeDimension.localization_away` — THE right API, dim-0),
    prime transfer (`isLocalization_of_submonoid_le` +
    `isLocalization_of_is_exists_mul_mem`), étale-fibre DVR analysis
    (FormallyUnramified.map_maximalIdeal over the field-fibre) + the
    PrincipalMaximalDVR criterion, and ideal classification
    (`IsDiscreteValuationRing.ideal_eq_span_pow_irreducible`) were ALL sound. Fixes:
    dot-notation on prime instances (`‹q.IsPrime›.ne_top`/`.mem_of_pow_mem`),
    `mk'_surjective` pair-destructure `⟨⟨a,s⟩,rfl⟩`, `IsPrime.to_maximal_ideal`
    (ROOT namespace, not `Ideal.IsPrime.`), `Units.mkOfMulEqOne` (no
    `isUnit_of_mul_eq_one` in this pin), and — the load-bearing one —
    `isLocalization_of_is_exists_mul_mem` / `EssFiniteType.of_isLocalization` take
    the localization RING `S` as FIRST EXPLICIT arg (delegate passed the submonoid
    there → `CommSemiring ↥(submonoid)` synth failure). GOTCHAS BANKED. WAVE-3a
    (officialAux chart core) delegate ALSO died on credits before writing anything —
    CartierDivisor.lean intact; route fully banked (scratchpad/wave3a-prompt.md).
    REMAINING for T-D11: wave-3a (chart-level `officialAux_exists_away_span`) +
    wave-4 isOfficial scheme assembly (mine); isFinite leg parked (ZMT).
  - **WAVE-3a FIBRE TRANSPORT — verified peer contribution** (2026-07-07T13:40Z):
    a sibling session delivered `exists_mem_fibre_principal` (fibre-level
    principality of I·S in the stalk-fibre S/pS, generator drawn from I) —
    scratchpad/ai_fibre_complete.lean, 246 lines, which I INDEPENDENTLY VERIFIED
    (compiles clean, #print axioms = standard three, no sorryAx). This discharges
    my route's steps 3-5 (the κ ⊗[R/p] (A/pA) transport — the hardest part) via
    `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` + `.of_algEquiv` +
    `rightAlgebra`/`IsLocalization.tensorRight` + `localizationAlgebraOfSubmonoidLe`.
    My Opus wave-3a delegate redirected (SendMessage) to ADOPT this lemma and finish
    only the two remaining legs: (6) Nakayama lift+spread fibre-principal ⟹
    away-principal on Localization.Away r (r ∉ q), (7) nzd via the T-FLAT1-SLICE box.
    Two efforts converged onto one verified building block.
  - **WAVE-3a DONE** (beastmode-D2, 2026-07-07T14:10Z): `officialAux_exists_away_span`
    PROVED + integrated into CartierDivisor.lean (Opus delegate; +526 lines, 8
    `officialAux_*` privates). INDEPENDENTLY VERIFIED by me: build green (exactly the
    3 pre-existing box/isOfficial/isFinite sorries, +526/−0), and #print axioms
    confirms `officialAux_exists_away_span` = [propext, sorryAx, Classical.choice,
    Quot.sound] with sorryAx tracing ONLY through `officialAux_away_nzd`→the box;
    both cruxes `officialAux_stalk_span` (fibre-descent) and
    `officialAux_flat_ideal_inf_le` (EGA flat-descent I⊓pA≤pA·I) individually
    standard-three clean. Helpers: flat_ideal_inf_le, exists_mem_fibre_principal
    (κ⊗A base change + wave-2 field-case + Nakayama generator descent), stalk_span
    (IsLocalization.map_inf + Submodule.le_of_le_smul_of_le_jacobson_bot), spread,
    finite_quotient_loc, fibre_nzd, away_nzd. Key names banked:
    `Algebra.IsStandardSmoothOfRelativeDimension.baseChange`,
    `IsLocalization.tensorProduct_tensorProduct_right`,
    `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, `Ideal.map_mapₐ`. REMAINING
    for T-D11 ⇐: WAVE-4 `isOfficial` scheme assembly (dispatched, Opus) — chart
    translation of D.finite/flat/lfp→ring hyps + officialAux + basicOpen transport,
    mirroring T-D22's `exists_affineOpen_ker_principal_nonZeroDivisor`.
  - **WAVE-4 DONE (body) + NEW GAP ISOLATED** (beastmode-D2, 2026-07-07T15:55Z, Opus
    delegate + independently verified): `RelEffCartierDiv.isOfficial` BODY PROVED
    sorry-free (+144 lines). Full scheme translation landed: off-support unit-ideal
    branch (mirrors T-D22 neg branch), appLE-algebra bridge, `HasRingHomProperty.appLE
    @Flat`/`@LocallyOfFinitePresentation` transport of D.flat/D.lfp to `Module.Flat/
    FinitePresentation R (A⧸I)`, `I.FG` via `FinitePresentation.ker_fG_of_surjective`,
    point→prime `IsAffineOpen.primeIdealOf` + `mem_support_iff_of_mem`, officialAux ring
    core, and `IsLocalization.algEquiv` basicOpen transport (`map_ideal_basicOpen` +
    `MulEquivClass.map_nonZeroDivisors`). VERIFIED: build green, #print axioms isOfficial
    = [propext, sorryAx, Classical.choice, Quot.sound]. sorryAx = EXACTLY two isolated
    sources: (1) T-FLAT1-SLICE box, (2) NEW **[T-D11-FINCHART]** box below.
  - **[T-D11-FINCHART] BOX REGISTERED** (the finiteness gap wave-4 surfaced):
    `officialAux_exists_finite_chart` (CartierDivisor.lean ~2304, sorried). FINDING
    (real, subtle — my wave-4 plan MISSED it): `Module.Finite R (A⧸I)` — needed by
    officialAux — is NOT source-local. `IsFinite = affineAnd RingHom.Finite` is
    Zariski-local-at-TARGET only, so `A⧸I = Γ(D∩V₀)` is finite over R IFF `D∩V₀` is
    CLOPEN in D, i.e. the std-smooth chart must capture the ENTIRE (finite, by D.finite)
    D-fibre over π(c). An arbitrary chart FAILS: counterexample `V(tx−1) ⊆ 𝔸¹` escapes
    to infinity ⟹ `A⧸I ≅ R[t,t⁻¹]` non-finite. DISCHARGE = "finitely many points of a
    smooth separated curve lie in one affine open" (+ std-smoothness of the enlarged
    chart + base-shrink closedness) — mathlib-ABSENT (no clopen/idempotent tooling for
    finite morphisms). MIRRORS the file's EXISTING sections-only machinery
    (`sectionsIdealAux_exists_chart` + `exists_groupChart` + disjoint-pieces gluing,
    ~200 lines) generalized from a section's image to a general finite subscheme —
    DISCHARGEABLE (~200 lines) by reusing/generalizing that. Everything else in
    isOfficial (flat/fp/FG/point-prime) is source-local + fully discharged. NET T-D11 ⇐:
    body proven modulo 2 boxes ([T-FLAT1-SLICE]→T-NOETH being built; [T-D11-FINCHART]→
    this generalization). T-D11 ⇒ (`isFinite`) parked (ZMT).
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
  - **Status**: done (beastmode-D2, 2026-07-06T14:45Z → 2026-07-06T22:00Z) —
    **`exists_incidenceLocusLE` (KM 1.3.4 KEY LEMMA) PROVED sorry-free, standard
    axioms**. Witness: `Z := vanishingLocus (D'.ι ≫ π) (D.ideal.comap D'.ι)`;
    proof = the a/a′/b lemmas + vanishingLocus_le_ker_iff + a Galois opener
    (mirroring ker_fst_of_isClosedImmersion + ker_subschemeι so the terminal
    goal closes syntactically) + one iso-transport aux
    (`incidenceAux_comap_eq_bot_iff`: comap along compatible iso preserves ⊥;
    iso = pullbackSymmetry ≪≫ pullbackRightPullbackFstIso π t D'.ι ≪≫
    pullbackSymmetry; leg-compat = one `simp [pullback.condition]`).
    `hsm`/[IsSeparated] unused by this route (statement furniture — the
    count-free construction never needs principality). CLEANUP DEBT (paused):
    the ~400-line vanishingLocusAux_* block + this file générally → CLEANUP-9.
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
  - **Progress**: 2026-07-06T21:15Z — **[T-D14c-2] COMPLETE sorry-free, standard
    axioms, committed d355db4e** (delegated; 9 private vanishingLocusAux_*
    helpers, ~400 lines). ARCHITECTURE OF RECORD (simpler than planned — worth
    reusing): χ (tensor→scheme) = `Algebra.TensorProduct.productMap` of the two
    appLEs into Γ(PB, fst⁻¹V ⊓ snd⁻¹D) (towers by of_algebraMap_eq' +
    appLE_comp_appLE ×2 + simp[pullback.condition]) — NO pushout-square
    computation; ψ (scheme→tensor) = `pullback.lift` of fromSpec-legs
    (SpecMap_appLE_fromSpec + includeLeftRingHom_comp_algebraMap) evaluated
    with fromSpec_app_self/map_appLE_assoc/ΓSpecIso_naturality — NO IsPushout,
    NO coconePointUniqueUpToIso. Both directions pointwise (le_ker_iff_forall)
    + sheaf-injectivity (`TopCat.Sheaf.eq_of_locally_eq'`) over point-indexed
    covers; (⟹) refines an arbitrary W-affine by basicOpens inside p⁻¹U +
    `Submodule.span_induction`. CORRECTIONS TO THE PLAN: (1) `pullback.snd t p`
    is NOT quasi-compact (it base-changes t, not p) — the iInf_ker route was
    wrong; pointwise replaces it. (2) `map_ideal` works for arbitrary affine
    pairs — no basicOpen gymnastics. GOTCHAS: appLE ⊤ ⊤ = appTop needs a
    3-line helper (preimage_top rfl + proof-irrelevance); core `Functor.map_id`
    shadows CategoryTheory's in rw; rewrite at HYPOTHESES to inherit lemma
    spelling (invisible instance-spelling defeats rw on hand-spelled terms);
    prefer `exact map_zero _` over `rw [map_zero]` on presheaf maps. Names:
    `IsAffineOpen.SpecMap_appLE_fromSpec`, `Scheme.Hom.comp_preimage` (rfl),
    `Scheme.Hom.preimage_mono`, `Algebra.TensorProduct.productMap_apply_tmul`.
    REMAINING FOR T-D14 = ASSEMBLY ONLY: instantiate W := D'.ideal.subscheme,
    p := D'.ι ≫ π (fields = D'.finite/flat/lfp), E := D.ideal.comap D'.ι;
    Z := vanishingLocus p E; chain: ∃h ⟺ Z ≤ t.ker (T-D14a′) ⟺(c-2)
    E.comap (snd t p) = ⊥ ⟺(pasting iso pullback t (D'.ι≫π) ≅
    pullback (fst π t) D'.ι — pullbackRightPullbackFstIso/pullbackAssoc +
    ker_comp_of_isIso + comap_comp) comap_ft I_D ≤ comap_ft I_D'
    (map_bot-Galois) ⟺(T-D14b ×2) (D.bc t).ideal ≤ (D'.bc t).ideal ⟺(T-D14a)
    IsSubdivisor (D'.bc t) (D.bc t).
  - **Progress**: 2026-07-06T18:40Z — **[T-D14c-i] DONE sorry-free** (delegated
    fill, verified green + standard axioms, landed via sibling sweep):
    `exists_affineOpen_mem_free` — free cover of a finite flat lfp morphism.
    DISCOVERIES OF RECORD: (1) the localization-transport keystone is
    `Module.Free.iff_of_equiv` (SEMILINEAR, FreeModule/Basic) used exactly as in
    mathlib's `Module.mem_freeLocus_of_isLocalization` — the whole
    compHom/Basis.mapCoeffs dance collapses to one semilinear equiv over
    σ := IsLocalization.algEquiv; supply only map_smul', closed by
    denominator-killing (`(Module.End.isUnit_iff _).mp (map_units …)).1` +
    `simp [← map_smul, ← smul_assoc]`); in-proof RingHomInvPair via
    `haveI := RingHomInvPair.of_ringEquiv e` + `.of_ringEquiv_symm e`.
    (2) Localized Finite/Flat instances are AUTOMATIC
    (Localization/Finiteness.lean:175, Flat/Stability.lean:116 —
    `Module.Flat.localizedModule`). (3) `RingHom.Flat → Module.Flat` delta-defeq
    under matching toAlgebra letI (same as the FinitePresentation move);
    `HasRingHomProperty.appLE @Flat` works. (4) affine-start idiom:
    `TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens` +
    `replace hU₀ : IsAffineOpen U₀ := hU₀`. (5) `S.affineBasicOpen` needs
    (U := ⟨U₀,hU₀⟩) explicit. (6) membership dictionary defeq-tight:
    `fromSpec_preimage_basicOpen` + `fromSpec_primeIdealOf`. (7) parser: hoist
    multi-line `{ __ := … }` fields into a have. REMAINING for c-2: the two
    directions of `vanishingLocus_le_ker_iff` ([c2-ii] Γ-pushout dictionary =
    mathlib `isPushout_appTop_of_isPullback` (Morphisms/Affine.lean:208) +
    `IsAffine.of_isPullback`; T-affine reduction via
    `Hom.iInf_ker_openCover_map_comp` + `Scheme.Pullback.openCoverOfLeft`;
    then the T-D14c bridge + `X.IsSheaf.section_ext`).
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
  - **Status**: done (beastmode-D2, 2026-07-06T22:05Z) — PROVED sorry-free,
    standard axioms, 5-line proof: `Z := Z₁ ⊔ Z₂` from T-D14 applied both ways;
    `exists_factor_subschemeι_iff` + `sup_le_iff` + the two universal
    properties. NO degree argument needed (the frozen mutual-subdivisor form
    bypasses KM's same-degree reduction entirely); T-D26's wrapper never
    enters. Incidence.lean remaining sorries: T-D16/T-D17/T-D18 only.
    T-D16 ROUTE BANKED: the (3)-condition's (deg D)²-descent IS a second
    application of `vanishingLocus` (Z_S := vanishingLocus (W-structure) Z_W —
    the operator is KM's coordinate-descent), so T-D16 = sup of three loci
    ([e] ≤ D via T-D14 at A's sectionDivisor of E.zero; D = inv*D via T-D15 at
    the iso-pullback divisor; [m(P₁,P₂)] ≤ D_W via T-D14-over-W +
    vanishingLocus-descent) + the IsSubgroup ⟺ three-conditions dictionary
    (D-inc.3(c) — the remaining NEW content).
- **[T-D16]** `exists_subgroupLocus` (KM 1.3.7, verbatim + proof in hand;
  `1 + deg + deg²` equations via `[e] ≤ D`, `D = inv*D`, `[m(P₁,P₂)] ≤ D_W`).
  Depends: T-D14, T-D15, T-D3.
  - **Status**: done (beastmode-D2, 2026-07-06T22:30Z → 2026-07-06T23:50Z) —
    **`exists_subgroupLocus` (KM 1.3.7) PROVED sorry-free, standard axioms**
    (delegated; 615 lines of subgroupLocusAux_* privates). CONSTRUCTION:
    Z := Z₁ ⊔ Z₂ ⊔ Z₃ — Z₁ = T-D14 at [e] := sectionDivisor E.zero;
    Z₂ = T-D14 at inv*D (NEW private invD := comap along mulByHom (-1);
    SIMPLIFICATION vs banked plan: ONE incidence-LE locus suffices — the single
    containment powers neg_mem both ways by comap calculus, no EQ-locus);
    Z₃ = vanishingLocus q (T-D14-over-W at the tautological-pair-sum section),
    W := D ×ₛ D — vanishingLocus IS the (deg D)²-descent. Conditions
    normalized t-level: comap-⊥/comap-≤ forms. DICTIONARY (the new content):
    ⟸ AddSubgroup with carrier {P | (D.bc t).ideal.comap P.1 = ⊥}; ⟹
    instantiations at 𝟙, the universal D_T-point, the tautological pair over
    T ×ₛ W. KEY DEFEQ WINS: point-addition val is `rfl`-transparent
    (`(P+Q).1 = pullback.lift P.1 Q.1 _ ≫ μ` — Equiv.addCommGroup transport +
    Hom.mul_def + Over.lift_left all defeq); μ-projection via
    `Over.μ_pullback_left_fst_fst'` mathlib lemmas. GOTCHAS OF RECORD:
    (1) the asSection/baseChange defeq-straddling trap is PERVASIVE — raw-typed
    aliases + obtain-rebinding at raw types + Iff.of_eq (congrArg (· = ⊥) h)
    instead of rw at mixed junctions; (2) pin pullback.lift's (f :=) at bc-
    spellings; (3) AddSubgroup anonymous-constructor field ORDER is add/zero/neg
    (declaration order); (4) Hom.mul_def lives at CategoryTheory.Hom.*; (5)
    DEDUP for /cleanup post-merge: subgroupLocusAux_{zero_val,mulBy_comp,
    mulByHom_neg_one_involutive} duplicate point_zero_val (TorsionFibre:254) +
    GammaH.lean:409-441 lemmas (outside Incidence's import closure — flagged,
    not fixed, imports were frozen). Incidence.lean remaining sorries: ONLY
    T-D17 + T-D18. v8 note: T-W8 consumes these loci over the atlas U.
    Route banked in the T-D15 done-note: three loci sup + vanishingLocus-as-
    coordinate-descent for condition (3) + the IsSubgroup ⟺ three-conditions
    dictionary (functor-of-points AddSubgroup form per ExactOrder.lean:91).
    Recon next: inv*D iso-pullback divisor construction; A's sectionDivisor
    signature; the m/inv morphisms + tautological-pair infrastructure in
    GroupLaw; universal-point instantiation pattern (T-B3's pointToTorsion).
- **[T-D17]** `exists_exactOrderLocus` (A-generators, `A = ℤ/N`; KM 1.6 instance).
  Depends: T-D16. Feeds T-E7.
  - **Status**: done (beastmode-D2, 2026-07-06T22:55Z → 2026-07-07T00:20Z) —
    **`exists_exactOrderLocus` PROVED** (commit 69e0901b), Incidence module
    green. AXIOMS: standard three + `sorryAx` inherited EXCLUSIVELY through
    REGISTERED boxes (T-D3/T-D1 `sectionsIdeal_isFinite/flat/lfp` +
    T-B4 KM 2.3.1 BB-QF/BB-FLAT via torsionπ_isFinite/flat) — provenance
    verified decl-by-decl; all in-file D-chain engines
    (exists_subgroupLocus/EQ/vanishingLocus/torsionIdeal_subscheme) are CLEAN.
    Construction: Z := exists_subgroupLocus (E.baseChange (torsionπ N))
    (orderDivisor (asSection u)) at the universal killed point u := torsionι;
    universality at c := pointToTorsion P hP via per-point additive transport
    (ψ/φ E-value projections + T-D16 add/zero/neg bridges) + the SHARED ENGINE
    `exactOrderLocusAux_ker_comap_eq` (raw-typed two-sided ker-comap comparison
    by le_ker_comp-antisymmetry with two pullback.lift comparisons — reusable). Route: T-D16 over the base E.torsion N at the universal
    torsion point's orderDivisor; HasExactOrder := (orderDivisor).IsSubgroup
    (ExactOrder.lean:105) makes the RHS the T-D16-condition at the base-changed
    section; classifying-map equivalence by pullback.lift uniqueness
    (pointToTorsion dictionary, Torsion.lean:50-72) + Point.pull/asSection
    naturality (pull_zsmul exists; orderDivisor-baseChange compat =
    sectionsDivisor-pullback bookkeeping).
- **[T-D18]** `exists_fullLevelLocus` (`A = (ℤ/N)²`). Depends: T-D16. Feeds T-E9.
  - **Status**: done (beastmode-D2, 2026-07-06T22:55Z → 2026-07-07T00:20Z) —
    **`exists_fullLevelLocus` PROVED** (same commit; Incidence.lean now has
    ZERO sorries — the ENTIRE KM 1.3–1.6 INCIDENCE CHAIN T-D13→T-D18 IS
    COMPLETE). Axioms: standard + sorryAx through registered boxes only (same
    provenance audit as T-D17). Construction: Z := exists_incidenceLocusEQ over
    E[N] ×ₛ E[N] between the universal pair divisor Σ[a·u₁+b·u₂] and the NEW
    `fullLevelLocusAux_torsionDivisor` (E[N] as RelEffCartierDiv from
    torsionπ_isFinite/flat + NEW torsionπ_lfp, transported along T-B3a);
    killed-clause FREE from hP/hQ; NEW standalone
    `fullLevelLocusAux_torsionIdeal_baseChange` (E[N]-formation commutes with
    base change at ideal level — reusable, feeds T-D8/T-B6-style work).
    GOTCHAS added to the trap-notes: baseChange-seam rewrites need
    freshly-elaborated have/calc + congrArg-at-typed-motives; `rw [P1,P2]`
    fails on instance-transparency — `Iff.of_eq (congrArg₂ Eq P1 P2)`;
    IsFullLevel's family literal has an extra grouping paren. MILESTONE:
    unblocks T-E7 (Y₁(N)) and T-E9 (Y(N)) representability feeders + v8's
    T-W8 atlas-level spaces. CLEANUP DEBT (paused): ~1000 new aux lines +
    dedup flags recorded in T-D16 note → CLEANUP-9/10. Same pattern over
    pullback (torsionπ N) (torsionπ N) with the (ℤ/N)²-divisor Σ[aP+bQ];
    IsFullLevel def at Basic.lean:183 — read at execution for the exact
    divisor-equality form (A-generator EQ-locus per D-inc.4 = T-D15/T-D14 +
    degree bookkeeping).
- **[T-D19]** `ecd-pair-section-interface` — `D ↔ (L, s)`, sum = tensor. BLOCKED on
  AG-LB. Sources: KM 1.2 (in hand).
- **[T-D20]** flat pullback along `Y → X` + composition laws. Depends: T-D12.
  - **Claimed**: beastmode-D2, 2026-07-07T04:05Z. Status: in-progress. SCOPE per
    KM p. 6 verbatim (quote-gate ✓ read at claim: "any effective Cartier divisor D
    in X/S gives rise to an effective Cartier divisor f*(D) in Y/S … the ideal
    sheaf I(f*(D)) is none other than f*(I(D)) … the short exact sequence …
    remains short exact after f*, thanks to the flatness of f"): (a) def
    `flatPullback` along `f : C' ⟶ C` over `S` with `[IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f]` (our structure carries finite/flat/lfp over
    S per KM 1.2.3 propriety, so f needs the same three; fields = base-change of
    f to the subscheme ≫ D-over-S, mirroring A's baseChange_prop); (b)
    `flatPullback_ideal` = comap; (c) composition laws at divisor level via
    `ext` (comap_id/comap_comp); (d) `baseChange_baseChange` — iterated base
    change = base change along the composite, transported through
    `pullbackLeftPullbackSndIso` (ideal-level). NOTE (adversarial, banked): for
    NON-finite flat f the pullback of a proper divisor can fail finiteness over
    S (𝔾ₘ ↪ 𝔸¹_{ℤp} against D = V(x²−p): pullback = the generic point of a DVR,
    not finite over ℤp) — the [IsFinite f] hypothesis is genuinely required for
    OUR (proper/KM-1.2.3) structure; KM p. 6's bare-flat statement is about the
    finiteness-free 1.1.1 notion.
  - **Status**: done (beastmode-D2, 2026-07-07T04:05Z → 2026-07-07T05:35Z) — ALL SIX
    delivered axiom-clean (standard three), CartierDivisor.lean now ZERO sorries:
    `ext` (obtain-rfl type-ascription coerces the projection-eq across defeq — plain
    subst fails), `flatPullback_prop` (mirror of baseChange_prop; composite transport
    `rw [← w, ← Category.assoc, ← pullback.condition, Category.assoc]` +
    `P.comp_mem _ _ (MorphismProperty.pullback_fst _ _ hf) hD` — pullback_fst's
    IsStableUnderBaseChangeAlong instance auto-derives from IsStableUnderBaseChange),
    `flatPullback` def, `flatPullback_ideal` (byte-mirror of baseChange_ideal),
    `flatPullback_id` (`Scheme.IdealSheafData.comap_id` EXISTS —
    IdealSheaf/Functorial.lean:68 @[simp]), `flatPullback_flatPullback`
    (comap_comp forward), `baseChange_baseChange_ideal` (3× baseChange_ideal + 2×
    ← comap_comp + `pullbackLeftPullbackSndIso_hom_fst` (Pasting.lean:532) closes rfl).
    Delegated (fresh-context, first-try green). NOTE for consumers: identity/composite
    IsFinite/Flat/lfp instances all synthesize — divisor-level laws usable directly.
- **[T-D21]** general-`A` A-structures/A-generators representability (KM 1.5–1.6,
  in hand): closed subscheme of `Hom(A, E)`. Depends: T-D16; structure theorem for
  finite abelian `A` (mathlib). The two instances T-D17/T-D18 do not wait for this.

### New stream SG — finite locally free closed subgroups (review requirement)
- **[T-SG1]** finite locally free closed subgroup schemes of `E/S`: definition +
  basic API (kernel-style constructors; `E[N]` as the leading example).
  **DONE** (beastmode-H, 2026-07-07) — `GroupScheme/Subgroup.lean` builds green; core
  (`FiniteLocallyFreeSubgroup` structure, `pointSubgroup`, `rank`/`HasRank`, the
  `RelEffCartierDiv` divisor dictionary `toRelEffCartierDiv`/`ofRelEffCartierDiv` +
  roundtrip, `torsionSubgroup` = `E[N]` leading example, `torsionι_factors_iff`,
  `torsionSubgroup_hasRank` KM 2.3.1 rank part, `HasRank.smul_eq_zero_of_factors`
  KM 1.4.2) all proven. Axiom audit: the three pure divisor-dictionary lemmas
  (`toRelEffCartierDiv_isSubgroup`, `torsionι_factors_iff`, `toRelEffCartierDiv_degree`)
  are AXIOM-CLEAN; the `torsionSubgroup`/`HasRank` decls carry `sorryAx` ONLY through the
  pre-registered upstream boxes (BB-QF/BB-FLAT/BB-DEG in Torsion.lean, BB-DELIGNE in
  ExactOrder.lean) — no new box minted. One parked follow-on = **T-SG1b** below.
- **[T-SG1b]** point-level base-change dictionary for `FiniteLocallyFreeSubgroup`
  (`baseChange.subgroup` field, the one parked `sorry` in Subgroup.lean:357): transport
  `G.subgroup (g' ≫ g)` across `(E.baseChange g).Point g' ≃+ E.Point (g' ≫ g)`, with
  factorisations corresponding via the universal property of `pullback G.ι
  (pullback.fst E.π g)`. The finite/flat/lfp/closedImmersion fields of `baseChange` are
  already proven (pasted-pullback descent); ONLY the subgroup condition is sorried.
  **BLOCKED on the same `(E.baseChange g).E`-vs-`pullback E.π g` spelling normalisation
  that parks `Point.asSection_zsmul`** (GroupLaw.lean PARKED note) — i.e. this funnels
  into the A-lane 3-spelling-normalisation refactor, exactly like the other gated
  H/C base-change memberships. Non-blocking for SG2 (which quantifies over a fixed
  base). Depends: A-lane spelling normalisation (asSection_zsmul unblock).
- **[T-SG2]** fppf-local cyclicity (KM 1.4.1 verbatim, in hand) as the **definition of
  record** for Γ₀(N); discharges/replaces the geometric-fibre surrogate in
  `IsGammaZero` (upgrade `T-D10`). **GATE: no Γ₀ representability theorem may be
  stated against the surrogate.**
  **DONE (def-of-record layer)** (beastmode-H, 2026-07-07) — `GroupScheme/CyclicSubgroup.lean`,
  SORRY-FREE, axiom-clean. `FiniteLocallyFreeSubgroup.IsCyclic G N := E.IsGammaZeroFppf N
  G.toRelEffCartierDiv` — cyclicity of record on the SG1 subgroup-scheme layer, routed through
  the proven `toRelEffCartierDiv` bridge (T-SG1) into T-D10's existing `IsGammaZeroFppf` (NO new
  fppf vocabulary, NO dependency on the T-SG1b sorry, does NOT touch the gated
  `isGammaZero_iff_fppf`). API: `IsCyclic.hasRank` (rank N from the degree conjunct),
  `IsCyclic.exists_fppf_generator`, `isCyclic_of_generator` constructor, and the Γ₀(N) datum
  `GammaZeroStructure` (cyclic flf subgroup of rank N — what representability targets, per the
  GATE). NOTE (v9): the reviewer DEPRIORITIZED Γ₀ cyclicity to work-order #7 ("only then");
  this layer is banked as non-blocking infra — no further SG effort now, H-lane pivots to the
  v9-sharpened T-C0 (#5). Downstream (SG2 representability via KM 3.7.1) stays gated.
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

### Katz–Mazur source gate — ⚡ LIFTED 2026-07-08 ⚡ (was: do-not-formalize-from-memory)
**The full Katz–Mazur text has LANDED**: `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`
(local-only, gitignored). The gate condition ("until the full KM text is in `refs/ModularCurves/`")
is now MET, so the do-not-formalize-from-memory block on KM 2.3, 2.8, 4.7, 5–7, 8–10, 12–13 is
**LIFTED**. **Every ⧗KM ticket is now dispatchable and MAY BE CLOSED** — do NOT leave them idle
"waiting for KM"; the wait is over. (A ⧗KM ticket may still be blocked by a *different*,
non-KM gate — e.g. the deferred T-A6 Abel/canonicity dictionary, T-Q2 = SGA III, or D2's
flatness/depth domain — so re-check each ticket's OTHER `Depends on:` before claiming; but the KM
gate itself no longer blocks anything.)

**New binding requirement (replaces the from-memory prohibition, keeps source-faithfulness):**
when formalizing a ⧗KM result, first READ the cited pages in the PDF, then cite the statement
**verbatim (page + KM section number) from the actual text** in the decl docstring / ticket, and
confirm the Lean statement matches that quote. Do NOT reconstruct "from standard knowledge". The
`⧗KM` marker now means "cite the real text", not "blocked".

(Original gate, for the record: KM 2.3/2.8/4.7/5–7/8–10/12–13 could be *stated* from [Loe]/[Hida]
quotes but not closed until the full KM text was in `refs/ModularCurves/` and the decomposition
quote-gate passed. That condition is now satisfied.)

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
  `point_smul_eq_comp_mulBy`). Depends: T-A6d spec only. **DONE** (beastmode 2026-07-06
  → glSmul FULLY sorry-free, axiom-clean: killing halves + generation via matrix-inverse
  recovery `pull P = (g⁻¹)₀₀·pull P' + (g⁻¹)₁₀·pull Q'`, coefficients reduced mod N by
  `↑g·↑g⁻¹ = 1`; new helpers `zsmul_eq_of_intCast_eq`, `recover_combo`; `glSmul_one`,
  `glSmul_mul`, `hOrbitSetoid` now also axiom-clean). Commit 6d851016.
- **[T-H3]** `gammaHNaiveProblem` functor laws + orbit-compat of pullback.
  - **GATE DIAGNOSIS (fable-P4, 2026-07-08 survey)**: the remaining `map`-membership +
    orbit-compat sorries (GammaH:384/385) — and likewise Γ₁/Γ(N) naive
    (Representability:214/229) and the Drinfeld pair (GammaH:997/1011) — ALL funnel
    through `EllHom.pullSection_add` (T-E4a, Representability:207, sorried), whose own
    docstring records the edge: it consumes `abelEnrichment_unique` (GME 2.2.5: pointed
    iso onto a pullback ⟹ group iso). STATUS OF THE GATE: half-open — T-W7b (DONE,
    2026-07-08) supplies canonicity over LOCALLY NOETHERIAN bases, and C3′
    (`isMonHom_of_one_comp_eq'`) IS GME 2.2.5 in that regime; but `EllObj R` bases are
    arbitrary `R`-schemes, so full generality = the T-W7.8 gap (blocked-on-mathlib,
    hom-existence descent). **OWNER DECISION REQUESTED**: (a) restrict `EllObj R` to
    locally noetherian bases (Loeffler/KM lose nothing on the Y(N) path; all
    representing objects are finite type over `Spec R`) ⟹ the whole cluster discharges
    NOW via the C-chain; or (b) keep arbitrary bases and park the cluster behind
    T-W7.8. **OWNER DECIDED (2026-07-08): (b) — keep arbitrary bases.** The functor-law
    sorries stay parked behind T-W7.8; fable-P4 executes the future-proof piece:
    **[T-E4a-noeth] DONE** (fable-P4 2026-07-08, `#print axioms` clean; NEW
    Moduli/PullSectionAdd.lean, own commit): `pullSection_add_of_isLocallyNoetherian` —
    exactly as routed: pointed comparison iso (zero_w + isoPullback) + C3′
    (= GME 2.2.5 over loc-noeth; instances proper/flat-via-smooth/r-supply/sep) +
    T-H2b dictionary + `pull_add` + transport injectivity. When T-W7.8 lands, swapping
    C3′ for its unrestricted successor discharges `pullSection_add` verbatim and the
    whole functor-law cluster follows.
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
  - **[T-FLAT1-SLICE]** (proof-ticket cut 2026-07-07 by beastmode-D2; the FIRST concrete
    T-FLAT1 discharge, driven by a real consumer). STATEMENT (frozen, already registered
    as a box in LevelStructure/CartierDivisor.lean):
    `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor (R A) [CommRing R][CommRing A]
    [Algebra R A][Algebra.FinitePresentation R A][Module.Flat R A] (f : A)
    (hq : Module.Flat R (A ⧸ Ideal.span {f}))
    (hfib : ∀ K [Field K][Algebra R K], f ⊗ₜ 1 ∈ nonZeroDivisors (A ⊗[R] K)) :
    f ∈ nonZeroDivisors A`. SOURCE: local criterion of flatness by fibres, Stacks 00MH/
    051C (regular-element form) — NOT EGA (unheld; KM 1.1.5.1 cites A-K V 3.6, also
    unheld; both merely cited, never needed for the Lean proof). ROUTE: Tor-free via
    mathlib's `Flat/EquationalCriterion.lean` + `Flat/TorsionFree.lean` (see the box
    board-note for the equational-criterion factorisation sketch). fp hypotheses are
    LOAD-BEARING (counterexample in docstring: M=m over a rank-1 non-discrete valuation
    ring). CONSUMER: `RelEffCartierDiv.isOfficial` (T-D11 ⇐). Discharging this makes the
    ENTIRE D-chain axiom-clean (removes the last sorryAx).
  - **DIFFICULTY RE-ASSESSED (2026-07-07T14:55Z, beastmode-D2 — CORRECTS the optimistic
    "100-200 line Tor-free" estimate above)**: I worked the proof through. The Tor-free
    part IS clean and reaches `Ann_A(f) ⊗_R κ(𝔭) = 0 for all residue fields κ(𝔭)` — via
    mathlib's flat-tensor-exactness (`Module.Flat.lTensor_exact`/`rTensor_exact`): fB is
    R-flat (kernel of A ↠ A/fB, both flat), so `0→Ann(f)→A→fB→0` stays exact after ⊗κ
    (Ann⊗κ ↪ A⊗κ) AND the fibrewise-nzd hyp kills the image ⟹ Ann(f)⊗κ = 0 ∀κ. **BUT the
    final step `Ann(f)⊗κ(𝔭)=0 ∀𝔭 ⟹ Ann(f)=0` FAILS without finiteness of `Ann_A(f)`** —
    `Ann(f)_𝔭 = 𝔭·Ann(f)_𝔭` only forces 0 under Nakayama, i.e. `Ann(f)` fin. gen. over R,
    which a general fp-flat (even standard-smooth) A does NOT give (A is not module-finite
    over R; ideals of the non-noetherian A needn't be fg). CONSUMER CHECK: the box is
    applied at B/(f) = (A⧸I)[1/r], a LOCALIZATION of the module-finite A⧸I — a localization
    of a finite module is NOT finite, so the consumer does NOT supply `Module.Finite R
    (B/(f))` either. CONCLUSION: at full generality the box is **EGA IV 11.3.8 / Stacks
    00ME proper**, genuinely gated on **noetherian approximation (HB-NOETH)** — descend to
    a noeth subring R₀ where Ann(f) is fg, conclude there, base-change up. HB-NOETH is
    itself a substantial unbuilt piece (decomposition-km1 §HB-NOETH: mathlib
    `SpreadingOut.lean`/`AffineTransitionLimit.lean`, ticket T-NOETH0, unbuilt). `nzd is
    local on Spec B` reduces to stalks B_𝔪 but each is only ess-smooth over R_𝔭 (a field
    base is needed for the wave-2 DVR route — not available here). NET: T-FLAT1-SLICE is
    NOT a clean standalone discharge; it needs T-NOETH first (or a smoothness-specific
    argument that is itself research-level). RECOMMENDATION: keep it a registered box (a
    legitimate WIP marker for a classical, mathlib-absent result) UNLESS the owner wants
    to fund the T-NOETH noetherian-approximation build. Est. REVISED: T-NOETH (multi-
    ticket) + ~150 lines, NOT 100-200 alone.
- **[T-OT0]** scoping after T-SG1; statement "flf comm. group scheme of rank N killed
  by N"; Deligne norm-argument decomposition (FltRegular norm lemmas per rescan).
- **[T-DESC0]** scoping — **DONE (beastmode-DESC, 2026-07-07)**. mathlib coverage:
  - **LANDED (in-lane, axiom-clean, `Moduli/Stack.lean`):** the **descent-of-morphisms
    engine** — `descend_hom_of_effectiveEpi` (a map coequalizing `f`'s kernel pair
    factors uniquely through `f`, via mathlib's `EffectiveEpi.desc`) + the **gluing
    half** `moduliProblem_fppf_descent` (dual to the proven `moduliProblem_fppf_separated`).
    Together: **relatively representable moduli problems are fppf sheaves** — the gluing
    half the file had deferred to T-E8's descent-data vocabulary, landed instead via
    mathlib `Sites/Fpqc` (`fppfTopology.Subcanonical`; `EffectiveEpi f` for
    flat+LFP+surjective, i.e. the plan's "fppf-covers-are-epis" DESC deliverable — now
    *in mathlib*, no longer a DESC target).
  - **mathlib-gap findings (survey):** the plan's stated object-descent route
    (relatively-ample embedding → module descent + Proj) rests on **three absent
    foundations**: (i) FF module *effective* descent in cocycle form — mathlib has only
    `comonadicExtendScalars` (comonadicity) + the abstract `DescentDataAsCoalgebra`
    framework, the effective/cocycle packaging is mathlib's own flagged TODO (single-map
    case is essentially `ComonadicLeftAdjoint`, but QC-globalization is absent);
    (ii) **relative `Proj`** over a base scheme — ABSENT (only absolute
    `ProjectiveSpectrum`); (iii) **relatively-ample / relative projective embedding** —
    ABSENT. Each of (ii)/(iii) is a multi-week mathlib-PR-scale AG development.
  - **Precise gating of `levelledCurve_descent_of_torsor` (T-E10):** every route needs
    an object-descent mechanism to *produce* the curve `E/T`, gated on ONE of
    {representability T-E9 [E-stream, sorried] · relative Proj+QC-descent+ample [absent,
    B3-scale] · T-Q2 SGA-III quotient charts [plan-deferred "statements-only by design"]},
    AND additionally on **T-G3 rigidity** (`aut_trivial_of_fullLevel`, sorried) to turn
    `hdesc`'s mere-existence isos into a strict cocycle. DESC's clean morphism-descent
    engine is delivered; the remaining object-descent is blocked on other-lane sorries or
    B3-scale absent mathlib AG foundations. `ellipticCurve_fppf_descent`/T-E10 stays
    `sorry` pending those.
- **[T-IRR0]** scoping: algebraic (KM Ch. 10 ⧗, Tate-curve degeneration) vs analytic
  (uniformisation ↔ LeanModularForms) route; target `yRho_geometricallyIrreducible`
  (statement exists). Late-phase; parallel.
  - **DONE (`/develop --decompose`, IRR-scoping, 2026-07-08)**: full decomposition in
    `.mathlib-quality/decomposition-km10.md`; buildable `:= by sorry` skeleton (3456 jobs green)
    in NEW `ModularCurve/IrreducibilityScoping.lean`. **KEY SOURCE FINDING (verbatim, KM 10.9.2
    p. 303 + 10.1 p. 287): KM's "algebraic route" is NOT analytic-free — its connectedness proof
    reduces to the geometric generic fibre and then invokes the transcendental `ℍ/Γ̃`
    uniformisation** ("the underlying complex manifold to `M(𝒫)⊗ℂ` is isomorphic to the quotient of
    the upper half plane by … `Γ̃ ⊂ SL(2,ℤ)`"). Both routes bottom out at `Y⊗ℂ ≅ ℍ/Γ̃` connected;
    the KM `T[N]`/component machinery (10.2.5 / 10.6 / 10.8.2 / 10.9.1) only *reduces* to it and is
    not needed for this single-fibre target. **Split = tractable shell + MAJOR-INFRA analytic core.**
    Shell buildable NOW (leaf tickets below); core gated on a scheme-analytification functor +
    LeanModularForms bridge (both absent from mathlib AND AINTLIB). Recommendation: keep BB-IRR a
    registered assumption (Buzzard-sanctioned), land the shell so the reduction + the labelled
    analytic `hconn` are on record. Route C (analytic-free geometric-monodromy `SL(2,ℤ/N)`-surjectivity
    via Tate-curve unipotents) is the alternative if complex-analysis-free is later mandated — NOT in
    KM, its own multi-session stream.
- **[T-IRR1]** (shell leaf L1) `irreducibleSpace_of_connectedSpace_of_smooth`
  (`IrreducibilityScoping.lean`): a nonempty connected smooth curve over `ℚ̄` is irreducible
  (regular ⟹ components = connected components). **Buildable now** (≤ few mathlib lemmas; pin the
  `regular ⟹ irreducible-of-connected` chain). Full statement/quote/attacks: decomposition-km10.md §L1.
- **[T-IRR2]** (shell leaf L4) `connectedSpace_quotient_orbitRel` (`IrreducibilityScoping.lean`):
  the quotient of a connected space by a group action is connected (the only property of `ℍ/Γ̃`
  KM 10.9.2 uses). **Buildable now** (mathlib `IsPreconnected.image` + `Quotient.mk` cont/surj).
  decomposition-km10.md §L4.
- **[T-IRR3]** (shell assembly MASTER) `yRho_geometricallyIrreducible_of_connected`
  (`IrreducibilityScoping.lean`): reduce the target to geometric connectedness `hconn` of `Y⊗ℚ̄`
  via base-change smoothness + T-IRR1. **Buildable now.** decomposition-km10.md §MASTER.
- **[T-IRR-L2]** (API-gap stream) geometric connectedness insensitive to `ℚ̄ ↪ ℂ` (Stacks 0363);
  **status: blocked/MAJOR-INFRA** — scheme `π₀` base-change absent from mathlib.
- **[T-IRR-L3]** (API-gap stream, THE core) `(Y⊗ℂ)^an ≅ ℍ/Γ̃` (KM 10.9.2 transcendental
  description); **status: blocked/MAJOR-INFRA** — needs scheme-analytification functor +
  LeanModularForms analytic-modular-curve bridge; gates BB-IRR; latest-phase.
- **[T-IRR-L5]** (API-gap stream) GAGA: `ℂ`-scheme connected ⟺ analytification connected;
  **status: blocked** on T-IRR-L3's analytification infrastructure.

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
  - **SCOPED (2026-07-07T15:20Z, beastmode-D2 — owner requested the T-NOETH build).
    MATHLIB SURVEY (grounds the scope; MUCH more is present than the stale "absent from
    mathlib" notes claimed):** `AffineTransitionLimit.lean` (31 lemmas) = the EGA IV §8
    FOUNDATION at scheme level (`nonempty_isColimit_Γ_mapCocone`,
    `exists_app_map_eq_map_of_isLimit`, `Scheme.exists_hom_comp_eq_comp_of_
    locallyOfFiniteType`) — PRESENT; `SpreadingOut.lean` (`spread_out_unique_of_
    isGermInjective`, EGA IV 8.8.2) — PRESENT; `TensorProduct/Finite.lean`
    `exists_fg_le_eq_rTensor_subtype` (module-element spreading) + `Finiteness/Descent`,
    `Flat/.../Descent` — PRESENT. **THE GAP** = ring/algebra-level object spreading:
    "fp-flat algebra + a chosen module over `R = colim Rᵢ` descends to a stage `Rᵢ`"
    (EGA IV 8.9.1 fp + 11.2.6 flatness, algebra form). **CONCRETE TICKET TREE:**
    [T-NOETH1] `R = colim (fg ℤ-subalgebras)` filtered, each stage noetherian (Hilbert
    over ℤ) ~40 lines · [T-NOETH2] fp-algebra descent `A ≅ Aᵢ ⊗_{Rᵢ} R` (+ element f,
    ideal I descend) — crux · [T-NOETH3] flatness + fibrewise-nzd descend (EGA IV 11.2.6)
    + `Ann(f) = Ann(fᵢ) ⊗_{Rᵢ} R` · [T-NOETH-FLAT1] discharge the T-FLAT1-SLICE box via
    NOETH1-3 + Nakayama at the noeth stage (removes last D-chain sorryAx). REVISED EFFORT:
    NOT a from-scratch stream — foundation is in mathlib; ~4 bounded tickets. Order:
    NOETH1→2→3→FLAT1. **COORDINATION w/ T-W7.8**: DISTINCT (W = morphism-equality descent,
    largely already in mathlib; D = object/module descent) — same foundation, no shared
    files (D builds `ForMathlib/NoethApprox*.lean`; W wraps existing SpreadingOut).
  - **T-NOETH1+2 DONE, T-NOETH3 BOXED** (beastmode-D2, 2026-07-07T16:10Z, Opus delegate +
    independently verified): `ForMathlib/NoethApprox.lean` (177 lines, committed).
    `exists_noetherianSubalgebra_supset` (NOETH1) + `exists_noetherian_descent` (NOETH2:
    fp R-algebra ≅ `R ⊗[R₀] A₀` over a noetherian fg-ℤ-subalgebra R₀, via
    presentation-coefficient descent — `Algebra.FinitePresentation.out` +
    `MvPolynomial.algebraTensorAlgEquiv` + `Algebra.TensorProduct.tensorQuotientEquiv`)
    BOTH axiom-clean (standard three). `exists_noetherian_descent_flat` (NOETH3) BOXED:
    R₀/A₀/noeth/fp/iso all DERIVED from NOETH2; ONLY the `Module.Flat R₀ A₀` component is
    sorried. **NOETH3 STICKING POINT (confirmed genuine mathlib gap)**: flatness must be
    descended after ENLARGING R₀ (can fail for the first R₀), needing a SINGLE enlargement
    that trivialises EVERY relation at once — that uniform bound IS **flat-locus openness /
    generic flatness (EGA IV 11.1.1)**, which mathlib does NOT have (no generic-flatness,
    no ring/module flat-locus-openness — only scheme-morphism `Flat.lean`). So NOETH3 is a
    clean box for EGA IV 11.2.6/11.1.1. **IMPLICATION FOR T-FLAT1-SLICE**: the box discharge
    (NOETH-FLAT1) needs flatness to descend (A/f flat at the noeth stage) ⟹ needs NOETH3 ⟹
    needs GENERIC FLATNESS. So the D-chain's last sorryAx bottoms out at a THIRD mathlib gap
    (generic flatness), beneath noetherian approximation. NOETH1+2 stand as reusable
    upstream-candidate infrastructure regardless. RECOMMENDATION FIRMED: keep T-FLAT1-SLICE
    boxed — full discharge = build noeth-approx (mostly done) + generic-flatness (EGA IV
    11.1.1, new multi-hundred-line project). Generic flatness is itself a good standalone
    mathlib contribution with many consumers if the owner wants to fund it.
- [T-D22] section-of-smooth-rel-curve ⟹ locally principal nzd ideal (HB-REGIMM;
  étale-local 𝔸¹ model route). [T-D23] closed pt of smooth curve /field has DVR
  local ring.
  - **[T-D22+T-D23] Status**: in_progress · **Claimed**: beastmode-D2 (stream-D
    successor), 2026-07-07T00:40Z. GOAL RE-SCOPED TO THE PAYOFF: discharge the
    four `sectionsIdeal_*` register boxes (CartierDivisor.lean:169-198) — the
    ONLY sorryAx-source in the D-chain (T-D3→D5→D6/7/9→D17/D18 all inherit
    them; discharge ⟹ the ENTIRE Drinfeld chapter goes axiom-clean modulo only
    T-B4's three KM 2.3.1 boxes, which are B/FLAT-lane). TWO CHUNKS:
    [Box-1] the KM 1.1.2 SES induction: from per-section local-principality-
    with-nzd+flat-quotient, derive finite/flat/lfp/rank-n of ∏ᵢ ker(Pᵢ) by
    induction over Fin n (SES `0 → A/hA →×g A/fgA → A/gA → 0`; flat-of-
    extension; T-D24's `rankAtStalk_eq_add_of_exact` for the degree leg;
    affine-local ⟹ global via the same IdealSheafData plumbing as
    vanishingLocus). [Box-2 = T-D22 proper] the étale-local 𝔸¹ engine for the
    input: section of smooth-rel-dim-1 has affine-locally principal nzd ideal
    with flat quotient — route: mathlib `IsStandardSmoothOfRelativeDimension`
    presentations (+ A-lane's ForMathlib/StandardSmoothHypersurface machinery)
    OR the direct KM/GME p.107 route ("I(P) is generated by T"); T-D23 (DVR
    local rings) only if the chosen route needs it. EXECUTION ORDER REVISED
    2026-07-07T00:55Z after the affineness-crux analysis: [Box-2] FIRST
    (independent, unambiguous), [Box-1] second with this REFINED ROUTE for its
    affineness leg (the reason A parked the boxes): (i) supp(∏ᵢ ker zᵢ) =
    ⋃ zᵢ(S)-images (mathlib support_mul + section-ker support = image);
    (ii) the REDUCED union of finitely many closed affine subschemes of a
    separated scheme is affine via the RING-PULLBACK construction
    (Z₁ ∪ Z₂ = Spec (A₁ ×_{A₁₂} A₂), scheme-theoretic-union induction);
    (iii) the ∏-subscheme is a FINITE-ORDER thickening of a closed subscheme
    of that union — KEY INCLUSION (I₁ ∩ … ∩ I_n)ⁿ ⊆ I₁⋯I_n (each factor of
    the n-fold product lands one term in each ideal) — so affineness transfers
    by induction over square-zero extensions; mathlib has NO
    nilpotent-thickening affineness lemma (grepped: absent) — that helper
    (X qc, closed immersion with square-zero/nilpotent kernel ideal, target
    affine ⟹ source affine — or the ⟺ form) is an UPSTREAM-GRADE ForMathlib
    piece, likely provable elementarily for the square-zero step via
    sections-lift-nilpotents + basicOpen-cover comparison, avoiding Serre
    H¹-vanishing. (iv) then finite = affine + module-finite (filtration
    algebra), flat/lfp via the KM 1.1.2 SES + extension-stability
    (Flat-of-extension may be missing in mathlib = T-D3a′ — check
    Module.Flat.extension/of_shortExact at build), rank via T-D24.
  - **Progress**: 2026-07-07T02:20Z — **[Box-2] = T-D22-PROPER FULLY PROVEN**
    (delegated, outcome (1)): `exists_affineOpen_ker_principal_nonZeroDivisor`
    (CartierDivisor.lean:754, 13 kerPrincipalAux privates) — AXIOM-CLEAN
    (standard three, NO register-box consumption), both CartierDivisor and
    downstream Incidence green. ROUTE OF RECORD: off-section via
    `Hom.support_ker`; on-section: SmoothOfRelativeDimension's DEFINITION
    hands standard-smooth charts directly (no Locally-elimination!); one
    basicOpen zigzag makes the retraction pair with `z⁻¹V = U` forced;
    principality = hand-rolled conormal (explicit f with σ(κf)=1 via
    span_range_derivation-induction; I ≤ (f) ⊔ I•I via a derivation into
    A⧸I•I lifted by liftKaehlerDifferential; `ker_fG_of_surjective` +
    Nakayama `exists_sub_one_mem_and_smul_le_of_fg_of_le_sup`; final open
    D(r)). NZD LEG (novel, NO noetherian descent): on A[1/κf], df generates
    Ω ⟹ Ω[A'/R[X]] = 0 (X ↦ f) ⟹ Jacobi–Zariski (H1Cotangent.exact_map_δ +
    IsStandardSmooth.subsingleton_h1Cotangent) ⟹ A' formally smooth over
    R[X] ⟹ smooth ⟹ FLAT ⟹ X-torsion-free ⟹ f regular; descend by the
    gⁿ-binomial trick. GOTCHAS: Localization carries the R-tower via
    OreLocalization — own letI Algebra creates SMul DIAMONDS (the
    of_algebraMap_eq'-mismatch is the tell); `(𝟙 S).appLE U U e =
    presheaf.map (𝟙 (op U))` by rfl (structure-eta) beats TopCat-synonym rw
    failures; new imports: Etale.Kaehler, Flat.TorsionFree, Kaehler.Basic/
    Polynomial, Nakayama, Smooth.Flat, Smooth.StandardSmoothCotangent.
    REMAINING = [Box-1] only (the four sectionsIdeal boxes via the refined
    (i)-(iv) route above, now with T-D22's principality as proven input).
  - **Status**: done (beastmode-D2, 2026-07-07T00:40Z → 2026-07-07T03:30Z) —
    **[Box-1] FULL DISCHARGE**: all four `sectionsIdeal_*` boxes PROVED
    axiom-clean (delegated; +612 lines CartierDivisor, NEW
    ForMathlib/SheafDisjointUnion.lean). ROUTE OF RECORD — the banked
    union/thickening machinery was AVOIDED entirely via DISJOINTIFICATION:
    sections through distinct fibre points are separated by shrinking CHARTS
    into complements of the other sections' closed images (π(c) = s forces
    collisions); per-fibre-value groups get merged T-D22-charts
    (`exists_basicOpen_le_affine_inter` + principality/nzd descent along
    map_ideal_basicOpen + `IsLocalization.map_nonZeroDivisors_le`); the pieces
    are pairwise-disjoint affines covering q⁻¹U ⟹ affine by mathlib's
    **`IsAffineOpen.iSup_of_disjoint`** (exists!). Module leg: KM 1.1.2
    filtration with SPLIT SESs (A/(f) ≅ R free ⟹ T-D24's split lemma) ⟹
    Γ(X, q⁻¹U) ≃ₗ R^n via the new sheaf-disjoint-union product lemma +
    card_eq_sum_card_fiberwise. Boxes via IsZariskiLocalAtTarget.of_iSup_eq_top
    + `Scheme.Opens.toSpecΓ_naturality`-pullback transport (NO appTop/resLE
    juggling); `Algebra.FinitePresentation.of_finitePresentation` (module-fp ⟹
    algebra-fp, EXISTS) closes lfp. AXIOM STATE OF THE CHAIN (verified):
    sectionsDivisor/sectionsDivisor_degree/sectionsIdeal_* /
    exists_exactOrderLocus (T-D17!) all STANDARD THREE; exists_fullLevelLocus
    (T-D18) sorryAx only through T-B4's KM 2.3.1 boxes (B-lane: BB-QF/BB-FLAT/
    BB-DEG) — the D-lane's own debt is ZERO. GOTCHAS: bind data with `set` not
    `have` (defeq loss); doc-comments can't sit between `open … in` and decl;
    Hom.ker_apply needs [QuasiCompact]. T-D23 (DVR) never needed — absorbed. [T-D24] finrank additivity in SES of finite free modules (local + glue).
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
  - **[T-D26] Status**: done-as-absorbed (beastmode-D2, 2026-07-07T00:40Z) —
    T-D15 was proven WITHOUT any degree argument (the frozen mutual-subdivisor
    form needs no same-degree reduction), so the planned wrapper has NO
    remaining consumer; the algebra engine is mathlib-present (see annotation
    above). Nothing to build. If a future ticket needs `degree ≡ 0 → ideal = ⊤`,
    re-open against that consumer's spelling.
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
  - **[T-D30] Claimed**: beastmode-D2, 2026-07-07T04:05Z. Status: in-progress.
    PLAN (KM 1.8.2, transcribed-in-hand; no ⧗): add form (1)
    `IsFullSetOfSectionsCharpoly` — ∀ A f, `(Algebra.lmul A (A ⊗[R] B) f).charpoly
    = ∏ i, (X − C (sectionBaseChange … f))` — + `isFullSetOfSectionsAlg_iff_charpoly`.
    (1)⟹(2) at T=0: coeff 0 via `LinearMap.det_eq_sign_charpoly_coeff` +
    `Algebra.norm_apply`; n = finrank from monic-degree comparison (nontrivial
    case; subsingleton A trivial). (2)⟹(1): T-D29 `Algebra.charpoly_lmul_eq_norm`
    over base A at f, transport the norm along cancelBaseChange
    `A[X] ⊗[A] (A ⊗[R] B) ≃ₐ A[X] ⊗[R] B`, apply hyp (2) at the R-algebra A[X],
    factors compute to `X − C cᵢ` via `sectionBaseChange_tensor_map` with
    ψ = C-as-R-AlgHom. Element spelling pinned per T-D29 note: `X ⊗ₜ 1 − 1 ⊗ₜ f`.
  - **[T-D30] Status**: done (beastmode-D2, 2026-07-07T04:05Z → 2026-07-07T05:35Z) —
    `IsFullSetOfSectionsCharpoly` + `isFullSetOfSectionsAlg_iff_charpoly` PROVED
    axiom-clean (standard three), scratch-first (TD30.lean replica → paste; file was
    delegate-locked for T-D20 meanwhile). Route AS PLANNED, all gadgets existed:
    (⟹) T-D29 at base A + `Algebra.norm_eq_of_algEquiv` (Norm/Basic.lean:211 — import
    upgraded Norm.Defs→Norm.Basic) along `Algebra.TensorProduct.cancelBaseChange
    R A A[X] A[X] B` (Maps.lean:470, @[simp] cancelBaseChange_tmul), element transport
    by tmul-induction (a • (1:A[X]) = CAlgHom a is RFL after Algebra.smul_def+mul_one),
    then hyp at R-algebra A[X]; factors via sectionBaseChange_tensor_map with
    ψ = Polynomial.CAlgHom (AlgebraMap.lean:95). (⟸) subsingleton_or_nontrivial;
    nontrivial: n = finrank from congrArg natDegree (LinearMap.charpoly_natDegree
    [StrongRankCondition ← Nontrivial CommRing TC] + natDegree_prod_of_monic +
    natDegree_X_sub_C), then norm_apply + det_eq_sign_charpoly_coeff +
    coeff_zero_eq_eval_zero + eval_prod; sign closes by Finset.prod_neg + pow_add +
    Even.neg_one_pow ⟨n,rfl⟩. GOTCHAS: (i) `C` shadowed by the Scheme section variable
    — Polynomial.C must be qualified in CartierDivisor.lean; (ii) simp with
    neg_eq_neg_one_mul spirals (HasDistribNeg maxRecDepth) where `rw [Finset.prod_neg]`
    succeeds — simp-motive pathology, banked; (iii) `even_add_self` does not exist —
    use ⟨n, rfl⟩. n-vs-rank adversarial note: def does NOT force n = finrank; iff still
    unconditionally true (degree comparison inside the nontrivial branch; zero ring
    vacuous both sides).
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
- **Status**: done (beastmode-Q, 2026-07-06T15:58Z → 2026-07-06T16:19Z) ·
  **Claimed**: beastmode-Q, 2026-07-06T15:58Z
- **Progress** (2026-07-06T16:19 — AffineQuotient.lean sorry-free, zero warnings,
  standard axioms ×5, module green; AG-QUOT's affine core is DISCHARGED):
  - Delivered (namespace `AlgebraicGeometry`): `existsUnique_factor_fixedPoints_away`
    (algebra engine, via `RingEquiv.ofLeftInverse` + `Function.invFun` — there is NO
    `RingEquiv.ofInjective` in mathlib); `invariantsπ_hom_ext_of_isOpenImmersion`
    (uniqueness in the route-locked transportable form: against `pullback π j` for
    any open immersion j — Surjective-stable-under-base-change instance lives in
    `PullbackCarrier.lean:431`); `invariantsπ_hom_ext` (j = 𝟙 corollary);
    `exists_invariantsπ_lift`; `existsUnique_invariantsπ_lift` (= [Loe] 3.6.1
    affine, absolute form). Private infra: chartA/chartB/chartπ + `_def`/
    `_opensRange` lemmas, `chart_square` (IsLocalization.map_comp), and
    `isPullback_chart` via `IsOpenImmersion.isPullback` (OpenImmersion.lean:752) —
    the D(a)-square recognition KILLED the deferred T-Q3c(iii): no
    invariants-of-tensor identification anywhere.
  - PROOF SHAPE OF RECORD (β): per-point affine chart of Y (affineCover.exists_eq),
    T := h₁⁻¹(range ι), push along j, basic open D(a) ⊆ j''T,
    `IsOpenImmersion.lift` twice, cancel πa at Γ-level via `Spec.map_surjective` +
    `Spec.map_injective` + T-Q3c(i); glue with `Scheme.Cover.mkOfCovers` (index :=
    POINTS of W) + `Scheme.Cover.hom_ext`. (γ): fibres-are-orbits + closedness
    (`PrimeSpectrum.isClosedMap_comap_of_isIntegral`) give the saturated basic open;
    (α) factors the chart-restricted morphism; `Scheme.OpenCover.glueMorphisms` with
    compat = TWO applications of (β) at `pullback.fst/snd chartA chartA` through
    the `isPullback_chart`-lift (private `chart_descent_side`); factorization
    verified on the B-side point-indexed cover.
  - GOTCHAS OF RECORD: `Scheme.Cover.hom_ext` (NOT OpenCover.hom_ext — Gluing.lean
    namespace Cover); `Cover.mkOfCovers` needs the cover TYPE ascribed
    (`: (Spec _).OpenCover`) or map_prop's P stays a metavariable; rw of a def-name
    under `Scheme.Hom.opensRange` is a dependent-instance motive error — state
    `_opensRange` lemmas directly (IsOpenImmersion is Prop, proof-irrelevance
    makes the instance mismatch free); a >150-line single proof hit 200k-heartbeat
    whnf timeouts — FIXED BY DECOMPOSITION into 3 private lemmas (NO maxHeartbeats,
    per the standing rule); `Y.affineCover.X i` is affine via
    `Scheme.isAffine_affineCover` + `Scheme.isoSpec`, avoiding IsAffineOpen/Opens
    plumbing entirely.
  - Post-proof cleanup: DEFERRED (owner pause; debt tracked with T-Q1/T-Q3a-c for
    the cleanup lane — CLEANUP-12 covers the three Q-files).
  - Consumers unblocked: T-H4 (quotient half), T-E5 (KM 4.7 ⇐ bootstrap objects),
    T-M2 (coarse Y₀(N) route), T-Q5 (gluing — next in lane).
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
  - **Status**: done (beastmode-Q, 2026-07-06T16:42Z → 2026-07-06T16:55Z;
    statements-only per scope — the four A7.1.1/A7.1.2 targets carry WIP sorries
    BY DESIGN, SGA III Exp. V is the proof source when someone picks them up) ·
  - **Delivered** (ForMathlib/InvariantTorsor.lean): `IsFreeAlgebraAction` (KM's
    freeness verbatim, hom-inequality form); `MulSemiringAction.torsorMul`
    (`A ⊗[Aᴳ] A →ₐ[Aᴳ] (G → A)` via `Algebra.TensorProduct.lift` of
    `Pi.constAlgHom` + `AlgHom.pi ∘ toAlgHom`; `torsorMul_tmul` is `rfl` — the
    rw-route hits a Pi.algebra instance mismatch, rfl doesn't); sorried:
    `Module.Finite.of_isFreeAlgebraAction`, `Algebra.Etale.of_isFreeAlgebraAction`,
    `torsorMul_bijective_of_isFreeAlgebraAction` (A7.1.1 split per Tier A5),
    `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` (A7.1.2, against
    T-Q4's map). Def layer axiom-clean; only warnings are the 4 intended sorries.
    Attack block in q-lane.md. Post-proof cleanup deferred (owner pause). ·
    Scope: KM A7.1.1's freeness def (`no fixed points on Hom_{R-alg}(A,R')`,
    quote banked under T-Q4) + sorried statements of A7.1.1 (étale-torsor: two
    single-conclusion parts per Tier A5) and A7.1.2 (freeness ⟹ ∗(A,G,R), via
    T-Q4's `fixedPointsBaseChange`). File: ForMathlib/InvariantTorsor.lean (NEW).
    Proofs are SGA III Exp. V territory — statement-level now by design (the
    board line says "statements").
- **[T-Q4]** base change of invariants — KM Ch. 7 appendix ("base change for rings
  of invariants") — **full KM text NOW IN refs/** (`katz-mazur-arithmetic-moduli-
  FULL.pdf`); read the appendix at pickup (quote-gate), decide the flat/finite-free
  hypotheses honestly. Feeds T-Q6 and the Y(ρ̄) twist route.
  - **Status**: done (beastmode-Q, 2026-07-06T16:25Z → 2026-07-06T17:20Z; core
    Q4a–Q4d — the phase-2 remainder is [T-Q4e], open, below)
  - **Delivered** (ForMathlib/InvariantBaseChange.lean, sorry-free, ZERO warnings,
    axioms: standard on all four): Q4a `MulSemiringAction G (A ⊗[R] R')` instance
    built on `{ TensorProduct.leftDistribMulAction with … }` (NO diamond — the smul
    is mathlib's `leftHasSMul`) + `smul_tmul_baseChange` + `SMulCommClass G R`
    instance; Q4b `fixedPointsBaseChange : Aᴳ ⊗[R] R' →ₐ[R] (A ⊗[R] R')ᴳ` (KM's
    ∗-map, `AlgHom.codRestrict` of `Algebra.TensorProduct.map val id`); Q4c
    `fixedPointsBaseChange_bijective_of_flat` (KM A7.1.3(1) — kernel-exactness
    `0 → Aᴳ → A → (G → A)` + `Module.Flat.rTensor_exact` +
    `rTensor_preserves_injective_linearMap`, with `TensorProduct.piLeft` for the
    finite-product commutation); Q4d `fixedPointsBaseChange_bijective_of_isUnit`
    (KM A7.1.3(4) — divided trace `u⁻¹ • Σ_g g` corestricted to a retraction,
    tensored; `IsUnit (Nat.card G : R)` hypothesis).
  - GOTCHAS OF RECORD: `DistribMulAction.toLinearMap` is DEPRECATED →
    `DistribSMul.toLinearMap`; tensor-side needs BOTH `[SMulCommClass G R A]` and
    `[SMulCommClass R G A]` (mathlib's left-tensor instances want the R-G order;
    taking both avoids loop-prone symm-instances); `TensorProduct.piLeft` needs
    `[Fintype ι]` (cases nonempty_fintype) and has NO application lemmas — unfold
    via `simp only [piLeft, LinearEquiv.trans_apply, comm_tmul, piRight_apply,
    piRightHom_tmul, piCongrRight_apply]`; `g • (a ⊗ₜ r)` is DEFEQ
    `(g • a) ⊗ₜ r` so rw-rfl often closes sum-congruences for free; `omit [..] in`
    goes BEFORE the docstring.
  - Post-proof cleanup: DEFERRED (owner pause; CLEANUP-12 scope grows to four
    Q-files).
- **[T-Q4e]** (open; phase 2 of T-Q4) KM A7.1.3(0) transitivity + (2) faithfully
  flat descent of ∗ + A7.1.4 DVR criterion; statements per the banked verbatim
  quotes. Cut when a consumer (T-Q6 / Y(ρ̄) twist) demands them.
  - **QUOTE-GATE SATISFIED** (2026-07-06T16:35Z; KM pp. 215–218 read from
    `katz-mazur-arithmetic-moduli-FULL.pdf`, pdf pp. 226–229 — the PDF is a pure
    scan, read visually; page offset = book + 11). Verbatim of record:
    - (A7.1) setup: "Let R be a ring, A an R-algebra, and G a finite group which
      acts on A by R-linear ring automorphisms. We denote by A^G ⊂ A the
      R-subalgebra of all G-invariants. For any R-algebra R', the group G acts
      R'-linearly on A ⊗_R R' [by g(a⊗r') = g(a)⊗r'], and we have a natural
      R'-homomorphism A^G ⊗_R R' → (A ⊗_R R')^G." ∗(A,G,R,R') = "the statement
      that the above map is an isomorphism"; ∗(A,G,R) = for every R-algebra R'.
    - THM A7.1.1 (freeness ⟹ étale torsor; proof deferred to SGA III Exp. V
      Thm 4.1): G acting freely (no fixed points on Hom_{R-alg}(A,R') for g ≠ id,
      R' ≠ 0) ⟹ A is a finite étale G-torsor over A^G and A ⊗_{A^G} A ≅ ∏_G A
      via x⊗y ↦ (x·g(y))_g. COR A7.1.2: then ∗(A,G,R). [NOT stated in Lean now —
      needs torsor vocabulary; belongs with T-Q2's freeness circle.]
    - PROP A7.1.3: (0) ∗(A,G,R) ⟹ ∗(A⊗_R R', G, R'); (1) R' flat over R ⟹
      ∗(A,G,R,R') ["A^G is a kernel: 0 → A^G → A → ⊕_g A via ⊕(1−g)"];
      (2) R' faithfully flat ⟹ (∗(A,G,R) ⟺ ∗(A⊗R',G,R')); (3) #G invertible in
      R' ⟹ ∗(A,G,R,R'); (4) #G invertible in R ⟹ ∗(A,G,R) ["divided trace
      T = (1/#G)·Σ_g g as a projection: A = A^G ⊕ (1−T)(A)"].
    - PROP A7.1.4 (DVR criterion): R DVR, π uniformizer: (1) ∗(A,G,R) ⟺
      (2) ∗(A,G,R,R/πⁿ) ∀n ⟹ (3) ∗(A/πⁿA,G,R/πⁿ) ∀n; all three ⟺ if
      char Frac(R) = 0 and A is R-flat.
  - **Lean decomposition (T-Q4a–d; File: ForMathlib/InvariantBaseChange.lean NEW)**:
    Q4a = the `G`-action on `A ⊗[R] R'` through the left factor (survey mathlib
    tensor-action instances FIRST — if a compatible `SMul` instance exists the ring
    action must EXTEND it, no diamond); Q4b = the comparison hom
    `(A^G) ⊗[R] R' → (A ⊗[R] R')^G` (KM's natural map; exact bundling decided at
    skeleton time against elaboration); Q4c = A7.1.3(1) flat ⟹ bijective (route:
    `A^G = ker(⊕(1−g))` + `Module.Flat.lTensor_exact` — the D-lane's T-D24 finding
    of record says the Flat-exactness API applies to baseChange directly);
    Q4d = A7.1.3(4) |G|-invertible ⟹ bijective (divided-trace projection;
    check `GroupTheory/Maschke` for the averaging idiom). (0)/(2)/A7.1.4 = phase 2
    of the ticket after a–d land.
- **[T-Q5]** gluing affine quotients (quasi-projective case; [Loe] 3.6.1 full
  statement): orbits-in-affines via quasi-projectivity; glue the `Spec(A_i^G)`;
  S-relative + `Over S` packaging of the universal property.
  - **Status**: done (2026-07-06T22:28Z) · **Claimed**: beastmode-Q, 2026-07-06T16:58Z
  - **T-Q5a DONE** (2026-07-06T17:10Z): ForMathlib/SchemeQuotient.lean —
    `SchemeAction` (two-law σ-family + derived `isIso_hom`), `SchemeAction.spec`
    (the specSMul instance), `IsStableOpen`, and the Γ-bridge
    `gammaMulSemiringAction : MulSemiringAction G Γ(X,U)` for stable U via
    `Scheme.Hom.appLE` (mul-law by `appLE_comp_appLE`; one-law by
    proof-irrelevance `homOfLE-op = 𝟙` + presheaf map_id — NOTE: the map_id
    rewrite needs `erw` (TopCat.Presheaf-vs-functor coercion blocks rw), the ONE
    erw in the Q-lane; flag for cleanup). Sorry-free, zero warnings, standard
    axioms.
  - **T-Q5b DONE** (2026-07-06T17:35Z): `exists_isStableOpen_isAffineOpen` —
    orbit ⊆ affine U + affine diagonal (`IsAffineHom (pullback.diagonal
    (terminal.from X))`, WEAKER than X.IsSeparated which implies it) ⟹
    `⨅ g, (σ.hom g) ⁻¹ᵁ U` is a G-stable affine open ∋ x. Tools:
    `IsAffineOpen.iInf` (Morphisms/Affine.lean — needs Nonempty ✓ group) +
    `IsAffineOpen.preimage_of_isIso` + `Opens.coe_iInf` (Finite) +
    `Surjective.iInter_comp (Equiv.mulLeft g)` for the reindex. Sorry-free,
    zero warnings, standard axioms. REMAINING LEAVES: T-Q5c (glue data over the
    stable-affine cover) + T-Q5d (π + UP assembly) — route below.
  - **T-Q5c/d fine route (banked 2026-07-06T17:40Z — READ BEFORE RESUMING; data-
    sorries are FORBIDDEN so the quotient must be built proven-as-you-go, no
    sorried-def skeleton)**:
    (1) KEY TOPOLOGY FACTS available: π_V := invariantsπ on a stable affine V is
    integral+surjective+fibres-orbits (T-Q1) ⟹ CLOSED+surjective ⟹ QUOTIENT map;
    for stable open W ⊆ V: π_V⁻¹(π_V(W)) = W (stability+orbits) ⟹ π_V(W) open.
    (2) STABLE-BASIC BASIS: inside a stable affine V, the stable basic opens
    D(f), f ∈ Γ(V)ᴳ, form a basis of stable opens (the separation argument in
    T-Q3's `exists_chart_descent` at every point; reuse its closedness idiom).
    (3) GLUING KEYS: for f ∈ Γ(V)ᴳ: Γ(D(f))ᴳ ≅ (Γ(V)ᴳ)_f — this is EXACTLY
    T-Q3b/T-Q3c(ii) (mem_range_fixedPoints_awayMap_iff) + T-Q5a's Γ-bridge.
    (4) PRIMARY ROUTE (mathlib-supported): `Scheme.GlueData` with pieces
    `Spec (Γ(V_i)ᴳ)` over a chosen stable-affine cover (T-Q5b per point + choice);
    transition opens: image-in-Q_i of V_i ∩ V_j via (1)-(2)-(3); cocycle from
    T-Q3's ExistsUnique (uniqueness kills the t_fac checks — same trick as
    hcompat in exists_invariantsπ_lift).
    (5) FALLBACK ROUTE (KM's actual construction, no cocycles): topological
    quotient |X|/orbits + invariants-of-pushforward sheaf (π_* O_X)ᴳ as a
    LocallyRingedSpace; scheme-property affine-locally via (3). Choose (4) unless
    its t-maps fight; both are multi-session-scale — fine.
    (6) T-Q5d STATEMENTS (the contract, single-conclusion each): `SchemeAction.
    quotient σ : Scheme` + `quotientπ : X ⟶ quotient` (DATA — must be real);
    `quotientπ_comp_hom : σ.hom g ≫ quotientπ = quotientπ`;
    `quotientπ_hom_ext` (transportable j-form like T-Q3's);
    `exists_quotientπ_lift`; `existsUnique_quotientπ_lift` (Loeffler 3.6.1 in
    full). T-Q6/T-Q7 consume ONLY these five signatures.
    (7) LEAF STATUS (2026-07-06T18:05Z): DONE — stable-basic basis
    (`exists_mem_basicOpen_subset_of_stable`), quotient-map
    (`invariantsπ_isQuotientMap`), stable-image openness
    (`isOpen_image_invariantsπ_of_stable`), all in AffineQuotient.lean, sorry-free.
    c2+c3-bridge DONE (2026-07-06T20:35Z): `localQuotient`/`localQuotientπ`
    (Spec Γ(V)ᴳ, R := ℤ after universe-widening R : Type v across the Q-files),
    `resLE_isoSpec_hom` (@[reassoc] — the geometric/algebraic intertwiner; proof:
    Scheme.isoSpec_hom_naturality + arrowResLEAppIso.hom.w + a Spec.map
    computation; GOTCHA: rw/reassoc-rw on goals containing the letI-Γ-action hit
    presheaf-coercion motive failures — `show`-expand localQuotientπ by defeq
    then rw closed terms), `resLE_localQuotientπ` (local invariance). All
    sorry-free, zero warnings, standard axioms.
    KEYSTONE PROVED (2026-07-06T20:42Z): `exists_invariantsπ_lift_of_isOpenImmersion`
    — the j-relative descent existence (AffineQuotient.lean, sorry-free, standard
    axioms; commit "T-Q5c KEYSTONE"). With the j-relative hom_ext this is the full
    effective-epi package. Also proven en route: `pullbackSpecSMul` + specs.
    (α) DONE (2026-07-07): `isOpenImmersion_localQuotientMap` PROVED (window
    layer: windowHom/imageOpens/windowIso via isoOfRangeEq + saturation;
    keystone-descended inverse; UP-uniqueness both sides; `localQuotient` made
    @[reducible] — REQUIRED for instance-transparency through the def). Also
    (β1) DONE: `IsStableOpen.inf`, `localQuotientMap_self`,
    `localQuotientMap_trans` (glue backbone; NOTE the ≤-proof-irrelevance makes
    eqToHom-free t-maps possible). All sorry-free, axiom-clean, committed.
    (β2) COMPLETE (2026-07-06T22:04Z): range_localQuotientMap, imageOpens_inf
    (saturation arithmetic), tripleIso + hom_fst/hom_snd + fst/snd-shuffles,
    isIso-of-eq-maps, glueF/glueT/glueT' (@[reducible] — REQUIRED for the
    rw-pattern matching through the defs), t_fac, cocycle, and
    **quotientGlueData : Scheme.GlueData** — ALL FIELDS PROVEN; X/G exists as
    `.glued`. GOTCHA: `isOpenImmersion_localQuotientMap` must be an INSTANCE
    (haveI-chains in statements caused whnf timeouts); ≤-proof-irrelevance of
    localQuotientMap makes every lattice-branch defeq (t_id/f_id/cocycle all
    close by _self/_trans + rfl). REMAINING (β3): quotientπ via glueMorphisms
    over the V-opens cover (compat = glue_condition + localQuotientπ_
    localQuotientMap, plan in transcript), invariance, then the contract
    (hom_ext / exists / ∃!) via per-chart affine machinery over 𝒟.openCover.
    (β3-β4) DONE — **T-Q5 COMPLETE** (2026-07-06T22:28Z, commit "T-Q5 COMPLETE"):
    the full T-Q5d contract is proven, sorry-free, zero warnings, standard
    axioms, in ForMathlib/SchemeQuotient.lean: `quotient` (:= glueData.glued,
    @[reducible]), `quotientπ` (glued from `localQuotientπ ≫ opensι` over
    `atlasCover` via `chartCompat`/`quotientπCompat`), `opensι_quotientπ`,
    `hom_quotientπ` (invariance; the contract's `quotientπ_comp_hom` under a
    mathlib-idiomatic name), `quotientπ_hom_ext` (uniqueness via per-chart
    invariantsπ_hom_ext + hπ'-idiom), `exists_quotientπ_lift` (existence:
    per-chart `exists_chart_lift` from the ABSOLUTE exists_invariantsπ_lift +
    specSMul_isoSpec_inv, overlap agreement `hover` via invariantsπ_hom_ext +
    localQuotientMap_trans_assoc + hleg both sides, then vPullbackCone
    transport by `PullbackCone.IsLimit.lift'` — NO conePointUniqueUpToIso
    needed, a bare lift + 2 leg-equations suffices; GOTCHA of record:
    repackage ℓ through a cleanly-TYPED ∃ (the mk-pt cone-point type pollutes
    rw-motives) and discharge the legs by PURE-DEFEQ `exact` — simp-
    normalizing them breaks the match; the @[reducible] chain makes plain
    exact work), `existsUnique_quotientπ_lift` (formal assembly).
    T-Q6/T-Q7/T-W3 consumers are UNBLOCKED with the full proven contract.
    OLD route notes below superseded where they conflict: β2a range_localQuotientMap = imageOpens
    (extract from (α)'s m₀-iso); β2b imageOpens-intersection arithmetic
    (π(A)∩π(B) = π(A∩B) for saturated A B — KEY: a stable set containing one
    orbit point contains the orbit); β2c tripleIso : pullback (f i j) (f i k) ≅
    Q_{V_i⊓V_j⊓V_k} via isoOfRangeEq, t' := tripleIso-conjugate of the
    eq-map, t_fac/cocycle by mono-cancel + localQuotientMap_trans; then
    GlueData.glued + π (glue per-chart π^{V_i} over the V_i-cover) + the five
    contract statements (β3, keystone per chart). T-Q6/Q7 + NEW v8 consumer
    T-W3 (quotient-stack core, lane Q) unblock at β3's skeleton.
    NEXT LEAVES (in order): c2 = local quotient of a stable affine open V
    (`Spec Γ(V)ᴳ` + local π := V.toScheme ≅ Spec Γ(V) [IsAffineOpen.isoSpec] ≫
    invariantsπ-of-Γ-bridge-action; invariance lemma); c3 = for stable affine
    W ≤ V the descended open immersion Q_W ⟶ Q_V (descend (homOfLE ≫ π^V) along
    π^W via T-Q3 ∃!; open-immersion-ness by reduction to invariant-basic W via
    the basis lemma + isPullback_chart); c4 = GlueData + contract (6).
  - **Route lock (binding unless B2)**: hypothesis of record is the MODERN one —
    "every `G`-orbit is contained in a `G`-stable affine open" (Stacks 07S7 shape;
    quasi-projectivity over an affine base IMPLIES it and is deferred to a
    corollary when a consumer needs that form — do NOT build a quasi-projectivity
    predicate for this). Action vocabulary: a family `σ : G → (X ⟶ X)` with
    `σ 1 = 𝟙` and `σ (g*h) = σ g ≫ σ h` (matches T-Q1's covariant `specSMul`
    convention; `specSMul` is the `Spec B` instance). Leaves:
    **T-Q5a** action-on-scheme vocabulary + stable opens + the Γ-bridge (a stable
    affine open `U` gives `MulSemiringAction G Γ(X,U)` and `U ≅ Spec Γ(U)`
    intertwines the actions — connects to the ENTIRE affine theory T-Q1/Q3);
    **T-Q5b** stable-affine refinement (orbit ⊆ affine `U`, `X` separated ⟹
    `⋂_g (σ g)⁻¹ U` is a G-stable affine open containing the point; finite
    intersections of affine opens in separated schemes — check mathlib
    `IsAffineOpen` inf lemmas at pickup);
    **T-Q5c** glue data: pieces `Spec (Γ(V_i)ᴳ)` over a stable-affine cover,
    transition isos from T-Q3's ExistsUnique (uniqueness kills cocycle checks);
    **T-Q5d** `π : X ⟶ X/G` + invariance + the ∃!-universal property (existence
    per-piece from T-Q3 + `invariantsπ_hom_ext_of_isOpenImmersion`-style glue,
    which was PROVEN in transportable form for exactly this step).
    Files: ForMathlib/SchemeQuotient.lean (NEW). NOTE: T-Q6/T-Q7 consume the
    STATEMENT of T-Q5d only — they unblock at skeleton time.
- **[T-Q6]** quotients of rigidified moduli problems (KM 4.7 ⇐ engine; T-E5).
  - **Status**: done (2026-07-07T02:10Z; scope-of-record met: Q6a-c + Q6d
    machinery PROVEN, Scholie assembly stated + gated — see T-Q6e) ·
    **Claimed**: beastmode-Q, 2026-07-06T22:50Z ·
    **Files**: Moduli/QuotientProblem.lean (NEW), ForMathlib/RepresentableAut.lean
    (NEW), ForMathlib/SchemeQuotient.lean (SchemeAction.ofAut added)
  - **DELIVERED (all sorry-free + axiom-clean unless noted)**: Q6a `simul`;
    Q6b `pullbackAlongπ`/`toPullbackAlong`/`isoPullbackAlong`/
    `homToPullbackAlong`/`homPullbackAlongEquiv`/`toPullbackAlong_pullbackAlongMap`
    + `connectHom` (KM's θ(g)) + `eq_id_of_baseHom_of_comp` (relative-mono);
    Q6c **`simul_representable`** (KM 4.7 step (i), fully formal);
    Q6d action chain: `RepresentableBy.transportHom`/`autMulHom` (ForMathlib,
    generic Aut-transport along representability, upstream candidate),
    `simulMapSnd`/`simulAutSnd`, `EllObj.autBase`, `SchemeAction.ofAut`,
    **`simulSchemeAction`** (the KM geometric action landing in T-Q5/T-Q3
    vocabulary); Q6d vocabulary: `RelRepData` (+ iff-bridge), `TorsorData`
    (KM axiom 2, conventions attack-adjudicated in q-lane.md);
    **`simulSchemeAction_free_of_rigid` PROVEN** (KM p. 113 θ(γ)-argument,
    first-try green; endgame via mathlib `isEmpty_of_commSq_sigmaι_of_ne`).
    ONE sorry: `representable_of_rigid_of_torsor` (SCHOLIE 4.7.0) — see T-Q6e.
- **[T-Q6e]** (open; the gated tail of T-Q6) prove `representable_of_rigid_of_torsor`
  (Moduli/QuotientProblem.lean): assembly per KM pp. 112–116 route banked in the
  docstring. GATES: (1) T-Q2's A7.1.1/SGA III Exp. V 4.1 statements
  (ForMathlib/InvariantTorsor.lean — free action ⟹ π is a finite étale G-torsor)
  must land for the quotient-torsor step; (2) stream-DESC descent of the
  universal curve + 𝒫-structure (SGA I Exp. VIII; `levelledCurve_descent_of_torsor`
  shape, T-E10 v2). The affine quotient itself is T-Q3 (DONE); the freeness input
  is `simulSchemeAction_free_of_rigid` (DONE). Cut/claim when the gates land.
  - **QUOTE-GATE SATISFIED** (2026-07-06T22:45Z; KM 4.7 read from
    `katz-mazur-arithmetic-moduli-FULL.pdf` pdf pp. 122–128 = book pp. 111–117;
    KM 7.1 read pdf pp. 197–199 = book pp. 186–188; Ch.4 Appendix (A.4) read pdf
    p. 136 = book p. 125; Loeffler §3.6–3.8 re-read from `modcurvesnotes.pdf`
    pp. 16–19). Verbatim of record:
    - SCHOLIE (4.7.0): "Let 𝒫 be relatively representable and affine over (Ell);
      then a necessary and sufficient condition that 𝒫 be representable is that
      𝒫 be rigid."
    - The axiomatized engine (KM p. 112): "Let N ≥ 1 be an integer, G a finite
      group, and δ a relatively representable and affine moduli problem on (Ell)
      which satisfies the following axioms: 1) δ is representable, by an affine
      ℤ[1/N]-scheme. 2) G operates upon δ, in such a way that for every elliptic
      curve E/S with S a ℤ[1/N]-scheme, the S-scheme δ_{E/S} is a finite etale
      G-torsor. We claim that over ℤ[1/N], 𝒫 is represented by the affine
      ℤ[1/N]-scheme 𝕸(𝒫,δ)/G." Applied with (N=2, δ=Legendre,
      G=GL(2,ℤ/2ℤ)×{±1}) and (N=3, δ=naive level 3, G=GL(2,𝔽₃)).
    - Proof skeleton (KM pp. 112–116): (i) "Because δ is representable, and 𝒫
      is relatively representable, the simultaneous problem (𝒫,δ) is
      representable, by 𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)}"; affine. (ii) G acts on 𝕸(𝒫,δ)
      through δ; θ(g) unique by rigidity ⟹ one-cocycle. (iii) "By axiom 2) and
      the rigidity of 𝒫, G operates freely on 𝕸(𝒫,δ)"; quotient exists (affine),
      π_univ is a finite étale G-torsor [SGA III Exp V, 4.1]. (iv) θ = descent
      data; E projective ⟹ descends via I⁻¹(0); α_univ descends since 𝒫
      relatively affine (SGA I Exp VIII, 7.8, 1.2, 1.7). (v) (E₀,α₀) represents
      𝒫: for (E/S,α) use the torsor δ_{E/S} → S, classify (E×δ_{E/S}, α, β_univ)
      → f : δ_{E/S} → 𝕸(𝒫,δ) G-equivariant, quotient f₀; cartesian since
      vertical arrows are G-torsors; rigidity + étale-surjective π gives
      f₀*(E₀,α₀) ≅ (E,α); uniqueness: a G-map of G-torsors is an iso.
    - KM 7.1.1 (G operates on 𝒫) = pointwise action + pullback-compat diagram
      (7.1.1.1) = `G →* Aut 𝒫` in the functor category. KM 7.1.2/7.1.3 (the
      problem-level quotient 𝒫/G, rel-repr affine, étale-torsor iff free, etc.)
      is the T-Q7-adjacent formalism — locator banked (book pp. 186–201), NOT
      in T-Q6 scope.
    - Appendix (A.4.1.2): 𝒫 representable ⟺ 𝒫̃ representable AND 𝒫 rigid (a
      tautology); Gabber counterexample shows 𝒫̃-representable ⇏ rigid. NOTE
      FOR T-E5: KM 4.7.0 carries an "affine over (Ell)" hypothesis that
      Loeffler 3.7.4 DROPS; the project's `representable_iff` statement follows
      Loeffler. At T-E5 pickup either add the affineness hypothesis (KM-honest)
      or route the general case through KM (A.4.2) (étale-sheaf condition,
      auto for rel-repr) — statement risk flagged, decision belongs to T-E5.
  - **Leaves (Tier A5 split, single-conclusion each)**:
    T-Q6a `simul` — the simultaneous problem (𝒫,δ) as a pointwise-product
    presheaf + API; REAL def (no data sorries).
    T-Q6b Ell-iso infrastructure: every `EllHom` is cartesian — the comparison
    iso `Y ≅ X.pullbackAlong u.baseHom` in `Ell/R` from `u : Y ⟶ X` (uses
    EllHom.isPullback + IsPullback.isoPullback + zero_w); feeds Q6c's
    value-transport.
    T-Q6c `simul_representable` : δ.Representable → 𝒫.RelativelyRepresentable →
    (𝒫.simul δ).Representable — KM step (i), fully formal, NO black box.
    Q6a+Q6b DONE (2026-07-07T00:15Z, commit "T-Q6a/b"): simul (pointwise
    product, defeq-transparent obj/map + @[simp] lemmas), pullbackAlongπ,
    toPullbackAlong/isoPullbackAlong (every Ell/R-morphism is cartesian),
    homToPullbackAlong + homPullbackAlongEquiv (universal property of the
    tautological square), toPullbackAlong_pullbackAlongMap (decomposition).
    Q6c DONE (2026-07-07T00:40Z, commit "T-Q6c"): **simul_representable
    PROVEN** — (P.simul δ).Representable from δ.Representable +
    P.RelativelyRepresentable, via simulRepresentableBy (universal-element
    toFun ⟹ homEquiv_comp = functoriality; invFun via homToPullbackAlong;
    map_val_eq transport by subst-generalization). All sorry-free, zero
    warnings, standard axioms. GOTCHA OF RECORD: mixed defeq-spellings
    ((v ≫ π).baseHom vs v.baseHom ≫ f) poison rw/simp kabstract at
    instances-transparency ("target not type-correct" note) — workarounds:
    erw (5 uses, cleanup-flagged), pure-term proofs (trans/congrArg), dsimp
    only to beta-reduce Equiv-field goals, pin of_horiz_isIso with named args.
    T-Q6d engine statement (the axiomatized claim, quote above) + assembly:
    vocabulary `G →* Aut δ` (mathlib-native, no new structure), induced action
    on `simul`, freeness-from-rigidity, quotient via T-Q3/T-Q5 machinery
    (`𝕸(𝒫,δ)` is AFFINE — invariantsπ suffices, no gluing), étale-torsor step =
    T-Q2's sorried SGA III V 4.1 interface, descent step = stream-DESC's
    `levelledCurve_descent_of_torsor`-shape black box (T-E10 v2 precedent).
    Q6d statements may sorry against those two black boxes per the T-H/T-Q2
    precedent; Q6a–c must close.
- **[T-Q7]** coarse quotient statements (`Y₀(N)`, `Y(1)`) — via groupoid layer (D6),
  phase M; consumes T-Q5 + T-M1/T-M2 vocabulary. NOTE (2026-07-06): KM Ch. 7
  (QUOTIENTS BY FINITE GROUPS, book pp. 186–214) read at T-Q6 quote-gate; 7.1.3
  (existence + properties of 𝒫/G for rel-repr affine 𝒫) and 7.3 (quotients of
  product problems) are the sources of record for the Γ₀-style problem-level
  quotients here.
- **[CLEANUP-12]** (already on the board, v2 cadence): quotient stream after
  T-Q3+T-Q4+T-Q5 — covers the three new ForMathlib files.

---

## Amendments v6 (2026-07-06): ★ Stream-H claim + execution order (beastmode-H)

*Stream H (general levels, `Moduli/GammaH.lean`) claimed by **beastmode-H**,
2026-07-06T16:55Z. Star reserves the lane; tickets claimed one at a time per rule 5.
Attack blocks: `decompose-attacks-2026-07-06/levels-stack.md` (all GammaH statements
covered; DEF fixes in-skeleton via 2bdae6cc). **Exclusion**: an in-flight unclaimed
edit proving `gammaHNaiveProblem.map_id/map_comp` (T-H3 law-half, GammaH.lean:123–141,
observed uncommitted 16:47Z, pullSection_id/comp route, T-E4 style) is NOT part of this
claim — whoever lands it keeps it; H-lane will not touch that block until it lands.*

### H-lane execution order (v6)
1. **T-H7** (below) → 2. **T-H1** (`gammaHNaive_bot`; derive `glSmul_one` from the
   group structure, NOT `ZMod.val` — N=1 edge per attack block) → 3. **T-H3**
   remainder (orbit-compat + `map`-membership: gated on pullSection-additivity =
   A6.δ/T-G2 hidden dep, attack finding 6 — state `EllHom.pullSection_add` spec,
   leave sorried, register the edge) → 4. **T-H5** (rigid_iff; mathlib
   CongruenceSubgroup API) → 5. T-H2/H2a LAST (provable via T-A6d but sits on the
   A-lane's in-flight asSection/mulBy 3-spelling refactor — defer until that lands).
- NOT workable now: T-H4 (T-C0/C1 unstarted + stream-Q in flight + T-D18 open),
  T-H6 (T-E5 + T-H4), T-H8/H9 (⧗KM; statements re-scoped by the attack pass),
  T-H10 discrete-half (T-G3).

### [T-H7] full level is not rigid for N ≤ 2 (the honest stack statement)
- **Status**: in_progress · **Claimed**: beastmode-H, 2026-07-06T16:55Z ·
  **File**: Moduli/GammaH.lean · `gammaFullNaive_not_rigid_of_le_two` (skeleton :203)
- **Depends on**: T-E4 (done-mod-gate; only the functor is consumed, not the gated
  membership sorries) · **Parent**: none (v3 stream-H) · **Type**: theorem
- **Statement**: in skeleton (post-DEF-1: `hN : N ≤ 2`, `hinv : IsUnit (N : R)`,
  `hR : ∃ X : EllObj R, Nonempty X.base`; conclusion
  `¬ (gammaFullNaiveProblem R N).Rigid`).
- **Proof sketch** (attack verdict "sound"; route refined to one geometric point):
  1. Unfold `Rigid` (EllCategory.lean:168): produce `X`, `e : X ≅ X` over `𝟙`-base,
     `e ≠ Iso.refl X`, and `a : P(X)` with `P.map e.hom.op a = a`.
  2. From `hR` pick `X₀` + a point `s` of `X₀.base`; base-change along
     `Spec k̄ → X₀.base` (`k̄ := AlgebraicClosure κ(s)`; `X := X₀.pullbackAlong g`) —
     nonempty base persists.
  3. Level point `a`: over `k̄` with `N` invertible (from `hinv`), naive full
     level-N structures exist — N=1: the zero pair; N=2: a basis of `E[2](k̄)` via
     B-lane torsion-fibre machinery (TorsionFibre.lean, T-B6 done). Bridge to
     `IsNaiveFullLevel` per its actual definition.
  4. `e := [-1]` (`mulByHom (-1)` packaged as an EllObj-iso over `𝟙`).
  5. `e ≠ refl`: else `[-1] = 𝟙`, contradicted on the k̄-fibre by a nonzero point
     of odd order M ∈ {3,5} chosen coprime to char k̄ (T-B6 `E[M](k̄) ≅ (ℤ/M)²`).
  6. Fixity: `P.map e.hom.op a = a` ⟺ `pullSection [-1] P = P` componentwise;
     `pullSection [-1] P = -P` (mulBy/pullSection compat, T-A6d layer), and
     `-P = P` since `2•P = 0` from killed-by-N + `N ∣ 2` (N=1: `P = 0`).
  Steps 3/5/6 are expected sub-ticket spawns (T-H7a geometric-point object, T-H7b
  level-existence over k̄, T-H7c pullSection/mulBy fixity) — cut at first contact
  with the actual definitions.
- **Mathlib lemmas**: `AlgebraicClosure`, `Scheme.fromSpecResidueField` (verify
  name), `IsLocalRing.ResidueField` — five-method search at use time.
- **Sources**: [Loe] §3.8 after 3.8.3 ("only a stack for N ≤ 2"); KM 4.4; attack
  block levels-stack.md §T-H7 (hypotheses shown necessary there).
- **Generality**: as stated (CommRingCat R, N ≤ 2, NeZero N) — frozen statement.
- **Progress**:
  - 2026-07-06T16:55Z: claimed; statement verified in skeleton at :203 against
    Rigid (EllCategory:168). Route pinned to single-geometric-point witness
    (avoids the trivialisation-scheme detour of the original attack sketch).
  - 2026-07-06T17:05Z: definitions contact done (IsNaiveFullLevel, Rigid, EllHom,
    pullSection, mulBy = 𝟙^n in Hom.group, point_smul_eq_comp_mulBy, TorsionFibre
    headline torsion_geometricFibre_rank_two + point_zero_val +
    smul_eq_zero_iff_comp_mulByHom). Baseline lake build GammaH green. KEY
    simplifications found: N=1 level point is the zero pair over ANY base (killing
    clause forces P=Q=0, generation vacuous); functor-value fixity ignores the
    E4a-gated membership sorry (Subtype.ext); [-1]∘[-1]=𝟙 via GrpObj.comp_zpow +
    zpow arithmetic, no new mathlib needed. Spawning T-H7a..T-H7d (below), starting
    T-H7a. glSmul_one found already proven in-skeleton (T-H1 gets cheaper).

### [T-H7a] negation automorphism of an EllObj + pullSection compat (sub-ticket)
- **Status**: in_progress · **Claimed**: beastmode-H, 2026-07-06T17:05Z ·
  **File**: Moduli/GammaH.lean (helpers section before T-H7; /cleanup may relocate) ·
  **Parent**: T-H7 · **Depends on**: none · **Type**: def + lemmas
- **Statements**:
  `EllipticCurve.mulBy_comp_mulBy : E.mulBy m ≫ E.mulBy n = E.mulBy (m * n)`;
  `EllipticCurve.zero_comp_mulByHom : E.zero ≫ E.mulByHom n = E.zero`;
  `EllObj.negIso (X : EllObj R) : X ≅ X` (baseHom `𝟙`, top `mulByHom (-1)`);
  `EllObj.pullSection_negIso : EllHom.pullSection R X.negIso.hom P = -P`.
- **Proof sketch**: (1) `mulBy = (𝟙)^n` in `Hom.group`; `mulBy m ≫ mulBy n =
  (mulBy m ≫ 𝟙)^n` by `GrpObj.comp_zpow`, then `zpow_mul`-arithmetic. (2) zero:
  `smul_zero` + `point_smul_eq_comp_mulBy` at the Section level + `point_zero_val`
  (TorsionFibre) + `Category.id_comp`. (3) `negIso`: hom/inv both from top
  `mulByHom (-1)` over `𝟙`; `hom_inv_id` by EllHom.ext from
  `mulBy_comp_mulBy` at `(-1)*(-1)=1` + `mulBy_one : mulBy 1 = 𝟙` (from `zpow_one`);
  `isPullback` by `IsPullback.of_horiz_isIso` (IsIso from self-inverse); `zero_w`
  from (2). (4) `pullSection_negIso`: `isPullback.hom_ext`; fst-leg: `(-P).1 ≫
  mulByHom (-1) = P.1` via `neg_one_zsmul`, `point_smul_eq_comp_mulBy`,
  `mulByHom`-self-comp; snd-leg: section property.
- **Mathlib lemmas**: `GrpObj.comp_zpow`, `zpow_mul`/`zpow_one`, `neg_one_zsmul`,
  `IsPullback.of_horiz_isIso`, `IsPullback.hom_ext`.
- **Sources**: parent T-H7 attack block; mulBy def GroupLaw.lean:85.
- **Generality**: mulBy lemmas for all `m n : ℤ` (upstream-shaped); negIso minimal.

### [T-H2b] the additive base-change point dictionary (LEAF, cut by fable-P4 2026-07-08)
- **Status**: **DONE** (fable-P4 2026-07-08, incl. the consumer:
  `FullLevelPt.pullAlong` membership discharged — `isNaiveFullLevel_pullAlong`, naive
  full level is stable under base change, `#print axioms` clean, GammaH 10→9 sorries).
  Prior progress note:
  `Over.monObjMkPullbackSnd_mul_left_fst` + grp-alias (NEW ForMathlib/OverPullbackMul.lean,
  own commit) and `Point.baseChangeEquiv` + `baseChangeEquiv_apply_coe` (GroupLaw.lean,
  `#print axioms` clean, downstream green).
  **SWEEP INCIDENTS #5 + #6 + #7 (2026-07-08)**: (#7: the NEW Moduli/PullSectionAdd.lean
  was swept into beastmode-A's `a4756384` — even untracked new files get picked up;
  their workflow must run `git add -A`. Coordinator: this now affects new files, not
  just modified ones.) the GroupLaw.lean insert was swept into
  beastmode-A's `cc856bcb`, and the GammaH.lean consumer discharge into their `472d6a36`
  (their commits picked up my working-tree edits — shared worktree). Content is in and
  green both times; attribution notes for the coordinator. ·
  **Claimed**: fable-P4, 2026-07-08T08:45Z · **File**:
  EllipticCurve/GroupLaw.lean (next to `Point.asSection`) · **Depends**: none (all
  ingredients landed) · **Type**: def (≃+) + 2 compat lemmas + consumer discharge
- **Statement**: `Point.baseChangeEquiv : (E.baseChange σ).Point t ≃+ E.Point (t ≫ σ)`
  for `σ : T' ⟶ T`?? roles: `E : EllipticCurve T`, `t : T'' ⟶ T'` — forward
  `x ↦ ⟨x.1 ≫ pullback.fst, condition-chase⟩`, backward `pullback.lift`; roundtrips are
  `hom_ext` one-liners (skeleton compile-validated in scratch).
- **The content = additivity of the forward map**: point-addition is the Hom-group of
  `grpObjMkPullbackSnd = ((Over.pullback σ).mapGrp.obj _).grp` (mathlib, with
  `@[simps -isSimp mul one]` lemmas `grpObjMkPullbackSnd_mul/_one` available); the
  `fst`-projection intertwines the μ's over the base-change square — mathlib's
  `isMonHom_pullbackFst_id_right` shows the id-specialized pattern; do it over general
  `σ` via the mapGrp/prodComparison plumbing OR the term-mode `mulByHom_baseChange`-style
  chains (the `asSection_zsmul` proof documents the kabstract-vs-term-mode wall — REUSE
  that discipline). Est. 150–250 lines.
- **Consumers** (unblock immediately): `FullLevelPt.pullAlong` membership sorry
  (GammaH.lean:311) — killing via existing `pull_zsmul/pull_zero/asSection_zsmul` (+
  derive `asSection_zero` on the spot), generation via the dictionary (additive ⟹
  `AddSubgroup.closure`-transport) + `Point.pull`-composition compat. NOTE: the
  v8-era gate "pullSection_add gated on abelEnrichment_unique" is CONFIRMED STALE —
  `Point.pull_add/pull_zsmul/pull_zero`, `EllHom.pullSection_add` (Representability:204),
  `Point.asSection_zsmul` all landed independently. The Drinfeld-side sorries
  (GammaH:943/957, `IsFullLevel`/`IsGammaOne` pull-stability) are D-stream Cartier
  territory — NOT this leaf.

### [T-H7b] naive full level structures exist over an algebraically closed base (sub-ticket)
- **Status**: **DONE — already landed in-file** (board stale; verified sorry-free by
  fable-P4 2026-07-08: `exists_isNaiveFullLevel_of_le_two` GammaH.lean:~680) · **File**:
  Moduli/GammaH.lean (helpers) ·
  **Parent**: T-H7 · **Depends on**: T-H7b-i · **Type**: theorem
- **Statement**: `(k : Type u) [Field k] [IsAlgClosed k]
  (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] (hN : N ≤ 2)
  (hk : (N : k) ≠ 0) : ∃ P Q : E.Section, E.IsNaiveFullLevel N P Q`.
- **Proof sketch**: N=1: `(0,0)`; killing by `one_zsmul`→`P=0`; generation: `1•x=0`
  forces `x=0` (`one_zsmul`), `zero_mem`. N=2: `torsion_geometricFibre_rank_two`
  at `t = 𝟙` gives `e : torsionBy ℤ (E.Section) 2 ≃+ (Fin 2 → ZMod 2)`; set
  `P := e.symm ![1,0]`, `Q := e.symm ![0,1]`; killing = torsionBy membership.
  Generation at `(k', t' : Spec k' ⟶ Spec k)`: headline again gives
  `torsionBy ℤ (E.Point t') 2` of card 4; `Point.pull` restricted to 2-torsion is
  injective (T-H7b-i + card/Klein-four argument: two distinct nonzero elements of
  `(ℤ/2)²` generate); transport membership through `AddSubgroup.closure`.
- **Mathlib lemmas**: `Nat.card` of `ZMod`-pi, `AddSubgroup.closure`,
  `AddEquiv.symm`, Klein-four generation (search `ZMod` two-torsion API).
- **Sources**: T-B6 headline TorsionFibre.lean:385; attack block T-H7 step 3.
- **Generality**: exactly `N ≤ 2` (the theorem needs no more; full-level existence
  for general `N` is T-H4/T-B6 territory).

### [T-H7b-i] point separation along extensions of the base field (sub-sub-ticket)
- **Status**: **DONE** (fable-P4, 2026-07-08; `#print axioms` clean) · **File**:
  Moduli/GammaH.lean (helpers) — `Scheme.hom_ext_of_comp_specMap_field` (general: Spec of
  a field embedding is an epi onto maps into ANY scheme; stalkClosedPointTo factorization
  + residueFieldCongr transport + fromSpecResidueField mono + Spec.map_injective) and
  `EllipticCurve.Point.restrict_injective` (the ticket statement, any base `S`) ·
  **Parent**: T-H7b · **Depends on**: none · **Type**: lemma
- **Statement**: `{k k' : Type u} [Field k] [Field k'] (f : k →+* k')
  (E : EllipticCurve S) (t : Spec (CommRingCat.of k) ⟶ S) :
  Function.Injective (fun x : E.Point t => x.restrict (Spec.map (CommRingCat.ofHom f)))`
  (up to the `Point (g ≫ t)` transport).
- **Proof sketch**: reduces to `Spec.map (ofHom f)` being an epimorphism onto maps
  into `E.E`: two morphisms `Spec k ⟶ E.E` with equal precompositions land at the
  same point (surjectivity of `Spec.map` of a field embedding) and their residue
  maps agree after composing with injective `f` — mathlib route candidates:
  `Scheme.SpecToEquivOfField` (morphism-from-field-spec classification) or
  epi-transfer through the affine-scheme equivalence. Five-method search at start.
- **Mathlib lemmas**: `Scheme.SpecToEquivOfField` (verify name), `Spec.map`,
  field-hom injectivity.
- **Sources**: standard (points of schemes over field extensions).
- **Generality**: any scheme target (state for `E.E` or general `Y`; prefer general).

### [T-H7c] `[-1] ≠ 𝟙` over a base with a geometric point (sub-ticket)
- **Status**: **DONE — already landed in-file** (board stale; verified sorry-free by
  fable-P4 2026-07-08: `EllipticCurve.mulByHom_neg_one_ne_id` GammaH.lean:519) · **File**:
  Moduli/GammaH.lean (helpers) ·
  **Parent**: T-H7 · **Depends on**: none · **Type**: lemma
- **Statement**: `(k : Type u) [Field k] [IsAlgClosed k] (E : EllipticCurve S)
  (t : Spec (CommRingCat.of k) ⟶ S) : E.mulByHom (-1) ≠ 𝟙 E.E`.
- **Proof sketch**: assume `=`; then every `x : E.Point t` has `-x = x`
  (`neg_one_zsmul` + `point_smul_eq_comp_mulBy` + `comp_id`), so `2•x = 0`.
  Set `M := if (3:k) = 0 then 5 else 3`; `(M:k) ≠ 0` (char case-split; char 3 ⟹
  `(5:k) = (2:k) ≠ 0`). `torsion_geometricFibre_rank_two M` gives
  `torsionBy ℤ (E.Point t) M ≃+ (Fin 2 → ZMod M)`; `x := e.symm ![1,0] ≠ 0`
  (`(1 : ZMod M) ≠ 0` for `M ≥ 3`). Then `M•x = 0 ∧ 2•x = 0` with
  `IsCoprime (2:ℤ) M` ⟹ `x = 0` (Bézout combination), contradiction.
- **Mathlib lemmas**: `neg_one_zsmul`, `Int.isCoprime_iff_gcd_eq_one` (or
  `Nat.Coprime` + cast), `ZMod.one_ne_zero` (M ≥ 3 side conditions), `CharP` API
  for the case split.
- **Sources**: attack block T-H7 step "e ≠ refl via odd fibre torsion".
- **Generality**: any `S`, any geometric point — reusable by T-H5/T-G3 later.

### [T-H7d] geometric point of a nonempty `R`-scheme with `N` invertible (sub-ticket)
- **Status**: **DONE — was already landed in-file** (board was stale; verified sorry-free
  by fable-P4, 2026-07-08: `EllObj.exists_geometricPoint` at GammaH.lean:836 is complete,
  via `Spec.preimage` of the composite to `Spec R`; claim released, duplicate insert
  removed per the no-dedup rule) · **File**: Moduli/GammaH.lean (helpers) ·
  **Parent**: T-H7 · **Depends on**: none · **Type**: lemma
- **Statement**: `(X : EllObj R) (hne : Nonempty X.base) (N : ℕ)
  (hinv : IsUnit (N : R)) : ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
  (t : Spec (CommRingCat.of k) ⟶ X.base), (N : k) ≠ 0`.
- **Proof sketch**: `s := hne.some`; `κ := X.base.residueField s`;
  `k := AlgebraicClosure κ`; `t := Spec.map (ofHom (algebraMap κ k)) ≫
  X.base.fromSpecResidueField s`. `(N:k) ≠ 0`: transport `IsUnit (N : R)` along a
  ring hom `R → k` extracted from `t ≫ X.structMap : Spec k ⟶ Spec R` (Spec-Γ
  adjunction / `Scheme.residueFieldMap` route — verify names), then
  `IsUnit.ne_zero` in the field.
- **Mathlib lemmas**: `Scheme.fromSpecResidueField`, `Scheme.residueField`,
  `AlgebraicClosure` instances, Spec-Γ adjunction hom equivalence (verify exact
  name: `Scheme.homSpecEquiv`?), `IsUnit.map`, `IsUnit.ne_zero`.
- **Sources**: standard.
- **Generality**: for any `Scheme` with a `⟶ Spec R` — state against `X : EllObj R`
  minimally (match use site per beastmode rule).

---

## Amendments v7 (2026-07-06): OWNER DIRECTIVE — EllipticCurveGeom fibre field → Zariski-local Weierstrass (A-lane ticket)

*Owner decision 2026-07-06 (chat, recorded by beastmode-H): the geometric record's
fibre condition changes from the fibrewise bridge to the **Zariski-local-model
bridge**; `FibrewiseElliptic` becomes a derived lemma; the converse is the Chain-A7
comparison theorem, later. Rationale verified against the tree: (i) `fibres` has
exactly ONE consumer today (GroupLaw.lean:163 baseChange) — cheapest-ever migration
moment; (ii) model side done: T-A2 (projModel any CommRing), T-A3
(`projModel_smooth` ⟺ Δ unit), `projModelπ_isProper` instance
(WeierstrassModel.lean:278); (iii) every constructed curve (universal Tate/Y₁(N),
Γ(3)/Legendre bootstrap for T-E5⇐, ℰ₃, j-line fibres) enters the record with a
trivial witness instead of per-construction fibre analysis; (iv) BB-RR leaves the
construction-side critical path (RR-only directive strengthened — RR then owed only
by the Abel/canonicity chain + the A7 comparison). Honest cost: until A7 lands the
record is a-priori a SUBCLASS of KM 2.1.1/DR II.1.1/Loe 3.3.1 — a stronger-direction
bridge, documented, same pattern as the existing genus-bridge note (T-A9).*

### [T-A8-4] the derived fibre condition — `EllipticCurveGeom.fibrewiseElliptic` (step-4 leftover)
- **Status**: **DONE** (fable-P4, 2026-07-08; `#print axioms` clean; Basic.lean sorry-free,
  GroupLaw + GammaH downstream green). Landed: `Spec_fromSpecResidueField_eq` (Spec-affine
  compat), `fibrewiseElliptic_projModel` (model fibres are elliptic),
  `LocallyWeierstrass.fibrewiseElliptic` (ONE paste of the base-change square onto the
  chart square puts the model over `κ(s)` in a pullback square over
  `(π, fromSpecResidueField s)` — single `isoPullback`, no fibre-congr plumbing), and the
  record corollary `EllipticCurveGeom.fibrewiseElliptic`. · **Claimed**: fable-P4,
  2026-07-07T23:25Z (OWNER-DIRECTED 2026-07-08) ·
  **File**: EllipticCurve/Basic.lean · **Depends**: T-A8 (done) · **Type**: 2 theorems
- **Scope note (the owner's question, answered)**: the FULL equivalence is two directions.
  (⟸ = this ticket) `LocallyWeierstrass ⟹ FibrewiseElliptic` — provable now, sketch was
  banked in T-A8 step 4: sub-lemma `fibrewiseElliptic_projModel` (model fibres are elliptic,
  `isPullback_projModelBaseChange` at residue fields, A5b `hA`/`hB` pattern) + transport
  along the local iso `e` + fibre-of-open-restriction pasting + `IsOpenImmersion`
  residue-field iso. (⟹ = NOT this ticket) `FibrewiseElliptic ⟹ LocallyWeierstrass` is
  T-A7-cmp/T-W-cmp (COH stream): needs cohomology-and-base-change + RR (`BB-COHBC`/`BB-RR`);
  mathlib has neither (verified 2026-07-08: no higher direct images / base-change /
  semicontinuity in Mathlib/AlgebraicGeometry) — stays deferred.

### [T-A8] EllipticCurveGeom v2 — `LocallyWeierstrass` field swap (OWNER-DIRECTED)
- **Status**: **DONE** (beastmode-A, 2026-07-06 — LocallyWeierstrass predicate + field swap
  fibres→localModel + GroupLaw consumer + **T-A8a `LocallyWeierstrass.baseChange` fully proven,
  axiom-clean**; Basic.lean sorry-free, green 2930 jobs; commits ad9a3332/3d862cbb/ca9fd165).
  Validated as the definition of record by v8 review. · **Claimed**: beastmode-A, 2026-07-06 · **Lane**: A (files owned by A; bundle with the
  in-flight 3-spelling refactor; NOT claimable by other lanes) ·
  **Files**: EllipticCurve/Basic.lean (predicate + field swap + drift note),
  EllipticCurve/GroupLaw.lean (:163), Moduli/EllCategory.lean +
  Moduli/Representability.lean (header honesty notes) ·
  **Depends on**: T-A2 (done), T-A3 (done), T-A5a (done) · **Type**: def change + lemmas
- **New predicate** (SPELLING CHOSEN + IMPLEMENTED 2026-07-06, elaborates clean —
  mirrors `FibrewiseElliptic` but over an affine open instead of a residue field, so the
  same `isPullback_projModelBaseChange` machinery drives the migration lemmas; the
  restriction is `pullback π U.1.ι`, the section via the proven
  `pullback.lift (U.1.ι ≫ z) (𝟙 _)` pattern from `FibrewiseElliptic.baseChange`):
  `def LocallyWeierstrass (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) : Prop :=
    ∀ s : S, ∃ (U : S.affineOpens) (_ : s ∈ U.1) (W : WeierstrassCurve Γ(S, U.1)),
      W.IsElliptic ∧ ∃ e : pullback π U.1.ι ≅ projModel W,
        e.hom ≫ projModelπ W = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _) …) ≫ e.hom = projModelZero W`
  The `Spec Γ(S,U)` (isoSpec) and `Spec (.of ↥Γ(S,U))` (projModelπ) codomains coincide
  defeq — no bridge. Predicate landed additively first (no field swap) so each commit stays
  green + sorry-free; field swap gated on `LocallyWeierstrass.baseChange` (no regression of
  the currently-proven base-change chain).
- **Migration steps**:
  1. Add `LocallyWeierstrass` next to `FibrewiseElliptic` (keep the latter, unchanged,
     as a predicate).
  2. Swap the record field `fibres : FibrewiseElliptic …` →
     `localModel : LocallyWeierstrass …`. KEEP `smooth`/`proper` fields (docstring
     note: redundant given localModel via T-A3 + `projModelπ_isProper` +
     locality-at-target — the deliberate `grp`-pattern; derivable later).
  3. GroupLaw.lean:163: `localModel := E.localModel.baseChange g` via new
     `LocallyWeierstrass.baseChange`: for `t : T` pick affine `U ∋ g t` with model
     `W`; affine `V ⊆ g⁻¹ᵁU` with `t ∈ V`; `(E ×_S T)|_V = (E|_U) ×_U V`; transport
     `W` along `Γ(U) → Γ(V)` via `isPullback_projModelBaseChange` + pullback pasting.
     (The old `FibrewiseElliptic.baseChange` lemma STAYS — it is about the predicate.)
  4. Derived lemma `EllipticCurveGeom.fibrewiseElliptic : FibrewiseElliptic E.π
     E.zero E.zero_π`. Sub-lemma `fibrewiseElliptic_projModel : FibrewiseElliptic
     (projModelπ W) projModelZero _` for `W` elliptic over any ring: fibre at `p` ≅
     `projModel (W.map (algebraMap _ κ(p)))` by `isPullback_projModelBaseChange` at
     residue fields (T-A5b `hA`/`hB` pattern); `Δ`-unit maps to unit. Then transport
     along the local iso + fibre-of-open-restriction identification.
  5. Basic.lean header: v2 drift note mirroring the genus-bridge note — a-priori
     stronger; equivalence = A7 comparison (gated COH-1 + [RR-box]); genus form
     remains T-A9's target.
  6. One-line honesty note in the two Moduli headers (functors quantify over the v2
     record; post-A7 provably the sources' class).
  7. Board-register **[T-A7-cmp]** `FibrewiseElliptic → LocallyWeierstrass`
     (Chain A7, decomposition-gme2 pp. 111–115 transcribed; gated COH-1 + [RR-box]).
     Skeleton `:= by sorry` in-file optional — executor's call; the board edge is
     mandatory.
- **Mathlib lemmas**: `IsAffineOpen.isoSpec`, affine-opens basis, `MorphismProperty`
  iso-invariance, pullback pasting.
- **Sources**: KM 2.2.5–2.2.6; GME 2.2.4–2.2.5 (= Chain A7); owner directive above.
- **Generality**: predicate shape matches `FibrewiseElliptic` (any `π, z, hz`).
- **Cross-lane impact audit** (done at filing): `fibres` consumer count = 1
  (GroupLaw:163). H-lane T-H7 (in flight) consumes smooth/proper/grp + T-B6 fibre
  torsion, NOT `fibres` — unaffected. B/D/Q lanes: no `.fibres` references.
- **PROGRESS** (beastmode-A, 2026-07-06): step 1 DONE — `LocallyWeierstrass` predicate
  added to Basic.lean (commit ad9a3332), elaborates clean; spelling recorded above.
  Remaining: `LocallyWeierstrass.baseChange` (→ sub-ticket **T-A8a**, route worked out:
  `isBasis_iff_nbhd.mp T.isBasis_affineOpens` for `V ∋ t ≤ g⁻¹U`; `g.appLE U V` for
  `W' := W.map`; two `pullbackRightPullbackFstIso` pastings; `isPullback_projModelBaseChange`
  bridge; then field swap + `EllipticCurveGeom.fibrewiseElliptic` derived lemma + GroupLaw:163
  fix). VALIDATED as the definition of record by the v8 expert review below.

---

## Amendments v8 (2026-07-06): EXPERT-REVIEW — Weierstrass-atlas / quotient-stack staging correction

*Second expert-review pass (2026-07-06). A **major staging correction**, not a replacement
for Katz–Mazur. It VALIDATES and EXTENDS the owner's T-A8 direction (`LocallyWeierstrass` as
the record). Core moves:*

1. **`LocallyWeierstrass` is the Phase-1 DEFINITION OF RECORD** for elliptic curves over `S`
   (already the T-A8 direction — CONFIRMED). The abstract "smooth proper geometrically-
   connected genus-1 fibres + section" definition is demoted to a **Phase-4 comparison
   target** (`T-W-cmp`). Reviewer Q1 (revised): do NOT use the fibrewise Weierstrass
   condition (`FibrewiseElliptic`) as the definition of record — a fibrewise condition does
   not directly give local equations, and proving that it does needs exactly the coherent-
   cohomology/base-change machine we are avoiding. `LocallyWeierstrass` is syntactically
   stronger but immediately gives explicit equations, coordinate changes, local group laws,
   division/torsion polynomials, Cartier divisors from sections, and the quotient-stack
   atlas. *(Phrasing note: reviewer suggests an affine-open-COVER form; our pointwise
   `∀ s, ∃ U ∋ s` form is equivalent — a cover gives point-neighbourhoods and the
   neighbourhoods form a cover — keep the pointwise form; it is what
   `isPullback_projModelBaseChange` drives.)*

2. **`M_ell` as a concrete quotient stack `[U/G]`**, NOT a Riemann–Roch theorem:
   `U = Spec ℤ[a₁,a₂,a₃,a₄,a₆][Δ⁻¹]` (nonsingular Weierstrass equations), `G =
   WeierstrassCurve.VariableChange` (the `(u,r,s,t)` coordinate-change group — **already in
   mathlib as a `Group`**) acting on `U`. With the locally-Weierstrass definition, `[U/G]`
   is *almost the definition* of the moduli stack — no RR needed. Aligns with KM's own remark
   that their Ch. 4 relatively-representable formalism is "working systematically with stacks
   without ever saying so".

3. **Group law from local Weierstrass charts + descent, NOT Abel/Pic⁰** (reviewer Q3
   revised). Construct/register the `grp` field of `EllipticCurve` from mathlib's Weierstrass
   point group law on each chart + `variableChange`-invariance + descent (`T-W7`). Abel/Pic⁰
   (the deferred `abelEnrichment` canonicity, T-A6) stays the *canonical explanation* but is
   **removed from the critical path** — it becomes part of the Phase-4 abstract comparison.

4. **Coherent cohomology → a separate long-term foundational stream (COH), NOT a
   prerequisite.** BB-COHBC, BB-RR (abstract side), Serre duality, the genus-form comparison
   (T-A9), and abelian-scheme⇒elliptic all live in COH and block ONLY the abstract comparison
   + Hodge/modular-forms + compactification — **never** the open curves `Y(N)`, `Y₁(N)`,
   `Y(ρ̄,p)`.

5. **Cartier machinery is NOT replaced** — the D-stream incidence/subgroup-locus
   representability (T-D11–T-D21) is still required to cut out the level conditions
   (`E[N] = Σ[aP+bQ]`, exact order, cyclic subgroup) as closed subschemes over `U`. The
   quotient-stack layer *organises* the moduli object; Cartier *constructs the level loci*.

### Revised dependency spine (v8)

```
Weierstrass equations over rings (mathlib)
 → universal Weierstrass curve E_U / U            [T-W5]
 → coordinate-change group G = VariableChange     [T-W4]
 → locally-Weierstrass elliptic curves            [T-A8]  ← DEFINITION OF RECORD
 → quotient-stack layer  [U/G]                     [T-W3, T-W6]
 → group law & [N] locally (Weierstrass/division polys) + descent   [T-W7]
 → Cartier divisors & incidence (D-stream)         [T-D11–T-D21]
 → level spaces U_P / U and stacks [U_P/G]         [T-W8]
 → fine schemes Y(N), Y₁(N) when rigid             [T-E7, T-E9, T-H*]  → Y(ρ̄,p) [T-F*]
Parallel, NON-blocking COH stream:
 coherent cohomology → genus-1 fibres → Pic⁰/Abel → abstract elliptic curves
 → M_ell^W ≃ M_ell^abstract [T-W-cmp] → abelian-scheme⇒elliptic → Hodge/modular forms
```

### Stream W — Weierstrass atlas & quotient stack for `M_ell` (NEW; per v8 review)

*Deliberately small stack layer — no atlases/diagonals/algebraic-stack properties/coarse
moduli yet, just enough groupoid-valued functor language. Sequenced BEFORE KM-4.7 (T-E5) and
stack-packaging (T-E8). Tickets are lane-tagged for the streams that own the relevant files.*

- **[T-W1] `projective-space-moduli`** (WARM-UP — do first). `ℙⁿ` represents
  `S ↦ {invertible quotients O_S^{n+1} ↠ L}`. Exercises the exact later API — moduli functor,
  representability, base change, line bundles, universal object, descent under
  trivialisations — and prepares Weierstrass equations as sections of line bundles.
  **Lane**: E · **Depends**: none · **mathlib**: `AlgebraicGeometry.Proj` + its universal
  property, scheme line bundles · **Type**: def + representability theorem · **Sources**:
  reviewer v8; Hartshorne II.7.1; EGA II.4.2.3.

- **[T-W2] `moduli-problem-core` (groupoid-valued)**. Add a groupoid-valued variant of
  `ModuliProblem` (`Schemeᵒᵖ ⥤ Cat`/`⥤ Grpd`) so `M_ell` is not pretended set-valued; keep the
  set-valued form for rigid problems (its `π₀`/coarse shadow). **Lane**: E · **Depends**:
  existing `ModuliProblem`, `Moduli/Groupoid.lean` · **Type**: def + API · **Sources**:
  reviewer v8 Q7; KM Ch. 4.

- **[T-W3] `quotient-stack-core`**. Minimal API: `GroupAction G X`, `ActionGroupoid G X :
  Category`, `QuotientStack G X : Schemeᵒᵖ ⥤ Cat`, and the user-facing theorem
  `[U/G](S) ≃ groupoid of G-torsors P → S with a G-equivariant P → U`. No algebraic-stack
  properties. **Lane**: Q (owns `SchemeQuotient`/`AffineQuotient`/`SpecGroupAction`) ·
  **Depends**: Q-stream quotient infra (T-Q5/T-Q6) · **Type**: def + API + torsor-description
  theorem · **Sources**: reviewer v8; standard `[U/G]` groupoid.
  - **Status**: done (2026-07-07T03:05Z; core scope: ActionGroupoid +
    QuotientStack functor + coarse comparison — the torsor-description theorem
    split to T-W3b at cut, see below) · **Claimed**: beastmode-Q,
    2026-07-07T02:20Z · **File**: Moduli/QuotientStack.lean (NEW)
  - **Alias decision (at pickup, per v8 note)**: `GroupAction G X` :=
    `AlgebraicGeometry.SchemeAction G X` (ForMathlib/SchemeQuotient.lean) — the
    established Q-lane vocabulary IS the T-W3 `GroupAction`; no new structure,
    no rename (T-W4 should `SchemeAction`-register its action). **T-W4 is
    hereby UNBLOCKED** (its dep was the GroupAction vocabulary).
  - **DELIVERED** (sorry-free, zero warnings, standard axioms):
    `ActionGroupoid σ S` (objects = S-points, homs = {g // t ≫ σ.hom g = t'},
    Groupoid instance, comp_val/id_val/eqToHom_val), `ActionGroupoid.restrict`
    (precomposition functors), `QuotientStack σ : Schemeᵒᵖ ⥤ Cat` (strict laws
    via private functor_ext; Cat.Hom-wrapper via Functor.toCatHom + congrArg),
    `ActionGroupoid.toQuotient : [X/G](S) ⥤ Discrete (S ⟶ X/G)` (coarse
    comparison via hom_quotientπ — the T-Q7 feed). GOTCHAS: bare @Functor.ext
    resolves to core-Lean LawfulFunctor.ext — qualify @CategoryTheory.Functor.ext;
    Discrete laws via Subsingleton.elim; congrArg-not-rw for subtype-motive.
- **[T-W3b]** (done 2026-07-07T06:50Z — scope: the v8 one-line equivalence is
  FALSE as literally stated (attack log); the mathematically-correct core is
  PROVEN: TorsorPair groupoid + trivialization functor + full faithfulness
  over connected nonempty bases + all trivial-torsor fields; the base-change/
  self-trivialization tail is T-W3c below) the torsor description of
  `[X/G](S)`: define the groupoid of pairs (finite étale `G`-torsor `p : P ⟶ S`
  in the ∐-comparison sense of `TorsorData`/Stack.lean, `G`-equivariant
  `u : P ⟶ X`), the trivialization functor from `ActionGroupoid σ S`
  (`t ↦ (∐_G S, γ ↦ σ γ ∘ t)`), full faithfulness (provable), and essential
  image = locally-trivial pairs (the fppf/étale-descent half — gated on
  stream-DESC like T-Q6e's descent step; for CONSTANT finite G étale-local
  triviality of torsors is the honest scope). Sources: reviewer v8; KM 4.7
  proof pp. 114–116 uses exactly the trivial-torsor comparison. Lane Q.
  - **Progress (2026-07-07T05:20Z) — CONSTRUCTIBLE CORE COMPLETE** (all
    sorry-free, zero warnings, axiom-clean, Moduli/QuotientStack.lean):
    `TorsorPair σ S` + Hom + Category instance; trivial-torsor data layer
    (`trivialTorsorAction`/`trivialTorsorπ`/`trivialTorsorMap` + laws +
    `trivialTorsorLeft` left-translations); ALL FOUR property fields:
    `trivialTorsorπ_etale` (IsZariskiLocalAtSource.sigmaDesc),
    `trivialTorsorπ_surjective`, `trivialTorsorπ_finite` (via
    `isFinite_sigmaDesc_id` — ForMathlib-grade: the fold of a finite coproduct
    is finite, base change of the sigmaSpec-model along
    specULiftZIsTerminal.from), and **`trivialTorsor_torsor`** (the
    ∐-comparison iso: single-distributivity square via
    isPullback_of_isColimit_left + the (γ,h) ↦ (h, h·γ) reindexing with
    explicit inverse + factorization `trivialTorsor_comparison_eq`); the
    **trivialization functor `trivialize : ActionGroupoid σ S ⥤ TorsorPair σ S`
    ASSEMBLED** (morphisms = left translation by `f.1⁻¹`). GOTCHAS: erw at
    ι_desc_assoc/isoPullback/Cofan.fac steps (instances-transparency);
    IsIso.comp_isIso' explicit; reassoc-variants pre-normalize (no trailing
    id_comp); duplicate [Finite G] section-vars poison instance synthesis.
    **`trivialize_faithful` PROVEN** (2026-07-07T05:40Z, first-try): faithful
    for [Nonempty S] exactly (left translations distinguished on a 1-summand
    point via sigmaι_eq_iff; the S = ∅ counterexample is the only faithfulness
    obstruction). REMAINING TAIL: fullness **for connected nonempty S**
    (clopen-decomposition argument: restrict a pair-hom to the 1-summand,
    the ι_γ-range preimages are a finite clopen partition of S, connectedness
    picks the unique γ, then hom = left γ⁻¹ by equivariance — attack finding
    q-lane.md; needs PreconnectedSpace vocabulary;
    **`isClopen_range_sigmaι` LANDED** 2026-07-07T06:00Z — clopen ranges of
    coproduct components, the partition ingredient; GOTCHA: no Sigma.ι-headed
    IsOpenImmersion instance exists, route via inferInstanceAs at the
    colimit.ι head, Gluing.lean:813) and the (descent-gated) essential-image
    statement (stackification-level comparison).
    **`trivialize_full` PROVEN** (2026-07-07T06:40Z): full for
    [ConnectedSpace S] — the clopen argument exactly as banked; with
    trivialize_faithful, **full faithfulness of the [X/G]-trivialization
    holds over connected nonempty bases** (the attack-log obstructions are
    exactly the failures). GOTCHAS: explicit args to IsOpenImmersion.lift
    (instance synth at metavars fails); ∀-shaped haveI instances fine but
    set-vars trip TC; reassoc_of% + erw for transparency-poisoned steps;
    ∃-repackage for opaque indices. REMAINING: only the (descent-gated)
    essential-image statement.
- **[T-W3c]** (**DONE** 2026-07-07T11:30Z, beastmode-Q — both parts, sorry-free,
  zero warnings, axiom-clean [propext/Classical.choice/Quot.sound]) TorsorPair base
  change + self-trivialization. **DELIVERED** (Moduli/QuotientStack.lean):
  `TorsorPair.pullbackAction` (base-changed action) + hom_fst/hom_snd/over_base;
  `isPullback_pullbackSnd_map` (pasting `(P×_S S')²_{S'} ≅ (P×_S P)×_S S'` via
  of_iso_pullback + explicit inverse); `isPullback_sigma_pullbackSnd` (distributivity
  `∐_G(P×_S S') ≅ (∐_G P)×_S S'` — extensivity template, `Sigma.desc` defeq to the
  Cofan.desc so `exact key` closes); `TorsorPair.pullback_shear_isIso` (the `torsor`
  field: `of_right` cancels distributivity-outer + pasting-right to exhibit the
  base-changed shear as base change of `A.torsor`, then `of_isPullback` on
  `isomorphisms Scheme`); `TorsorPair.pullback` (full base-changed pair; finite via
  inferInstance, etale/surjective via `MorphismProperty.pullback_snd`, u through `A.u`);
  `TorsorPair.homInv`/`isoOfHom` (TorsorPair.Hom with iso underlying ⟹ groupoid iso);
  `TorsorPair.selfTrivialization` (**part ii**: `A.pullback A.p ≅ trivialTorsorPair
  σ A.P A.u`, the comparison IS `A.torsor`'s shear as a torsor-pair morphism — NOT
  descent-gated). GOTCHAS: `pullback.map` cond is `condition.symm`; `pullback.lift_fst/snd`
  are `@[reassoc]` NOT `@[simp]` (pass `_assoc` variants; base won't fire on right-assoc);
  `simp [condition]` corrupts pullback type-indices — use targeted `← condition`; TC won't
  reduce `{..}.hom` for `[IsIso f.hom]` synth → name the Hom (`let f` + `haveI : IsIso
  f.hom := A.torsor`); `omit [Group G] in` goes BEFORE the docstring. **T-Q6e's
  f₀-pullback vocabulary now available.**
  - **(superseded planning notes below; kept for the SIGMA-FACTS survey)** (i)
  `TorsorPair.pullback (q : S' ⟶ S) : TorsorPair σ S →
  TorsorPair σ S'` — total space `P ×_S S'`, action by functoriality, property
  fields via base-change stability instances (IsFinite/Etale/Surjective ✓
  mathlib instances; the ∐-comparison for the pulled-back pair from the
  original by pullback-juggling). (ii) **self-trivialization** (NOT
  descent-gated — CORRECTION of the earlier note: the torsor FIELD is exactly
  local triviality along p): for `A : TorsorPair σ S`, `A.pullback A.p ≅
  trivialTorsorPair σ A.P A.u` — the comparison IS `A.torsor`'s iso read
  through `∐_G P ≅ P ×_S P`. This is the KM pp. 114–116 f₀-pullback step's
  vocabulary (T-Q6e-adjacent). The full stackification equivalence stays out
  of scope (that half is genuinely descent/sheafification). Lane Q.
  - **MATHLIB SIGMA-FACTS SURVEY (2026-07-07T04:00Z, banked for pickup)**:
    (1) Etale (Sigma.desc f) ← `IsZariskiLocalAtSource.sigmaDesc`
    (Morphisms/Basic.lean:303; Etale is HasRingHomProperty ⟹
    IsZariskiLocalAtSource via RingHomProperties.lean:379; Flat.lean:105 is the
    template) — **USED, trivialTorsorπ_etale LANDED**. (2) Surjective via
    `Surjective.sigmaDesc_of_union_range_eq_univ` (UnderlyingMap.lean:116) —
    **USED, trivialTorsorπ_surjective LANDED**. (3) IsFinite/IsAffineHom/
    IsIntegralHom of Sigma.desc: NOT in mathlib — only BINARY
    `coprod.desc` instances (Finite.lean:147, Affine.lean:218, Integral.lean:98;
    engine `HasAffineProperty.coprodDesc_affineAnd` AffineAnd.lean:283) ⟹
    T-W3b-i sub-lemma: `IsFinite (Sigma.desc fun _ : ι => 𝟙 S)` for
    [Finite ι]. ROUTE OF RECORD (probed 2026-07-07T04:10Z, all pieces exist):
    (i) `sigmaSpec R : (∐ Spec (R i)) ⟶ Spec (Π R i)` is an ISO for [Finite ι]
    (AG/Limits.lean:606,640) ⟹ the model fold `∐_ι Spec ℤ ⟶ Spec ℤ` is
    iso-conjugate to `Spec.map (diagonal ℤ →+* Π_ι ℤ)`, which is IsFinite via
    the Spec-map/HasAffineProperty criterion + `Module.Finite` for finite Pi;
    (ii) the general fold `∐_ι S ⟶ S` is the base change of the model along
    `terminal.from S` (`Scheme.specZIsTerminal`) — identify via the
    distributivity iso `IsUniversalColimit.isPullback_of_isColimit_left` +
    `FinitaryPreExtensive.isUniversal_finiteCoproducts` (worked template
    AG/Geometrically/Reduced.lean:97-101); (iii) IsFinite is stable under base
    change + respects isos (instances). Alternative fallback: iterate the
    binary coprod.desc instance by `Finite.induction_empty_option`.
    ForMathlib-grade, upstream candidate. **MODEL CASE LANDED**
    (2026-07-07T04:30Z): `isFinite_sigmaDesc_id_spec` (QuotientStack.lean) —
    the affine fold `∐_ι Spec R ⟶ Spec R` is finite (sigmaSpec-conjugation,
    pi≫eval = 𝟙 by rfl, IsFinite.SpecMap_iff + Module.Finite.pi; the
    RingHom.Finite letI-instance is DEFEQ to the Pi module structure — double
    show-unfold + direct exact; Spec.map_id needed exact-not-rw). Remaining:
    step (ii) base-change to general S per the route of record. (4) pullback-∐
    distributivity: `IsUniversalColimit.isPullback_of_isColimit_left`
    (VanKampen.lean:796) + `FinitaryPreExtensive.isUniversal_finiteCoproducts`
    (Extensive.lean:449) + `instance FinitaryExtensive Scheme`
    (AG/Limits.lean:455); WORKED TEMPLATE at
    AG/Geometrically/Reduced.lean:97-101 — the ∐-comparison-iso field of the
    trivial TorsorPair goes through this. (5) NO torsor-of-constant-group
    notion anywhere in mathlib AlgebraicGeometry — our TorsorPair is new
    (upstream candidate with SchemeQuotient).

- **[T-W4] `weierstrass-coordinate-change-group`**. Package mathlib's
  `WeierstrassCurve.VariableChange R` (`(u,r,s,t)`, `[Group]` EXISTS) as a group-scheme `G`
  acting on `U := Spec ℤ[a₁,a₂,a₃,a₄,a₆][Δ⁻¹]` via `WeierstrassCurve.variableChange` on the
  coefficients; register as a `GroupAction` (T-W3). **Lane**: A · **Depends**: T-W3 ·
  **mathlib**: `WeierstrassCurve.VariableChange`, `.variableChange`, `variableChange_Δ`
  (`Δ ↦ u⁻¹²·Δ`, a unit, so the action preserves `Δ⁻¹`) · **Type**: def + action lemmas ·
  **Sources**: reviewer v8; Silverman III Table 1.2.

- **[T-W5] `universal-weierstrass-atlas`** — **DONE, axiom-clean** (beastmode-A 2026-07-06/07: Moduli/WeierstrassAtlas.lean — universalWeierstrass over ℤ[a₁..a₆], atlas ring = Localization.Away Δ, universalWeierstrassLoc + IsElliptic, weierstrassAtlas U = Spec, universalCurve E_U = projModel, proper+smooth+zero-section, **`universalCurve_localModel` FULLY PROVEN** (T-W5a — both chart-compat squares, via term-`▸` crux + `erw` poison-bypass), and **`universalEllipticCurve : EllipticCurveGeom weierstrassAtlas` assembled**; all sorry-free + axiom-clean. Feeds T-W6 quotient stack). `U := Spec ℤ[a₁,a₂,a₃,a₄,a₆][Δ⁻¹]` and the
  universal Weierstrass elliptic curve `E_U := projModel W_univ → U` (`W_univ` = the
  tautological `WeierstrassCurve` over `ℤ[a₁..a₆,Δ⁻¹]`, `IsElliptic` since `Δ` is a unit).
  **Lane**: A · **Depends**: T-A2 (`projModel`, done) · **Type**: def + `IsElliptic` witness ·
  **Sources**: reviewer v8; KM 2.2 / GME 2.2. Mostly assembly over `projModel`.

- **[T-W5a] `universal-curve-localModel-compat`** — **DONE, axiom-clean** (beastmode-A 2026-07-07).
  Both `LocallyWeierstrass` compatibility squares (`c1` structure-map, `c2` section) in
  `universalCurve_localModel` are PROVEN. **Breakthrough**: the crux skew was bypassed via
  **term-`▸`** (`hφ_eq := (Scheme.isoSpec_Spec_inv _).symm` and `hcrux := hφ_eq ▸ crux_test` —
  the direct-term defeq coercion works where `rw`/`simp` on `isoSpec_Spec_inv` trips the
  presheaf-representation skew), and the affineOpens-subtype coercion **poison** (`rw` fails at
  *instances* transparency) was bypassed with **`erw`** (default transparency) + `cancel_mono φ`
  (c1) and conv-isolated poison-elimination-first (c2, keeping it under the heartbeat budget).
  `crux_test : isoSpec_⊤.hom ≫ isoSpec.inv = ⊤.ι` is a clean standalone lemma. Historical recipe
  below (the earlier `inv φ` route was abandoned; the `@inv`-explicit fix was insufficient).
  **Math is trivial** — it is the affine single-chart special case of
  `LocallyWeierstrass.baseChange` (already proven, EllipticCurve/Basic.lean). Reduction (derived,
  on paper): `c1 = simp [Iso.trans_hom, asIso_hom, asIso_inv, IsPullback.isoPullback_inv_snd]`
  `+ hbc (inv(fst)≫snd = π ≫ inv φ, via pullback.condition) + pullback.condition + hid`
  `(⊤.ι ≫ inv φ = isoSpec.hom, via Scheme.isoSpec_Spec_inv + IsAffineOpen.fromSpec_top +`
  `IsAffineOpen.isoSpec_inv_ι)`; `c2` analogous landing on `projModelZero` naturality.
  **BLOCKER is Lean elaboration, not math**: `inv φ` / `inv (pullback.fst _ φ)` (φ =
  `Spec.map (ofHom (algebraMap WeierstrassAtlasRing Γ(⊤)))`) fail `IsIso` synthesis — the local
  `IsIso φ` fact is not matched because (a) the `algebraMap` term is only defeq at *instances*
  transparency, (b) `set φ` makes TC let-unfold φ and search the failing `IsIso (Spec.map …)`,
  (c) `weierstrassAtlas.isoSpec` trips a presheaf-type skew under instances transparency.
  **Fix path** (for the picking-up worker): hoist `hid`/`hbc`/`c1`/`c2` to *top-level* private
  lemmas stated with explicit `@CategoryTheory.inv _ _ _ _ φ hφi` instance arguments (bypasses
  synth entirely), or rebuild the e-iso without `isoSpec` (use `Scheme.ΓSpecIso`/`topIso`
  directly). **Lane**: A · **Depends**: T-W5 (e-iso core, done) · **Type**: 2 compat lemmas.

- **[T-W6] `Mell-Weierstrass-quotient-stack`** (HEADLINE). `M_ell^W := [U/G]` (T-W3 on
  T-W4/T-W5) and `M_ell^W(S) ≃ groupoid of LocallyWeierstrass elliptic curves over S` — the
  equivalence is descent of Weierstrass equations under coordinate changes; with T-A8 it is
  *almost definitional*. **Lane**: W · **Depends**: T-W3, T-W4, T-W5, T-A8 (+ its
  `baseChange`) · **Type**: def + equivalence theorem · **Sources**: reviewer v8; KM Ch. 4.

- **[T-W7] `group-law-from-weierstrass-charts`** (Q3 reframe; HIGH LEVERAGE). Construct the
  `grp` group-scheme structure on a LocallyWeierstrass curve from mathlib's Weierstrass point
  group law per chart (`WeierstrassCurve.Jacobian.Point`/`.Affine.Point`), prove
  `variableChange`-invariance so it descends chart-independently; `[N]` likewise from division
  polynomials. Reviewer's replacement for Abel/Pic⁰ as the *route* to the group law.
  **UNBLOCKS** the `abelEnrichment`-EXISTENCE direction (group law exists constructively),
  potentially retiring the T-A6 gate on the level-functor `map` fields (`pullSection_add`).
  **Lane**: A · **Depends**: T-A8, T-W4 · **Type**: def + descent/invariance lemmas ·
  **Sources**: reviewer v8 Q3; Silverman III.2–3; mathlib `EllipticCurve.Weierstrass` group.
  **Progress** (beastmode-A 2026-07-07): **AFFINE GROUP-HOM DONE** (axiom-clean, commit dbcb4448) —
  `ForMathlib/AffinePointVariableChange.lean`, general-`C` (mathlib only had the special
  origin-translation `equation_iff_variableChange`). 18 decls: `vcX`/`vcY` (maps `u⁻²(x−r)`,
  `u⁻³(y−s(x−r)−t)`); `equation_smul` (poly scales by `u⁻⁶`); `nonsingular_smul` (Jacobian
  `∂/∂Y↦u⁻³∂/∂Y`, `∂/∂X↦u⁻⁴(∂/∂X+s·∂/∂Y)`); `pointMap`+`pointMap_neg`; `addX/negAddY/addY_smul`
  (poly identities); `slope_smul` (secant + tangent, `= u⁻¹(slope−s)`); **`pointMap_add`**
  (case analysis over `Point.add_of_X_ne/Y_ne/Y_eq`) and **`pointHom : W.Point →+ (C•W).Point`**.
  **AFFINE GROUP-ISO NOW COMPLETE** (commit, ~25 decls): added `equation_smul_iff`/`nonsingular_smul'`
  (reverse via unit-cancellation kept in the `u⁻¹` atom — `IsUnit.mul_right_eq_zero`), `ivcX`/`ivcY`
  + composition identities, `pointMap_injective`/`surjective`, and **`pointEquiv : W.Point ≃+
  (C•W).Point`** (`AddEquiv.ofBijective`). The elliptic-curve group law is invariant under a
  Weierstrass coordinate change AS A FULL GROUP ISOMORPHISM, axiom-clean. Also `pointEquiv_zsmul`
  (carries `n`-torsion to `n`-torsion → level-structure invariance, feeds T-W8).
  **DESCENT DATA COMPLETE (2026-07-07, ~37 decls)**: the coordinate change now has the full
  cocycle — `vcX_comp`/`vcY_comp` (coordinate), **`pointMap_mul`** (point-level, via `eqRec`
  `subst` transport helpers) and **`pointMap_one`** (unit) so `pointMap` is a genuine action of the
  `VariableChange` group on points; plus **base-change naturality** `vcX_map`/`vcY_map` (functorial
  in the base ring). The affine/fibrewise descent datum for the group law is fully formalised.
  **SCOPING (2026-07-07)**: the SCHEME-level descent (retiring T-A6) is a LARGE foundational phase,
  not a quick next step — mathlib's elliptic-curve group law is **field-only**
  (`Affine.Point`/`Projective.Point.instAddCommGroup` need `[Field F]`); there is **no group-scheme
  structure over a general base** (only the categorical `MonObj`/group-object machinery). So the
  descent needs the elliptic-curve group-SCHEME structure (mult morphism `E ×_S E → E`) built
  first — its own sub-project (route via the abelEnrichment/T-A6 machinery or a dedicated
  group-scheme development). The affine/fibrewise invariance (this ticket) is the reusable input.
  **PLANNED (2026-07-07, `/develop`, rigidity route, full-GrpObj scope)**: sharp goal =
  construct `GrpObj (Over.mk π)` = discharge `abelEnrichment_exists` (GroupLaw.lean:74); everything
  else (`mulBy`/[N], `pointAddCommGroup`, `baseChange`) is already derived from the `grp` field. On
  the critical path (owner directive: only BB-RR assumed). Full decomposition +
  Lean-skeleton design + source status in **`.mathlib-quality/tw7-plan.md`**. **ROUTE CORRECTED
  after reading Faltings–Chai I (`.djvu`→`refs/…/faltings-chai-degeneration.pdf`):** FC I.1.1
  *defines* an abelian scheme AS a group scheme (smooth/proper/connected) — rigidity does NOT prove
  associativity of a constructed `mul`; FC 2.7's homomorphism-extension needs S *normal* (not the
  moduli non-reduced case). Existence axioms instead go via **reduce-to-universal-integral-atlas +
  base change** (mathlib field-level `Affine.Point.instAddCommGroup` over `Frac R`, `R↪K`, density);
  rigidity (GIT §6.1) is used ONLY for canonicity (T-W7.7). Sub-tickets below.
  **REVIEWER REPLY INTEGRATED, ADVERSARIALLY AUDITED (2026-07-07;
  `.mathlib-quality/expert-review/2026-07-07-tw7/{reply,integration}.md` + tw7-plan.md v2)**:
  reduce-to-universal CONFIRMED. Adopted: uniform per-ring `Γ(projModel W, O) ≅ R` (2-chart
  computation, universality-by-instantiation — **BB-COHBC RETIRED**); `mulHom_U` via the
  **Bosma–Lenstra complete system of two (2,2)-addition-laws** (acquire B–L 1995 + Lange–Ruppert 1985
  first); generic-POINT bridge (pointwise over `κ(η)` — no field addition morphism needed); global
  VC-equivariance leaf; bundled atlas; T-W7a/T-W7b milestone split. REJECTED: reviewer's rigidity
  sketch is INCOMPLETE over non-reduced bases (globalization step — their own Q6 argument blocks it);
  R3 = SOURCE-REQUIRED (Mumford GIT verbatim), follow-up filed (`REVIEW_FOLLOWUP-tw7.md`). CAUGHT
  (reviewer missed): chart-gluing needs the **comparison theorem** (pointed iso of projModels =
  unique variable change) — new 1b, elementary via the pole filtration (0i). **PARALLEL LANES
  P0–P5 in tw7-plan.md — workers can be assigned NOW to P0/P2/P3/P4/P5.**
  **SOURCES ACQUIRED (2026-07-07 pm)**: Mumford GIT (djvu→pdf, text layer) + Mumford *Abelian
  Varieties* (owner-supplied); Bosma–Lenstra JNT 53 (fetched, Lenstra's Leiden archive, OCR'd) +
  Lange–Ruppert Invent. 79 (fetched, GDZ `LOG_0040`) — all local `refs/`, never committed. **GIT
  §6.1 + Cor 6.2–6.6 quote-mined verbatim → `tw7-source-quotes.md`: R3 RESOLVED** (mechanism =
  Artinian thickenings + Krull intersection + clopen/connected; case 3 not needed — `E` has a
  section). Rigidity scope honest: **locally noetherian, componentwise** (GIT ch. 6 convention) —
  arbitrary-`S` polish split off as T-W7.8 (EGA IV §8 spreading-out, mathlib gap). **ALL SIX LANES
  P0–P5 NOW UNBLOCKED** (P1 ungated by B–L; P4 fully specified R1–R3+C1–C4). Follow-up revised:
  F1 retired (answered by source), F1′ = is loc.-noeth. canonicity enough downstream; F2 = B–L
  `{Z=0,Y=0}` instantiation check; F3 = comparison theorem (unchanged).
  **ROUND-2 REPLY INTAKE (2026-07-07 pm; `reply2.md`, table in `integration.md`)**: assessed as a
  ROUND-1 DIGEST — F1′/F2/F3 NOT addressed (re-send `REVIEW_FOLLOWUP-tw7.md`); its m_U/rigidity
  sketches superseded by B–L/GIT. Adopted: 0i decl names `projModel_globalSections_eq_baseRing` /
  `locallyWeierstrass_pushforward_O_eq_O`. Its **"urgent Γ₁(N) drift" VERIFIED FALSE (stale)**:
  code is KM-correct — `orderDivisor = [P]+⋯+[NP]` deg-N (ExactOrder.lean:97), `HasExactOrder` =
  subgroup divisor KM 1.4.1 (:104), `IsGammaOne := HasExactOrder` (LevelStructure/Basic.lean:70);
  brief warns N-vs-N² explicitly (REVIEW_BRIEF.md:24,:72). **Do NOT spawn a worker on the "drift".**

- **TICKET CONTRACT (T-W7 board v3, cut from the decompose skeleton 2026-07-07, commit
  `ba82784b`)**: every ticket below is *"fill the named `sorry` declarations"* in the named
  file — the Lean statements are CANONICAL IN THE SKELETON (copy nothing; the decls exist and
  `lake build` is green). Per-ticket **statement text, proof sketch, mathlib-lemma list,
  verbatim source quotes, and generality decisions** live in the matching leaf entry of
  `.mathlib-quality/decomposition.md` (leaf IDs cited per ticket) — that entry is part of the
  ticket. Done-bar per AINTLIB: build green, sorry-free decls, standard axioms only, NO
  maxHeartbeats. **Lanes**: P0/P2 IN PROGRESS (owner-dispatched workers 2026-07-07); P1, P3,
  P4, P5 open for workers now.

- **[T-W7.0a]** atlas ring is a domain — `universalWeierstrass_Δ_ne_zero`,
  `instance IsDomain WeierstrassAtlasRing` (GroupLawConstruction.lean:44–66).
  - **Status**: done (lane P0; both decls proven; board flipped 2026-07-07T14:01Z per coordinator 1a) ·
    **File**: EllipticCurve/GroupLawConstruction.lean ·
    **Depends**: none · **Parallel**: yes · **Type**: lemma + instance
  - Sketch: evaluate `Δ` at `y² = x³ − x` over `ℚ` (`Δ = 64`); then
    `IsLocalization.isDomain_localization` (verified) with `Δ ∈ nonZeroDivisors`.
    Leaf **L-0a** (decomposition.md).

- **[T-W7.0b]** negation on the model — `negModelHom` + `_π`, involution, `_zero`,
  `_specPoints` (GroupLawConstruction.lean:346–430 — pointer refreshed per coordinator 1a).
  - **Status**: **DONE (5/5 decls, axiom-clean)** · **Claimed**: beastmode-B (lane P0),
    2026-07-07T16:55Z. **DONE (axiom-clean, committed)**: `negModelHom` (def), `negModelHom_π`
    (7ddc51b6, via new ForMathlib `map_comp_toSpecZero` 25a8a4c9 + `awayMap_fromZeroRingHom`
    d627068f + `gradedRingHomZero`), `negModelHom_negModelHom` (involution), **`negModelHom_zero`
    PROVED** (swept into HEAD). `_zero` infra all axiom-clean: (N) ForMathlib
    `Proj.fromOfGlobalSections_map` + `irrelevant_map_comp_toRingHom_eq_top` (9bae1c62), (ρ=id)
    ForMathlib `Proj.map_negScaling_eq_id`/`map_degScaling_eq_id` "unit-rescaling ⇒ id on Proj"
    (f32dbc1e), (=) `projModelZeroEval_neg_eq_allNeg`, plus GLC helpers `allNegVec_smul_of_homogeneous`
    (aeval of `−X` scales homogeneous deg-`d` by `(−1)^d`), `allNegGradedQuot_scale`, `allNeg_map_id`.
    **`_specPoints` PROVED (axiom-clean, in HEAD)** — `by_cases InZChart`: infinity via
    `specPoint_eq_zero_of_not_inZ` + `negModelHom_zero` + `projModelPointsEquiv_zero`; Z-chart via
    `projModelPointsEquiv_some` on both `P` and the composite, with the coordinate leaf **L2**
    (`negChartMap = Away.map (negGradedQuot) ∘ awayCongr`; chart action `X₀/X₂↦X₀/X₂`,
    `X₁/X₂↦(−X₁−a₁X₀−a₃X₂)/X₂`) proved via `negChartMap_coord0`/`_coord1`, threaded through
    `chartHom_negModelHom` (L2a: `φ_{g≫neg} = φ_g ∘ negChartMap`, via `cancel_mono` on `awayι(X₂)`)
    and `negModelHom_zEquation`/`_zCoord0`/`_zCoord1`; RHS by `Affine.Point.neg_some`.
    **KEY (leaf infra)**: the coordinate lemmas MUST use `simp only` not `rw` — the goals mix
    `chartSolutionsEquiv`- and `chartHomEquiv`-headed heavy terms, and `rw`/kabstract (no
    discrimination-tree pre-filter) `isDefEq`s the pattern against the wrong-headed term and times
    out whnf-ing the equiv (200000 heartbeats); `simp only`'s disc-tree skips non-matching heads.
    Also caught+fixed: `Scheme.comp_base` → `Scheme.Hom.comp_base` (mathlib rename) had SILENTLY
    sorried `inZChart_iff_opensRange` (L1's leaf) — a failed `rw` injects `sorryAx` via error
    recovery; only `#print axioms` (not `lake build`, which was green) surfaced it. ·
    **File**: GroupLawConstruction.lean · **Depends**:
    T-W7.0a (done; specPoints also T-W7.0f, now done) · **Parallel**: with P1–P5 · **Type**: def + 4 lemmas
  - Sketch: projectivise `[X : −Y−a₁X−a₃Z : Z]` via the `baseChangeGradedHom` template
    (`WeierstrassModel.lean:1657`, PROVEN pattern); points-spec by the `projModel_points`
    chart analysis. Δ-free except specPoints. Leaf **L-0b**.

- **[T-W7.0c-i]** the two B–L addition laws — transcribe §5, define `blOpenZ`, `blOpenY`,
  `addOnZ`, `addOnY` (GroupLawConstruction.lean:252–274 — pointer refreshed per coordinator 1a).
  - **Status**: in_progress (lane P1) · **Claimed**: coordinator-P1, 2026-07-07T14:33Z ·
    **Increment 1** (this claim): `EllipticCurve/AdditionLaw.lean` polynomial layer — law-2
    defs + the 6 core certified identities (3 minors, 3 diagonal) + O-columns/scaling +
    c5α skeleton decls; certificate policy per coordinator: nothing above ~150-term
    cofactors (equation_addXYZ + c5 go via c5α/c5β). GLC scheme defs deferred while P0
    holds live edits there. · **File**: GroupLawConstruction.lean · **Depends**: T-A8
    (done), **T-W7.0e, T-W7.0f (coordinator §2: the c5 reroute consumes the ext principle +
    dictionary — "Depends: none" was FALSE; P1 is NO LONGER gate-free)** · **Parallel**: after
    0e/0f · **Type**: 4 defs + 2 NEW leaves (factorization bridge; (2,2)-triple→morphism
    plumbing — skeletonize per coordinator §2 BEFORE proving c5 into them)
  - Sketch: transcribe the two bidegree-(2,2) triples (lines `Z=0`, `Y=0`) from
    `refs/ModularCurves/bosma-lenstra-addition-laws.pdf` §5, **CAS-verify each polynomial
    before Lean**; opens = complements of the common-vanishing loci; triple-on-open ⟹
    morphism (repo `Proj` chart plumbing). Leaves **L-0c1** (quotes: B–L Thm 2 + p. 230–231).
  - **Progress** (coordinator-P1, 2026-07-07T14:49Z): **increment 1 LANDED** (dba3aa8c) —
    `EllipticCurve/AdditionLaw.lean` green + axiom-clean (propext/choice/quot only on all 10
    audited decls), ZERO sorries, default heartbeats (27s elaboration / 24s lake build):
    law-2 defs `dblAddX/Y/Z` + `dblAddXYZ` (verbatim from the CAS exports via
    `emit_addition_law.py` — transcription is not a trust step); **all six core certificates
    kernel-checked on the first sign convention** (3 cross-law minors, cofactors 45–110
    terms; 3 diagonal-is-`dblXYZ`, cofactors 3–13 terms); 6 O-columns + 3 bidegree-smul by
    plain `ring`. BONUS: c5α's engine `eq_zero_of_forall_isMaximal_mem` PROVEN (not
    sorried). REMAINING for 0c-i: the 4 GLC defs (`blOpenZ/Y`, `addOnZ/Y`) = c5β plumbing +
    c5α per-chart vanishing; GLC held by P0's live edits — claim stays open for increment 2.

- **[T-W7.0c-c5α]** on-curve factorization bridge (NEW leaf, coordinator §2): the B–L
  triples land on the curve at the RING level over the universal atlas.
  - **Status**: done (coordinator-P1, 2026-07-07T18:06Z → 20:34Z) · **Claimed**:
    coordinator-P1, 2026-07-07T18:06Z. Route note at claim: the field-level input needs NO
    new content — at a field point `dblAdd(P,Q)` is either `0` (equation trivial) or, by
    the six dba3aa8c certificates, projectively proportional to a law-1/doubling value,
    which mathlib's equation specs put on the curve.
  - **DONE** (91f9499e field layer + 217f7aba ring layer, both zero-sorry, axiom-clean):
    headline `equation_dblAddXYZ_of_isJacobsonRing` — over ANY reduced Jacobson ring with
    `Δ` a unit, `Equation P → Equation Q → Equation (dblAddXYZ P Q)`. Files:
    `AdditionLawField.lean` (field case via nonsingular_add + the six certificates),
    `AdditionLawOnCurve.lean` (maximal-ideal evaluation through
    `eq_zero_of_forall_isMaximal_mem`; `IsField`-parametrized to dodge the quotient
    instance-path whnf blowup — see the 217f7aba commit message). Consumers instantiate at
    the `E_U ×_U E_U` chart rings (reduced by 0e, Jacobson by f.t.-over-ℤ, Δ unit, chart
    points tautologically on the curves) — that one-line instantiation is c5β/0c-i work.
    Base-change naturality of law 2 (`map_dblAddXYZ`) landed alongside — 0c-iii's
    `mulModelHom_map` leg can reuse it.
  Element form: in
  the biprojective chart rings of `E_U ×_U E_U` (reduced by 0e; **Jacobson** — f.g. over
  `ℤ[a][Δ⁻¹]`), `F(dblAddX, dblAddY, dblAddZ)` vanishes because it vanishes at every field
  point (0f dictionary + mathlib `nonsingular_add`/`dblXYZ` specs) and closed points are
  dense with reduced stalks. Decls: `eq_zero_of_forall_residueField_eq_zero` (reduced
  Jacobson f.t. algebra) + per-chart vanishing. Skeleton decls land with
  `EllipticCurve/AdditionLaw.lean` (P1's next file; polynomial layer =
  `scripts/tw7-p1-bosma-lenstra`). **Depends**: 0e, 0f · Est. 150–300 lines · **NOTE**:
  L-ext is NOT the engine here (it proves morphism equality, not ideal membership).
  - **Progress** (coordinator-P1, 2026-07-07T14:49Z, dba3aa8c): the residue-field engine
    `eq_zero_of_forall_isMaximal_mem` (reduced Jacobson ring: in every maximal ideal ⟹ 0)
    is **PROVEN** in `AdditionLaw.lean`. Remaining: `IsJacobsonRing`/`IsReduced` instances
    for the `E_U ×_U E_U` chart rings (f.g. over `ℤ[a][Δ⁻¹]` — Jacobson by
    finite-type-over-Jacobson; reduced by 0e) + the per-chart vanishing statements.
  - **Progress** (coordinator-P1, 2026-07-07T20:09Z): **FIELD LAYER DONE** (91f9499e) —
    `EllipticCurve/AdditionLawField.lean`, zero sorries, axiom-clean:
    `equation_dblAddXYZ` ([Field F], Nonsingular P/Q ⟹ Equation (dblAddXYZ P Q)),
    certificate-free via mathlib's `nonsingular_add` + `add_of_equiv`/`add_of_not_equiv`
    and the dba3aa8c minors/diagonal (proportionality lemma
    `exists_eq_smul_of_cross_eq_zero`; helpers `Nonsingular.ne_zero`,
    `equation_zero_triple`, `dblAdd*_smul_left`). REMAINING for c5α: ring-level wiring —
    evaluate at maximal ideals of the biprojective chart rings (Jacobson: f.t. over ℤ via
    `isJacobsonRing_MvPolynomial_fin` + quotient; reduced: from 0e integrality, or the
    tensor-cone route via AdjoinRoot-monic freeness + `projective_polynomial_prime` over
    `Frac`) and feed `equation_dblAddXYZ` through `eq_zero_of_forall_isMaximal_mem`.
    Wiring architecture: tensor-cone `R[X₁..Z₂]/(F₁,F₂)` preferred over 4 chart rings
    (single statement; c5β localizes it).

- **[T-W7.0c-c5β]** bihomogeneous-triple → morphism template (NEW leaf, coordinator §2):
  `toProjOfBihomTriple` (new ForMathlib on the `ProjectiveSpaceChart` plumbing): where a
  (2,2)-triple generates the unit ideal on an open of `E_U ×_U E_U`, it defines a morphism
  to `ℙ²_U`; c5α's vanishing factors it through the closed subscheme `projModel W`
  (`ProjClosedImmersion` API). This is the actual content of `addOnZ`/`addOnY`
  (GLC:252–274). **Depends**: c5α (DONE) · Est. 200–400 lines.
  - **Status**: in_progress · **Claimed**: coordinator-P1, 2026-07-08T08:40Z ·
    **Execution decomposition** (cut at claim; tool names verified at the pin):
    - **β1** chart-product cover: cover `pullback (projModelπ W) (projModelπ W)` by the 9
      products of the `Proj.awayι` charts via `Scheme.Pullback.openCoverOfLeftRight` +
      `pullbackSpecIso` (Γ of the (i,j)-product ≅ chartRing i ⊗_R chartRing j, using the
      repo `chartQuotientEquiv`/`chartCoordEquiv` presentations).
    - **β2** dehomogenized triple + vanishing: the law-2 triple dehomogenized in the
      (i,j)-product ring (`dehomogenizeAux` kit, `ProjectiveSpaceChart.lean`); its curve
      equation vanishes by `equation_dblAddXYZ_of_isJacobsonRing` (c5α) — instances:
      IsReduced from 0e integrality via `IsIntegral.component_integral`; IsJacobsonRing
      from f.t.-over-ℤ (`isJacobsonRing_MvPolynomial_fin` + quotient through the
      chart presentations); Δ unit via `algebraMap`.
    - **β3** per-(i,j,k) affine piece: ring hom chartRing k →+* Localization.Away
      (triple_k on the (i,j)-product) by X_m/X_k ↦ triple_m/triple_k; well-defined into
      the quotient BY β2's vanishing; gives Spec-level maps into the k-chart of projModel.
    - **β4** glue: k-pieces agree on overlaps (the six dba3aa8c minors, localized);
      chart-product pieces agree (dehomogenization compatibility); glue via
      `Scheme.Cover.glueMorphisms` / open-cover ext.
    - **β5** package: `blOpenY := ` the triple's nonvanishing open; `addOnY := ` the glued
      morphism; `addOnY ≫ projModelπ = π-product` spec. Mirror for law 1 (`blOpenZ`,
      `addOnZ` — mathlib's addXYZ triple, same template; its on-curve input is
      equation_addXYZ via the SAME c5α theorem applied to law 1... requires the analogous
      field-level fact for addXYZ, which is `(nonsingular_add).left` + `add_of_not_equiv`
      — add `equation_addXYZ_of_isJacobsonRing` alongside, reusing the c5α engine).
  - **Progress** (coordinator-P1, 2026-07-08T08:20Z): **β5's law-1 prerequisite DONE**
    (68b33427) — `equation_addXYZ_of_isJacobsonRing` + field case + vector API
    (`addXYZ_self'`, smul/zero lemmas) in `AdditionLawOnCurve.lean`; zero sorries,
    axiom-clean. BOTH laws now have certificate-free on-curve theorems; the 422/584-term
    `cof_I1_*.txt` exports are retired. Remaining: β1–β4 (chart-product cover, per-chart
    triple + c5α instances, per-(i,j,k) ring homs, gluing) — the scheme-plumbing phase.
  - **Progress** (coordinator-P1, 2026-07-08T08:33Z): **β2 ring core DONE** (4eebfdee,
    `AdditionChartRing.lean`, zero sorries, axiom-clean) — presented chart/chart-product
    rings (`affineChartRing`/`biChartRing`, chartCoordEquiv-style), tautological points
    with BY-CONSTRUCTION curve equations (`eval₂_…` tautology lemmas), both law triples
    (`lawOneTriple`/`lawTwoTriple`) and their on-curve theorems under [IsReduced]
    [IsJacobsonRing] on the chart-product. REMAINING: β2b instances at the universal atlas
    (reduced: AdjoinRoot-monic freeness on Y/Z charts + `projective_polynomial_prime` over
    `Frac`, then localization-injectivity; Jacobson: rename-to-Fin-4 +
    `isJacobsonRing_MvPolynomial_fin` + quotient; note the X-chart cubic is NOT monic in
    either variable — the domain chain must run on the Y/Z charts only, which suffices by
    `chartY_sup_chartZ_eq_top` [P3's b3, landed]) · β1 Spec-identification (`pullbackSpecIso`
    + `chartCoordEquiv` + tensor↔4-variable-quotient iso) · β3 per-(i,j,k) ring homs ·
    β4 gluing.
  - **Progress** (coordinator-P1, 2026-07-08T09:12Z): **β2b LADDER DONE** (cfae244c,
    `AdditionChartLadder.lean`, zero sorries, axiom-clean) — `biChartRingEquiv :
    biChartRing W i j ≃ₐ[R] affineChartRing (W ⊗ chartRing_j) i` (three-step quotient
    transport; `quotientEquivQuotientMvPolynomial_symm_mk` proven as a missing-mathlib
    helper, upstream candidate) + `isDomain_biChartRing` (chart-product domain-ness
    REDUCED to single charts over enlarged bases) + Jacobson instances confirmed
    AUTOMATIC (`MvPolynomial.isJacobsonRing` Finite-ι + quotient; inferInstance test).
    β2b's remaining leaf is now exactly ONE statement: `IsDomain (affineChartRing W i)`
    for `i ∈ {1,2}` over a domain base (AdjoinRoot-monic freeness + field case via
    ProjIntegral + `IsIntegral.component_integral`, or reuse of PoleFiltration b1's
    `infChartQuotEquiv` machinery for the Y-chart).
  - **Progress** (coordinator-P1, 2026-07-08T10:29Z): **β2b(Z) DONE** (d38f52b9,
    `AdditionChartDomain.lean`, zero sorries, axiom-clean, NO sorryAx):
    `instIsDomainAffineChartRingZ` — the Z-chart ring IS mathlib's affine `CoordinateRing`
    (reusing P3's public `chartZAffineEquiv`), so mathlib's own `IsDomain` instance (its
    Frac-descent from `irreducible_polynomial`) discharges it — the freeness chain I had
    planned was NOT needed. Chained through the ladder: `instIsDomainBiChartRingZZ`.
    **PAYOFF LANDED**: `equation_lawTwoTriple_zz` / `equation_lawOneTriple_zz` — BOTH B–L
    laws land on the curve on the (Z,Z) chart-product over ANY Jacobson domain with Δ a
    unit (atlas qualifies: f.t. over ℤ + T-W7.0a). No certificate, no side conditions.
  - **ARCHITECTURE FINDING (supersedes the Y-chart leaf)**: do NOT grind
    `IsDomain (affineChartRing W 1)` algebraically. P2's `IsIntegral universalCurve`
    (PointsDictionary.lean:112, instance) + mathlib's `IsIntegral.component_integral`
    (Γ of any nonempty open of an integral scheme is a domain, an instance) give
    reducedness of EVERY chart-product ring for free — once β1 identifies
    `biChartRing W i j` with `Γ` of the (i,j) chart-product open of `E_U ×_U E_U`.
    So **β1 subsumes the Y-chart leaf**; the (Z,Z) result above stands as the
    independent, base-general statement (any Jacobson domain, not just the atlas).
    NEXT: β1 = `Spec (biChartRing W i j) ≅` chart-product open (via `pullbackSpecIso` +
    `chartCoordEquiv` + a tensor presentation of `biChartRing`; mathlib has
    `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` / `MvPolynomial.sumAlgEquiv`).
  - **β2b CLOSED** (coordinator-P1, 2026-07-08T10:52Z; 5b1f8da2 + 7c9ddc07, zero sorries,
    axiom-clean). The Y-chart DID fall to algebra — cheaper than the β1 route I flagged, so
    β1 no longer has to carry reducedness (it remains the right next step for β3, and its
    scheme-integrality argument stays available as an independent cross-check).
    · NEW ForMathlib (`MonicQuotientDescent.lean`, upstream candidates):
      `Polynomial.dvd_of_monic_of_map_dvd_map`; `AdjoinRoot.mapRingHom(_mk/_injective)` +
      `AdjoinRoot.isDomain_of_monic_of_map` (abstract form of the hand-rolled descent mathlib
      uses for `Affine.CoordinateRing`); `HomogeneousLocalization.isDomain_away` (the
      `IsDomain` sibling of `Proj.isReduced_away`).
    · `isDomain_affineChartRing_of_field` — over a field, EVERY chart ring is a domain
      (chartCoordEquiv + isDomain_away + `mk_X_ne_zero`).
    · `instIsDomainAffineChartRingY` — the Y-chart over ANY domain, by monic descent along
      `R[t] → Frac R[t]` through P3's `infChartQuotEquiv`/`infChartCubic_monic`
      (+ new `infChartCubic_map`). Z-chart: mathlib's `CoordinateRing` instance.
    · `instIsDomainBiChartRing{YY,YZ,ZY,ZZ}` — all four products of the COVERING charts
      (`chartY_sup_chartZ_eq_top`), via the ladder.
    · **`equation_lawTwoTriple_of_isDomain` / `equation_lawOneTriple_of_isDomain`** — BOTH
      B–L laws land on the curve on all four covering chart-products, over every Jacobson
      domain with Δ a unit (atlas qualifies). Corollaries `_zz`, `_yy`.
    NEXT (β1/β3): `Spec (biChartRing W i j)` ≅ the (i,j) chart-product open of the pullback
    (`pullbackSpecIso` + `chartCoordEquiv`); then the per-(i,j,k) ring homs
    `X_m/X_k ↦ triple_m/triple_k`, well-defined by the theorems above.
  - **β1 ALGEBRA CORE DONE** (coordinator-P1, 2026-07-08T10:31Z, fc670a51,
    `AdditionChartTensor.lean`, zero sorries, axiom-clean): `biChartRingTensorEquiv :
    biChartRing W i j ≃ₐ[R] affineChartRing W i ⊗[R] affineChartRing W j`, built directly by
    `AlgEquiv.ofAlgHom` (forward `aeval` on the two generator families; backward
    `Algebra.TensorProduct.lift` of the rename-and-quotient maps) — NOT by chasing extended
    ideals through `quotientTensorEquiv` (fewer moving parts; that chase is what made the
    ladder iterate). Key lemmas `toTensorAux_rename_inl/_inr` (⟹ simp lemmas
    `biChartRingTensorEquiv_mk_rename_inl/_inr`) are why the two curve relations die.
    REMAINING for β1: the scheme half — `Scheme.Pullback.openCoverOfLeftRight` over the
    `modelChartCover` + `pullbackSpecIso` gives `Γ` of the (i,j) chart-product open of
    `pullback (projModelπ W) (projModelπ W)` as `chartRing i ⊗[R] chartRing j`; compose with
    `biChartRingTensorEquiv.symm` + `chartCoordEquiv` to land the triples and their on-curve
    theorems on that `Γ`. Then β3.
  - **β1-scheme: route pinned + two obstacles found** (coordinator-P1, 2026-07-08T10:35Z;
    NO code yet — the iso would be a data-def and the DATA-SORRY register is frozen, so it is
    boarded rather than sorried):
    1. The cover piece is `pullback (awayι_i ≫ projModelπ) (awayι_j ≫ projModelπ)`; the repo's
       `awayι_projModelπ` (WeierstrassModel.lean:709) rewrites each leg as
       `Spec.map (ofHom ((algebraMap (quotientGrading _ 0) (Away …)).comp (gradeZeroRingEquiv W)))`.
       **Obstacle 1**: `pullbackSpecIso R S T` wants `[Algebra R S]` with `algebraMap` DEFEQ to that
       composite — so the R-algebra structure on `Away` must be introduced as a local instance
       `((algebraMap _ (Away …)).comp (gradeZeroRingEquiv W)).toAlgebra` (it does not exist as a
       global instance; the structure map factors through the degree-0 part).
    2. Transport `Away_i ⊗[R] Away_j → affineChartRing i ⊗[R] affineChartRing j` by
       `Algebra.TensorProduct.congr`. **Obstacle 2**: `chartCoordEquiv W i` is only a `≃+*`
       (`chartZAffineEquiv` is the sole `≃ₐ[R]`), so it needs an `AlgEquiv` upgrade
       (`AlgEquiv.ofRingEquiv` + a `commutes'` proof against the same `gradeZeroRingEquiv`
       factorization). Do this ONCE as `chartCoordAlgEquiv` — β3 needs it too.
    3. Then `Spec (of (biChartRing W i j)) ≅` the (i,j) piece, via `biChartRingTensorEquiv`
       (fc670a51), and `Scheme.Pullback.openCoverOfLeftRight (modelChartCover W) (modelChartCover W)`
       assembles the pieces into a cover of `E ×_R E`.
    Est. 150–250 lines. Everything below it (β3/β4) is unblocked by this one iso.
  - **β1 CLOSED** (coordinator-P1, 2026-07-08T10:54Z, bb5c86d9, `AdditionChartSpec.lean`,
    zero sorries, axiom-clean, no sorryAx — 111 lines, under the 150–250 estimate). BOTH
    boarded obstacles resolved exactly as the route of record predicted, and both were
    cheaper than feared:
    · Obstacle 1: `chartAwayAlgebra := ((algebraMap (grade 0) Away).comp (gradeZeroRingEquiv W))
      .toAlgebra`. With it `chartι_projModelπ` closes by `rw [awayι_projModelπ]` ALONE — the
      `toAlgebra` structure is DEFEQ to the composite that lemma produces, so `pullbackSpecIso`
      applies verbatim (no `RingHom.algebraMap_toAlgebra` massaging needed).
    · Obstacle 2: `chartCoordAlgEquiv := AlgEquiv.ofRingEquiv (chartCoordEquiv W i)` whose
      `commutes'` obligation is EXACTLY the repo's existing `chartCoordEquiv_mk_C`
      (WeierstrassModel.lean:586). Zero new math. Built once — **β3 should consume this**.
    · Deliverables: `chartPieceTensorIso`, `biChartRingAwayTensorEquiv`, **`chartPieceIso` :
      pullback (chartι i ≫ π) (chartι j ≫ π) ≅ Spec (biChartRing W i j)**, `chartProductCover`
      (`Scheme.Pullback.openCoverOfLeftRight` on `modelChartCover`).
    **β3 and β4 are unblocked.** The triples and their on-curve theorems (7c9ddc07) now read as
    regular functions on honest open subschemes of `E ×_R E`.
  - **UPSTREAM CANDIDATES from c5β** (for the forming upstreaming lane, per the D2 dispatch):
    · `ForMathlib/MonicQuotientDescent.lean` — `Polynomial.dvd_of_monic_of_map_dvd_map`;
      `AdjoinRoot.mapRingHom`/`_mk`/`_injective`/`isDomain_of_monic_of_map` (**upstreaming this
      would let mathlib SHORTEN an existing proof**: `Affine.CoordinateRing`'s `IsDomain`
      instance hand-rolls exactly this descent); `HomogeneousLocalization.isDomain_away`
      (the `IsDomain` sibling of mathlib-adjacent `Proj.isReduced_away`).
    · `AdditionChartLadder.lean` — `MvPolynomial.quotientEquivQuotientMvPolynomial_symm_mk`
      (a missing `symm`-apply lemma for an existing mathlib equiv).
    · `ForMathlib/HomogeneousEval.lean` — `MvPolynomial.IsHomogeneous.eval₂_mul_left` /
      `aeval_mul_left`: `eval₂ f (c * g ·) φ = c ^ n * eval₂ f g φ` for φ homogeneous of degree
      n. Mathlib has the homogeneity API and `eval₂_eq` but not the scaling lemma between them.
  - **β3 RING CORE DONE** (coordinator-P1, 2026-07-08T11:06Z, 345c75c9,
    `AdditionChartHom.lean`, zero sorries, axiom-clean): **an on-curve triple with an invertible
    k-th coordinate IS a chart morphism.**
    · `aeval_dehomogenizeAux_eq_zero` — the β3 identity, proven with NO per-chart computation:
      rescaling by `u` (`t k * u = 1`) makes the k-th entry `1`, so the dehomogenised value is
      the cubic at `(u * t ·)` = `u ^ 3 * (curve equation at t)` = 0, by the new homogeneity
      scaling lemma. (The per-chart `linear_combination` route I first sketched is unnecessary.)
    · `chartHomOfTriple : affineChartRing W k →ₐ[R] S` (X m / X k ↦ t m * u) + `_coord` simp;
      `chartAwayHomOfTriple` — the same into the model's `Away` chart ring via β1's
      `chartCoordAlgEquiv` (the form `Proj.awayι` consumes; β1's build-once paid off here).
    REMAINING in β3: instantiate `S := Localization.Away (lawTwoTriple W i j k)` over
    `biChartRing W i j` (on-curve hypothesis = `equation_lawTwoTriple_of_isDomain`, 7c9ddc07),
    and the basicOpen covering of the (i,j) piece by the three `t_k`-loci. Then β4 (gluing via
    the six certified minors) and the four `GroupLawConstruction.lean` sorries.
    Engineering note for whoever continues: state `hstep`/`hscale` as explicit `have`s with the
    beta-redex shape before `rw` — unifying the homogeneity lemma against a beta-reduced goal
    whnf-blows-up (200k heartbeats) on these terms.
  - **β3 DONE** (coordinator-P1, 2026-07-08T11:24Z; d7bda67d + f1dd27ad + 7ba4314e; all
    zero-sorry, axiom-clean; `AdditionChartAway/Mor/Cover.lean`):
    · `addOnYPieceHom` / `addOnZPieceHom` — ring level, `chartAway W k →ₐ[R]
      Localization.Away (law{Two,One}Triple W i j k)`. BOTH hypotheses arrive free: on-curve =
      β2b's `equation_law*Triple_of_isDomain`; invertibility = the localization's `invSelf`.
    · `addOnYPieceMor` / `addOnZPieceMor` — SCHEME level, `Spec (Localization.Away t_k) ⟶
      projModel W`, with over-R specs `pieceMor ≫ projModelπ = Spec.map (algebraMap R _)`
      (free from β1's `chartι_projModelπ` + `AlgHom.comp_algebraMap`).
    · `regularityOpen t := ⨆ k, D(t k)` + `regularityOpen_eq_top_iff` +
      **`regularityOpen_ne_top_of_forall_mem`** — the formal statement of *why two laws are
      needed*: a triple with a common zero (an exceptional-divisor point, which every (2,2) law
      has by B–L Thm 1) does not cover the chart-product. Law 2's regularityOpen on the (i,j)
      piece IS that piece's contribution to `blOpenY`; law 1's, to `blOpenZ`.
    ANTIDOTE (banked): `.toProjective` blocks the syntactic `rw [WeierstrassCurve.map_map]` —
    apply the curve equality with `▸` instead (`equation_awayTriple`).
    NEXT = **β4**: (a) the k-pieces agree on `D(t_k) ⊓ D(t_l)` — this is where the six certified
    minors (dba3aa8c) finally get consumed; (b) the (i,j)-pieces agree (dehomogenisation
    compat); (c) assemble `blOpenY`/`blOpenZ` + `addOnY`/`addOnZ`, then the four
    `GroupLawConstruction.lean` sorries. Will FLAG before claiming 0c-ii (per v10.18/v10.22).

- **[CLEANUP-GLC-1]** `/cleanup` GroupLawConstruction.lean. **Depends**: T-W7.0c-i (3rd proof
  ticket on file). Blocks later GLC tickets.

- **[T-W7.0c-ii]** cover, agreement, glue — `blOpen_cover`, `addOn_agree`, `mulModelHom`,
  `blOpenZ_ι_mulModelHom`, `blOpenY_ι_mulModelHom`, `mulModelHom_π`
  (GroupLawConstruction.lean:118–154).
  - **Status**: blocked · **Depends**: T-W7.0c-i, CLEANUP-GLC-1 · **Type**: 2 lemmas + def +
    3 specs
  - Sketch: cover fibrewise via B–L Thm 2 (`O ∉ {Y=0}`; `F(1,0,0) = −1`); agreement as
    2×2-minor identities mod the curve relations — `linear_combination` with precomputed
    cofactors, per-coordinate, NO maxHeartbeats; glue two-open. Leaves **L-0c2/0c3/0c4/0d**.

- **[T-W7.0c-iii]** the points spec + base-change naturality — `mulModelHom_specPoints`,
  `mulModelHom_map` (GroupLawConstruction.lean:≈167,180).
  - **Status**: blocked · **Depends**: T-W7.0c-ii, T-W7.0f · **Type**: 2 lemmas
  - Sketch: secant-open case = §5 vs mathlib `slope/addX/addY` identity; remaining
    configurations via the Y-law + neg/zero specs (field-side case split, legitimate —
    `[DecidableEq K]` instance-arg); naturality per piece by `Proj.map`-functoriality
    (`projModelBaseChange` pattern, PROVEN) + opens base-change. Leaves **L-0c6/L-0cnat**.

- **[T-W7.0g]** the group axioms over every ring — `mulOver`/`oneOver`/`invOver` (+`_left`
  pins), `mulOver_assoc`, `oneOver_mulOver`, `mulOver_oneOver`, `mulOver_comm`,
  `invOver_mulOver` (GroupLawConstruction.lean:≈200–253).
  - **Status**: partially done (inv/identity half) · **Claimed**: beastmode-B (lane P0),
    2026-07-08. **DONE (axiom-clean, in HEAD)**: `invOver` (`= Over.homMk (negModelHom W)
    negModelHom_π`), `invOver_left` (`rfl`), `oneOver` (`= Over.homMk ((𝟙_).hom ≫ projModelZero W)`
    via `projModelZero_projModelπ`; obligation needs a `show` to reduce `(modelOver W).hom →
    projModelπ W` — the `modelOver` abbrev stays folded under `instances` transparency so a bare
    `rw` misses it), `oneOver_left` (`rfl`). These build ONLY on the finished P0 pieces
    (`negModelHom`/`_π`, `projModelZero_projModelπ`), independent of the blocked mul side.
    **STILL BLOCKED** (needs `mulModelHom` from 0c-ii/iii): `mulOver`, `mulOver_left`,
    `mulOver_assoc`, `oneOver_mulOver`, `mulOver_oneOver`, `mulOver_comm`, `invOver_mulOver`.
    · **Depends**: T-W7.0c-iii, T-W7.0e, T-W7.0a · **Type**: 3 defs + 8 lemmas
  - Sketch: universal case by `hom_ext_of_forall_specPoint` + reducedness instances +
    specPoints lemmas + mathlib `Point.instAddCommGroup` over `κ`; general `R` by
    instantiating `mulModelHom_map` along `classifyRingHom` (+ one-liner unit/inv
    naturality from `projModelZero_baseChange`). Leaf **L-0g**.

- **[CLEANUP-GLC-2]** `/cleanup` GroupLawConstruction.lean. **Depends**: T-W7.0g (6th proof
  ticket on file).

- **[T-W7.0h]** global VC-equivariance — `mulModelHom_vc` (GroupLawConstruction.lean:≈265).
  - **Status**: blocked · **Depends**: T-W7.0c-ii, T-W7.mvc, CLEANUP-GLC-2 · **Type**: lemma
  - Sketch: field-points ext over the universal VC-base (domain) + the affine cocycle ⓟ at
    points; instantiate. Leaf **L-0h**.

- **[CLEANUP-GLC-3]** final `/cleanup` GroupLawConstruction.lean. **Depends**: T-W7.0h.

- **[T-W7.0i-a]** pole filtration + freeness — `poleOrderFiltration` + `_one`, `_two`,
  `_three`, `_mul_le`, `linearIndependent_one_coordX_coordY`
  (PoleFiltration.lean:41–75; `coordX`/`coordY` already real).
  - **Status**: done · **Claimed**: beastmode-A, 2026-07-07T~12:30Z (retrofit)
  - **Progress**: 2026-07-07: ALL SIX LEAVES + helper PROVEN, axiom-clean (propext/choice/quot
    only), `lake build` green. Def = R-span of pole-order-bounded monomials {x^i : 2i ≤ n} ∪
    {x^i y : 2i+3 ≤ n} (KM-Weierstrass-sections form; the intrinsic ideal-sheaf characterization
    is the 1b-side bridge, spawn there if needed). New helper `coordY_mul_coordY` (the Weierstrass
    relation solved for y², algebraMap-mult form) — proven via AdjoinRoot.mk_self + index-preserving
    expansion + linear_combination; feeds _mul_le case (x^i y)(x^k y). linearIndependent via
    mathlib `smul_basis_eq_zero` + R→R[X] tower-cast + coefficient extraction. NOTE for
    CLEANUP-PF: interval_cases lacked bounds (omega-obtain used); Phase-6.5 per-decl cleanup
    deferred into CLEANUP-PF (same file, next ticket 0i-b builds directly on it — recorded
    deviation). · **File**: EllipticCurve/PoleFiltration.lean · **Depends**:
    none · **Parallel**: yes · **Type**: def + 5 lemmas
  - Sketch: define `F n` via the section ideal `(s)` on `D(u)` (`t = s³u`); normal-form
    basis one-element-per-pole-order (mathlib `Affine.CoordinateRing` freeness; `B`
    monic-in-`s` free over `R[t]`); all Δ-free. Leaf **L-P3** (part 1).

- **[T-W7.0i-b]** global sections + scheme density + pushforward —
  `projModel_globalSections_eq_baseRing`, `infChart_s_nonZeroDivisor`,
  `projModel_hom_ext_of_affine`, `locallyWeierstrass_pushforward_O_eq_O`
  (PoleFiltration.lean:85–117).
  - **Status**: done (all children b1/b2/b3/b4 + i3/i5 landed axiom-clean; parent label flipped per coordinator v10.1 GO, beastmode-A 2026-07-08) ·
    **Depends**: T-W7.0i-a (done), T-W7.0i-b1 (done), b2 (done), b3/b4 (skeleton pending —
    coordinator §2) · **Type**: 4 lemmas
  - **Progress** (2026-07-07, session cont.): **2 of 4 leaves FULLY PROVEN, axiom-clean**:
    `infChart_s_nonZeroDivisor` (transport along the b1 bridge) and
    `projModel_hom_ext_of_affine` — the latter END-TO-END: general
    `spec_hom_ext_of_nonZeroDivisor` (equalizer-closed-immersion + appTop-injectivity ending,
    any `IsLocalization.Away` presentation) + mathlib Proj overlap API
    (`SpecMap_awayMap_awayι`, `Away.isLocalization_mul`) + per-chart ζ-nzd
    (`chart_isLocalizationElem_nonZeroDivisor`: j=0 via NEW z-outer chart-0 bridge
    `zChartQuotEquiv` + coeff-0 = −1 unit trick; j=1 via infChart t-transport with
    subsingleton split; j=2 via isLocalizationElem-self = 1). Recurrent poison + antidotes
    logged: fin_cases literal skew → omega-obtain; rw-in-big-motive → term-calc
    calc/▸/congrArg; AlgEquiv-coe → `show`-recast at wrapper def. REMAINING: i3 `Γ ≅ R`
    (b3 scheme plumbing + b4 equalizer core) and i5 pushforward.
  - **Progress**: 2026-07-07: execution decomposition — spawned b1–b4 (Tier A2/A4). SKEW
    FOUND: `hom_ext_of_affine` consumes the *t*-coordinate (and chart-0 *z*-) nonzerodivisor,
    not the skeleton's s-version (which serves 1b's filtration side; kept, still true). Both
    proved by the mod-variable two-step (kill by constant-unit/monic leading coefficient), or
    via the b2 basis.

- **[T-W7.0i-b1]** chart-ring bridge — explicit `infChartPoly` (= dehomogenizeAux at Y of the
  projective cubic, computed: `t + a₁st + a₃t² − s³ − a₂s²t − a₄st² − a₆t³`) + alg-equiv of the
  Y-chart quotient to `AdjoinRoot` of the monic-in-`s` cubic over `R[t]`.
  - **Status**: done (committed 4c89b0c5; board flipped 2026-07-07T14:01Z per coordinator 1a) · **File**: PoleFiltration.lean · **Parent**:
    T-W7.0i-b · **Depends**: none · **Type**: def + equiv + 2 lemmas
  - Sketch: subtype-index ≃ Fin 2; `finSuccEquiv` + Fin-1 ≃ `Polynomial R`; transport the
    span along `Ideal.quotientEquivAlg` (pattern: repo `chartCoordEquiv`). Monicity: leading
    s-coefficient −1 (unit).

- **[T-W7.0i-b2]** basis and nonzerodivisors — `Basis (Fin 3) R[t]` of the AdjoinRoot
  (`AdjoinRoot.powerBasis'`, monic) + `s`-nzd (basis matrix triangularity + McCoy) + `t`-nzd
  (scalar on a free module) + chart-0 `z`-nzd (constant term −1 unit trick).
  - **Status**: done (with b1; beastmode-A 2026-07-07) · **Parent**: T-W7.0i-b · **Depends**:
    T-W7.0i-b1 (done) · **Type**: 4 lemmas
  - **Progress**: b1+b2 PROVEN, build green: `infChartS/T`, `dehomogenizeAux_projective_polynomial`
    (explicit chart cubic), `infChartCubic` (+`_monic` via `monicity!`, `_natDegree` — needs
    honest `[Nontrivial R]`), `infChartPolyEquiv` (+ generator/`dehomogenize` computation; the
    `uniqueAlgEquiv` route, universe-safe), `infChartQuotEquiv` (≃ₐ via `quotientEquivAlg`;
    coe-path fixed by `→+*`-ascribed `show`), general `adjoinRoot_root_mem_nonZeroDivisors`
    (mod-X two-step; ForMathlib-grade), `infChartBasis` (`Module.Basis` — mathlib renamed!),
    `infChart_algebraMap_mem_nonZeroDivisors`, `infChart_t_mem_nonZeroDivisors`,
    `infChart_root_mem_nonZeroDivisors` (s-nzd; `mem_nonzeroDivisors_of_coeff_mem` = McCoy
    corollary, found in mathlib). NOTE: chart-0 z-nzd deferred until hom_ext's cover choice
    fixes whether chart-0 is needed (2-chart route may suffice).

- **[T-W7.0i·i5]** — **DONE (beastmode-A 2026-07-07; axiom-clean)**:
  `locallyWeierstrass_pushforward_O_eq_O` PROVEN: `IsIso (G.π.app U)` for every open `U`
  of every locally-Weierstrass family — `O_S ≅ π_*O_E` as sheaves. Route:
  `locallyWeierstrass_app_affine_isIso` (affine V inside a trivializing chart: (π∣_V) is a
  pullback of the chart pullback along `S.homOfLE` via `isPullback_morphismRestrict` +
  `of_right'`; isoSpec/appLE bridge at the identity; transport along `e` and
  `isPullback_projModelBaseChange` to `projModel (W.map ρ)`; `appTop` iso by i3; exit
  `morphismRestrict_appTop`), then stalkwise assembly: `π.c` packaged as a sheaf morphism,
  `app_isIso_of_stalkFunctor_map_iso`, germ-level bijectivity from the affine basis
  (exists_germ_eq/germ_eq/germ_res_apply + c-naturality elementwise).
  **T-W7.0i IS COMPLETE — PoleFiltration.lean is sorry-free (2660+ lines).**

- **[T-W7.0i·i3]** — **DONE (beastmode-A 2026-07-07; axiom-clean)**:
  `projModel_globalSections_eq_baseRing` PROVEN for every commutative ring `R`. Route:
  bijectivity of `ΓSpecIso.inv ≫ π.appTop`. Injectivity: Y-chart + grade-zero readoff +
  `algebraMap_adjoinRoot_injective` (basis index-0). Surjectivity: two-chart transports
  (`chartY/ZRingEquiv` of the `basicOpenIsoAway.inv`-images), overlap agreement
  (`chart_transports_agree` via `awayIso_res_squareY/Z` from `Proj.awayMap_awayToSection` +
  `overlapLocEquiv` transport with compat-i (`ringEquivOfRingEquiv_eq`) and compat-ii
  (`overlapLocEquiv_awayMap_z` by `chart_hom_aeval` on generators + `overlapMap` pins)),
  then `overlap_pair_eq_baseRing` produces the constant and
  `sections_ext` (`eq_of_locally_eq₂`) + `structure_section_square`(_apply) +
  `awayToSection_inv_cancelY/Z` glue `Φ r = s`. All heavy `rw`s replaced by
  `congrArg`-term chains (motive-search on the graded types times out otherwise);
  the `Γ`-bridge `Proj_awayι_appTop_ΓSpecIso` is stated generically over any
  `GradedAlgebra` (ForMathlib-grade).

- **[T-W7.0i-b3]** two-chart Γ plumbing — SKELETON LANDED 2026-07-07T14:15Z per coordinator §2:
  `chartY_sup_chartZ_eq_top`, `chartYSectionsEquiv`, `chartZSectionsEquiv`
  (PoleFiltration.lean; overlap-sections equiv folded into b4's `overlapMap` route);
  `objSupIsoProdEqLocus` remains the discharge tool for i3's assembly.
  - **Status**: done (beastmode-A 2026-07-07; axiom-clean) · **Claimed**: beastmode-A,
    2026-07-07T06:55Z · **Parent**: T-W7.0i-b · **Depends**: T-W7.0i-b1 (done) ·
    **Type**: 3 decls + assembly
  - **Progress**: all 3 PROVEN. `chartY_sup_chartZ_eq_top`: prime containing mk X₁ and
    mk X₂ contains mk X₀³ (explicit Weierstrass grouping) hence mk X₀ hence the
    irrelevant ideal — contradicts relevance; opensRange via show-recast to `awayι` +
    `Proj.opensRange_awayι` (instance-transparency-safe). `chartSectionsIso` (new
    private): Γ(model, chart-range) ≅ chart ring by `image_top_eq_opensRange` eqToIso +
    `appIso ⊤` + `ΓSpecIso`. `chartY/ZSectionsEquiv` := that ∘ `chartCoordEquiv.symm`.

- **[T-W7.0i-b4]** the algebraic equalizer core — SKELETON LANDED 2026-07-07T14:15Z per coordinator §2:
  `chartZAffineEquiv` (Z-chart ≃ mathlib CoordinateRing), `overlapMap` (x ↦ s/t, y ↦ 1/t)
  + `overlapMap_coordX`/`_coordY` pins, `overlap_pair_eq_baseRing` (the equalizer heart;
  shared-witness ∃∧ documented). The A_y normal-form-basis leaf lives INSIDE
  `overlap_pair_eq_baseRing`'s proof plan (free bases from 0i-a/b2 + the x²y⁻¹ exclusion).
  - **Status**: done (beastmode-A 2026-07-07; commits c7202f94, 2d6af093, 812afe60,
    d34ef42d, + endgame) · **Claimed**: beastmode-A, 2026-07-07T05:00Z · **Parent**:
    T-W7.0i-b · **Depends**: T-W7.0i-a (done), T-W7.0i-b1 (done), T-W7.0i-b2 (done) ·
    **Type**: 2 defs + 3 theorems
  - **Progress**: ALL PROVEN, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`):
    `overlap_eval₂_polynomial` (mk-normalization + `linear_combination -t⁷·hrel` after a
    timed-out algebraMap-calc route was replaced), `overlapMap` + `_coordX`/`_coordY`,
    `chartZAffineEquiv` (via new affChart bridge: `affChartX/Y`,
    `dehomogenizeAux_two_projective_polynomial`, `affChartPolyEquiv` + X-pins +
    `_dehomogenize` — exact sign match, no negation), and `overlap_pair_eq_baseRing` via
    the **sPowCoord coordinate tower**: `sCubeCoord₀/₁/₂` (t-divisible), `sPowCoord`
    3-term recursion + `root_pow_eq`, K1 T-adic lower bounds (slotwise conjunction
    induction, `X_pow_dvd_sPowCoord` + coeff form), K2 leading-coefficient-exactly-1
    (`sPowCoord_sub_lead_aux`), `coordOf` cleared coordinates + cross-kill + leading-slot
    lemmas, `cleared_term`/`pow_mul_mul_overlapInvT` clearing, `overlap_coordOf_eq`
    (t^N-clearing + `IsLocalization.injective` + free-basis comparison), then the
    parity-gap endgame (2·deg p vs 2·deg q + 3 never equal ⟹ q = 0 ⟹ deg p = 0 ⟹
    shared constant; the x²y⁻¹ exclusion is exactly the odd-slot kill). The A_y
    normal-form leaf discharged in-proof as planned.
  - Sketch: 2-chart equalizer (`x²y⁻¹` excluded = the `H¹` witness); universality BY
    INSTANTIATION (never base-change the proof); McCoy for `s`-nonzerodivisor; sheafify
    over chart opens via `isPullback_projModelBaseChange` ⓟ. Leaf **L-P3** (part 2).

- **[CLEANUP-PF]** final `/cleanup` PoleFiltration.lean. **Depends**: T-W7.0i-b.

- **[T-W7.mvc]** variable-change model isos — `projModelVCIso` + `_π`, `_zero`, `_mul`,
  `_map` (ModelVariableChange.lean:34–58).
  - **Status**: **DONE** (lane P5, 2026-07-07) — **`projModelVCIso` + `_π` + `_map` + `_mul`
    + `_zero` ALL PROVED, axiom-clean** (`[propext, Classical.choice, Quot.sound]`).
    `_mul` (cocycle, bb51832c) via `vcMvSubst_mul`/`aeval_vcMvSubst_mul` + the shared HEq
    transport; `_zero` (pointedness, abd89c16) via a NEW unit-rescaling automorphism
    `allScaleGradedQuot` (generalises GLC's `−1` `allNeg` to a unit `μ = u³`): `Proj.map` of
    it is `𝟙` by `Proj.map_degScaling_eq_id`, and `projModelZeroEval_vc_eq_allScale`
    (both sides = eval at `(0,u³,0)`) + `fromOfGlobalSections_map` naturality assemble it,
    exactly mirroring `negModelHom_zero`. Remaining file sorries are T-W7.1b (separate lane).
    **Progress 2026-07-07**: crux+graded-hom
    layer (66300bb4) → `projModelVCIso` iso via `Proj.map`(C)/`Proj.map`(C⁻¹) + `Proj_map_congr`
    (064b040c) → `_π` via `map_comp_toSpecZero`+`vcGradedHom_algebraMapGradeZero` (0efff5f2) →
    `_map` (coordinator §2-P5) via a novel eqToHom-transport route: `projMap_transport_heq`
    (HEq bridge, `subst`) + `gradedHom_heq` + `mk_heq` + `map_aeval_vcMvSubst`
    (`map f ∘ aeval σ_C = aeval σ_{C.map f} ∘ map f`) + `vcMvSubst_map`. Inverse graded hom
    reuses ALL C-infra via `C⁻¹` (clean types by `inv_smul_smul` at the ideal level). ·
    **Claimed**: lane-P5 (beastmode), 2026-07-07T14:04Z (claimed BEFORE skeleton edit — rule 5) ·
    **File**: EllipticCurve/ModelVariableChange.lean ·
    **Depends**: none · **Parallel**: yes · **Type**: def + 4 lemmas
  - Sketch: graded hom of the linear substitution (`baseChangeGradedHom` template) — the
    homogenized `ivcX`/`ivcY` substitution `X↦u²X+rZ, Y↦u³Y+su²X+tZ, Z↦Z` (each generator
    degree-1 ⟹ graded via `MvPolynomial.IsHomogeneous.aeval`); crux polynomial identity
    `aeval σ_C poly_W = u⁶·poly_{C•W}` (clears via `variableChange_aᵢ` + `↑u·↑u⁻¹=1`);
    then `quotientGradingMap` + `Proj.map`, iso via `Proj.map_comp`/`map_id` on `C`/`C⁻¹`;
    cocycle via `eqToHom (mul_smul …)`; affine side from the ⓟ cocycle. Leaf **L-0h**
    (iso half). **coordinator §2-P5**: `projModelVCIso_map` (base-change naturality) added
    to the leaf — 0h's transport along `classifyRingHom` needs it.
    **Progress 2026-07-08 (beastmode-A, b2-γ geometric layer COMPLETE)**: b1 done (`pointedIsoCoordEquiv`, ba35c165 lineage); b2 intrinsic criterion + local-global principle done (PoleFiltration sorry-free); THIS CYCLE the full per-maximal transport toolkit landed: chartPointOf package (fromSpec point of a section prime + `chartPointOf_mem_basicOpen_iff`, efd754cb), aug = zeroChartHom (INC-3c), `Proj_fromSpec_awayToSection_awayι` bridge + overlap = `X.basicOpen`(t-section) (52c34fa5), ε-transport `pointedIsoChartTransport` + unit-aug neighbourhoods (266479a6), overlap-equation transport `pointedIso_overlap_sections_equation` (ba35c165, d-generalized), sections dictionary `overlapSectionsEquiv_res_chartY/Z`, zero-appLE values at ⊤ and basic opens (cf37d856, d30790fb), hez-appLE square via opaque-generic `appLE_appLE_of_comp_eq` (76a38884), **the F4 vanishing** `pointedIsoChartTransport_mem_span_of_aug_eq_zero` (872c7735: transports of ker-aug′ land in (s,t)-localized), division enablers aug(U)=1 + root-nzd-localized (0ecc16fe), mirror prep pointedIso_hez/heπ_symm + roundtrip `app_app_res_of_comp_eq_id` (c1cf9b77). REMAINING for b2: divisions assembly (τ=wσ, mirror ŝ=Θσ, α-unit via s-nzd), per-P witness pull-back to B, δ-assembly — the sentinel `.mathlib-quality/beastmode_active.beastmode-A` has the exact 7-step pipeline + all antidotes (per-decl heartbeat budget → split aux decls; kernel timeouts → opaque-variable generics; forward congrArg chains only). **Progress 2026-07-08+ (beastmode-A): b2 COMPLETE, AXIOM-CLEAN** — `pointedIsoCoordEquiv_filtration` proven (commit lineage through 82e334f9 the per-prime witness, 5c39a14c forward inclusion, composite identities, le_antisymm assembly; #print axioms = [propext, Classical.choice, Quot.sound]). Remaining leaves b3x/b3y/main/b5 (4 sorries) dispatched to parallel lane (dev/modular-curves-b3).
    **Integrator de-risk 2026-07-08 (beastmode-A)**: merge path CONFIRMED CLEAN. P3b3's `ComparisonCoefficients.lean` hypothesis `hfil : ∀ n, Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' n) = poleOrderFiltration W n` is discharged verbatim by `fun n => pointedIsoCoordEquiv_filtration e heπ hez n` at `Φ := pointedIsoCoordEquiv e heπ hez` (source/target order W'→W matches; both sides `≃ₐ[R]`). Full b2 spine re-certified `sorryAx`-free (#print axioms = [propext, Classical.choice, Quot.sound] on: pointedIsoCoordEquiv_filtration, pointedIso_exists_witness, exists_basicOpen_transport_root_unit_mul, exists_basicOpen_root_mem_span_transport, pointedIsoChartTransport_mem_span_of_aug_eq_zero, pointedIsoCoordEquiv_filtration_le). Wire-step (when P3b3 merges): instantiate their 4 general wrappers with that hfil to fill b3x/b3y/main/b5 sorries; then full-file axiom sweep + board close.
    **INTEGRATION 2026-07-08 (beastmode-A, PR #5220 MERGED into dev/modular-curves): 3/4 LEAVES DONE, main PENDING.** Merged P3b3's ComparisonCoefficients/Bridge/Injective (they import ModelVariableChange, so the 4 ticketed leaves are discharged in a NEW capstone `EllipticCurve/Comparison.lean` above the stack; statements relocated verbatim; registered in root). WIRED axiom-clean: `pointedIsoCoordEquiv_coordX`/`_coordY` (via `exists_coord{X,Y}_image_of_filtration` + `hfil := pointedIsoCoordEquiv_filtration`), `projModelVCIso_injective` (via `projModelVCIso_injective'`). ModelVariableChange now sorry-free. **GAP — `pointedIso_exists_variableChange` (main) still `sorry`:** PR #5220's "main" (`exists_variableChange_of_filtration`) delivers the COORDINATE-equation form (∃C, C•W'=W ∧ Φx'=u²x+r ∧ Φy'=…), NOT the ticketed MODEL-MORPHISM form (e.hom = eqToHom ≫ projModelVCIso C W'). Bridging them needs a FAITHFULNESS lemma NOT in the PR: `pointedIsoCoordEquiv` injective on morphisms. Precise reduction (scoped, beastmode-A): coordEquiv-equal → (cancel fixed chart isos in the b1 def) `pointedIsoΓ`-equal → (cancel the presheaf.mapIso) target-Z'-chart `e.hom.app`-equal → (the crux, scheme-level: Spec-from-affine factors through the Z'-chart, `Spec` faithful) `chartZ_W ≫ e.hom` agree → `projModel_hom_ext_of_affine`. Bounded (~2 cancel lemmas + 1 scheme-faithfulness + the bridge-transport of pointedIsoCoordEquiv(VCIso)), but a real sub-development, ~in P3b3's b1/pointedIsoΓ wheelhouse. T-W7.1b NOT flipped DONE; T-W7.12's 1b dep stays. Awaiting coordinator routing (beastmode-A can write faithfulness as follow-on, or P3b3).

- **[T-W7.1b]** THE comparison theorem — `pointedIso_exists_variableChange`,
  `projModelVCIso_injective`; **sub-decls SKELETONIZED 2026-07-07T14:15Z per coordinator §2**:
  `pointedIsoCoordEquiv` (b1), `pointedIsoCoordEquiv_filtration` (b2 + the
  INTRINSIC-FILTRATION BRIDGE — gates all of 1b; the landed monomial-span filtration is not
  iso-invariant for free), `pointedIsoCoordEquiv_coordX`/`_coordY` (b3, several hundred
  lines, shared-witness ∃-bundles documented). Source status: DESIGN-DERIVED (decomposition.md
  addendum) — no verbatim KM/formulaire quote available (image-only scans).
  - **Status**: in_progress · **Claimed**: beastmode-A, 2026-07-07T12:55Z ·
    **Depends**: T-W7.0i-a (done), T-W7.0i-b (**DONE** beastmode-A 2026-07-07 —
    PoleFiltration.lean is sorry-free incl. `locallyWeierstrass_pushforward_O_eq_O`),
    T-W7.mvc (**DONE** 2026-07-07 lane-P5) · **Type**: def + 5 theorems
  - **Blocker note (P5, 2026-07-07)**: T-W7.mvc unblocked, but b2 `pointedIsoCoordEquiv_filtration`
    (the intrinsic-filtration bridge) GATES all 6 leaves and needs the pole-filtration theory
    from T-W7.0i-b (stream-W, beastmode-A's lane — DON'T cross). `projModelVCIso_injective` is
    NOT dischargeable from T-W7.mvc alone: `Proj.map` is not injective (the new `allScale_map_id`
    exhibits nontrivial graded homs → `𝟙`, the projective unit-scaling ambiguity), so it needs the
    affine coordinate ring from b1. Skeletons live in ModelVariableChange.lean:~641-712; resume
    once beastmode-A lands T-W7.0i-b.
  - Sketch: pointed iso preserves `E∖O` (Z-chart) ⟹ ring iso `Φ`; `Φ(F'_n) = F_n`
    (intrinsic via section ideal); `F₂`/`F₃` freeness forces `x' ↦ αx+β`, `y' ↦ γy+δx+ε`,
    units; relations force `α³ = γ²`, `u := γ/α`; extend by `projModel_hom_ext_of_affine`.
    Leaf **L-1b** (prior-B2 fix-option-3, BB-RR-free). Shared-witness `∃` documented.
  - **CLAIM (beastmode-P3b3, 2026-07-08)**: sub-leaves **b3x** (`pointedIsoCoordEquiv_coordX`),
    **b3y** (`pointedIsoCoordEquiv_coordY`), **main** (`pointedIso_exists_variableChange`),
    **b5** (`projModelVCIso_injective`). Work in NEW file
    `EllipticCurve/ComparisonCoefficients.lean` as hypothesis-parameterized versions taking the
    b2 conclusion `hfil` as an argument (b5 is hfil-independent). Isolated worktree
    `../aintlib-mc-b3` (branch `dev/modular-curves-b3`), PR back to `dev/modular-curves` when
    green. **NOT claiming b2** (`pointedIsoCoordEquiv_filtration`, in flight on beastmode-A) —
    final wiring of the four sorries in ModelVariableChange.lean deferred until b2 flips done.
  - **PROGRESS (beastmode-P3b3, 2026-07-08)**: **b3x/b3y DONE** — `exists_coordX_image`,
    `exists_coordY_image` cores + general-base wrappers `exists_coordX_image_of_filtration`,
    `exists_coordY_image_of_filtration` (subsingleton split), axiom-clean (`ComparisonCoefficients.lean`,
    commits 29cf027d + a39be9b7). **main-alg DONE** — `exists_variableChange_of_filtration`: builds
    `C : VariableChange R` with `C•W'=W` + coordinate relations, via `six_ext` (R[X]-basis
    coefficient extraction) + `α³=γ²` ⇒ `u:=γ/α` + `variableChange_aᵢ` unit-cancellation
    certificates, axiom-clean (commit cb948d3d). **BRIDGE DONE** (was a *missing* sub-lemma, not
    "b1 proven" as the sketch assumed) — NEW file `ComparisonBridge.lean`: `bridge_coordX`/
    `bridge_coordY` compute `pointedIsoCoordEquiv (projModelVCIso C W)` explicitly (= the
    `x↦u²x'+r, y↦u³y'+su²x'+t` affine variable change) via `pointedIsoCoordEquiv_sections` +
    `Away.map (vcGradedHom)` + `chartZRingEquiv_x/_y` + AwayCongr transport, axiom-clean (commit
    809f4616). **b5 DONE** — NEW file `ComparisonInjective.lean`: `projModelVCIso_injective'`
    (hfil-independent) from the bridge + `coordXY_ext` + unit arithmetic (`IsUnit.mul_left_inj`
    cancels `↑u²`), axiom-clean (commit 67c9feab). The eqToHom-transport of `pointedIsoCoordEquiv`
    across the curve equality is proven poison-free by `transport_general` stated with the two
    models as FREE variables (so `subst` collapses the equality) + `coordRingCongr_refl_apply`
    applied to an OPAQUE element via `rw` (NOT `simp` — simp's congruence motive whnf's the huge
    carrier = the kernel timeout) + `pointedIsoCoordEquiv_congr` on the now-opaque isos; the
    theorem instantiates the concrete isos by pure function application, so nothing large is
    re-checked. **ALL FOUR SECOND-HALF LEAVES (b3x/b3y/main/b5) DONE, axiom-clean, in PR #5220.**
    Final wiring of the four ModelVariableChange.lean sorries deferred until b2
    (`pointedIsoCoordEquiv_filtration`, beastmode-A) lands — `projModelVCIso_injective` is then a
    one-line `exact projModelVCIso_injective' …`; the other three need b2's `hfil`.

- **[CLEANUP-MVC]** final `/cleanup` ModelVariableChange.lean. **Depends**: T-W7.1b.

- **[T-W7.0f]** the canonical points dictionary — `projModelPointsEquiv`,
  `projModelPointsEquiv_zero` (PointsDictionary.lean:30,37).
  - **Status**: in_progress · **Claimed**: lane-P2 worker (handle unrecorded — OWNER: retrofit
    per rule 5), retrofit 2026-07-07T14:03Z; 9373a093 landed the equiv — coordinator §2-P2: add the chartwise
    VALUE-lemma decls (`projModelPointsEquiv_some`/chart-case characterizations) BEFORE flipping
    done · **File**: EllipticCurve/PointsDictionary.lean ·
    **Depends**: none (discharges from PROVEN `projModel_points`) · **Type**: def + lemma
  - Sketch: choice-extract from the `∃`-form; pin at `O ↦ 0`. Leaf **L-0f** (prior-B2
    naturality caveat noted there).

- **[T-W7.0e]** field-points extensionality + reducedness — `hom_ext_of_forall_specPoint`,
  `isReduced_of_smoothOfRelativeDimension`, instances for the atlas, `universalCurve`, the
  double and triple products (PointsDictionary.lean:51–84).
  - **Status**: in_progress · **Claimed**: lane-P2 worker (handle unrecorded — OWNER: retrofit
    per rule 5), retrofit 2026-07-07T14:03Z; 9b47bd47 landed integrality — coordinator §2-P2: PORT greens into
    the canonical EllipticCurve/PointsDictionary.lean, DEDUP the doubled
    `IsDomain WeierstrassAtlasRing` (keep GLC:62; drop Moduli/PD:54) + IsNoetherianRing; board-
    register off-board sub-IDs T-W7.0e-proj (done, ProjIntegral.lean) and T-W7.0e-affine ·
    **Depends**: T-W7.0a (done) · **Type**: 2 lemmas + 4 instances
  - Sketch: equalizer closed (separated) + hit by residue-field points + surjective closed
    immersion onto reduced ⟹ iso; engine: smooth ⟹ flat + regular fibres over reduced base
    (mathlib check FIRST; fallback = repo standard-smooth charts, AG-2). Leaves
    **L-ext/L-0e**.

- **[CLEANUP-PD]** final `/cleanup` PointsDictionary.lean. **Depends**: T-W7.0e, T-W7.0f.

- **[T-W7.1a]** bundled atlas + classifying map — `EllipticCurveGeom.atlas`,
  `classifyRingHom`, `universalWeierstrassLoc_map_classifyRingHom` (+ helper
  `classifyCoeffHom` and `universalWeierstrass_map_classifyCoeffHom`)
  (WeierstrassAtlasBundle.lean:50–96).
  - **Status**: done (lane P5) · **Claimed**: lane-P5 (beastmode), retrofit
    2026-07-07T14:04Z (work landed 8cd4beba BEFORE claim — rule-5 incident, retro-legalized) ·
    **File**: EllipticCurve/WeierstrassAtlasBundle.lean · **Depends**: none · **Type**: 3 defs + 2 lemmas
  - Sketch: choice from `localModel` (index by points); `IsLocalization.Away.lift` with
    `Δ ↦` unit (via `classifyCoeffHom` + `universalWeierstrass_map_classifyCoeffHom`); the
    spec via `map_map` + `Away.lift_comp`. Leaf **L-1a′/1a**. DONE axiom-clean — all 5 decls
    `[propext, Classical.choice, Quot.sound]`.

- **[CLEANUP-WAB]** final `/cleanup` WeierstrassAtlasBundle.lean. **Depends**: T-W7.1a.

- **[T-W7.r1]** rigidity cores — `exists_unique_factor_of_isAffine`,
  `rigidity_of_subsingleton_range` (né `_base`), plus `hom_ext_of_isAffine` and
  `UniversallyOConnected.baseChange` (EllipticCurve/Rigidity.lean).
  - **Status**: ✅ DONE (lane P4, 2026-07-07) — sorry-free, axiom-clean. **Statement
    corrections at implementation** (producer-scope, recorded): the skeleton's
    `rigidity_of_subsingleton_base` was FALSE as stated — it lacked GIT's collapse
    hypothesis ("`f(X_s)` set-theoretically a single point"); counterexample `f = 𝟙 ℙ¹`
    over a field. Replaced by the STRONGER `rigidity_of_subsingleton_range`: any base
    (one-point never used by the Γ-argument), hypothesis
    `Set.Subsingleton (Set.range f.base)`, and `[IsSeparated q]` dropped (unused). This is
    the exact form the case-2 seed/thickening steps consume.
  - Route: Γ-Spec (`ΓSpec_adjunction_homEquiv_eq`, `Scheme.toSpecΓ_naturality`) for the
    affine core `Γ(X ×_S Y) = Γ(Y)`; constant-image case factors through an affine chart
    (`Scheme.Cover.idx/covers` + `IsOpenImmersion.lift`) then applies the affine core at
    `g = 𝟙 S`; empty-`X` case via `isInitialOfIsEmpty`.

- **[T-W7.r-supply]** the hypothesis supply — `EllipticCurveGeom.universallyOConnected`
  (Rigidity.lean).
  - **Status**: **DONE** (fable-P4, 2026-07-07, minutes after P3's i5 landed; `#print
    axioms` clean) · **Depends**: T-W7.0i·i5 (DONE) · **Type**: lemma
  - As sketched: base-changed geometry constructed inline (the `EllipticCurve.baseChange`
    field-recipe) + `locallyWeierstrass_pushforward_O_eq_O` instantiated; let-defeq closes.
  - **CONSEQUENCE (MILESTONE)**: `abelEnrichment_unique_of_connectedSpace` — canonicity of
    the group law over every connected locally noetherian base — now verifies to
    `[propext, Classical.choice, Quot.sound]`: the full GIT chain 6.1→6.2→6.3→6.4→6.6conn
    is sorry-free end-to-end. Rigidity.lean has ONE sorry left (C4glue).

- **[T-W7.r2]** THE rigidity lemma (GIT 6.1, case 2) — `rigidity` (Rigidity.lean).
  - **Status**: ✅ **DONE — SORRY-FREE, AXIOM-CLEAN** (fable-P4, 2026-07-07; #print axioms
    = propext/Classical.choice/Quot.sound). Full dependency tree proven: eqLocus API,
    seed (·b, preimmersion route), Krull neighbourhood (·c: ring engine + Z_U openness +
    cross-affine vanishing via `map_ideal` + Artinian case-1 mechanism + the direct
    thickened point through `fromSpecStalk` with the generic stalk-evaluation lemma
    `germ_eq_zero_of_fromSpecStalk_app` — no stalk-of-pullback needed), clopen assembly
    (·d). GIT-faithful statement (`hgconst`). · **Claimed**: fable-P4,
    2026-07-07T14:25Z · **Type**: theorem

- **[T-W7.r2·b]** the κ(s) seed — `fibre_subset_eqLocus_of_collapsed` (Rigidity.lean).
  - **Status**: ✅ PROVEN (fable-P4, 2026-07-07T15:35Z) — simpler than planned: no chart
    needed at all. The residue-field projection `pullback.fst q (fromSpecResidueField s)`
    is a preimmersion (mathlib instance + `IsStableUnderBaseChange`), hence injective on
    points, so the base-changed comparison morphism has SUBSINGLETON range directly and
    `rigidity_of_subsingleton_range` applies; then `exists_factor_eqLocus` + `range_fst` +
    `range_fromSpecResidueField` finish. `rigidity` now rests on the single leaf ·c.

- **[T-W7.r2·c]** Krull neighbourhood — `exists_open_factor_of_fibre_subset`
  (Rigidity.lean). **Status**: in_progress (fable-P4, 2026-07-07T16:05Z — route REFINED
  after IdealSheaf API survey) · **Depends**: T-W7.r1 (done) · **Type**: theorem
  - **Refined route (names verified at pin)**: the factorization consumable is
    `IsClosedImmersion.lift (ι) (V.ι) (H : ι.ker ≤ V.ι.ker)` + `lift_fac`
    (Morphisms/ClosedImmersion.lean:207–215) — NO glue-data plumbing needed. So the leaf
    reduces to: `(eqLocusι f g hf hg).ker ≤ ((p ⁻¹ᵁ U₀).ι).ker` for some open `U₀ ∋ t`,
    i.e. the ideal sheaf J := ι.ker VANISHES on `p⁻¹(U₀)` (ker of an open immersion = the
    sections vanishing on the open).
  - **TRAP documented**: `IdealSheafData.support` is the VANISHING LOCUS V(J) (= range ι,
    by `range_gluedTo`) — NOT the module-support {x | J_x ≠ 0} that Krull kills. Do not
    use `support` for the vanishing statement; work affine-locally.
  - Two sub-steps (in-proof): (c·i) thickening input: for every n, the Artinian fibre
    `X ×_S Spec (Γstalk t ⧸ 𝔪ⁿ)` factors through ι — case-1-over-Artinian-point via the
    SAME preimmersion/subsingleton-range mechanism as the r2·b seed (fromSpecStalk-composite
    preimmersion; one-point base; collapse from `hset` + `eqLocusι_comp_eq` pointwise);
    gives `ι.ker ≤ (thickened-fibre).ker`, whose affine-local kernel is `𝔪ᵗⁿ`-multiples.
    (c·ii) affine-local Krull: on affine `U ∋ x` (x in the fibre), `J.ideal U` is f.g.
    (noetherian, `LocallyOfFiniteType.isLocallyNoetherian`); its image in
    `O_{X,x}` lies in `⋂ₙ (𝔪ᵗ·O_{X,x})ⁿ = ⊥` (`Ideal.iInf_pow_eq_bot_of_isLocalRing`);
    f.g. + stalk-zero ⟹ a basicOpen ∋ x where the ideal restricts to 0; union the
    basicOpens over the (quasi-compact, `IsProper`) fibre; properness tube
    `U₀ := S ∖ p(X ∖ W)`.
  - **Progress (fable-P4, 2026-07-07T16:40Z)**: (c·ii) ring engine
    `Ideal.exists_notMem_mul_eq_zero_of_fg` PROVEN standalone (axiom-clean, scratch-compiled
    against pure mathlib) and inserted into Rigidity.lean — build verification pending an
    upstream red window (WeierstrassModel.lean mid-edit by another lane; olean watcher
    armed). Remaining (c·i) names ALL verified at pin: `IsPreimmersion (X.fromSpecStalk x)`
    (Stalk.lean:89, so the r2·b subsingleton mechanism transfers to
    `Spec (stalk/𝔪ⁿ) ⟶ Spec stalk ⟶ S` via preimmersion-comp), `IsLocalization.map_eq_zero_iff`
    (elementwise annihilation on `IsAffineOpen.isLocalization_stalk`),
    `Ideal.iInf_pow_eq_bot_of_isLocalRing` (Krull), `Scheme.stalkMap_germ` (push sections of
    `ι.ker` to the thickened stalk). Remaining sub-statement to formalize (THE one honest
    gap): the one-point base-change stalk computation — stalk of `X ×_S Spec (stalk t/𝔪ⁿ)`
    at a point over `x` is `O_{X,x} ⧸ 𝔪ᵗⁿ·O_{X,x}` (equivalently: ker of the projection's
    stalkMap contains exactly the `𝔪ᵗⁿ`-multiples) — plus the ker-≤ translation
    `vanishing near the fibre ⟹ ι.ker ≤ (tube).ι.ker` (per-affine, `Hom.ker` of an open
    immersion). Assembly after that: engine per fibre-point → basicOpen union →
    quasi-compact fibre → properness tube → `IsClosedImmersion.lift` (already wired in the
    committed hW-consumable shape).
  - **Progress (fable-P4, 2026-07-07T18:30Z — beastmode stretch)**: r2·c is CONCEPTUALLY
    COMPLETE, mechanically 2 residues. PROVEN sorry-free this stretch:
    `Ideal.exists_notMem_mul_eq_zero_of_fg` (ring engine), `isOpen_germMap_ideal_eq_bot`
    (Z_U openness), `germ_ideal_eq_zero_of_exists_affine` (cross-affine vanishing —
    `IdealSheafData.map_ideal` (:221, full equality along ANY affine inclusion) dissolved
    the basicOpen-HEq swamp), hW steps 1–3 (good locus + fibre-membership via c·i+Krull +
    properness tube). RESIDUE 1: section_ext coercion seam (in-file notes, /tmp/rig31-33
    shapes); RESIDUE 2: c·i proof (route banked). `rigidity` axioms trace through exactly
    these two + T-W7.7 chain untouched.
  - **Progress (fable-P4, 2026-07-07T17:15Z)**: c·i STATED green (`germ_ker_mem_pow_of_fibre_subset`,
    402ade6a). hW-assembly design settled after the cross-affine-germ analysis: work on the
    BASICOPEN BASIS to make the stalk-ideal well-defined — per affine `U`, let
    `Z_U := {z ∈ U | Ideal.map (germ_z) (ker.ideal U) = ⊥}`; `Z_U` is open (the proven
    engine `exists_notMem_mul_eq_zero_of_fg` + noetherian f.g. + `fromSpec_preimage_basicOpen`
    membership bridge + s-annihilation kills germs on `basicOpen s`), fibre∩U ⊆ Z_U (c·i +
    `Ideal.iInf_pow_eq_bot_of_isLocalRing` + `IsLocalHom (stalkMap)`), and cross-affine
    consistency via `map_ideal_basicOpen` (IdealSheaf/Basic ~:300) on basicOpen refinements.
    Then `W := ⋃ Z_U`, tube `U₀ := (p '' Wᶜ)ᶜ` via `Scheme.Hom.isClosedMap`
    ([UniversallyClosed] from [IsProper]), and the final `ι.ker ≤ (tube.ι).ker` per-affine
    via germ-ext (`Hom.ker_apply` needs [QuasiCompact (V.ι)] — from loc-noeth instance
    Noetherian.lean:205). Est. 150–250 lines + c·i's own proof (preimmersion mechanism +
    `pullbackSpecIso` kernel algebra).

- **[T-W7.r2·d]** clopen assembly — `exists_factor_of_connected` (Rigidity.lean).
  - **Status**: ✅ PROVEN (fable-P4, 2026-07-07T15:00Z) — modulo consuming the sorried ·c
    (leaf-DAG design). Route as planned: `U₁` clopen (flat+lfp open map / closed-immersion
    range), connectedness, `Cover.glueMorphisms` glue with `cancel_mono`-compatibility.
    With this, `rigidity` rests on exactly ·b + ·c.
  - Sketch (GIT pp. 115–116, transcribed; mathlib names VERIFIED in this checkout,
    assembly map inline at the `rigidity` sorry): equalizer backbone
    `isClosedImmersion_equalizer_ι_left` (in `Over S`, uses `[IsSeparated q]`); case 1
    over `Spec κ(s)` (seed) and the Artinian thickenings via
    `rigidity_of_subsingleton_range` + `UniversallyOConnected.baseChange` (both DONE);
    Krull intersection = `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` (stalks noetherian by
    the `IsLocallyNoetherian` stalk instance) + coherence + `p` closed ⟹ neighbourhood;
    `U₁ = S ∖ p(X−Z)` clopen — closed via flat ⟹ open = `UniversallyOpen.of_flat`
    (`[Flat p]` + `LocallyOfFinitePresentation` from properness over loc-noeth), open via
    the Krull neighbourhoods; connectedness + glue-the-factorizations (`ι` mono) ⟹
    split-epi closed immersion ⟹ iso. Leaf **L-R2**.

- **[CLEANUP-RIG-1]** `/cleanup` Rigidity.lean. **Depends**: T-W7.r2 (3rd proof ticket).

- **[T-W7.7·C2conn]** total space connected over connected base —
  `connectedSpace_of_universallyOConnected` (Rigidity.lean). **Status**: **DONE**
  (fable-P4, commit 3e9e51af) · **Depends**: none · **Type**: theorem
  - **Claimed**: fable-P4, 2026-07-07T20:30Z · **Done**: 2026-07-07 (`#print axioms` =
    propext/Classical.choice/Quot.sound on both decls). The idempotent-from-clopen leaf
    landed as `preconnectedSpace_of_isField` (glue `(1,0)` via `existsUnique_gluing'`,
    idempotency via `eq_of_locally_eq₂`, field ⟹ `χ ∈ {0,1}`, stalk nontriviality kills a
    piece; ~90 lines, upstream candidate). Assembly consumed P5's engine exactly as
    offered (thanks): open (flat+lfp chain, as r2·d) + closed (proper) + fibre =
    `range (pullback.fst p (fromSpecResidueField t)).base` with `Γ ≅ κ(t)` via `hp _ ⊤` +
    `commRingCatIsoToRingEquiv` transfer, nonempty via the section.
  - **Statement change (logged per rule 5)**: added `[IsLocallyNoetherian S]` to the
    skeleton statement — needed for `p.isOpenMap` (lfp from properness over loc-noeth,
    same instance chain as r2·d). Every consumer (C1–C4, all in the loc-noeth regime)
    already assumes it.
  - Route (refined): WLOG `e(S) ⊆ C` for a nonempty clopen `C` (pull back along the
    section, connectedness of `S`); for `x ∉ C` the fibre over `p x` meets both `C`
    (through `e`) and `Cᶜ` (through `x`); fibre-connectedness kills it. Fibre
    connectedness = the ONE sub-leaf: `Γ(fibre) ≅ κ(t)` (instantiate hp at
    `fromSpecResidueField`, `U := ⊤`) is a field, and a clopen decomposition of a scheme
    yields a nontrivial idempotent in `Γ` — the idempotent-from-clopen bridge is ABSENT
    from mathlib (verified 2026-07-07): build via sheaf-gluing on the two-clopen cover
    (`Γ(C ⊔ Cᶜ) ≅ Γ(C) × Γ(Cᶜ)`, glue `(1,0)`), est. 80–120 lines, its own leaf. `p`
    open (`UniversallyOpen.of_flat`) + closed (proper) as in r2·d.
  - **P5 supply note (2026-07-07, commit b182e1a5)** — the *topological* core is now a general
    reusable lemma, `ForMathlib/ConnectedTotalSpace.lean`:
    `connectedSpace_of_isOpenMap_of_isClosedMap_of_isConnected_preimage`
    `(IsOpenMap f) (IsClosedMap f) [ConnectedSpace Y] (∀ y, IsConnected (f ⁻¹' {y})) : ConnectedSpace X`
    (axiom-clean; mathlib `CardComponents` has only the vacuous cardinality bound). It packages
    the "clopen image is clopen = full base, splits a connected fibre" argument once, so the
    scheme wrapper reduces to: `p` open+closed (as noted) + per-fibre `IsConnected (p.base ⁻¹' t)`
    via `Scheme.Hom.fiberHomeo` (already in mathlib) + the ONE idempotent-from-clopen leaf. Use
    or ignore per the section-based route — **fable-P4 owns the wrapper + the idempotent leaf**;
    this is offered as shared infra, not a claim on the ticket.

- **[T-W7.7·C1]** GIT Cor 6.2 — `eq_mul_of_fibre_eq` (Rigidity.lean). **Status**: **DONE**
  (fable-P4, commit 637280a4) · **Depends**: T-W7.r2 · **Type**: theorem
  - **Claimed**: fable-P4, 2026-07-07T22:05Z · **Done**: 2026-07-07 (`#print axioms` clean).
    Route as planned, via the mathlib `Hom`-group of `G` (`Hom.mul_def` etc. all rfl):
    `comp_mul_inv_left` (generic collapse helper, reusable for C2) + rigidity + Hom-group
    algebra (`inv_mul_cancel_right`).
  - **Statement change (logged per rule 5)**: added `(e : 𝟙_ (Over S) ⟶ A)` — rigidity's
    section. Faithful to the banked case-2 scope decision (quotes file: case 3 sectionless
    fppf descent NOT NEEDED; `E` has the zero section). C2/C3 applications have it.

- **[T-W7.7·C2]** GIT Cor 6.3 — `factor_mul_of_tensor` (Rigidity.lean). **Status**:
  **DONE** (fable-P4, commits f3e9c6fc + order-flip) · **Claimed**: fable-P4,
  2026-07-07T22:20Z · **Done**: 2026-07-07, `#print axioms` clean · **Depends**:
  T-W7.7·C1 (DONE), T-W7.7·C2conn (DONE) · **Type**: theorem
  - **Statement changes (logged per rule 5)**: (i) added `(e₂ : 𝟙_ (Over S) ⟶ B)` — the
    source quote's `e₂`; (ii) added `[IsLocallyNoetherian B.left]`; (iii-RETRACTED) the
    conclusion keeps the ORIGINAL boarded Mumford order `lift (fst ≫ g) (snd ≫ h) ≫ μ` =
    `g(x)·h(y)` — obtained from the LEFT quotient `δ := (Ẽ≫f)⁻¹·f`; the flipped order
    would make GIT 6.4 produce an ANTIhomomorphism and kill 6.5. All three leaves landed
    (C2·res as `fromSpecResidueField_comp_section`; C2·fib inline via `hEfix`; C2·asm).
    Defeq-seam discipline: ascribed `set`-bridges keep every rw uniformly pullback-typed.
  - Route (raw-scheme, NO Over-`B.left` category / no `GrpObj` base-change needed): all
    Hom-group algebra stays in `Over S`: `F₂ := lift (fst) (toUnit _ ≫ e₂) ≫ f`,
    `δ := f * F₂⁻¹`; rigidity applied over base `B.left` to
    `⟨δ.left, (snd A B).left⟩ : pullback A.hom B.hom ⟶ pullback G.hom B.hom` (Over-monoidal
    is definitionally pullbacks: `tensorObj_left`/`fst_left`/`snd_left` rfl); instances by
    base change (`IsProper`/`Flat`/`IsSeparated` for `pullback.snd`, hO.baseChange);
    section `ẽ := pullback.lift (B.hom ≫ e₁.left) (𝟙 _)`; collapsed fibre at
    `y₀ := e₂.left (B.hom b₀)` via `comp_mul_inv_left`. Leaves:
  - **[C2·res]** `fromSpecResidueField_comp_section`: for a section–retraction
    `e ≫ q = 𝟙 S`, `B.fromSpecResidueField (e s) ≫ q ≫ e = B.fromSpecResidueField (e s)`
    (residue maps: split injection + retraction of fields ⟹ both isos, composite = id).
  - **[C2·fib]** fibre-inclusion fixes `E₂ := lift (fst) (toUnit _ ≫ e₂)`:
    `ι ≫ E₂.left = ι` for `ι := pullback.fst p̃ (fromSpecResidueField y₀)` — pullback
    hom-ext + C2·res.
  - **[C2·asm]** assembly: `g := lift (𝟙 A) (toUnit A ≫ e₂) ≫ f`, `h := homMk (sec ≫ fst)`;
    `fst ≫ g = F₂` by terminal-uniqueness; `f = δ * F₂` closes.

- **[T-W7.7]** canonicity (= MILESTONE T-W7b, loc-noetherian) — `isMonHom_of_one_comp_eq`,
  `abelEnrichment_unique_of_isLocallyNoetherian` (Rigidity.lean).
  - **Status**: **DONE — MILESTONE COMPLETE** (fable-P4, 2026-07-08; `#print axioms` =
    propext/Classical.choice/Quot.sound; **Rigidity.lean is SORRY-FREE**) · **Type**:
    2 theorems (+ ∀-component variants)
  - **C4glue DISSOLVED** — no componentwise gluing was needed: the ∀-component rigidity
    chain works over ANY loc-noeth base. New pieces (all axiom-clean):
    `exists_factor_of_forall_component` + `rigidity_of_forall_component` (seed in every
    component; clopen locus ∩ component nonempty ⟹ component ⊆ locus);
    `isConnected_fibre_of_universallyOConnected` (extracted from C2conn);
    `connectedComponent_eq_preimage_connectedComponent` (ForMathlib/ConnectedTotalSpace:
    components of the total space = fibres of the base's components — engine restricted
    over a component); `factor_mul_of_tensor_of_forall_component` (collapse at every
    fixed point of `e₂∘q`); `isMonHom_of_one_comp_eq'` (no connectivity — fixed points
    of `η∘π` in every component via the correspondence). Connected-base wrappers kept.
    Also new ForMathlib: `NoetherianSpace.isOpen_connectedComponent` + noetherian ⟹
    locally connected (upstream candidates; ended up unused by the final route but
    independently valuable).
  - **C3 DONE** — `isMonHom_of_one_comp_eq` (GIT 6.4): C2 at `μ[A] ≫ f`, `e₁ = e₂ = η[A]`;
    axis restrictions + unit identity + group flip; `tensorHom = lift` is defeq.
    `#print axioms` clean. Statement change (rule 5): `(hconn : ConnectedSpace S)` added —
    C2conn needs it; the arbitrary-base reduction is C4glue's job.
  - **C4conn DONE** — `abelEnrichment_unique_of_connectedSpace` (GIT 6.6, connected base):
    units agree via `one_eq_zero`; C3 at `𝟙` with the two `GrpObj` instances
    (@-application) gives `μ = μ'`; `MonObj.ext` + `GrpObj.ext` + definitional
    proof-irrelevance. Axioms: + `sorryAx` ONLY through the designed r-supply gate.
  - **[C4glue] (SORRIED LEAF, open)** — `abelEnrichment_unique_of_isLocallyNoetherian`:
    componentwise reduction. `S` loc-noeth ⟹ locally connected ⟹ components clopen;
    restrict both records along the component open immersions (base change of group
    objects, `Functor.mapGrpObj`-style as in `mulBy_baseChange`), apply C4conn per
    component, glue `μ = μ'`/`η = η'` along the induced open cover of the total spaces
    (`Scheme.OpenCover.hom_ext`), rebuild the record equality. Est. 120–180 lines.
  - The UNRESTRICTED `abelEnrichment_unique` stays sorried, gated on T-W7.8.

- **[CLEANUP-RIG-2]** final `/cleanup` Rigidity.lean. **Depends**: T-W7.7.

- **[T-W7.12]** glued negation + multiplication over `S` — `EllipticCurveGeom.negHom`
  (+`_π`, `_zero`), `EllipticCurveGeom.mulHom` (+`_π`) (GroupLawDescent.lean:≈37–60).
  - **Status**: blocked · **Depends**: T-W7.0b, T-W7.0c-ii, T-W7.0h, T-W7.1a, T-W7.1b ·
    **Type**: 2 defs + 3 lemmas
  - Sketch: per chart = base change of the model maps along `classifyRingHom` (via
    `isPullback_projModelBaseChange` ⓟ + the `e i` chart isos); overlap agreement =
    comparison (1b) + equivariance (0h); glue over the atlas pullback cover
    (`Scheme.Cover.glueMorphisms`). Leaf **L-desc** (maps half).

- **[CLEANUP-ALL-W7]** `/cleanup-all` on the T-W7 files. **Depends**: every open proof
  ticket above except T-W7.36. Blocks the milestone.

- **[T-W7.36]** axioms over `S` + assembly (= MILESTONE T-W7a — retires T-A6 EXISTENCE) —
  `EllipticCurveGeom.grpObj`, `grpObj_isCommMonObj`, `grpObj_one_eq_zero`
  (GroupLawDescent.lean:≈66–76) + fill `abelEnrichment_exists` (GroupLaw.lean:74–75).
  - **Status**: blocked · **Depends**: T-W7.0g, T-W7.12, CLEANUP-ALL-W7 · **Type**:
    def + 2 lemmas + theorem
  - Sketch: each axiom chart-locally = base change of the model identity (`Cover.hom_ext`);
    package; `abelEnrichment_exists := ⟨G.toEllipticCurve, G.toEllipticCurve_geom⟩` — the
    assembly (`toEllipticCurve`/`_geom`) ALREADY COMPILES (`rfl`). **No rigidity, no
    cohomology, no reducedness of `S` on this path.** Leaf **L-desc** (axioms half).

- **[CLEANUP-DESC]** final `/cleanup` GroupLawDescent.lean. **Depends**: T-W7.36.

- **[T-W7.8]** arbitrary-`S` canonicity upgrade (**RELABELED per coordinator 2026-07-07:
  thin wrapper — re-check at implementation**; the "absent from mathlib" note is CONFIRMED
  STALE — `spread_out_of_isGermInjective` SpreadingOut.lean:329,
  `spread_out_unique_of_isGermInjective` :198,
  `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` AffineTransitionLimit.lean:632;
  LOW priority pending reviewer F1′). EGA IV §8 spreading-out (FC Rem. 1.2(a) names the
  vehicle): `(E,e,m,m')` finitely presented ⟹ descend to a f.g. `ℤ`-subalgebra; equality
  descends. Needs Hom-spreading-out along filtered colimits — **absent from mathlib**
  (watch noetherian-approximation work). NOT skeletonized (quote-or-delete: EGA IV 8.8.2
  not yet transcribed). Gates ONLY the fully-general `abelEnrichment_unique`.
  - **COORDINATION (2026-07-07T15:20Z, from beastmode-D2's T-NOETH scoping)**: the
    "absent from mathlib" claim looks STALE — `AlgebraicGeometry/SpreadingOut.lean` has
    `spread_out_of_isGermInjective` + `spread_out_unique_of_isGermInjective` (EGA IV
    8.8.2 morphism spreading + uniqueness) and `AffineTransitionLimit.lean` has
    `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`. W-lane: RE-CHECK whether
    these discharge T-W7.8 directly (likely a thin wrapper). DISTINCT from the D-lane's
    T-NOETH (fp-flat algebra/object descent, not morphism-equality) — same foundation,
    no file overlap.
  - **Status**: blocked-on-mathlib (RE-CHECK COMPLETE, fable-P4 2026-07-08; claim
    released) · **Depends**: T-W7.7 (DONE) + mathlib hom-existence descent · **Type**:
    infra + theorem.
  - **RE-CHECK VERDICT (fable-P4, 2026-07-08)**: NOT a thin wrapper. Mathlib's
    `AffineTransitionLimit` has ONLY the INJECTIVE part of stacks 01ZC
    (`Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType` — equality of
    stage-morphisms descends); the SURJECTIVE part (hom-EXISTENCE: `colim Hom(Dᵢ,X) →
    Hom(lim,X)` surjective for `X` lfp — what we need to descend `μ, μ'` to a f.g.
    noetherian stage) is ABSENT (file TODO says morphism-property spreading is planned).
    `SpreadingOut` is the stalk-germ-neighbourhood variant (needs germ-injectivity ≈
    loc-noeth anyway — no help for arbitrary `S`). Routes forward: (i) WAIT for mathlib's
    noetherian-approximation stream (D2's T-NOETH watches it); (ii) concrete descent for
    the Weierstrass shape (a morphism into `projModel W` is chart-locally finitely many
    ring elements — ~300–500 lines, partially duplicative of (i)); (iii) drop to the
    stated loc-noeth theorem (DONE) as the permanent scope. Recommendation: (i), keep LOW
    priority per reviewer F1′; the loc-noeth canonicity covers every base in the Y(N)
    pipeline.

- **[CLEANUP-W7-FINAL]** `/cleanup-all` on all T-W7 files (the Phase-III close-out).
  **Depends**: T-W7.7, T-W7.36 (and T-W7.8 if/when it lands).

- **[T-W8] `level-spaces-over-U`**. `U_{Γ(N)} = {W + (P,Q) Drinfeld full level N}`,
  `U_{Γ₁(N)} = {W + P exact order N}`, `U_{Γ₀(N)} = {W + cyclic rank-N subgroup}`, as
  schemes/subfunctors over `U` cut out by the D-stream Cartier incidence loci; the quotient
  stacks `[U_P/G]` are the level stacks, represented by `Y(P)` when rigid. **Lane**: W + D/H ·
  **Depends**: T-W5, T-W6, T-D14+ (incidence), H-stream level defs · **Type**: def +
  representability bridge · **Sources**: reviewer v8; KM 3.1/3.2/Ch. 4.

- **[T-W-cmp] `abstract-comparison`** (DEFERRED, COH stream, NON-blocking). `M_ell^W ≃
  M_ell^abstract`, abstract = smooth proper geometrically-connected genus-1 fibres + section.
  Home of coherent cohomology / Serre duality / RR / Hodge bundle, and
  `abelian-scheme dim 1 ⇒ elliptic curve`. Explicitly OFF the critical path to `Y(N)`.
  **Lane**: COH (new parallel stream) · **Depends**: BB-COHBC, T-A9, T-A6 (`abelEnrichment`) ·
  **Type**: equivalence theorem · **Sources**: reviewer v8; KM 2.1; Katz Antwerp; DR II.1.

### Existing-ticket updates (v8)

- **T-A8** — VALIDATED as the definition of record; continue (T-A8a `baseChange`, then field
  swap + derived `EllipticCurveGeom.fibrewiseElliptic` — the record still IMPLIES
  `FibrewiseElliptic`, now a theorem not a field). No phrasing change (pointwise ≡ open-cover).
- **T-A6** (`abelEnrichment`) — reframed: NO LONGER on the critical path. Primary group-law
  route is T-W7 (local Weierstrass + descent). Abel/Pic⁰ canonicity moves into T-W-cmp (COH
  stream). Level-functor `map` fields (`pullSection_add`, gated on `abelEnrichment_unique`)
  should re-route through T-W7 once it lands — re-audit that gate then.
- **BB-COHBC / BB-RR (abstract side) / T-A9** — reclassified into the COH parallel stream;
  block only T-W-cmp + Hodge/modular-forms + compactification, never the open curves.
- **T-E5 / T-E8** (representability ⟺ rel-rep+rigid; stack packaging) — sequence AFTER the
  Stream-W layer (T-W1–T-W6); T-E8 stack packaging can consume `QuotientStack` (T-W3).

### H-lane progress log (beastmode-H, appended 2026-07-06T22:55Z)
- **[T-H7] DONE** (2026-07-06T22:50Z; claimed 16:55Z). `gammaFullNaive_not_rigid_of_le_two`
  PROVED, statement byte-identical to skeleton. Witness chain: T-H7d geometric point
  (AlgebraicClosure of a residue field; IsUnit via Spec.preimage) → pullbackAlong →
  T-H7b level point (N=1 zero pair; N=2 = T-B6 basis + Klein-four exhaustion by
  `decide` in ZMod 2 × ZMod 2 coordinates) → T-H7a negIso ([m]≫[n]=[mn] via
  GrpObj.comp_zpow; pullSection_negHom = negation) → T-H7c [-1]≠𝟙 (odd fibre
  torsion M ∈ {3,5}, ringChar dvd-arithmetic char-dodge) → assembly.
  **Axioms**: helpers `section_ext`/`pull_injective`/`exists_geometricPoint` + all of
  T-H7a CLEAN (propext/Classical.choice/Quot.sound). `exists_isNaiveFullLevel_of_le_two`
  + the headline carry `sorryAx` through exactly two REGISTERED gates: (i) the T-B6
  KM 2.3.1 boxes (BB-QF/FLAT/DEG/DIFF via `torsion_geometricFibre_rank_two`), (ii) the
  `gammaFullNaiveProblem.map` membership sorry (T-E4a/A6.δ gate; v8 re-routes it via
  T-W7). Done-modulo-registered-boxes, stream-B convention.
- **Sub-tickets**: T-H7a DONE (10 decls, axiom-clean) · T-H7b DONE · T-H7b-i DONE
  (REVISED at contact: epi-route replaced by closed-point separation via mathlib
  `ext_of_apply_closedPoint_eq` — `section_ext` + `pull_injective`, both clean) ·
  T-H7c DONE · T-H7d DONE.
- **Cross-lane repair** (flagged): `TorsionFibre.lean` was an ORPHAN module broken by
  the A-lane's `mulByHom_baseChange` addition to GroupLaw.lean (duplicate decl —
  T-B6a's copy was identical to GroupLaw's `mulByHom_baseChange_fst`). Repair: deleted
  the duplicate, repointed 2 uses to `mulByHom_baseChange_fst`. B-lane heads-up left
  here; GammaH.lean now imports TorsionFibre (first importer).
- **Board sync notes**: T-H2 + the `gammaHNaiveProblem` functor laws were done
  concurrently by another worker (landed 495b4030/6d851016 + earlier) — v6 execution
  order updated accordingly: NEXT = T-H1 (`gammaHNaive_bot`), then T-H3 remainder
  (orbit-compat; `map`-membership stays gated per v8 → T-W7), then T-H5.
- **Cleanup**: headline decl /cleanup single-decl at close; helper-decl golf batched
  into [CLEANUP-14] (GammaH.lean file cleanup — its T-H2/T-H3 preconditions are now
  largely met; T-H5 outstanding).
  - 2026-07-06T23:20Z: T-H7 post-proof cleanup ✓ ran (single-decl /cleanup: gates all
    pass, body 42→11 + 2 private helpers, one strictly more general
    (gammaFullNaiveProblem_map_negIso_of_le_two — [-1] fixes EVERY level structure);
    axioms unchanged; simplify n/a in single-decl mode). Claiming **T-H1**
    (gammaHNaive_bot, :352) — ⊥-orbits are singletons via glSmul_one; iso by
    NatIso.ofComponents + Quotient.lift id; naturality by Quotient.ind +
    Subtype.ext (memberships proof-irrelevant, the map's gated sorries don't block).
  - 2026-07-06T23:40Z: **T-H1 DONE** — gammaHNaive_bot proven (18-line NatIso term;
    ⊥-orbits singletons via glSmul_one; naturality by proof-irrelevance on the gated
    membership fields). Axioms: registered-gate profile (sorryAx via the functors'
    internal T-E4a-gated sorries only). Cleanup: golf-clean term proof; file-level
    pass batched into [CLEANUP-14] per board cadence. T-H2/T-H2a/T-H3-laws +
    hOrbitSetoid.iseqv confirmed landed by the concurrent worker — H-lane remaining:
    T-H5 (next), gated memberships (T-W7), T-H4/H6/H8/H9/H10 (gated).
    **T-H5 recon**: statement sound (Nontrivial R guard present); ⟸ direction needs
    T-G3 content (GME 2.6.4 Aut-computation, transcribed §B9) — T-G3 is UNCLAIMED →
    recursing into it as the dependency (Tier A3). ⟹ direction (elliptic-point
    witnesses j=0/1728) sequenced after the A-lane W4/W5 layer per v8 spine.

### H-lane G6 continuation (beastmode-H, 2026-07-06T23:55Z)
- H-lane drained modulo registered gates (T-H4: C+Q+D18; T-H5: W7/E12-15 spine +
  T-G3 engine; T-H6: E5+H4; T-H8/9: ⧗KM; memberships: T-W7 gate; T-H10 laws half
  found already proven, discrete half T-G3-gated). Stale board notes: T-G1 was
  DELETED by the adversarial pass (bullet stale); T-F0 already done (beastmode-B).
- **Claiming T-C0** (char-0 étale-descent Weil pairing — unclaimed C-stream, review
  first milestone; deps T-B6 ✓ done-mod-boxes, Galois machinery ✓ AG-GG landed):
  it unblocks H-lane's own T-H4 (H=1 Weil-pairing open locus). **Claimed**:
  beastmode-H, 2026-07-06T23:55Z, Status: in_progress.
  - 2026-07-07T00:15Z: T-C0 decomposed + skeleton landed (WeilPairing/EtaleDescent.lean,
    builds green): **T-C0a** `torsionAlgebra` (E[N] over Spec k as CommAlgCat.FiniteEtale k
    — finite ⟹ affine + T-B5 étale boxes + Γ-transport) → **T-C0b**
    `torsionAlgebraPointsEquiv` (fibre functor value ≃ torsionBy of the geometric point
    group; Galois-equivariance clause cut at contact) → **T-C0c** HasseWeil pairing
    Gal(k̄/k)-equivariance (statement at contact; HasseWeil has DivisorGalois /
    FrobeniusConjugation to mine) → **T-C0d** transport through the AG-GG Galois
    equivalence (PreGaloisCategory (FiniteEtale k)ᵒᵖ landed by B) → **T-C0e**
    `exists_weilPairingSpecField` (field-base DS4 discharge; general ℚ-scheme case
    recorded as follow-up — needs the étale-trivialisation tower, T-H4-adjacent).
    Scope note: field-base first per review Q5's own milestone framing; YRho consumer
    (AlgebraicClosure ℚ) is covered.
  - 2026-07-07T00:35Z: T-C0a delegated (torsionAlgebra construction — route: IsFinite
    ⟹ IsAffineHom ⟹ IsAffine, Γ-transport, HasAffineProperty/HasRingHomProperty
    extraction of Finite/Etale to the algebra side, FiniteEtale.of packaging).
    **T-C0c recon done**: HasseWeil's pairing = transport-constant of τ_S g_T / g_T
    (Pairing.lean:217, Classical.choose of pairing_const_of_transport);
    DivisorGalois.lean has the full RingEquiv-transport toolkit (map_XYIdeal,
    valuation_map_ringEquiv, count_map_ringEquiv) and FrobeniusConjugation.lean the
    coordinate-ring generator-extensionality pattern — T-C0c (general σ-equivariance)
    = generalise their Frobenius chain to arbitrary σ : k̄ ≃ₐ[k] k̄; patterned,
    substantial; statement to be cut in HasseWeil-vocabulary inside EtaleDescent.lean
    (cross-project import already legal — one workspace).
  - 2026-07-07T00:55Z: **T-C0a DONE** (delegated, first-try) — torsionAlgebra via
    IsFinite⟹IsAffineHom⟹isAffine_of_isAffineHom, k-algebra by
    (ΓSpecIso).inv ≫ appTop toAlgebra, Module.Finite from IsFinite.finite_app +
    finite_respectsIso.cancel_left_isIso, Algebra.Etale from
    HasRingHomProperty.iff_of_isAffine + Etale.respectsIso; packaged with
    CommAlgCat.FiniteEtale.of. Axioms: boxes only. **T-C0b route pinned**: AlgHom
    side ≃ {h : Spec k̄ ⟶ E.torsion N // h ≫ torsionπ = t} (affine Γ-adjunction /
    isoSpec + Spec.preimage glue) ∘ torsionPointsEquiv (TorsionFibre:304) — delegating.
  - 2026-07-07T01:10Z: T-C0b delegated (affine Γ-adjunction glue ∘ torsionPointsEquiv).
    **T-C0c placement decided**: HasseWeil files are READ-ONLY on this branch
    (cross-branch drift risk — their dev branch owns them); the σ-equivariance
    generalisation lives in ModularCurves as a NEW file
    WeilPairing/GaloisEquivariance.lean importing HasseWeil — their DivisorGalois
    toolkit is already σ-general (map_XYIdeal/valuation_map_ringEquiv take arbitrary
    RingEquiv); only the Frobenius-specific instantiation files
    (FrobeniusFunctionFieldEquiv/DivisorGalois/Conjugation, pattern theorem
    frobeniusFunctionFieldEquiv_weilFunction_eq_smul :492) need σ-mirroring.
    Statement design after T-C0b returns (its equiv form feeds T-C0d's shape).
  - 2026-07-07T01:30Z: **T-C0b DONE** (delegated, first-probe compile) — the affine
    Γ⊣Spec glue went through with isoSpec_inv_naturality/toSpecΓ_appTop/
    ΓSpecIso_naturality; no gap lemmas. **DEFECT FLAGGED (self-report)**: the T-C0e
    skeleton statement `exists_weilPairingSpecField` is TOO WEAK as stated — the
    over-S condition alone is satisfiable by the trivial section through μ_N's unit,
    so it does not pin the pairing. RE-CUT PLAN: after T-C0c/d land the
    identification vocabulary (fibre-functor points of the product ↔ pairs of
    torsion points; HasseWeil comparison), restate T-C0e with the fibrewise
    HasseWeil-comparison spec (T-C4's content at field bases) as the defining
    clause. ALSO SURFACED: the k̄-points bridge from scheme-E to a Weierstrass
    model's point group needs the fibre model (FibrewiseElliptic at the point of
    Spec k gives W/k ✓ exists today) PLUS group-law comparison across the pointed
    fibre iso — that is A6.δ/T-W7-gate-adjacent; T-C0c/d will surface the exact
    edge. Next: T-C0c skeleton (WeilPairing/GaloisEquivariance.lean).
  - 2026-07-07T01:50Z: T-C0c delegated (new file WeilPairing/GaloisEquivariance.lean;
    σ-general mirror of the HasseWeil Frobenius chain, statement-first). **T-C0d
    designed + RE-CUT against mathlib's CategoryTheory/Galois/Equivalence.lean**
    (functorToContAction : C ⥤ ContAction FintypeCat (Aut F), Full+Faithful+EssSurj —
    with B-lane's GaloisCategory instance for (FiniteEtale k)ᵒᵖ this is the whole
    transport): **T-C0d-i** (gate-free) — any Aut-equivariant continuous pairing map
    between the fibre values of torsionAlgebra ⊗ torsionAlgebra and the μ_N algebra
    lifts to a FiniteEtale-morphism, via functorToContAction.Full; **T-C0d-ii**
    (GATED) — the concrete pairing map on fibre values via the Weierstrass fibre
    model: needs the pointed fibre iso (FibrewiseElliptic at the point of Spec k) to
    be a GROUP iso, which is the A6.δ/abelEnrichment content = **the T-W7 edge**
    (v8: T-W7 retires that gate). Board edge recorded: T-C0d-ii, T-C0e-re-cut ←
    T-W7 (A-lane, spine-sequenced; W4/W5 just landed). H-lane keeps the gate-free
    side moving (T-C0c chain + T-C0d-i statement) and hands the concrete-map edge
    to the spine like the level-functor memberships.
  - 2026-07-07T02:40Z: **T-C0c DONE, sorry-free + FULLY axiom-clean** (delegated;
    888-line WeilPairing/GaloisEquivariance.lean, zero sorries, zero warnings).
    `weilPairing_galois_equivariant : σ (e_ℓ(S,T)) = e_ℓ(σ•S, σ•T)` for any
    σ : F ≃+* F with W.map σ = W; point action = pointHom (coordinatewise, additive
    via HasseWeil's mapAddMonoidHom). DISCOVERY: HasseWeil's whole pairing chain
    (weilPairing, frobeniusScaling_holds included) is SORRY-FREE — so the C0
    field-level layer carries no boxes at all; only the scheme-side (torsionAlgebra
    etc.) carries the T-B4/B5 boxes. Engineering notes in-file (KE-instance defeq
    walls dodged via explicit translate formulas; S=0 case needs application-level
    rewriting). NEXT: T-C0d-i (gate-free descent transport via functorToContAction).
  - 2026-07-07T03:00Z: T-C0d-i first dispatch died on a session-limit API error
    BEFORE any edit (tree verified clean at the T-C0b commit); re-dispatched
    post-reset. Deliverables unchanged: muNAlgebra + fibre desc, tensor pair
    algebra + fibre desc, packaging theorem (equivariant point-pairing ⟹
    FiniteEtale morphism via functorToContAction.Full).
  - 2026-07-07T03:35Z: **T-C0d-i DONE, zero new sorries** (retry worker). Descent
    heart `exists_finiteEtaleHom_of_galoisEquivariant` AXIOM-CLEAN; packaging
    `exists_pairingAlgebraHom_of_galoisEquivariant` carries only the torsionAlgebra
    boxes. muNAlgebra needed NO boxes (muNπ_isFinite/muNπ_etale_iff are proven in
    MuN.lean). Upstream candidates minted: `algHomEquivSpecOver` (generic Γ⊣Spec
    over-points correspondence), `tensorAlgHomPairEquiv` (no bundled mathlib form
    exists). FINDINGS: mathlib's fibre functor Ω = SeparableClosure k (hence
    [CharZero k] + IsSepClosure.equiv conjugation in the packaging); the Aut-F
    action bridge is DEFINITIONAL (toAut ∘ fiberMulAction = AlgHom.comp — no
    comparison lemma needed). **T-C0 gate-free portion COMPLETE**: a+b+c+d-i proven.
    Remaining: T-C0d-ii (concrete pairing map on fibres — model bridge, T-W7 edge)
    then T-C0e re-cut with the comparison spec. C-stream hands the baton to the
    A-lane spine (T-W7) exactly like the level-functor memberships.
  - 2026-07-07T03:45Z: G6 — H+C gate-free frontiers drained; ALL remaining H/C items
    funnel into T-W7 (A-lane spine, unstarted). Next unclaimed met-deps ticket:
    **claiming T-SG1** (stream SG, definition + basic API of finite locally free
    closed subgroup schemes of E/S; KM 1.4.1 quote in hand for SG2 downstream).
    **Claimed**: beastmode-H, 2026-07-07T03:45Z, Status: in_progress. Planning
    contact first (definition ticket — design against Torsion/CartierDivisor
    vocabulary; adversarial attack block before any proof per standing rule 1).
  - 2026-07-07 (resumed session, model switched to Opus 4.8 past the Fable-5 credit
    wall): **T-SG1 DONE.** A prior firing had written the full `GroupScheme/Subgroup.lean`
    (503 lines, matching the planned design: structure-not-predicate, RelEffCartierDiv
    divisor dictionary, HasRank predicate, torsionSubgroup leading example, all ATTACK
    blocks) but died BEFORE getting it green — it had 2 hard errors + the parked sorry.
    ROOT CAUSE of the 2 errors: `IsIso (Scheme.Hom.toImage G.ι)` (the mathlib instance
    `[IsClosedImmersion f] → IsIso f.toImage`, ClosedImmersion.lean:153) synthesises in
    the MAIN tactic context but NOT in the goals under `refine ⟨H, fun P => (hH P).trans
    ⟨?_, ?_⟩⟩` — the delayed metavariable goals under the `fun P` lambda don't consult
    the instance for `inv G.ι.toImage`, even with a local `have : IsIso … := inferInstance`
    hoisted. FIX (3-step): (1) `set j := inv G.ι.toImage with hj` in the MAIN context
    (synthesis works there); (2) derive `hjeq : j ≫ G.ι = G.ι.ker.subschemeι` in the
    main context via `IsIso.inv_comp_eq`; (3) `simp only [toRelEffCartierDiv_ideal]` to
    normalise the goal's `G.toRelEffCartierDiv.ideal` → `G.ι.ker` BEFORE the bullets, so
    `k`'s type aligns syntactically with `j`/`hjeq` (the `rw` motive needs syntactic, not
    just defeq, match — image=ker.subscheme is reducible but toRelEffCartierDiv.ideal is
    not). Bullets then use the plain named term `j` (no synthesis). Green in build7.
    AXIOM AUDIT (lake env lean scratch): toRelEffCartierDiv_isSubgroup / torsionι_factors_iff
    / toRelEffCartierDiv_degree AXIOM-CLEAN; torsionSubgroup / torsionSubgroup_hasRank /
    torsionSubgroup_pointSubgroup / HasRank.smul_eq_zero_of_factors carry sorryAx ONLY via
    the registered upstream boxes (BB-QF/BB-FLAT/BB-DEG/BB-DELIGNE) — no new box. Spawned
    **T-SG1b** (base-change subgroup field, the one parked sorry) → funnels to the A-lane
    asSection_zsmul spelling normalisation. NEXT: G6 re-scan.

## Amendments v9 (2026-07-07): EXPERT-REVIEW integration — statement-drift audit reply

*Third expert-review pass. Verdict: **ON TRACK**; the v8 restaging validated wholesale.
Verbatim reply + brief + state archived at `.mathlib-quality/expert-review/2026-07-07/`
(`reply.md`, `brief.md`, `state.md`). Three headline asks: (1) fix the Γ₁(N) drift [DONE — the
code was correct, only the brief prose was wrong]; (2) separate finite quotients from the
Weierstrass quotient stack; (3) keep marginal workers on the core Y₁(N)/Y(N) path, not the
Galois/F-stream or the N≤2 guardrails. Owner approved "apply all" 2026-07-07.*

### v9.0 Headline drift Γ₁(N) — RESOLVED (no Lean change)
The reviewer feared `Σ_a [aP] = E[N]` (degree N vs N²). The code is CORRECT:
`IsGammaOne` = `Section.HasExactOrder` = `(orderDivisor P N).IsSubgroup E`, i.e. the
**degree-N** divisor `[P]+…+[NP]` is a **subgroup divisor** (Deligne exact order), NOT equated
to E[N]; `IsFullLevel` = the **degree-N²** divisor `Σ_{(a,b)} [aP+bQ]` with `.ideal =
torsionIdeal N` (= E[N]). Both match KM 3.1/3.2 + Deligne exactly. The drift was PROSE-ONLY in
the brief (§2.1, §4), corrected in both copies. Reviewer's "fix the code before more depends on
it" branch does not apply — nothing downstream is corrupted. The `IsNaiveGammaOne` killing-clause
adversarial fix (2026-07-06) already handles the subtler `N·P=0` trap.

### v9.1 Current work order (start-now set — SUPERSEDES the v3/v4/v8 start-now sets)
Reviewer's marginal-worker priority (annotated with live board reality 2026-07-07T~04Z):
1. Fix Γ₁(N) drift — **DONE** (prose; code was already right).
2. Finish **T-W3/W4/W5** → state `[U/G](S)` as torsors + equivariant maps. (T-W3/W3b DONE;
   T-W3c in_progress beastmode-Q; T-W5 DONE. Near.)
3. **T-W7**: group law from Weierstrass charts + descent. ★ **CURRENT CRITICAL BOTTLENECK** —
   UNSTARTED (A-lane); BOTH the H-lane (T-SG1 / level memberships) and C-lane (T-C0d-ii concrete
   fibre pairing) frontiers now funnel into it. Marginal A-lane effort here unblocks the most.
   This is reviewer step 3.
4. Discharge the **invertible-N torsion/étale bottleneck** — **BB-DIFF or its local substitute
   (new T-B5z) BEFORE BB-DELIGNE**. `[N]` étale when N invertible; E[N] finite étale rank N²;
   geometric fibres (ℤ/N)² (T-B6 DONE).
5. Char-0 **scheme-level** Weil pairing over arbitrary ℚ-schemes (T-C0 sharpened — v9.4).
6. Symplectic Isom-scheme for Y(ρ̄) (T-F6).
7. **Only then**: BB-DELIGNE (T-D5), Γ₀ cyclicity (T-D10), bad-level integral theory.
Do NOT re-staff N≤2 non-rigidity (T-H7) — v9.4.

### v9.2 Stream split directive (Q3) — W-stack ≠ Q-finite [BINDING]
`G = WeierstrassCurve.VariableChange` is an **affine group scheme, morally `G_m ⋉ 𝔸³`** in
`(u,r,s,t)` with `u` invertible — **NOT a finite constant group**. Consequences:
- **W-stack** (owns [U/G]): affine-group-scheme actions, **G-torsors**, quotient groupoid
  `[U/G]`. This is the T-W3b route (TorsorPair + trivialization + full faithfulness over
  connected nonempty bases) — ALREADY the correct machinery. `[U/G]` is built from **torsors**,
  NOT from the finite invariant quotient `Spec(A^G)`.
- **Q-finite** (T-Q1–T-Q6): finite constant group actions, affine invariant quotients
  `Spec(A^G)`, finite quotients of level schemes, and the **minimal finite-quotient API for
  KM 4.7 / finite level quotients / Γ_H** (Q7: this API is NOT deferred, unlike full coarse
  moduli / j-line / Stream M).
- **ACTION**: verify T-W3's `Depends: T-Q5/T-Q6` is on the SchemeAction/torsor vocabulary
  (the T-W3b basis), NOT on `Spec(A^G)` (T-Q3); sever any spurious dependency so `[U/G]` does
  not wait on finite-invariant-quotient machinery. "Do not wait for coarse affine invariants to
  finish [U/G]."

### v9.3 New tickets (v9)
- **[T-A8b] `weierstrass-atlas-cover-object`** (Q1a; REVERSES the v8 pointwise-only deferral —
  owner-approved). Define an explicit cover-object `WeierstrassAtlas E S` (index set, affine
  opens + cover, per-chart `WeierstrassCurve`, per-chart pointed iso `π⁻¹(Uᵢ) ≅ projModel Wᵢ`)
  and prove **equivalence with the pointwise `LocallyWeierstrass` predicate EARLY**. Keep the
  pointwise form public. Rationale (reviewer): descent, `[U/G]`, local group law, coordinate
  changes, and patching `E[N]` are all easier from an explicit cover object. **Lane**: A ·
  **Depends**: T-A8 · **Type**: structure + equivalence theorem · **Sources**: reviewer v9.
  Distinct from the DONE universal atlas `Moduli/WeierstrassAtlas.lean` (that is the universal
  U; this is the per-curve local-Weierstrass witness data).
- **[T-D33] `subgroup-divisor-locus`** (Q — incidence-centre completion). The closed locus where
  a relative effective Cartier divisor `D` is a **subgroup divisor** (representability of
  `RelEffCartierDiv.IsSubgroup` as a closed subscheme). Needed to cut out the Γ₁ exact-order
  condition over U. **Lane**: D · **Depends**: T-D14/T-D15 · **Type**: representability theorem ·
  **Sources**: reviewer v9; KM 1.3. (The other four centres exist: incidenceLE = T-D14 DONE,
  incidenceEQ = T-D15, A-str/A-gen representability = T-D21.)
- **[T-GG-gen1] `fiber-functor-parameterized`** (Q5; for-mathlib, **LATE — post-critical-path**).
  Reparameterize the finite-étale fibre functor over an arbitrary separably closed geometric
  point `Ω/k` with `IsSepClosure k Ω`, NOT the hard-coded `SeparableClosure k`. The C-lane
  ALREADY hit this friction (T-C0d-i FINDINGS: mathlib's fibre functor Ω = SeparableClosure k
  forces [CharZero k] + IsSepClosure.equiv conjugation) — evidence the parameterized form is more
  robust. **Lane**: F/for-mathlib · **Type**: generalization.
- **[T-GG-gen2] `finite-etale-algebra-product-decomposition`** (Q5; for-mathlib, LATE). Upstream
  via `finite étale k-algebra ≃ ∏ finite separable field extensions`, then derive `connected
  finite étale k-algebra ↔ field` from the primitive-idempotent/product decomposition (replacing
  the ad-hoc idempotent-splitting proof for the mathlib-facing version). **Lane**: for-mathlib ·
  **Type**: refactor/generalization.
- **[T-B5z] `mulBy-N-etale-local-weierstrass`** (Q4; BB-DIFF SUBSTITUTE, prioritized before
  BB-DELIGNE). Prove `[N]` étale when N invertible via the **invariant differential on Weierstrass
  charts** (mathlib `WeierstrassCurve` invariant differential / division polynomials) + descent —
  narrower than a full relative-differentials (Ω¹) scheme API (the T-B5y gate). **Lane**: B ·
  **Depends**: T-W5 (charts) · **Type**: theorem · **Sources**: reviewer v9. Supersedes T-B5y on
  the critical path (T-B5y stays as the general-API form).
  - **Claimed**: beastmode-B, 2026-07-07T09:41Z → **BLOCKED (foundational gap), claim released
    2026-07-07T10Z** after investigation (local + dedicated mathlib-API research agent). Target
    was `mulByHom_formallyUnramified` (the BB-DIFF `sorry`). **FINDING**: the invariant-differential
    route is INFEASIBLE at current mathlib — there is NO invariant differential `ω` for
    `WeierstrassCurve`, NO `[N]`-as-a-map (division polynomials `ψ_N` exist as *polynomials* over
    `CommRing` but are NOT connected to any point map; the only `[N]` is field-only `nsmul` on
    `Point`), and elliptic curves are NOT realized as schemes in mathlib. The project's `[N]`
    (`mulByHom = (mulBy n).left`) is **categorical** (`GrpObj`), not chart-based. **All routes to
    BB-DIFF need a large foundational build**: (a) invariant-differential + Kähler API [absent];
    (b) a `ψ_N`↔torsion-point separability bridge over fields [absent]; or (c) the
    categorical-`[N]` ↔ Weierstrass-chart-`[N]` comparison = **T-W7 scope** (A-lane, in-progress,
    its own "large phase"). The fibre result **T-B6 is CIRCULAR** (consumes `torsionπ_etale` ⟸
    BB-DIFF). **RECOMMENDATION**: BB-DIFF is best unlocked by T-W7's group-scheme phase, OR
    commissioned as its own multi-session ticket — the `ψ_N`-separability bridge is the most
    self-contained mathlib-aligned route (`FormallyUnramified` reduces cleanly to
    `Subsingleton Ω[coordinateRing⁄base]` via `HasRingHomProperty.Spec_iff` +
    `Algebra.formallyUnramified_iff`). The reviewer's "local substitute is easier" premise
    (v9 step 4) does NOT hold — the categorical `[N]` makes even the chart connection T-W7-scale.
    (Reusable partial: `FormallyUnramified(torsionπ N) → FormallyUnramified(mulByHom N)` via group
    infinitesimal-lifting is self-contained/buildable, but only *reframes* the box, not discharges
    it.) Full route analysis: `scratchpad/tb5z_architecture.md`.

### v9.4 Existing-ticket updates (v9)
- **[T-A4] RE-FROZEN** (Q2; clears blocked-B2). New statement (owner-approved, torsor form):
  *for a fixed locally-Weierstrass E/S, the sheaf of Weierstrass presentations of E is a **torsor
  under `G = VariableChange`** (as an affine group scheme); after a trivialization of the
  Hodge/conormal sheaf `ω_{E/S}` at the identity, the remaining changes are exactly the `u = 1`
  subgroup.* The Lean theorem **consumes the G-action / torsor statement**, NOT a fragile
  coordinate formula (general change `x = u²x' + r`, `y = u³y' + u²s·x' + t`; KM 2.2.5's further
  2-parameter reduction depends on the precise meaning of "adapted" — do not hard-code). `ω` =
  chosen Hodge/conormal trivialization (compatible with the Katz modular-forms `ω_{E/S}`). Ties
  T-A4 to Stream W (G-torsors). Retire the false points-cardinality form; the B2 counterexample
  record (2-isogenous pair y²=x³−36x vs y²=x³+144x) stays as the rationale.
- **[T-C0] SHARPENED** (Q6). Target the **T-relative morphism**
  `weilPairingCharZero : E[N] ×_T E[N] ⟶ μ_{N,T}` over arbitrary `Spec ℚ`-schemes T (construct
  étale-locally on T where E[N] trivializes, then descend) — a pairing over FIELDS is NOT enough
  for the moduli functor on ℚ-schemes. **If the first milestone proves only the field case, LABEL
  it a field-valued-points theorem, not the pairing for `RepresentsYRho`.** Keep
  Silverman/determinant normalization + the symplectic pin `e_N(aP+bQ, cP+dQ) = e_N(P,Q)^{ad−bc}`.
  STATUS reality: T-C0 a+b+c+d-i already PROVEN (`exists_pairingAlgebraHom_of_galoisEquivariant`,
  the descent heart the reviewer praised); remaining T-C0d-ii (concrete fibre pairing map) is a
  T-W7 edge.
- **[T-H7] PARKED — do not re-staff** (Q4). N≤2 non-rigidity is a useful GUARDRAIL but off the
  critical path; put no more workers here. The `in_progress` marker (beastmode-H, 07-06T16:55Z) is
  STALE — the H-lane correctly drained its gate-free frontier and moved to T-SG1 (07-07T03:45Z).
  Critical path needs **positive rigidity for N≥3** (feeds T-E9/T-H*) + the quotient-stack/torsion
  infra, not N≤2 guardrails.
- **Convention**: results whose proof consumes a sorried black box are tagged
  **[PROVED-MODULO-BOXES]**, not [PROVED] (kernel-checked ≠ box-free) — in future briefs and the
  board scoreboard.

### v9.5 Confirmations (no action)
- Q1a def-of-record: `EllipticCurveGeom`/`LocallyWeierstrass` split ENDORSED (plus T-A8b).
- Q3 strategy: post-v8 sequencing endorsed wholesale (W bottom-up, T-W7 group law, D unchanged,
  F via the in-project Galois correspondence). "Nothing in §5–§6 to stop doing."
- Q7 coarse moduli: deferral CONFIRMED (Stream M stays skeleton); only the minimal
  finite-quotient API (v9.2 Q-finite) is near-term.

### H-lane G6 + v9-integration (beastmode-H, 2026-07-07, Opus 4.8)
- **T-SG2 DONE** (def-of-record layer), banked. `GroupScheme/CyclicSubgroup.lean` sorry-free,
  axiom-clean (`IsCyclic`, `IsCyclic.hasRank`/`exists_fppf_generator`/`isCyclic_of_generator`,
  `GammaZeroStructure`). Design: reuse T-D10's `IsGammaZeroFppf` on `G.toRelEffCartierDiv` — DRY,
  no new fppf vocab, no T-SG1b/T-W7 dependency. Import chain: new file above both
  `GroupScheme.Subgroup` and `LevelStructure.Basic` (acyclic; Basic imports ExactOrder).
- **v9 expert-review incorporated** into the H/C lane direction (reply.md archived; owner wrote
  Amendments v9). Effect on my streams:
  - Γ₀ cyclicity (T-SG2/T-D10) DEPRIORITIZED to work-order #7 → T-SG2 banked, no more SG effort.
  - T-H7 (N≤2 non-rigidity) PARKED — do not re-staff (already DONE). Stale in_progress marker cleared.
  - **T-C0 SHARPENED (v9.4) = my next target (reviewer #5).** Field pairing is NOT enough for the
    moduli functor; target the **T-relative** `weilPairingCharZero : E[N] ×_T E[N] ⟶ μ_{N,T}` over
    `Spec ℚ`-schemes T (construct étale-locally on T where E[N] trivializes, then descend). My
    `exists_pairingAlgebraHom_of_galoisEquivariant` (the descent heart the reviewer praised) is the
    right abstraction; extend field→T-relative via the étale-descent route (NOT the T-W7 Weierstrass
    route, which is the separate KM 2.8 path). Re-cut the too-weak `exists_weilPairingSpecField`
    (T-C0e) as an explicitly-LABELED field-valued-points theorem + state the T-relative target.
  - T-GG-gen1 (fiber functor over `IsSepClosure k Ω`) spun off from my T-C0d-i finding — LATE/
    for-mathlib, not now.
- **NEXT**: scope the T-relative char-0 Weil pairing (v9.4 T-C0); re-cut T-C0e; advance gate-free
  scaffolding (μ_{N,T} target, étale-local trivialization of E[N], descent of the morphism over T).
- **T-C0e RE-CUT DONE** (beastmode-H, 2026-07-07, per v9.4). Removed the too-weak
  `exists_weilPairingSpecField` from `WeilPairing/EtaleDescent.lean` (its `w ≫ muNπ = fst ≫
  torsionπ` constraint was satisfiable by a trivial section — neither the field-valued-points
  theorem nor the moduli pairing). `EtaleDescent.lean` is now **sorry-free** (remaining decls
  carry only the registered T-B4/B5 boxes). Module docstring re-cut: the field-valued-points
  pairing of record is the PROVEN `exists_pairingAlgebraHom_of_galoisEquivariant` (descent heart,
  reviewer-praised); the DS4 target is the T-relative `weilPairingCharZero : E[N] ×_T E[N] ⟶
  μ_{N,T}` over ℚ-schemes (étale-local trivialisation + finite-flat descent — mathlib
  `Morphisms/FlatDescent` EXISTS; `muN S N`/`muNPointsEquiv` are ALREADY base-general, so the
  μ_{N,T} target is free). Concrete point identification funnels into **T-W7**. T-C0e now = that
  T-relative construction (spec to be cut carefully against KM 2.8/Silverman when T-W7 lands —
  NOT reconstructed from memory, per the v9 statement-drift caution).

### H-lane PHASE-8 terminal (beastmode-H, 2026-07-07, Opus 4.8) — v9 incorporated, lane drained
Session accomplishments (all committed): **T-SG1 DONE** (fixed the prior firing's 2 IsIso-synthesis
errors + committed, green, axiom-audited); **T-SG2 DONE** (Γ₀ cyclicity def-of-record,
CyclicSubgroup.lean, sorry-free); **v9 expert-review integrated & committed**; **T-C0e re-cut per
v9.4** (removed the too-weak field placeholder → EtaleDescent.lean sorry-free; documented the honest
T-relative weilPairingCharZero target).
**Terminal reason — PHASE-8 (all dispatchable H-lane tickets done; blocked/owned ones remain):**
- Critical-path remainder is CLAIMED + actively in-progress by other lanes: **T-W7** group-scheme law
  (beastmode-A, ~37 decls done, scheme-level phase ongoing), **T-B5z** invertible-N étale
  (beastmode-B, in_progress), W3c (Q), D11 (D2). Taking any collides with an active worker.
- ALL remaining H/C items funnel into **T-W7** (the E↔Weierstrass point identification / scheme-level
  group law that the level-functor `map`-memberships and the concrete Weil-pairing values both need) —
  gated on beastmode-A's in-progress work.
- The only gate-free-and-mine work left (T-GG-gen1/gen2 fibre-functor generality) is EXPLICITLY
  deprioritized by the v9 review ("move effort away from generality polishing"; LATE/post-critical-path).
- N≤2 non-rigidity (T-H7) done and PARKED per v9 ("do not re-staff").
**Resume trigger for H-lane**: when T-W7 lands (scheme-level group law), re-audit the `map`-membership
gate (T-A6/A6.δ) and the concrete Weil-pairing values (T-C0d-ii / T-C0e T-relative construction) — both
unblock together, per v8/v9.

### H-lane: N≥3 positive rigidity — [-1]-part (beastmode-H, 2026-07-07, user-directed)
Proved `ModularCurves.gammaFullNaiveProblem_map_negIso_ne_of_three_le` (GammaH.lean) — the POSITIVE
counterpart to `gammaFullNaiveProblem_map_negIso_of_le_two`: for N≥3 invertible, the [-1]
automorphism has NO fixed points on the naive full-level problem (over any object with a nonempty
base). Proof: a fixed structure forces −P=P, −Q=Q → at a geometric point pull P, pull Q are
2-torsion → the subgroup they generate is 2-torsion → but the full-level condition puts all of
E[N]≅(ℤ/N)² inside it (via `torsion_geometricFibre_rank_two`) → 2=0 in ℤ/N → N≤2, contradiction.
Reuses the T-H7 machinery (negIso/pullSection_negHom/exists_geometricPoint/rank-two fibre).
Sorry-FREE; axiom profile IDENTICAL to its T-H7 sibling ([propext,sorryAx,Classical.choice,
Quot.sound] — sorryAx only via the pre-existing gammaFullNaiveProblem.map WIP, no NEW box).
Engineering: whnf-timeout dodged by replacing simp with explicit rws (Pi.smul_apply/cons_val_zero/
zsmul_eq_mul; Submodule.coe_eq_zero/coe_smul; ZMod.intCast_zmod_eq_zero_iff_dvd) — NO heartbeat bump.
SCOPE: this is the generic-automorphism case (Aut(E)={±1}, all j∉{0,1728}) — reviewer v9's requested
"positive rigidity for N≥3". FULL `Rigid` (every automorphism incl. the extra ones at j∈{0,1728})
needs the automorphism group scheme and stays the ⧗KM/T-W7-gated `gammaFullDrinfeld_representable`.

### C-lane: T-C0e weilPairingCharZero — descent + local model LANDED (beastmode-H, 2026-07-07, user-directed)
Reviewer v9 work-order #5 (T-relative char-0 Weil pairing) — new file `WeilPairing/CharZeroDescent.lean`,
ALL decls axiom-CLEAN ([propext,Classical.choice,Quot.sound], ZERO sorryAx), zero warnings.
DELIVERED in two gate-free layers:
- **Descent (the "then descend" half):** `weilPairingCharZero E N p ζ' hcocyc :
  pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N` — descends a local pairing ζ' (on the base
  change of E[N]×_S E[N] along a trivialising fppf cover p:S'→S, valued in the FIXED target μ_{N,S})
  to the DS4 target shape (Basic.lean:42's weilPairing), via `descend_hom_of_effectiveEpi` (stream-DESC
  reuse; fppf⟹EffectiveEpi mathlib instance, base-change-stable Flat/lfp/Surjective on the pulled-back
  cover). Specs `_restrict`/`_over`. Approach-2 geometry (descend along a cover of the SOURCE, fixed
  target μ_{N,S}) — sidesteps the point-level 3-spelling trap (E[N] base change is clean at scheme
  level via `torsion_baseChange_isPullback`).
- **Local model (the "build étale-locally" half, gate-free):** `detFun`/`gl2Both`/`constSchemeMap`
  (+`_comp`/`_π`) and the symplectic pin `detConstMor_gl2Both`: e(g·v,g·w)=e(v,w)·det g on the
  constant (ℤ/N)²-scheme (= v9 review Q6 normalization pin; the change-of-triv cocycle, invariant on
  SL₂). Pure constScheme+ZMod (Matrix.det_fin_two); NO E[N], NO torsion boxes.
HONEST GATING: the descent theorem is axiom-clean because the gated content is its LABELED INPUTS —
the cover exists since E[N] finite étale for N inv (torsionπ_etale ⟸ T-B5 box mulByHom_formallyUnramified),
and (ζ',hcocyc) come from trivialising E[N]/μ_N on the cover + the local det model. WIRING the local
model into ζ' over a concrete étale-local full-level trivialisation (Layer 3) is the point-level
E[N]≅(ℤ/N)² step that funnels into T-W7 (A-lane) — that's what would discharge the DS4 weilPairing sorry
over ℚ-schemes. Field case unchanged (exists_pairingAlgebraHom_of_galoisEquivariant, EtaleDescent.lean).
Commits: d9961638 (descent), + this (local model).

### C-lane: weilPairingCharZero API completion + base-change naturality (beastmode-H, 2026-07-07, user-directed)
Completed the char-0 Weil-pairing API (all axiom-clean, gate-free) in WeilPairing/CharZeroDescent.lean:
- **Weil axioms (combinatorial):** detFun_self (alt e(v,v)=0), detFun_swap (antisym), detFun_add_left/_right
  (bilinear); constSchemeMap_id/_ι (functoriality + points rule); detConstMor_sl2 (SL₂-invariance ⟹
  cocycle vanishes); weilPairingCharZero_unique (∃! descent).
- **μ_N base-change API (reusable):** de-privatised isPullback_muN_baseChange in GroupScheme/MuN.lean
  (proof unchanged, 1-word); named wrapper muNBaseChange g N : muN S' N ⟶ muN S N + _isPullback + _muNπ.
- **Base-change naturality (review Q4 "compatible with arbitrary base change"):** weilPairingSourceBaseChange
  (E_T[N]×_T E_T[N] ⟶ E[N]×_S E[N] via torsion_baseChange_isPullback on each factor) + weilPairingCharZero_baseChange:
  GIVEN cover-level local-pairing compatibility hζ, the T-pairing ≫ (μ_N proj to μ_{N,S}) = (source base change) ≫
  S-pairing. Clean statement (equation in the FIXED target μ_{N,S}, avoids constructing e_T in μ_{N,T});
  proof = epi-cancel + weilPairingCharZero_restrict (hζ propagates cover-local → scheme-level, mirroring _over).
  The local compatibility hζ is an honest hypothesis (analogous to hcocyc); wiring ζ'_T = base-change-of-ζ'
  to DISCHARGE hζ is the same point-level trivialisation step that funnels into T-W7.
Commits: 4f3ab9a9 (axioms+SL₂+uniq), 24a159f8 (constSchemeMap_ι), 41f19f09 (μ_N base change), + this (naturality).


---

## Generic Flatness stream (T-GF*) — owner-funded 2026-07-07, discharges the D-chain's last sorryAx

Source: Stacks 051R (fetched + transcribed; decomposition-genericflatness.md). File:
`ForMathlib/GenericFlatness.lean` (new, upstream-candidate) unless noted. Order:
GF1→GF2→GF3→GF4→GF5→GF6→GF7→NOETH-FLAT1.

### [T-GF1] prime-quotient injection (Stacks 10.62.1 building block)
- **Status**: done · **Claimed**: beastmode-D2, 2026-07-07T16:40Z · **File**:
  ForMathlib/GenericFlatness.lean · **Depends on**: none · **Type**: theorem
- **Statement**: `exists_primeQuotient_injection {R M} [CommRing R][IsNoetherianRing R]
  [AddCommGroup M][Module R M][Nontrivial M] : ∃ p : Ideal R, p.IsPrime ∧
  ∃ f : (R ⧸ p) →ₗ[R] M, Function.Injective f`
- **Proof**: `associatedPrimes.nonempty` → `isAssociatedPrime_iff` (I prime, I = colon ⊥ {x})
  → `toSpanSingleton R M x` has ker = I (mem_colon_singleton) → `I.liftQ … ` injective by
  `ker_liftQ_eq_bot'`. PROVEN in scratch, axiom-clean.

### [T-GF2] extension of free modules is free (Stacks 0516)
- **Status**: done (beastmode-D2 2026-07-07, delegate; `free_of_exact_of_free`, axiom-clean, via lequivProdOfRightSplitExact) · **Depends on**: none · **Type**: theorem
- **Statement**: for a SES `0→A→B→C→0` of R-modules with A, C free (C free ⟹ projective ⟹
  split), B is free. Lean: `Module.Free R A → Module.Free R C → (∃ split) → Module.Free R B`,
  or via `Function.Exact` + `Module.Projective C`. Mathlib: `Module.free_of_...`? survey; likely
  via split ≅ A × C then `Module.Free.prod`. ~30 lines.

### [T-GF3] generic finiteness / Noether normalization over a domain (Stacks 10.115.7)
- **Status**: done-field-core (beastmode-D2 2026-07-07; `exists_noetherNormalization_baseChange` = Noether norm of the generic fibre K⊗S over K, axiom-clean; the spread-down is inside the domain-case box) · **Depends on**: none · **Type**: theorem
- **Statement**: R Noetherian domain, S = domain, finite-type R-algebra ⟹ ∃ 0≠f∈R and
  y₁..y_d ∈ S_f with R_f[y] → S_f finite (i.e. after inverting f, S is finite over a poly
  subring). Mathlib: field-base Noether normalization (`RingTheory/NoetherNormalization.lean`)
  applied to S_K over K=Frac R + spread down. ~100 lines. May itself spawn sub-tickets.

### [T-GF4] support-avoidance annihilation (Stacks 10.40.5)
- **Status**: done (beastmode-D2 2026-07-07, delegate; `exists_smul_eq_zero_of_notMem_support`, axiom-clean, via support_eq_zeroLocus + mem_annihilator) · **Depends on**: none · **Type**: theorem
- **Statement**: N finite R-module, 𝔭 prime, 𝔭 ∉ Module.support N ⟹ ∃ g ∉ 𝔭, g • N = 0
  (g annihilates N). Mathlib: `Module.mem_support_iff_exists_annihilator` + finite ⟹
  ann-determines-support. ~20 lines.

### [T-GF5] generic flatness (Stacks 051R main dévissage)
- **Status**: done-modulo-domain-box (beastmode-D2 2026-07-07, delegate + verified). `exists_generically_free`
  landed: the FULL prime-filtration dévissage PROVEN (via mathlib's
  `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` + GFree.of_exact localization plumbing);
  sorryAx sourced SOLELY from `exists_generically_free_domain` (the domain-case dim induction).
  **DOMAIN-CASE BOX IN FLIGHT** (delegate ae294be5): survey CORRECTED the delegate's over-flagging —
  `MvPolynomial.ringKrullDim_of_isNoetherianRing` (dim k[x]=d) EXISTS, hypersurface-drop exists
  (KrullDimension/Regular.lean), tensor-domain via localization; the ONE real gap = dim-under-integral-ext
  (or use trdeg as the measure). Bounded. · **Depends on**: T-GF1..GF4 · **Type**: theorem
  - **UPDATE 2026-07-07T19:20Z**: domain-case dévissage PROVEN (delegate, verified) modulo ONE
    box `GFDatum` (Noether-normalization data: generic-finiteness descent + free-P-submodule-with-
    finite-torsion-cokernel — genuinely mathlib-absent). Route: TRANSCENDENCE DEGREE measure
    (`trdeg_quotient_prime_lt` + `trdeg_le_of_injective`, NO going-up-dim). Also fixed a latent
    doc-before-omit build error masked by stale olean; builds green from source. GF5 = axiom-clean
    modulo GFDatum. OFF the box-discharge critical path (Tor-free T-LC route doesn't need generic
    flatness); GFDatum is a standalone-completeness box, not a blocker.
- **Statement**: `R Noetherian domain, R→S finite type, M finite S-module ⟹ ∃ 0≠f∈R,
  Module.Free R_f M_f` (equivalently `Module.Flat`). Proof = strong induction on d=dim(S_K)
  via GF1 (reduce M to R⧸𝔮 pieces by noetherian induction) + GF2 (assemble free) + GF3
  (Noether norm) + GF4 (kill the cokernel N, drop dimension). ~150 lines. LARGE — delegate.

### [T-GF6] openness of the flat locus (Stacks 00RC = Thm 10.129.4)
- **Status**: open · **Depends on**: T-GF5 · **Type**: theorem
- **Status**: BLOCKED-ON-FOUNDATION (beastmode-D2 2026-07-07, delegate + verified). Setup
  landed in `ForMathlib/FlatLocus.lean`: `flat_localizedModule_of_flat` (the flat-localization
  ENGINE — R-flat survives localizing at any S-submonoid, axiom-clean, mathlib-worthy),
  `flatLocus_stableUnderGeneralization`, `basicOpen_subset_flatLocus_of_free` (generic-flatness
  neighbourhood, axiom-clean). But **`isOpen_flatLocus` is BOXED** and CANNOT be closed without
  the **LOCAL CRITERION OF FLATNESS** (Stacks 00MK/039A; Matsumura Thm 22.3; EGA IV): the
  generic-flatness→openness reduction needs to reconcile `flat over R⧸𝔭` with `flat over R`,
  which is Tor-theoretic (`Tor₁^R(M, R⧸𝔭) = 0`). **VERIFIED mathlib-absent**: only abstract
  monoidal-category `CategoryTheory/Monoidal/Tor.lean` exists — NO commutative-ring `Tor₁`, NO
  local criterion (grep decisive). EVERY route to 00RC hits this: the classical
  generic-flatness route AND Stacks 00RC's own resolution route (00MH/00MI) both need it. This
  is the TRUE FOUNDATIONAL BOTTOM under the box: box ← 07RF ← 00RC ← **local criterion / commutative
  Tor** — a published-theorem-scale, multi-week+ mathlib-library development (a recognized major
  gap). Generic flatness (GF5, built) does NOT suffice — it doesn't provide the criterion.
  **This is a B3 OFF-TRACK boundary** (see beastmode report). ORIGINAL note follows —
  **Source CONFIRMED (fetched)**: Stacks Thm 10.129.4 (tag 00RC), §10.129 "Openness of the
  flat locus". Statement: R Noetherian, S fp over R, M fp S-module ⟹ `{𝔮 ∈ Spec S : M_𝔮 flat
  over R}` is open. **ROUTE DECISION (source-study finding)**: Stacks 00RC's OWN proof does
  NOT use generic flatness — it uses finite-free-resolutions + the LOCAL FLATNESS CRITERION
  (00MH "freeness from fibre freeness" / 00MI / 00RB), which is ALSO mathlib-absent. We
  instead take the CLASSICAL route via **GF5 (generic flatness 051R, being built)** +
  Noetherian induction: for R a domain GF5 gives flatness on a dense open; over general
  Noetherian R, Noetherian-induct on Spec R (the non-flat locus is closed) applying GF5 to
  each irreducible component mod its generic point. This reuses GF5; do NOT chase the
  resolution/local-criterion route (a separate mathlib-absent foundation). ~150-250 lines.
  LARGE — delegate. NOTE: the classical route needs "flat over a dense open ⟹ ..." glue;
  if that glue is heavy, the resolution route's `Module.Flat` fibre-criterion (00MH/00MI)
  is the fallback and would be its own sub-development.

### [T-GF7] flatness descends in a directed colimit (Stacks 07RF = Lemma 10.168.1(3))
- **Status**: open · **Depends on**: T-GF6 · **File**: ForMathlib/NoethApprox.lean · **Type**: theorem
- **Source CONFIRMED (fetched)**: Stacks Lemma 10.168.1 part (3) (tag 07RF). This is EXACTLY
  the NOETH3 statement: `(R→S,M) = colim (R_λ→S_λ, M_λ)`, R_λ→S_λ fp, M_λ fp over S_λ, M flat
  over R ⟹ M_λ flat over R_λ for all large λ. Proof (fetched, verbatim): descend a base
  presentation `(R₀→S₀,M₀)` with `R₀→R`, `M₀` flat over R₀; the transition maps Ψ_λ become
  isos at large λ; conclude via **Thm 10.129.4 (GF6 / flat-locus openness)**. Discharges the
  `Module.Flat R₀ A₀` sorry in `exists_noetherian_descent_flat` (NoethApprox.lean) directly —
  our NoethApprox R₀ IS the finite stage. ~100-200 lines.

### [T-NOETH-FLAT1] discharge the T-FLAT1-SLICE box
- **Status**: open · **Depends on**: T-GF7 (NOETH3), T-NOETH1, T-NOETH2 · **File**:
  LevelStructure/CartierDivisor.lean · **Type**: theorem
- **Statement**: prove `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` (currently the
  sorried box): descend (R,A,f) to a noetherian stage (NOETH1-3), where Ann(f) is fg, and
  the flat-tensor-exactness argument (Ann⊗κ=0 ∀κ) + Nakayama closes Ann(f)=0. ~150 lines.
  DISCHARGE ⟹ the ENTIRE Drinfeld D-chain is axiom-clean.

---

## Flat-locus / local-criterion stream (T-LC*) — TOR-FREE route (owner-funded 2026-07-07)

Discharges the D-chain's last sorryAx. Source: Stacks 00MH/00MI/00RC/07RF (fetched) +
decomposition-flatlocus.md. **Key finding: NO derived-functor Tor needed** — the fibre
criteria use `Module.Flat.lTensor_exact` (flatness ⟹ Tor₁-vanishing, from the hypothesis) +
Nakayama, all mathlib-present. Order: LC1→LC2→LC3→GF7→NOETH-FLAT1.

### [T-LC1] freeness from fibre freeness (Stacks 00MH) — THE MAKE-OR-BREAK
- **Status**: DONE (beastmode-D2 2026-07-07T19:40Z, verified) — `Module.free_of_flat_of_fibre_free` in ForMathlib/LocalCriterion.lean, AXIOM-CLEAN, TOR-FREE. ROUTE VALIDATED end-to-end; B3 'needs Tor' REFUTED. Landed the LOCAL form (R,S local); prime-localized form for T-LC3 = localization bookkeeping. Snake engine `lTensor_injective_of_exact_of_exact_of_rTensor_injective` + `rTensor_preserves_injective_linearMap` + Nakayama. Fibre = M⧸(𝔪S·⊤) free over S⧸𝔪S (NOT residue field — that's vacuous, delegate caught + counterexampled).
- **PRIOR-Status**: in_progress · **Claimed**: beastmode-D2, 2026-07-07T18:10Z (Opus delegate
  a42306399 → ForMathlib/LocalCriterion.lean). Validates the whole Tor-free route: if
  the Nakayama + `Module.Flat.lTensor_exact` proof lands, the box chain opens Tor-free.
- **File**: ForMathlib/LocalCriterion.lean ·
  **Depends on**: none · **Type**: theorem
- **Statement**: `R→S` comm rings, M finite S-module, 𝔮 : PrimeSpectrum S, 𝔭 := 𝔮.comap,
  M flat over R (at 𝔮), `M ⊗_R κ(𝔭)` free over κ(𝔭) ⟹ `LocalizedModule 𝔮.primeCompl M` free
  over `Localization.AtPrime 𝔮`. (Design the exact Lean spelling for "fibre" and "at 𝔮".)
- **Proof sketch**: (1) Fibre `M⊗_R κ(𝔭)` free rank r; lift a basis to `φ : S_𝔮^r → M_𝔮`,
  iso mod 𝔮 by construction (Nakayama: `eq_bot_of_le_smul_of_le_jacobson_bot` for surjectivity).
  (2) `K = ker φ`. M flat over R ⟹ `0→K→S_𝔮^r→M_𝔮→0` stays exact after `⊗_R κ(𝔭)`
  (`Module.Flat.lTensor_exact` / `rTensor_preserves_injective_linearMap`). (3) `M_𝔮⊗κ(𝔭) ≅ κ^r`
  and `φ⊗κ` iso ⟹ `K⊗_R κ(𝔭) = 0` ⟹ `K = 𝔭·K ⊆ 𝔪_𝔮·K`. (4) K fg (S noeth) ⟹ Nakayama ⟹ K=0
  ⟹ φ iso ⟹ M_𝔮 free.
- **Mathlib lemmas**: `Module.Flat.lTensor_exact`, `rTensor_preserves_injective_linearMap`,
  `RingTheory.Nakayama.eq_bot_of_le_smul_of_le_jacobson_bot`, `Module.free_of_isLocalizedModule`,
  `LocalizedModule.*`, `IsScalarTower`. All #check-confirmed present.
- **Sources**: Stacks 00MH (Lemma 10.129.1); Matsumura *CRT* Thm 22.5. Tor-FREE.
- **Generality**: `[CommRing R] [CommRing S] [Algebra R S] [Module.Finite S M]`, S noetherian
  (or Module.Finite for the Nakayama K-fg step).

### [T-LC2] exactness/flatness from fibres (Stacks 00MI/00RB)
- **Status**: open · **Depends on**: T-LC1 · **Type**: theorem
- **Statement**: a bounded complex of finite free S-modules, flat over R and exact on the
  fibre κ(𝔭), is exact near 𝔮 with flat cokernel. (Companion criterion assembling LC1 along a
  resolution.) Exact Lean form designed at execution.
- **Proof sketch**: induct down the resolution applying T-LC1 at each stage (fibre-exact +
  flat ⟹ the boundary maps have free cokernels near 𝔮), Nakayama + flat-tensor-exactness.
- **Sources**: Stacks 00MI (10.129.3), 00RB. Tor-free.

### [T-LC3] openness of the flat locus (Stacks 00RC) — discharge isOpen_flatLocus
- **Status**: PARTIAL (beastmode-D2 2026-07-07T20:30Z) — `isOpen_flatLocus` SORRY-FREE, reduced to
  ONE box `isConstructible_flatLocus` (flat locus constructible) via the mathlib openness criterion +
  proven generization-stability. HONEST ROADMAP: constructibility needs T-LC2 (00RB/00MI, "flatness
  from fibre exactness" — the OTHER direction from T-LC1's "freeness from flatness") + finite-free-
  resolution infra (00LP existence, 00HM syzygy-flatness), all mathlib-absent (surveyed) but TOR-FREE.
  ~several hundred lines resolution-level. T-LC1 alone insufficient (confirmed).
  - **UPDATE 2026-07-07T21:30Z (delegate + verified)**: DECISIVE — flat locus generization-stable
    ⟹ **constructible ⟺ open** (no lightweight constructibility shortcut; full 00RC content
    unavoidable). `isConstructible_flatLocus` + `isOpen_flatLocus` now BOTH PROVEN (NoetherianSpace
    ⟹ open⟹retrocompact⟹constructible). SINGLE remaining box collapsed to
    `exists_basicOpen_subset_flatLocus_of_mem` = LOCAL openness at a flat point (00RC true content).
    `#print axioms isOpen_flatLocus` = standard three + sorryAx via THAT box only. ROADMAP for the box
    (verified vs Stacks 00RC source): finite free resolution (00LP) + poly-ring reduction + finite
    global dimension of κ(𝔭)[x] + **Buchsbaum-Eisenbud exactness (00N1)** + fibre-exactness (00RB) +
    cokernel-flat (00MI) — ALL mathlib-absent, TOR-FREE (T-LC1 00MH + lTensor_exact + Nakayama +
    resolutions). Substantial (~500-800 lines, several hard classical homological lemmas) but bounded.
    T-LC2 = 00RB/00MI; NEW sub-tickets needed: 00LP (finite free resolutions of fp modules), poly-ring
    global dimension, Buchsbaum-Eisenbud 00N1.
- **PRIOR-Status**: open · **Depends on**: T-LC1, T-LC2 · **File**: ForMathlib/FlatLocus.lean ·
  **Type**: theorem
- **Statement**: fill the boxed `isOpen_flatLocus` in FlatLocus.lean.
- **Proof sketch**: EITHER (i) resolution route: finite free resolution of M (M fp), apply
  T-LC2 to show flatness is an open condition at each 𝔮 (a basic-open nbhd of every flat
  point); OR (ii) constructible route: flat locus is `IsConstructible` (T-LC1 + generic-flatness
  neighbourhood `basicOpen_subset_flatLocus_of_free` + Noetherian induction over Spec S) then
  `PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible` + the proven
  `flatLocus_stableUnderGeneralization`. Pick the cleaner.
- **Mathlib lemmas**: `PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`,
  `isConstructible_basicOpen`, `IsConstructible.{union,inter,sdiff,iUnion}`, resolution API.
- **Sources**: Stacks 00RC (Thm 10.129.4).

### [T-GF7] flatness descends in a directed colimit (Stacks 07RF) — discharge NOETH3
- **Status**: open · **Depends on**: T-LC3 · **File**: ForMathlib/NoethApprox.lean · **Type**: theorem
- **Statement**: fill `exists_noetherian_descent_flat`'s `Module.Flat R₀ A₀` sorry.
- **Proof sketch**: Stacks 07RF (fetched): descend a base presentation with M₀ flat over R₀;
  transition maps Ψ_λ iso at large λ; conclude via T-LC3 (00RC). Our NoethApprox R₀ IS the stage.
- **Sources**: Stacks 07RF (Lemma 10.168.1(3)).

### [T-NOETH-FLAT1] discharge the T-FLAT1-SLICE box
- **Status**: open · **Depends on**: T-GF7, T-NOETH1, T-NOETH2 · **File**: LevelStructure/CartierDivisor.lean
- **Statement**: prove `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` (the box).
- **Proof sketch**: descend (R,A,f) to the noeth stage (NOETH1/2 done + T-GF7 for the flat
  hypothesis), where Ann(f) is fg; flat-tensor-exactness gives Ann(f)⊗κ=0 ∀κ; Nakayama ⟹
  Ann(f)=0. ⟹ **entire Drinfeld D-chain axiom-clean.**

## G-lane claim (beastmode-P2, 2026-07-07): T-G3 aut_trivial_of_fullLevel

- **Claiming T-G3** (`aut_trivial_of_fullLevel`, Groupoid.lean:84; GME 2.6.4 Aut-computation,
  transcribed §B9 of decomposition-gme2.md). UNCLAIMED per H-lane note L5388; parked by
  beastmode-H (funnelled to T-W7 spine). **Claimed**: beastmode-P2, 2026-07-07, in_progress.
- **Scope (honest, post-decomposition read):** the FULL theorem is the rigidity of level
  structures over a base `S` — it needs elliptic-curve **endomorphism theory over `S`**:
  the degree map `deg : End(E/S) → ℤ` as a positive quadratic form, its polar/trace form,
  the dual isogeny (§B8: `fᵗ∘f = [deg f]`, T-RED0 reduced-base transfer, T-NORM0 norm of
  pushforward), and the Hasse bound `tr(f)² ≤ 4·deg f` (§B9, fibrewise). Anchor for the
  field case: HasseWeil `Foundation/DegreeQuadraticForm.lean` + `HasseBound.lean`. This is a
  genuine multi-piece infrastructure build; rigidity-reduction (fibrewise→global over a base
  with nilpotents) is adjacent to fable-P4's GIT engine.
- **Decomposition (sub-tickets):**
  - **[T-G3a]** *engine core (GME 2.6.4 arithmetic)* — pure ℤ: given `n ≥ 3`, `d = deg g ≥ 0`,
    `t = tr g`, the linear relation `n·t + n²·d = 0` (from `deg ε = 1`) and the discriminant
    bound `t² ≤ 4·d`, conclude `d = 0`. **SELF-CONTAINED, provable NOW.** ← building first.
  - **[T-G3b]** `End(E/S)` as a (non-commutative) ring with `deg : End → ℤ` and the quadratic
    expansion `deg(1 + n•g) = 1 + n·tr g + n²·deg g`. GATED on dual-isogeny infra (§B8).
  - **[T-G3c]** fibrewise Hasse bound `tr(g)² ≤ 4·deg g` on `End(E/S)`. GATED on §B9 + HasseWeil
    field-case transfer (T-RED0).
  - **[T-G3d]** divisibility: `e : E ≅ E` fixing a naive full level-`N` structure ⟹ the
    endomorphism `ε = e.hom - 1` is `N`-divisible in `End(E/S)`, `ε = N•g`. Needs the E[N]-action
    of `End` + `IsNaiveFullLevel` generation.
  - **[T-G3e]** rigidity reduction: `deg(e.hom) = 1 ∧ (e.hom = 1 on the generic/all fibres) ⟹
    e = Iso.refl`. Reuses `hom_ext_of_forall_specPoint` (PointsDictionary) / fable-P4 rigidity.
  - **assembly:** T-G3 = T-G3d ⟹ `ε = N•g`; T-G3b gives `deg(e.hom)=deg(1+N•g)=1+N·tr g+N²·deg g`;
    `e.hom ∈ Aut ⟹ deg = 1` ⟹ T-G3a ⟹ `deg g = 0` ⟹ (deg pos-def) `g = 0` ⟹ `ε = 0` ⟹
    `e.hom = 1` ⟹ (T-G3e) `e = refl`.

### T-G3 landing (beastmode-P2, 2026-07-07) — done-modulo-boxes at the KM-Ch2 gated frontier
- **T-G3a DONE** — `gme_deg_trace_forces_zero` (Groupoid.lean:88): the pure-ℤ GME 2.6.4 engine
  (`n≥3, d=deg g≥0, n·t+n²·d=0, t²≤4d ⟹ d=0`) proven + **axiom-clean** `[propext, Classical.choice,
  Quot.sound]`. The one piece of GME 2.6.4 outside the KM gate (no EC content). Reused by T-H5.
- **`aut_trivial_of_fullLevel` PROVEN** (iso-plumbing) — `Iso.ext ∘ HomOver.ext` reduces
  `e = Iso.refl E` to the scheme-morphism equation `e.hom.hom = 𝟙 E.E` (`(Iso.refl E).hom.hom = 𝟙`
  by rfl; `HomOver.ext` uses only the `hom` field). Content factored into the named box below.
- **T-G3 core box** `aut_hom_eq_id_of_fullLevel` (Groupoid.lean:120, sorried) — clean statement
  `e.hom.hom = 𝟙 E.E`, gated proof. Its docstring records the full GME reduction wiring T-G3a +
  the gated infra (T-G2 additivity [Rigidity.lean, A-lane]; T-G3b deg quad-form; T-G3c Hasse;
  T-G3d divisibility). **GATE**: T-G3b/c/d = End(E/S)/deg/dual-isogeny/Hasse = **KM Chapter 2**,
  under the binding do-not-formalize-from-memory gate — may NOT be closed from memory; stated
  from §B8/§B9 quotes. Commits f43f76ef (G3a), 78adbfd3 (board), + reduction commit.
- **Frontier reached**: T-G3's non-gated content is exhausted (G3a + plumbing). Closing the box
  requires either KM-Ch2 text (gate) or T-G2 (another lane's sorried rigidity). G6 → next ticket.

### G-lane PHASE-8 terminal (beastmode-P2, 2026-07-07, Opus 4.8) — cross-stream T-G3 landed
Session accomplishment (committed): **T-G3 landed done-modulo-boxes** — the cross-stream ticket
the owner directed ("work on other streams"). **T-G3a** `gme_deg_trace_forces_zero` PROVEN +
axiom-clean (the pure-ℤ GME 2.6.4 engine, reusable by T-H5); **`aut_trivial_of_fullLevel` PROVEN**
via iso-plumbing (`Iso.ext ∘ HomOver.ext`); geometric content in one precise source-quoted box
`aut_hom_eq_id_of_fullLevel` (T-G3b–e decomposed on board). Build green (3087 jobs).
**Terminal reason — PHASE-8 (dispatchable G-lane work done; blocked/owned remainder):** mirrors the
H-lane PHASE-8 (L5707) exactly.
- T-G3's remaining content = `End(E/S)`/`deg`/dual-isogeny/Hasse = **KM Chapter 2**, under the binding
  do-not-formalize-from-memory gate (may NOT close from memory); + **T-G2** additivity (Rigidity.lean,
  fable-P4's active lane). Both blocked/owned.
- Every other startable ticket is CLAIMED + in-progress by another lane (T-W7=A, T-B5z=B, W3c=Q,
  D11/D-stream=D2, Rigidity/T-G2=fable-P4) — one-worker-per-lane; taking any collides.
- The only gate-free-and-mine option (T-GG-gen1/gen2) is coordinator-deprioritized (v9 "move effort
  away from generality polishing"; LATE/post-critical-path).
**Resume trigger for G-lane**: when the KM Ch.2 text lands in `refs/ModularCurves/` (degree/dual-isogeny/
Hasse), OR when T-G2 (`isMonHom_of_one_comp_eq`) + a `deg` API land — then close the box
`aut_hom_eq_id_of_fullLevel` via the reduction already documented in its docstring (wiring T-G3a).

### KM-text gate: evidence-based re-assessment (beastmode-P2, 2026-07-07)
KM book confirmed present at `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf` (since 6 Jul).
Read KM §1.1 (Cartier divisors), §1.4 (exact order / cyclic subgroups), §1.5–1.6 (A-structures/
generators, representability) in full. **Finding: the text satisfies the *statement-accuracy* half of
the do-not-formalize gate (quotes already transcribed in the docstrings), but does NOT unblock proof
work — every gated KM-Ch1 level-structure sorry bottlenecks on deep-AG prerequisites that KM itself
CITES rather than proves, and mathlib lacks:**
- **Lemma 1.4.2** (`BB-DELIGNE`, `smul_eq_zero_of_factors`): "exact order N ⟹ NP=0" — KM's proof is
  verbatim *"any finite locally free commutative group-scheme of rank N is known to be killed by N
  (cf. [Oort–Tate])"*. Oort–Tate is absent from mathlib → still boxed.
- **Prop 1.6.4** (A-Str étale for N invertible) + **Lemma 1.4.4 (3)⟺(4)** (`T-D6b/c`, `T-D7-bridge`,
  ExactOrder.lean:183/195/226): rest on *"[N]:C→C is étale when N invertible"* (= `BB-DIFF`,
  beastmode-B confirmed mathlib-absent: no invariant differential / division-polynomial↔point bridge)
  + the finite-locally-free discriminant/trace-form étale criterion + the **fibre-model bridge**
  (D_k = Σ[aP_k] on the geometric fibre curve) = **T-W7** (beastmode-A's active work).
- So the KM Ch1 theory funnels into T-W7 + BB-DIFF + BB-DELIGNE, exactly like the H/C lanes. The book
  doesn't change the critical path.
**One non-gated substrate piece surfaced**: the general "finite locally free morphism is étale ⟺ all
geometric fibres are étale (⟺ discriminant a unit)" criterion (feeds T-D6c/T-D7-bridge). Buildable as
ForMathlib, but is *substrate not a ticket-closer* — the ModularCurves sorries still need the T-W7
fibre-model on top to identify D_k with Σ[aP_k]. Recorded for whoever builds the discriminant layer.

---

## DEV-1/DEV-2 stream (T-DEV*) — the D-chain's last two boxes, TOR-FREE (owner-funded 2026-07-07)

Source: decomposition-devs.md + Stacks 00RC/00LP/00N1/07RF. mathlib foundation richer than earlier
delegates assumed (proj-dim theory + AffineTransitionLimit). Order: DEV1a→DEV1b→DEV1c ‖ DEV2a→DEV2b.

### [T-DEV1a] Hilbert syzygy — finite global dimension of a polynomial ring over a field — MAKE-OR-BREAK — VALIDATED
- **Status**: DONE-modulo-[T-DEV1a-prime] · commit 8918fe97 · **File**: ForMathlib/HilbertSyzygy.lean (build green)
- **VERDICT (2026-07-07): proj-dim route WORKS — NO Buchsbaum-Eisenbud.** Landed `HilbertSyzygy.hasProjectiveDimensionLE_of_field
  (K field) (n) (M : ModuleCat (MvPolynomial (Fin n) K)) : HasProjectiveDimensionLE M n` (stronger than target: no [Finite]).
  Axiom-clean: base case + `hasProjectiveDimensionLE_extendScalars` (base-change half). One isolated sorry → [T-DEV1a-prime].
- **BRIDGE CONFIRMED (de-risks DEV1c)**: `ShortComplex.Exact.moduleCat_of_range_eq_ker` + `moduleCat_exact_iff_function_exact`
  + `ModuleCat.projective_of_free` connect DEV1b's CONCRETE `range_d_succ` to categorical `hasProjectiveDimensionLT_X₃_iff`
  (syzygy-shifting) — so NO separate categorical-ProjectiveResolution packaging (no T-DEV1b') is needed.

### [T-DEV1a-prime] characteristic short exact sequence (isolated HilbertSyzygy box, ~L146)
- **Status**: in-progress (dispatched 2026-07-07) · **File**: ForMathlib/HilbertSyzygy.lean · **Depends on**: none · **Type**: lemma
- **Statement**: `exists_characteristicShortExact` — `0 → R[X]⊗_R M →^{X⊗1−1⊗X} R[X]⊗_R M →^{counit} M → 0` as `ShortComplex.ShortExact`.
- **Proof sketch**: transport via `PolynomialModule.polynomialTensorProductLEquivPolynomialModule` to `ℕ→₀M`; φ=shift−X-action
  (injective by leading coeff; range=ker by downward support induction), ε=counit. ~100-150 lines. ⟹ HilbertSyzygy fully clean.

### [T-DEV1a-OLD] (superseded — original sketch below, kept for the trdeg-recursion idea)
- **Statement**: for a field K, a finite `MvPolynomial (Fin n) K`-module has projective dimension ≤ n
  (`HasProjectiveDimensionLE`). Design exact spelling vs mathlib `projectiveDimension`/`HasProjectiveDimensionLE`.
- **Proof sketch**: induction on n. Base n=0: K field ⟹ finite module free ⟹ pd 0. Step: `MvPolynomial (Fin (n+1)) K
  = (MvPolynomial (Fin n) K)[X]`; the last variable X is a regular element; `projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`
  raises pd by 1; combine with the IH via `hasProjectiveDimensionLE_iff_forall_primeSpectrum` / the poly-extension pd bound.
- **Mathlib lemmas**: `projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`, `hasProjectiveDimensionLT_of_forall_finite`,
  `hasProjectiveDimensionLE_iff_forall_primeSpectrum`, `MvPolynomial.finSuccEquiv`/`optionEquivLeft`, `Polynomial` regular X. (#check at execution.)
- **Sources**: Stacks Hilbert-syzygy tag; Weibel *Homological Algebra* §4.3. Validates the proj-dim route for DEV-1.

### [T-DEV1b] finite free resolution of an fp module over a Noetherian ring (Stacks 00LP) — DONE
- **Status**: DONE · commit d81a0918 · AXIOM-CLEAN · **File**: ForMathlib/FiniteFreeResolution.lean (build green 8614 jobs)
- Landed: `Module.exists_finite_free_surjective_finite_ker` + explicit resolution (`aug`,`d n`,`range_d_succ`,`d_comp_d`,
  `syzygy n`,`finite_syzygy n`) with syzygies as genuine `Submodule S (Fin b → S)`. Consumed by DEV1c via CONCRETE form.
- **Statement**: M fp over noetherian S ⟹ a resolution by finite free S-modules (inductive syzygy chain / `CochainComplex`).
- **Proof sketch**: `S^n ↠ M` (fp gives generators); kernel fg (S noeth ⟹ submodule of fg is fg); iterate. API: the n-th syzygy is finite.
- **Mathlib lemmas**: `Module.Finite`, `Submodule.fg_of_...` (noeth), `IsNoetherian`, `Module.FinitePresentation`. ~100 lines.
- **Sources**: Stacks 00LP.

### [T-DEV1c] local openness at a flat point — MAKE-OR-BREAK: FAILED (proj-dim does NOT avoid Buchsbaum-Eisenbud)
- **Status**: box→isolated residual (commit 7b15980a); TRUE residual = `flatLocus_spreads_of_flat` (00MK+00RB) · **File**: ForMathlib/FlatLocus.lean:199 · **Type**: theorem
- **VERDICT (2026-07-07): the projective-dimension route is REFUTED.** Airtight counterexample: R=k[t], S=k[t,x], M=S/(xt) —
  first syzygy K₁=(xt)≅S FREE everywhere, yet M NOT R-flat on V(t) (t·x=0, x≠0). So "Kₙ free on D(g) ⟹ M flat on D(g)" is FALSE;
  syzygy-freeness ≠ fibre-EXACTNESS. Flatness needs the local criterion of flatness (00MK) + fibre-exact-locus openness (00RB/00MI),
  classically via Buchsbaum-Eisenbud (00N1). None of 00MK/00RB/00MI/00N1 (nor Module.depth/Auslander-Buchsbaum/dévissage) in mathlib.
  DEV1a (HilbertSyzygy) is now ORPHANED from the D-chain (still a valid standalone result); DEV1b likewise.
- **OWNER DECISION (2026-07-08): ROUTE A FUNDED** (Buchsbaum–Eisenbud / local flatness criterion). Full source-faithful
  tree in `decomposition-buchsbaum-eisenbud.md`; skeleton `ForMathlib/BuchsbaumEisenbud.lean` (d70a8209). Verdict: full
  00N1 REQUIRED (Ext-support only handles the depth-openness sub-step, mathlib already has it via of_flat_of_isBaseChange).
- **B-E EXECUTION STATUS (2026-07-08, beastmode-D2):**
  - **[T-FIT] DONE, AXIOM-CLEAN** — `ForMathlib/FittingIdeals.lean` (split from skeleton, committed via sibling sweep 266479a6).
    Full minor-ideal API: `LinearMap/Matrix.idealOfMinors`, antitone, base-change `idealOfMinors_map`, McCoy over a field
    `idealOfMinors_eq_bot_iff_rank_lt`, locus bridge `idealOfMinors_le_ker_iff_rank_lt`, hard McCoy `exists_det_submatrix_ne_zero_of_le_rank`
    (delegate PROVED it — no residual). All 14 decls [propext,Classical.choice,Quot.sound].
  - **[T-GRADE] DONE-modulo-[T-GRADE-REES]** — `ForMathlib/Grade.lean`. `gradeGE_localize` AXIOM-CLEAN. **STATEMENT FIX**: both
    conclusions carry `∨ (I.map…)=⊤` (mathlib IsRegular needs S/(rs)≠0 so gradeGE can't hold for ⊤; counterexample S=k[x],I=(x)
    localise→field k(x)); this IS the Stacks 10.129.2 disjunction + exactly what buchsbaumEisenbud_acyclic consumes. `isOpen_gradeGE_locus`
    modulo one isolated Rees/Ext bridge `gradeGE_or_top_locus_eq_iInter_compl_zeroLocus`. [T-GRADE-REES] dispatched to close it.
  - **[T-BE] MAKE-OR-BREAK RESOLVED** — `buchsbaumEisenbud_acyclic` PROVEN over two named cores (own sorry GONE, `⟨be_forward,be_backward⟩`).
    First pass found+machine-refuted the statement off-by-one (`φ i`→`φ(i-1)`, FIXED 9f677b4e). Second pass: assembled the iff,
    **PROVED the McCoy base case of BE.3** (`det_submatrix_smul_eq_zero` + `injective_of_maxMinors_nonZeroDiv`) and wired it in
    (discharges the top exactness spot), + all trivial cases + dispatchers + regular-element/prime-avoidance recipe.
    **Residual = TWO precisely-documented depth cores** (BuchsbaumEisenbud.lean, committed via sibling sweep):
    - `be_forward_core` (L187): exact ⟹ grade conditions. Needs **Auslander–Buchsbaum + grade-via-primes** (Stacks 00N1 (1)⟹(2)(b)).
    - `be_backward_core` (L272, deep interior rk(i+1)≠0∧rk(i+2)≠0): conditions ⟹ exact. Needs **Peskine–Szpiro acyclicity** (00N1 (2)⟹(1), 0AVQ).
    These need the **depth-theory layer** route A explicitly funded ("Module.depth + Auslander–Buchsbaum from scratch") — the genuine
    frontier, now cleanly isolated. Foundations present: grade/regular-seq (Grade.lean), grade⟺Ext (T-REES Rees), McCoy (T-FIT). → [T-DEPTH] planning.
  - **[T-REES + Ext-localization] DONE, AXIOM-CLEAN** (fbc6e376) — the ENTIRE grade-openness chain is sorry-free/axiom-clean
    (`isOpen_gradeGE_locus`: [propext,Classical.choice,Quot.sound]). Two classical theorems mathlib lacked, both PROVEN:
    (B) Rees grade⟺Ext-vanishing over S_𝔮 (Grade.lean ReesLocal); (A) **flat base change for higher Ext** — NEW
    `ForMathlib/BaseChangeExt.lean` (~379 lines, `isLocalizedModule_mapExt` by induction, n+1 five-lemma dévissage on the
    localized Ext LES; beat a Localization instance-diamond without maxHeartbeats). SECOND of T-RB's 3 inputs done (McCoy✓ grade-openness✓).
  - **[T-DEPTH] DECOMPOSED — TRACTABLE, no wall** (`decomposition-depth.md`, skeleton Depth.lean+Acyclicity.lean committed via sibling sweep).
    Route COLLAPSED (3 adversarial corrections): **(A) acyclicity lemma is Stacks 00N0 NOT 0AVQ** (0AVQ=torsion-free, mis-cited);
    **(B) Auslander–Buchsbaum NOT needed** by either core (00N1 forward runs via assoc-primes+nzd+00MZ, no pd/AB); **(C) depth⟺Ext heart
    = `Grade.rees_core` ALREADY PROVEN for general M**. Minimal API: HasDepthGE + 00LW(=rees_core) + 00LX ses1/2/3 (Ext-LES) + 00LD + depth-free.
    ~1100-1600 NEW LOC, no AB/Tor. **DONE AXIOM-CLEAN: Depth.lean (d6bec711, all 8 leaves incl. ses2/3 via Ext-LES),
    Acyclicity.lean (67322a63 00MZ+00MYW [00MZ over-claim fixed: spots≥2], 81c4aa7e 00N0 make-or-break — the Peskine-Szpiro
    acyclicity lemma, closed via syzygy descent + disjunctive depth≥m+1∨Subsingleton invariant).** THREE skeleton stmt bugs
    caught by counterexample this arc (T-BE off-by-one, T-GRADE unit-ideal, 00MZ bottom-spot). RUNNING: [a6df153d] be_forward_core.
    NEXT (after be_forward_core): be_backward_core (consumes 00N0) → both B-E cores DONE → buchsbaumEisenbud_acyclic clean → T-RB + bookkeeping → T-FINAL.
  - **GATED** (BuchsbaumEisenbud.lean, split for parallel when core-closing): T-DEVISSAGE/T-ME/T-MI/T-REDUCEP (Tor-free), T-RB (⟸ T-BE+T-FIT+T-GRADE), T-FINAL.
- **ROUTE OPTIONS for `flatLocus_spreads_of_flat`** (each multi-week — A chosen):
  (A) develop 00MK local flatness criterion + 00RB fibre-exact openness / 00N1 Buchsbaum-Eisenbud (most general/reusable, largest);
  (B) route (ii): flat locus CONSTRUCTIBLE via generic flatness GF5 (needs GFDatum/051R) + Noeth induction, then open via 00I0
      (sidesteps this box, fills isOpen_flatLocus differently — but T-LC3 earlier found constructible⟺open so may not be cheaper);
  (C) CONSOLIDATE: accept the D-chain discharged to this minimal set of named registered boxes (WIP markers, AINTLIB-tolerant).
- **DOWNSTREAM IMPACT**: T-00R6 (colimit flat descent) needs isOpen_flatLocus ⟹ transitively needs `flatLocus_spreads_of_flat`;
  T-FLAT1-STAGE needs T-00R6. So the ENTIRE FLAT1-box axiom-cleanliness now rests on `flatLocus_spreads_of_flat` (00MK+00RB).
- **Statement**: the boxed lemma in FlatLocus.lean (each flat point has a basic-open nbhd in the flat locus).
- **Proof sketch**: finite free resolution (DEV1b) of M; at a flat 𝔮 over 𝔭, the fibre `M⊗κ(𝔭)` over `S⊗κ(𝔭) ≅ κ(𝔭)[x]`
  has finite proj dim (DEV1a) ⟹ the syzygy `K_d` at d=gldim is fibre-free; K_d also R-flat (`Module.Flat.lTensor_exact` +
  the resolution flat) ⟹ `(K_d)_𝔮` free over `S_𝔮` by T-LC1 (00MH) ⟹ the truncated finite free complex is fibre-exact on a
  basic-open nbhd ⟹ M flat there. MAKE-OR-BREAK: if the "fibre-exact ⟹ exact near 𝔮" step needs Buchsbaum-Eisenbud (00N1)
  beyond the proj-dim/T-LC1 toolkit, SPAWN [T-DEV1b'] 00N1. ~200-300 lines.
- **Mathlib lemmas**: T-LC1 `Module.free_of_flat_of_fibre_free`, `Module.Flat.lTensor_exact`, `isConstructible_basicOpen`,
  the resolution API (DEV1b), `Localization.AtPrime`. **Sources**: Stacks 00RC.

### [T-DEV2a/2b] exists_flatLocus_univ_stage (07RF geometric box) — DONE, residual isolated to 00R6
- **Status**: DONE-modulo-[T-00R6] · commit e037338a · **File**: ForMathlib/NoethApprox.lean (build green 8616)
- Box `exists_flatLocus_univ_stage` sorry GONE. Assembled from `flatLocus_eq_univ_of_flat` (PROVEN axiom-clean,
  converse of flat_of_flatLocus_univ) + the isolated residual `exists_subalgebra_flat_baseChange` (= T-00R6).
- **STRUCTURAL FINDING**: naive openness+quasi-compactness has an IMAGE GAP (`Spec(R⊗A₀)→Spec(Rᵢ⊗A₀)` non-surjective,
  ℤ[1/n]→ℚ), so fixed-space `elim_directed_cover` gives only ψ⁻¹(U)=univ, never U=univ. Honest route = cofiltered
  limit of spectra. `exists_noetherian_descent_flat` axioms sorryAx ← 00R6 only.

### [T-00R6] colimit flat descent — fill `exists_subalgebra_flat_baseChange` (Stacks 00R6 = 10.128.3) — LAST HARD CORE
- **Status**: open (dispatch after DEV1c lands so isOpen_flatLocus is clean) · **File**: ForMathlib/NoethApprox.lean:215 · **Depends on**: isOpen_flatLocus (⟸ DEV1c), AffineTransitionLimit · **Type**: theorem
- **Statement**: `Module.Flat R (R⊗[R₀]A₀) → ∃ R₁ (h:R₀≤R₁), IsNoetherianRing R₁ ∧ Module.Flat R₁ (R₁⊗[R₀]A₀)` — flatness of the
  colimit descends to a finite fg-ℤ stage. THE SHARED LEAF: FLAT1's `sliceAux_exists_noetherianStage` also needs it (for A and A/(f)).
- **Proof sketch (cofiltered-limit-of-spectra, avoids the image gap)**: the NON-flat locus `Zᵢ ⊆ Spec(Rᵢ⊗A₀)` is CLOSED
  (complement of `isOpen_flatLocus` over the Noetherian `Rᵢ`, ⟸ DEV1c); `Spec(R⊗A₀) = lim_i Spec(Rᵢ⊗A₀)` as a cofiltered
  limit of spectral spaces; the non-flat locus is limit-compatible (`Z = lim Zᵢ`, flatness base-changes); `M` flat over R
  ⟹ `Z = ∅` ⟹ by AffineTransitionLimit `exists_mem_of_isClosed_of_nonempty'` (Stacks 01Z3: a cofiltered limit of nonempty
  closeds is nonempty, contrapositive) some `Zᵢ = ∅` ⟹ `Rᵢ⊗A₀` flat over `Rᵢ`. Wire `Spec(R⊗A₀)` into the AffineTransitionLimit
  cone (CT plumbing, engine present). ~250-450 lines, substantial but BOUNDED (not B3). Closing it ⟹ DEV-2 clean.
- **Mathlib**: `isOpen_flatLocus`/`flat_of_flatLocus_univ`/`flatLocus_eq_univ_of_flat` (ours), `AffineTransitionLimit`
  (`Scheme.nonempty_of_isLimit` 01Z2, `exists_mem_of_isClosed_of_nonempty'` 01Z3, `exists_map_eq_top`/`exists_preimage_eq` 01Z4),
  `Module.Flat.iff_forall_exists_factorization`. **Sources**: Stacks 00R6/10.128.3, EGA IV 11.2.6.

### [T-NOETH-FLAT1] discharge the T-FLAT1-SLICE box — DONE (2026-07-07, beastmode-D2), reduced to one leaf
- **Status**: DONE-modulo-T-FLAT1-STAGE · **File**: LevelStructure/CartierDivisor.lean · commit c0ba1428
- `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`: own sorry GONE; 9 helpers inserted; noeth-stage
  argument (Part I Tor-free homology `sliceAux_tmul_ann_subsingleton` + Part II support/Nakayama
  `sliceAux_ann_subsingleton` + core `sliceAux_nzd_of_isNoetherianRing`) all AXIOM-CLEAN
  ([propext,Classical.choice,Quot.sound]). Box axioms = [propext,sorryAx,Classical.choice,Quot.sound].
- **The one residual leaf** is the new box below, T-FLAT1-STAGE. GF7 `exists_noetherian_descent_flat`
  descends only A's flatness — the FLAT1 datum needs MORE (A/(f)-flatness + hfib + relation reflection),
  so the delegate correctly isolated a self-contained spreading box rather than routing through GF7.

### [T-FLAT1-STAGE] fill `sliceAux_exists_noetherianStage` (EGA IV 11.2.6 / Stacks 07RF, FLAT1 datum spreading)
- **Status**: open · **File**: LevelStructure/CartierDivisor.lean (private, ~L1957) · **Depends on**: T-DEV2a (07RF core), T-FLAT1-INJ · **Type**: theorem
- **Statement**: given R→A fp with (f) such that A/(f) is R-flat and ·f is fibrewise-injective (hfib), plus
  a relation f·a=0, descend the whole datum to a fg-ℤ Noetherian base R₀⊆R: A≃R⊗_{R₀}A₀, A₀/(f₀) flat over R₀,
  hfib₀, and reflect f·a=0 to f₀·a₀=0. (Then `sliceAux_nzd_of_noetherianBase` at R₀ + pull back a=0.)
- **Depends on**: T-00R6 (×2 for A and A/(f) — generalise its statement or apply twice), T-FLAT1-INJ, NOETH1/2 (all ours).
- **Proof sketch**: three spreadings to a common stage + a colimit reflection:
  (i) A flat over R descends — **T-00R6** with M=A (also NOETH1/2 give A≃R⊗A₀ fp);
  (ii) A/(f) flat over R descends — **T-00R6** with M=A/(f);
  (iii) hfib (·f injective on every fibre) descends — T-FLAT1-INJ (injectivity-spreading, 05LN);
  (iv) reflect f·a=0 back to a finite stage (filtered-colimit bookkeeping on the fp presentation).
  Take the max stage; apply `sliceAux_nzd_of_noetherianBase`; base-change a₀=0 back to a=0. ~150-250 lines assembly on T-00R6.
- **Mathlib/ours**: T-DEV2a (07RF, ours), NOETH1/2 `exists_noetherian_descent` (ours), `AffineTransitionLimit`
  colimit reflection, `sliceAux_nzd_of_noetherianBase` (ours, proven). **Sources**: EGA IV 11.2.6, Stacks 07RF/05LN.
- Discharging T-FLAT1-STAGE ⟹ FLAT1 box axiom-clean ⟹ **entire D-chain axiom-clean**.

### [T-FLAT1-INJ] injectivity of a morphism of fp modules spreads to a Noetherian stage (Stacks 05LN)
- **Status**: open · **File**: ForMathlib/NoethApprox.lean (or FlatDescentLimit.lean) · **Depends on**: (AffineTransitionLimit) · **Type**: theorem
- **Statement**: `φ : M →ₗ N` a morphism of fp `R=colimᵢRᵢ`-modules, injective on every fibre `M⊗κ(𝔭)→N⊗κ(𝔭)`
  (equivalently the FLAT1 case: ·f injective on `A⊗κ(𝔭)`) ⟹ some `φᵢ : Mᵢ→Nᵢ` is fibrewise-injective at stage i.
- **Proof sketch**: fibrewise-injectivity of an fp-morphism is a constructible-open condition on Spec (its
  non-locus is the support of a fp cokernel/kernel datum), quasi-compact ⟹ spreads to a stage. Parallels
  T-DEV2a's openness+quasi-compactness route. ~100-150 lines. **Sources**: Stacks 05LN, EGA IV 11.2.6.

### BB-DELIGNE scoping (beastmode-P2, 2026-07-07): major build + general-base source-gap
Read Mumford AV §14 "Duality theory of finite commutative group schemes". Findings:
1. **§14 is FIELD-ONLY** (opens: *"the ground field k is assumed algebraically closed, of positive
   characteristic p>0"*) and proves things via heavy structure theory: Cartier dual G↦Ĝ, the
   local/reduced decomposition G = G_rr×G_rl×G_lr×G_ll, p-Lie algebras, Frobenius/Verschiebung
   (height-one ⟹ [p]=0 corollary, p.141).
2. **The box `smul_eq_zero_of_factors` needs the GENERAL-BASE theorem** (incl. non-reduced, char p —
   the Drinfeld raison d'être), which does NOT reduce to the field/fibre case: N•Q=0 over a
   non-reduced T is a closed condition not detected by geometric points. Its clean general-base proof
   (Deligne/Tate) is NOT in refs (Mumford = field-only; Tate "Finite flat group schemes"
   [Cornell–Silverman–Stevens] absent).
3. **mathlib substrate = Hopf algebras/bialgebras only** — no Cartier dual, Frobenius/Verschiebung,
   or group schemes.
**VERDICT:** BB-DELIGNE is a *major* multi-session foundational build (finite-group-scheme structure
theory from Hopf algebras up). Its one virtue: **T-W7-INDEPENDENT** (attackable without waiting on
beastmode-A). Prerequisite to start faithfully: add Tate's "Finite flat group schemes" to
refs/ModularCurves/ for the general-base proof. NOT a quick discharge. Sentinel released pending
owner's scope decision.

---

## Amendments v10 (2026-07-08): fleet re-dispatch — KM-lift execution order + new parallel streams

*Coordinator pass (owner-directed, 2026-07-08T~10:45Z). Inputs: the six live worker reports, the
`beastmode_active.*` sentinels, and the board above. The KM source gate is LIFTED (§Amendments v2
gate note, commit 90ed0986); this amendment turns the lift into dispatched work and absorbs the
idle capacity. Housekeeping done in this pass: the unpushed `dev/modular-curves` commits were
PUSHED (`66300bb4..5f4829dc`, 238 commits).*

### v10.0 Fleet ground truth (2026-07-08)
| Worker | On | State / v10 action |
|---|---|---|
| c5β (A-lane, W7) | T-W7.0c-c5β triple→morphism; β2b ladder landed (cfae244c) | active — unchanged (next: single-chart `IsDomain` leaf, β1, β3, β4, then W7.0c-i inc. 2) |
| P3b3 | T-W7.1b main-alg integration; b3x/b3y DONE; b5 poison → sub-ticket | active (`dev/modular-curves-b3`) — unchanged |
| beastmode-A | T-W7.1b owner (b1/b2 done); coordination tail | GO given — v10.1 |
| D2 | T-ACYC (00MZ/00MYW running, 00N0 queued) → B–E cores → T-RB | active — **do not disturb** |
| p2 (=beastmode-P2) | BB-DELIGNE T-D5e, isolating to Lemma 3.8.2 | active — source acquisition v10.6 |
| p0 | T-D6b reboxed→open; **T-KMQ DONE** (ledger banked, 3 closed) | → [T-END0] v10.5 (first act: `/develop --decompose`) |
| fable-P4 | idle after T-E4a-noeth ("awaiting instruction") | DISPATCHED — v10.4 |
| beastmode-H | PHASE-8 terminal (C/H lanes drained) | resume target — v10.3 |
| beastmode-Q | quiet since 07-07T15:03 (T-W3b/c, T-W5, T-Q1–Q4 done) | lane restaffed — v10.4(iii); its bare `beastmode_active` sentinel is STALE (says "T-W3c cut"; T-W3c is DONE) — ignore, do not claim from it |

### v10.1 beastmode-A housekeeping — GO (owner, 2026-07-08)
- Push: **DONE by coordinator** (`66300bb4..5f4829dc`) — no action left.
- Flip the stale T-W7.0i-b parent label: **go**.
- T-E scout: **answered here** — the E-cluster next claims are dispatched to fable-P4 (v10.4);
  A does NOT open a new E claim. A's standing work order: (i) remain the T-W7.1b integrator
  (wire-and-verify when P3b3's branch merges — that is the ticket's close-out), (ii) finish the
  T-D6a-ii tail (in-progress, non-blocking, yours), (iii) T-W7 remains the v9 #3 bottleneck and
  you own its comparison spine — stay on it.

### v10.2 p0 redirect — T-D6b re-assessment, then [T-KMQ]
- **Blocker-list CORRECTION**: `IdealSheafData.comap_mul` is NOT absent — **T-D6a-i landed DONE
  overnight** (beastmode-A, `ForMathlib/IdealSheafComapMul.lean`, sorry-free, arbitrary schemes;
  ticket above). p0's sentinel ("comap_mul machinery absent (may need to build)") predates it.
  **First action: re-assess T-D6b against the landed lemma.** Do NOT take T-D6a-ii (beastmode-A's
  in-progress tail).
- If T-D6b still needs the étale-divisor layer beyond `comap_mul` (KM 1.4.4 (3)⟺(4) territory:
  BB-DIFF + the flf-discriminant étale criterion + the T-W7 fibre-model bridge — see
  beastmode-P2's "KM-text gate: evidence-based re-assessment" above), **REBOX it**: leave a
  precise sorried statement + docstring route, return T-D6b to `state: open`, and pivot to:
- **CLAIMED beastmode-A 2026-07-08 (v10.13 priority-1): re-assessing pull_nsmul_ne_zero against the T-D6a-ii toolkit.**
- **v10.2 VERDICT (p0, 2026-07-08): REBOXED → state: open. Pivoting to [T-KMQ].** Re-assessed
  `pull_nsmul_ne_zero` (ExactOrder.lean:183) against the landed `comap_mul`: it does NOT unblock
  the box. comap_mul feeds only the base-change *assembly* (T-D6a-ii, beastmode-A's in-progress
  tail — not crossed), while the operative content of KM (2)⟹(3) is the genuinely-absent étale
  core (flf rank-`N` group scheme over a field with `N` invertible ⟹ finite étale ⟹ `N` distinct
  reduced geometric points; BB-DIFF / the (3)⟺(4) discriminant criterion). Statement is already
  precise + theorem-level `sorry` (DS-clean); docstring discharge route sharpened in-file to
  record this. No statement drift. Registered as `state: open`, not a leaf for p0.

### [T-KMQ] the ⧗KM quote sweep — NEW (p0's pivot destination; fast lane)
- **Status**: DONE (p0, 2026-07-08) — quote-debt zeroed; reclassification ledger immediately below · **Assignee**: p0 · **Type**: source-fidelity sweep (no new math) ·
  **Depends on**: refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf (present)
- **Job**: for every ⧗KM-marked ticket/decl — T-A4, T-A6, T-B4/T-B4x, T-D8(-bridge), T-D10,
  T-E9, T-H8/T-H9, T-M1, the IRR KM-Ch.10 route (T-C1 and T-E5 are dispatched separately,
  v10.3/v10.4) — read the cited pages in the PDF, bank the **verbatim quote (page + KM §)** in
  the decl docstring / ticket per the lifted-gate rule, confirm the Lean statement matches, and
  update the ticket's Sources line.
- **Close outright** any ⧗KM decl whose proof is already complete from [Loe]/[Sil] and lacked
  only the citation (p0 has a list from the T-D6b reading — those first).
- **Statement MISMATCH protocol**: do NOT silently fix — flag it on the board immediately
  (v9 statement-drift protocol) and stop on that item.
- **Deliverable**: quote-debt zeroed + a table on the board: each ⧗KM ticket reclassified as
  *closed* / *KM-quoted, still gated by <non-KM dependency>*.
- **After T-KMQ**: p0 takes [T-END0] (v10.5) unless p2 has freed up first (P2 has right of
  first refusal on the END stream — it closes their own T-G3 box).

### [T-KMQ] COMPLETE — the ⧗KM quote-debt ledger + reclassification (p0, 2026-07-08)

**Deliverable of the v10.2 pivot.** Every ⧗KM-marked target ticket read against the full KM PDF
(`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`, offset PDF = print + 11). Verbatim
quotes (page + §) banked below; each Lean statement confirmed to match the source (drift/locator
caveats flagged per the v9 protocol — flagged, NOT silently fixed). The global gate note (line
~2827) already redefined `⧗KM` = "cite the real text", so the markers stay; this ledger IS the
citation. T-C1 (KM 2.8, →beastmode-H v10.3) and T-E5 (KM 4.7 headline, →fable-P4 v10.4) are
dispatched separately and excluded.

#### Reclassification table

| Ticket | Decl | KM § banked | Proof status | Classification |
|---|---|---|---|---|
| T-A2 | `projModel`/`projModel_points` (DS1) | 2.2.5.1 | done, sorry-free | **CLOSED** (quote-only; real proof [Loe] 3.3.3 / [Sil] III.3) |
| T-A4 | `isWeierstrassModel_unique` | 2.2.5 | sorried (torsor form) | KM-quoted; gated by **BB-RR** proof (v9.4 torsor form, workable — non-KM) |
| T-A6 | `abelEnrichment_exists`/`_unique` | 2.1.2 (Abel) | open (deep) | KM-quoted; gated by the **7-box Abel/Pic⁰** canonicity project (non-KM; deferred) |
| T-B2 | `muNGrpObj`, `muNPointsEquiv` | 1.12.1 / 1.12.2 | done, sorry-free | **CLOSED** (KM 1.12 attribution-only) |
| T-B4 | E[N] flf rank N² | 2.3.1 (+ 2.3.2) | done-mod-boxes | KM-quoted; gated by **BB-FLAT** register box (non-KM) |
| T-B5y | `mulByHom_formallyUnramified` | 2.3.2 (Lie variant) | **blocked** | KM-quoted; gated by **AG-Ω mathlib gap** (no relative-differentials sheaf API) |
| T-B7 | `muNπ_etale_iff` | 1.12 (attribution) | done, sorry-free | **CLOSED** (KM 1.12 attribution-only; content standard) |
| T-D8 | `isFullLevel_iff_naive` | 3.1.1-2 + 3.7.1 / Cor 3.7.2 | done-mod-box | KM-quoted; gated by **T-D8-bridge box + T-B6** (non-KM) |
| T-D9 | `isGammaOne_iff_naive` | 3.2 | done | (bonus) KM 3.2 = "point of exact order N"; rests on D5/D6 boxes |
| T-D10 | `isGammaZero_iff_fppf` | 3.4.2, 6.1.1, 3.7.1 (p.105) | stmt done, proof ⧗-gated | KM-quoted; gated by **KM 3.7.1 étale-descent representability** proof ([T-D10-proof], v10.7) |
| T-E9 | `gammaFullNaive_representable` | **4.7.2** + 5.1.1 | open | KM-quoted (4.7.2 = Y(N) smooth affine /ℤ[1/N], N≥3 — the exact statement); gated by **T-E5 / explicit route + T-C1 + T-D8** (non-KM) |
| T-SG3 | cyclicity closed condition | 6.4.1 | statement-level | KM-quoted; gated by **flattening-stratification** impl (non-KM) |
| T-H8/H9 | `gammaOneDrinfeld_representable` &c. | 4.7.0/4.7.1/4.7.2 + 5.1.1 | sorried | KM-quoted (4.7.0 = representable⟺rigid); gated by **T-W7 memberships + T-G3** rigidity (non-KM) |
| T-M1 | `jLine_coarse_points` | 8.2.1 + 8.1.3.1 | sorried | KM-quoted; gated by **coarse-moduli machinery** (non-KM) |
| T-IRR | BB-IRR (geom. irreducibility) | 10.9.2 (+10.1, 10.9.1) | black box | KM-quoted; **BB-IRR** black-boxed for consumers (plan §; the 10.9.2 proof = transcendental H/Γ̃) |

**Net: 3 tickets CLOSED (T-A2, T-B2, T-B7 — quote-only debt paid); the rest KM-quoted and
reclassified as gated by explicitly NON-KM dependencies (or a mathlib gap).** No ⧗KM ticket
remains blocked "waiting for KM".

#### Banked verbatim quotes (page + §)

**KM 1.12.1** (print p.55, PDF 66) — T-B2/T-B7: *"We denote by μ_N/Z the group-scheme 'N'th roots
of unity', i.e., μ_N = G_m[N]."* **Lemma 1.12.2** (print p.55, PDF 66): *"Over any scheme S, (μ_N)_S
is the unique closed S-subgroup-scheme of (G_m)_S which is finite flat over S of finite presentation
and of rank N."* (μ_N-points ↔ roots of unity is packaged in μ_N = G_m[N].)

**KM Theorem 2.1.2 (Abel)** (print p.63, PDF 74) — T-A6: *"There exists a unique structure of
commutative group-scheme on E/S such that for any S-scheme T, and any three points P, Q, R in
E(T), we have P + Q = R if and only if there exists an invertible sheaf L₀ on T and an isomorphism
I⁻¹(P) ⊗ I⁻¹(Q) ⊗ I(0) ≃ I⁻¹(R) ⊗ f_T*(L₀)."* ("unique structure" = existence + canonicity; the
identity is the fixed section "0" of setup 2.1.1.)

**KM 2.2.5** (print p.68–69, PDF 79–80) — T-A4: adapted bases — *"f_*(I⁻²(0)) is free on 1, x with
x uniquely determined up to x ↦ x + a … f_*(I⁻³(0)) is free on 1, x, y with y uniquely determined
up to y ↦ y + ax + b … We say that such x, y are 'adapted to ω'."* (Uniqueness for a FIXED ω = the
u=1 subfamily of `VariableChange` — exactly the v9.4 torsor form.) **KM 2.2.5.1** (print p.69, PDF
80) — T-A2: *"y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆ … the affine ring H⁰(E−{0}; O) … is none other
than A[x,y]/(this Weierstrass equation)."*
⚑ LOCATOR CAVEAT (not drift): a close-out citing "[KM] 2.2" for the *definition* of a generalized
Weierstrass equation should cite **2.2.5.1** (print p.69); the §2.2 opening (2.2.1, p.67) defines
ω_{E/S} = f_*Ω¹, not the equation.

**KM Theorem 2.3.1** (print p.73, PDF 84) — T-B4: *"the S-homomorphism 'multiplication by N' [N]:E→E
is finite locally free of rank N². If N is invertible on S, its kernel E[N] is finite etale over S,
locally for the etale topology … isomorphic to Z/NZ × Z/NZ."* **Cor 2.3.2** (print p.75, PDF 86):
*"If E[N] is finite etale over S … then N is invertible on S."* (2.3.2 is also the Lie([N])=N
source noted for T-B5y.)

**KM 3.1** (print p.98, PDF 109) — T-D8: *"A Γ(N)-structure on E/S … is a group homomorphism φ:
(Z/NZ)² → E[N](S) which is a 'generator' of E[N] … Explicitly … an equality of effective Cartier
divisors E[N] = Σ_{a,b mod N} [φ(a,b)] … the N² sections φ(a,b) form a 'full set of sections'."*

**KM 3.2** (print p.99, PDF 110) — T-D9: *"A Γ₁(N)-structure on E/S, also called a point of 'exact
order N' … is a homomorphism φ: Z/NZ → E[N](S) … [such that] the effective Cartier divisor
Σ_{a mod N}[φ(a)] is a subgroup-scheme of E."*

**KM 3.4** (print p.100, PDF 111) — T-D10: *"A Γ₀(N)-structure on E/S is … a finite flat
subgroup-scheme K ⊂ E[N], locally free of rank N, which is cyclic in the sense that locally f.p.p.f.
on S, it admits a generator."*

**KM 3.6.0 Relative Representability Theorem** (print p.102, PDF 113): *"[the functors of Γ(N)-,
Γ₁(N)-, balanced Γ₁(N)-structures] … Each of these functors is represented by a finite S-scheme."*
⚑ LOCATOR CAVEAT: 3.6.0 covers only THREE problems; Γ₀(N) representability is asserted "much
deeper" in Rem 3.6.1 (proved in Ch 6).

**KM 3.7.1** (print p.104, PDF 115) — T-D8/T-D10: *"Let N … S a scheme on which N is invertible …
Consider the four functors [Γ(N), Γ₁(N), bal.Γ₁(N), Γ₀(N)] … Each is represented by a finite etale
S-scheme."* Γ₀ descent (p.105): *"the notion of cyclicity is by definition local for the f.p.p.f.
topology, so a fortiori for the etale topology … reduce to the case when E[N] is the constant
group-scheme (Z/NZ)² … our constant group-scheme K is cyclic … if and only if the abstract group
K(T) is a cyclic group of order N."* **Cor 3.7.2** (print p.106) gives the constant-scheme
description (naive bases / exact-order points / cyclic subgroups). ⚑ LOCATOR CAVEAT: the four cases
are one Theorem 3.7.1; the per-structure constant-set description is Cor 3.7.2.

**KM 5.1.1 First Main Theorem** (print p.129, PDF 140) — T-E9/T-H9: *"Each of the four moduli
problems [Γ(N)], [Γ₁(N)], [bal.Γ₁(N)], and [Γ₀(N)] is relatively representable over (Ell). Each is
finite and flat over (Ell) of constant rank ≥ 1, and regular (necessarily of dimension two). Each
tensored with Z[1/N] is finite etale over (Ell/Z[1/N])."* (Base is (Ell); rigidity/absolute
representability of Y(N) for N≥3 is a separate downstream consequence, not this wording.)

**KM 6.1.1 Main Theorem on Cyclic Groups** (print p.152–153, PDF 163–164) — T-D10: *"G ⊂ E[N] a
finite locally free commutative S-subgroup-scheme … of rank N … (1) G is cyclic if and only if its
scheme of generators G^× is finite locally free over S, of rank φ(N). (2) … the Cartier divisor D =
Σ_{(a,N)=1} [aP] … D = G^×."* with the divisor identity *"G as a Cartier divisor in E is given by
G = Σ_{a mod N} [aP]"* and cyclic = *"locally f.p.p.f. on S, G admits a generator … {aP},
a=0,…,N−1 form a 'full set of sections'."*

**KM 6.4.1 Cyclicity as a closed condition** (print p.162, PDF 173) — T-SG3: *"there exists a closed
subscheme W ⊂ S, defined locally … by finitely many equations, which is universal for the condition
'G is cyclic', in the sense that for any T → S, the inverse image G_T/T is cyclic if and only if the
map T → S factors through … W."* (Mechanism: cyclicity ⇔ O(G^×) locally free of rank φ(N), Lemma
6.4.2 + Mumford flattening stratification Prop 6.4.3.)

**KM 4.7.0 Scholie** (print p.111, PDF 122) — T-H8/H9, T-E5: *"Let 𝒫 be relatively representable and
affine over (Ell); then a necessary and sufficient condition that 𝒫 be representable is that 𝒫 be
rigid."* **Cor 4.7.1** (print p.116): *"Any relatively representable moduli problem 𝒫 which is affine
and etale over (Ell), and rigid, is representable by a smooth affine curve over Z."* **Cor 4.7.2**
(print p.117) — T-E9: *"For N ≥ 3, the naive level N moduli problem of 4.6 is representable, by a
smooth affine curve Y(N) over Z[1/N]."*

**KM 8.2.1** (print p.228, PDF 239) — T-M1: *"over any ring R, the coarse moduli scheme attached to
the moduli problem [Γ(1)] is the j-line over R, M([Γ(1)]) = Spec(R[j]), with the j-invariant
normalized à la Tate; j = 0 has complex multiplication by Z[ζ₃], j = 1728 by Z[i]."* **Lemma
8.1.3.1** (print p.225, PDF 236): *"When k is an algebraically closed field, then M(𝒫)(k) = the set
of k-isomorphism classes of 'elliptic curves E/k with given level 𝒫-structure'."* (The 𝔸¹(k) ↔
iso-classes-via-j bijection T-M1 uses is the composite of 8.1.3.1 at 𝒫=[Γ(1)] with 8.2.1; the map
is E ↦ j(E).)

**KM Corollary 10.9.2(2)** (print p.303, PDF 314) — T-IRR: *"The scheme M̄(𝒫)[1/NK] is a proper
smooth curve over Z[ζ_N,1/NK] with geometrically connected fibers."* (For 𝒫=[Γ(N)], Γ={1}, K=N:
X(N) over Z[ζ_N,1/N] is proper smooth with geometrically connected — i.e. geometrically irreducible
— fibers.) The **BB-IRR** black box is exactly the proof input (print p.303): *"the underlying
complex manifold to M(𝒫) ⊗ C is isomorphic to the quotient of the upper half plane by the subgroup
Γ̃ ⊂ SL(2,Z) … the complete inverse image of Γ by reduction mod N"* — connectedness from H being
connected, the one non-algebraic input, flagged in **10.1 Motivation** (print p.287) as *"the
transcendental description of our moduli spaces as quotients of the upper-half plane … used in the
proof of 10.9.2."* Cusp count (**Thm 10.9.1**, print p.301): *"the cusps of M̄(𝒫) are the disjoint
union of n(Γ) sections … n(Γ) = #(Hom Surj((Z/NZ)², Z/NZ)/±Γ)."*

### v10.3 [T-C1-KM28] WS-C re-decompose (KM 2.8 backend) — the plan.md standing order, now DUE
- **Status**: open · **Assignee**: beastmode-H on resume (C-lane is theirs), else any fresh
  worker · **Type**: `/develop --decompose` planning ticket + skeleton ·
  **Depends on**: KM full text (present); AG-CD substrate = `ForMathlib/CartierDual.lean`
  (p2's BB-DELIGNE Layer A — REUSE, do not duplicate)
- **Job**: execute plan.md's standing order (*"re-run `/develop --decompose` on WS-C['s]
  KM-sourced subtree when the full text lands"*): read KM 2.8 in full (+ the KM 2.3 [N]-material
  it consumes), transcribe verbatim quotes, and cut the **norm/divisor comparison backend** for
  T-C1 into WeilPairing/ leaf tickets — reconciled against what already exists:
  `CharZeroDescent.lean` (T-relative descent + local model + naturality, axiom-clean),
  `EtaleDescent.lean` (field-level descent heart), and the D7 decision (duality is the final
  API; KM 2.8 is the comparison backend + KM-faithful proof — do NOT re-litigate the API).
- **Deliverable**: `decomposition-km28.md` + sorried skeleton (`lake build` clean; DS-register
  rule for any def-level sorry) + leaf tickets on this board.

### v10.4 [T-E5-KM47] WS-E re-decompose + Q-lane restaff — fable-P4 (dispatched)
- **Status**: open · **Assignee**: fable-P4 (idle; E-lane is their recent context) ·
  **Type**: planning + skeleton + proof tickets
- **(i) KM 4.7 quote pass**: read the KM 4.7 proof (now allowed), reconcile against [Loe] 3.7.4
  (quote in hand), bank verbatim quotes into `representable_iff`'s docstring + the T-E5 ticket.
- **(ii) Bootstrap objects**: cut the KM-4.7 bootstrap sub-tickets from
  `decomposition-gme2.md` §E12–E15 (M₁, rigidity, Legendre, ℰ₃ — bodies already fully explicit
  there) into real board tickets + sorried skeleton decls in Moduli/ (DS-register rule applies).
  These are T-E5's "sub-tickets at cut time", never cut — cut them now.
- **(iii) Q-lane restaff**: beastmode-Q is quiet; the lane's next-in-lane is **T-Q5** (gluing
  affine quotients, quasi-projective case, [Loe] 3.6.1 — body cut at pickup per the lane note),
  then **T-Q6** (quotients of rigidified problems — the KM 4.7 ⇐ feeder), plus the T-Q4e
  phase-2 remainder if quick. v9.2 is binding: this is the Q-finite minimal API (NOT deferred);
  keep it severed from the W-stack torsor machinery.
- **Order**: (i)+(ii) first (independent, unblocks T-E5 planning), then (iii).
- fable-P4's named alternative T-H5-forward stays second-choice (v10.7) — this dispatch wins on
  the v9 "keep marginal workers on the core Y₁(N)/Y(N) path" directive.

### v10.5 [T-END0] End(E/S)/degree layer from KM Ch. 2 — the G-lane resume trigger has FIRED
- **Status**: CLAIMED p0 2026-07-08 (p2 still on BB-DELIGNE T-D5e `deligne_operators`, NOT freed
  → right-of-first-refusal not exercised); `/develop --decompose` first act IN PROGRESS ·
  **Assignee**: p0 (was: beastmode-P2 when T-D5e wraps — right of first refusal — else p0 after
  T-KMQ) · **Type**: `/develop --decompose` planning (BINDING first act, v10.8) + execution ·
  **Depends on**: KM Ch. 2 (NOW in refs — this was the G-lane PHASE-8 resume trigger, verbatim:
  *"when the KM Ch.2 text lands in refs/ModularCurves/ (degree/dual-isogeny/Hasse)"*); GME
  §B8/§B9 transcriptions (`decomposition-gme2.md`); HasseWeil
  `Foundation/DegreeQuadraticForm.lean` + `HasseBound.lean` (fibre anchor — IMPORT, never
  re-prove)
- **Job**: read the KM Ch. 2 degree/dual-isogeny/Hasse sections + §B8/§B9, bank quotes, then
  skeletonize `End(E/S)` + `deg : End(E/S) → ℤ` (file placement at pickup; Groupoid-adjacent or
  new EllipticCurve/EndomorphismDegree.lean) with the already-decomposed T-G3 sub-tickets as the
  work order: **T-G3b** (deg quadratic expansion) → **T-G3d** (N-divisibility of a
  level-fixing automorphism-minus-one) → **T-G3c** (fibrewise Hasse via T-RED0/HasseWeil
  transfer) → close the box `aut_hom_eq_id_of_fullLevel` (Groupoid.lean:120) via the reduction
  already documented in its docstring, wiring the PROVEN T-G3a engine.
- **Consumers**: T-G3 = rigidity → T-E10 assembly, T-E9's rigid half, T-H6/T-H10; BB-DEG /
  T-B4x synergy (KM 2.3 boxes). T-W7-INDEPENDENT — genuine parallel stream.
- Cleanup cadence: add **[CLEANUP-END]** (EndomorphismDegree/Groupoid files) after T-G3b+d+c.

### v10.6 OWNER ACTION — acquire Tate, "Finite flat group schemes"
Add Tate's chapter (in Cornell–Silverman–Stevens, *Modular Forms and Fermat's Last Theorem*) to
`refs/ModularCurves/` (local-only, gitignored — same handling as KM). It is the named general-base
source for the LAST BB-DELIGNE sorry: p2 is isolating T-D5e onto exactly Lemma 3.8.2
(`deligne_operators`); their scoping note above records Mumford AV §14 as field-only and this
chapter as the missing text. Until it lands, p2's isolation work stands as designed (the one
sorry sits precisely on 3.8.2).
- **RESOLVED 2026-07-08 (same day)** — the book is IN refs: `refs/ModularCurves/css-modular-forms-flt.pdf`
  (+ source `.djvu`; TOC verified: **Chapter V, "Finite Flat Group Schemes", John Tate,
  pp. 121–154**; the Lemma-3.8.x range sits in §3 "Finite flat group schemes; passage to
  quotient", pp. 132–146). **Gate lifted for `deligne_operators`** under the standard rule:
  READ the cited pages, quote them verbatim (page + §) in the decl/ticket, confirm the Lean
  statement matches the quote — do NOT prove from memory.

### v10.7 Available-not-priority (idle-capacity overflow list)
- **[T-D10-proof]** `isGammaZero_iff_fppf` — the KM 3.7.1 étale-descent argument is now readable
  (quotes ALREADY banked in the ticket; design (a) implemented). v9 priority #7 — take only if
  the core lanes above are saturated.
- **[T-H5-forward]** rigidity direction of `gammaHNaive_rigid_iff` via the PROVEN T-G3a engine —
  legitimate but second to v10.4; memberships remain T-H3/T-W7.8-parked.
- **T-W7.8 route (ii)** (concrete Weierstrass-shape hom-existence descent, ~300–500 lines) —
  only on explicit owner override of the v9 F1′ LOW-priority call; default stays route (i)
  wait-for-mathlib (fable-P4's 2026-07-08 re-check verdict stands).

### v10.8 OWNER DIRECTIVE (2026-07-08, binding): RR-ONLY reaffirmed + `/develop` is the planning vehicle
- **The ONLY standing assumable is BB-RR** (Riemann–Roch, per the v3 RR-only register).
  Everything else — including every stream this amendment opens — is a PROVE-IT target: no new
  standing boxes; a sorry may exist only inside a stream whose plan terminates in a proof (or an
  explicit owner-visible gap ticket per the DS-register rules).
- **`/develop --decompose` is the BINDING first act** of each new stream, before any proof
  execution: **T-C1-KM28** (assignee: H on resume), **T-E5-KM47** (fable-P4), **T-END0** (p2,
  else p0). Deliverables per the skill: prose proof per top-level result, ordered lemma
  decomposition, `:= by sorry` skeleton that `lake build`s clean, verbatim source quotes per
  leaf + a Lean↔source match paragraph each, and the leaf tickets on this board.
- Coordinator note: these `/develop` runs belong to the **assignees' sessions** (this worktree
  hosts live builds; p2 holds right of first refusal on T-END0) — not to the coordinator pass.

### v10.9 Addendum (2026-07-08): fable-P4 session report absorbed — cross-links
- fable-P4's full report (relayed post-v10) confirms the v10.4 dispatch and surfaces reusable
  API from **T-H2b** (done, 2026-07-07): `Point.baseChangeEquiv : (E.baseChange σ).Point t ≃+
  E.Point (t ≫ σ)` (GroupLaw.lean) + `Over.monObjMkPullbackSnd_mul_left_fst` (NEW
  `ForMathlib/OverPullbackMul.lean`, pure category theory, **upstream candidate**) +
  `isNaiveFullLevel_pullAlong` discharged (GammaH 10 → 9 sorries). All axiom-clean.
- **Cross-link → beastmode-A (T-D6a-ii)**: the additive `Point.baseChangeEquiv` dictionary may
  shorten the remaining L3/L4 assembly (the `Point.pull_zsmul` / `ker_sectionBaseChange` steps) —
  check it before hand-rolling.
- Same session arc also banked (consistent with the board, no dispatch changes): T-A8-4 (record
  ⟹ fibrewise-elliptic comparison), T-H7b-i (point separation along field extensions), and the
  **T-W7.7/T-W7b canonicity milestone** (Rigidity.lean sorry-free, GIT 6.1→6.6 end-to-end) — the
  input that made T-E4a-noeth possible.

### v10.10 NEW STREAM for a fresh worker (2026-07-08): the invertible-N étale bottleneck — [T-B5D] + [T-DISC]
- **Why now**: reviewer v9 work-order **#4** ("discharge the invertible-N torsion/étale
  bottleneck — BB-DIFF or its local substitute — BEFORE BB-DELIGNE") has been UNSTAFFED since
  beastmode-B's T-B5z claim release (v9.3). Consumers: T-B5 ([N] étale ⟹ E[N] finite étale) →
  the T-B6-consuming fibre chain → the T-D8-bridge box → **T-E7 Y₁(N) MILESTONE**; also
  T-D6c / T-D7-bridge (KM 1.4.4 (3)⟺(4)) and T-B7's étale spec.
- **[T-B5D] BB-DIFF discharge, commissioned as its own multi-session stream** (exactly per
  beastmode-B's recommendation in the v9.3 T-B5z finding): target
  `mulByHom_formallyUnramified` (the BB-DIFF sorry). Route of record = the
  **ψ_N-separability bridge**, the most self-contained mathlib-aligned route per the banked
  finding: `FormallyUnramified` reduces to `Subsingleton Ω[coordinateRing⁄base]` via
  `HasRingHomProperty.Spec_iff` + `Algebra.formallyUnramified_iff`; the reusable partial
  `FormallyUnramified (torsionπ N) → FormallyUnramified (mulByHom N)` (group
  infinitesimal-lifting) is banked self-contained/buildable — a good first landing.
  beastmode-B's fuller route analysis lived at `scratchpad/tb5z_architecture.md` and may be
  session-ephemeral — if absent, the v9.3 finding IS the spec. **Do NOT re-litigate the mapped
  dead ends** (no invariant differential in mathlib; categorical-[N] ⟷ chart-[N] comparison is
  T-W7 scope). **First act (binding, v10.8): `/develop --decompose`** — sources ([Sil], [KM] 2.3)
  pinned with verbatim quotes at decompose time, never from memory.
- **[T-DISC] flf ⟺ discriminant étale criterion** (beastmode-P2's banked substrate piece, see
  "KM-text gate: evidence-based re-assessment" above): the general "finite locally free
  morphism is étale ⟺ all geometric fibres étale (⟺ discriminant a unit)" layer, as
  ForMathlib. Substrate, not a ticket-closer — but it is what T-D6c/T-D7-bridge sit on.
  Re-check T-B7's étale-spec state at pickup. Same `/develop` discipline.
- **FILE DISCIPLINE**: new ForMathlib/bridge files only — `GroupLawConstruction.lean`,
  `Torsion.lean` and the W7 files are held by active workers.
- **Runner-up big streams for ADDITIONAL fresh workers** (priority order):
  (1) **T-PIC0 + COH-1** — Pic of a scheme + GME 1.10.4 cohomology-and-base-change;
  owner-sanctioned parallel de-black-boxing (2026-07-05 directive), T-PIC0 explicitly
  unclaimed; COH-3 = coordinate with the mathlib lane (#36345/#36218), don't build.
  (2) **T-IRR0** — the KM Ch. 10 algebraic route to geometric irreducibility is NOW readable
  (gate lifted); late-phase but owner-directed to plan in parallel.
  (3) **T-Q2 proofs** (A7.1.1/A7.1.2, InvariantTorsor.lean) — OWNER ACTION first: add SGA III
  Exp. V to `refs/ModularCurves/` (the named proof source).

## Amendments v10.11 (2026-07-08): ★ Stream claim — T-PIC0 + COH-1 (fable-PIC0)

*Stream **T-PIC0 + COH-1** (Pic of a scheme + GME 1.10.4 cohomology-and-base-change; v10.10
runner-up #1, owner-sanctioned parallel de-black-boxing per the 2026-07-05 directive) claimed
by **fable-PIC0**, 2026-07-08T11:20Z. Sentinel: `beastmode_active.PIC0`. The stream star
reserves the lane; individual leaf tickets are claimed one at a time per rule 5 as they are
cut.*

- **Claimed**: fable-PIC0, 2026-07-08T11:20Z (stream star: T-PIC0 + COH-1)
- **Scope**: (a) **[T-PIC0]** Pic(X) for a scheme via invertible O_X-modules (mathlib
  `SheafOfModules` + LocallyFree) + fibre-degree of an invertible sheaf; (b) **[COH-1]** GME
  Lemma 1.10.4 cohomology-and-base-change exactness criterion, as pinned in
  decomposition-gme2.md header. **COH-3 = mathlib lane (#36345/#36218) — coordinate, do NOT
  build.** COH-2 not claimed (separate cut).
- **First act (binding, v10.8 discipline)**: `/develop --decompose` — GME 1.10 + 2.2.2(2.17)
  read from `refs/ModularCurves/` with verbatim quotes at decompose time, never from memory;
  deliverables: prose proof per top-level result, ordered lemma decomposition, `:= by sorry`
  skeleton that `lake build`s clean, verbatim source quotes per leaf + Lean↔source match
  paragraph, leaf tickets on this board. Decomposition file: `decomposition-pic-coh.md`.
- **FILE DISCIPLINE**: new files only — `ModularCurves/Picard/*.lean` +
  `ForMathlib/*.lean` additions; no held files touched (GroupLawConstruction, Torsion, W7
  files, LevelStructure/*, AdditionChart* are other workers' lanes).

## Amendments v10.12 (2026-07-08): SGA III LANDED — the T-Q2 proofs are dispatchable

- **Source landed (coordinator)**: `refs/ModularCurves/sga3-1.pdf` + `sga3-2.pdf` (SGA 3,
  1970 edition; intro verified: Exposé V "résultats généraux sur l'existence de quotients"
  is in vol. 1; French text, legible scan). v10.10 runner-up (3)'s OWNER ACTION is satisfied.
- **[T-Q2-proofs] — now a dispatchable fresh-worker stream**: discharge the four by-design
  sorries in `ForMathlib/InvariantTorsor.lean` — `Module.Finite.of_isFreeAlgebraAction`,
  `Algebra.Etale.of_isFreeAlgebraAction`, `torsorMul_bijective_of_isFreeAlgebraAction`
  (A7.1.1, split per Tier A5), `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`
  (A7.1.2, against T-Q4's `fixedPointsBaseChange`). Proof source: **SGA III Exp. V** — read +
  quote verbatim (page + numbering) per the standard lifted-gate rule; no memory
  reconstruction. beastmode-Q's banked attack block applies:
  `decompose-attacks-2026-07-06/q-lane.md`. **First act (binding, v10.8):
  `/develop --decompose`.**
- **FILE DISCIPLINE**: this stream owns `InvariantTorsor.lean` ONLY (beastmode-Q is quiet;
  fable-P4's Q-restaff owns AffineQuotient/gluing + T-Q6; fable-PIC0 owns Picard/* — all
  disjoint; coordinate via the board). Consumers: KM Ch. 7 regularity (phase 4) + the
  étale-torsor layer behind the quotient theory.

## Amendments v10.13 (2026-07-08): beastmode-A re-dispatch (post-T-D6a-ii) + P3b3 PR nudge

- **beastmode-A report absorbed**: T-D6a-ii COMPLETE, axiom-clean — L3
  `Section.orderDivisor_baseChange`, ForMathlib `exists_factor_comap_iff` (comapIso factoring
  dictionary, upstream-grade), L4 `RelEffCartierDiv.IsSubgroup.baseChange`, headline
  `Section.HasExactOrder.baseChange` (= KM 1.4.4 (1)⟹(2)). 0i-b flipped; integrator merge
  path de-risked (b2 spine re-certified sorryAx-free); pushed. **Standing duty preserved**:
  the T-W7.1b integrator wire PREEMPTS everything below the moment P3b3's PR opens.
- **Next claim for beastmode-A (priority order; all compatible with the wire duty):**
  1. **[T-D6b] re-assessment + attack** — the claim is RELEASED (p0 → T-END0 after T-KMQ; no
     sentinel holds it; ExactOrder.lean free). p0's assessment predates BOTH `comap_mul`
     (T-D6a-i) and today's T-D6a-ii suite — beastmode-A now holds the freshest toolkit for it
     (comap_mul + orderDivisor_baseChange + HasExactOrder.baseChange + Point.baseChangeEquiv).
     Re-assess KM 1.4.4 (2)⟹(3) against that toolkit (read the KM pages, quote verbatim); if
     it is STILL étale-gated beyond the toolkit, rebox per the v10.2 protocol (precise sorried
     statement + docstring route) and fall through.
  2. **[T-D33] subgroup-divisor locus** — dependencies NOW BOTH DONE (T-D14 ✓; T-D15 ✓
     2026-07-06, 5-line proof); the D-lane is otherwise unstaffed; beastmode-A holds the
     freshest IsSubgroup/divisor context (today's L4). Cuts the Γ₁ exact-order condition over
     U — feeds T-W8 / level spaces + representability.
  3. **[T-IRR0] scoping** (v10.10 runner-up 2) — interruptible `/develop` scoping work if
     1–2 both wedge.
- **P3b3 coordination nudge (coordinator)**: b3x/b3y/main/bridge are landed on
  `dev/modular-curves-b3` but no PR is open, and b5-injectivity is poison-blocked →
  sub-ticketed. Do NOT hold the merge hostage to b5: unless b5 is imminent, OPEN THE PR NOW
  with the landed leaves — the integrator wire discharges 3 of the 4 remaining T-W7.1b
  sorries on merge; b5 keeps its sub-ticket and lands separately.

### [T-END0] FIRST ACT DONE (p0, 2026-07-08) — leaf tickets (see §v10.5; full plan: decomposition-end0.md)
*Appended at EOF (mid-file board region was under concurrent churn). `/develop --decompose` first act:*
- **Decomposition**: `.mathlib-quality/decomposition-end0.md` — prose proof = **KM Cor 2.7.2(1)** verbatim,
  ordered lemmas, verbatim KM §2.5–2.7 quotes per leaf + Lean↔source match, HasseWeil import anchors.
  Confirms `aut_hom_eq_id_of_fullLevel` (Groupoid.lean:125) **is** KM 2.7.2(1).
- **Skeleton**: `EllipticCurve/EndomorphismDegree.lean` (new) — `lake build` **CLEAN** (3074 jobs, 0
  errors, 11 expected `sorry`s). `End(E/S) := E.asOver ⟶ E.asOver` (`Hom.commGroup` additive / `≫` mult;
  `mulBy n = [n]`). Committed `745cd328`.
- **DS-data (DS-END0)**: `endDeg`/`endDual`/`endTrace` — pins `endDual_comp_self` (KM 2.6.1),
  `endDeg_mulBy` (2.6.1.1), `endDual_mulBy` (2.6.2.1), `endTrace_spec` (2.6.2.2).
- **Leaf tickets** (work order T-END0a→b→c/d→G3b→G3d→G3c→G3e→close box):
  - **[T-END0a]** `Ring (End E)` instance (biadditivity of `≫` over `Hom.commGroup`) · infra · KM 2.5.1 · instance
  - **[T-END0b]** build `endDeg`/`endDual` (DS-data, dual via Abel `E ≅ Pic⁰` T-A6-adj) + pins · KM 2.5.1/2.6.1 · def(data)+thm
  - **[T-END0c]** `endDeg_mulBy : deg[N]=N²` · KM 2.6.1.1 · anchor HasseWeil `mulByInt_degree`/BB-DEG (T-B6) · thm
  - **[T-END0d]** build `endTrace` + `endTrace_spec` (`f+f^t=[tr f]`) · KM 2.6.2.2 · def(data)+thm
  - **[T-G3b]** `endDeg_one_add_mulBy_comp` (`deg(1+g∘[N]) = 1+N·tr g+N²·deg g`) · KM 2.6.3/2.7.2 · thm
  - **[T-G3c]** `endTrace_sq_le` (`(tr g)² ≤ 4·deg g`) · KM 2.6.3(2) · **IMPORT** HasseWeil `hasse_bound`/`degree_quadratic_closed` (T-RED0) · thm
  - **[T-G3d]** `exists_eq_one_add_mulBy_comp_of_fixesTorsion` (ε fixes E[N] ⟹ ∃g, ε=1+g∘[N]) · KM 2.7.2 proof · thm
  - **[T-G3e]** `eq_zero_of_endDeg_eq_zero` (deg g=0 ⟹ g=0, pos-definite) · KM 2.6.3(2) proof · thm
  - **close** `aut_hom_eq_id_of_fullLevel` = T-G2 + G3d + G3b + `deg ε=1` + G3c + `gme_deg_trace_forces_zero` (**PROVEN**) + G3e
- **Consumers**: T-G3 rigidity → T-E10, T-E9 rigid half, T-H6/T-H10. **NEXT (p0)**: execution — T-END0a then T-END0b. T-W7-independent.

## Amendments v10.14 (2026-07-08): PR #5220 OPEN — the integrator wire FIRES; v10.13 nudge superseded

- **P3b3 beat the nudge**: `dev/modular-curves-b3` now carries ALL FOUR leaves axiom-clean —
  including **b5** (`T-W7.1b-b5 PROVED — faithfulness of projective variable-change action`,
  67c9feab; the kernel-poison wall fell to the bridge-based section-level transport) — and
  **PR #5220 is OPEN** (verified: `dev/modular-curves-b3` → `dev/modular-curves`, non-draft,
  "T-W7.1b (2nd half): b3x/b3y/main + bridge + b5 — all four leaves, axiom-clean").
  The v10.13 P3b3 nudge is SUPERSEDED — no partial merge needed.
- **beastmode-A: the v10.13 preempt has FIRED.** Do the integrator wire NOW: review #5220,
  discharge the four T-W7.1b sorries via the de-risked path (hfil ← `byv_filtration e heπ hez n`),
  full-file axiom sweep, merge, board-flip **T-W7.1b → DONE** (comparison-theorem milestone;
  T-W7.12's `1b` dependency flips ✓ — its remainder is 0c-ii/0h/1a on the c5β chain). The
  v10.13 next-claims list (T-D6b → T-D33 → T-IRR0) becomes your follow-on after close-out.
- **P3b3: freed on merge.** Stand by for wire feedback until #5220 merges; then next claim:
  **[T-IRR0]** (v10.10 runner-up 2, the last unstaffed stream) — `/develop --decompose` scoping
  of the KM Ch. 10 algebraic route to geometric irreducibility (now readable) vs the analytic
  route; v10.8 discipline binding. New files only.

### v10.11.1 (2026-07-08, fable-PIC0): T-PIC0+COH-1 decompose DONE — leaf tickets

*`/develop --decompose` complete: `decomposition-pic-coh.md` (verbatim GME/Mumford
quotes + attack blocks per leaf, gate 1–7 status inside), skeleton green:
`ForMathlib/BaseChangeKerCoker.lean` (8 sorried leaves, defs implemented, mathlib-only
imports) + `Picard/InvertibleSheaf.lean` (4 sorried leaves; monoidal-instance bridge
landed). Route of record: Mumford §5 K-complex module core (Hida's own §1.10.4 proof
needs EGA III 3.2.1 + 4.1.5 = absent/B3-scale/COH-3-lane; Hida himself cites [ALG]
III.12.10 = the K-complex machine). Čech/R^if_* instantiation explicitly deferred to
the owned mathlib lane. Statements are the skeleton contract; sketches + sources per
leaf live in decomposition-pic-coh.md (quote-or-delete enforced).*

**COH-1 leaves** — File: `ModularCurves/ForMathlib/BaseChangeKerCoker.lean` (work order):
- **[T-COH1-A3]** purity: `Module.Flat.lTensor_subtype_injective_of_flat_quotient`
  (flat quotient ⟹ submodule inclusion pure). Deps: none. THE workhorse.
  Sketch: free presentation of M + 3×3 chase, Tor-free, inside
  `TensorProduct/RightExactness` API; five-method search first (G2) — closest misses
  logged (Flat/Basic `lTensor_exact` is the other-variable statement).
  - **Claimed**: fable-PIC0, 2026-07-08T12:00Z · **Status**: in_progress
- **[T-COH1-A3b]** `Module.Flat.of_flat_quotient` (N ⊆ Q, Q flat, Q/N flat ⟹ N flat).
  Deps: T-COH1-A3. Sketch: ideal criterion (`Module.Flat.iff_rTensor_injective'`) +
  A3-chase; decomposition has the 3-step diagram. · **Status**: open
- **[T-COH1-A4]** `kerLTensorComparison_bijective` (coker flat ⟹ T⁰ base change).
  Deps: A3, A3b. Sketch: prose steps 3–4 of decomposition (two SES purity
  applications + right-exactness bookkeeping). · **Status**: open
- **[T-COH1-A1]** `range_lTensor_range_subtype` (T¹ base change / range identity).
  Deps: none · Parallel: yes. Sketch: antisymm; generators m ⊗ f p both ways;
  `TensorProduct.tensorQuotientEquiv` composition note in file docstring. · **Status**: open
- **[T-COH1-A2]** `Module.subsingleton_of_forall_field_tensor_subsingleton` (f.g. +
  all R-field fibres vanish ⟹ zero; ℚ/ℤ counterexample sans f.g. in docstring).
  Deps: none · Parallel: yes. Sketch: `Module.support_eq_empty_iff` + NAK bridge at
  κ(𝔭) (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` route or
  FreeLocus rankAtStalk route — pick at proof time). · **Status**: open
- **[T-COH1-A5a]** `LinearMap.fg_ker_of_finite` (noeth: ker of map out of finite is
  FG). Deps: none · Parallel: yes. Golf-sized (`IsNoetherian` submodule). · **Status**: open
- **[T-COH1-A5b]** `Module.Projective.ker_of_flat_coker` (Cor 1.10.5 module form).
  Deps: A3b, A5a. Sketch: im d finite+flat ⟹ fp (noeth) ⟹ projective
  (`Module.Flat.projective_of_finitePresentation` ✓ pin-verified) ⟹ split SES ⟹ ker
  summand of finite projective P. · **Status**: open
- **[T-COH1-A6]** `kerBaseChangeComparison_bijective` (A-linear fibre identification,
  the (2.15)/(2.17) consumer shape). Deps: A4. Sketch: A4 + `AlgebraTensorModule`
  bridging (`LinearMap.baseChange` vs `lTensor` restriction of scalars). · **Status**: open
- **[CLEANUP-PC1]** /cleanup BaseChangeKerCoker.lean — after A3+A3b+A4 · **[CLEANUP-PC2]**
  after A1+A2+A5a · **[CLEANUP-PC3]** final, after A5b+A6. · **Status**: open (cadence)

**T-PIC0 stage-P1 leaves** — File: `ModularCurves/Picard/InvertibleSheaf.lean`:
- **[T-PIC1a]** `isInvertible_unit`. Deps: none. Sketch: cover {⊤}, `(⊤).ι` pullback of
  unit ≅ unit (`pullbackObjUnitToUnit` — finality of `Opens.map` via lattice-meet
  zig-zag if instance missing, 15-line fallback). · **Status**: open
- **[T-PIC1c]** `exists_tensorObj_unit_iso` (M ⊗ 𝒪 ≅ M). Deps: none. Sketch: presheaf
  right-unitor + sheafification counit iso on sheaves (adjunction from
  Modules/Sheaf.lean); NO GAP-1 content. · **Status**: open
- **[T-PIC1d]** `IsInvertible.pullback`. Deps: none. Sketch: preimage cover +
  `Modules.pullbackComp` + unit-pullback iso; `morphismRestrict_ι` square. · **Status**: open
- **[T-PIC1b]** `IsInvertible.tensorObj`. Deps: **T-PIC-GAP1** (BLOCKED — the only
  gap-gated sorry in the skeleton). · **Status**: blocked
- **[T-PIC-GAP1]** (scoping) GAP-1: sheafification ⊗-compatibility / restriction-
  commutes-with-sheafification on the Zariski site. FIRST ACT: ecosystem check of the
  Riou lane (Sites/Monoidal.lean pattern → PresheafOfModules W.IsMonoidal analogue;
  mathlib4 open PRs) — build ONLY if unowned; then own /develop pass (3 candidate
  routes recorded in decomposition-pic-coh.md). Blocks T-PIC1b + all of stage P2
  (Pic group, (2.16)/(2.17)). · **Status**: open
- **[T-PIC-DEG0]** (scoping) fibre degree: audit HasseWeil divisor/degree anchor
  (ecosystem survey §3: ClassGroup/Pic⁰ machinery exists there); cut statements for
  deg of an invertible sheaf on fibres. Consumer: Pic^ν / (2.16). · **Status**: open
- **[CLEANUP-PIC1]** /cleanup InvertibleSheaf.lean after T-PIC1a+c+d ·
  **[CLEANUP-PIC2]** final (post-P1b when unblocked). · **Status**: open (cadence)

*Stage P2 (Pic group via Skeleton-units pattern of mathlib PicardGroup.lean) and the
GME (2.16)/(2.17) statements: cut AFTER T-PIC-GAP1 resolves. Semicontinuity ([Mum]
Cor 1) and Hida's surjectivity clause: explicitly out of pin, not cut (decomposition
records why).*

## Amendments v10.15 (2026-07-08): p0 report absorbed — GO on T-G3b–e against the pins; T-END0a gate re-check; DS-END0 registered

- **p0 report absorbed** (all three v10.2/v10.5 assignments closed):
  (1) **T-D6b reboxed** per protocol (81689211) — `comap_mul` does NOT unblock it; the true
  core is the absent étale layer (flf rank-N group scheme over a field, N invertible ⟹ finite
  étale ⟹ N distinct points; BB-DIFF / the (3)⟺(4) discriminant criterion). **That is EXACTLY
  the v10.10 stream [T-B5D]+[T-DISC]** — dependency edges recorded: the v10.10 worker is the
  un-blocker for T-D6b, T-D7-bridge and the T-D8-bridge box. beastmode-A's immediate re-claim
  (8e48acdd) + fresh route (33630479, "reduces to closed-in-étale-over-k̄ reduced") noted —
  the v10.14 wire PREEMPTS it until #5220 closes.
  (2) **T-KMQ DONE** — quote-debt ledger + reclassification banked; locator caveat for all
  future KM cites: **PDF page = print page + 11**.
  (3) **T-END0 first act DONE** (745cd328, 985d011d) — see the EOF leaf-ticket section.
- **DECISION (owner-relayed): GO — execute T-G3b/c/d/e against the DS-END0 pins NOW.** This is
  the DS-register pattern as designed: prove G3b (quadratic expansion), G3d (divisibility),
  G3e (positive-definiteness) from the pins; G3c by IMPORT of HasseWeil
  `hasse_bound`/degree-quadratic through the T-RED0 transfer. With
  `gme_deg_trace_forces_zero` already PROVEN, `aut_hom_eq_id_of_fullLevel` then closes modulo
  the registered data — rigidity lands for T-E10 / T-E9-rigid-half / T-H6 with the residual
  concentrated exactly in T-END0a/b.
- **T-END0a gate re-check (p0: do this FIRST)**: fable-P4's T-W7.7/T-W7b milestone left
  Rigidity.lean sorry-free (GIT 6.1→6.6), and T-E4a-noeth consumes C3′
  (`isMonHom_of_one_comp_eq'`) axiom-cleanly — so pointed-morphism-additivity IS proven over
  locally-noetherian bases. If that is the T-G2 statement END0a rests on, the ring instance is
  open NOW at loc-noeth generality: take the established future-proof pattern (T-E4a-noeth
  precedent) — state `Ring (End E)` under `[IsLocallyNoetherian S]`, drop-in swap to
  unrestricted when T-W7.8 lands. Park END0a only if the needed statement is verified-in-file
  to be genuinely the unrestricted one.
- **T-END0b's gate is a LIVE stream, not a deferral**: the Abel/Pic⁰ autoduality it rests on
  is fable-PIC0's claimed T-PIC0+COH-1 stream (v10.11). Dependency edge recorded both ways —
  fable-PIC0 should know T-END0b consumes their headline.
- **DS-END0 registered** in plan.md's DATA-SORRY REGISTER (coordinator repair of the
  same-commit rule — the skeleton commit predates the register entry).

## Amendments v10.16 (2026-07-08): D2 checkpoint — 00N0 CLOSED; B–E endgame is assembly; follow-on pointer

- **D2 report absorbed** (their own board commit f0a9123f): route A's make-or-break — **00N0,
  the Peskine–Szpiro acyclicity lemma — is CLOSED, axiom-clean**. All of: minor-ideal/McCoy ✓,
  Rees + flat-base-change-for-Ext (grade-locus openness) ✓, full depth API ✓, 00MZ + 00MYW ✓,
  00N0 ✓. Remaining for `buchsbaumEisenbud_acyclic`: `be_forward_core` (delegate running) +
  `be_backward_core` (unblocked by 00N0; dispatches when BuchsbaumEisenbud.lean frees). Then
  pure assembly: T-DEVISSAGE/T-ME/T-MI/T-REDUCEP in parallel, T-RB (all three inputs ready),
  T-FINAL — retiring `flatLocus_spreads_of_flat` → `isOpen_flatLocus` → 00R6 → FLAT1 →
  **entire Drinfeld D-chain axiom-clean**. No redirect; the lane stays do-not-disturb.
- **Follow-on pointer (D2: flag before claiming, after T-FINAL)**: the local-criterion toolbox
  this chain built (00MH ✓, 00RB/00MI via T-RB, B–E) covers most of what **BB-FLAT** — the
  fibrewise flatness criterion (EGA IV 11.3.10) behind **T-B4/T-B4x (KM 2.3.1, E[N] rank
  N²)** — still needs. That box is unowned and on the Y₁(N) path: the natural next claim.
- **Ops caution (fleet at full load, ~10 workers on this machine)**: delegates treat exit 143
  as OOM-not-failure; build single targets; the evidence-merge pattern applies.
- **Upstreaming note**: when the chain closes, D2 lists the mathlib-PR candidates from the
  ForMathlib output (FittingIdeals, BaseChangeExt, LocalCriterion, GenericFlatness,
  HilbertSyzygy, FiniteFreeResolution, Depth, Acyclicity) on the board for the future
  upstreaming lane.

## Amendments v10.17 (2026-07-08): c5β checkpoint — β2b headline banked; GO on the β1 scheme half

- **c5β report absorbed**: BOTH Bosma–Lenstra laws now provably land on the curve on every
  chart-product of the cover (`equation_lawTwoTriple_of_isDomain` /
  `equation_lawOneTriple_of_isDomain`), over any Jacobson domain with Δ a unit — which the
  universal atlas is. That is the complete certificate-free on-curve input for
  `addOnZ`/`addOnY`. Yesterday's "β1 must carry reducedness" finding is **RETRACTED**
  (superseded): the Y-chart fell to monic descent — `AdjoinRoot.isDomain_of_monic_of_map` +
  `HomogeneousLocalization.isDomain_away` (`ForMathlib/MonicQuotientDescent.lean`, both
  **UPSTREAM CANDIDATES** — added to the upstreaming list alongside D2's and fable-P4's).
  β1 algebra core DONE: `biChartRingTensorEquiv` via direct `AlgEquiv.ofAlgHom` (bypassing
  the ideal-image chase that made the ladder iterate five times).
- **GO (owner-relayed): c5β takes the β1 scheme half next.** The two boarded obstacles + fixes
  stand as the route: (i) explicit LOCAL `[Algebra R S]` instance for `pullbackSpecIso` where
  `awayι_projModelπ` factors through the degree-0 part via `gradeZeroRingEquiv`; (ii) upgrade
  `chartCoordEquiv` to an `AlgEquiv` (`chartCoordAlgEquiv`) — build it ONCE here, β3 consumes
  it too. Est. 150–250 lines; it is the single iso that unblocks BOTH β3 and β4.
- **DS-register note (clarifying c5β's caution)**: the register is not frozen — v10.8 requires
  any data-sorry to be REGISTERED with pins + a discharge plan terminating in a proof. For an
  iso of this size, building it directly (as c5β chose) is the better call; the register path
  is for genuinely-gated data only. The discipline shown here is the model.

### [T-END0] EXECUTION (p0, 2026-07-08, coordinator GO v10.15) — END0a foundation PROVEN
- **END0a gate CONFIRMED OPEN** (coordinator correction #1 verified): `endMonHom`
  (`EllipticCurve/EndomorphismDegree.lean`) **PROVEN axiom-clean** (`[propext, Classical.choice,
  Quot.sound]`) — a pointed endomorphism of `E/S` (`η ≫ f = η`) is a monoid hom `μ ≫ f = (f⊗f) ≫ μ`,
  under `[IsLocallyNoetherian S]`. Reuses the sorry-free T-W7.7 engine `isMonHom_of_one_comp_eq'`
  + `EllipticCurveGeom.universallyOConnected` + `SmoothOfRelativeDimension.smooth ⟹ Flat`. The
  `[IsLocallyNoetherian S]` drops out at T-W7.8 (EGA IV §8), per the T-E4a-noeth pattern. This is
  the additivity underlying END0a's `Ring (End E)`.
- **Consumer edges recorded** (coordinator #2): **T-END0b ← fable-PIC0's T-PIC0 + COH-1** (Abel/Pic⁰
  autoduality, v10.11 — `endDeg`/`endDual` data-sorry is *dischargeable*, not permanent); **T-END0a ←
  T-G2** (= `isMonHom_of_one_comp_eq'`, already sorry-free — so END0a's only residual is the
  `Ring`-instance packaging on top of `endMonHom`).
- **NEXT (p0)**: `endPostcomp_mul` (`(a*b) ≫ f = (a≫f)*(b≫f)` for pointed `f`, from `endMonHom` +
  cartesian `lift`) → ring algebra → **T-G3b** (deg quadratic from pins) → T-G3d/e → T-G3c (HasseWeil).

## Amendments v10.18 (2026-07-08): c5β — β1 CLOSED (bb5c86d9); β3/β4 unblocked; W7 endgame pointer

- **β1 CLOSED** (bb5c86d9): 111 lines (under the 150–250 estimate), zero sorries, axiom-clean.
  Both v10.17 obstacles resolved as the route of record predicted: (i) `chartAwayAlgebra`
  installed as the composite through `gradeZeroRingEquiv` makes `chartι_projModelπ` close by
  `rw [awayι_projModelπ]` alone — `pullbackSpecIso` applies verbatim; (ii) the `AlgEquiv`
  upgrade's commutes-obligation IS the existing `chartCoordEquiv_mk_C` — zero new math;
  `chartCoordAlgEquiv` built once for β3's consumption.
- **Deliverables**: `chartPieceIso : pullback (chartι i ≫ π) (chartι j ≫ π) ≅
  Spec (biChartRing W i j)` + `chartProductCover` (left-right cover of E ×_R E by
  chart-products). With β2b, the addition-law triples + on-curve theorems now read as regular
  functions on honest open subschemes of E ×_R E — the exact input for `addOnZ`/`addOnY`.
  **β3 and β4 are unblocked**; c5β continues (sentinel up): β3 per-(i,j,k) ring homs
  (well-defined via `equation_lawTwoTriple_of_isDomain`), β4 gluing via the six certified
  minors, then the four GroupLawConstruction.lean sorries fill.
- **Upstreaming list grows**: `AdjoinRoot.isDomain_of_monic_of_map` (the STRONGEST candidate —
  mathlib's `Affine.CoordinateRing` IsDomain instance hand-rolls exactly this descent, so the
  PR would shorten an existing mathlib proof), `HomogeneousLocalization.isDomain_away`,
  `quotientEquivQuotientMvPolynomial_symm_mk`.
- **W7 endgame pointer (after β4, flag before claiming)**: with 0c-i inc. 2 completing and
  1b merging via PR #5220, T-W7.12's outstanding deps reduce to **0c-ii (mulModelHom), 0h,
  1a** — a W7-endgame sequencing review is due then (who takes 0c-ii; status of 0h/1a), since
  T-W7.12 → T-W7.36 is the MILESTONE that retires `abelEnrichment_exists`.
- Ops note absorbed by c5β: β3 builds will be the heaviest yet — exit 143 = OOM, build single
  targets.

## Amendments v10.19 (2026-07-08): p0 session terminal — END0a foundation PROVEN; hold at the clean milestone

- **p0 report absorbed (session tally, 7 commits)**: T-D6b rebox (81689211, beastmode-A holds
  it post-wire), T-KMQ ledger + 3 closes (770edcc1), T-END0 first act (745cd328), leaf
  tickets (985d011d), **END0a foundation `endMonHom` PROVEN** (37ba2875): a pointed
  endomorphism of E/S is a monoid hom (`μ ≫ f = (f⊗f) ≫ μ`) over `[IsLocallyNoetherian S]`
  — the T-E4a-noeth drop-in-swap hypothesis, exactly as directed; axiom-clean. Both v10.15
  gate corrections verified: T-G2 gate IS open (`isMonHom_of_one_comp_eq'` sorry-free;
  Rigidity.lean:1560-1565 gave the instance recipe); T-END0b ← fable-PIC0 edge recorded (the
  DS-END0 data-sorry is dischargeable, not permanent).
- **DECISION (coordinator): HOLD — session ends at this clean milestone.** `endPostcomp_mul`
  needs an elusive mul-unfolding lemma; a long-session build-battle there is exactly the
  pattern this board's history says to avoid (whnf/diamond fights fall to fresh context +
  decomposition, not persistence). State is committed, honest (11 registered sorries: 3
  DS-data + 8 leaf theorems), and the route is boarded.
- **NEXT-UP note for the resuming session (p0-fresh or any worker — the route is boarded and
  claimable)**: `endPostcomp_mul` ((a·b) ≫ f = (a≫f)·(b≫f), from `endMonHom` + cartesian
  lift_map) → `Ring (End E)` instance → T-G3b (ring algebra vs the deg/dual pins) → T-G3c
  (HasseWeil `hasse_bound` import via T-RED0) → T-G3d/e. **Banked antidote for the
  mul-unfolding fight**: the repo has beaten the `Hom.group`-diamond/mul-unfolding wall
  before — see T-D6a-ii's `Functor.map_zpow'` note (`open scoped CategoryTheory.Obj`
  dissolved the diamond that blocked 6 direct attempts) and T-H2b's
  `Over.monObjMkPullbackSnd_mul_left_fst` / `Point.baseChangeEquiv` spellings — start from
  those patterns, not from scratch.

## Amendments v10.20 (2026-07-08): #5220 MERGED, 3/4 leaves wired — [T-W7.1b-faith] cut and assigned to beastmode-A; P3b3 released to T-IRR0

- **Wire report absorbed (beastmode-A)**: PR #5220 MERGED to dev/modular-curves, consumer
  verified, nothing broke. Import topology forced a clean relocation: the four ticketed
  leaves moved verbatim into a NEW capstone `EllipticCurve/Comparison.lean` above the stack
  (registered in root) — `ModelVariableChange.lean` is now SORRY-FREE. Discharged axiom-clean
  ([propext, Classical.choice, Quot.sound]): `pointedIsoCoordEquiv_coordX`/`_coordY`
  (← `exists_coord{X,Y}_image_of_filtration`, hfil := `pointedIsoCoordEquiv_filtration`) and
  `projModelVCIso_injective` (← `projModelVCIso_injective'`). Leaf sorry-count 4 → 1.
  **T-W7.1b correctly NOT flipped** — `main` still carries its sorry; T-W7.12's 1b dep stays.
- **Form-mismatch finding (real, recorded)**: `pointedIso_exists_variableChange` concludes in
  MODEL-MORPHISM form (`e.hom = eqToHom ≫ (projModelVCIso C ...)`) while the PR's main-alg
  delivers the COORDINATE-EQUATION form (∃ C, C•W'=W ∧ Φx'=u²x+r ∧ …). Bridging needs
  **faithfulness: `pointedIsoCoordEquiv` injective on morphisms** — not in the PR, and always
  integrator-side scope (the coordinate form WAS the agreed main-alg deliverable; no defect
  on P3b3's side).
- **NEW SUB-TICKET [T-W7.1b-faith]** (the last leaf): beastmode-A's scoped reduction is the
  route of record — coordEquiv-equal → cancel the fixed chart isos (b1 definition) →
  pointedIsoΓ-equal → cancel presheaf → `e.hom.app`-equal → the crux scheme-level step
  (chartZ_W ≫ e.hom factors through the Z'-chart, pinned by that app; Spec faithful;
  `hom_ext_of_affine`) + computing `pointedIsoCoordEquiv` of the eqToHom-transported
  `projModelVCIso` via `bridge_coordX/Y`. Bounded cancellation lemmas + one
  scheme-faithfulness step.
- **CLAIMED beastmode-A 2026-07-08 (in_progress → BLOCKED-REPORTED): T-W7.1b-faith.** Math CONFIRMED (S1 logic + `pointedIsoCoordEquiv_apply` function-level rfl interface, compiles; `ringEquiv_trans_mid_inj` generic cancel, compiles). BLOCKED by the b1 chart-iso layer's REDUCIBILITY/HEARTBEAT WALL: `chartZRingEquiv`, `basicOpenIsoAway`, `pointedIsoΓ`, `pointedIsoCoordEquiv` are near Lean's term-size limit, so ANY proof-level manipulation (`rw`, injectivity, type-ascription) triggers whnf/isDefEq exhausting 200k heartbeats — even under `local irreducible` (the chart isos in the wrappers still grind). FOUR routes tried (function-level, generic mid-cancel, small-goal rw, local-irreducible) — all wall. Closing needs b1-layer INFRASTRUCTURE: systematic irreducibility + a complete whnf-free interface (application/injectivity/cancellation lemmas) for the chart isos, done without breaking the merged b2/Comparison stack. A dedicated reducibility-engineering sub-development, best owned jointly with P3b3 (built the b1 layer). WIP committed (Comparison.lean green, S1+main sorried with the obstacle documented + salvaged interface lemmas). ESCALATING to coordinator: this is not a wire and not a few-iterations close.
- **ASSIGNMENT: beastmode-A takes T-W7.1b-faith NOW.** Rationale: A scoped the reduction and
  owns the b1/b2 (`pointedIsoCoordEquiv`) layer it sits on, and closing the W7 bottleneck's
  last comparison leaf outranks T-D33. On landing: discharge `main`, full-file axiom sweep,
  flip **T-W7.1b → DONE** (comparison milestone; T-W7.12's 1b dep flips ✓). T-D33 stays A's
  queued follow-on (then T-IRR0 fallback is RETIRED from A's list — it goes to P3b3).
- **P3b3 RELEASED from wire standby** (feedback = clean, no defect): proceed to **[T-IRR0]**
  per v10.14 — `/develop --decompose` scoping of the KM Ch. 10 route, v10.8 discipline.
- Also absorbed: A re-reboxed T-D6b with a sharper statement after their fresh-route attempt —
  the étale core remains the v10.10 stream's to discharge.

## Amendments v10.21 (2026-07-08): T-IRR0 DONE — PR #5221 MERGED; the convergence finding; P3b3 → [T-B5D]+[T-DISC]

- **P3b3 outran the directive**: T-IRR0 was already complete when the v10.20 release landed.
  `/develop --decompose` delivered: `decomposition-km10.md` (KM Ch. 10 quotes pinned per leaf
  — 10.1/10.2.5/10.6/10.8.2/10.9.1/10.9.2, PDF=print+11 confirmed independently),
  `ModularCurve/IrreducibilityScoping.lean` (3456 jobs green, 3 intended shell sorries),
  leaf tickets T-IRR1/2/3 (shell) + T-IRR-L2/L3/L5 (gap-streams).
  **PR #5221 MERGED by coordinator** (light review: new-files + board only, no held files).
- **HEADLINE FINDING (owner-relevant)**: KM Ch. 10's "algebraic route" is NOT analytic-free —
  Cor. 10.9.2 (p. 303) proves connectedness by reducing to the geometric generic fibre and
  then invoking the transcendental `M(𝒫)⊗ℂ ≅ ℍ/Γ̃`. Both routes bottom out at the SAME
  statement (`Y⊗ℂ ≅ ℍ/Γ̃` connected). Consequence: the shell (L1/L4/MASTER — the reduction)
  is buildable NOW; the core (L3 uniformisation + L2/L5) is **MAJOR-INFRA gated** on a
  scheme-analytification functor (GAGA-adjacent, mathlib-absent) + the LeanModularForms
  bridge — recorded as a FUTURE STREAM candidate, phase-3-aligned with the T-G* analytic
  comparison. Not staffed now.
- **Framing correction (v10.8 compliance)**: BB-IRR is NOT a "registered assumption" — it
  remains a sorried STREAM TARGET whose discharge route is now planned (shell first; core
  behind the named MAJOR-INFRA gaps), with every downstream use a tracked dependency edge
  per the v3 de-black-boxing rule. Nothing here becomes permanent.
- **P3b3 next claim: [T-B5D] + [T-DISC]** (v10.10) — sentinel sweep 2026-07-08T12:12 verified
  the étale-bottleneck stream was NEVER staffed. It is the highest-value unstaffed item on
  the board (reviewer work-order #4; T-D6b, T-D7-bridge and the T-D8-bridge box all funnel
  to it; feeds the T-E7 Y₁(N) milestone). `/develop --decompose` first act per v10.8; file
  discipline per v10.10 (new ForMathlib/bridge files only).
- Queue note: **[T-Q2-proofs]** (v10.12, SGA III landed) remains the next unstaffed stream
  after this — first worker to free takes it.

## Amendments v10.22 (2026-07-08): c5β sequencing correction ACCEPTED + β3 ring half done

- **Sequencing correction (c5β, accepted)**: the v10.18 endgame pointer UNDER-COUNTED —
  T-W7.12's outstanding dependencies are **0c-ii / 0h / 1a AND STILL 1b**, since
  `pointedIso_exists_variableChange` carries its sorry until [T-W7.1b-faith] (beastmode-A,
  v10.20) lands. The W7 endgame review fires when BOTH c5β's ticket finishes AND faith lands,
  and counts 1b until then. (v10.18's "reduce to 0c-ii/0h/1a" is superseded on this point.)
- **β3 checkpoint (d7bda67d, zero sorries, axiom-clean)**: `addOnYPieceHom` /
  `addOnZPieceHom : chartAway W k →ₐ[R] Localization.Away (triple k)` — the k-th chart
  morphisms of both addition laws on the (i,j) chart-product, via `chartAwayHomOfTriple`
  instantiated at the localization. Both hypotheses FREE: on-curve =
  `equation_lawTwoTriple_of_isDomain` (β2b), invertibility = the localization's `invSelf`.
  **Antidote banked**: `.toProjective` blocks the syntactic rewrite of
  `WeierstrassCurve.map_map` — apply the curve equality with `▸`.
- **State**: every ingredient of `addOnZ`/`addOnY` now exists at RING level over any Jacobson
  domain with Δ a unit (universal atlas included). Remaining in β3 is purely geometric
  (Spec + `Proj.awayι` to scheme morphisms; the three t_k-basicOpens cover the (i,j) piece),
  then β4's gluing via the six certified minors → the four GroupLawConstruction.lean sorries
  fill. c5β continues, sentinel up, no redirect.

## Amendments v10.23 (2026-07-08): T-W7.1b-faith → definitive wall finding; [T-W7.1b-faith-infra] cut; beastmode-A proceeds to T-D33

- **Definitive finding absorbed (beastmode-A)**: the faithfulness MATH IS CONFIRMED
  (`pointedIsoCoordEquiv_apply` — the function-level structural bridge — and
  `ringEquiv_trans_mid_inj` — generic mid-cancellation — both compile; S1's logic
  elaborates), but the proof CANNOT CLOSE: the b1 chart-iso layer (`chartZRingEquiv`,
  `basicOpenIsoAway`, `pointedIsoΓ`, `pointedIsoCoordEquiv`) sits at Lean's term-size limit —
  ANY proof-level manipulation (rw, injectivity application, even type ascription) exhausts
  200k heartbeats in whnf/isDefEq; only function-level `rfl` is cheap. FOUR routes walled:
  (1) function-level simp + injectivity → kernel timeout; (2) generic mid-cancel via
  `.toRingEquiv` → rfl on the reconstructed toRingEquiv kernel-times-out; (3) small-goal rw
  against the `_apply` interface → whnf timeout; (4) `attribute [local irreducible]` on the
  b1 defs → the chart isos inside the wrappers still grind. State: Comparison.lean GREEN
  (S1 + main sorried, obstacle fully documented in-file; the two interface lemmas salvaged);
  all committed + pushed. Milestone standing unchanged: 3/4 leaves merged axiom-clean,
  ModelVariableChange.lean sorry-free.
- **NEW SUB-TICKET [T-W7.1b-faith-infra]** — b1-layer reducibility engineering: systematic
  DEFINITION-LEVEL irreducibility + a complete whnf-free interface (application /
  injectivity / cancellation lemmas) for the four chart isos, engineered to not break the
  merged b2/Comparison stack. beastmode-A's scoping is the starting spec; the salvaged
  `_apply` + mid-cancel lemmas are its first two citizens. **FRESH-SESSION work by design**
  (the v10.19 lesson, re-affirmed: whnf walls fall to fresh context + decomposition, never
  tail-of-session persistence — four walled routes IS the stop signal). Default owner:
  beastmode-A's NEXT session; optional joint ownership with P3b3 at a natural boundary —
  P3b3 is NOT pulled off [T-B5D]+[T-DISC] (reviewer #4) for this. Ecosystem recipe pointer:
  the AdicSpaces fleet beat the same wall shape with def-level irreducible + opaque
  interface built BEFORE the proofs + direct instance heads — same family as A's scoping.
- **Schedule note**: 1b has slack — the W7 endgame review (v10.22) also waits on c5β's
  0c-chain (0c-ii not started). faith-infra must land before THAT review, not before T-D33.
- **DECISION: beastmode-A proceeds NOW to [T-D33]** (subgroup-divisor locus over U; deps
  T-D14 ✓ / T-D15 ✓; their `IsSubgroup.baseChange` from T-D6a-ii is the freshest context on
  the board). Queue after: T-W7.1b-faith-infra as the next session's first act.

## Amendments v10.24 (2026-07-08): OWNER POLICY — slowdown ⟹ decompose (BINDING, all lanes)

*Owner directive (2026-07-08): "if we are hitting slowdowns that means we need to break up
proofs more." Elevated to binding policy, in the two forms the evidence supports:*

- **(a) Proof-level**: any proof that times out or crawls is split into private helper lemmas
  IMMEDIATELY — never ground through, never `set_option maxHeartbeats` (already banned by the
  cleanup cadence; a proof needing it is a proof needing decomposition). Precedent: c5β's
  >150-line proof → 3 private lemmas, zero heartbeat bumps, green.
- **(b) Definition-level** (the T-W7.1b-faith lesson): any definition of chart-iso scale ships
  **in the same increment** as its opaque interface — `_apply` / injectivity / cancellation
  lemmas, with `irreducible` set so consumers only ever touch the interface, never the raw
  term. A heavy definition without an interface is technical debt that lands on the NEXT
  ticket: b1 was built interface-free and its bill came due one ticket later as a four-route
  whnf wall ([T-W7.1b-faith-infra] is the retro-fit).
- **Prospective application to every live heavy layer**: c5β's β3-geometric/β4 gluing (already
  flagged heaviest-yet), P3b3's B5D ψ_N bridge, the End(E/S) ring-layer resume, fable-PIC0's
  Pic layer, D2's B–E assembly. Workers: when you feel elaboration slow down, STOP and split —
  the slowdown IS the signal, and four walled routes is far past it.
