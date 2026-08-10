# Decomposition — Finite-jet pinching (Campaign 4, 2026-07-16)

Source: **[FJP]** *Finite-jet pinching: a uniform strongly sheafy domain which is not stably
uniform*, Anonymous, 16 July 2026, 27 pp. Local copy: `refs/AdicSpaces/sheafyring.pdf`
(local-only, never committed). All quotes below are verbatim from that PDF; page numbers refer
to it. §7 (derived) is out of scope by owner instruction.

## §0 Source-verification provenance (the owner's "check very carefully" mandate)

The paper was verified in **three independent passes** before this decomposition was accepted:

1. **Planner pass** (inline, twice over §§1–6 during reading): checked every proof step,
   including the support-monoid closure cases of (1.8), the quotient-norm = max computations,
   `KJ = Q³𝒞` both inclusions, the (3.3) collapse `y = ϖⁿXⁿ(W⁻ⁿy)`, all constant-chases of
   §4, and the §5 gluing chain. **No errors found.**
2. **Hostile referee pass on §4** (the sheafiness-critical strict-localization machinery):
   attacked Lemmas 4.1–4.6 and Prop 4.5 with mandated kill-shots. Highlights: the m = 1
   degeneration (⋀² = 0) was attacked with explicit candidate zero-divisor data — the
   candidate `gT−f` is always monic-after-localization or a unit, `ann = 0`; the
   flat-base-change step was attacked — completion is flat but **not faithfully flat**, and
   `H₀` genuinely collapses (at the 𝒞-vertex with datum `(W; ϖ)`, `r = ϖT − W` becomes a unit
   with inverse `−W⁻¹∑(ϖW⁻¹)ⁿTⁿ`, so `C_α = 0` — exactly [FJP] Remark 3.3); the paper claims
   only positive degrees transfer, which is all it uses. Koszul unit-scaling needs the
   wedge-scaling isomorphism `e_{i₁}∧…∧e_{i_j} ↦ (∏ u_{i_t})·e_{i₁}∧…∧e_{i_j}` (recorded for
   the implementer). **Verdict: all of §4 SOUND, no bugs, no gaps.**
3. **Hostile referee pass on §§1–3, 5, 6**: attacked all eleven flagged claims by explicit
   computation (support additivity subcases; `(f+Qg)ⁿ = fⁿ + nf^{n−1}Qg` both directions;
   `𝒜° = 𝒜₀` via the restriction-of-multiplicative-norm; the `1 = 0` evaluation happening
   inside `k⟨W⟩`, never on `L`; embedding-cancellation and the OMT upgrade; `S_d` additivity
   for §6). **Verdict: all SOUND.** Two presentational nits only (multiplicativity of the
   evaluation map in Lemma 1.1 asserted-not-derived — routine density argument; the
   finite-covers reduction feeding the sheaf-on-basis argument left tacit) — both are
   handled explicitly in our leaves.

**V0 gate (consumed-theorem check), run 2026-07-16**: `lean_verify` on
`ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` returns axioms
`[propext, Classical.choice, Quot.sound]` — **axiom-clean, no sorryAx**. The 828b input to
this campaign is genuinely proven. (File-level sorries in `WedhornCechAcyclicity.lean`/
`Cor832.lean`/`FaithfulLocLift.lean` are off its dependency cone.)

## Skeleton location

Every leaf below exists as a `:= by sorry` declaration. `lake build «Adic spaces».FiniteJetMain`
**passes (3084 jobs, sorries only, no type errors)** — verified 2026-07-16. Files (all under
`projects/AdicSpaces/Adic spaces/`):

| File | Leaves (sorry count) | [FJP] |
|---|---|---|
| `RestrictedLaurent.lean` | 63 | §1, Prop 2.3 (L-layer) |
| `JetDualNumberNorm.lean` | 20 | §1.4, (5.2) power formula |
| `FiniteJetRings.lean` | 58 | Def 1.2, Prop 2.1, Lemma 2.2, (2.1a–d) |
| `FiniteJetUniformDomain.lean` | 14 | Prop 2.3, Prop 2.4, (5.2) |
| `FiniteJetNoetherianVertices.lean` | 12 | Prop 2.1 (strong noeth), Thm 5.3 input |
| `FiniteJetGraphKoszul.lean` | 15 | Lemma 4.2 |
| `FiniteJetStrictLocalization.lean` | 25 | Lemmas 4.1, 4.3, 4.4, Prop 4.5 |
| `FiniteJetFunctoriality.lean` | 53 | Lemma 1.1, 4.6, 5.1 |
| `FiniteJetSheafTransfer.lean` | 3 | Lemma 5.2, Thm 5.3 |
| `FiniteJetChart.lean` | 10 | Prop 3.1, Cor 3.2 |
| `FiniteJetMain.lean` | **0** | Thm 1.3 (assembly compiles from the leaves) |

Naming: `𝓐 = FiniteJet.JetA F`, `𝓑 = JetB F = DualNumber (K⟨W⟩)`, `𝓒 = JetC F = (L F)⟨Q⟩`,
`𝓓 = JetD F = DualNumber (L F)`, `L F = RestrictedLaurent K`, `K = LaurentSeries F`.

---

## Result R1 (PRIORITY): `FiniteJet.finiteJet_isSheafy : IsSheafy (JetA F)`

### Plain-English proof ([FJP] structure preserved)

[FJP] Thm 5.3 via Lemma 5.2: the square `𝓐 → 𝓑, 𝓒 → 𝓓` is a strict Milnor square of Huber
pairs (Prop 2.1 + (5.2)); every rational localization of 𝓐 preserves the square strictly
(Prop 4.5, built from Lemma 4.1 Tate-extension, Lemma 4.2 graph–Koszul at the affinoid
vertices, Lemma 4.3 controlled ideal pullback, Lemma 4.4 strict quotient); the three vertices
are strongly noetherian (Prop 2.1) hence sheafy (Huber Thm 2.2 = our `828b`); the gluing and
embedding conditions for 𝓐's rational coverings transfer through the localized rows (Lemma
5.2's chain: push matching family → glue at 𝓑, 𝓒 → 𝓓-separatedness matches the images →
row-exactness produces the section → per-piece injectivity recovers restrictions; embedding
via closed equalizer + Tate OMT).

Layered as M1 (construction) → M2 (vertices sheafy) → M3 (graph–Koszul) → M4 (strict
localization) → M5 (functoriality/bridges/loc-lift) → M6 (transfer).

### M1 — construction layer

- **L1.1** (cluster, `RestrictedLaurent.lean`, decls `instOne/instAdd/instNeg/instMul`,
  `summable_mul_coeff`, `instCommRing`, `single`, `single_mul_single`, `C`, `W/Wu`):
  the ring `L = k⟨W,W⁻¹⟩`.
  - Source: [FJP] p. 5 (1.4) "`L = k⟨W,W⁻¹⟩` … Thus `L` is the radius-one Laurent algebra; in
    particular both `W` and `W⁻¹` are power-bounded", and p. 5 (1.8) "An element is a series
    `∑_{(a,b)∈S} c_{a,b}W^aQ^b` such that, for every ε > 0, only finitely many coefficients
    have `|c_{a,b}| ≥ ε`; its norm is `sup |c_{a,b}|`."
  - Lean ↔ source: `RestrictedLaurent R` = coefficient functions `ℤ → R` with cofinite decay;
    convolution `(f*g) m = ∑' a, f a · g (m−a)`; the `Q`-free specialisation of (1.8).
  - Discharge: convolution summability from `CompleteSpace K` + ultrametric summability
    (mathlib `Summable` nonarch criteria; cf. vendored stack's analogous sums); ring axioms
    by `tsum` manipulation (mathlib `tsum_add`, Fubini `Summable.tsum_comm`-style over ℤ×ℤ).
  - Attacks: (1) counterexample search — convolution of two-sided-infinite series without
    decay diverges; decay hypothesis present on both factors; termwise product family is
    null on the antidiagonal filter — verified by hand estimate `‖f_a g_{m−a}‖ ≤ ‖f_a‖·‖g‖`
    with `f_a → 0`, cofinally small. (2) edge cases: `m = 0` index, `f = 0`, monomials —
    `single_mul_single` gives `W^a·W^b = W^{a+b}` ✓. (3) hypothesis strength — completeness
    of the base genuinely needed for `tsum` (drop it and `Mul` is junk): recorded on the
    instance. Verdict: SURVIVED.
- **L1.2** (`gaussNorm`, `exists_gaussNorm_eq`, `isRingNorm`, `NormedCommRing`,
  `IsUltrametricDist`, `norm_single`, `norm_W`, `norm_W_mul`, `CompleteSpace`):
  the Gauss norm package.
  - Source: p. 7 Prop 2.3 "the coefficient family of a restricted Laurent series tends to
    zero, so its nonzero coefficient supremum is attained"; p. 1 "All Banach direct sums
    carry the maximum norm."
  - Discharge: mirrors vendored `CoramRestrictedNorm` (`RingNorm.toNormedRing` pattern —
    already used in the skeleton); completeness mirrors `Restricted.isCompleteSpace`
    (coefficientwise Cauchy).
  - Attacks: (1) sup attained requires decay — non-restricted series attain no max; decay in
    the type. (2) `‖W·f‖ = ‖f‖` fails for non-shift-invariant norms — here coefficients
    shift, sup invariant ✓. (3) `eq_zero_of_map_eq_zero'` needs norm-faithfulness — sup of
    norms = 0 forces all coefficients 0 ✓. Verdict: SURVIVED.
- **L1.3** (`norm_mul_eq`, `mul_ne_zero_of_ne_zero`; consumed by
  `FiniteJetUniformDomain.norm_L_mul`, `norm_JetC_mul`):
  multiplicativity over discretely valued K.
  - Source: p. 7 Prop 2.3, quoted in §0 pass 3; full passage: "Since every nonzero
    coefficient norm belongs to `|k^×|`, so does every nonzero Gauss norm. We may therefore
    scale two nonzero elements to norm one. Their reductions are nonzero Laurent polynomials
    in `k̃[W,W⁻¹,Q]` … restrictedness leaves only finitely many coefficients of norm one.
    Their product remains nonzero because this Laurent polynomial ring is a domain. Reduction
    commutes with the Laurent convolution here: coefficients of norm less than one have norm
    at most `|ϖ|` … Consequently the product in 𝒞 again has norm one."
  - Discharge (two admissible routes, worker chooses): (a) residue-reduction as in source —
    reduction to `AddMonoidAlgebra F ℤ` resp. `F[ℤ×ℕ]`, domain via mathlib
    `AddMonoidAlgebra` `IsDomain` (`UniqueProds` for ℤ, ℤ×ℕ ✓); needs
    `FiniteJetRings.norm_K_discrete` (leaf: `∃ n, ‖x‖ = 2^n`, from the `RankOne`
    normalisation `WithZeroMulInt.toNNReal 2` in `ExampleUnitDisc.lean`); (b) lex-achiever
    argument mirroring vendored `MvRestricted.isAbsoluteValue` with index ℤ (min-index
    achiever; discreteness gives attained max cleanly).
  - Attacks: (1) discreteness genuinely used — over ℂ_p-like base the "norm < 1 ⟹ ≤ |ϖ|"
    step fails; our `K` is discrete ✓ (recorded as the reason for DD1). (2) the ℤ×ℕ support
    version: finitely many norm-one coefficients — needs two-sided decay ✓ (referee pass 3
    verified). (3) `𝒞`-case via base-`L` multiplicativity + vendored univariate mult lemma:
    the vendored `Restricted.gaussNorm_mul_eq_mul` hypothesis shape must be checked at
    implementation (risk item 2, plan.md); fallback route (b) stated. Verdict: SURVIVED
    (with recorded fallback).
- **L1.4** (`nonnegSubring`, `isClosed_nonnegSubring`, `nonnegEquiv`, `ofRestricted`,
  `evalHom`, `evalHom_surjective`): `k⟨W⟩ ⊂ L` and the affinoid presentation surjection.
  - Source: p. 6 Lemma 2.2 "In the Laurent expansion of `L`, the subspace `k⟨W⟩` is the
    intersection of the kernels of the continuous negative-coefficient maps `[W^a] : L → k`
    for `a < 0`; it is therefore closed." and p. 5 Prop 2.1 "Each of ℬ, 𝒞, 𝒟 is a quotient
    of a finite Tate algebra over k".
  - Lean ↔ source: `evalHom : K⟨W,V⟩ → L` (`W ↦ Wu, V ↦ Wu⁻¹`) is *our* realisation of the
    quotient presentation; we keep only **surjectivity** (norm-preserving monomial section
    `W^a ↦ W^a (a ≥ 0), V^{-a} ↦ W^a (a < 0)`), because noetherianity transfers along
    surjections — the kernel is never needed (planner simplification, recorded; the source's
    "quotient of" is implied by surjectivity).
  - Attacks: (1) coefficient functionals continuous — norm-decreasing ✓. (2) `nonnegEquiv`
    multiplicative — supports in ℕ closed under addition ✓. (3) `evalHom` well-defined on
    *restricted* two-variable series: image coefficients regroup along `a = i − j`; decay
    preserved (max over the fibre) — checked by hand; the section makes surjectivity
    constructive. Verdict: SURVIVED.
- **L1.5** (`JetDualNumberNorm.lean` cluster: `isRingNorm`, instances, `pow_eq`, `mapHom`,
  `norm_mapHom`, `aeval_eps_surjective`, `isNoetherianRing`): the jet-vertex norm layer.
  - Source: p. 6 Lemma 2.2 "`‖b‖_ℬ = max{‖f₀‖, ‖f₁‖}`"; p. 17 (5.2) "(f + Qg)ⁿ = fⁿ +
    nf^{n−1}Qg is bounded independently of `n` (recall that `|n| ≤ 1`)".
  - Discharge: max-norm submultiplicativity via ultrametric on the cross term (planner
    verified: `‖ad+bc‖ ≤ max ≤ ‖x‖‖y‖`); noetherianity via `Polynomial.aeval ε` surjective
    (mathlib `isNoetherianRing_of_surjective`).
  - Attacks: (1) `pow_eq` at `n = 0,1` (edge): `n·a^{n−1}` term — `n=0` gives `0·a^{-1}` —
    in ℕ-subtraction `a^(0−1) = a^0 = 1`, coefficient `(0:R)` kills it ✓ statement checked
    at `n = 0` by hand. (2) norm well-defined vs `TrivSqZeroExt` topology diamond — mathlib
    pin has **no** `TopologicalSpace (TrivSqZeroExt ..)` instance (checked); our norm is the
    only topology. (3) `eq_zero_of_map_eq_zero'` ✓ max = 0 forces both components 0.
    Verdict: SURVIVED.
- **L1.6** (`FiniteJetRings.lean` cluster: `rhoC`, `rhoB`, `sectionD` + its four lemmas,
  `jetSupport`, `isClosed_jetSupport`, `jB`, `square_commutes`,
  `mem_jetSupport_iff_jet_in_range`, `milnorRow_exact`, `max_norm_eq`,
  `difference_strict_surjective`): the square and the strict row, constants 1.
  - Source: p. 5 Prop 2.1 (verbatim): "Reduction modulo `Q²` has the norm-preserving linear
    section `f₀+Qf₁ ↦ f₀+Qf₁`, so `𝒞 → 𝒟` is a strict surjection. The difference map in
    (2.1) is therefore a strict surjection of Banach spaces. Its kernel is the algebraic
    pullback (1.6); since 𝒟 is Hausdorff, this kernel is closed. This proves completeness of
    𝒜 and strict exactness." p. 6 Lemma 2.2 (verbatim): "Projection to 𝒞 is an isometric
    embedding of 𝒜 with image (1.7)." p. 6 (2.1b): "the Milnor row is already exact
    integrally … Thus the two denominator losses in the defining square are zero."
  - Lean ↔ source: our 𝓐 *is* the image (1.7) (subring model), so Lemma 2.2's isometry is
    definitional; `milnorRow_exact` is (1.6)-cartesianness; all constants 1 = (2.1b).
  - Attacks: (1) support additivity `b+b' ≤ 1` subcases (pass 3 verified exhaustively —
    `(−5,2)+(3,0)` lands in `b = 2`, unconstrained; no leak into jets). (2) `sectionD`
    multiplicativity is NOT claimed (it is linear only — [FJP] "linear section"); statement
    set records only `sectionD_add` + `rhoC_sectionD` + norm ✓ (a multiplicative-section
    claim would be FALSE: `(1+Q)·(1+Q)` jets ≠ section product — attack found this would be
    an over-claim; statements avoid it). (3) `mem_jetSupport_iff_jet_in_range` — range of
    `ρB` = pairs with both components in `nonneg` ✓ needs injectivity of `ofRestricted` ✓
    leaf present. Verdict: SURVIVED (one over-claim avoided by design).
- **L1.7** (instance stack: `IsHuberRing/IsTateRing ×4`, `PlusSubring ×4` (maximal),
  `IsRingOfIntegralElements ×4`, `IsUniformAddGroup ×4`, right-uniformity
  `CompleteSpace ×4`, `unitBall`, `isOpen_unitBall`, `constC/constA/tA` cluster):
  - Source: p. 17 before (5.2): "Give every ring its maximal plus ring of power-bounded
    elements." (5.2) computations; p. 17: "the rings in (5.2) are valid maximal plus rings. A
    bounded homomorphism sends power-bounded elements to power-bounded elements; hence every
    map in (5.1) is a morphism of Huber pairs. The plus rings of ℬ and 𝒟 are unbounded,
    which is permitted for a ring of integral elements."
  - Discharge: `ExampleUnitDisc.lean` pattern (`podD`, `IsHuberRing`, `IsTateRing`,
    right-uniformity bridge `SeminormedAddCommGroup.to_isUniformAddGroup` — already realised
    in the skeleton as term-level instances where possible). `IsRingOfIntegralElements` for
    the maximal plus ring: open (⊇ unit ball), integrally closed ([FJP] §5's monic-equation
    argument, p. 17, quoted in §0 pass 3), `subset_powerBounded` = refl.
  - Attacks: (1) **B2-log echo** (`IsPowerBounded.map` false in general): all our maps are
    norm-≤ 1 ring homs of normed rings — power-bounded transfer is via norm bounds, never via
    bare continuity ✓ statements phrased with norms. (2) unit-ball-as-plus-ring for 𝓑 would
    be WRONG (not integrally closed: `λQ` with `|λ|>1` is integral, `x² = 0`) — maximal plus
    ring chosen instead; recorded as the reason. (3) `AffinoidRings.IsRingOfIntegralElements`
    has no boundedness field (checked at `AffinoidRings.lean:47`) — unbounded plus rings
    admissible ✓ (risk item 5 closed). Verdict: SURVIVED.

### M2 — vertices strongly noetherian and sheafy (`FiniteJetNoetherianVertices.lean`)

- **L2.1** `isNoetherianRing_restricted_L (m)`:
  - Source: p. 5 Prop 2.1 "Each of ℬ, 𝒞, 𝒟 is a quotient of a finite Tate algebra over `k`,
    so each is strongly noetherian." (`L` case: `L⟨Z₁..Zₘ⟩` is the image of `K⟨W,V,Z₁..Zₘ⟩`.)
  - Discharge: `evalHom`-style surjection extended by `Z`-variables (compose vendored
    `restrictedGaussEquiv` bridge + `mapRestricted (evalHom)` + flattening
    `exists_flatten'`-pattern) + `isNoetherianRing_of_surjective` +
    `IsStronglyNoetherian K` (`ExampleLaurentSeries.lean`, proven).
  - Attacks: (1) **B2 echo T-SUM-6/T-Q4**: never argue "noetherian ⟹ strongly noetherian";
    each arity gets its own surjection ✓ statement is per-`m`. (2) surjectivity of the
    extended map — coefficientwise lift via the monomial section, decay preserved ✓ (same
    computation as L1.4 attack 3). (3) the topological-vs-Gauss restricted bridge at base `L`
    — `restrictedGaussEquiv` requires radius-1 and `NormedCommRing L` ✓ available. Verdict:
    SURVIVED.
- **L2.2** `IsStronglyNoetherian (JetC F)`; **L2.3** `isNoetherianRing_restricted_dualNumber`
  + `IsStronglyNoetherian (JetB F)`, `(JetD F)`; **L2.4** unit-ball noetherianity ×4
  (`isNoetherianRing_unitBall_*`).
  - Source: same Prop 2.1 sentence; for L2.4, p. 11 Lemma 4.2's construction "Put
    `A₀ = k°⟨Y₁,…,Y_s⟩` … The ring `A₀` is noetherian and ϖ-adically complete" — our unit
    balls are the concrete such rings (`DualNumber (k°⟨W⟩)`, `L₀⟨Q⟩`, `DualNumber L₀`).
  - Discharge: L2.2 = disc-example flattening verbatim over base `L`; L2.3 = jet flattening
    `(DualNumber S)⟨Z⟩ ≅ DualNumber (S⟨Z⟩)` (coefficientwise) + `JetNorm.isNoetherianRing`;
    L2.4 via `k° = F⟦X⟧` noetherian + integral restricted rings as ϖ-adic completions
    (mathlib `AdicCompletion` noetherianity; project `AdicCompletionBridge.lean` has the
    bridge pattern) + quotient/surjection closure.
  - Attacks: (1) **B2 echo L16**: "strongly noeth ⟹ noeth A₀" is FALSE generically — we
    never use it; each unit ball gets its own concrete proof ✓. (2) `DualNumber S` noeth
    needs `S` noeth only ✓ (S[X] surjection, Hilbert basis). (3) completeness of `k°⟨W⟩` vs
    `AdicCompletion` identification — the classical bridge; if the project bridge doesn't
    fit, fallback: direct Hilbert-basis-for-restricted-series argument (BGR 5.2.6 style;
    or transport along `Psi`-style transpose as in `ExampleLaurentSeries`'s
    `IsStronglyNoetherian K` proof, which already handles exactly this shape). Verdict:
    SURVIVED with recorded fallback.
- **L2.5** `isSheafy_JetB/C/D`:
  - Source: p. 21 Thm 5.3 proof (verbatim): "The three comparison rings are strongly
    noetherian. Huber's direct sheaf theorem [4, Theorem 2.2] gives the rational-cover sheaf
    condition for their structure presheaves."
  - Discharge: `isSheafy_of_stronglyNoetherian_828b` (V0-verified axiom-clean). The full
    hypothesis bundle is supplied by M1 instances + L2.2/L2.3. Non-reducedness of 𝓑, 𝓓 is
    admissible (bundle has no domain hypothesis — checked; [FJP] Lemma 4.2 "possibly
    nonreduced" mirrored).
  - Attacks: (1) instance-resolution: the `letI` right-uniformity binder shape matches our
    declared `@CompleteSpace _ (rightUniformSpace _)` instances (disc pattern) ✓.
    (2) `T2Space` from metric ✓ automatic. (3) `hasLocLiftPowerBounded_faithful` requires
    `IsNoetherianRing` — vertices are noetherian ✓ (it is 𝓐 that needs the bespoke route,
    L5.6). Verdict: SURVIVED.

### M3 — graph–Koszul (`FiniteJetGraphKoszul.lean`) — [FJP] Lemma 4.2 in degrees ≤ 2

- **L3.1** `d1_d2` — trivial sign computation (source p. 10 sign convention displayed).
- **L3.2** `syzygy_coordinate`:
  - Source: p. 11 "The coordinate sequence is regular over an arbitrary coefficient ring:
    successive quotients are polynomial rings in the remaining variables, in which
    multiplication by the next variable is injective."
  - Discharge: elementary induction on `m` (planner wrote the full induction by hand:
    reduce mod `T_m`, apply IH over the smaller polynomial ring, correct with
    `T_m e_j − T_j e_m` relations; ~all-tactic). No mathlib Koszul needed.
  - Attacks: (1) `m = 0,1` edges — `m=1`: `u₁T₁ = 0 ⟹ u₁ = 0` (poly ring over any base,
    mul-by-variable injective) ✓ `Pairs 1 = ∅` so conclusion is `u = 0` — consistent ✓.
    (2) arbitrary base ring (nonreduced!) — the induction never divides ✓. (3) mathlib
    negation search: no contradicting lemma. Verdict: SURVIVED.
- **L3.3** `syzygy_graph_polynomial`:
  - Source: p. 11 (quoted in full in the file docstring — the two-case prime argument,
    (4.3), translation, unit scaling).
  - Discharge: localization at primes (`Submodule.eq_top_of_localization_maximal`,
    mathlib, verified present), two cases: `r_i` unit (explicit Koszul expression of any
    syzygy when one entry is a unit — planner verified the formula
    `u = ∑_{j≠i} (u_j/r_i)(r_i e_j − r_j e_i)` reproduces `u` using `∑ u_j r_j = 0`);
    `g` unit + translation automorphism (`MvPolynomial.aeval` substitution
    `T_i ↦ T_i + f_i/g`) + unit scaling of syzygies + L3.2.
  - Attacks: (1) the referee's m=1 kill shot — defeated (see §0 pass 2). (2) unit-scaling
    correctness — the wedge-scaling form recorded; in degrees ≤ 2 it is
    `v_{ij} ↦ u_i u_j v_{ij}` — planner checked commutation by hand. (3) localization of the
    quotient module Syz/Koszul commutes (localization exact, finite presentation not needed
    for eq_top-detection over maximal ideals ✓ mathlib lemma is for arbitrary submodules).
    Verdict: SURVIVED.
- **L3.4** `mapRestricted` + `norm_mapRestricted_le` — coefficientwise functoriality
  (elementary; decay via `‖φ x‖ ≤ ‖x‖`).
- **L3.5** `polyToP`, `flat_polyToP`:
  - Source: p. 11–12, (4.4) and "Noetherian adic completion is flat [8, Lemma 10.97.2, Tag
    00MB], and localization preserves flatness."
  - Discharge: `polyToP` via vendored `MvPolynomial.toMvRestricted`;
    (4.4) `P_E ≅ (E₀[T])^∧_ϖ[1/ϖ]` with `E₀ = unitBall E` noetherian (L2.4);
    `AdicCompletion.flat_of_isNoetherian` (mathlib, verified present at
    `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean:379`) + localization flat +
    `Module.Flat.comp/baseChange`.
  - Attacks: (1) faithful-flatness NOT claimed (would be FALSE — §0 pass 2's `C_α = 0`
    example); only positive-degree transport stated ✓. (2) the (4.4) identification is the
    heaviest sub-leaf — sub-decomposed in the ticket into: integral restricted series =
    ϖ-adic completion of `E₀[T]` (coefficientwise; `AdicCompletionBridge.lean` pattern) and
    the `[1/ϖ]` comparison; referee pass 2 verified the mathematical content (e). Verdict:
    SURVIVED.
- **L3.6** `syzygy_graph_restricted`:
  - Source: p. 12 "Hence flat base change preserves the positive-degree exactness."
  - Discharge: L3.3 + L3.5 + "kernel of a matrix map commutes with flat base change"
    (mathlib `Module.Flat` exactness API: flat ⟹ `lTensor` preserves kernels; the syzygy
    module of `(r_i)` over `P` = `P ⊗ Syz_{E[T]}` and the Koszul span is generated by the
    same elements).
  - Attacks: (1) base-change identification of `Fin m → ·` with tensors — finite free ✓.
    (2) the span generation transfers by `Submodule.span` image lemmas ✓. Verdict: SURVIVED.
- **L3.7** `isClosed_graphIdeal`, **L3.8** `exists_d1_lift`, **L3.9** `exists_d2_lift`:
  - Source: p. 12 (verbatim): "Finally, `P_D` is a complete noetherian Tate ring. Every
    term, kernel, and image in the Koszul complex is a finite `P_D`-module … Huber's
    finite-module theorem [4, Lemma 2.4(ii)] makes `K_{j+1} ↠ B_j` and `B_j ↪ K_j` strict.
    … A complete subspace of the Hausdorff Banach space `K_j` is closed."
  - Discharge: `NoetherianTateModules.lean` (module topology = Banach topology on finite
    frees via `IsModuleTopology` Pi instances; surjections open; finite modules complete)
    + `IdealClosedness.lean` Krull closedness where convenient + OMT-with-constants
    (`ContinuousLinearMap.exists_preimage_norm_le`, needs the `NormedSpace K`-structure on
    `P` and closed-range corestriction — a small `NormedSpace K (P E m)` instance leaf is
    folded into the ticket).
  - Attacks: (1) circularity check ([FJP] referee (h)): the canonical topology on `P^m` IS
    the max-norm topology — via `IsModuleTopology` uniqueness over the Tate `P` ✓ project
    has exactly this machinery (Wedhorn 6.18). (2) `P` noetherian required — supplied by
    vertex strong noetherianity (M2), never by a generic principle ✓. (3) OMT over `K`
    (nonarch complete) — mathlib's Banach OMT is field-agnostic ✓. Verdict: SURVIVED.

### M4 — strict localization (`FiniteJetStrictLocalization.lean`)

- **L4.1** cluster (`ext_square_commutes`, `extRhoC_strict_surjective`,
  `ext_milnorRow_exact`, `ext_max_norm_eq`, `ext_pair_injective`):
  - Source: p. 10 Lemma 4.1 (verbatim in file docstring): coefficientwise lifting; "If
    `b = ∑ b_ν T^ν` and `c = ∑ c_ν T^ν` have the same image, each coefficient pair comes
    from a unique `a_ν ∈ R`, with `‖a_ν‖ ≤ ρ max{‖b_ν‖, ‖c_ν‖}`."
  - Discharge: coefficientwise application of L1.6's row (constants 1 make the decay
    bookkeeping trivial: `‖a_ν‖ = max` ✓).
  - Attacks: (1) referee pass 2 attack 1–2 verified the uniform-constant necessity — ours
    are 1 ✓. (2) `MvPowerSeries.map` coefficient formula (`map_coeff`) drives everything ✓.
    Verdict: SURVIVED.
- **L4.2** `span_pushed_B/C/D`:
  - Source: p. 12 "After mapping to each of the k-algebras B, C, D, the tuple `(g, f₁,…,f_m)`
    therefore generates the unit ideal."
  - Discharge: `Ideal.span` image lemmas: `1 = a₀g + ∑ aᵢfᵢ` pushes through ring homs.
  - Attacks: trivial; edge `m = 0` — datum `{g}` with `g` generating ⊤ ✓ pushes. SURVIVED.
- **L4.3** `ideal_row_surjective`, **L4.4** `ideal_pullback_controlled`, **L4.5**
  `isClosed_IA`:
  - Source: pp. 12–13 Lemma 4.3 (verbatim statement in file docstring; the full
    constant-chase (4.11)–(4.16) re-derived independently by referee pass 2 and the planner
    — every displayed bound matches).
  - Discharge: L3.7/L3.8 at 𝓑, 𝓒, 𝓓 (via L4.2's unit-ideal push) + L3.9 at 𝓓 + L4.1's
    lifting; closedness: `I_𝓐` = preimage of the closed
    `(I_𝓑 × I_𝓒) ∩ ker(difference)` under the L4.1-embedding.
  - Attacks: (1) m = 1 degeneration — `Pairs 1 = ∅` forces `ker d₁ = 0` at 𝓓, which L3.9
    delivers (referee-verified); the chase degenerates gracefully (planner re-checked:
    `s = 0` forced). (2) sign consistency `d₁∘d₂ = 0` in the correction step — L3.1.
    (3) the "canonical map injective" needs `P_𝓐 ↪ P_𝓑 ⊕ P_𝓒` — L4.1 `ext_pair_injective` ✓.
    Verdict: SURVIVED.
- **L4.6** `quotient_row_exact` (Lemma 4.4, gluing form):
  - Source: p. 14 Lemma 4.4 (verbatim in docstring). Our statement is the middle-exactness
    workhorse (`ψ y ∈ H₂ → y ∈ φ(G₀) + H₁`), the form consumed by Prop 4.5; the norm
    bookkeeping of the source's left-arrow bound is absorbed into L4.7/L4.8's topological
    conclusions (openness of group-quotient maps replaces explicit η-chases — planner
    decision, recorded; the source's constants remain available via L4.3/L4.1 if the
    quantitative form is ever needed).
  - Attacks: (1) needs `I₁ ↠ I₂` from the TOP row — hypothesis `hHsurj` present (referee
    pass 2 flagged this as the load-bearing input ✓). (2) algebraic 3×3 chase — standard.
    Verdict: SURVIVED.
- **L4.7** cluster (`locJB/locIotaC/locRhoB/locRhoC` + `_mk` lemmas +
  `loc_square_commutes`, `loc_row_exact`, `loc_pair_injective`, `locRhoC_surjective`):
  - Source: pp. 14–15 Prop 4.5 (verbatim in docstring) + (4.21) "the completed graph
    quotient is already the Banach quotient `E_α = P_E/I_E`."
  - Discharge: `Ideal.Quotient.lift` along `ext*` (ideals map into ideals ✓ by construction
    of `rB/rC/rD`); exactness by diagram chase from L4.3 + L4.6 + L4.1.
  - Attacks: (1) **B2 echo #6/P3**: the quotient here is of the *restricted* ring `P_E`,
    never of `MvPolynomial` — the completed localization is only identified with it because
    the ideal is CLOSED (L4.5/L3.7); the false algebraic-localization shortcut is
    structurally excluded ✓. (2) middle-exactness needs the ideal row's surjectivity — L4.3
    ✓. (3) inf-max isometry (referee pass 2, item 5.2) — needed only for the normed reading;
    topological form avoids it. Verdict: SURVIVED.
- **L4.8** cluster (`loc_pair_isEmbedding`, `locRhoC_isOpenMap`, `locA_t2`,
  `locA_completeSpace`):
  - Source: Prop 4.5's strictness + (4.21).
  - Discharge: quotient maps of topological groups are open (mathlib); embedding via
    L4.6-style chase + closedness (L4.5) ⟹ Hausdorff ⟹ complete (closed image of Banach
    quotient; `QuotientAddGroup` normed-quotient instances).
  - Attacks: (1) `T2` requires closed ideal — supplied; (2) completeness of normed-group
    quotient by closed subgroup — mathlib `Quotient` completeness ✓. Verdict: SURVIVED.

### M5 — functoriality, bridges, loc-lift (`FiniteJetFunctoriality.lean`)

- **L5.1** pods (`podA/B/C/D`): concrete `PairOfDefinition`s on unit balls with the
  `t`-ideal. Source: p. 6 (2.1a) "choose the bounded rings of definition …". Discharge:
  `podD`-pattern (`ExampleUnitDisc.lean:448`), `isAdic` by the same metric argument.
  Attacks: (1) **B2 echo L14_L2** — completeness of the ball needs ambient completeness ✓
  M1 instances; (2) `Ideal.span {t}` f.g. ✓ trivial. SURVIVED.
- **L5.2** `pushDatumB/C/D` + `IsRational` transfer:
  - Source: p. 18 Lemma 5.1 (verbatim): "its inverse image `U_E = p_E⁻¹(U)` is the rational
    domain in `Y_E` defined by the image of the same datum."
  - Discharge: image datum; `hopen` via the generic span-⊤/principal-pod computation
    (planner-verified: `b ∈ (t^N)` ⟹ `b/s = ∑ (t^N aᵢ b')(tᵢ/s)` with `t^N aᵢ ∈ A₀` for
    `N` large — the finitely many `aᵢ` from `1 = ∑ aᵢtᵢ` are absorbed by topological
    nilpotence). `IsRational` via `RationalLocData.isRational_of_span_eq_top` + L4.2.
  - Attacks: (1) risk item 3 (plan.md): if the generic `hopen` lemma resists, per-vertex
    concrete proofs are possible (norm estimates); recorded fallback. (2) `Finset.image`
    needs `DecidableEq` — `Classical` opened ✓. SURVIVED.
- **L5.3** `presheafValueMap*` + continuity + `canonicalMap` compatibility + restriction
  naturality (`presheafValueMap*_restriction`):
  - Source: p. 15–16 Lemma 4.6 (verbatim): "The isomorphism (4.20) is canonical and natural
    in the strict Milnor square and in the rational datum. In particular, for rational
    domains `V ⊆ U`, the kernel descriptions commute with the restriction map
    `𝒪(U) → 𝒪(V)`." (Iteration clause NOT formalised — not needed for Thm 5.3; scope note.)
  - Discharge: `IsLocalization.Away.map` + `locTopology` lattice comparison (images of
    `locSubring` generators are generators) + `UniformSpace.Completion.extensionHom`;
    naturality by `IsLocalization.ringHom_ext` + completion-extension uniqueness on the
    dense localization (planner note: density of the *localization* in the completion is
    automatic; density of `A` in the localization is NOT claimed — B2-adjacent trap
    avoided).
  - Attacks: (1) continuity of the localization map for `locTopology` — the lattice
    inclusion is concrete for our pods; (2) uniqueness arguments need `T2` targets ✓
    completions are T0+group ⟹ T2 ✓. SURVIVED.
- **L5.4** `DatumEnum` + `graphBridgeA` + continuity both ways:
  - Source: p. 3–4 Lemma 1.1 (verbatim): "The separated completion
    `(E⟨T₁,…,T_m⟩/(gT_i−f_i)_{i=1}^m)^∧` represents bounded k-algebra homomorphisms
    `φ : E → F` … for which `φ(g)` is invertible and every `φ(f_i)/φ(g)` is power-bounded.
    It is therefore canonically the underlying Tate algebra of Huber's rational localization
    `E_α`. In particular, it is independent of the presentation of the rational subset and
    is transitive under rational refinement." Plus (4.21) closedness (`I_𝓐` closed, L4.5,
    so the quotient is already complete).
  - Lean ↔ source: `presheafValue D` = Huber's completed localization in the project's
    model (`Completion (Localization.Away s)` with `locTopology`); `locA` = the graph
    quotient; the bridge is Lemma 1.1's canonicity. Forward direction: `s` is invertible in
    `locA` (from `span T = ⊤`: `1 = ∑aᵢtᵢ ⟹ 1 = s·∑aᵢT̄ᵢ` — the (4.3) computation);
    `Localization.Away`-lift; continuity (lattice); completion-extend (target complete by
    L4.8). Reverse: evaluation `P_𝓐 → presheafValue D` at `Tᵢ ↦ canonicalMap tᵢ ·
    (canonicalMap s)⁻¹` — the needed `IsUnit (canonicalMap s)` is the **D′ = D case**, which
    holds because `s` is already invertible in `Localization.Away s` (no loc-lift class
    needed — circularity break, recorded); kills `I_𝓐` (graph relations ↦ 0); factors
    through the quotient; round-trips agree on dense images.
  - Attacks: (1) **the M5 keystone risk (plan.md item 4)**: the density and continuity
    arguments were re-derived by the planner in the project's exact vocabulary — the
    referee-verified Lemma 1.1 convergence argument ((1.3), §0 pass 3) is the mathematical
    core; the `TopologyComparison.lean` singleton-T bridge is the in-project precedent
    (generalising it is the ticket's job, with its hypothesis bundle replaced by our
    concrete closedness). (2) presentation-independence is NOT baked into `graphBridgeA`
    (it takes an explicit `DatumEnum`); consumers fix one enumeration per datum — no
    hidden canonicity claim ✓. (3) `graphBridge_natural_C` placeholder statement (True) is a
    **skeleton stub**: the real statement (bridge intertwines `presheafValueMapC` with the
    coefficientwise `locIotaC`) is fixed in ticket T-M5-4 — flagged, not hidden. SURVIVED
    with explicit stub-flag.
- **L5.5** `HasLocLiftPowerBounded (JetB/C/D)`: via `hasLocLiftPowerBounded_faithful`
  (vertices noetherian ✓; bundle available ✓). Attacks: instance-shape (the letI binder) —
  same as L2.5 ✓. SURVIVED.
- **L5.6** `hasLocLiftPowerBounded_JetA`:
  - Source: [FJP] has no such statement (it is a project-vocabulary obligation — the class
    gates `restrictionMap`); mathematically it is Lemma 1.1's universal-property data for 𝓐,
    obtained componentwise: p. 13 (4.9)-pullback + p. 4 Lemma 1.1's "power-bounded"
    condition, componentwise in the max norm.
  - Discharge: through `graphBridgeA` + `loc_row_exact`: a unit in both vertex-charts with
    matching inverses is a unit in the pullback (`(b⁻¹, c⁻¹)` matches in 𝓓 by uniqueness of
    inverses); power-boundedness in the max norm is componentwise; vertices supply their
    fields via L5.5.
  - Attacks: (1) circularity — resolved by the D′=D observation (L5.4); dependency order
    checked: bridges (L5.4) need no loc-lift; L5.6 consumes bridges; `restrictionMap`-based
    statements come after ✓ (file order enforces). (2) the `D ⊆ D'` inclusion-induced maps
    exist at graph level via Lemma 1.1's universal property — the ticket routes through
    graph quotients only. SURVIVED.
- **L5.7** coverage (`mem_rationalOpen_pushDatum*_iff`, `pushCovering*`, `*_isRational`):
  - Source: p. 19 (verbatim): "Inverse images preserve the defining valuation inequalities
    and unions. Hence, for `E = B, C, D`, `U_E = ⋃ᵢ (Uᵢ)_E` is a rational covering of the
    inverse-image domain."
  - Discharge: pointwise valuation comparison via `ValuationSpectrum.comap` +
    `comap_mem_spa` (project, sorry-free); coverage from `C.hcover` composed with comap.
  - Attacks: (1) `comap` needs `Continuous ι` + `A⁺ ≤ comap E⁺` — our maps are bounded
    norm-≤1 homs; power-bounded preservation is the norm argument (B2 `IsPowerBounded.map`
    trap avoided again) ✓. (2) empty pieces allowed (zero ring convention, [FJP] p. 3) —
    `RationalCovering` fields don't require nonemptiness ✓. SURVIVED.
- **L5.8** `interDatum` + `rationalOpen_interDatum` + `IsRational`:
  - Source: p. 19 "Put `U_{ij} = U_i ∩ U_j`, which is again rational."
  - Discharge: the standard product-datum computation (pointwise, both inclusions; uses
    `v(s₁s₂) ≠ 0 ↔ v(s₁) ≠ 0 ∧ v(s₂) ≠ 0` and the `T·`-product comparisons; span-⊤ of the
    product set from span-⊤ of the factors).
  - Attacks: (1) the classical pitfall — the product formula needs `sᵢ ∈ Tᵢ` or span-⊤
    normalisation; our data are span-⊤ (`IsRational` hypotheses threaded) and the planner
    verified the two inclusions pointwise under them; if a corner case resists, normalise
    data by `insert s T` first (recorded fallback — same rationalOpen). SURVIVED.

### M6 — transfer (`FiniteJetSheafTransfer.lean`)

- **L6.1** `productRestrictionSub_injective_JetA`:
  - Source: p. 19–20 (the injectivity part of the embedding chain: `J ∘ r_R` injective).
  - Discharge: chase — `x` with all restrictions 0 has all chart-images 0 (naturality L5.3),
    vertex separatedness (`IsSheafy.separationSub`, L2.5) gives vanishing of the pushed
    global sections, and the base Milnor row (bridge + `loc_pair_injective` at the base
    datum) forces `x = 0`.
  - Attacks: (1) needs the BASE datum's row too, not just pieces — statement quantifies over
    all coverings of any rational base; base bridge available for any datum ✓. SURVIVED.
- **L6.2** `gluing_JetA`:
  - Source: p. 19–20 Lemma 5.2 proof (verbatim key steps): "Compatibility gives
    `x_i|_{U_{ij}} = x_j|_{U_{ij}}` … For the images `b_i ∈ B_{U_i}` and `c_i ∈ C_{U_i}`
    this gives `b_i|_{(U_{ij})_B} = b_j|_{(U_{ij})_B}` … sheafiness of B and C glues them
    uniquely to `b ∈ B_U` and `c ∈ C_U`. The two images of `(b,c)` in `D_U` agree after
    restriction to every `D_{U_i}`, because each `x_i` belongs to the local fiber product.
    The restriction `D_U → ∏_i D_{U_i}` is injective by separatedness for `D` … Exactness of
    (5.7) gives a unique `x ∈ R_U` mapping to `(b, c)`. For each `i`, the elements `x|_{U_i}`
    and `x_i` have the same images under the injective map `j_{U_i}`, and hence are equal."
  - Discharge: the ten-step chain, each step a named prior leaf: push family (L5.3), pairwise
    compat on `interDatum` (L5.8 + hypothesis instantiated at `D₃ := interDatum`), vertex
    compat quantified over arbitrary `D₃` in the vertex (obtained by restricting through the
    pushed intersection — transitivity of `restrictionMap` = project `restrictionMap_comp`),
    glue (L2.5), 𝓓-match (L2.5 separation + L5.3), pull back (L5.4 bridge + L4.7
    `loc_row_exact`), identify restrictions (L4.7 `loc_pair_injective` + naturality).
  - Attacks: (1) **the planner's hardest transfer attack** — the project's gluing
    compatibility quantifies over ALL rational `D₃` inside two pieces of the *vertex*, not
    only pushed ones; resolution (recorded in the ticket): for vertex-side `D₃` inside
    `(Uᵢ)_E ∩ (Uⱼ)_E = (U_{ij})_E` (L5.8 pushed-intersection identity), restrict the pushed
    sections first to `(U_{ij})_E` (equal there by pushed 𝓐-compatibility at `U_{ij}`), then
    to `D₃` by `restrictionMap_comp` — so FULL vertex-compatibility follows from
    𝓐-compatibility at intersections. Verified step-by-step by the planner; this is the
    place a lazy formalisation would stall, hence spelled out. (2) uniqueness of the glued
    `b, c` not needed (only existence + the matching). (3) zero-ring pieces — all steps are
    vacuous there ✓. SURVIVED.
- **L6.3** `productRestrictionSub_isEmbedding_JetA`:
  - Source: p. 19 (5.8)-cancellation + p. 21 Thm 5.3 "the Banach open mapping theorem makes
    the continuous bijection onto that image a homeomorphism"; p. 20 "That subring is closed
    in the finite product."
  - Discharge: mirror of the 828b assembly (WCA:13388): range ⊆ `sectionEqualizer` (project
    generic, sorry-free), equality of range and equalizer from L6.2 + L6.1, closedness
    (`sectionEqualizer_isClosed`, project, sorry-free), then
    `isInducing_of_closedRange_of_topNilpUnit` (project σ-compact-free Tate OMT, sorry-free)
    + injectivity L6.1.
  - Attacks: (1) the project OMT lemma's hypothesis shape (Tate unit) — 𝓐 is Tate ✓ M1.
    (2) `presheafValue`s complete/first-countable — project instances ✓. SURVIVED.
- **L6.4** assembly `isSheafy_JetA` — **already term-level in the skeleton** (no sorry):
  `{ embedding := L6.3, gluing := L6.2 }`. Type-checked ✓.

### Composition attacks (internal nodes, R1)

- Could M1–M5 all hold and M6 fail? The transfer chain was re-derived twice (planner +
  referee pass 3 item 10) with every silently-used property enumerated (12 items, all
  present as leaves or project lemmas — list in §0 pass 3). The single non-source-explicit
  step (vertex-side arbitrary `D₃`) is L6.2 attack 1, resolved.
- Could the skeleton's statements drift from [FJP]? Every leaf carries its quote; the two
  deliberate deviations are RECORDED: (i) evalHom-surjectivity replaces the kernel-exact
  presentation (noetherianity only needs surjections); (ii) Lemma 4.4/Prop 4.5 stated
  topologically instead of with explicit quotient-norm constants (the constants exist at
  P-level; the transfer consumes only the topological form). Neither weakens the headline.
- m = 0 datum edge (empty T): excluded by `m ≥ 1` convention ([FJP] p. 3 "an empty tuple may
  be padded by `f₁ = 0`"); our `DatumEnum` allows padding the enumeration; recorded in
  ticket T-M5-4.

## Result R2: `finiteJet_isUniform` + `finiteJet_isDomain` ([FJP] Prop 2.3)

Leaves: `norm_L_mul`, `norm_JetC_mul` (L1.3), `IsDomain (JetC F)`, `IsDomain (JetA F)`,
`isPowerBounded_JetA_iff`, `isUniform_JetA` (`FiniteJetUniformDomain.lean`).
- Source (verbatim, p. 7): "If `v_{𝒞₀}(a) < 0`, then `v_{𝒞₀}(aⁿ) = n v_{𝒞₀}(a)` tends to
  `−∞`, so `a` is not power-bounded. If `v_{𝒞₀}(a) ≥ 0`, all powers of `a` lie in 𝒜₀. Thus
  the valuation formulation gives directly `𝒜° = 𝒜₀`." "Finally, 𝒜 is a domain because it
  is a subring of 𝒞."
- Lean ↔ source: `IsPowerBounded a ↔ ‖a‖ ≤ 1` (the norm is the restriction of 𝒞's
  multiplicative norm — definitional in the subring model); `IsUniform` = project class
  (`Uniform.lean:43`, `IsBounded (powerBoundedSubring A)`); ball bounded in a normed ring ✓.
- Attacks: referee pass 3 item 4 (the "restriction still power-multiplicative" trap —
  defeated: powers computed in 𝒞 ✓); `IsBounded` is the project's Huber-boundedness — for
  the metric ball, absorption by `t^n`-scaling (same as disc `isBounded_OD`) ✓. SURVIVED.

## Result R3: `finiteJet_not_noetherian` ([FJP] Prop 2.4)

Leaves: `winv_not_integral`, `not_moduleFinite_L`, `moduleFinite_of_ker_jB_fg`,
`ker_jB_not_fg`, `not_isNoetherianRing_JetA` (`FiniteJetUniformDomain.lean`).
- Source (verbatim, pp. 7–8): "Let `J = Q²𝒞 ⊂ 𝒜` … `K = ker(𝒜 → R_W) = QR_W + Q²𝒞` …
  `KJ = Q³𝒞, J/KJ = Q²𝒞/Q³𝒞 ≅ 𝒞/Q𝒞 = L` … If `J` were generated as an 𝒜-ideal by
  `x₁,…,x_r`, their classes would generate `J/KJ` over `𝒜/K` … It would follow that `L` is a
  finite `R_W`-module. A module-finite algebra is integral, so `W⁻¹` would satisfy a monic
  equation … Multiplication by `Wⁿ` gives `1 + a_{n−1}(W)W + ⋯ + a₀(W)Wⁿ = 0`. The inclusion
  `R_W ↪ L` is injective, so evaluation at `W = 0` would give `1 = 0`."
- Lean ↔ source: `J = ker(jB)` (the 2-jet kernel = `Q²𝒞` — support form); the `𝒜/K ≅ R_W`
  module structure enters through `Algebra (K⟨W⟩) L` via `ofRestricted`; the evaluation at
  `W = 0` is `PowerSeries.constantCoeff` on `K⟨W⟩` (never on `L` — referee-checked).
- Attacks: pass 3 item 5 (all five sub-attacks defeated — `Q ∈ 𝒜` support (0,1); `KJ = Q³𝒞`
  both inclusions; the decomposition of zero-jet elements). `Module.Finite → IsIntegral`:
  mathlib `Algebra.IsIntegral.of_finite` ✓. B2-log: no name/shape match. SURVIVED.

## Result R4: `finiteJet_not_stablyUniform` ([FJP] Prop 3.1 + Cor 3.2)

Leaves: `Wa`, `chartDatum`, `chartDatum_isRational`, `chartEquiv` (+2 continuity),
`isUniform_of_ringEquiv`, `not_isUniform_chart`, `not_isStablyUniform_JetA`
(`FiniteJetChart.lean`); `isPowerBounded_JetB_iff`, `not_isUniform_JetB`
(`FiniteJetUniformDomain.lean`).
- Source (verbatim, p. 8, Prop 3.1 proof): "For any `y ∈ Q²𝒞 ⊂ 𝒜` and `n ≥ 0`, one has
  `W⁻ⁿy ∈ Q²𝒞 ⊂ 𝒜` and `‖W⁻ⁿy‖ = ‖y‖`. In G, `y = Wⁿ(W⁻ⁿy) = ϖⁿXⁿ(W⁻ⁿy)`,
  `‖y‖_G ≤ |ϖ|ⁿ‖y‖`. Letting `n → ∞` shows directly that the image of the entire closed
  subspace `Q²𝒞` is zero in the separated completion." Then the two-map argument (ψ, φ,
  dense agreement). Cor 3.2 (verbatim, p. 9): "It is not uniform: `Q ≠ 0`, `Q² = 0`, and
  every element of the unbounded line `kQ` is power-bounded, while `‖λQ‖ = |λ|` … Thus a
  rational localization of the uniform ring 𝒜 is nonuniform."
- Lean ↔ source: the chart target `k⟨X,Q⟩/(Q²)` **is** `JetB F` (planner observation —
  double reuse); `chartEquiv` is Prop 3.1 stated against `presheafValue chartDatum`;
  the identity `y − ϖⁿXⁿ(W⁻ⁿy) = (Wⁿ − (ϖX)ⁿ)(W⁻ⁿy) ∈ (ϖX − W)` (referee-supplied
  factorisation) drives the collapse; `IsStablyUniform` negated at `chartDatum`
  (the project class quantifies over ALL `RationalLocData`, so one witness suffices).
- Attacks: pass 3 items 6–7 (all defeated, including the `{1, λQ, 0, 0, …}` full power-set
  check and `T ≠ 0`); `isUniform_of_ringEquiv` transport — power-bounded and bounded are
  topological-ring invariants under bi-continuous ring isos (planner-verified; no bare
  `IsPowerBounded.map` use — B2 respected: both directions of the iso are continuous ring
  homs and boundedness transports through open images). SURVIVED.

## Prior-B2 consultation (Step 4.6)

`b2_log.jsonl` (79 entries) was read in full. Matches and how they are addressed:
- `IsPowerBounded.map` (FALSE generically) → all transfer statements use norm-≤ homs or
  bi-continuous isos (L1.7, L5.7, R4).
- `presheafValue_eq_quotient_AlangleX_iterated` / P3 (algebraic-localization confusion) →
  bridges only ever target the **restricted-ring** quotient with **closed** ideal (L5.4).
- `restrictionMapHom_injective` (FALSE) → never assumed; separation always routed through
  vertex `IsSheafy.separationSub` (L6.1).
- `aplus_le_pod` / CompatiblePlusSubring (unsatisfiable for nondiscrete Tate) → not used;
  828b bundle avoids it (L2.5).
- `isStronglyNoetherian_of_isNoetherianRing_isTateRing` (FALSE) and
  `_aux_noeth_A0_generic_…` (FALSE) → per-arity surjections and concrete unit-ball proofs
  (L2.1–L2.4).
- `principalPair_A0_completeSpace` (needs ambient completeness) → M1 completeness instances
  precede pods (L5.1).
- No name or shape matches against any new leaf (checked by grep over the new decl names).

## Provability check summary (Step 4)

Every leaf is (i) discharged from mathlib (verified names: `AdicCompletion.flat_of_isNoetherian`,
`Submodule.eq_top_of_localization_maximal`, `ContinuousLinearMap.exists_preimage_norm_le`,
`SubringClass.toNormedCommRing`, `AddMonoidAlgebra` domain instances, `Polynomial.aeval`,
`isNoetherianRing_of_surjective`, quotient-group norm instances), (ii) discharged from
project code (verified: `isSheafy_of_stronglyNoetherian_828b` [axiom-clean],
`sectionEqualizer_isClosed`, `isInducing_of_closedRange_of_topNilpUnit`,
`IsSheafy.separationSub`, `restrictionMap_comp`, `spaComap`/`comap_mem_spa`,
`hasLocLiftPowerBounded_faithful`, the vendored Coram/Xia stack, `ExampleUnitDisc` engines
`exists_flatten'`/`restrictedGaussEquiv`, `IsTateRing.quotient`, `NoetherianTateModules`,
`IdealClosedness`), or (iii) an intra-campaign leaf listed above with its own discharge plan.
**No REVIEW-PENDING leaves. No unresolved API gaps**: the three survey gaps (ℤ-indexed
Laurent ring; quotient norms; fiber product) are closed by DD2/DD3/DD4 designs whose leaves
are all in category (i)/(iii).

## Confidence gate (Step 5) — assessment

1. Every leaf discharged or planned (above) ✓  2. Skeleton compiles, sorries only
(3084 jobs) ✓  3. Verbatim quotes per leaf-cluster ✓ (this file)  4. Adversarial pass run
(three passes + per-leaf attack logs) ✓  5. B2 log consulted, matches addressed ✓
6. Tree mirrors [FJP]'s own lemma structure (Lemma-for-lemma; two recorded deviations with
justification) ✓  7. Single-conclusion statements throughout (Thm 1.3 split into five;
Prop 2.1 into its four claims; (5.2) into per-ring lemmas) ✓

**Feasibility**: feasible. The genuinely new mathematics is concentrated in three places —
the ℤ-indexed restricted ring (L1.1–L1.4, vendored-stack-shaped), the degree-≤2 graph–Koszul
package (L3.2–L3.9, elementary commutative algebra + existing noetherian-module machinery),
and the bridge/transfer glue (L5.4, L6.2) whose every step was hand-verified. The
highest-risk single leaf is the graph bridge L5.4 (isolated in M5; two in-project precedents;
does not block the R2/R3 track). Stretch M7 (strong sheafiness) is deferred to a follow-up
board section and blocked on M6.
