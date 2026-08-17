# Decomposition: AP-E4a → `weilPairingEval_self` via the universal family

2026-08-10. Strategy validated by ChatGPT 5.6-sol (max effort) — see the consultation
summary in `tickets.md`'s E4a section. Skeleton: `WeilPairing/SelfUniversal.lean`
(compiles, 7 sorries). Target: `Basic.lean:372` `weilPairingEval_self` (e_N(x,x) = 1,
arbitrary base, no invertibility).

## Why not the direct routes (adversarial record)

- **Identity-juggling is provably insufficient**: every combination of bilinearity
  (E2/E3 ✓), level compatibility (E6 ✓), μ_N-landing (✓), and covers reconverges to an
  irreducible symmetry leaf (session log: the N²-trick gives e_N(x,x) = e_{N²}(y,y)^N —
  level always outruns the exponent; ChatGPT concurs: "A nondegenerate bilinear pairing
  need not be alternating. The missing input is the skew self-duality of the principal
  polarization.")
- **The naive relative telescope collapses**: relativising Silverman III.8.1(b) at the
  cocycle level loses the divisor-level cancellation and provably degenerates to the
  known e^N = 1 (session log). The divisor-level version routes through
  `RelEffCartierDiv` — the owner-frozen B2 zone. Rejected.
- **Oda §1 is genuinely relative** (Thm 1.1 duality for isogeny kernels over a
  prescheme, Cor 1.3 biduality sign, Lemma 1.4 theta-commutator comparison; pp. 66–77)
  but that route is the full Cartier-duality/biextension machinery — E5-scale. Deferred
  to E5, where it is needed anyway.

## The chosen route (KM's own practice: reduce to the universal case)

**R**: `weilPairingEval_self`. Sources: KM 2.8.3 with footnote (print p. 90): "In fact,
e_N(P,P) = 1, cf. Notes Added in Proof"; the classical alternation Silverman AEC
III.8.1(b) (print p. 94–95), proof read in full:

> "(b) From (a) we have e_m(S+T,S+T) = e_m(S,S)e_m(S,T)e_m(T,S)e_m(T,T), so it suffices
> to show that e_m(T,T) = 1 for all T ∈ E[m]. [...] div(∏_{i=0}^{m−1} f∘τ_{[i]T}) =
> m Σ (([1−i]T) − ([−i]T)) = 0. It follows that ∏ f∘τ_{[i]T} is constant, and if we
> choose some T' ∈ E satisfying [m]T' = T, then ∏ g∘τ_{[i]T'} is also constant, because
> its m-th power is the above product of f's. Therefore [...] Canceling like terms from
> each side gives g(X) = g(X + [m]T') = g(X+T), and hence e_m(T,T) = g(X+T)/g(X) = 1."

(Section hypothesis, print p. 92: "we fix an integer m ≥ 2, which we assume to be prime
to p = char(K) if p > 0" — hence the field leaf carries `(N : K) ≠ 0`, matching
HasseWeil's formalisation.)

The field-level alternation is already formalised: `HasseWeil.weilPairing_self`
(`HasseWeil/WeilPairing/PairingProps.lean:254`, section `Alternating` with
`variable [IsAlgClosed F]`), for the pairing DEFINED by the translation
characterisation `weilPairing_spec` (`Pairing.lean:227`):
`τ_S g_T = algebraMap F KE (e_ℓ(S,T)) * g_T`.

The relative statement follows from the field-level one by KM's standard
reduce-to-the-universal-family argument, which is sound here because the universal
N-torsion base is **affine, ℤ-flat, with reduced N-inverted locus** (ChatGPT-sharpened
formulation: work with `B ↪ B[1/N]`, no density/components needed).

## Tree

- **U1** `weilPairingEval_mapIso` (skeleton `SelfUniversal.lean`): pairing invariance
  under pointed isos `φ : E.asOver ≅ F.asOver` `[IsMonHom φ.hom]` over the same base.
  - Route: the φ-sibling of `torsionSplittingEval_mulByN_pullback` (E6-d) — the
    `localPullback` gadgets are f-generic (`transitionUnitOfCover_localPullback` at
    `f := φ.hom.left`), so only `kappa_mapIso` (mirror of `kappa_restrictBase`), the
    hnorm-transport (pointed zero-compat), and the pin remain. Kill-transport via
    `mulByHom_comp_left_of_isMonHom` (✓ exists, MulByHomFibres.lean:100).
  - Attacks: (1) hypothesis test — `[IsMonHom φ.hom]` is necessary (a non-pointed iso
    shifts the zero section and the normalisation; e.g. translation-conjugates change
    datasets); `[IsLocallyNoetherian S]` inherited from the isMonHom machinery — check
    at execution whether droppable. (2) composition — value in Γ(T,⊤) is unchanged
    because the base T is untouched; only E-side data transports. (3) discharge — all
    named gadgets verified to exist and be f-generic this session. SURVIVED.
- **U2** classification plumbing: `localModel` (`Basic.lean:204` `LocallyWeierstrass`,
  read verbatim: ∀ s, ∃ affine U ∋ s, W over Γ(S,U), pointed iso
  `pullback π U.ι ≅ projModel W` with π- and zero-compat) + `classifyRingHomU` and
  `universalWeierstrassLocU_map_classifyRingHomU` (✓ exist, AdditionSpecPoints) + the
  model-base-change pointed iso `modelEllipticCurve (W.map c) ≅ pullback of
  modelEllipticCurve 𝕌` (generalise `modelBaseChangeIsoAsOver` from field bases to ring
  maps, or build from the Addition* base-change machinery).
  - Attacks: (1) different local choices need not agree — harmless, the CLAIM is
    intrinsic and transported by U1 (ChatGPT Q4 confirmed). (2) the base of the local
    piece is Spec Γ(S,U) not U — the isoSpec-bridge (`isoSpec_appLE_bridge` genre)
    handles it. SURVIVED with the note that U2 is pure plumbing, no mathematics.
- **U3** gluing: value equality is Zariski-local on T (sections of O^× form a sheaf;
  restriction along the cover is `weilPairingEval_restrict` ✓ PROVED).
- **U4** universal vanishing (skeleton: `weilPairingEval_self_universal`, conditional
  on U5): over `X_N := (modelEllipticCurve 𝕌).torsion N = Spec B`:
  - U4a: X_N affine — torsionπ over the atlas is finite (IsProper via `mulByHom_π` +
    lqf ✓ `mulByHom_locallyQuasiFinite_global` + `IsFinite.of_isProper_of_locallyQuasiFinite`,
    all verified this session) ⟹ IsAffineHom over the affine Spec(atlas ring).
  - U4b: B ℤ-flat — torsionπ flat (pullback of `mulByHom_flat` ✓) over the atlas ring
    = localised polynomial ring over ℤ (flat ✓); composite flat ⟹ torsion-free.
  - U4c: `B ↪ B[1/N]` — N regular on B from ℤ-torsion-freeness.
  - U4d: B[1/N] reduced — chain `B[1/N] ↪ B ⊗ ℚ ↪ B ⊗_R Frac(R_ℚ) =: B_K`
    (flat/torsion-free steps over domains), and `B_K` = sections of the N-torsion of
    the generic-fibre curve, finite étale over the field K (`torsionπ_etale` ✓
    TorsionFibre:704, N invertible in K) ⟹ reduced (étale algebra over a field is a
    finite product of separable extensions; mathlib discharge to be pinned at
    execution — candidates: unramified+finite over a field ⟹ reduced via Ω = 0, or
    the smooth-scheme regularity route; the STATEMENT is unimpeachable).
  - U4e: pointwise vanishing at every p ∈ Spec B[1/N] — `weilPairingEval_restrict`
    (✓ PROVED) along `Spec κ(p) → X_N` + U5 at (κ(p), fibre record, restricted
    tautological point); `(N : κ(p)) ≠ 0` since N invertible in B[1/N].
  - U4f: reduced + vanishing at every residue field ⟹ zero (nilradical = ⋂ primes,
    elementary).
  - Attacks: (1) N = 1 edge — the whole route works uniformly (also free via
    e^N = 1). (2) non-reduced B would break U4f — that is exactly why U4d is load-
    bearing; its proof does NOT use any reducedness of special fibres (E[p] in char p
    is non-reduced — only the N-INVERTED locus is claimed reduced). (3) the tautological
    point's kill condition is `pullback.condition` verbatim — no content. SURVIVED.
- **U5** the field leaf (skeleton: `weilPairingEval_self_of_field` — API GAP, own
  sub-development to be planned by a dedicated `/develop` pass before execution):
  alternation of OUR `weilPairingEval` over a field K, `(N : K) ≠ 0`.
  - Route (ChatGPT-recommended "narrow comparison"): descend to K̄ (Γ-injectivity of
    K → K̄); over K̄ instantiate the KM dataset through the classical Weil function
    `g_Q` and match translation characterisations — the KM side ALREADY HAS its
    characterisation proved (`eq_mul_globalTwist_of_translate`, Translation.lean:266:
    `τ^# h_i = h_i · π^# C` with C = the glued h(P)-value); the HasseWeil side IS
    DEFINED by its characterisation (`weilPairing_spec`); uniqueness of the scalar
    against the same function-object gives the comparison; import
    `HasseWeil.weilPairing_self` (✓ PROVED, [IsAlgClosed]). Fallback: the direct
    telescope over K̄ in the backend (Silverman III.8.1(b), quoted above).
  - The comparison is the T-C4 normalisation-pinning the project independently owes
    (register docstring, Basic.lean:22-27) — double value.
- **Assembly** `weilPairingEval_self'` (skeleton): U3 ∘ (U2 + U1) ∘ U4 ∘ U5. Fills
  `Basic.lean:372` once the import-order is resolved at landing time (the assembly
  lives downstream of Basic; final wiring = either move the register statement or a
  coordinator restructure — recorded, not a blocker).

## Prior-B2 consultation

`b2_log.jsonl` (2 entries, both 2026-08-09): `evalGenerator_mem_nonZeroDivisors`,
`relEffCartierDiv_of_degreeOne_package` — no name or shape overlap with any leaf above.
The rejected divisor-level telescope WOULD have routed near that zone — one more reason
for the chosen route.

## Confidence gate

Every leaf is (a) discharged against verified in-tree decls (named above with
file:line, all checked this session), (b) elementary verified commutative algebra
(U4b/c/f), (c) mathlib-discharge-with-candidates flagged for execution-time pinning
(U4d étale-over-field ⟹ reduced), or (d) an explicit API GAP with its own planned
sub-development (U5, plus the U1 kappa_mapIso block and the U2 model-base-change
generalisation as templated NAT2/E6-d-mirror work). Skeleton compiles (0 errors,
7 sorries). REVIEW-PENDING: none.

## U5 sub-decomposition (2026-08-10, validated ChatGPT 5.6-sol max — consultation #3)

Scope: the comparison `e_KM = e_Sil` over a field and the alternation import, for the
MODEL curve `E := modelEllipticCurve W` over `Spec k` (record-generality deferred to the
U-assembly via U1/U2). Verdict highlights (ChatGPT had repo access and cited files):
- **Orientation PINNED**: `transitionUnitOfCover` = `e.inv ≫ g.hom` (InvertibleSheafCocycle
  :44, KMPatching:197) ⟹ F_ij = r_j/r_i ⟹ the comparison gives **equality** `e_KM = e_Sil`
  (with the literal `e_i∘e_j⁻¹` convention it would be the inverse; for the diagonal either
  suffices).
- Q1 confirmed: `[N] ∘ τ_P = [N]` (`translateByPoint_comp_mulByN`), so `τ_P^#` fixes
  `[N]^# K(E)` pointwise — formalised as `functionFieldMap_apply_functionFieldMap_of_comp_eq`
  (PROVED, DominantFunctionField.lean).
- Q2 clean form: with r_i := local equations of D = (Q)−(O) through φ : M ≅ O(D),
  `G_i := h_i·[N]^#r_i` glue to one `G` with div G = [N]^*D = div g_Q, so `G = a·g_Q`,
  `a ∈ k̄^×` scalar; hence `H := FF-class(h_{i₀}) = a·g_Q·[N]^#(r_{i₀}⁻¹)`. Alternative same
  content: `ĥ_i := g_Q/[N]^#r_i` is another splitting of the SAME pulled cocycle; `h_i/ĥ_i`
  glue to the scalar. Warnings: comparing arbitrary rational trivialisations gives only an
  arbitrary FF-element — the [N]^#-form comes from the cocycle calculation; if cocycles are
  merely cohomologous, absorb the coboundary into the r_i first.
- Q3: Γ(X,O)^× = k^× via geometric integrality; in-tree formal route
  `EllipticCurveGeom.universallyOConnected` + `UniversallyOConnected.isIso_app`. The scalar
  `a` needs no descent.
- Q5: do the WHOLE comparison over k̄, descend only the value (Γ-injectivity); IsAlgClosed +
  (N:k)≠0 are needed only for the Silverman endpoint.
- Q6 missing input (the genuine work): the divisor/line-bundle dictionary — κ(Q) ↔ O((Q)−(O))
  concretised, HW `weilFunction_divisor` (valuation divisor) ↔ Cartier data on projModel,
  [N]^#-FF vs HW pullback (the last IS brick6_intertwining, PROVED).

### Leaves
- **U5-L1** (the dictionary, hard): `∃ a v, H = a • (g_Q-image · [N]^#-FF v)` in
  `W.toAffine.FunctionField` — where H := FF-class of h_{i₀} (chart ∋ generic), g_Q :=
  `HasseWeil.weilFunction` (already lives in the same FunctionField). Split:
  - L1a: r_i-family from the sectionDivisor/idealModule data of κ(Q) with
    FF-transition-match (`transitionUnitOfCover`-image = r_j/r_i) and HW-divisor pinning
    (div r_i = (Q)−(O) on W_i as valuation divisors) — the scheme↔valuation layer (T-C4 debt).
  - L1b: div(G) = div(g_Q) ⟹ G/g_Q ∈ k̄^× (HW divisor-zero⟹constant over k̄ +
    pullbackDiv-vs-[N]^#-FF via brick6).
- **U5-L2** (τ-relation in FF): instantiate `eq_mul_globalTwist_of_translate` at
  τ := translateByPoint (the KMBilinear:380–430 boilerplate is the template), push the i₀-chart
  relation through germToFunctionField, conjugate by the PROVEN bridge
  `functionFieldMap_translateBy` ⟹ `translateAlgEquivOfPoint W P₀ H = c·H`, c :=
  algebraMap-image of `torsionSplittingEval … P'`. Needs the gluing
  translateByPoint-vs-translateByIso.left (two spellings of translation — check/lemma).
- **U5-L3** (scalar match): L1 + L2 + deck-invariance + `weilPairing_spec` + cancel g_Q ≠ 0 +
  k̄ → K(E) injectivity ⟹ c = e_Sil(P₀, Q₀).
- **U5-L4** (value plumbing): `weilPairingEval` at the model = C := torsionSplittingEval
  (via `weilPairingEval_eq_weilPairingKM` + `eq_torsionSplittingEval`), c = algebraMap C.
- **U5-L5** (diagonal): Q := P ⟹ e_KM(P,P) = e_Sil(P₀,P₀) = 1 (`weilPairing_self` /
  `fieldWeilPairing_self`).
- **U5-L6** (descent): base-change the k-data to k̄, `weilPairingEval_restrict` +
  Γ(Spec k) → Γ(Spec k̄) injective; then the record→model transport at a field (U1-consumer).

Execution order: L2 (all inputs proven, boilerplate) → L4 (plumbing) → L1a/L1b (the math) →
L3 → L5 → L6.

## U5-L1 design notes (2026-08-11, pre-execution)

Target (validated form): for the chosen B-side dataset over Spec k̄ and chart i₀ ∋ generic,
∃ (a : k̄ˣ) (v : K(E)ˣ), germ(h_{i₀}) = a • (g_Q-image · [N]^#-FF v) in W.toAffine.FunctionField
(after the L2g-conjugation, all objects live in W.toAffine.FunctionField).
- The [N]^#-FF here is `functionFieldMap (mulByN …)` conjugated to `mulByInt_pullbackAlgHom`
  via brick6_intertwining (PROVEN) — so v's image is `mulByInt_pullbackAlgHom`-applied,
  i.e. HW-language directly.
- g_Q-image := HasseWeil.weilFunction W ℓ hℓ T hT (already in W.toAffine.FunctionField).
- L1a (r_i-family): the dataset's (M, e_i) against O(D_Q): realise via ChatGPT-#4's
  ĥ_i := g_Q/[N]^#r_i alternative — BUILD the comparison splitting from g_Q and local
  equations r_i of the section-divisor ideal (sectionDivisor Q).ideal = ker-ideal, whose
  locallyPrincipal generators (sectionDivisor_isOfficial.locallyPrincipal) ARE the r_i on
  an affine refinement. Transition-match: F_ij = r_j/r_i needs the e_i-vs-r_i comparison —
  the toSkeleton-class-equality hM gives M ≅ idealModule(ker Q)⁻¹-form; the trivialisation
  comparison is where the work is. Alternative dodge per #4 warning: absorb the coboundary.
- L1b (div G = div g_Q ⟹ scalar): over k̄; HW-side `pairing_const_of_transport`-input
  machinery (the divisor-zero⟹constant extraction already used by weilPairing's def);
  needs div(germ h_i · [N]^#r_i-glued) computed = pullbackDiv-difference — via the
  valuation-reading of scheme-germs (the T-C4 layer: ord at closed points of the model vs
  HW valuations — check FibrePointDict/FieldPairingValue for existing readers).
- REUSE-FIRST checklist before writing L1: grep RelPicLocal.lean + PoincareBiextension.lean
  ("κ(Q) = β(1, −Q∘π)" dictionary + `eq_kappaCls` through the zero-section splitting +
  `kappa_ratio_algebra`) — the κ-vs-O(D)-dictionary may partially exist there.

### L1a reuse verdict (2026-08-11, inventory read)
`PoincareBiextension.lean` has THE dictionary: `normCls Q = sectionPicCls · zeroPicCls⁻¹`
([𝒪(D_Q)]·[𝒪(D_0)]⁻¹, the honest divisor classes), `kappaCls` (β-form),
`kappaCls_eq_normCls_mul` (κ = normCls · π^*-twist), `eq_kappaCls` (any 0^*-killed class
≡ normCls mod Im π^* IS κ). **Over Spec k the twist DIES (Pic of a field is trivial)** ⟹
κ(Q) = normCls Q on the nose ⟹ the dataset module M with hM is Pic-equal to
sectionPicCls·zeroPicCls⁻¹; the L1a trivialisation-comparison runs through the
sectionDivisor idealModule (r_i = its locallyPrincipal generators). Also available:
`exists_picMap_pi_sectionPicCls_add` (square, Pic-form) for the [N]^*-computation.
L1-entry: state over Spec k̄; first brick = "Pic (Spec (CommRingCat.of K)) trivial"
(mathlib: Pic of local ring / field — check `Pic`-triviality for Spec-of-field; likely
via projective-modules-over-field free ⟹ small lemma if absent).

### L1-Pic-brick analysis (2026-08-11)
Needed: `Subsingleton (Scheme.Pic (Spec (CommRingCat.of K)))`, K a field.
`Scheme.Pic X := (Skeleton X.Modules)ˣ` (Picard/Pic.lean:118). Cheapest route found:
Spec K is a ONE-POINT space ⟹ any trivialising cover of an `IsInvertible` module contains
⊤ ⟹ `M.over ⊤ ≅ unit` ⟹ `toSkeleton M = 1` directly (no affine-modules equivalence
needed). Gap to check at execution: the unit-class ⟹ IsInvertible direction ([PIC-P2-CMP]
registered comparison — invertible-to-unit is the constructed one; for our use the
arriving elements are Pic.map-images of classes built from IsInvertible reps, so track
representatives instead of quantifying over raw units if the comparison is missing).
Fallback: Γ-side via ForMathlib/PicSubsingletonFree (`Subsingleton (Pic K)` fires from
mathlib’s semilocal instance since a field has one maximal ideal).

L1-Pic-brick UNBLOCKED (2026-08-11 final scoping): `isInvertible_of_isUnit_toSkeleton`
EXISTS (KMDataset:154-region) — units give IsInvertible reps, so the one-point route runs:
u ↦ fromSkeleton-rep ↦ IsInvertible ↦ trivialising cover ↦ some W i = ⊤ (PrimeSpectrum of a
field is a subsingleton) ↦ M.over ⊤ ≅ unit ↦ toSkeleton = 1. Remaining sub-brick: the
over-⊤-iso ⟹ global-iso step (an `.over ⊤`-conservativity/equivalence lemma — check
RelPicLocal `overTrivialization`/`IsInvertible.of_restrict_cover` layer first).

Pic-brick final chain (all named, one converter to build): u ↦ fromSkeleton-rep ↦
`isInvertible_of_isUnit_toSkeleton` ↦ cover ∋ ⊤ (PrimeSpectrum-of-field subsingleton) ↦
pullback-iso along ⊤.ι (an ISO of schemes — mathlib topIso) ↦ [BUILD: pullback-along-iso
reflects/transports iso-to-unit ⟹ global `M ≅ unitObj`] ↦
`toSkeleton_eq_one_of_iso_unitObj` (LineVerticalAssembly:39 ✓) ↦ u = 1.

### L1a step-3 API finding (2026-08-11): the generator trivialisation IS `idealGenHom`
(Picard/IdealModule:240 — mult-by-f from unitObj to the restricted ideal module), shown
IsIso on principal affine charts inside `isInvertible_idealModule` (:406). So the r_i-side
trivialisations of I(Q)/I(0) come packaged with transitions r_j/r_i by construction; the
step-3 comparison composes the M ⊗ I(Q) ≅ I(0)-iso with idealGenHom-inverses on a common
principal refinement to produce an M-trivialisation whose transition-cocycle FF-image is
(r0/rQ)-ratios — the shape the L2e-germ side consumes. Statement next session; entry
point: a common-refinement lemma for two locallyPrincipal families + the restrictFunctor
vs .over-form conversion (restrictIsoOfPullbackIso / overTrivializationOfRestrictIso,
InvertibleSheaf:241/255).

Step-3 recon addendum: NO ready common-refinement lemma in the Picard layer — step-3a =
build it (two locallyPrincipal choices + a dataset cover ⟹ one indexed family of affine
opens, principal for both ideals and inside a dataset chart; elementary: intersect + the
affine-basis refinement, `Opens.mem_iSup`-glue). `localPullbackTrivializationT`
(LocalTrivialization:264) handles the .over-conversions. Steps: 3a refinement ⟹ 3b the
M-trivialisation (tensor-iso ∘ idealGenHom⁻¹-pair) ⟹ 3c its cocycle FF-image = r-ratios.

Step-3a inputs found: mathlib `IdealSheafData.map_ideal` (affine U ≤ V ⟹ ideal
restricts by map) + `Ideal.map_span` give span-restriction in 2 lines. The
nonZeroDivisors-transfer to the refined chart: either via localisation-injectivity on
basic opens, or dodge entirely — take PER-POINT choices from each isOfficial at the
refined point (the r_i are per-chart data; no global choice needs restricting). The
IsIso-machinery on basic opens is `bijective_idealGenHom_app` (IdealModule:309).

### 3c cut (2026-08-11, all entry points named)
Engine: `overTrivializationOfRestrictIso_hom_eq_comp_scalar` (PoleSheaf:3488) — two
restrict-isos differing by `unitEndomorphismOfTopSection r` have .over-forms differing by
the scalar-end of r ⟹ their `trivializationTransitionUnit` is r (spec
`overUnitScalarEnd_transitionUnit`, InvertibleSheafCocycle:52). Cut:
- 3c-i: two nzd generators of one principal ideal differ by a unit (comm-algebra:
  span-eq + nzd ⟹ f_i = u·f_j, u ∈ Γˣ; mathlib-adjacent).
- 3c-ii: `idealGenHom` at f_i = `idealGenHom` at f_j ∘ mult-by-u (from the mult-def).
- 3c-iii: push through the 3b-ii chains (each leg a named iso) + the scalar-transfer ⟹
  the M-transition on an overlap = (u₂/u₁)-ratio.
- 3c-iv: FF-germ of the transition (units of sections ↦ FFˣ, ratios ↦ divisions) — the
  L2e-consumer shape.
Then L1b (divisor-zero ⟹ scalar over k̄: HW `pairing_const_of_transport`-machinery) and
the L1-glue: run L2e at THE dataset built from these trivialisations (its h_i are then
g-related by construction).

3c-i DISCHARGED BY MATHLIB: `Ideal.span_singleton_eq_span_singleton` (span{x} = span{y} ↔
Associated x y, over a domain — the refined charts are domains via component_integral) +
`Associated`-destructuring gives the unit. No new lemma. 3c-ii..iv remain as cut.

3c-ii statement design (2026-08-11): `unitEndomorphismOfTopSection r`-app is mult-by-r
(@[simp] rfl, UnitPullback:42). Candidate: for f₁ = f₂·u (u ∈ Γ(X,V)ˣ from 3c-i),
`idealGenHom J V.1 f₁ hm₁ = (unit-endo of u transported to Γ(V-scheme,⊤) via the
sections-topIso Restrict:146) ≫ idealGenHom J V.1 f₂ hm₂` — value-level: res f₁·(…) =
res f₂·res u·(…), a ring shuffle; prove by SheafOfModules hom-ext + the :244-248 app-def.
Then 3c-iii pushes u through asIso-symm/restrictFunctorIsoPullback (iso-algebra) to the
3b-i-iso difference = mult-by-u⁻¹-form, and PoleSheaf:3488 converts to the transition
unit; the M-transition on overlaps assembles as (u₂/u₁)-shape from the 3b-ii chain legs.

3c-ii probe result (2026-08-11): `ext W a` + `simp [idealGenHom]` fires and the LHS
distributes to `res f₂ * res u * (…) g`; the remaining eq vs the composite-RHS is a
comm-ring shuffle PLUS one transport identity: the V-scheme section `topIso.inv u`
restricted through the unitEndo-app equals X-side `res u` through the `ι`-appIso — the
`Scheme.Opens.topIso`-naturality leaf. Probe file: scratchpad/probe3cii2.lean (goal-shape
displayed via failing rfl). Next session: close the transport leaf (likely
`Opens.topIso_inv`-simp or `ι.appIso`-naturality), then mul_comm/assoc finishes; then
3c-iii/iv per the cut.

3c-ii probe addendum: do NOT unfold `unitEndomorphismOfTopSection`/`unitHomEquiv` in the
simp set (whnf-wall, 200k). Correct sequence: split the composite app FIRST (find the
SheafOfModules comp-app lemma), then the @[simp] `unitEndomorphismOfTopSection_app_apply`
fires, then `simp [mul_comm, mul_assoc, mul_left_comm]` + the isolated topIso-transport
leaf. Probe file preserved at scratchpad/probe3cii2.lean (current state: ext+simp
[idealGenHom]+Subtype.ext+show all fire; tail is the documented residue).

3c-ii final probe state: statement should use `Scheme.Modules.openTopSection V u` (the
PoleSheaf:3488-native form, NOT topIso.inv). The `ext W a`-tactic itself whnf-walls on
the endo-composite — next session (with LSP): either `SheafOfModules.Hom.ext` explicit +
per-app typed-haves, or prove the app-level identity per-open as its own lemma first and
assemble hom-ext-free; comp-split via `SheafOfModules.comp_val` (Sheaf.lean:62) at the
val-level. Probe file: scratchpad/probe3cii2.lean.

3c-ii deepest probe state (2026-08-11, end of session 4): the per-app statement
elaborates; after `Subtype.ext` + `show _ * _ = _` + `rw [unitEndo-app]` +
`simp only [idealGenHom, openTopSection, map_mul, id_apply]` both sides display; the
FINAL LEAF is the appIso-path identity: LHS-factor `res u` (homOfLE-path) vs RHS-factor
`(appIso V.ι ⊤).hom ≫ (V-scheme).presheaf.map (le-⊤-res) then (appIso W).inv`-path —
i.e. `Scheme.Hom.appIso`-NATURALITY along W ≤ ⊤ (an appIso-naturality-square lemma;
check mathlib `Scheme.Hom.appIso_hom_naturality`/`appIso_inv_naturality`). Also
beta-reduce the RHS ModuleCat.ofHom-application (`ModuleCat.ofHom_apply`?) before the
factor-match. Probe: scratchpad/probe3cii2.lean (kept at this state).

3c-ii FINAL RECIPE (blind-mode complete, 2026-08-11): per-app statement + Subtype.ext +
`show _ * _ = _` + `rw [unitEndo-app]` + `simp only [idealGenHom, openTopSection, map_mul,
hom_ofHom, coe_mk]` + `simp [appIso_inv/hom_naturality, ← Functor.map_comp]` +
`rw [mul_right_comm, mul_assoc]; congr 1; congr 1` isolates THE FACTOR-GOAL:
`res u = 𝟙-hom (res (eqToHom-map u))` — a 3-line LSP-fix (fuse via the goal-spelled
comp_apply variants + thin-cat Subsingleton.elim + map_comp; the blind comp_apply-rw
pattern-misses on the CommRingCat-instance spelling). Probe frozen at this state
(scratchpad/probe3cii2.lean, tail = sorry at the factor-goal).

3c-ii LANDED (2026-08-11, session 5): `idealGenHom_mul_app` (FieldLeaf.lean, per-app
form) PROVEN AXIOM-CLEAN — build green, standard three. THE BLIND PROTOCOL THAT BROKE
THE LSP-GATE (reusable): (1) `done` as goal-printer — replacing a probe tail with `done`
makes the unsolved-goals error PRINT the full goal, no LSP needed; (2) batch N candidate
tails as N copies of the same `example` in ONE probe file — one lake run tests all;
(3) ROOT CAUSE of every simp/rw pattern-miss was a defeq-but-not-syntactic TYPE mismatch
((↑V).presheaf.obj W vs Γ(X, V.ι ''ᵁ unop W)) at the application slots — `erw` unifies
through it where simp/rw keyed-matching cannot; (4) the closer: erw [ConcreteCategory.
id_apply], erw [← ConcreteCategory.comp_apply], rw [← Functor.map_comp], then thin-cat
`congrArg (fun g => hom (X.presheaf.map g) u) (Subsingleton.elim _ _)` (also closable by
bare `rfl` — proof-irrelevant preorder-op arrows). CAUTION for reading batch outputs: a
FAILING tactic mid-sequence poisons the rest via sorryAx-recovery — only a run whose
sole error is the `done` (or zero errors) is trustworthy.

3c-iii NEXT (design refined): first sub-leaf 3c-iii-a = the idealGenHom-vs-restriction
square (restricting the V-chart trivialisation to an overlap W ≤ V equals the W-chart
trivialisation at the restricted generator, modulo the restriction functor) — every
route through the engine (PoleSheaf:3488 `overTrivializationOfRestrictIso_hom_eq_comp_
scalar`, hypothesis shape `e.hom = g.hom ≫ unitEndo(openTopSection U r)` on the COMMON
open) needs it; then 3c-iii-b = overlap generator comparison (3c-i unit u_ij) + 3c-ii
feeds the engine's h; transition-unit read-off via `overUnitScalarEnd_transitionUnit` +
`overUnitScalarEndRingEquiv`-injectivity (InvertibleSheafCocycle:44-63).

### 3c-iii REFINED CUT (2026-08-11, session 5 — the characterisation architecture)
Recon findings that close the architecture:
- `restrictOverTrivialization_inv_comp_over` (PoleSheaf:4049): a characterisation
  `e.inv ≫ i.over U = overUnitScalarEnd U r` against a GLOBAL comparison hom i RESTRICTS
  to sub-opens with the restricted scalar. This is the intended transition mechanism —
  transitions are pinned by characterisations, never computed as ratios.
- `restrictOverTrivialization_hom_eq_comp_scalar` (TrivializationRestriction:911) +
  `overTrivializationOfRestrictIso_hom_eq_comp_scalar` (PoleSheaf:3488) already exist.
- Bridges `restrictIsoOfPullbackIso`/`pullbackIsoOfRestrictIso` (InvertibleSheaf:242/249).
- `overUnitScalarEnd` takes r : Γ(X, U) directly (no openTopSection at over-level).
- The over-site hom_ext stack WORKS (no whnf-wall): Iso.ext + SheafOfModules.hom_ext +
  PresheafOfModules.hom_ext + ModuleCat.hom_ext + LinearMap.ext (TrivializationRestriction
  house style).

LANDED this session: pullbackIdealTrivOfPrincipal + pullbackTrivOfTensorIdeal (definite
3b forms, green); A0 `idealModuleToUnitHom` (inclusion, componentwise Subtype.val); A1-pre
(clothing cancellation); A1 `idealGenHom_comp_toUnitHom_app_apply` (the characterisation
per-app — rfl-attempt in build).

REMAINING LADDER (each bounded):
- (B1) over-characterisation of the ideal def-triv:
  `(overTrivializationOfRestrictIso … (restrictIsoOfPullbackIso … (pullbackIdealTriv…))).inv
    ≫ (idealModuleToUnitHom J).over V = overUnitScalarEnd V f` — from A1 + A1-pre via the
  over-conversion (hom_ext + per-app).
- (B2) scalar-mono: `overUnitScalarEnd V r` is mono for r ≠ 0 on an INTEGRAL chart
  (components = sub-opens, sections domains, restrictions injective — the 3a
  component_integral layer supplies both).
- (B3) the M-triv characterisation square (five-chain equation, per-app, blind protocol):
  incl₂-over ∘ pb(e)-over ∘ tensor-legs ∘ (id ⊗ f₁-gen) = f₂-mult ∘ (M-def-triv).
- (C) assembly: restrict both charts' B1/B3-characterisations to the inf via PoleSheaf:4049,
  apply 3c-i units (res f₁ⁱ = u₁·res f₁ʲ, res f₂ⁱ = u₂·res f₂ʲ), cancel via B2 ⟹
  `transitionUnitOfCover M W E i j = (u₂·u₁⁻¹)`-form via
  `overUnitScalarEnd_transitionUnit` + `overUnitScalarEndRingEquiv`-injectivity.
Then 3c-iv (FF-germ reading of the transition — L2e-consumer shape) rides `sectionUnits`/
germ-machinery on the C-output.

3c-iii B-LAYER LANDED (2026-08-11, session 5 cont.): B1
`overTriv_pullbackIdealTriv_inv_comp_toUnitHom` — full G.map_injective choreography
PROVEN (A1-pre rewrite + preimageIso-expansion + overEquiv_unitScalarEnd conjugation +
F.inv.naturality + cancel_epi + Iso.eq_comp_inv + calc-rfl); rests on exactly ONE
micro-sorry `idealGenHom_comp_toUnitHom_comp_unitComparison` (the
overFunctorEquiv/sheafOfModulesEquivOverUnit unit-collapse; toolkit located:
localModuleSection app-lemmas in DualPullback/OpenUnit.lean,
restrictUnitIso_inv_app_applyP in DualPullback/UnitComp.lean,
SheafOfModules.pushforwardCongr_inv_app_val_app in mathlib PushforwardContinuous —
NOTE it needs erw AND its instance context may fail; the app-splitting road
(sheafOfModules_comp_app_apply) creates type-blurred goals where NO rewriting works —
approach the micro-leaf HOM-LEVEL ONLY). B2
`mono_overUnitScalarEnd_of_nonZeroDivisors` PROVEN AXIOM-CLEAN (componentwise
cancellation; the key trick: transport the whole app-equation to the Γ-spelling via a
show-from restatement `:= by exact happ` — instances only exist at ONE spelling; ALL
mixed-spelling HMul/rw attempts fail). Remaining ladder: micro-leaf, B3 (five-chain
characterisation square), C (transitionUnitOfCover assembly), 3c-iv.

3c-iii (B3)/(C) DESIGN REFINEMENT (2026-08-11, end of session 5):
- FINDING: the tree has NO hom-level tensor functoriality (only iso-level
  `tensorObjCongr`, InvertibleSheaf:218) — the (id ⊗ incl₁)-strip characterisation of B3
  cannot be stated without building ⊗-hom-functoriality. AVOID IT:
- (C) route WITHOUT the strip: E_k := pullbackTrivOfTensorIdeal-chain = A ≪≫ B_k ≪≫ C
  ≪≫ D ≪≫ F_k (A = tensorObjUnitIso.symm, B_k = tensorObjCongr(refl, triv₁ᵏ.symm),
  C = monoidal.symm, D = mapIso e, F_k = triv₂ᵏ; A, C, D SHARED between charts).
  Transition-hom E_i.inv ≫ E_j.hom = F_i.inv ≫ D.inv ≫ C.inv ≫ (B_i.inv ≫ B_j.hom) ≫
  C.hom ≫ D.hom ≫ F_j.hom (shared A cancels). Then:
  (i) B_i.inv ≫ B_j.hom = tensorObjCongr(refl, triv₁ⁱ.symm.symm ≪≫ triv₁ʲ.symm)-form;
  the ⊗-slot iso-composite = the IDEAL transition = unitEndo(u₁)-form via the
  B1-characterisations restricted to the inf (PoleSheaf:4049) + B2-cancel;
  (ii) conjugating the ⊗-slot unitEndo through C, D, F: needs ONE new naturality
  principle — scalar-endomorphisms commute through module homs (smul-naturality),
  instantiated at tensorObjCongr/monoidal/mapIso legs. Check first:
  `unitEndomorphismOfTopSection`-naturality lemmas + whether tensorObjCongr of an
  endo-iso commutes with the monoidal leg (candidate existing lemmas in
  PullbackTensorSection.lean — grep before building).
  (iii) then transition = scalar(u₂·u₁⁻¹)-form; read off with
  overUnitScalarEndRingEquiv-injectivity (+ its RingHom structure for products).
- All of B1's restriction behaviour comes FREE from PoleSheaf:4049 once the micro-leaf
  closes (characterisations restrict; no new restriction lemmas needed for the
  ideal-legs).
PRIORITY NOTE: 3c-iii's remaining rungs (micro-leaf, (i)-(iii)) are INDEPENDENT of the
other U5 leaves — L4 (value plumbing, ranked easy, all inputs proven) and 3c-iv/L1b/L3
can land in parallel sessions. Execution order rebalance: L4 next when blind, 3c-iii
micro-leaf when LSP returns.

U5-L4 LANDED (2026-08-11, session 5): `weilPairingEval_eq_torsionSplittingEval`
(FieldLeaf, ValuePlumbing section) PROVEN AXIOM-CLEAN — the register pairing =
torsionSplittingEval at ANY normalised dataset, full generality (any base T, any pair),
by composing the two proven bridges (Basic:108 + KMNaturality:55; needed
`import ModularCurves.WeilPairing.Basic` added to FieldLeaf). The L2-side c is the
algebraMap image of this value at the 3b-dataset — L3's two inputs (L2g bridge + L4)
are now both in place; L3 additionally consumes L1 (the dictionary) for the H-form.

U5-L2 GLUING-CHECK RESOLVED (2026-08-11): the flagged "translateByPoint-vs-
translateByIso.left two-spellings" check is a NON-ISSUE — `(translateByIso E x).hom`
is DEFINITIONALLY `E.translateBy x` (Iso structure-literal projection,
TranslationBySection:77: hom := E.translateBy x), so the bridge's
τ = (translateByIso …).hom.left literally IS (translateBy …).left; and
`translateByPoint E t P := ((E.baseChange t).translateBy (overPoint E t P)).left`
(Translation:161) differs only by the overPoint/id-base-change clothing, which the
PROVEN L2b layer (baseChangeIdFstOver + translateBy_comp_of_isMonHom +
translateByPoint_id_comp_fst) transports. If the L1-glue ever hits a syntactic wall
here, add the one-liner `translateByIso_hom … := rfl`; no lemma needed now.

U5-L1b ANCHOR RECON (2026-08-11): the HasseWeil engine is COMPLETE AND PROVEN —
`const_of_projectiveDivisorOf_eq_zero` + `const_unit_of_projectiveDivisorOf_eq_zero`
(+ the τ-specialised `pairing_const_of_transport`) in
HasseWeil/HasseBound/WeilPairing/Constancy.lean, over [IsAlgClosed F] [W.IsElliptic]
[IsDedekindDomain CoordinateRing]: nonzero FF-element with projectiveDivisorOf = 0 is a
nonzero base-field scalar. L1b's REMAINING content = the scheme↔valuation divisor
translation at the quotient G/g_Q (div-scheme(G) = div-scheme(g_Q) from the 3b/3c
dictionary + brick6 pullbackDiv-vs-[N]^#-FF ⟹ projectiveDivisorOf (G/g_Q) = 0) — the
same T-C4-debt species as L1a's r-pinning — then one application of the anchor.

★ 3c-iii MICRO-LEAF PROVEN + B1 FULLY AXIOM-CLEAN (2026-08-11, session 5 finale):
`idealGenHom_comp_toUnitHom_comp_unitComparison` closed BLIND — the winning per-app
sequence: hom_ext stack + `repeat' erw [sheafOfModules_comp_app_apply]` (this time the
splitter consumed the WHOLE equiv-plumbing — the difference vs the failed B1-v3 attempt:
no cancel_epi/Iso.eq_comp_inv rearrangement first, apply the splitter to the RAW
composite-with-C.hom) + `erw [unitEndomorphismOfTopSection_app_apply,
sheafOfModulesEquivOverUnit_hom_app_apply]` + inline show-rfl (A1-value surface) +
`rw [mul_comm]; congr 1` + x-leaf (`rw [Scheme.Opens.ι_appIso]; simp; erw
[ConcreteCategory.id_apply]`) + f-leaf (`openTopSection_restrict` + `ι_appIso`-rw,
exact h). B1 `overTriv_pullbackIdealTriv_inv_comp_toUnitHom` now rests on the standard
three END-TO-END. FieldLeaf = ZERO sorries again. The 3c-iii A+B foundation is COMPLETE:
remaining rungs are (C)(i)-(iii) per the strip-free route + 3c-iv.

3c-iii C(i) ENGINE COMPLETE (2026-08-11, session 5 finale+): LANDED AXIOM-CLEAN in
FieldLeaf — `mono_idealModuleToUnitHom_over` (inclusion mono, Subtype.ext),
`overUnitScalarEnd_mul` (scalar multiplicativity; the all-Γ show-transport again),
`trivialization_inv_comp_hom_of_characterisation` (THE READ-OFF: T₁.inv ≫ T₂.hom =
scalar u from characterisations r₁ = u·r₂ via cancel_mono — NO B2-cancellation needed
for the ideal legs), `tensorObjCongr_refl`/`_trans` (C-algebra;
← MonoidalCategory.tensorHom_comp_tensorHom + Iso.ext_iff + trailing rfl).
REMAINING for (C): [C-rest-1] restrict the B1-characterisation to the inf
(PoleSheaf:4049 applied to B1 — one instantiation lemma); [C-rest-2] the inf's 3c-i unit
(span-eq + Associated on the inf-chart — mathlib-discharged per 3c-i); [C-rest-3] the
M-chain transition assembly: E_k-over-restricted transitions from the ideal-leg
transitions via the five-chain shared-leg cancellation (tensorObjCongr_trans + the
⊗-slot scalar conjugation through monoidal/mapIso/triv₂ legs — the ONE remaining
conjugation lemma) + transitionUnitOfCover read-off (overUnitScalarEndRingEquiv-inj).
Then 3c-iv (FF-germ), L1b (translation layer), L1-glue, L3, L5, L6.

★★ 3c-iii IDEAL-LEG LANE COMPLETE (2026-08-11, session 5 close): LANDED AXIOM-CLEAN —
[C-rest-1] `overTriv_pullbackIdealTriv_restrict_inv_comp_toUnitHom` (B1 restricted via
PoleSheaf:4049, term-mode one-shot); `idealTriv_restrict_inv_comp_hom` (hom-level
overlap transition = scalar u, pure assembly); ★ `trivializationTransitionUnit_idealTriv`
(THE TRANSITION THEOREM: trivializationTransitionUnit of two principal-chart
trivialisations = the 3c-i generator unit u, via overUnitScalarEndRingEquiv-injectivity;
needed the OpenUnit local-instance trick `letI : ∀ U, IsMulCommutative …` via `change` to
presheaf-obj). The FULL ideal-leg pipeline: definite triv → B1 characterisation →
4049-restriction → C(i)-b read-off → transition unit. REMAINING for 3c-iii: the M-CHAIN
assembly ([C-rest-3]: five-chain shared-leg cancellation via tensorObjCongr_trans + the
⊗-slot scalar conjugation through monoidal/mapIso/triv₂ legs) + transitionUnitOfCover
packaging; then 3c-iv. Window total: 17 axiom-clean declarations.

[C-rest-3] TARGET PINNED (2026-08-11): the KM dataset (exists_normalized_dataset,
KMDataset:220) consumes `e : ∀ i, M.over (W i) ≅ unit(over (W i))` — OVER-trivialisations
directly. The L1-glue's family is e k := overTrivializationOfRestrictIso(
restrictIsoOfPullbackIso(pullbackTrivOfTensorIdeal M J₁ J₂ e_dict V_k f₁ᵏ f₂ᵏ …)) —
exactly the crown-theorems' form. [C-rest-3]'s statement: transitionUnitOfCover M W e i j
= u₂ᵢⱼ · (u₁ᵢⱼ)⁻¹ (the two 3c-i units of the J₂- and J₁-generators), whose proof
decomposes restrictOverTrivialization of the overTriv-of-five-chain leg-wise (shared
legs A/C/D cancel via tensorObjCongr algebra; ideal legs via
trivializationTransitionUnit_idealTriv). The ONE new lemma species needed: how
restrictOverTrivialization/overTrivializationOfRestrictIso interact with the five-chain
COMPOSITE (an Iso.trans-compatibility for overTrivializationOfRestrictIso + the ⊗-slot
scalar conjugation through the C/D legs). Design next session; all inputs proven.

[C-rest-3a/b] LANDED AXIOM-CLEAN (2026-08-11): `overIsoOfRestrictIso` (general non-unit
converter, preimageIso-form) + `overTrivializationOfRestrictIso_trans` (the splitting
law: overTriv(φ ≪≫ e) = overIso(φ) ≪≫ overTriv(e); Iso.ext + map_injective +
preimageIso-simps, first shot). ANALYSIS OF THE REMAINING M-CHAIN CONTENT (next window):
the transition (restrictOver E_i).inv ≫ (restrictOver E_j).hom with E_k = overIso(φ_k)
≪≫ gen₂ᵏ-overTriv needs (α) restriction of GENERAL over-isos (a `restrictOverIso`
mirroring Dual:792's restrictOverTrivialization, + functoriality on ≪≫ so composites
restrict leg-wise), and (β) THE IRREDUCIBLE ⊗-SLOT CONJUGATION: φ_i⁻¹∘φ_j restricted =
D⁻¹C⁻¹(B_i⁻¹B_j)CD with B_i⁻¹B_j = tensorObjCongr(refl, ideal-triv₁-transition) — needs
the RESTRICT-side ideal-triv transition (the over-side crown's restrict-sibling — either
re-derive by the same characterisation at restrict-level, or transport the over-crown
back through overEquiv) and the conjugation of tensorObjCongr(refl, unitEndo-iso)
through the monoidal leg D and mapIso e — i.e. scalar-naturality of the C/D legs. Route
suggestion for (β): work at the OVER level throughout — express restrictOver(overIso φ_k)
via overIsoOfRestrictIso of the RESTRICTED φ_k (needs (α)-compat), then the B-leg
difference is the over-side ideal transition ALREADY PROVEN (crown), conjugated through
overIso(C/D-legs) — the conjugation lemma: for any over-iso ψ : A.over ≅ B.over and the
scalar-end action, ψ.inv ≫ (unit-side scalar) ≫ ψ = scalar (scalars central through
sheaf-module isos — provable per-app since scalar-end app = mult and ψ-app is linear...
CAREFUL: scalar-end lives on the UNIT only; the ⊗-slot's endo transported through
tensorObjCongr lands as an endo of pb M ⊗ pb I₁ — the smul-endo of the tensor. The
conjugation target: tensorObjCongr(refl, unitEndo u)-over-form conjugated to the
smul-endo, then through C/D/gen₂-triv to scalar u on the unit. Define the SMUL-ENDO of
an arbitrary module (smulEndo M r : End M, app = r-scaling) + its naturality through
EVERY module hom (map_smul!) — THE clean central-scalar principle; then every
conjugation step is one map_smul-naturality application. smulEndo + naturality =
next window's first construction.)

smulEndo ATTEMPT PARKED (2026-08-11, window end): the componentwise def hits the
OP-UNOP ETA WALL — at an ᵒᵖ-binder U, `(homOfLE le_top).op` lands in
`obj (op (unop U))` which is NOT syntactically `obj U`, so the SMulCommClass/Module
instances key-miss regardless of spelling (presheaf vs ringCatSheaf both tried; the
ascription coerces the term but not the instance search). Next-window fixes (pick one):
(a) eta-normalise the binder by matching `fun U => match U with | .op V => …` so all
components are at literal `op V`; (b) build smulEndo NOT componentwise but as the image
of r under a global-sections→End ring map (mirror `overUnitScalarEnd`'s
unitHomEquiv-route: does mathlib's SheafOfModules have a Module-Γ(X,⊤)-structure on
(M ⟶ M) or an endMulMap? re-grep `unitHomEquiv` consumers for the general-M pattern);
(c) define it at the PRESHEAF level (PresheafOfModules-hom componentwise where the eta
issue may not bite) and sheaf-package. The naturality THEOREM shape is right
(hom_ext + splitter + map_smul); only the carrier def is blocked. FieldLeaf reverted to
green (the two smulEndo decls removed; everything else stands).

smulEndo ROUTE (b) PAVED BY MATHLIB (2026-08-11, post-close recon): mathlib's
`PresheafOfModules` "module_over_initial" section (Presheaf.lean:385-460:
forgetToPresheafModuleCatObjObj/Map + the functor) gives each M.obj Y a
Module Γ(X,⊤)-structure via restrictScalars along `R.map (hX.to Y)` where
hX : IsInitial (op ⊤ : (Opens X)ᵒᵖ). THE ETA-FIX: `hX.to U : op ⊤ ⟶ U` lands at
LITERAL U (no op-unop artifact), and `hX.hom_ext` kills every arrow-spelling mismatch
(mathlib's own map_smul' proof there shows the pattern: rw [← R.map_comp]; congr;
apply hX.hom_ext). smulEndo carrier next window: componentwise
`fun m => (R.map (hX.to U) r) • m` with hX := initialOpOfTerminal
(IsTerminal.ofUniqueHom (fun V => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _));
naturality via M.map_smul + hX.hom_ext. Also inspect whether the mathlib functor
`forgetToPresheafModuleCat` itself already yields the endo (its morphism-level =
Γ(⊤)-linear components — smulEndo may be `(functor-image linearity)` for free).

smulEndo CARRIER LANDED (2026-08-11, true window close): `isInitialOpTop` +
`smulEndo M r : M ⟶ M` (initial-object route — the eta-wall BEATEN: hX.to-arrows land at
literal objects; the RingCat-comm wall solved by inline IsMulCommutative-change +
Std.Commutative.comm; the map_smul' via ← mul_smul ×2 + congr) + the rfl value-lemma
`smulEndo_app_apply` ALL COMPILE. `smulEndo_naturality` PARKED as a one-sorry leaf:
its proof (hom_ext stack + erw-splitter + map_smul — the shape is right) CUMULATIVE
whnf-timeouts at decl-elaboration (200k, position <decl>:0). Next-window structural
fixes: (i) prove it at the PRESHEAF level first (PresheafOfModules-hom naturality of the
val, then sheaf-hom-ext is one layer thinner); (ii) or per-app with explicit
PresheafOfModules.Hom.ext × ModuleCat.hom_ext WITHOUT the SheafOfModules.hom_ext outer
layer; (iii) or the v4.33 opacity options locally around the theorem (file has them
file-wide already — check whether the theorem's elaboration hits a `.types`-hole).
NO heartbeat bumps (user rule). Everything else in the window stands green.

★ CENTRAL-SCALAR PRINCIPLE COMPLETE (2026-08-11, window coda): `isInitialOpTop` +
`smulEndo M r : M ⟶ M` + `smulEndo_app_apply` (rfl) + `smulEndo_naturality` ALL
AXIOM-CLEAN, zero sorries. THE STORM DIAGNOSIS (reusable): the cumulative-whnf timeout
was `repeat' erw [sheafOfModules_comp_app_apply]` — repeat' retries UNBOUNDED at generic
modules and each failed attempt whnf-storms under respectTransparency-false; the fix =
BOUNDED erws (exactly as many as the goal's comp-apps). Also collected: (i) at an
ᵒᵖ-binder use IsInitial.to-arrows (isInitialOpTop) — components land at literal opens,
hom_ext kills arrow mismatches (the mathlib module_over_initial pattern); (ii)
RingCat-clothed commutativity via inline IsMulCommutative-change + Std.Commutative.comm
(mul_comm's implicit can't pin); (iii) PresheafOfModules.Hom naturality-fields are
restrictScalars-clothed — state component shows in the app_V(mapped) = mapped(app_U)
orientation (idealGenHom-precedent). M-CHAIN NEXT: restrictOverIso + ≪≫-functoriality,
then the B-leg conjugation via smulEndo_naturality ⟹ transitionUnitOfCover = u₂u₁⁻¹.

★ M-CHAIN TOOLKIT COMPLETE (2026-08-11, window coda 2): `restrictOverIso` (general-iso
restriction, three-leg mirror of Dual:792) + `restrictOverTrivialization_comp_iso`
(leg-wise restriction: restrictOver(φ ≪≫ e) = restrictOverIso φ ≪≫ restrictOverTriv e)
BOTH AXIOM-CLEAN FIRST SHOT (Iso.ext + simp on the def-shapes — the middle comparisons
cancel). THE COMPLETE BRICK LIST for the final assembly (all proven): five-chain def →
overIsoOfRestrictIso + splitting law → restrictOverIso + comp_iso → ideal-leg crown
(trivializationTransitionUnit_idealTriv) → smulEndo + naturality → C(i)-b read-off +
ringEquiv-inj → tensorObjCongr algebra. REMAINING: ONE assembly theorem
(transitionUnitOfCover of the M-family = u₂·u₁⁻¹) wiring the bricks — the composite
computation E_i-restricted.inv ≫ E_j-restricted.hom expanded by the splitting laws, the
shared legs cancelled, the B-leg = ideal-crown conjugated by smulEndo-naturality, read
off. Then 3c-iv (FF-germ), L1b translation, L1-glue, L3, L5, L6 — and U5 closes for
BOTH E4a and E5.

★ FIVE-CHAIN FACTORISATION LANDED (2026-08-11, window coda 3): `restrictOverIso_trans` +
`tensorChainPrefix` (the definite M|_V ≅ I₂|_V prefix — chart-dependence ONLY in the
J₁-leg) + `restrictIsoOfPullbackIso_pullbackTrivOfTensorIdeal` (restrict-side form =
prefix ≪≫ gen₂-division) — all green FIRST SHOT, axiom-clean. 28 landings. THE
ASSEMBLY IS NOW EXACTLY TWO RUNGS:
- [RUNG-1, the last new content] the ⊗-slot scalar transport: the B-leg difference
  restricted to the inf — restrictOverIso of overIso-of-(tensorObjCongr(refl,
  idealTriv₁-difference)) = a smulEndo-u₁-form (connect the restricted ideal-triv₁
  difference (C-rest-1×2 + C(i)-b at J₁ ⟹ scalar u₁) through tensorObjCongr — the one
  place tensor meets scalar; use smulEndo_naturality + tensorObjCongr_trans/refl).
- [RUNG-2, pure wiring] transitionUnitOfCover(M-family) = u₂·u₁⁻¹: expand
  restrictOver(E_k) via the factorisation + splitting + comp_iso laws; shared prefix-legs
  cancel (restrictOverIso_trans + overIsoOfRestrictIso_trans leg-wise); RUNG-1 gives the
  middle scalar; the gen₂-tails give the crown-scalar; compose via overUnitScalarEnd_mul;
  read off via overUnitScalarEndRingEquiv-injectivity (the crown-unit pattern).

RUNG-1 REFINED (2026-08-11): the assembly's scalars live on the INF (Γ(X, U)), so the
needed carrier is the OVER-SITE scalar `overSmulEndo M U (r : Γ(X,U)) : End (M.over U)`
(general-M sibling of overUnitScalarEnd; the global smulEndo stays as the
principle-template). Sub-rungs: (1a) def + rfl app-lemma (componentwise res-r • x along
V.hom-arrows — no initial-object trick needed, the Over-site provides the arrows; thin-cat
uniqueness for naturality); (1b) naturality through over-homs (bounded-erw shape);
(1c) THE TENSOR-MEETS-SCALAR ATOM: tensorObjCongr(refl, unitEndo u)-over-form =
overSmulEndo-u on the ⊗-object (per-app on the sheafified tensor); (1d) restrictOverIso
transports overSmulEndo to the restricted scalar; (1e) at unit: overSmulEndo =
overUnitScalarEnd (mul_comm-modulo). Then RUNG-2 wiring unchanged.

RUNG-2 DEFINITIVE WIRING MAP (2026-08-11): via the crown-pattern, RUNG-2 reduces to the
hom-level `(restrictOver E_i|inf).inv >> (restrictOver E_j|inf).hom = overUnitScalarEnd
(inf) (u2*u1^-1)`. Expansion: E_k = overIso(prefix_k) << overTriv(gen2^k) [splitting +
factorisation, LANDED]; restriction leg-wise [comp_iso + trans-laws, LANDED]. TAILS:
C-rest-1-style characterisation at gen2 (A1-pre identifies overTriv(restrictIso(pbTriv))
with overTriv(asIso(gen).symm) via congrArg). MIDDLE: prefix_i/j live at DIFFERENT
charts — decompose INSIDE the restriction: restrictOverIso(overIso(prefix_k))|inf
leg-wise; the REMAINING BULK = per-leg restriction-computation lemmas (species:
restrictOverIso(overIso(leg-at-V))|inf = overIso(leg-at-inf)) for the 5 shared
leg-species (plumbing-app, tensor-unit-iso, monoidal, mapIso-e_dict, plumbing2) — then
shared legs cancel pairwise, leaving the B-slot difference
tensorObjCongr(refl, triv1^i << triv1^j.symm-restricted) = (1c)-atom = overSmulEndo-u1
[via the J1-crown-scalars + tensorObjCongr_symm/trans]. Also needed cheap:
tensorObjCongr_symm. All scalar-plumbing (overSmulEndo trio + unit-coincidence) LANDED.

COMMUTATION-SQUARE RESIDUAL EXPOSED (2026-08-16): ONE goal — the coherence between the
OVER-restriction legs (overFunctorMap.inv >> overMap-of-preimage >> overFunctorMap.hom,
G_W-imaged) and the 11-leg PULLBACK-side chain (overFunctorEquiv >> rfip >>
pullbackCongr >> pullbackComp.inv >> pb-maps of (rfip.inv, phi, rfip.hom) >>
pullbackComp.hom >> pullbackCongr.inv >> rfip.inv >> overFunctorEquiv.inv). Full goal
text in scratchpad/probeSquare.lean's output (task b7vzdh9vl). THE TOOLKIT:
Picard/DualPullback/OverRestriction.lean's Stage-lemmas (overRestrictionStage1/2/3 +
_app_apply, overMapCompOverEquivStage1_app_apply, overMapOpenIso,
overRestrictionComparisonLeft/Right + overRestrictionComparison_app_apply) — built for
exactly this over-vs-pullback restriction comparison; mine them next window (match the
goal's leg-spellings against the Stage-composites, or go per-app with the bounded-erw
protocol reading each leg's value off its Stage-app-lemma).

SQUARE PER-APP PLAN (2026-08-16, for the dedicated probe session): bare per-app rfl
fails (whnf-budget); the working combination = hom-level kitchen-sink simp FIRST (lands
the 14-leg equation, probeSquare.lean) THEN hom_ext + per-app with the leg-value
erw-chain: LHS legs via overRestrictionStage1_app_apply (=x) + the overMap-preimage
middle (Functor.FullyFaithful.map_preimage + overFunctorEquiv_hom/inv_app_apply values)
+ overFunctorMap-hom-app; RHS legs via rfip-app values + pullbackCongr/Comp-app values
(locate/derive their _app_apply lemmas — likely rfl-species like the Stages) + pb-map-φ
app. Both sides reduce to φ.hom-app at transported sections; close by
congrArg-Subsingleton on the arrow-spellings (the whole session's standard protocol).
Bounded erws throughout (NO repeat'). Probe base: scratchpad/probeSquare.lean.

SQUARE 12-ERW WALL (2026-08-16): the bounded 12-erw splitter chain itself
whnf-timeouts (cumulative at the example head) — each erw-unification over the giant
14-leg goal compounds. NEXT SHAPES for the dedicated session: (i) HALVE — prove each
side separately equal to a common normal form (two lemmas, each a 6-erw chain); (ii)
with the LSP restored, interactive goal-state management; (iii) opacity-scoped
per-leg value lemmas FIRST (each leg's app = x as its own rfl-lemma at the FieldLeaf
defs — restrictOverIso_app_apply etc.), then the chain is pure exact-rewriting. The
square stays pinned (1 sorry); everything else in 3c-iii's finale consumes it, so the
CURRENT unblocked work = U5-L1b (scheme↔valuation divisor translation, HW anchors
verified proven, INDEPENDENT of the square) and the L1-glue prep.

L1a R-PINNING RECON (2026-08-16): the HW valuation layer is present
(exists_uniformizer Valuation.lean:258, ord_P, divisorOf, projectiveDivisorOf + _mul).
The crossing statement — scheme-side sectionIdealSheaf-generator r_i on V_i ⟼ HW
valuation-divisor of its FF-image = the (Q)-indicator restricted to V_i — is the
deepest remaining T-C4-debt item and needs its OWN sub-develop pass (the
sectionDivisor-vs-ord_P dictionary: relate `RelEffCartierDiv.sectionDivisor`'s
ideal-data through the projModel charts to ord_P at the corresponding SmoothPoint;
likely rides residueField/pointValuation comparisons + the FieldComparisonBridge
points-dictionary). Design next dedicated session; L1b-core (LANDED) consumes its
output as hdiv.

## L1a R-PINNING SUB-DEVELOP CUT (2026-08-16)
Source: KM 1.2.2 (the section divisor [P]) + Silverman II.1 (uniformizers/ord).
Scheme datum: `sectionDivisor π z hz` with `.ideal = z.ker` (CartierDivisor.lean:172);
on a principal chart V of the model curve E := modelEllipticCurve W over k, a generator
r ∈ Γ(projModel W, V) of z.ker's sections. HW target: the FF-image of r (germ →
projModelFunctionFieldEquiv) has ord 1 at Q₀ (the W-point of the section Q via the
points dictionary) and ord 0 at every other point of V's image. Leaf cut:
- [RP-1] the stalk of z.ker at the section's image point = the maximal ideal of the
  local ring (section-kernel stalk property; scheme-side, from IsClosedImmersion z +
  the retraction hz — likely near SectionsIdeal machinery).
- [RP-2] generator of a chart-restriction of z.ker generates each stalk over V
  (localisation of the span; IdealSheafData stalk-generation — mathlib-adjacent).
- [RP-3] the ord-dictionary: for x in the chart with SmoothPoint image P, ord_P of the
  FF-image of a chart-section g = the local-ring valuation of the germ of g at x
  (the scheme-stalk vs HW pointValuation comparison — the ONE genuinely new bridge;
  entry points: HW pointValuation_eq_heightOneValuation (used in Constancy's proof),
  residueFieldAtSmoothPoint, FieldComparisonBridge's projModelPointsEquiv/SpecPoints +
  pointEquivClosedPoint species).
- [RP-4] uniformizer read-off: generator of m_P has valuation 1; non-vanishing section
  has valuation 0 (HW valuation layer: exists_uniformizer Valuation.lean:258 +
  ord-characterisations).
- [RP-5] assembly: div_V(FF r) = [Q₀] on V — the hdiv-feeder for L1b-core, and the
  r_i-family transition-match (transitionUnitOfCover-image = r_j/r_i in FF) that L2e's
  dataset consumes.
[RP-3] is the sub-develop's core; do it first in the dedicated session (probe the stalk
comparison at the zChart with the FieldComparisonBridge context loaded).

RP-3 SUBSTRATE CLOSED (2026-08-16): HW-side `localRingAt P = Localization.AtPrime
(maximalIdealAt P)` of the COORDINATE RING, with DVR + IsFractionRing-to-FF instances
(Valuation.lean:50-70); pointValuation = the maximal-ideal valuation; ord_P derived.
⟹ RP-3 = scheme-stalk-at-x ≅ localRingAt P: affine-chart stalk-iso (mathlib
IsAffineOpen stalk machinery) ∘ chart-to-coordinate-ring identification (the tree's
`coordRingToZSection W` etc., as in brick6's proof) ∘ localisation-comparison — a
composition of EXISTING identifications, no new mathematics. The whole RP-1..5 cut has
identified substrates; execution is a dedicated session with the chart-identification
stack loaded (start: state RP-3 at the zChart, probe the stalk-iso composite against
pointValuation via the maximalIdealAt-correspondence).

RP RECON 100%% EXPLICIT (2026-08-16, final): `SmoothPoint C = {x, y // Nonsingular}`
with `maximalIdealAt = WeierstrassCurve.Affine.CoordinateRing.XYIdeal` (MATHLIB's
XYIdeal!) and `C.CoordinateRing = C.toAffine.CoordinateRing` — the SAME ring as the
bridge's W.toAffine side, so the SmoothPoint↔W.toAffine.Point(.some) dictionary is
coordinate-identity. THE RP-3 COMPOSITE, fully explicit:
  stalk(projModel W, x) ≅ Γ(zChart)-localisation at prime(x)   [mathlib affine stalk-iso]
    ≅ CoordinateRing-localisation                        [coordRingToZSection transport]
    ≅ Localization.AtPrime (XYIdeal P.x P.y) = localRingAt P   [prime-correspondence]
with ONE pinning lemma: the zChart-prime of the closed point x corresponds under
coordRingToZSection to XYIdeal(x-coords) (the closed-point↔maximal-ideal dictionary at
the chart — Spec-side comap computation). Every RP-leaf now has substrates named to the
mathlib-constant level; the dedicated session opens by stating the composite + the
pinning lemma at the zChart.

RP-3 DESIGN DISSOLUTION (2026-08-16, the P-parametrised dodge): NO point-classification
needed. Parametrise everything by P : SmoothPoint — define m_P := Ideal.map
(coordRingToZSection W) (maximalIdealAt P) (equiv-transport, maximality free); the
zChart-scheme-point x_P := the PrimeSpectrum point of m_P through the chart's isoSpec;
then stalk(x_P) ≅ Γ(zChart)-localisation-at-m_P [mathlib affine-stalk] ≅
Localization.AtPrime (maximalIdealAt P) = localRingAt P [IsLocalization
.ringEquivOfRingEquiv along coordRingToZSection — mathlib species]. The former
"pinning lemma" becomes DEFINITIONAL; the ONE remaining proof obligation is the
FF-COMPATIBILITY SQUARE: the localisation-equiv composite commutes with
projModelFunctionFieldEquiv on function fields (fraction-field functoriality of
ringEquivOfRingEquiv — mathlib-species). RP-4 then reads valuations through the
transported DVR structure; RP-5 assembles div_V(FF r) = [Q₀]. The whole RP-execution
is now transport + one square + the RP-1/RP-2 scheme-side stalk-generation facts.

RP-BRICK-3 RECIPE COMPLETE (2026-08-16): `projModelFunctionFieldEquiv` is ITSELF
`IsLocalization.ringEquivOfRingEquiv` along `(coordRingToZSection W).symm` at the
nonZeroDivisors (MulByHomDegree.lean:85 — same equiv, same mechanism as
zChartLocalizationEquiv at the primeCompl). ⟹ THE FF-COMPATIBILITY SQUARE = extension
UNIQUENESS: both composites Localization.AtPrime(chart-m) →+* W.FunctionField
(via zChartLocalizationEquiv → algebraMap-localRingAt-FF, and via the
primeCompl≤nonZeroDivisors tower-map → projModelFunctionFieldEquiv) restrict on
Γ(zChart) to algebraMap ∘ (coordRingToZSection).symm (by the two
ringEquivOfRingEquiv_eq computation rules) ⟹ equal by `IsLocalization.ringHom_ext
(M := primeCompl)`. Ingredients (all named): the tower-map = IsLocalization.map along
RingHom.id with primeCompl ≤ nonZeroDivisors (domain: Γ(zChart) is a domain via the
CoordinateRing-equiv transport; mathlib's primeCompl-le-nonZeroDivisors species);
HW-side algebraMap-instance localRingAt.instIsFractionRing. Statement + ringHom_ext
proof = the next quantum; then RP-brick-4 (scheme-stalk ≅ chart-localisation at x_P,
mathlib IsAffineOpen stalk machinery + hZaff), RP-1/2, RP-4-uniformizer, RP-5.

RP-BRICK-3 DRAFT LESSONS (2026-08-16, attempt parked, tree green): (i) `zChart` is NOT
in FieldLeaf's import closure (projModelFunctionFieldEquiv arrives transitively but the
abbrev doesn't) — add `import ModularCurves.EllipticCurve.MulByHomDegree`; (ii) the
`Γ(projModel W, zChart W)` notation CLASHES with the Modules-Γ overload in this file —
spell the chart ring as `((projModel W).presheaf.obj (Opposite.op (zChart W)))` (with
↑-carrier in Ideal/instance positions) or hoist the whole RP-block to a NEW FILE
(ModularCurves/WeilPairing/ValuationTransport.lean) importing MulByHomDegree + Constancy
directly, where the notation environment is clean — RECOMMENDED (also unclutters
FieldLeaf, which has grown to ~1500 lines). The brick's mathematical recipe is complete
(previous entry: ringHom_ext at primeCompl); execution = the new-file hoist + the
skeleton at the clean environment.

RP-STATE (2026-08-16, ValuationTransport.lean): bricks 1-2 AXIOM-CLEAN
(zChartMaximalIdeal + maximality + abstract primeCompl-law + zChartLocalizationEquiv);
brick-3 at 95%% — statement + ringHom_ext-reduction + simp-normalisation + h1
(tower-collapse via IsScalarTower.algebraMap_apply, PROVEN in-body) all land; ONE line
parked: `(IsLocalization.map_eq _ a).symm` (six loc-instance implicits stuck blind even
goal-anchored — canonical LSP one-liner; alternatives: fully-named M/S/T/Q/g +
hy-from-MulEquivClass.map_nonZeroDivisors-le). BRICK-4 RECIPE (mathlib entries
confirmed): x_P := hZaff.fromSpec.base ⟨zChartMaximalIdeal W P, isPrime⟩;
stalk(projModel W, x_P) ≅ Localization.AtPrime (zChartMaximalIdeal W P) via the
fromSpec-stalk comparison + `Spec.stalkIso` (AffineScheme:1293), with
`IsAffineOpen.primeIdealOf` (:775) + `fromSpec_primeIdealOf` (:780) giving the
roundtrip. Then RP-1/2 (z.ker-stalk = max-ideal at the section point; generator
generates stalks), RP-4 (DVR-uniformizer through zChartLocalizationEquiv), RP-5
(assembly). The transport's algebra-half is DONE; the scheme-half is one brick.

RP-4 CUT (2026-08-16): HW has `Uniformizer C P t := ord_P = 1` (Valuation.lean:250) but
NO generator-lemma. RP-4 = two pieces:
- [RP-4a, HW-side pure DVR] `uniformizer_of_span_maximalIdealAt`: r generating
  maximalIdealAt P ⟹ Uniformizer P (algebraMap-FF r). Route: localRingAt-image of r
  generates the DVR maximal ideal (localisation-of-span; mathlib
  IsLocalization.AtPrime.map_eq_maximalIdeal-species) ⟹ the HeightOneSpectrum-valuation
  (= pointValuation by def) of the FF-image = exp(-1) (mathlib DVR/HeightOneSpectrum
  generator-valuation species — name-hunt: intValuation_uniformizer /
  valuation_exists_uniformizer-converse / Ideal.span-generation valuation) ⟹ ord_P = 1
  by the ord_P_of_ne computation (mirror exists_uniformizer's own ending,
  Valuation.lean:258-271).
- [RP-4b, transport application] chart-side r' generating zChartMaximalIdeal ⟹
  (coordRingToZSection).symm r' generates maximalIdealAt (equiv-span-transport:
  Ideal.map-span + the equiv) ⟹ RP-4a applies; the FF-image matches the chart-side
  germ-image through brick-3's square (the parked line pins the identification).
Then RP-1/2 (section-side): z.ker-restriction's generator on a chart V ∋ Q-image maps
to a zChartMaximalIdeal-generator at P := Q-dictionary-image — the sectionDivisor-to-
transport connector (KM 1.2.2 stalk-property; needs the Q-point-to-P-dictionary at the
zChart, which is the FieldComparisonBridge points-machinery evaluated at zChartPoint).
RP-5 assembles div_V = [Q0] and feeds exists_const_mul_of_projectiveDivisorOf_eq.

RP-4a FULLY GROUNDED (2026-08-16): mathlib's `intValuation_singleton` (AdicValuation:304
— v.asIdeal = span{r} ⟹ intValuation r = exp(-1)) + `valuation_of_algebraMap` (:341 —
FF-valuation of algebraMap = intValuation) are EXACTLY the chain's core. RP-4a =
[r generates maximalIdealAt] → localRingAt-image generates DVR-max
(IsLocalization.AtPrime map-span species) → intValuation_singleton at the DVR-max
HeightOneSpectrum → valuation_of_algebraMap → pointValuation(FF-image) = exp(-1) →
ord_P = 1 (mirror exists_uniformizer's ending, Valuation.lean:263-271: ord_P_of_ne +
WithZero.unzero-computation). Every link is a named constant; the draft is mechanical.
The RP-programme's remaining unknowns: ZERO — all five leaves grounded.

## ★★ RP-PROGRAMME COMPLETE AT THE CORE (2026-08-16, ValuationTransport.lean)
51 axiom-clean landings. The full scheme→valuation chain EXISTS IN LEAN:
`zChartMaximalIdeal` (+maximality, primeCompl-law) → `zChartLocalizationEquiv`
(chart-loc = localRingAt) → `zChartPoint` + `isLocalization_stalk_zChartPoint`
(stalk = the localisation, instance-form) → `uniformizer_of_span_maximalIdealAt` (RP-4a:
generator ⟹ ord_P = 1) → `uniformizer_of_span_zChartMaximalIdeal` (RP-4b: chart-level)
→ `ord_P_algebraMap_eq_zero_of_notMem` (away-vanishing) → ★`divisorOf_algebraMap_eq_single`
(div r = [P₀]) — feeding `exists_const_mul_of_projectiveDivisorOf_eq` (L1b-core, FieldLeaf).
PARKED in the file: brick-3's one map_eq line (95%%-proven compat square).
RP-1/2 REASSESSED: the section-connector's (hspan, hoff)-hypotheses arrive CHART-WISE
from the L1-glue's own data (the 3b-charts have principal z.ker by construction) — no
standalone lemma needed; fold into the glue.
NEXT MAJOR UNIT: THE L1-GLUE (FieldLeaf-side): build the KM dataset (M := kappa-witness,
W-cover := the 3b-charts, e := the definite over-trivs) — its hM from kappa_eq-collapse,
hnorm from the crown-transitions (u-units normalised along zero — the KM h-norm content),
then L2e-instantiation ⟹ H = a·g_Q·[N]^#(r⁻¹)-form ⟹ L3 via the divisor-core +
L1b-core + brick6. Session-lessons bank (this stretch): symm-first before
single_eq_of_ne (Zero-metavar); untopD auto-reduces in display; plain-hQ direction.

## THE L1-GLUE CUT (2026-08-16)
Producer verified: `exists_affine_common_principal` (FieldLeaf:534) gives per-point
common-principal charts refined into any cover. The glue's ladder:
- [G1] the CONCRETE pre-normalised dataset: ι := ↥X-points; W c := the produced chart;
  e-family := overTriv(restrictIso(pullbackTrivOfTensorIdeal at (V_c, f₁ᶜ, f₂ᶜ)));
  hM := the 3a kappa-collapse (kappa_eq_sectionCls_mul_inv_zeroCls_of_field +
  nonempty_tensorObj... + toSkeleton_tensorObj_eq — FieldLeaf-landed); transitions =
  the (C)-assembly output (u₂u₁⁻¹-form — NEEDS the parked square + the M-chain
  assembly, OR state G1's transition-content as the chart-wise (hspan, hoff)-data
  consumed downstream without the hom-level transition theorem: REASSESS — the L2e
  reading may only need the FF-images of the r's, obtainable from RP-4b + the
  divisor-core WITHOUT transitionUnitOfCover; check L2e's exact hypothesis shape first
  (functionFieldMap_translateByPoint_germ's dataset-inputs).
- [G2] normalisation: replay exists_normalized_dataset's re-cover/rescale (KMDataset:220
  proof) CONCRETELY with tracked rescalers d_i (zero-section data ⟹ the r-relation
  survives: h_i-rescaled still a·g_Q·[N]^#(r⁻¹)-form with adjusted a).
- [G3] the L2e-instantiation at the normalised concrete dataset ⟹ H-form ⟹ L3.
FIRST ACTION next quantum: read L2e's (functionFieldMap_translateByPoint_germ) exact
hypothesis-shape to determine whether G1 needs the hom-level transitions at all.

L2E-SHAPE DECODED (2026-08-16, decisive for the glue-order): L2e
(functionFieldMap_translateByPoint_germ, FieldLeaf:279) consumes the dataset
(M,hM,W,e,hnorm) PLUS the SPLITTING FAMILY h (units on [N]⁻¹-preimages, hn-normalised)
with hsplit: [N]^#(transitionUnitOfCover M W e i j) = h_i·h_j⁻¹. ⟹ (1) the hom-level
transitions ARE consumed — the (C)-assembly (the parked square + the M-chain transition
theorem) is ON the glue's critical path (no dodge); (2) the h-family is ANOTHER concrete
dataset component: the [N]^*-splittings (KMSplitting-layer species — the [N]-pullback of
κ(Q) trivialised by the h_i; concretely from the 3b-trivs pulled along [N] + the
r-relations giving hsplit BY the crown/assembly transitions). REVISED CRITICAL PATH to
YR-2: [square (LSP/3-shapes)] → [(C) M-chain transition assembly] → [G1 dataset + h-family]
→ [G2 normalisation] → [G3 = L2e] → [L3 scalar-match] → [L6] → [U-assembly]. The square
is THE bottleneck; its dedicated session is the next major unit.

★ SQUARE REDESIGN FOUND (2026-08-16): the tree ALREADY PROVES the needed coherence —
`overRestrictModuleIso_comp_overFunctorEquiv` (OverRestriction.lean:280-ish, via the
Stage-machinery): (overRestrictModuleIso M i).hom ≫ restrictFunctor(homOfLE).map(F.app M)
= F.app M-at-V ≫ (restrictOpenCompIso i).hom.app M — the commutation of over-restriction
with the F-comparison AT EACH MODULE. THE SQUARE'S NEW ROUTE: (1) restate the square
with the RESTRICT-NATIVE restriction (restrictOpenCompIso-conjugated
(restrictFunctor (X.homOfLE)).mapIso φ) instead of my pullback-clothed
restrictRestrictIso; (2) the proof = the comparison-lemma at M and N + naturality of
restrictFunctor(homOfLE).map on φ + G.map_injective-choreography — NO per-leg app-work
remaining (the Stage-machinery already did it). (3) my pullback-clothed
restrictRestrictIso then equals the native one by a separate bridge (needed only if a
consumer wants the pullback-spelling — check consumers; the (C)-assembly can use the
NATIVE spelling throughout). ALSO LANDED this stretch: restrictOverIso hom/inv
app-twins (RFL — restriction is value-transparent), which already collapsed the
square's per-app LHS to a single overIsoOfRestrictIso-app. Next quantum: define
restrictRestrictIsoNative + restate/prove the square via the comparison-lemma;
check overRestrictModuleIso's def-relation to restrictOverIso first.

SQUARE REDESIGN VERIFIED AGAINST DEFS (2026-08-16): `overRestrictModuleIso M i`
(DualPullback:27) = G_V(mapIso (overFunctorMap.app M).symm) ≪≫ (overMapCompOverEquiv
i).app (M.over U) — the G-IMAGED over-restriction, same overFunctorMap-leg as
restrictOverIso. THE ASSEMBLY (execution-spec): G.map_injective; G(square-LHS) factors
through overRestrictModuleIso(M/N) [by restrictOverIso's def + G-functoriality];
G(square-RHS) factors through the F-apps at V [by overIsoOfRestrictIso's def]; the two
factorisations meet by `overRestrictModuleIso_comp_overFunctorEquiv` at M and N +
`(restrictFunctor (X.homOfLE)).map`-naturality on the φ-middle + restrictOpenCompIso-
conjugation matching the restrict-native restriction. Statement change: use the
restrict-native `restrictRestrictIsoNative φ := (restrictOpenCompIso i).app-conjugated
(restrictFunctor (X.homOfLE (leOfHom i))).mapIso φ`. All three assembly-lemmas PROVEN
in-tree; the square's execution = one statement + one choreography, zero new species.

SQUARE ENDGAME DIAGNOSIS (2026-08-16): the def-expansion simp (projecting to .hom)
CREATES the sheaf-type blur that then poisons ALL goal-rewriting (rw, simp-only,
conv alike — 'target not type-correct under implicit transparency'). THE CLEAN ROUTE =
ISO-LEVEL CHOREOGRAPHY (never project to .hom): G.mapIso(square-LHS) decomposes as
G-mapIso(FM.symm) ≪≫ G-mapIso(overMap.mapIso(preimageIso K)) ≪≫ G-mapIso(FM); conjugate
the middle by the NatIso overMapCompOverEquiv (its naturality in ISO form) to
capp ≪≫ restrictFunctor.mapIso(G_U.mapIso(preimageIso K)) ≪≫ capp.symm; collapse
G_U.mapIso(preimageIso K) = K-as-iso (FullyFaithful preimageIso-roundtrip); then the
comparison-lemma pair (hcompM/N — RESTATE AS ISO-EQUATIONS via Iso.ext-inverse or use
their hom-forms only at the final Iso.ext step) assembles the two sides. All banked
in-proof ingredients stay valid. Iso-level lemma names to gather: NatIso-conjugation of
mapIso (β.app-conjugation), Functor.FullyFaithful.preimageIso-roundtrip
(map-preimageIso = the iso), Iso.trans-assoc-normal simp-set.

SQUARE ENVIRONMENTAL RESOLUTION (2026-08-16): every route hits the SAME schism — the
Scheme-world (TopCat.Sheaf RingCat) vs the Sites-world (Sheaf (Opens.grothendieckTopology))
spelling divide between FieldLeaf's environment and OverRestriction.lean's. The Stage-
machinery lives natively in the latter. RESOLUTION = HOIST (the ValuationTransport
pattern): move restrictOverIso + overIsoOfRestrictIso + their trans-laws + app-twins +
restrictRestrictIsoNative + THE SQUARE into a new
`WeilPairing/OverRestrictionSquare.lean` that imports
Picard/DualPullback/OverRestriction.lean and copies ITS opens/namespace conventions
exactly (namespace AlgebraicGeometry.Scheme.Modules alignment) — there the comparison-
lemma pair, the naturality, and the def-expansions all share ONE spelling-world and the
banked choreography (hnat + hcompM/N + hmid + htail-inversion + the assembly) should
fire without blur. FieldLeaf re-imports the new file. The banked in-proof ingredients
and the recorded assembly-plan carry over verbatim.

SQUARE LANDED (2026-08-16): `restrictOverIso_overIsoOfRestrictIso` PROVEN AXIOM-CLEAN
in the new `WeilPairing/OverRestrictionSquare.lean` (namespace
AlgebraicGeometry.Scheme.Modules; FieldLeaf imports it; the cluster defs
overIsoOfRestrictIso / restrictOverIso / restrictRestrictIsoNative moved there;
FieldLeaf green + sorry-free). ROOT-CAUSE RESOLUTION: the blur is NOT FieldLeaf's
opacity options — it is inherent to the `TopCat.Sheaf`-vs-`Sheaf (Opens.grothendieckTopology)`
schism inside `X.ringCatSheaf`-typed terms: any rw/simp whose pattern must unify at an
`overFunctorEquiv`/`overFunctorMap`-headed app node fails EVEN AT DEFAULT TRANSPARENCY
and EVEN HYPOTHESIS-SIDE (their functor-implicits carry the blur-node
`Sheaf.over X.ringCatSheaf`); omc-/restrictOpenCompIso-headed apps match fine; DEFEQ
UNIFICATION (exact / typed-have casts / rfl) bridges everything. THE BLUR-PROOF
PROTOCOL (reusable): (1) typed-have restatements cast library facts into one
NatTrans-level spelling (`.hom.app`/`.inv.app`); (2) every pair-collapse is a
TERM-APPLIED lemma (Iso.hom_inv_id_app / _assoc variants, Functor.map_comp/map_id via
congrArg-on-Functor.map); (3) reassoc_of% for prefix-rewrites and to auto-type the
composable-k segment lemmas; (4) splice collapses tail-first into right-assoc chains
by congrArg under prefix-lambdas; (5) assoc-regroup to the goal's bracketing by
Category.assoc term-application; (6) close with `exact` (defeq bridges Iso.app-vs-
hom.app and Over.mk-hom spellings). Zero pattern-matching at blurred nodes.

[C-rest-3] ROUTE LOCKED (2026-08-16): the CHART-DEPENDENT CHARACTERISATION route
(generalised crown), chosen over leg-restriction-coherences (5 iso-species) and
tensor-multiplicativity (needs over-monoidal comparison) after full triage. Mechanism:
- nu_k : M.over(W) --> unit.over(W), the chart's comparison hom :=
  (M ~ M(x)O --(1(x)f1_k-insert)--> M(x)I1 --e_dict--> I2 --iota2--> unit)-over-form,
  restricted to the overlap (chart-dependence ONLY through the inserted f1_k).
- PER-CHART characterisation: T_k.inv >> nu_k = overUnitScalarEnd(res f2_k): the
  e/e.inv and (x)-slot triv1/insert-f1 pairs cancel WITHIN the chart (tensorObjCongr
  algebra + A1-pre/3c-ii species, all landed), leaving the idealGenHom_mul 3c-ii value.
- CROSS-CHART: nu_i = nu_j-times-u1 ((x)-linearity in the I1-slot: f1_i = u1*f1_j),
  so T_i.inv >> T_j.hom reads off as scalar(res f2_i * (res f2_j)^-1 * u1^-1-form)
  = u2 * u1^-1 via the generalised C(i)-b (characterisations against DIFFERENT
  nu's related by a unit) + mono_overUnitScalarEnd_of_nonZeroDivisors (B2 — built
  for exactly this cancellation).
- Read-off: overUnitScalarEndRingEquiv-injectivity (crown pattern) ==>
  transitionUnitOfCover M W e i j = u2 * u1^-1.
Bridging lemmas already landed en route: overTrivializationOfRestrictOpenTrivialization
(TrivializationRestriction:822 — over-restriction = overTriv of restrict-side rOT),
restrictOpenTrivialization_eq_pullback (:814), overTrivializationOfRestrictIso_injective
(:852), restrictOverTrivialization_hom_eq_comp_scalar (:911), transitionUnitOfCover def
= trivializationTransitionUnit of the two restricted overTrivs (KMPatching:197).

[C-rest-3] SESSION LANDINGS (2026-08-16, route-C execution): SEVEN of the nine skeleton
leaves PROVEN in FieldLeaf — [SK-W2'] overTriv_inv_comp_hom_of_restrict_scalar (G.map_inj
+ preimageIso-expansion + overEquiv_unitScalarEnd + Category.assoc term-bridges);
[SK-read-off] pullbackTrivialization_inv_comp_hom_of_nu (cancel_mono on the r2-endo, NO
nu-mono needed); [SK-B2-restrict] mono_unitEndomorphismOfTopSection_of_nonZeroDivisors
(mul_cancel_right_mem_nonZeroDivisors dodges the sub_mul instance-wall); idealGenHom_mul
(hom-level of the 3c-ii app-lemma, one-exact); smulEndo_unitObj [RUNG-1e-restrict]
(Subsingleton-arrow congrArg + mul_comm (G := Gamma)-defeq-cast); ***THE TENSOR-MEETS-
SCALAR ATOM*** sheafificationMap_whiskerLeft_unitEndomorphism [RUNG-1c] (sheafification-
adjunction homEquiv-injective + unit-naturality + TensorProduct.induction_on + the
`show ... from`-RE-TYPING of the scalar to the tensor's own base-ring clothing — plain
type-ASCRIPTION is a no-op on rigid terms and leaves the SMulCommClass wall);
[SK-ratio] nuPullback_mul (h2core at the trans-form + defeq-cast — def-unfold simp
whnf-storms; then hp1 (tOC-refl = sheafification-whisker, rfl) + whiskerLeft_comp +
THE ATOM + ONE smulEndo_naturality at the whole 5-chain composite + smulEndo_unitObj).
REMAINING: [SK-normal] (rOT vs restrictTrivialization under restrictIsoOfPullbackIso),
[SK-per-chart] (the characterisation grind), the final assembly statement (glue-side).
NEW BATTLE-LESSONS: (i) probe-files that RE-STATE IsIso(idealGenHom ...)-binders
whnf-storm at statement-elaboration while the identical in-FieldLeaf skeleton is fine
— iterate heavy statements IN THE FILE; (ii) `reassoc_of%` on an already-tail-less
equation adds a spurious ?h-tail that blocks rw — use the plain lemma + assoc-flatten;
(iii) wrong-namespace `map_smul` (AG-shadow) silently mismatches — pin LinearMap.map_smul.

[SK-per-chart] GRIND-PLAN (2026-08-16, for the next quantum — the LAST route-C leaf):
Statement: (restrictTrivialization hWV (pullbackTrivOfTensorIdeal ... V f1 f2)).inv >>
nuPullback(res f1) = unitEndomorphismOfTopSection (openTopSection W (res f2)).
ROUTE-TRIAGE done: (a) leg-restriction coherences need a pullbackTensorObjIso-COMP
lemma that does NOT exist (PullbackTensorMonoidal has only the single-immersion iso)
=> heavy; (b) VALUE-ROUTE chosen: both sides are homs unitObj W -> unitObj W;
`apply (unitObj W.toScheme).unitHomEquiv.injective` (mathlib equiv, no new species).
RHS-value free: unitEndomorphismOfTopSection r := unitHomEquiv.symm (moduleSectionsOfTop r)
(UnitPullback:36) => unitHomEquiv-image = moduleSectionsOfTop (openTopSection W (res f2))
by Equiv.apply_symm_apply. LHS-value: unitHomEquiv (T.inv >> nu) — chase the section:
(i) find/derive the unitHomEquiv-naturality (unitHomEquiv (f >> phi) = phi-section-image);
(ii) T.inv's unit-section = the restricted five-chain trivialising section — compute
through restrictTrivialization's four legs (pullbackCongr/pullbackComp/mapIso/
pullbackUnitIso) at the TOP component via their app-lemmas (KMPatching's
sectionEval/resUnit machinery is precedent); (iii) nu's value on it: slot-insert of
res f1, e_dict, iota2 (Subtype.val), pullbackUnitIso — per-app; (iv) the composite
value collapses by the e/e-inv and f1-divide/insert cancellations ELEMENT-WISE to
(res f2)-multiplication (3c-ii idealGenHom_mul_app is the model). Expect bounded-erw
protocol + the show-from re-typing trick at cross-clothed smuls. All work IN FieldLeaf
(probe-restating IsIso(idealGenHom)-binders whnf-storms — battle-lesson).
AFTER per-chart: state+prove the ASSEMBLY ([C-rest-3] proper): transitionUnitOfCover of
the overTriv-of-five-chain family = u2 * u1^-1 — wiring: KMPatching:197-def +
overTrivializationOfRestrictOpenTrivialization + [SK-normal] + per-chart at both charts
+ nuPullback_mul (u1-ratio, g_i = u1 * g_j needs mul-hyp massage) + [SK-read-off]
(r1 = res f2_i, r2 = res f2_j, v = the u2u1-ratio via span-Associated at the inf) +
[SK-W2'] + [SK-B2-restrict] (nzd-hyps from the curve's integrality at instantiation).
Then 3c-iv, G1-G3, L3, L5, L6, U-assembly, E5-assembly.

[SK-per-chart] VALUE-TOOLKIT POINTER (2026-08-16): the reduction's mathlib API is
rfl-level and COMPLETE — SheafOfModules.unitHomEquiv (Sheaf.lean:178),
unitHomEquiv_apply_coe (:183, .val X = f.val.app X 1, rfl), unitHomEquiv_comp_apply
(:186, equiv-of-composite = sectionsMap, rfl), sectionsMap_comp (rfl),
unitHomEquiv_symm_comp (:190). unitEndomorphismOfTopSection r :=
unitHomEquiv.symm (moduleSectionsOfTop r) so its equiv-image is free. The engine's
section-value machinery for the leg-chase lives in Picard/DualPullback/
{PullbackSection, LocalSection, LocalTrivialization, LocalTrivializationInv,
LocalTrivializationSection, LocalUnit}.lean — e.g. iso_hom_inv_app_applyT /
iso_inv_hom_app_applyT (PullbackSection:25/33, T = top-component). MINE THESE FIRST
before writing any new app-value lemma.

[SK-per-chart] HTOP CUT (2026-08-16 continuation): htop is now the verified-show recast
point-equation `nu.app top (T.inv.app top 1) = (unit).map (top<=top) (openTop res-f2)`.
(The bare literal `1` in a show is TYPE-BAD and silently sorryAx-recovers — clothe as
`show W.toScheme.presheaf.obj (op top) from 1`, engine idiom; VERIFY every show with a
done-swap build, never trust a green sorry-tailed build.) Remaining cut:
[H1] RHS map-along-top<=top = id (Subsingleton-arrow + map_id; engine pattern
PullbackSection:81). [H2] T.inv.app top 1 = the transported V-section: statement via
sheafIso_inv_app_eq_of_hom_app_eqT (LocalTrivializationInv:131 — the GENERAL inversion
tool: hom-value determines inv-value); candidate x := (pbCongr.inv)(pbComp(eta_h(s_V)))
with s_V := pbTriv-V.inv.app top_V 1; hom-value-chain via the eta-transport family
(pullbackUnit_map_appT LocalSection:252, pullbackUnitIso_hom_unit_oneT :296,
pullbackUnit_one_transport_topT :318 for the eqToHom top-corrections) + iso_inv_hom free
at V. [H3] nu.app top on the transported section = openTop(res f2): nu-legs elementwise —
slot-insert/e_dict/iota2 on eta-points (pullbackUnit_map_appT again for pb-W-maps... note
nu's legs are pb(W-iota)-maps and tensor-legs: tensor-point-values via the toSheafify/
adjunction idiom as in THE ATOM; the e/e-inv cancellation happens between H2's s_V-content
and H3's e-leg — consider merging H2+H3 into one chain ending at the V-level
f2-generator value (idealGenHom-app is concrete: f*appIso.inv-formula, IdealModule:240)).

[SK-per-chart] H2 LANDED + H3 FRONTIER (2026-08-16, cont.): H1 closed (Subsingleton-arrow
+ restrictScalarsId'App_inv_apply wrapper-erw). H2 = restrictTrivialization_inv_app_top_one
PROVEN (standalone, reusable at both charts): the inversion tool
sheafIso_inv_app_eq_of_hom_app_eqT reduces to a hom-value chain closed by g1..g7:
congr/comp-cancels (iso_inv_hom/hom_inv_app_applyT at the pullbackCongr/Comp app-isos),
pullbackUnit_map_transportT at t.hom, t-inversion, PresheafOfModules.naturality_apply at
the eqToHom, pullbackUnitIso_hom_unit_oneT, and a PRESHEAF-CLOTHED map_one (the
module-clothed carrier has no One instance — restate g7 at W'.presheaf and defeq-cast).
LESSON: the erw-cascade version whnf-STORMS at the first pair-cancel (kabstract on the
eqToHom-laden goal) — the congrArg TERM-chain with fully-spelled inner terms is the way
(python-template the terms). H2 is PLUGGED into the per-chart frontier (htop' : top =
preimage-top is rfl). REMAINING = H3: nu.app top (pbCongr.inv(pbComp.hom(eqMap(eta(s_V)))))
= openTopSection W (res f2), s_V := pbTriv-V.inv.app topV 1. H3-cut: (a) V-LEVEL:
s_V's five-chain value — by the SAME inversion-tool pattern at V: s_V is THE element with
pbTriv.hom(s_V)=1; candidate x_V := tensor-transported e.inv-image of the f2-generator
section (genHom-app formula IdealModule:240 is concrete: f * appIso.inv-arg); the
five-chain hom-value on x_V via tensor-point lemmas (toSheafify/eta idiom as in THE ATOM).
(b) W-LEVEL: nu's four legs on the transported point — slotIso (tensor), pb(e), pb(iota2),
pbUnitIso — using pullbackUnit_map_appT on eta-points + the eqToHom-naturality plumbing
(H2's g5-pattern). (c) the alignment: nu-legs vs the transported V-data — the e/e-inv
cancellation manifests as: pb-W(e).map on the eta-image of e.inv-applied-x = eta-image of
x (map_appT + e.inv-hom-cancel at V-level). Consider proving (a)+(c) MERGED: define the
candidate x_V so that the H3-chain never needs s_V alone.

[H3] DESIGN RESOLVED (2026-08-16, cont.2): the four-leg chase on the transported point.
KEY INSIGHT — the map-legs WALK by NATURALITY, not by value: pb(W.iota).map(e.hom) and
pb(W.iota).map(iota2) commute LEFT through the pbCongr.inv/pbComp.hom transport by the
NatIso-naturality of pullbackCongr/pullbackComp (hom-level, no values), turning them into
pb(h).map(pb(V.iota).map(...)) which act on eta_h-points by pullbackUnit_map_appT; the
V-level values then cancel against s_V's five-chain V-legs (e.inv against e.hom at V —
iso_hom_inv_app_applyT; the triv2-tail yields the f2-generator value via idealGenHom-app's
concrete formula). The pbUnitIso-tail closes by the oneT-family + eqToHom-naturality
(H2's g5-g7 pattern). THE ONE IRREDUCIBLE NEW COHERENCE [H3-T]: the slot-leg
(tensorIdealSlotIso, W-local tensor-structural) does NOT walk by naturality — needs the
TENSOR-TRANSPORT coherence: pullbackTensorObjIsoOfIsOpenImmersion vs pullbackComp
(pb(h)-image of the V-comparison = W-comparison modulo pbComp-legs on both tensor-factors)
— PLUS the same for tensorObjUnitIso (unit-slot) and for the genHom-B-slot
(genHom-restriction: pb(h)-transport of idealGenHom-V vs idealGenHom-W(res f1) — this one
is ALSO the deferred glue-instantiation species!). Technique for all three: the
sheafification-adjunction + eta/toSheafify idiom (THE ATOM's pattern) — presheaf-level
tensor is pointwise, the coherences are toSheafify-naturality chases. Alternatively
consider stating [H3-T] directly as the SLOT-LEG's action on the transported point
(one merged value-lemma instead of three iso-coherences) — fewer statements, same content.

[H3-T1] PROOF LAYER-MAP (2026-08-16, cont.3): pullbackTensorObjIsoOfIsOpenImmersion's
def (PullbackTensorMonoidal:331) = e1 (rfip.symm) >> e2 (sheafifyValIso.symm) >>
e3 (asIso of the sheafificationW-inverted pushforward-unit-tensor comparison) >>
e4 (sheafification.mapIso (pushforwardTensorIso (restrictRingHom f)).symm) >>
e5a (refl) >> e5b (tensorObjCongr of rfip's). pushforwardTensorIso (:206) =
restrictScalarsTensorObjIso >> restrictScalars-mapIso (Functor.Monoidal.muIso
(pushforward0OfCommRingCat F R)) — mathlib's monoidal-functor mu at the reindexing +
scalar-restriction along the componentwise-iso ring comparison. [H3-T1]'s proof
therefore decomposes along: (L1) rfip-comp (restrictFunctorIsoPullback_comp — LANDED,
RestrictComp:180) aligns the e1-legs; (L2) sheafifyValIso vs sheafification-functor
composition (naturality of the counit — mathlib); (L3) the e3-legs: sheafificationW-
inverted comparisons compose (W-members closed under the composition — the hmem-terms'
asIso-functoriality); (L4) pushforwardTensorIso-COMP: mu-composition for
pushforward0OfCommRingCat of a composite site-functor (mathlib Functor.Monoidal
composition laws: muIso of F ⋙ G) + restrictScalarsTensorObjIso-comp (two-step scalar
restriction along composed ring-comparisons); (L5) tensorObjCongr-algebra tail (landed).
Estimated as its own decompose-first task — run /develop-style leaf-cuts on L2/L3/L4
before tactics. ALTERNATIVE still open: state the SLOT-LEG's transported-point VALUE
directly and prove by the adjunction/eta idiom end-to-end (one lemma, no iso-coherences;
revisit after attempting L1-L5's first leaf).

[H3-S] PROOF ROUTE OPENED (2026-08-16, cont.4): the merged slot-transport square
pullbackRestrictTransport_tensorIdealSlotIso is stated; tau := pbComp.hom >> pbCongr.inv
(pullbackRestrictTransport) with its NATURALITY PROVEN (handles the e_dict/iota2 map-legs
of the per-chart chase in one stroke — typed-have + congrArg-splice past the Iso.app
blur, again). Proof-route for the square: DOUBLE-ADJUNCTION reduction — (1) geometric:
(pullbackPushforwardAdjunction (homOfLE hWV)).homEquiv-injective + homEquiv_apply
[OPENED, green]; transposed sides are eta-precomposed pushforward-images at V-level
(pushforward along an open immersion is concrete: sections at preimages); (2) then the
sheafification-adjunction (THE ATOM's pattern) to reach the presheaf-pointwise level;
(3) TensorProduct.induction_on pure-tensors + eta-naturality chases; the genHom-
restriction content (res-g vs g) lands as a presheaf-level component identity
(idealGenHom's app formula IdealModule:240 is concrete). Fallback remains H3-T1's
layer-route L1-L5. AFTER H3-S: per-chart closes = slot-walk (H3-S) + map-leg walk
(tau-nat) + pbUnitIso-tail (oneT + g5-g7 pattern) + V-level cancellation
(iso_hom_inv_app_applyT at pb-V(e) + genHom-value); then the cross-chart assembly.

[H3-S] TRANSPOSED FORM + HONEST ASSESSMENT (2026-08-16, cont.5): after the geometric
transposition the square reads `unit >> pf(tau_M >> slot-W) = unit >> pf(pb(slot-V) >> 
tau_tensor)`; pf-map_comp splits and the RHS's pb-factor walks out by unit-naturality,
leaving `upsilon_M >> pf(slot-W.hom) = slot-V.hom >> upsilon_tensor` with
upsilon_A := unit.app (pb-V A) >> pf(tau_A) (natural in A by unit-nat + tau-nat, both
landed). The remaining content is the slot-legs' values, which stay sheafification-
opaque under further transpositions (the source M is an abstract sheaf, so the atom's
sheafification-source trick does not directly apply). VERDICT: H3-S's proof needs the
slot unfolded to its sheafification normal-form — i.e. the LAYER ROUTE (L1-L5 of the
H3-T1 map) is the honest cost either way; the square-form is still the better TARGET
statement (single consumer-shaped equation). NEXT SESSION: decompose-first on the
layers — start with [L4a] pushforwardTensorIso-COMP (mathlib Functor.Monoidal mu-comp
laws + restrictScalarsTensorObjIso-comp) and [L3] the sheafificationW-asIso
functoriality, each as its own probe; then assemble H3-S by the e1-e5b-normal-forms of
both slot-W and pb(slot-V) against tau's pbComp/pbCongr legs (rfip-comp LANDED covers
the e1-alignment).

[PER-CHART PRIME ALTERNATIVE — THE NATIVE-MIDDLE INSERTION] (2026-08-16, cont.6):
potential TRANSPORT-FREE assembly discovered while triaging the L-layers. Insert the
W-NATIVE chain t_W(k) := (tensorIdealSlotIso at W with res f1_k) >> pb-W(e_dict) >>
pullbackIdealTrivOfGen-J2-W(res f2_k) — ALL general-W species (already landed as defs!)
— as middle terms via the transition-cocycle law:
  transition(e_i|, e_j|) = transition(e_i|, tW_i) * transition(tW_i, tW_j) * transition(tW_j, e_j|).
- MIDDLE = native-vs-native = the crown-pattern with nuPullback: tW.inv >> nu_W collapses
  by PURE ISO-CANCELLATION (slot.inv against slot, pb(e).inv against pb(e) — no values,
  no sheafification!) to the J2-generator tail; with [SK-read-off]+nuPullback_mul+B2r
  (all landed) gives u2*u1^-1 CHEAPLY. Needs one new W-level species: hom-level
  `pullbackIdealTrivOfGen.inv >> pb(iota2) >> pullbackUnitIso = endo(res f2)`
  (the A1/3c-ii sibling at general W — genHom-app is concrete, no opacity).
- OUTER terms A_k := transition(e_k|, tW_k): chart-restricted-vs-native. DO NOT compute
  them: define A_k-full := transition(e_k, t_{V_k}-native) in Gamma(V_k)-units at the
  FULL chart, and use a TRANSITION-RESTRICTION coherence (trivializationTransitionUnit
  of restricted pairs = res of the unit — provable from
  restrictOverTrivialization_hom_eq_comp_scalar (:911, landed) + overUnitScalarEnd-
  restriction) to get A_k-at-W = res(A_k-full). Then the e-family transition =
  res(A_i) * (u2 u1^-1) * res(A_j)^-1 with A_k CHART-LOCAL — the h-family absorbs them
  (h_k := [N]^#(A_k)-corrected), hsplit keeps its cocycle shape.
⚠ ADVERSARIAL CHECK REQUIRED before adopting: does the U5-chain's downstream (L2e
tau-relation, L1b divisor-matching, 3c-iv germ-reading, L3 scalar-match) tolerate the
transition value u2*u1^-1 * res(A_i A_j^-1) with A chart-local units — i.e. do the
A-factors cancel in the final pairing-value (they should: the pairing is an h-ratio and
chart-local units drop out of the SAME-chart evaluations, mirroring KM's own
normalisation freedom — this is exactly the exists_normalized_dataset rescaling-slack)?
If YES: the ENTIRE transport-block (H3-S/H3-T1/L1-L5, and even H2!) leaves the critical
path — [SK-per-chart] as stated becomes UNNECESSARY (delete or park the three sorried
transport lemmas). If NO: continue the L-layer route. DECIDE FIRST NEXT SESSION
(decompose-adversarial on the A-cancellation through the glue's consumption chain).

[GATE — DECISIVE OBSERVATION] (2026-08-16, cont.7): the A-dressing is THE SAME SPECIES
as G2's normalisation-rescalers. The glue's own plan (G2: exists_normalized_dataset
replay with TRACKED RESCALERS) already dresses every transition as
res(r_i) * f_ij * res(r_j)^-1 with chart-local units r_k, and the downstream design
(hsplit-absorption into the h-family, 3c-iv germ-reading, L1b constant-freedom) was cut
to cope with exactly that — otherwise G2 itself would be unsound. Hence the prime
alternative's A_k := transition(e_k, t_{V_k}-native) are absorbable exactly like the
r_k: fold them INTO the G2-rescaling step (equivalently: normalize the NATIVE-family
directly). DEFAULT FLIPPED: next session executes the NATIVE-MIDDLE ROUTE —
(N1) W-level A1-sibling: pullbackIdealTrivOfGen.inv >> pb(iota2) >> pullbackUnitIso =
endo-of-generator (hom-level, genHom-app concrete); (N2) native-vs-native transition =
u2*u1^-1 via iso-cancellation + [SK-read-off]/nuPullback_mul/B2r (all landed);
(N3) transition-restriction coherence (res of transitionUnit — :911-based) + A_k-full
definition; (N4) re-cut the glue's G1/G2 to carry the A/r-dressing uniformly; then the
transport lemmas (H2 [proven — keep, may serve elsewhere], H3-S/H3-T1 skeletons,
[SK-per-chart] as stated) get PARKED (comment DEFERRED, or delete the sorried skeletons
at the G1-recut if truly consumed nowhere). VERIFY at N4-time that hnorm's
zero-section-normalisation interacts with the A-fold as with r-fold (same lemma).

[N-ROUTE MILESTONE] (2026-08-16, cont.8): N1 + N2-cancel PROVEN — the native-middle
route's characterisation chain is COMPLETE: nativeTensorIdealTriv (def) is characterised
against nuPullback by pure iso-cancellation (one simp: slot+dictionary collapse) down to
the W-level A1-sibling pullbackIdealTrivOfGen_inv_comp_toUnit, itself closed by the
rfip-naturality walk + restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG + the
concrete app-chase (KEY: Scheme.Opens.iota_appIso collapses appIso to Iso.refl — then
the wrappers are RFL-transparent; simp refuses them but rfl-bridges + show-from
clothing close; openTopSection_restrict massaged by the same iota_appIso rw). WITH the
landed [SK-read-off] + nuPullback_mul + B2-restrict, the NATIVE-vs-NATIVE transition
value u2*u1^-1 is now a pure assembly. REMAINING for [C-rest-3]-via-N-route:
(N3) transition-restriction coherence + A_k-full (from :911) — then the assembly
statement dressing transitions as res(A_i) * u2u1^-1 * res(A_j)^-1; (N4) G1/G2-recut
carrying the dressing. The three transport-sorries (H3-T1, H3-S, [SK-per-chart]-as-
stated) are now OFF the critical path — park/delete at the G1-recut.

★★ [N-ROUTE CORE COMPLETE — AXIOM-CLEAN] (2026-08-16, cont.9): #print axioms confirms
nativeTensorIdealTriv_inv_comp_hom + pullbackIdealTrivOfGen_inv_comp_toUnit +
nativeTensorIdealTriv_inv_comp_nu are ALL [propext, Classical.choice, Quot.sound] —
NO sorryAx: the native-vs-native transition u2*u1^-1 is proven END-TO-END independent
of the parked transport-sorries. The (C)-computation's mathematical heart is DONE.
N-transition proof pattern (reusable): subst the unit-relations FIRST (g free vars ⟹
subst works, aligning all dependent-hypothesis types), then the two N2-characterisations
+ nuPullback_mul + endo-composition algebra (unitEndomorphismOfTopSection_comp, _one,
openTop-map_mul/map_one as local haves) + the C(i)-b read-off + `ring` for the
unit-coe arithmetic. REMAINING for [C-rest-3]: (N3) the transition-RESTRICTION
coherence (trivializationTransitionUnit of restricted trivialisation-pairs = res of
the unit; from restrictOverTrivialization_hom_eq_comp_scalar :911 + [SK-W2']) +
A_k := transitionUnit(chart-e_k, native-at-V_k) in Gamma(V_k)-units; then the
transitionUnitOfCover-packaging (KMPatching:197-def + overTriv-of-native via
[SK-W2']-style bridges) dressing as res(A_i) * u2u1^-1 * res(A_j)^-1; (N4) the
G1/G2-glue-recut. Then 3c-iv, L3, L5, L6, U-assembly, E5.

[N-PACKAGING ANALYSIS — THE DRESSING BOUNDARY] (2026-08-16, cont.10): N3 + the cocycle
law (trivializationTransitionUnit_trans, InvertibleSheafCocycle:118 — LANDED) give the
packaging frame, but the chart-LOCAL dressing hits a genuine fork:
- cocycle-insertion with res-generator-natives t_W(k): middle = u2*u1^-1 [N-TRANSITION,
  proven] but the outer terms transition(res-e_k, t_W(k)) are PAIR-local (W-dependent),
  not chart-local — cannot fold into the h-family directly.
- cocycle-insertion with restricted-FULL-natives res(tfull_k): outer terms = res(A_k)
  by [N3] with A_k := transition(e_k, tfull_k) CHART-local — but the middle then needs
  transition(res-tfull_i, res-tfull_j), whose reduction to u2*u1^-1 needs
  res-tfull_k = t_W(k)-modulo-1 — WHICH IS the parked transport-coherence again
  (restricted-native vs res-generator-native = the [SK-per-chart] species).
⟹ the transport-content is irreducible FOR AN EXPLICIT chart-locally-dressed value.
BUT the value may not be needed in that form: the h-family in hsplit is produced by
AP-D4's machinery (exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints) for ANY
normalized kappa-dataset — NOT from an explicit u2u1^-1 formula. The explicit value
enters ONLY at 3c-iv (the FF-germ reading tying the transition to the g_Q-quotient for
L1b/L2e). Whether 3c-iv tolerates pair-local (or chart-local) dressing is a question
about the L1-GLUE'S STATEMENTS (G1-G3 + 3c-iv cuts), not about more lemmas.
NEXT SESSION = THE (N4) DESIGN SESSION: re-open the G1-G3/3c-iv design (/develop-style,
source-faithful to the U5 cut + KMPairing's D4) and decide: (a) glue consumes the
PAIR-local-dressed transition (germ-reading absorbs W-local units into the L1b-matching
per-overlap — check whether L2e's hsplit + the tau-relation are per-overlap statements
— they ARE (i j fixed)!  strong hint the pair-local dressing suffices); or (b) the
chart-local form is required ⟹ resume the transport-block (H3-S layer-route). Under
(a): [C-rest-3] completes with N-TRANSITION + N3 + cocycle + [SK-W2']-bridge + the
rfip-cancel — ALL LANDED — only the packaging statement remains. STRONG DEFAULT: (a).

[N4-PREREAD CONFIRMED] (2026-08-16, cont.11): L2e (functionFieldMap_translateByPoint_germ,
read in full) consumes ONLY hnorm + (h, hn, hsplit) — NO transition-VALUE appears in its
hypotheses or conclusion (the value-side is torsionSplittingEval, produced by the engine).
⟹ the u2*u1^-1-value's ONLY consumer is the not-yet-stated 3c-iv/L1a germ-identification
(tying h's germs to the g_Q-quotients for the U5 comparison). The N4-design therefore has
ONE degree of freedom: state 3c-iv around the dressed transition. Design options (pick at
the session): (i) state 3c-iv for the MIDDLE term only (germ of the native-vs-native
transition = g-quotient germ — from N-TRANSITION directly) and thread the outer
transitions as h-corrections through D4's h-family (h is EXISTENTIAL in L2e — replace
h_i by h_i * [N]^#-lift of the outer-unit-data where the outer units' [N]-pullbacks
split trivially since they are... CHECK); or (ii) state 3c-iv for the full dressed value
with the A-ratio explicit. Either way NO new transport mathematics — only statement-
placement. The parked transport-sorries (H3-T1, H3-S, [SK-per-chart]-as-stated) can be
DELETED at the design session if (i)/(ii) confirm.

★ [N4 ADJUDICATED — PAIR-LOCAL SUFFICES, DIV-INVARIANCE] (2026-08-16, cont.12): the
3c-iv/L1a consumption is DIVISOR-level (the L1 dictionary runs on div-statements:
div G = div g_Q => G = c g_Q), and UNITS HAVE ZERO DIVISOR on their domain — so ANY
unit-dressing (pair-local included) drops out of the div-reading. The tau-ratio side is
value-free (L2e preread). ⟹ the packaging theorem is the EXISTENTIAL form:
  ∃ a b : Γ(W_i ⊓ W_j)ˣ, transitionUnitOfCover M W e i j = a * (u₂·u₁⁻¹-unit) * b⁻¹
proven by the cocycle law ×2 with the native-middle insertion (a := transition(res-e_i,
tW-over-i), b := transition(res-e_j, tW-over-j)) + the middle = N-TRANSITION through
the overTriv-bridge ([SK-W2'] + the rfip-cancel, both landed). CONSEQUENCE: the three
transport-sorries (H3-T1, H3-S, [SK-per-chart]-as-stated incl. its H2-plug scaffold)
are DELETED — FieldLeaf returns to zero sorries. KEPT (proven, useful): H2
(restrictTrivialization_inv_app_top_one), tau + tau-nat, [SK-normal], the full N-cluster,
N3, and the entire earlier battery. 3c-iv will be stated div-level against the
existential packaging.

★★★ [C-rest-3] CLOSED (2026-08-17): `transitionUnitOfCover_eq_dressed_native` PROVEN
AXIOM-CLEAN — for ANY chart trivialisation family of M (with M ⊗ I₁ ≅ I₂ and
unit-related generator data at the overlap), the transition unit is
a * (u₂ · u₁⁻¹) * b⁻¹ with overlap-units a, b. Proof = the native-middle cocycle
insertion: cocycle law ×2 + symm-inverse + the mid through PACKAGE-mid (the abstract
unit-level W2'-bridge) + PACKAGE-cancel (abstract rIso-conjugation-drop) +
N-TRANSITION. WHNF-LESSON (reusable): when instantiating at large composite terms,
HOIST every rewrite-bearing step into an ABSTRACT micro-lemma (small binders) and
instantiate by term-application — refine/simp at big terms whnf-storm even for
trivial content. 3c-iii IS NOW FULLY COMPLETE (ideal-leg crown + M-chain package),
FieldLeaf sorry-free. NEXT BOXES: 3c-iv stated DIV-LEVEL against the dressed form
(div germ(transition) = div germ(u₂u₁⁻¹) — the a/b-units drop); then the L1-glue
G1-G3 (dataset + normalisation-replay + L2e-instantiation), L3, L5, L6, U-assembly,
E5-assembly.

[3c-iv SCOPING NOTE] (2026-08-17): the div-level 3c-iv consumes: (i) the dressed
package (landed); (ii) [DIV-UNIT] ord_P of the FF-germ of an overlap-UNIT is 0 for
P in the overlap — the RP-chain's vocabulary: a unit of Γ(X,W) maps to a unit of the
local ring at P ∈ W ⟹ not in the maximal ideal ⟹ the RP-5-atom species
(ord_P_algebraMap_eq_zero_of_notMem, ValuationTransport — landed) applies through the
germ-to-FF plumbing; (iii) the generator-quotient germ-reading (u₂u₁⁻¹ = (f₂ⁱ/f₂ʲ)·
(f₁ⁱ/f₁ʲ)⁻¹-germs — from the span/Associated-data at the overlap, the 3c-i unit's
DEFINITION). The 3c-iv STATEMENT belongs inside the G1-glue design (needs the curve-
level dataset context: germToFunctionField, the W-cover from
exists_affine_common_principal, the J₁/J₂ = pole-sheaf ideals with their generator
divisors). NEXT SESSION = the G1 design+skeleton: write the dataset-statement
(cover, e-family via pullbackTrivOfTensorIdeal at the affine charts, hnorm via the
G2-replay with tracked rescalers — the a/b-dressing folds into the SAME rescaler
bookkeeping), then 3c-iv div-statement, then G3 = L2e-instantiation.

★★ [G1-TRANSITION] PROVEN AXIOM-CLEAN (2026-08-17, cont.): exists_transition_dressed_
of_charts — given two common-principal charts (span/nzd/mem data at affine Vi Vj matching
the cover-opens) and a nonempty overlap, the e-family's transitionUnitOfCover is
a * (u2*u1^-1) * b^-1 with hu-relations tying u1 u2 to the restricted generator ratios.
Proof-recipe (reusable): affine overlap via Vi.2.inf Vj.2 (separatedness-surrogate
[IsAffineHom (pullback.diagonal (terminal.from X))]); span-transfer via J.map_ideal +
Ideal.map_span (the file's own hs-pattern); nzd-transfer via @map_injective_of_isIntegral
(@-form with the Nonempty positional — mirror the file); mem-transfer via
idealSections_map; units via Ideal.span_singleton_eq_span_singleton -> Associated;
IsIso-genHoms RE-DERIVED at the affine overlap by isIso_idealGenHom_of_principal (NO
restriction-coherence needed); hmono via B2r with the per-Z family (nonempty: open-
subscheme integrality isIntegral_of_isOpenImmersion + component_integral + the
eqToHom-roundtrip openTop-injectivity (hcomp := Subsingleton-arrow + map_id, then the
ι_appIso-REWRITE FIRST since appIso=refl is a THEOREM not defeq, then congrArg-cast);
empty: Z = bot by ext + Subsingleton Γ(-, bot) instance + the mem_nonZeroDivisors_iff
CONJUNCTION-shape). REMAINING GLUE: [G1-dataset] the cover+e-family existence-packaging
(choice over exists_affine_common_principal; e_k := overTriv(rIso(pbTrivOfTensorIdeal))
at charts; iSup = top); [G2/hnorm] the zero-section normalisation replay (curve-level);
[3c-iv] div-level germ-reading (DIV-UNIT via RP-5 + the u-relations from G1-transition);
then G3 = L2e-instantiation, L3, L5, L6, U-assembly, E5-assembly.

★ [G1 COMPLETE] (2026-08-17, cont.2): exists_chart_family PROVEN (the chart-data
existence: choose over exists_affine_common_principal at W := top; hfmem via
ker_subschemeι_app + mem_span_singleton_self — the isInvertible_idealModule template).
G1 = dataset + dressed-transition both axiom-clean. The e-family at consumers:
efam c := overTrivializationOfRestrictIso M (V c).1 (restrictIsoOfPullbackIso
(pullbackTrivOfTensorIdeal M J1 J2 e (V c) (f1 c) (f2 c) ...)) — definitional on the
data. REMAINING GLUE: [G2/hnorm] zero-section normalisation (curve-level: the kappa-
dataset's exists_normalized_dataset replay — needs the CURVE context (E, mulByN,
baseChangeZero) — lives beside KMDataset/KMPairing consumers); [3c-iv] div-level
germ-reading; [G3] L2e-instantiation. Then L3, L5, L6, U-assembly, E5-assembly.

[G2 DESIGN — REPLAY WITH THE CHART-FAMILY] (2026-08-17, cont.3): exists_normalized_
dataset (KMDataset:220-read) takes an ARBITRARY family (Nonempty-choice via
exists_over_trivialization_of_isInvertible) and normalises by: (a) the d-rescale from
exists_transitionUnit_eq_mul_inv_of_picMap_eq_one (zero-section splitting), (b) the
two-family SUM-cover refinement (W0 i ⊓ snd⁻¹(z⁻¹ W0 i)) ⊕ (W0 i ⊓ Zc). KEY
STABILITY INSIGHT: the dressed-generator transition-form is CLOSED under both
operations — refinement restricts the generator-data (map_ideal-transfer keeps the
span/nzd/mem-relations on sub-overlaps) and unit-rescaling multiplies the a/b-dressing.
[G2-package] therefore = an exists_normalized_dataset-VARIANT with e0 := the G1-chart-
family as INPUT (replacing the choice), concluding hnorm ∧ dressed-generator-transitions
on the refined overlaps. Execution = replay KMDataset's construction (~200 lines,
curve-level context E/mulByN/baseChangeZero) tracking the transition-formula through
(a)+(b) — its own session with KMDataset.lean open; the FieldLeaf-side stability
micro-lemmas (restriction of the dressed form; rescale of the dressed form) can be
proven X-generic FIRST: [G2-s1] dressed-transition of a RESCALED family (e'_k :=
e_k ≪≫ scalar-unit-auto) = same-dressed (a/b absorb); [G2-s2] dressed-transition
restricted to a sub-overlap = dressed with res-generators (map_ideal + N3-restriction).
THEN 3c-iv (div-germ), G3 (L2e-instantiation at the G2-output).

[G2 TOOLKIT COMPLETE] (2026-08-17, cont.4): BOTH stability species already exist —
[G2-s1] = trivializationTransitionUnit_trans_scalarIso (KMDataset:95, the engine's own:
transition(rescaled) = transition * ca^-1 * cb) and restriction-side = my N3 +
restrictOverTrivialization_trans_scalarIso (KMDataset:78, restriction-of-rescale =
rescale-of-restriction). The G2-REPLAY (exists_normalized_dataset-variant with the
G1-chart-family as input, concluding hnorm AND dressed-generator transitions on the
refined sum-cover) is now pure assembly at the KMDataset-level (curve context) — its
transition-computation on the inl-inl case is ALREADY in the construction (KMDataset:397
uses s1!); the replay adds: the dressed-input-hypothesis threaded through, with
map_ideal-restriction of the generator data to the refined overlaps (the G1-transition
recipe applied at the SUM-cover overlaps, which sit inside chart-overlaps). NEXT
QUANTUM: write exists_normalized_chart_dataset in KMDataset.lean (or a new
KMChartDataset.lean importing FieldLeaf pieces — CAREFUL: import direction! FieldLeaf
imports KMBilinear imports KMDataset ⟹ the replay-variant must live in FieldLeAF or
later — put it in FieldLeaf's Curve-context section or a new GlueDataset.lean importing
FieldLeaf) with the full conclusion; then 3c-iv, G3.

[G2-STATEMENT LANDED] (2026-08-17, cont.5): exists_normalized_chart_dataset elaborates
(GlueDataset.lean, sorried). GOTCHAS for the file: BOTH scoped Gamma-notations (scheme
Scheme.lean:103 + modules Modules/Sheaf.lean:92) live in the AlgebraicGeometry scope —
at EXPRESSION-schemes (pullback E.π t) the overload stalls => spell sections explicitly
as ↑((….pullback E.π t).presheaf.obj (Opposite.op U)); WITHOUT the Modules-open,
qualify Scheme.Modules.idealModule / Scheme.Modules.baseChangeZero and use M.tensorObj
dot-form; pullback needs CategoryTheory.Limits-qualification anyway. PROOF-PLAN (the
replay): copy exists_normalized_dataset's body (KMDataset:220+) with (V,f-data) :=
exists_chart_family-choice, e0 c := overTrivializationOfRestrictIso ∘
restrictIsoOfPullbackIso ∘ pullbackTrivOfTensorIdeal at (V c); the sum-cover + cZ-
rescale verbatim; hnorm-cases verbatim; the NEW dressed-conclusion per case from
hAB-formula (transition-of-restricted = resUnit of chart-transition) + s1 (KMDataset:95)
+ exists_transition_dressed_of_charts + Units.map-multiplicativity + N3; indices c d :=
the cover-points of the two summands, hWc/hWd := inf_le_left-chains.

★★★ [G2 COMPLETE — AXIOM-CLEAN] (2026-08-17, cont.6): exists_normalized_chart_dataset
FULLY PROVEN (GlueDataset.lean, zero sorries): chart data (V, f1, f2, spans, nzds) +
sum-cover normalized dataset + hnorm + DRESSED transitions with generator-tied units on
every inhabited overlap. Proof = the KMDataset normalisation replayed with the G1
chart family + the general transitionUnit_restrict_rescale formula (proven first-shot:
trans_scalarIso ×2 + s1 + comp_eq ×2 + transitionUnit_restrict) + the four case-variants
(unrescaled legs masked by e = e ≪≫ scalarIso-1 via overUnitScalarIso_one +
Iso.trans_refl). BATTLE-LESSONS: (i) ac_rfl sorts atoms SYNTACTICALLY — defeq-but-
differently-spelled proof-subterms break it; instead REORDER the existential WITNESSES
so only associativity separates the sides and close with assoc-only simp; (ii) align
witness spellings to the formula-side (spelled-out opens, not set-variables);
(iii) KMDataset's open-list continues on a second line (Modules-open present);
(iv) private upstream lemmas (sectionEval_id, mul_inv_mul_inv_cancel,
sections_subsingleton_of_le_bot) inline-copied. GLUE STATUS: G1 ✓ G2 ✓. NEXT: [3c-iv]
the div-level germ-reading of the dressed transitions (DIV-UNIT species via RP-5 +
the u-relations = generator-quotient germs) and [G3] the L2e-instantiation at the
G2-dataset (hsplit via AP-D4's exists_transitionUnit_eq_mul_inv_of_mem_torsionPoints
at the normalized family); then L3, L5, L6, U-assembly, E5-assembly.

[G3 ADJUDICATED — ASSEMBLY-ONLY] (2026-08-17, cont.7): the FULL D4-pipeline exists:
exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints (KMUniqueness:264)
consumes EXACTLY the G2-dataset shape (N Q hQ M hM W hW e hnorm) and produces
(h, hn, hsplit) — L2e's complete hypothesis-set. G3 = apply it at the G2-output and
feed L2e; no new lemmas. REMAINING STRUCTURAL INPUT [KAPPA-DICT]: kappa(Q) =
[O(Q-0)] via sectionToPicRel (SelfAdjointN:198); the G2-theorem needs a representative
M with e_dict : M ⊗ idealModule J₁ ≅ idealModule J₂ (J's = the pole-ideals of [Q] and
[0]-ish) + the common-principal covers h₁ h₂ (from the curve's smoothness/Cartier —
the pole-divisors are official-Cartier: IsOfficialCartier/locallyPrincipal in
IdealModule.lean's isInvertible route!). Route: mine sectionToPicRel/PoleSheaf for the
concrete quotient-representative; the dict transfers along ≅ by tensorObjCongr. Then
instantiate exists_normalized_chart_dataset at it. NEXT BOXES (order): [KAPPA-DICT]
(PoleSheaf-mining, E4a-side); [3c-iv + L1a] joint design (the dressed-transition
germ-divisor vs g_Q-quotients feeding exists_const_mul_of_projectiveDivisorOf_eq);
[L3] scalar-match; [L5] diagonal; [L6] descent; [U-assembly]; [E5-assembly].

[KAPPA-DICT RECON] (2026-08-17, cont.8): sectionToPicRel (DivisorClass:180) =
picRelProj of (sectionDivisor P).picClass * ((sectionDivisor zero).picClass)^-1 —
the class of I(D_P)-vs-I(D_0) with the kernel-model projection (picRelProj multiplies
by a base-pullback correction). The DICT-target (M ⊗ idealModule J₁ ≅ idealModule J₂
with hM : kappa-val = toSkeleton M) therefore needs: (i) the RelEffCartierDiv →
IdealSheafData bridge (sectionDivisor's underlying ideal — RelEffCartierDiv's fields;
its picClass presumably = toSkeleton of the idealModule — READ RelEffCartierDiv +
picClass defs); (ii) the picRelProj-correction handled — KEY SIMPLIFICATION HYPOTHESIS:
at the U5-instantiation the base is a FIELD (T = S = Spec k, t = 𝟙 S) where the
correction class is trivial/absorbable — CHECK picRelProj's def and whether the
kernel-model at t = 𝟙 collapses; (iii) skeleton-transfer: from the CLASS-equation
kappa = [I_Q]*[I_0]^-1*[corr] produce the MODULE-level e_dict by toSkeleton-injectivity
-on-classes (Skeleton-API: toSkeleton_eq_toSkeleton_iff — USED at DivisorClass:160!
nonempty-iso from class-equality ✓ the mechanism exists) applied to M := the
skeleton-representative (exists_module_kappa's M) tensored with I(D_Q): the class of
M ⊗ I_Q = kappa*[I_Q] = [I_0]*[corr] ⟹ nonempty-iso M ⊗ I_Q ≅ I_0 ⊗ corr — with corr
trivial: THE DICT ✓. (iv) the common-principal covers h₁ h₂: sectionDivisor is
OFFICIAL-Cartier (sectionDivisor_isOfficial ✓ exists!) — IsOfficialCartier carries
locallyPrincipal ⟹ h-shape directly (grep IsOfficialCartier's fields). NEXT STRETCH:
read RelEffCartierDiv/picClass/picRelProj/IsOfficialCartier defs; adjudicate the
field-case correction; state kappa_dict (∃ M hM J₁ J₂ e_dict h₁ h₂) and prove by the
class-to-iso mechanism. Then G2-instantiate, D4-pipe, L2e — and the τ-side of U5 is
fully fed.

[KAPPA-DICT DESIGN COMPLETE] (2026-08-17, cont.9): picRelProj x = x * (snd^* z^* x)^-1
(RelativePic:81) — the correction is the snd-pullback of the z-restriction class; over
Pic-trivial T (Spec k!) it vanishes and kappa-val = [I(D_Q)]^-1 * [I(D_0)] on the nose.
IsOfficialCartier.locallyPrincipal is LITERALLY the h₁/h₂ hypothesis-shape (the covers
are free from sectionDivisor_isOfficial ×2). picClass D h := (isUnit_toSkeleton of the
invertible ideal-module).unit^-1. THE KAPPA_DICT THEOREM (state at Pic-T-trivial or
with the correction-triviality hypothesis, discharged at the field):
  ∃ M hM, ∃ e_dict : M ⊗ idealModule (sectionDivisor Q').ideal ≅
    idealModule (sectionDivisor zero).ideal — PROOF: M := exists_module_kappa's;
  class-chase toSkeleton(M ⊗ I_Q) = kappa * [I_Q-class] [toSkeleton_tensorObj]
  = proj([I_Q]^-1[I_0]) * [I_Q] = [I_0] [correction-trivial + group-algebra]
  = toSkeleton(I_0-module) ⟹ toSkeleton_eq_toSkeleton_iff ⟹ Nonempty-iso ⟹ choice.
  (Unit-vs-Pic-element plumbing: picClass lives via IsUnit.unit — mind the coe-layer;
  DivisorClass:160's own hmain-block is the template for exactly this manipulation.)
Then: exists_normalized_chart_dataset at (M, e_dict, officiality-covers) + the
D4-pipeline + L2e = THE COMPLETE τ-SIDE. Remaining U5 after that: 3c-iv/L1a joint
design (div-germ vs g_Q), L3, L5, L6, U-assembly, E5-assembly.

★★ [KAPPA-DICT PROVEN] (2026-08-17, cont.10): exists_kappa_dict axiom-clean
(GlueDataset sorry-free): over hPicT : ∀ y : Scheme.Pic T, y = 1, any skeleton-
representative M of kappa(Q) has Nonempty (M ⊗ I(D_Q) ≅ I(D_0)). Mechanics: the
picRelProj-correction dies by hPicT + map_one; the units-equation kappa * uQ = u0
(mul_comm + inv_mul_cancel), val-ed and unit_spec-ed; the tensorObj-vs-monoidal bridge
by nonempty_tensorObj_iso_tensor + toSkeleton_eq_toSkeleton_iff; toSkeleton_tensorObj's
direction is mul = tensor (use PLAIN not .symm for tensor-to-mul calc-steps). GOTCHA:
Pic-vs-Skeletonˣ HMul stalls on dot-Pic spelling — wrap unit-terms with
`show Scheme.Pic … from` in mixed equations. τ-SIDE PIPELINE NOW STRUCTURALLY
COMPLETE: exists_kappa_dict → (officiality's locallyPrincipal = the h₁ h₂ covers,
DIRECT) → exists_normalized_chart_dataset → KMUniqueness:264 D4-pipe → L2e. NEXT:
the [3c-iv/L1a] joint design (div-germ of the dressed transitions vs the g_Q-quotient
divisors — the OTHER side of U5's comparison), then L3, L5, L6, U-assembly, E5.

[RECONCILIATION + CONVERGENCE] (2026-08-17, cont.11): my GlueDataset exists_kappa_dict
was a DUPLICATE of the session-5 landing nonempty_tensorObj_sectionIdeal_iso_zeroIdeal_
of_field (FieldLeaf:472; sectionDivisor.ideal = Hom.ker DEFINITIONALLY) — deleted; the
field-Pic-brick (subsingleton_pic_of_subsingleton_space) and kappa_eq_sectionCls_mul_
inv_zeroCls_of_field ALSO landed then. THE CONVERGENCE: the doc's own L1a-notes
(2026-08-11) list "transition-match F_ij = r_j/r_i — where the work is" — THIS IS
EXACTLY WHAT G2 DELIVERED (the dressed transition with u₂u₁⁻¹ = the f₂/f₁-generator-
ratio, r_i := the D-difference equations f₂ⁱ/f₁ⁱ-quotients). CORRECTED L1a-STATUS:
dictionary ✓, 3a ✓, 3b ✓, 3c-i/ii/iii ✓ (G2!), REMAINING: [3c-iv] the FF-germ reading
(germToFunctionField of the dressed transition vs the generator-quotient germs; unit-
dressing dies at div-level), [r-FAMILY] r_i := f₂ⁱ/f₁ⁱ as FF-elements + [G-GLUE]
G_i := h_i · [N]^#r_i gluing (div G = [N]^*D), [DIV-PIN] div r_i = ((Q)-(0))|_{W_i}
(the RP/ValuationTransport layer: divisorOf_algebraMap_eq_single + the ord-machinery
— LANDED as the RP-chain!), then L1b ✓ (landed) closes L1. The remaining-work map for
U5 is now: 3c-iv + r-family/G-glue/div-pin (L1a-tail) → L3 → L5 → L6 → U-assembly →
E5-assembly, with the τ-side pipeline fully proven.

★ [3c-iv-a PROVEN] (2026-08-17, cont.12): germToFunctionField_transition_dressed
(GlueDataset) — the germ-equation in DIVISION-FREE mul-form
t·b·f₁ᶜ·f₂ᵈ = a·f₂ᶜ·f₁ᵈ (at germs), proven by: units-massage t·b·u₁ = a·u₂
(rw heq + `group`), congrArg-germ + map_mul, the germ-res collapse idiom
(TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) (genericPoint X) _ _ —
FieldLeaf:166's own), and `linear_combination (f₁d-germ * f₂d-germ) * hC`.
Instance-note: germToFunctionField needs [Nonempty U]-BARE spelling (the Opens-coe-sort).
L1a-TAIL REMAINING: [DIV-PIN] div-germ of the chart generators = the section-divisor
restricted (the RP/ValuationTransport reading at the curve's closed points — connect
divisorOf_algebraMap_eq_single + the span-data to (Q)-(0)); [r/G-GLUE] r_c-family +
G_c := germ(h_c)·[N]^#r_c overlap-agreement (hsplit + 3c-iv-a + the FF-cocycle
cancellation); then L1-assembly (H = a·g_Q·[N]^#(r⁻¹)-form) via L1b (landed). These
consume the HasseWeil-side dictionary (weilFunction_divisor, the T-C4 valuation-layer)
— the next design+build block, at the CURVE over k-bar (Q5).
