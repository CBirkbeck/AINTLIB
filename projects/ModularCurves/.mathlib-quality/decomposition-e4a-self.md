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
