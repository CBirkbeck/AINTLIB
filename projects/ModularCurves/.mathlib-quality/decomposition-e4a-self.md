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

[DIV-PIN RECON COMPLETE] (2026-08-17, cont.13): the ker-vs-point-ideal dictionary
EXISTS — ker_eq_XYIdeal (TheoremOfSquareField:782, from the square-field work: the
kernel of an affine-coordinate-ring evaluation IS XYIdeal) + ker_affineChartHom
(quotientXYIdealEquiv-based). THE DIV-PIN CHAIN (all pieces landed): the section's
ker-ideal span-generator f at a chart —[ker_eq_XYIdeal]— XYIdeal(point) =
SmoothPlaneCurve.maximalIdealAt —[RP-4 uniformizer_of_span_maximalIdealAt +
RP-5 ord_P_algebraMap_eq_zero_of_notMem + divisorOf_algebraMap_eq_single,
ValuationTransport]— divisorOf(FF-image f) = Finsupp.single point 1. The germ-transport
scheme-FF ↔ model-FF via the comparison bridge (T-W7.1b landed). DIV-PIN's statement:
at the zChart with the section-point affine, divisorOf(model-FF-image of the ker-span
generator) = single(section-point) 1; assemble from the named pieces; then div r_c =
div(f₂-germ) - div(f₁-germ) = single(0-pt) - single(Q-pt) per chart ✓ = ((Q)-(0))-
restricted with the L1-orientation (r = f₂/f₁ = 0-over-Q equations — CHECK the sign
convention against weilFunction_divisor at assembly). NEXT BUILD: state div_pin at the
zChart (ValuationTransport-context), prove from the chain; then r/G-glue statements;
then the L1-assembly (H = a·g_Q·[N]^#(r⁻¹)) via L1b; then L3/L5/L6/U/E5.

[DIV-PIN FORM RESOLVED — ORD-WISE LOCAL] (2026-08-17, cont.14): the infinity-question
dissolves by stating DIV-PIN ORD-WISE AT CHART-POINTS (the doc's own "div r_i = (Q)−(O)
on W_i" — LOCAL): for a point P IN the chart-open, ord_P(FF-image of the ker-span
generator f) = (if P = section-point then 1 else 0) — no global divisorOf, no ∞ (∞ is
not in the affine chart; the global div-G computation is pointwise via the cover).
Statement lives in ValuationTransport-context (ord_P-vocabulary); proof = ker_eq_XYIdeal
+ RP-4 (at P = the point) + RP-5 (P ≠ the point: f ∉ maximalIdealAt-P since f spans
ker-Q-ideal and P ∉ V(ker-Q) — the membership-argument via the span + P-in-chart-minus-Q)
— all landed pieces. Then ord_P(r_c) = [P = 0pt] - [P = Qpt] per chart; div-G pointwise;
L1b consumes. This is the next build-block, followed by r/G-glue, L1-assembly, L3, L5,
L6, U-assembly, E5-assembly — the full remaining U5-path, every step with named tools.

★ [DIV-PIN PROVEN] (2026-08-17, cont.15): divisorOf_algebraMap_eq_single_of_span +
eq_of_maximalIdealAt_le (ValuationTransport) — the span of the maximal ideal at P₀
ALONE pins div(germ) = [P₀]: the away-nonmembership derived by maximal-containment
(IsMaximal.eq_of_le) + point-separation (constants-are-units kills nonzero
K-differences in a maximal ideal; XClass/YClass-difference identities via
sub_sub_sub_cancel_left + C_sub term-chains — C_sub takes NO explicit args). With
ker_eq_XYIdeal (= the chart-span-to-maximalIdealAt identification) the DIV-PIN chain
is COMPLETE: chart-ker-span ⟹ div(germ f) = [section-point] on the chart. L1a-TAIL
REMAINING: [r/G-GLUE] (r_c := germ f₂ᶜ/germ f₁ᶜ; G_c := germ(h_c)·[N]^#r_c;
overlap-agreement from germed-hsplit + 3c-iv-a; div G = [N]^*((Q)-(0)) pointwise from
DIV-PIN + brick6) and the [L1-ASSEMBLY] (H = a·g_Q·[N]^#(r⁻¹) via L1b + the model-FF
bridge). Then L3, L5, L6, U-assembly, E5-assembly.

[r/G-GLUE DESIGN RESOLVED — NO GLUING NEEDED] (2026-08-17, cont.16): the L1-target H
is the SINGLE germ at the generic chart (H := germ h_{c₀}) — G is never glued; the
overlap-relations enter the POINTWISE div-computation where the unit-dressing dies at
each ord. Cut: [G-REL] (scheme-side, buildable NOW): germ h_i · [N]♭(germ b) ·
[N]♭(germ f₁ᶜ) · [N]♭(germ f₂ᵈ) = germ h_j · [N]♭(germ a) · [N]♭(germ f₂ᶜ) ·
[N]♭(germ f₁ᵈ) — from hsplit germed through the L2c-reader (functionFieldMap_
germToFunctionField + germ_res, the FieldLeaf:148-block's own sub-lemmas) + [N]♭ of
3c-iv-a + field-algebra (division-free mul-form). [ORD-G] (the HW-side): for each
closed point P, ord_P(H·[N]♭r_{c₀}) computed by moving to a P-covering chart-d via
G-REL (dressing + h-units die: h_d is a UNIT-section on its open ∋ relevant points ⟹
germ-ord 0 — the DIV-UNIT reading; a/b likewise), then ord([N]♭ r_d) = the pullback-
ord = e_P · ord_{[N]P}(r_d) with DIV-PIN finishing. NEEDS RECON: the HW [N]-pullback-
ord transfer (brick6_intertwining + MulByIntUnramified's ord-machinery — how HW reads
ord of mulByInt_pullbackAlgHom-images; the e_P-ramification bookkeeping — HW's
weilFunction_divisor consumed exactly this, mine its proof). THEN the L1-assembly:
div(H·[N]♭r) = div(g_Q) [ORD-G vs weilFunction_divisor] ⟹ L1b ⟹ H = a·g_Q·[N]♭(r⁻¹).
NEXT STRETCH: build [G-REL] (statements+proof, all pieces landed), recon the HW
pullback-ord, state [ORD-G].

★ [G-REL PROVEN] (2026-08-17, cont.17): germ_split_transition_rel (GlueDataset,
axiom-clean) — germ(h_i)·τ♭(germ b·f₁ᶜ·f₂ᵈ) = germ(h_j)·τ♭(germ a·f₂ᶜ·f₁ᵈ) from
hsplit + the dressed data. Proof-recipe: inverse-free units-massage (map-t·hj = hi via
inv_mul_cancel_right), congrArg-germ + Units.coe_map/MonoidHom.coe_coe simp, the
functionFieldMap_germToFunctionField naturality, typed-have realignment of the
coe-spellings (ConcreteCategory-hom-application vs FunLike-↑ atoms differ for ring!),
goal-side map_mul split, and the SIGNED linear_combination (hj·hτ − τblock·hval' —
compute the combination by hand, the sign matters). SCHEME-SIDE L1a-TAIL COMPLETE.
REMAINING: [ORD-G] — the HW-side pointwise div-computation (mine HasseWeil's
weilFunction_divisor proof for the [N]-pullback-ord reading + the e_P-ramification;
consume G-REL + DIV-PIN + DIV-UNIT); then [L1-ASSEMBLY]; then L3/L5/L6/U/E5.

[ORD-G RECON COMPLETE — FULLY TOOLED] (2026-08-17, cont.18): the general FF-pullback-
divisor transfer EXISTS: projectiveDivisorOf_pullback_eq_pullbackDivisor
(DivisorPullback:244, under ProjOrdTransport φ — discharged for mulByInt in the
weilFunction_divisor pipeline) + weilFunction_divisor_eq_pullbackDivisor_kappaDivisor
(HfactLemma:133) gives the TARGET-side shape div g_Q = pullbackDivisor [N]
(kappaDivisor Q). ORD-G's statement: projectiveDivisorOf(H-HW · (mulByInt N).pullback
r-HW) = the same RHS — proof pointwise: affine places by the chart-hop (G-REL relates
the H-germ to h_d-germs modulo generator-germs; unit-ords die; DIV-PIN pins the
generator-ords; the [N]-transfer via ProjOrdTransport/pullbackDivisor_apply), the
∞-place via OrdAtInftyBridge; then L1b closes L1 (G/g_Q constant). REMAINING
STRUCTURAL LAYER (the last!): the SCHEME-FF ↔ HW-FF TRANSPORT of H and r — the
T-W7.1b comparison-bridge applied: (i) the scheme-K(curve) ≅ HW-FunctionField
identification (ComparisonCoefficients/Bridge/Injective — landed); (ii) germ-ord
compatibility across it (the zChart/RP-dictionary — ValuationTransport's purpose);
(iii) [N]♭-vs-mulByInt-pullback intertwining = brick6_intertwining (PROVEN). NEXT
SESSION: write the transport-statements (H-HW := bridge(H-germ), r-HW := bridge(r)),
state ORD-G, execute the pointwise proof; then L1-assembly, L3, L5, L6, U-assembly,
E5-assembly. THE END IS ENUMERABLE: every remaining box has named proven tools.

[ORD-G RE-CUT — THE DRESSING OBSTRUCTION + NATIVE FIX] (2026-08-17, cont.19): pricing
the pointwise proof exposed a REAL obstruction: G2's a/b-dressing units live on
OVERLAPS ONLY, but the ord-computation of G := H·[N]♭r at p over W i reads the germ
of a/b at points OUTSIDE W i ⊓ W c₀ — unpinned (a germ of an overlap-unit has
arbitrary ords beyond its domain). One-sided degree-0 tricks fail for the same
reason. THE FIX (two moves): (1) rebuild G2's e₀-family as the PURE NATIVE trivs
(e₀ᵢ := overTriv(restrictIso(nativeTensorIdealTriv at V i))) so THE PACKAGE-dressing
at e₀-level becomes a₀ = t(nat-Vᵢ|ovl, nat-ovl(res gᵢ)) — which is 1 GIVEN
[NAT-RESTRICT]; the only surviving dressing is the cZ-normalisation, which is
PER-CHART by construction: t_ij = res(cZᵢ)·(u₂u₁⁻¹)·res(cZⱼ)⁻¹ — every factor
chart-local ⟹ pointwise ords all computable (h_i unit ∋ p; cZ-res germ-ord 0 via
chart-locality; u-parts via DIV-PIN; [N]-transfer via the GLOBAL divisor identity
projectiveDivisorOf_pullback_eq_pullbackDivisor evaluated at p — no pointwise
e_p-lemmas needed). (2) [NAT-RESTRICT] proven via the ν-CHARACTERISATION (no
iso-chasing): [NR-1] ν-RES — the ν-composite is natural under open-restriction
(map-level congrArg-chains; tensor-slot piece = the one blur-risk); [NR-2] the
restricted native triv satisfies the W-level read-off (apply restrict-functor to the
V-level read-off + NR-1); [NR-3] ν mono (insert-g₁ nzd + e_dict iso + ideal-inclusion
mono) ⟹ trivialisations with equal read-off are equal ⟹ transition
t(restrictTriv(nat-V), nat-W(res g)) = 1. Overlap-nonemptiness for the hsplit
germ-read at (i, c₀): X integral ⟹ irreducible ⟹ nonempty opens meet ✓. ∞-place: the
zero-section IS the model-∞; J₂-charts cover it; OrdAtInftyBridge species on the HW
side (verify at execution). ORDER: [NR-0] recon ν/read-off/restrictTrivialization
defs → [NR-1..3] → [G2′ native rework] → transport statements (H-HW/r-HW via
projModelFunctionFieldEquiv ∘ fst-FF, germ-compat via zChartLocalizationEquiv_compat
— brick-3 CLOSED cont.19, symm+apply IsLocalization.map_eq) → [ORD-G pointwise] →
L1-assembly → L3/L5/L6/U/E5.

[NR EXECUTION STATE + THE 1b/SLOT CUT] (2026-08-17, cont.20): LANDED axiom-clean-modulo-
NR-1: unit_hom_ext (from-unit maps determined at ⊤-1 via SheafOfModules.unitHomEquiv +
sections_property), openTopSection_homOfLE (the res-square of openTopSection;
poset-Hom-subsingleton finish), restrictTransportSection def (H2's transport composite
as a def), [NR-1a] restrictTransportSection_naturality (4-square exact-defeq chain:
adjUnit-nat, presheaf-res-nat [.presheaf.map vs .val.map are DIFFERENT SPELLINGS —
typed-have realignment], pullbackComp-nat, pullbackCongr-nat; naturality_apply
orientation is phi-tgt(M-map) = N-map(phi-src)... i.e. h3 NOT h3.symm),
unitEndomorphismOfTopSection_app_top_one, [NR-2] (unit_hom_ext + H2 + NR-1 + V-level
N2-cancel-at-1 + OTS-RES), [NR-3] (read-off + endo(1)=id + iso-algebra). REMAINING =
NR-1 ONLY. Analysis (triple-checked, no cheaper route): the dressing-wall is real; BUT
G2-prime does NOT need NR-3/NAT-RESTRICT-EQ — the per-chart A_i := transition(e_i,
restrictOverTriv-of-overTriv(rIso(nat-V_i))) exists trivially; t_ij = res(A_i)·m_ij·
res(A_j)^-1 by trivializationTransitionUnit_restrict + _trans (LANDED); m_ij =
u₂u₁^-1 via [restrictOverTrivialization_comp + overTrivializationOfRestrictOpen-
Trivialization + SK-normal (ALL LANDED)] + PACKAGE-mid + read-off from TWO NR-2
instances (generator-change via nuPullback_mul). NR-1's cut: 1a-instances for
pb(e.hom)/pb(toUnitHom) FREE; [1b] unit-tail = pRT-(unitObjX) ≫ pullbackUnitIso-W.hom
= pbH.map(pullbackUnitIso-V.hom) ≫ pullbackUnitIso-homOfLE.hom (unit-cocycle over
W.ι = homOfLE ≫ V.ι; prove via unit_hom_ext-conjugation at concrete 1,
pullbackUnitIso_hom_unit_oneT species); [SLOT-SQ] pRT-M ≫ slotW.hom = pbH.map(slotV.hom)
≫ pRT-(M⊗I₁) — general-⊤-sections of sheafified tensors have NO element calculus
(sheafification!) ⟹ MUST go map-level via the sheafify-adjunction TRANSPOSITION
(sources are sh-images: Hom(sh A, B) ≃ presheaf-Hom) then tmul-induction — the ATOM
template at scale. Then NR-1 assembly at elements.

★ [STATEMENT-LAYER COMPLETE] (2026-08-17, cont.21): the ENTIRE remaining U5-endgame is
now TYPED as sorried statements with proven transport-infrastructure:
- OrdPipeline.lean (NEW): pullbackCurveFunctionFieldEquiv PROVEN axiom-clean (fst-iso
  FF-equiv via RingEquiv.ofRingHom + functionFieldMap_comp/congr/id, ≪≫
  projModelFunctionFieldEquiv; gotchas: instance-VARIABLES not auto-included unless
  syntactically mentioned → explicit [AlgebraicGeometry.IsIntegral (projModel W)]
  binder; .E-vs-projModel instance-forms need haveI-inferInstanceAs BOTH in the
  def-TYPE (haveI-in-type) and body; rw-motive fails on functionFieldMap-composites →
  functionFieldMap_congr chain instead; letI-in-hypothesis swallows next paren-group
  unless the app closes ON the letI-line → (Spec (.of K)) shortening).
  [L1] exists_const_mul_weilFunction STATEMENT: H_HW·[N]^*r = c·g_T with r
  EXISTENTIAL (tau-invariance holds for ANY [N]-pullback — kills the r-pinning);
  [TAU-INV] translateAlgEquivOfPoint_mulByInt_pullbackAlgHom STATEMENT;
  [VAL-TRANSPORT] pullbackCurveFunctionFieldEquiv_germ_globalTwist STATEMENT
  (globalTwist-germ ↦ algebraMap∘ΓSpecIso);
  [L3] torsionSplittingEval_eq_weilPairing STATEMENT (ΓSpecIso-image of the KM-value =
  weilPairing at the basePointCast-points; general (P',Q) for E5-reuse).
- GlueDataset: [G2'] exists_normalized_chart_dataset_perChart STATEMENT (per-chart A
  dressing + fixed ch-assignment).
- NativeRestriction: NR-battery landed (unit_hom_ext, OTS-RES, NR-1a, 1b
  pullbackRestrictTransport_unitIso via pullbackUnitIso_compLow/congrLow [UnitComp.lean
  GOLDMINE] + pullbackCongr_symm_app_inv [subst+rfl], NR-2, NR-3); ONLY NR-1 sorried.
REMAINING PROOF-MAP (priority order): (1) [SLOT-SQ] → NR-1 (the one hard brick;
sheafification-adjunction-injectivity + open-immersion-presheaf-shadow tmul-induction;
element-formula library at PullbackTensorGeneral:1433-1496); (2) [G2'-proof] (G2-body
rework: e-family vs restricted-natives via NR-2×2 + read-off + nuPullback_mul;
PACKAGE-mid; trivializationTransitionUnit_restrict + _trans); (3) [ORD-G/L1-proof]
(pointwise: G-REL germ-read at (i,c₀)-pairs [nonempty by irreducibility] + DIV-PIN +
DIV-UNIT + projectiveDivisorOf_pullback_eq_pullbackDivisor + OrdAtInftyBridge + L1b);
(4) [TAU-INV-proof] (IsLocalization.ringHom_ext to R-generators + tau-fixes-coordHom
via x∘[n]∘tau_S = x∘[n]; translateAlgEquivOfPoint = case-dispatch formula AlgEquiv,
TranslationOrd:3411; generic-point route via translateAlgEquivOfPoint_map_genericPoint
SeparableKernelTorsor:209 + genericPointAct); (5) [VAL-TRANSPORT-proof] (cast-chase;
germ-of-globalTwist through the two equivs); (6) [L3-proof] (eigen-value match:
L2e+L2f+L2g-transport + L1 + weilPairing_spec + TAU-INV + VAL-TRANSPORT + domain
cancellation); (7) L5 (diagonal: weilPairing_self import) + L6 + U-assembly +
E5-assembly. All consumers typed against these exact signatures.

★★ [L3 PROVEN + TAU-INV PROVEN] (2026-08-17, cont.22): torsionSplittingEval_eq_weilPairing
is PROVEN in OrdPipeline.lean (modulo the three consumed sorried statements L1/
VAL-TRANSPORT/EQUIV-TAU): the eigen-chain = L2e-at-c₀ → congrArg-equiv + map_mul →
EQUIV-TAU-rw → VAL-TRANSPORT-rw → obtain-L1 → translate-congrArg + map_mul + TAU-INV-rw
+ AlgEquiv.commutes + weilPairing_translate-rw → rw [h2] → the hkey-cancellation
(rw [← hfact] then linear_combination h7 − e-image·hfact — the e·hfact-coefficient is
REQUIRED; mul_right_cancel₀ + algebraMap-injective finish). TAU-INV proven via HW's
SHIPPED machinery: hxy_mulByInt + hcov_of_xy (TorsionGeometric) + Isogeny.mem_kernel_iff
+ mulByInt_apply + mulByInt_pullback_x/y (OmegaPullbackCoeff) + dif_neg-pullback-unfold +
x_gen/y_gen rfl-bridges to the algebraMap-spellings. IsDominant-τp discharged via
hτp_eq : τp = inv fst ≫ (tBP ≫ fst) (from translateByPoint_id_comp_fst +
IsIso.inv_hom_id_assoc) + infer_instance. GOTCHA: binder-position .functionField needs
instance-BINDERS ([IsIntegral (pullback ...)]), conclusion-haveIs don't reach binders.
REMAINING SORRIES (the complete list): NR-1/SLOT-SQ (NativeRestriction), G2′-proof
(GlueDataset), L1-proof = ORD-G-pointwise (OrdPipeline :122), VAL-TRANSPORT-proof
(:230, mechanical cast-chase: germ-of-globalTwist = appLE-germ → invfst♯∘snd♯ = π♯ →
zChart-collapse → ringEquivOfRingEquiv_eq → coordRingToZSection-of-constant),
EQUIV-TAU-proof (:256, L2f ∘ L2g composite — mostly mechanical given both landed).
THEN: L5 (diagonal weilPairing_self import at P' := Q), L6-descent, U-assembly
(weilPairingEval_self_of_field), E5-assembly.

★ [EQUIV-TAU + VAL-TRANSPORT + GERM-Z PROVEN] (2026-08-17, cont.23): EQUIV-TAU proven
(L2f∘L2g composite; hfg/hgf inverse-identities as functionFieldMap_congr-chains applied
at elements). VAL-TRANSPORT's assembly proven: h12 (globalTwist-germ =
germToFunctionField_restrict-collapse of the snd-app'd constant — globalTwist-val =
appLE-application is DEFEQ), h3 (functionFieldMap_germToFunctionField at inv-fst), h45
(collapse to the zChart + the π-vs-invfst≫snd app-identity: hπ from
pullback.condition.trans (comp_id) + IsIso.inv_hom_id_assoc; the appLE-fusion via
congrArg-(appLE-of-morphism)-of-hπ + Scheme.Hom.comp_appLE + rfl-tails), then the
trans-chain endgame (NO rw's on germ-spellings — coe-atoms differ; congrArg with a
CONCRETE hinner (h3.trans h45) instead of refine-holes). GERM-Z proven: simp only
[projModelFunctionFieldEquiv-unfold] + exact IsLocalization.ringEquivOfRingEquiv_eq _ t
(the germ-vs-algebraMap argument is DEFEQ via the toAlgebra-instance). REMAINING
SORRIES (full repo-wide list for the U5 endgame): (1) [CONST-SECTION]
coordRingToZSection_res_pi_app (OrdPipeline ~:262) — the K-scalar chase through the
SEALED coordRingToZSection = chartZRingEquiv.symm ≪≫ basicOpenIsoAway (ModelVariableChange
:970); route: find/derive the K-algebra-compat of chartZRingEquiv + basicOpenIsoAway +
the π-app-⊤-as-algebraMap identity (Proj-Γ-plumbing; the pointedIsoCoord-battlefield —
'rw on OPAQUE element never simp'); (2) [NR-1]/[SLOT-SQ] (NativeRestriction) — see
cont.20 route; (3) [G2′-proof] (GlueDataset) — see cont.20 route; (4) [L1-proof]
= ORD-G-pointwise (OrdPipeline :122) — see cont.18/19 route. EVERYTHING ELSE in the
L3-chain is PROVEN. After these four: L5 = L3 at P' := Q + HW weilPairing_self;
L6-descent; U-assembly (weilPairingEval_self_of_field needs the kappa-dict + G2′ +
D4-instantiation packaging to PRODUCE the dataset-hypotheses); E5-assembly.

★ [L5 PROVEN] (2026-08-17, cont.24): torsionSplittingEval_self_eq_one — L3 at
(P', pS, hxpS, hS) := (Q, p, hxp, hT) + HasseWeil.WeilPairing.weilPairing_self
(PairingProps:255). The field-leaf VALUE statement is done: the KM diagonal value is 1
under the dataset hypotheses. What weilPairingEval_self_of_field still needs on top:
(i) the dataset-PRODUCTION package (kappa-witness M via exists_module_kappa-species +
kappa-dict [FieldLeaf:472] + officiality-covers → G2′-instantiation → D4-pipeline
exists_normalized_transitionUnit_eq_mul_inv_of_mem_torsionPoints [KMUniqueness:264]
producing (h, hn, hsplit) → a c₀ with nonempty preimage-chart [irreducibility]);
(ii) the value-plumbing weilPairingEval_eq_torsionSplittingEval [FieldLeaf:2376 LANDED]
+ the ΓSpecIso-into-Γ(T,⊤)-units read (the register-value vs its ΓSpec-image — a
units-coe massage); (iii) the point-dictionary production (p, hxp, hT from x — the
L2g-vocabulary SpecPoints/projModelPointsEquiv/basePointCast + killedBy-transport);
(iv) the descent from arbitrary field to the model-curve presentation (the E ≅
modelEllipticCurve-of-its-Weierstrass-model transport — U1/U2-species — plus the
alg-closure descent Γ-injectivity per the U5-plan). Remaining sorries repo-wide: STILL
the 3 (SLOT-SQ, G2′, ORD-G).

[SLOT-SQ RECON — THE μ-LIBRARY DISCOVERY] (2026-08-17, cont.25): the tree contains a
COMPLETE μ-calculus layer the cont.20 plan did not account for:
- PoleSheaf:1940-2100: monoidalUnitObjIso (𝟙_ ≅ unitObj, DEFINITE — sheafifyValIso),
  monoidalTensorObjIso (M ⊗ N ≅ tensorObj M N, DEFINITE — the tensorObj-vs-⊗ bridge!!),
  tensorSection (pure-tensor sections of M ⊗ N), unitObjTensorIso + MonObj-structure.
- PoleSheaf:2606/2623: pullbackTensorTrivialization_eq_monoidal +
  pullbackComp_tensorTrivialization — a monoidal comparison α between composite
  pullbacks (with [α.hom.IsMonoidal] — SUPPLIED by pullbackComp_hom_isMonoidal,
  PullbackCompMonoidal:1264) PRESERVES canonical tensor-frames. THE Comp-leg tensor
  transport, landed.
- PullbackTensorSection.lean: the ELEMENT-FORMULA LIBRARY — pullback_μ_formula,
  pullback_μ_unit_tensorSection, composite_pullback_μ_tensorSection (μ of composite
  pullbacks on tensorSections, via δ_μ-cancellation + sheafification_map_pullback_δ
  species), restrictFunctorIsoPullback_hom/inv_unit_app_apply,
  restrictMonoidalTensorIso_* (restrict-side monoidal-tensor transport!),
  tensorSection_map_restrictIso, overTrivializationSection_tensor_one,
  pullback_monoidalTensorObjIso_inv_unit.
REVISED SLOT-SQ ROUTE: (1) bridge the slot's pieces to μ-vocabulary — the missing
bridges are tensorObjUnitIso-vs-(monoidalTensorObjIso + ρ/λ + monoidalUnitObjIso),
tensorObjCongr-vs-⊗ᵢ-conjugation (both plausibly one-line via monoidalTensorObjIso-
naturality monoidalTensorObjIso_inv_natural [PoleSheaf:5218] + SectionContraction's
monoidalTensorObjIso_comp_* lemmas), and pullbackTensorObjIsoOfIsOpenImmersion-vs-μIso
(BOTH are pb(M⊗N)-vs-pbM⊗pbN comparisons — compare via the tensorSection/adjUnit-image
elements + sheafification-adjunction-injectivity, the composite_pullback_μ_tensorSection
proof-pattern); (2) then SLOT-SQ = the μ-square from pullbackComp_hom_isMonoidal
(NatTrans.IsMonoidal) + pullbackCongr-subst + Functor.Monoidal unitor-coherences.
ALTERNATIVE (possibly cheaper): redefine the ν-characterisation vehicle at the
μ-vocabulary from the start and re-prove N2-cancel/read-off there — NO: N2/read-off
are landed at the tensorObj-spelling; bridge instead. START next quantum: grep
SectionContractionLocal:32/201 (monoidalTensorObjIso_comp_tensorUnitStructureIso /
_unitStructureTensorIso — likely EXACTLY the tensorObjUnitIso-bridge!).

[SLOT-SQ BRIDGE CONFIRMATIONS] (2026-08-17, cont.25b): tensorObjUnitIso M :=
sheafification.mapIso (ρ_ M.val) ≪≫ sheafifyValIso M (InvertibleSheaf:195) — EXACTLY
the RHS of monoidalTensorObjIso_comp_tensorUnitStructureIso (SectionContractionLocal:32,
private — REPROVE or de-private on consumption): so (tensorObjUnitIso M).hom =
(monoidalTensorObjIso M unitObj).inv ≫ ((refl ⊗ᵢ monoidalUnitObjIso.symm) ≪≫ ρ_).hom.
The unitor-piece of the slot bridges to ⊗-vocabulary essentially definitionally. The
congr-piece: monoidalTensorObjIso_inv_natural (PoleSheaf:5218, private) is the
naturality that conjugates tensorObjCongr into ⊗ᵢ. REMAINING GENUINE BRICK for the
μ-route: [μ-BRIDGE] pullbackTensorObjIsoOfIsOpenImmersion f M N vs (Functor.Monoidal.μIso
(pullback f) M N + monoidalTensorObjIso-legs) — both compare pb(M⊗-forms); prove via
sheafification-adjunction-injectivity on adjUnit/tensorSection-elements
(PullbackTensorSection's pullback_μ_unit_tensorSection + pullback_monoidalTensorObjIso_inv_unit
give BOTH sides' element-formulas — compare on unit-images, then hom-ext). Then
SLOT-SQ = unitor-bridge + congr-bridge + μ-BRIDGE + pullbackComp_hom_isMonoidal(μ-square)
+ pullbackCongr-subst + Functor.Monoidal coherences. NOTE: several needed lemmas are
`private` in PoleSheaf/SectionContractionLocal — copy-or-deprivatise as producer-legal
inline copies (the KMDataset-inlining precedent).

[mu-BRIDGE EXECUTION STATE] (2026-08-17, cont.26): pullbackTensorObjIsoOfIsOpenImmersion
_eq_mu is ~90% proven in NativeRestriction: the double-adjunction transposition entry
(pbAdj.homEquiv-injective + shAdj.homEquiv-injective — the tensorObj-source is accepted
as a sheafification-image DEFINITIONALLY), tmul-induction (zero: map_zero×2; add:
simp only [map_add, hs, ht] — rw-form STORMS there), the hcollapse-rfl (the double-unit
collapse is rfl; consume via refine (hcollapse _ _).trans (Eq.trans ?_ (hcollapse _ _
).symm) — rw does NOT match its spelling), THE RHS-CHAIN PROVEN (hR1 := adjUnit-
naturality congrArg at the sh-unit image [the private pullback_monoidalTensorObjIso_
inv_unit argument inlined]; hR2 := pullback_δ_unit_tensorSection [PUBLIC,
PullbackTensorSection:464]; hR3 := iso_inv_hom_app_applyT-fold of tensorSection-def;
hRHS assembled via an rfl-hsplit + rw-chain), THE LHS-WALK PROVEN (hL1 :=
restrictFunctorIsoPullback_inv_unit_app_apply [:531]; hL2 := sheafifyValIso_inv_app_
apply [PullbackTensorGeneral:1433]; hres := unit_app_app-rfl + naturality_apply.symm
[orientation: phi-tgt(M-map) = N-map(phi-src)] + tensorObj_map_tmul [typed-have
realignment — rw storms on the (𝟭.obj)-clothing]; hfwd/hL3 via NEW small-binder
micro-lemmas sheafificationMap_app_unit + iso_inv_app_of_hom_app + the IsIso-instance
from sheafificationW_pushforward_unit_tensor + sheafificationW_iff; hL4 same pattern;
hL4b := rfl at show-clothed PF-carriers [pushforwardTensorIso IS literal on tmuls];
hL5 via NEW micro-lemma tensorObjCongr_hom_app_unit_tmul [uses the project
tensorHom_app_tmul (T := Y.sheaf.obj)-named-args; the mathlib-erw-route storms] +
hfac-retypes at the show-spelling). REMAINING: the ASSEMBLY (chain hstep₄ + hL4b +
the PF-vs-restrict hcross + hL5 + a final composite-split-rfl into the goal): the
hL4b-congr/composed-instance elaborations WHNF-STORM on the pushforward-tensor-carrier
crossings (tried: pinned-domain congrArg, w := _ inference, a composed micro-lemma
sheafificationMap_app_unit_eq — all storm at the pfTI-typed-over-(T⋙forget₂)-clothing
vs Y.ringCatSheaf.obj-clothing unification). NEXT IDEAS: (a) hfinal-direct: prove
e5b-app(hstep₄-RHS) = target with the INNER at PRESHEAF-level only (⊗ₘ-pair-app(
pfTI.inv-app W3) = pbUnit-tmul via tensorHom_app_tmul + hfacs — no sheaf-crossings),
then final := split-rfl.trans (congrArg-e5b-of-hstep₄).trans hfinal; (b) restate
hL4b/pfTI-pieces at the (T ⋙ forget₂)-clothing throughout; (c) a clothing-crossing
rfl-have at the PRESHEAF-map-level g-position. All the landed micro-lemmas are
axiom-clean and reusable.

★★ [mu-BRIDGE PROVEN AXIOM-CLEAN] (2026-08-17, cont.27): pullbackTensorObjIsoOfIsOpen
Immersion_eq_mu COMPLETE. THE DECISIVE LESSON: the cont.26 "assembly storms" were NOT
per-step costs — heartbeats are PER-DECL CUMULATIVE; the walk's landed haves had eaten
the budget and every further step "stormed". FIX = extract the landed have-chains into
private lemmas (mu_bridge_rhs, mu_bridge_lhs_e4 [statement-level IsIso haveI needed for
its asIso-conclusion], mu_bridge_l4b, mu_bridge_l5) and re-run the IDENTICAL assembly
steps in the slimmed main decl — hstep₄' (the previously-storming hL4b-congr), the
hcross carrier-crossing rfl (previously storming!), hstep₅, and the final exact all
landed VERBATIM. NEW BATTLE-RULE: on (deterministic) whnf/isDefEq timeout in a
long proof, FIRST check the decl's cumulative weight — extract landed haves to private
lemmas before redesigning the step. NativeRestriction now has TWO sorries: [SLOT-SQ]
(:775) and [NR-1] (:792). SLOT-SQ's mu-route now has its key brick: slot re-expressed
via mu (tensorObjUnitIso/tensorObjCongr/mu-BRIDGE) + pullbackComp_hom_isMonoidal +
Congr-subst + Functor.Monoidal coherences. NR-1 then per cont.20 (1a-instances + 1b +
SLOT-SQ at elements via pullbackUnit_map_transportT + the [NR-unit-val] general-z
pullbackUnitIso-collapse [statement drafted, re-add from cont.26 scratch]).

[SLOT-SQ ENTRY + WALK-PLAN] (2026-08-17, cont.28): the double-transposition entry is
LANDED in-file (homEquiv-injective at homOfLE- and V.ι-pullback-adjunctions + hom_ext
chain to plain m : M.val.obj U — NO tensor in the source, no induction). The transposed
goal (printed): both sides = double-homEquiv images of (pRT-M ≫ slotW.hom) resp
(pbH.map(slotV.hom) ≫ pRT-⊗), .val.app U applied at m. NEXT-QUANTUM WALK: (1)
homEquiv_apply-unfolds + an hcollapse-style rfl reducing both sides to
composite.val.app-(op-preimage)-values at the double-unit image r₀(m); (2) LHS: pRT on
the double-unit image (the pullbackUnit_map_transportT/H2-species), then slotW's three
pieces at the W-unit image: tensorObjUnitIso.symm at elements (m ↦ m ⊗ₜ 1 — mathlib
rightUnitor_inv_apply species at the presheaf level + the ATOM-adjunction pattern),
tensorObjCongr(refl, genTrivW.symm) via tensorObjCongr_hom_app_unit_tmul (LANDED
micro-lemma!) with the genTriv.symm-at-1-value (pullbackIdealTrivOfGen.symm-elements —
the N1-hcore species: 1 ↦ the g-ideal-section), then pullbackTensorObjIsoOfIsOpen-
Immersion.symm — INVERT the mu-BRIDGE (NOW PROVEN!) or walk its .inv on unit-images
directly (its .symm-value on shUnit-tmuls follows from the mu-BRIDGE-equality +
mu/δ-element-formulas); (3) RHS: transportT at q := slotV.hom + the V-side same-shape
walk + pRT-⊗ on the resulting tensor-unit-image; (4) both sides meet at
shUnitW-((m-res) ⊗ₜ (res-g₁-section-form)) — the res-compat of the generator-elements
(map_tmul + idealSections-subtype-res). EXTRACT EVERY LANDED HAVE INTO A PRIVATE LEMMA
FROM THE START (per-decl-budget rule). After SLOT-SQ: NR-1 (1a×2 + 1b + SLOT-SQ at
elements + re-add [NR-unit-val] from cont.26), then G2', then ORD-G.

[SLOT-SQ WALK REFINEMENT] (2026-08-17, cont.28b): the 4x homEquiv_apply-unfold fires;
both sides become (unitV ≫ pushfwdV(unitH ≫ pushfwdH(SIDE))).val.app U m — collapse via
the hcollapse-∀-rfl pattern to SIDE.val.app-(op homOfLE⁻¹(V.ι⁻¹U'))-(r₀(m)) with r₀ :=
unitH-app(unitV-app m). WALK-PIECES (all tooled): [W-RHS-inner] pbH.map(slotV.hom) on
r₀ = pullbackMap_app_unit (LANDED cont.28b) giving unitH(slotV-app(unitV-m));
[W-slotV-elements] s1 unitor: tensorObjUnitIso.symm.hom = sheafifyValIso.inv ≫
sh.map(ρ⁻¹): sheafifyValIso_inv_app_apply + sheafificationMap_app_unit +
rightUnitor_inv_apply (w ↦ w ⊗ₜ 1); s2 congr-genTriv: tensorObjCongr_hom_app_unit_tmul
(LANDED) at (refl, genTrivV.symm) with genTriv.inv-at-1-value = idealGenHom-app(1) [the
g₁-subtype-section] pushed through rFIP via restrictFunctorIsoPullback_hom_unit_app_
apply-at-idealModule; s3 comparison: mu-BRIDGE.symm.hom = mTOI.inv ≫ μ ≫ pb.map(mTOI.
hom): mTOI.inv-app(shUnit-tmul) = tensorSection [def-rfl], pullback_μ_unit_
tensorSection, then pullbackMap_app_unit at mTOI.hom; [W-pRT-collapse] pRT-app(double-
unit-image) = unit-W.ι-image(m): [COMP-UNIT-micro, TO BUILD]: (pullbackComp f g).app-P
.hom.val.app on the two-step unit image = the (f ≫ g)-unit image — via the
Adjunction.homEquiv_leftAdjointUniq_hom_app template (the restrictFunctorIsoPullback_
hom_unit_app_apply :511-proof pattern; pullbackComp := leftAdjointUniq-species) —
then (pullbackCongr homOfLE_ι.symm).inv-app = subst-rfl re-index; [MEET] both sides at
shUnitW/unitW-images of (m-res ⊗ₜ res-g₁-section) — generator-res-compat via map_tmul +
idealSections-subtype-res. Estimated 8-12 more private micro-lemmas + the assembly;
EXTRACT-AS-YOU-GO per the per-decl-budget rule.

[COMP-UNIT RECON] (2026-08-17, cont.28c): mathlib's SheafOfModules.pullbackComp :=
Adjunction.leftAdjointCompIso (adj-φ) (adj-ψ) (adj-comp) (pushforwardComp φ ψ)
[PullbackContinuous:167] with @[simp] conjugateEquiv_pullbackComp_inv relating its
inv-conjugate to the adjunction-composition. The Scheme.Modules.pullbackComp is the
scheme-clothed wrapper. [COMP-UNIT]'s route: the leftAdjointCompIso unit-triangle
(hom-app on the two-step unit image = the composite-adjunction unit image, which by
Adjunction.comp-def IS unitG ≫ pushfwdG(unitF)-whiskered — so the lemma may reduce to
homEquiv/conjugate-algebra as in pullbackUnitIso_compLow's proof [UnitComp:321
template: adjc.homEquiv-injective + unitToPushforward-composition]) + then
(pullbackCongr (homOfLE_ι hWV).symm).inv on the composite-unit-image = the W.ι-unit
image by subst-rfl (pullbackCongr_symm_app_inv species, LANDED). NEXT QUANTUM: build
[COMP-UNIT] via the UnitComp:321-template, then execute the cont.28b walk
(s1/s2/s3-pieces as private lemmas), then the SLOT-SQ assembly, then NR-1.

[SLOT-SQ WALK PROGRESS] (2026-08-17, cont.29): LANDED AXIOM-CLEAN-modulo-nothing:
[COMP-UNIT] pullbackComp_hom_app_unit (unit_conjugateEquiv at (adj-direct, comp-adj,
Comp.hom) + the conjugate-identification hc := Equiv.apply_symm_apply — the def-layer
crossing (Scheme-wrapper → SheafOfModules.pullbackComp → leftAdjointCompIso →
leftAdjointCompNatTrans := (conjugateEquiv _).symm e.inv) is ACCEPTED at exact-defeq —
+ rfl glue-collapse of the pushforwardComp.inv-app on unit-images);
[pRT-COLLAPSE] pullbackRestrictTransport_app_unit — output deliberately stops at the
Congr-stage (Congr.inv-app of the composite-unit image): the W.ι-form needs the
PROPOSITIONAL homOfLE_ι-crossing, but BOTH slot-square sides end with pRT so the walk
meets at the Congr-stage symmetrically; [s1] tensorObjUnitIso_symm_hom_app (hsplit-rfl
+ sheafifyValIso_inv_app_apply-congrArg + sheafificationMap_app_unit + the presheaf-
rho-inv-at-q value is RFL: q ⊗ₜ 1). NEXT [s2]: the genTriv-at-1 factor:
idealGenHom-app-formula (IdealModule:240): g ↦ ⟨res-f · appIso-inv g, mem⟩; at 1 needs
mul_one + Subtype.ext to reach ⟨res-f, mem⟩; then align with restrictUnit-image
(unit_app_app-rfl res-map) — CAREFUL: the [511]-instantiation at U := image-V returns
the value at .op (Wo.ι⁻¹(image V)) ≠ .op V SYNTACTICALLY (preimage_image_eq is
propositional) ⟹ state [s2] with an H2-style eqToHom-clothing (hpre : V =
Wo.ι ⁻¹ᵁ (Wo.ι ''ᵁ V)) or at the preimage-spelling throughout. THEN [s3] (mu-BRIDGE.symm
+ mTOI.inv-def-rfl + pullback_μ_unit_tensorSection + pullbackMap_app_unit at mTOI.hom),
then the V-vs-W meet (res-g-compat via map_tmul + idealSections-subtype-res), then the
SLOT-SQ assembly (per-decl-budget discipline: consume the walk-lemmas by term-app).

[s2 STATE] (2026-08-17, cont.29b): pullbackIdealTrivOfGen_symm_hom_app_one — statement
landed (H2-style hpre eqToHom-clothing; conclusion = pbUnit-image of the res-g
idealSection under the re-index); hsplit-rfl + the hgen1-structure + the rFIP-hom
naturality (hnat) landed. TWO marked sorry-residuals: (a) the hgen1 subtype-collapse
(post mul_one: res-A-g = the ↑(restrict-map-eqToHom(restrictUnit-app(w')))-value — the
idealPresheafAb-map .1-layers [IdealModule:59-62 structure-literal] + unit_app_app
[.app-vs-.val.app spelling blocks the @[simp]] + eqToHom-res fusion — an LSP-session
def-transparency rfl-chase); (b) the [511]-splice under the eqToHom-res (coe-spelling
realignment of the restrictUnit-argument in the congrArg + final .val-vs-.presheaf rfl).
Both are plumbing, not math. NEXT: [s3] (mu-BRIDGE.symm value on shUnit-tmuls of
pbUnit-factors: mTOI.inv-def-rfl → tensorSection → pullback_μ_unit_tensorSection →
pullbackMap_app_unit at mTOI.hom), then the W-side mirror walk, then the meet + the
SLOT-SQ assembly.

[SLOT-SQ WALK: s3 LANDED] (2026-08-17, cont.29c): [s3]
pullbackTensorObjIsoOfIsOpenImmersion_symm_hom_app_unit PROVEN — the comparison's
inverse on shUnit-tmuls of pbUnit-factors = the pbUnit-image of the X-side tensor.
Recipe: hmu := congrArg-symm-hom-app of the mu-BRIDGE equality (single congrArg at the
full argument, NOT congrFun-of-congrArg); hv1-rfl (mTOI.inv on shUnit-tmul =
tensorSection, def-rfl); hv2 := the μ-direction derived from the PUBLIC
pullback_δ_unit_tensorSection + Functor.Monoidal.δ_μ (the private μ-lemma is
inaccessible — δ_μ-congrArg at the pbUnit-image then rw [hδ]); SPELLING: the
δ/μ-interacting positions MUST use MonoidalCategoryStruct.tensorObj (the instance-⊗),
NOT the ModularCurves tensorObj-def (namespace-resolution picks the wrong one and the
congrArg-domain mismatches); hv3 := pullbackMap_app_unit at mTOI.hom; hcancel :=
iso_inv_hom_app_applyT folding tensorSection; hcomp-rfl composite-split + rw-chain.
STATE: NativeRestriction sorries = 4: s2's two plumbing residuals, SLOT-SQ, NR-1.
NEXT: (a) close s2-residuals (LSP-ish def-transparency chases); (b) the SLOT-SQ
walk-assembly: LHS-side = pRT-collapse → [need the Congr-stage-carried versions of
s1/s2/s3 at the W-side (the pieces are stated at generic opens ✓ instantiate at the
Congr-clothed positions)]; RHS-side = pullbackMap_app_unit(slotV.hom) → s1/s2/s3 at
V-side → pRT-collapse-⊗; the MEET: both = Congr.inv-clothed pbUnit-images of
(res-m ⊗ₜ res-g-section) — generator-res-compat.

[SLOT-SQ TOOLKIT COMPLETE] (2026-08-17, cont.29d): [CONGR-UNIT]
pullbackCongr_app_inv_app_unit LANDED (subst h + rfl; the g-side argument enters via a
show-by-rw cast in the statement — elaborates cleanly). THE WALK TOOLKIT IS NOW
COMPLETE: pullbackMap_app_unit, pullbackComp_hom_app_unit [COMP-UNIT],
pullbackRestrictTransport_app_unit [pRT-COLLAPSE, Congr-stage], pullbackCongr_app_inv
_app_unit [CONGR-UNIT], tensorObjUnitIso_symm_hom_app [s1],
pullbackIdealTrivOfGen_symm_hom_app_one [s2, 2 plumbing residuals],
pullbackTensorObjIsoOfIsOpenImmersion_symm_hom_app_unit [s3], tensorObjCongr_hom_app_
unit_tmul, sheafificationMap_app_unit(_eq), iso_inv_app_of_hom_app — ALL axiom-clean
except s2's residuals. REMAINING FOR SLOT-SQ: THE ASSEMBLY — after the transposition-
entry (landed in-file): both sides at r₀(m) := unitH(unitV-m); LHS: pRT-COLLAPSE →
CONGR-UNIT (re-express the Congr-clothed comp-unit image as the W.ι-unit image cast) →
the W-walk (s1 at the unit-image; tensorObjCongr_hom_app_unit_tmul with the s2-b-factor;
s3 at f := W.ι) → cast-back; RHS: pullbackMap_app_unit(slotV.hom) → the V-walk (s1, s2,
s3 at f := V.ι) → unitH-of-that → pRT-COLLAPSE-⊗ (Congr-stage); MEET: CONGR-UNIT on the
RHS + the generator-res-compat (the s2-outputs' idealSections at res-paths — subsingleton
res-fusion on the .1's + Subtype.ext). Assemble per the per-decl-budget rule (each side's
chain as its own private lemma). Then NR-1 (1a×2 + 1b + SLOT-SQ-at-elements +
UNIT-VAL-readd), then G2', then ORD-G.

[AXIOM-CLEAN MANDATE + SLOT-WALK LANDED] (2026-08-17, cont.30): OWNER DIRECTIVE: "no
tracked sorries, it needs to be axiom clean" — yRho_representable must reach the
standard three axioms. THE DEFINITIVE WORKLIST (computed: collectAxioms over all 10289
MC decls → 296 dirty; source-BFS from yRho_representable → 136 reachable-dirty; literal
leaves among them = THREE):
  (A) weilPairingEval_self (WeilPairing/Basic:370) — THE E4a grind (this campaign);
  (B) weilPairingEval_nondegenerate (Basic:435) — field-leaf statement; HasseWeil has
      weilPairing_nondegenerate (used in DetDeg omegaForm_nondegenerate:216) ⟹ B rides
      the same L3-comparison transport as L5. Nearly free after the campaign.
  (C) IsOfficialCartier.isFinite (CartierDivisor:2858, KM 1.2.3 ⇒) — proper+qf⟹finite;
      mathlib's IsFinite.of_locallyQuasiFinite is ARTINIAN-base only (not applicable);
      needs a route (ZMT-lite or affine+proper). Separate ticket.
Everything else in the repo (abelEnrichment, EndomorphismDegree, GammaH, YFullRoute,
ExactOrder, Factorization sorries...) is NOT under yRho_representable (source-BFS;
final gate = #print axioms at the end). yRho_geometricallyIrreducible (frozen analytic)
is a SEPARATE decl, not in RepresentsYRho — confirmed out of the mandate's cone.
NOTE: the ":2204 T-F3 sorry" was a DOCSTRING false positive — PairingCompatAt is a real
definition; T-F3 is discharged. Tracer gotcha: imported theorem VALUES are inaccessible
(env.find?/kernel/private all strip them; 4.33 olean design precomputes per-decl axiom
arrays — Lean.collectAxioms is the ONLY oracle; carrier-walks must be source-level).
[SLOT-WALK PROVEN]: slot_walk = prefix (s1/congr-tmul/s2 + rfl-closes the refl-slot) +
hA2 (unit-eq-res) + tail (fresh budget: e3-fusion **by rfl** — the tensorObj_map_tmul
LEMMA-application storms even under respectTransparency-false, but the fact IS rfl and
the kernel path is cheap; A45 composite-naturality micro (shUnit ≫ mTOI.symm.hom.val
as ONE naturality_apply — no congrArg-lambda typing, no subst/map-id residue); s3-
congrArg). NEW LESSONS: (1) when a lemma-application storms, try `rfl` if the lemma
itself is rfl — kernel-defeq has no metavars and often sails; (2) naturality of a
COMPOSITE hom in one naturality_apply beats congrArg-of-naturality (the congrArg-lambda
retypes the middle carrier = storm); (3) subst-then-simp on eqToHom-micro-lemmas leaves
restrictScalarsId'App residue — avoid, use naturality. NEXT: SLOT-SQ assembly (:1383,
entry landed; cont.29d chains), then NR-1 (:1403), s2-residuals (:418/:431), G2', ORD-G.

[SLOT-SQ ASSEMBLED] (2026-08-17, cont.30b): SLOT-SQ = slot_sq_lhs ∘ [MEET-sorry] ∘
slot_sq_rhs.symm after the double-homEquiv transposition + a `show` at the reduced
value-form (homEquiv_unit fires by simp; the comp/pushforward app-split is NOT
simp-able — the X.Modules wrapper-category blocks SheafOfModules.comp_val — but IS
exact-defeq: `show` the reduced form directly). CHAINS: slot_sq_rhs (peel-form,
stated REVERSED so it closes by rfl) = R1 pullbackMap_app_unit → R2 slot_walk-V →
R3 unitH-naturality-at-eqToHom → R4 pRT-naturality at (Opens.map h).map-eqToHom →
R5 pRT-COLLAPSE at IMV; all g/h-spelled, NO W.ι-crossing, compiled first try.
slot_sq_lhs = L1 pRT-COLLAPSE under slot → L2 app_pullbackCongr_inv_unit → L3
congrArg-cast slot_walk-W. ★★ THE CROSSING PATTERN (the W.ι = homOfLE ≫ V.ι
propositional wall): (1) the opens h⁻¹(Vι⁻¹U) vs W.ι⁻¹U are NOT defeq (probe!), but
comp-preimage IS rfl; (2) NEVER congrArg-lambda across the wall (lambda-typing
storms); (3) state the crossing as ONE subst-lemma over ABSTRACT {f g} (he : f = g)
— morphism-vars subst-able, Congr-proof-args cross by PROOF-IRRELEVANCE (f = g is
Prop!) — with the φ-application INSIDE (app_pullbackCongr_inv_unit: φ.app-op-g⁻¹U
(Congr.inv (unit-g w)) = show-CAST (φ.app-op-f⁻¹U (unit-f w)); subst he; rfl); (4)
thread `he` as a BINDER through the consumer-lemma so the statement-cast and the
proof-cast elaborate from the SAME syntax (identical Eq.mpr-motives — never mix
concrete (X.homOfLE_ι hWV).symm-casts with he-var-casts in one chain, except where
proof-irrelevance covers it). REMAINING [MEET]: CAST(map-eqToHom-W(unit-W-IMW(shX
((res m) ⊗ₜ (res-res g))))) = map-arrowV(Congr.inv(unit-comp-IMV(shX((res m) ⊗ₜ
res-g)))) — plan: arg-level crossing-lemma (Congr.inv∘unit-comp → CAST(unit-W), the
φ-free version) + cast/eqToHom-normalization (eqToHom_map: map-eqToHom-applications
ARE casts) + the PURE-W res-fusion (IMW ≤ IMV: pullbackUnit_app_res + shX-naturality
+ tensorObj_map_tmul-fuse + Subsingleton-arrows). Then NR-1 consumes SLOT-SQ.

[SLOT-SQ COMPLETE] (2026-08-17, cont.30c): pullbackRestrictTransport_tensorIdealSlotIso
PROVEN END-TO-END. Final architecture (9 private lemmas, all landed):
slot_walk_prefix + slot_walk_tail + comparison_shUnit_app_map_eqToHom [A45] + slot_walk;
app_pullbackCongr_inv_unit + pullbackCongr_inv_unit_arg + map_eqToHom_cast_crossing
[the three abstract-{f g}(he : f = g) subst-crossing micros]; slot_sq_lhs (L1-collapse →
crossing → cast-walk); slot_sq_rhs (R1-R5 peel, reversed, rfl-closed); map_ef_split +
slot_sq_meet_inner (b1-b2) + slot_sq_meet_inner_x (b3-naturality typed-have + b4-rfl +
b5-legs congr_arg₂) + slot_sq_meet_inner_cast + slot_sq_meet_peel (M1-M3 peel);
SLOT-SQ := entry-transposition + show-reduced-form + hef-hoist + 4-fold trans chain
lhs/(inner_cast)/(peel)/rhs. BUDGET-LESSONS (hit ~6 times): (1) a decl's STATEMENT-
elaboration counts into its 200k budget — a giant-statement lemma has little proof-
headroom; keep big-statement lemmas' proofs to ≤4 steps, extract the rest; (2) congrArg-
λ-over-σ with a giant FIXED body = the λ-elaboration storms — hoist as ∀-section micro
(map_ef_split pattern: small binders, general y); (3) NEVER compose two independently-
elaborated show-casts across decls UNLESS both elaborate from the same he-BINDER +
same-syntax (then instantiation makes them identical); decl-boundaries belong at CAST-
FREE forms; (4) typed-have realignment for naturality_apply when the adjunction-target
functor-spelling ((sheafification ⋙ forget ⋙ restrictScalars).obj) differs from the
sheaf-val spelling — ascribe the sheaf-val form, prove by the raw naturality term.
REMAINING in NativeRestriction: s2-residual (ONE sorry, in
pullbackIdealTrivOfGen_symm_hom_app_one ~:381) + NR-1 (:2033). NEXT: s2-residual →
NR-1 (1a×2 + 1b + SLOT-SQ-at-elements + UNIT-VAL re-add) → G2' → ORD-G/L1 →
E4a-diagonal reduction → leaves A (weilPairingEval_self) + B (_nondegenerate via
HasseWeil weilPairing_nondegenerate transport).

[SLOT-SQ + s2 AXIOM-CLEAN] (2026-08-17, cont.30d): #print axioms
pullbackRestrictTransport_tensorIdealSlotIso = [propext, Classical.choice, Quot.sound] ✓
and pullbackIdealTrivOfGen_symm_hom_app_one ✓. s2-residual-a: hu typed-have crossing the
.app-sugar (Hom.app := forget₂-wrapped .val.app; restrictAdjunction_unit_app_app is rfl
but simp can't see through the spelling), then arrow-swap to the composite path
(opensFunctor.map (eqToHom hpre.symm) ≫ pre ≫ imgle), double map_comp split, ALIGNED
rfl (the standalone rfl fails only because the ARROWS differ — after aligning the
arrows the coe-unwinding is rfl). s2-residual-b: hnat.trans + congrArg-map-eqToHom of
the [511] restrictFunctorIsoPullback_hom_unit_app_apply. NativeRestriction is now
ONE sorry: NR-1 (nuPullback_app_restrictTransport). NEXT: NR-1 (consumes SLOT-SQ +
NR-1a restrictTransportSection_naturality + 1b pullbackRestrictTransport_unitIso, all
proven; + possibly the UNIT-VAL pullbackUnitIso_hom_app_unit re-add from cont.26).

[NR-1 DESIGN] (2026-08-17, cont.30e): restrictTransportSection hWV P htop x =
[Congr.inv ∘ Comp.hom]-app-⊤ (map-eqToHom-htop (unitH.app-V⊤ x)) — i.e. = pRT-P.app-⊤
z₀ with z₀ := map-htop(unitH x) (pRT unfolds to Comp.hom ≫ Congr(symm).inv per 1b's
calc). nuPullback = slotIso.hom ≫ pb-map-e.hom ≫ pb-map-idealModuleToUnitHom ≫
pullbackUnitIso.hom (FieldLeaf:1455). NR-1-CHAIN at ⊤-elements: (1) [NR-slot-T]:
slotW.app-⊤(T-M x) = T-⊗(slotV.app-⊤ x) — via SLOT-SQ-congr_hom at z₀ + push
(pbH-map-slotV).app through map-htop (eqToHom-naturality) + pullbackMap_app_unit
(pbH-map-on-unitH-image = unitH-of-slotV-value); (2)+(3) NR-1a
restrictTransportSection_naturality DIRECT at f := e.hom and f := idealModuleToUnitHom
J₂; (4) [1b-at-elements]: evaluate pullbackRestrictTransport_unitIso at z₀' +
push-through + the [UNIT-VAL] micro (pullbackUnitIso_hom_app_unit, re-derive from
cont.26 scratch): unitIsoH.app-⊤(map-htop(unitH s)) = res-htop(homOfLE-app-⊤ s) —
matches the NR-1-RHS spelling (W.toScheme.presheaf.map (eqToHom htop).op ∘
(Scheme.Hom.app (X.homOfLE hWV) ⊤).hom). Each stage its own lemma per the budget rule.

[★ NATIVERESTRICTION COMPLETE] (2026-08-17, cont.30f): the file has ZERO sorries;
nuPullback_app_restrictTransport [NR-1] = [propext, Classical.choice, Quot.sound].
Final NR-1 assembly: stage-unfold at the element was pure defeq (no show needed — the
first congrArg-trans's unification crossed the ν-composite-app); slot-T + 1a at e.hom +
1a at idealModuleToUnitHom J₂ + unit-T. [NR-unit-T]: 1b at the re-indexed unit image +
push-through + core := congrArg-at-elements of
pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit with homEquiv_unit rw'd —
the wrapper/toRingCatSheafHom bridges all crossed at defeq (exact hval). Lesson: the
mathlib homEquiv-characterisation lemmas evaluate at elements cleanly — congrArg with
an UNANNOTATED λ (inferred domain), never hand-spell the SheafOfModules-hom-type
(universe pins broke it). NEXT: [G2'] exists_normalized_chart_dataset_perChart
(GlueDataset, NR-2×2 + read-off route cont.20) → [ORD-G/L1] exists_const_mul_weilFunction
(OrdPipeline, pointwise divisor route cont.18-19) → L3/L5 already proven modulo L1 →
E4a-diagonal reduction → leaves A (weilPairingEval_self) + B (_nondegenerate).

[G2' RECON CORRECTION] (2026-08-17, cont.30g): G2' is NOT a re-witnessing of base-G2.
The base's dressing units a₀ b₀ come from transitionUnitOfCover_eq_dressed_native
(FieldLeaf:2077) and are genuinely per-OVERLAP (the efam-vs-native comparison ON the
overlap). The per-chart route (as the G2' docstring says): A i := the chart-level
ν-comparison unit — nuPullback M J₁ J₂ e (W i) g … evaluated at the ⊤-section 1 (the
unit-value of the chart-trivialisation-vs-native comparison ON THE WHOLE PIECE W i);
the overlap-identity t_ij = res(A i)·(u₂u₁⁻¹)·res(A j)⁻¹ then follows from:
(a) TWO instances of restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu [NR-2,
proven], one per chart, RESTRICTED to the overlap via nuPullback_app_restrictTransport
[NR-1, JUST PROVEN — this is exactly what it was built for]; (b) nuPullback_mul for
the generator change u₁ (J₁-generators of the two charts differ by u₁ on the overlap);
(c) the transitionUnit-decomposition through the native middle (the
transitionUnitOfCover_eq_dressed_native PROOF-SHAPE, re-run keeping the ν-provenance).
EXECUTION PLAN: (1) read transitionUnitOfCover_eq_dressed_native's proof body
(FieldLeaf:2097+) to extract where a b := ν-values enter; (2) define A i := the
ν-⊤-value-unit on W i (needs: the piece W i carries a J₁-generator res-g₁ and the
IsIso-instances — supplied by the chart-data through W i ≤ V (ch i)); (3) prove the
overlap-identity via NR-1 + nuPullback_mul; (4) assemble G2' with the base-G2 cover
(charts ⊓ z-parts, cZ-rescale absorbed INTO A or kept as an extra explicit factor —
check whether the perChart-statement's A can absorb cZ: A-inl-i := cZ i · ν-unit-i).
Watch: the cZ-rescale (overUnitScalarIso) multiplies the transition by
res(cZ i)·res(cZ j)⁻¹ (transitionUnit_restrict_rescale) — composes with the ν-A's
multiplicatively ⟹ A-total := cZ-factor · ν-factor per piece ✓ per-chart-shaped.

[G2' ROUTE FINAL] (2026-08-17, cont.30h): transitionUnitOfCover_eq_dressed_native's
a := trivializationTransitionUnit(overlap, res-efam-i, overTrivializationOfRestrictIso
(restrictIsoOfPullbackIso (nativeTensorIdealTriv AT-THE-OVERLAP with res'd generators)))
and b := (same for j)⁻¹-side. PER-CHART REFINEMENT: A i := trivializationTransitionUnit
(W i, efam i, native-trivialisation-ON-W-i with the chart generators); then
res-to-overlap(A i) equals the a-above via (i) transitionUnit-restriction-compat and
(ii) [NR-3] restrictTrivialization_nativeTensorIdealTriv (PROVEN — the native
trivialisation restricts on the nose, its NR-2/NR-1 machinery now fully clean).
EXECUTE: (1) read NR-3's exact statement + find/prove transitionUnit-res-compat
(grep trivializationTransitionUnit_restrict / _res in FieldLeaf+NativeRestriction);
(2) state G2'-helper: res(A i) = a-term (per chart-side); (3) G2'-proof := base-G2
construction verbatim + per-branch: dressed-native as-is, then rewrite a := res(A i)
· b := res(A j) via the helper, absorb the cZ-rescale into A-total (inl: cZ i · A i;
inr: A i); the u-relations carry unchanged. All pieces proven — assembly only.

[G2' ASSEMBLY DESIGN] (2026-08-17, cont.30i): confirmed NR-3 is ON-THE-NOSE
(restrictTrivialization hWV (native-V) = native-W-of-res-gens, needs hmono of res-g₂)
and trivializationTransitionUnit_restrict gives res-of-transition = transition-of-res.
DEFINE A a := trivializationTransitionUnit (W a) (e a) (native-W-a-triv at res'd
ch-a-chart generators) — against the FULL e-a (cZ-rescale absorbed ✓). PER-OVERLAP:
t_ab = res(A a) · (u₂u₁⁻¹) · res(A b)⁻¹ via the dressed-native calc-shape
(hc1/hc2/hb/hmid) with the a/b-legs rewritten: transitionUnit(res-e-a, res-native-a)
= [transitionUnit_restrict] res(A a) after [NR-3] identifies res-native-a =
native-overlap-res-gens; mid = u₂u₁⁻¹ via trivializationTransitionUnit_overTriv_of_
inv_comp_hom + nativeTensorIdealTriv_inv_comp_hom (verbatim from dressed-native).
OPEN PLUMBING QUESTION: per-PIECE generator instances — the pieces W-a (chart ⊓
z-preimage / chart ⊓ Zc) are NOT affine; need (i) idealSections-membership of res-gens
on W-a (idealSections_map ✓ trivial), (ii) IsIso (idealGenHom J (W a) res-g) — from
the chart-level IsIso by restriction: grep idealGenHom-restriction-compat lemmas
(candidates: idealGenHom_restrict / restrictTrivialization-machinery in
NativeRestriction — the pullbackIdealTrivOfGen existence at chart-level shows the
chart-iso; the restriction-functor maps isos to isos IF idealGenHom-res-compat
exists); (iii) hmono at overlap-level res-g₂ (the base derived Mono from nzd via
IsIntegral germ-injectivity — mono_unitEndomorphismOfTopSection_of_nzd-ish, grep how
dressed_of_charts got hmono). If (ii) lacks a compat-lemma, prove
idealGenHom_restrictTrivialization: restrictTrivialization-of-idealGenHom-iso or the
direct statement idealGenHom J W' (res g) = conjugated-restriction — one more
NR-battery micro (the toolkit patterns apply).

[G2' LAST PLUMBING PIECE] (2026-08-17, cont.30j): no idealGenHom-res-compat exists yet.
Route for the piece-level IsIso (W-a ≤ chart V-c, non-affine): ONE micro
`idealGenHom_restrict`: the restriction (over-category / restrictTrivialization-style)
of idealGenHom J V f to W ≤ V equals idealGenHom J W (res f) — provable by
unit_hom_ext (homs out of unitObj are pinned by the ⊤-value; both sides read the
res'd generator — the NR-battery's own unit_hom_ext at NativeRestriction:~68) + the
openTopSection_homOfLE res-compat; then IsIso transfers (functor-image of iso +
conjugation). hmono at overlaps: as in dressed_of_charts (nzd + IsIntegral
germ-injectivity — copy its derivation, grep hmono-construction there). THEN the G2'
assembly per cont.30h/30i is fully unblocked: per-piece native trivialisations +
A-def + the dressed-native-calc with restrict/NR-3 leg-rewrites. Estimated: 1 micro
(idealGenHom_restrict) + 1 helper (res-A-identity) + the 4-branch assembly.

[G2' EXECUTION STRUCTURE] (2026-08-17, cont.30k): NO new micros needed — inventory
complete: restrictOverTrivialization_comp_eq (KMIndependence:85, double-restriction
path-independence), trivializationTransitionUnit_restrict (InvertibleSheafCocycle:158),
NR-3 + the over-language crossings (overTrivializationOfRestrictOpenTrivialization,
restrictOpenTrivialization_restrictIsoOfPullbackIso — the G2'-docstring's own list),
isIso_idealGenHom_of_principal (chart-level only — NO piece-level IsIso needed
anywhere!). TWO-STEP PLAN:
STEP-1 [new lemma, FieldLeaf after :2135]: exists_transition_dressed_of_charts_perChart
— same hypotheses as dressed_of_charts (charts Vi=Wf i, Vj=Wf j affine, generators,
spans, nzd) + CONCLUSION ∃ (Ai : Γ(Wf i)ˣ) (Bj : Γ(Wf j)ˣ) (u₁ u₂ : overlap-units),
transitionUnitOfCover = resUnit(Ai)·(u₂u₁⁻¹)·resUnit(Bj)⁻¹ ∧ the two u-relations —
where Ai := trivializationTransitionUnit(Wf i, efam i, overTriv(restrictIso(native-at-
CHART-i with f-gens))) [chart-level IsIso ✓]. PROOF = the dressed-native calc-shape
(hc1/hc2/hb/hmid verbatim from transitionUnitOfCover_eq_dressed_native) with the a/b
legs rewritten: transitionUnit(res-efam-i, overTriv-native-OVERLAP-gens) =
[over-crossing + NR-3] transitionUnit(res-efam-i, res-overTriv-native-CHART-i) =
[trivializationTransitionUnit_restrict] resUnit(Ai); the span/nzd/hmono machinery at
the affine chart-overlap copied from dressed_of_charts (:2158-2230).
STEP-2 [G2' proof]: base-G2 proof copy (GlueDataset:317-720) with dressed_of_charts →
the perChart variant; witnesses: ch := Sum.elim id id; A := Sum.elim
(fun i => cZ i · resUnit(piece≤chart)(A-chart-i)) (fun i => resUnit(Ai)); per-branch
read-offs: Units.map-res of the chart-overlap identity + resUnit-fusion
(Subsingleton-arrows) — the transitionUnit_restrict_rescale-dressing composes the
cZ-factors exactly as the base's witnesses show.

[G1'/G1'' LANDED] (2026-08-17, cont.30l): transitionUnitOfCover_eq_dressed_native_perChart
[G1', axiom-clean] + mono_unitEndomorphismOfTopSection_openTopSection_of_ne_zero +
exists_transition_dressed_of_charts_perChart [G1'', zero errors] all PROVEN in
NativeRestriction (still zero sorries). G1'' takes chart data at the Wf-parametrization
directly (haffi/haffj : IsAffineOpen (Wf i/j) + span/nzd/mem ×4) — NO hVi-casts — and
outputs the per-chart form: transitionUnit = resUnit(A-i)·(u₂u₁⁻¹)·resUnit(A-j)⁻¹ with
A-c := trivializationTransitionUnit(Wf c, efam c, overTriv(restrictIso(native-chart-c)))
spelled explicitly (chart-IsIso via isIso_idealGenHom_of_principal-terms inline), plus
the two u-relations. Gotchas fixed: [IsAffineHom diagonal]-instance hypothesis needed
(the transitionUnit machinery), J.map_ideal wants the affineOpens-subtype-≤ (annotate
(inf_le_left : (… : X.Opens) ≤ …)), chart-domain instances needed for
mem_nonZeroDivisors_iff_ne_zero at the charts (component_integral + Nonempty-from-hne).
REMAINING FOR G2' [STEP-2b]: the assembly in GlueDataset — add
`import ModularCurves.WeilPairing.NativeRestriction`; copy the base-G2 proof
(:317-720); replace the 4 branches' exists_transition_dressed_of_charts-calls with
G1''-calls (charts: haffi := (V i).2 at W₀ i := (V i).1-defeq); witnesses: ch := Sum.elim
id id, A := fun a => match a with | .inl i => Scheme.resUnit inf_le_left?? — NO: A-inl-i
must combine the cZ-rescale with the chart-A: the e-(inl i) := restrictOver(e₀ i) ≪≫
scalar-cZ-i — the G1''-A-term is computed against efam := e-THE-PIECE-FAMILY?? NO —
G1'' is called at the PIECE-cover (Wf := W-pieces, efam := e)?? — the pieces are NOT
affine ⟹ G1'' (needs haffi of Wf i) does NOT apply at pieces!!! ⟹ call G1'' at the
CHART-cover (Wf := W₀, efam := e₀ — the base-G2's dressed-call was exactly there ✓)
then RESTRICT to the pieces via transitionUnit_restrict_rescale (as the base does):
t-piece-ab = resUnit(cZ-dressing) · res(t-chart-ij) — with t-chart-ij in G1''-form ⟹
t-piece = [resUnit-cZ-j-form]⁻¹·[resUnit-cZ-i]·res(resUnit(A-i)·(u₂u₁⁻¹)·resUnit(A-j)⁻¹)
— fold res-res via resUnit_resUnit → the perChart-statement's shape with
A-piece-inl-i := resUnit(piece≤chart)(A-chart-i) · cZ-i-INVERSE?? — CHECK the
rescale-orientation against transitionUnit_restrict_rescale's exact statement (grep
in GlueDataset/FieldLeaf) and the G2'-statement's required shape
t = res(A i)·(u₂u₁⁻¹)·res(A j)⁻¹ — the cZ-factors sit OUTSIDE the res-A's:
res-piece(A-chart-i)·cZ-form-i commute (units in a commutative ring ✓) ⟹
A-piece-i := cZ-factor-i · resUnit(A-chart-i) works with mul_comm-shuffles.

[★★ G2' COMPLETE] (2026-08-17, cont.30m): exists_normalized_chart_dataset_perChart
PROVEN AXIOM-CLEAN [propext, Classical.choice, Quot.sound]; GlueDataset.lean ZERO
SORRIES. Final architecture: units_shuffle (abstract 8-atom CommGroup ac_rfl; the
in-context AC-simp storms on giant atoms — ALWAYS shuffle abstractly) +
perChart_piece_transition (the piece-step: transitionUnit_restrict_rescale + congrArg
of the chart-dressing + simp-fusions + units_shuffle rfl rfl — in the ABSTRACT
setting resUnit_resUnit fires and the fusion-hypotheses become proof-irrelevant rfl!)
+ hdressed (∀-hoisted G1''-call with Ach-ascribed types) + A-witness uniformity
(inr-side gets ·(1)⁻¹ so all four branches share one helper) + 4 thin branches
(hmask-congrArgs for inr-sides — rw fails under the tUOC-def, congrArg-λ works).
GOTCHA LOGGED: python-replacement anchors MUST be region-sliced past the G2'-docstring
(the base-G2 proof contains IDENTICAL branch-text; a global replace corrupted the base
and cost a stash-recovery — b1/b2 rewritten from session history). CAMPAIGN STATE:
NativeRestriction zero sorries (SLOT-SQ, s2, NR-1, G1', G1''), GlueDataset zero
sorries (G2'). NEXT: [ORD-G/L1] exists_const_mul_weilFunction (OrdPipeline:~124, the
pointwise divisor route cont.18-19, now with the perChart dataset as input) — the LAST
brick before the L3/L5-chain (already proven modulo L1) closes; then the E4a-diagonal
reduction → leaf A (weilPairingEval_self) → leaf B (_nondegenerate transport).

[ORD-G ENTRY-POINTS] (2026-08-17, cont.30n): verified the two HW-side transfer
theorems as banked: projectiveDivisorOf_pullback_eq_pullbackDivisor
(HasseWeil DivisorPullback:244, needs ProjOrdTransport φ + Finite ker) and
weilFunction_divisor_eq_pullbackDivisor_kappaDivisor (HfactLemma:133) — so the L1
target-side divisor is pullbackDivisor [N] (kappaDivisor T). The pointwise species
G-REL / DIV-PIN / OrdAtInftyBridge are cont.18-19 DESIGN NAMES, not yet stated —
ORD-G needs: (1) the r-choice (the c₀-chart generator-ratio correction; recon the
kappaDivisor-vs-(J₁,J₂,f₁,f₂)-dictionary — how κ(Q)'s divisor reads the chart
generators; entry: kappaDivisor def in HasseWeil Curves + the kappa-def in
FieldLeaf); (2) the ORD-G statement in OrdPipeline: projectiveDivisorOf(H_HW ·
mulByInt_pullbackAlgHom N r) = pullbackDivisor [N] (kappaDivisor T) with H_HW :=
pullbackCurveFunctionFieldEquiv-image of germ(h c₀); (3) the pointwise proof at an
affine place P: split by which chart W i contains the image point; the hsplit +
G2'-perChart dressing express the H-germ as (chart-local units)·(u-ratio germs);
unit-ord-0 species + the span-pinned generator-ords via ValuationTransport
(uniformizer_of_span_maximalIdealAt :279, the span-dictionary :226) + the RP-germ
transport (pullbackCurveFunctionFieldEquiv_germ_globalTwist, PROVEN in OrdPipeline);
(4) the ∞-place: the zero-section is the model-∞; J₂-charts cover it
(OrdAtInftyBridge species to state); (5) L1-assembly := ORD-G + HfactLemma-target +
exists_const_mul_of_projectiveDivisorOf_eq (FieldLeaf:2340). All scheme-side
transports PROVEN (OrdPipeline's five landed lemmas). NEXT CYCLE: recon
kappaDivisor + kappa-def dictionaries, then state (2) with the r-construction.

[ORD-G κ-DICTIONARY] (2026-08-17, cont.30o): kappa (SelfAdjointN:198) := κ_T(Q) =
[𝒪(Q − 0)] via sectionToPicRel; kappaDivisor W P := single(P) − single(∞)
(HasseWeil PicZero:232). So the (J₁,J₂)-pair presents 𝒪(Q−0) with J₁ ↔ the
zero-section ideal and J₂ ↔ the Q-section ideal (through sectionToPicRel's
construction + hM); the chart generators f₁ i / f₂ i vanish on the respective
section loci with order pinned by the span data. The pointwise DIV-PIN species:
at a place P over chart i, ord_P(f₂ i germ) = multiplicity of P in the Q-section
divisor, ord_P(f₁ i) = in the zero-section divisor — state via the
ideal-of-section ↔ maximalIdealAt dictionary (ValuationTransport :226/:279 +
sectionToPicRel internals; recon sectionToPicRel's presentation next). Then the
u-ratio germs (u₁ = f₁-ratio, u₂ = f₂-ratio via the G2' u-relations) carry orders
(zero-sec vs Q-sec differences), the hsplit relation transfers along [N], and the
per-place sum reproduces pullbackDivisor [N] (kappaDivisor T) at each w.

[ORD-G κ-ORIENTATION WATCH] (2026-08-17, cont.30p): sectionToPicRel (DivisorClass:180)
= picRelProj(picClass(sectionDivisor Q) · picClass(sectionDivisor zero)⁻¹) — GME 2.16
"P ↦ I(P)⁻¹ ⊗ I(0)". With hM : κ(Q).val = toSkeleton M and e_dict : M ⊗ J₁ ≅ J₂
(⟹ M ≅ J₂ ⊗ J₁⁻¹), the orientation candidate is J₂ ↔ I(0)-side (zero-section) and
J₁ ↔ I(Q)-side (Q-section) — BUT the picClass-inverse conventions and the
picRelProj-normalisation must be checked at execution before pinning the DIV-PIN
signs (ord_P(f₁ i) counts the Q-section, ord_P(f₂ i) the zero-section, OR swapped).
The divisors are RelEffCartierDiv.sectionDivisor (pullback.snd) Q / zero — their
ideal-sheaves' maximalIdealAt-dictionary at closed points = the DIV-PIN input
(sectionDivisor + IsOfficialCartier machinery, LevelStructure/CartierDivisor).
Next cycle: state DIV-PIN from this dictionary, then G-REL, then ORD-G.

[DIV-PIN INPUT COMPLETE] (2026-08-17, cont.30q): sectionDivisor π z hz :=
{ ideal := z.ker, … } (CartierDivisor:172) — the section-divisor ideal IS the
section's kernel ideal-sheaf. DIV-PIN therefore reads: for a chart generator f
spanning (z.ker).ideal V (common-principal data), the germ of f at a closed point
P is a UNIFORMIZER at P when P lies on the section image (smooth relative curve ⟹
the section is a reduced divisor, multiplicity 1 — uniformizer_of_span_
maximalIdealAt, ValuationTransport:279) and a UNIT germ when P ∉ the section
(the span generates the unit ideal at P — the stalk of z.ker at off-section
points is ⊤). Both cases via the span-transport (:226-shape) + maximalIdealAt.
So ord_P(f-germ) ∈ {0, 1} with indicator = P ∈ section-image; the u-ratio germs
carry ord = [P ∈ sec₁] − [P ∈ sec₂]; summed against the hsplit/[N]-transfer this
reproduces pullbackDivisor [N] (kappaDivisor T) pointwise. ALL RECON DONE — next
cycle is pure statement+proof work: DIV-PIN → G-REL → ORD-G → L1-assembly.

[DIV-PIN TOOLING VERIFIED] (2026-08-17, cont.30r): RP-4b
uniformizer_of_span_zChartMaximalIdeal (ValuationTransport:~270) is the ON-SECTION
tool (ord_P = 1 for zChart-span-generators of the transported maximal ideal; the
RP-dictionary roundtrip already inside). DIV-PIN decomposes into: (a) the chart-to-
zChart germ hop for the L1-chart generators (germToFunctionField (Wc i) f →
zChart-localization — via projModelFunctionFieldEquiv_germToFunctionField_zChart
[GERM-Z, PROVEN in OrdPipeline] + zChartLocalizationEquiv_compat [brick-3, CLOSED]);
(b) ON-section: the span-data of z.ker at the chart transports to a span of
zChartMaximalIdeal (Ideal.map-span + the section-ideal ↔ maximalIdealAt dictionary
— the one NEW ingredient: z.ker's stalk at an on-section closed point IS the
maximal ideal, smoothness/reducedness of the section; state as its own micro) →
RP-4b → ord 1; (c) OFF-section: z.ker-stalk = ⊤ at P ∉ image(z) ⟹ the generator
germ is a UNIT in the local ring ⟹ ord_P = 0 (state the unit-ord-0 species:
pointValuation of a local-unit's FF-image = 1; probably derivable from
intValuation-of-unit or Uniformizer-adjacent API — grep ord_P/pointValuation unit
lemmas next cycle). NEXT CYCLE ENTRY: state the (b)-micro (stalk-of-section-kernel
= maximalIdealAt on the section) + the (c)-species, then DIV-PIN, then G-REL,
then ORD-G, then L1. All in OrdPipeline (imports reach everything).

[DIV-PIN DICHOTOMY FULLY STOCKED] (2026-08-17, cont.30s): the off-section species
EXISTS: ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt (HasseWeil
MulByIntUnramified, used at :188-203) — ord_P(algebraMap r) ≠ 0 ⟺ r ∈
maximalIdealAt P. So DIV-PIN = ONE new micro [SEC-STALK]: for the L1-chart span
data of z.ker (z = a section: the Q-section via overPoint Q or baseChangeZero),
the transported generator's maximalIdealAt-P-membership ⟺ P lies over the
section image (through the zChart/RP-dictionary: germ-Z [GERM-Z proven] +
zChartLocalizationEquiv_compat + coordRingToZSection). ON-section: membership +
span ⟹ uniformizer_of_span_maximalIdealAt ⟹ ord 1; OFF: non-membership ⟹ ord 0.
Then G-REL (the hsplit germ identity at a place, transported via
pullbackCurveFunctionFieldEquiv_germ_globalTwist [VAL-TRANSPORT proven] +
[EQUIV-TAU proven]) → ORD-G pointwise (Finsupp.ext w; affine places by the chart
dichotomy + pullbackDivisor_apply; ∞ via the zero-section chart) → L1-assembly.
EVERY ingredient is now either proven or a single named micro. NEXT CYCLE: write
[SEC-STALK] + [DIV-PIN] statements in OrdPipeline and prove them.

[DIV-PIN STATEMENT SHAPE] (2026-08-17, cont.30t): LHS-form (matching VAL-TRANSPORT's
:291 spelling): ord_P applied to `pullbackCurveFunctionFieldEquiv W
(germToFunctionField V s)` for s : Γ(pullback-curve, V) — with the haveI-IsIntegral
preamble as in :291-300. P ranges over (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint (the
HW ord_P-side); the scheme-side section-image membership crosses via
SpecPoints (projModel W) (projModelπ W) K + projModelPointsEquiv (the L1-statement's
own p/hxp-pattern: p.1 is the scheme-point). SEC-STALK then states: [transported
generator ∈ maximalIdealAt P] ⟺ [p.1 ∈ Set.range z-section.base ∧ p over V] —
via the RP-dictionary (zChartMaximalIdeal + coordRingToZSection roundtrips,
ValuationTransport :226/:270) + germ-restriction hops (germToFunctionField_restrict,
as used in VAL-TRANSPORT's h12-h45 chain). NEXT WINDOW OPENING MOVES: (1) read
ValuationTransport's RP-decl signatures (:1-120, the pointValuation/ord_P-transport
family) + SpecPoints def; (2) state SEC-STALK + DIV-PIN in OrdPipeline after
[GERM-Z]; (3) prove via the stocked dichotomy (cont.30s).

[SEC-STALK SIMPLIFICATION — Spec-K SECTIONS ARE POINTS] (2026-08-17, cont.30u): in
the L1 context T = Spec K (pullback along 𝟙), so the Q-section and zero-section are
K-POINTS: each section's image is ONE closed point, its kernel ideal-sheaf is the
ideal of that single point, and the section-divisor is the single-point divisor.
SEC-STALK therefore reduces to: the chart generator f of z.ker at V spans
maximalIdealAt at THE section point (P = P_z) and is a non-member (unit) at every
other P over V — the span-transport to the RP-dictionary at P_z is exactly the
:226-shape span-statement; membership/non-membership at P ≠ P_z from the
single-point ideal (stalk = ⊤ off the point). The on-section predicate is
morphism-level (the L1-hxp pattern: p.1 = the section composite) ⟺ point-equality
(K alg closed, K-points ↔ closed points). DIV-PIN's indicator := [P = P_Q] for the
J-Q-side and [P = P_O] for the J-zero-side (κ-orientation per cont.30p to fix).
SpecPoints := {g : Spec K ⟶ X // g ≫ f = Spec.map (algebraMap)} (WeierstrassModel:65).

[DIV-PIN ALREADY PROVEN] (2026-08-17, cont.30v): the RP-programme (session-8) landed
it: divisorOf_algebraMap_eq_single_of_span (ValuationTransport:483) — div(r) = [P₀]
for a maximalIdealAt-P₀-span-generator, away-nonmembership internal (via
eq_of_maximalIdealAt_le + divisorOf_algebraMap_eq_single). Also stocked:
ord_P_algebraMap_eq_zero_of_notMem (:309). SO the cont.30n "DIV-PIN"-item is DONE;
the residual [SEC-STALK] is only the SPAN-SUPPLY: transport the L1-chart span
(J.ideal V = span {f}, J = a section-kernel at T = Spec K) to the HW-side span
(maximalIdealAt P_z = span {transported-r}) — via the zChart-hop (zChartMaximalIdeal
:43 + zChartLocalizationEquiv_compat :116 + coordRingToZSection) + the
section-kernel-stalk = point-ideal identification (Spec-K-section = closed point,
cont.30u). REMAINING L1-LAYER: [SEC-STALK span-supply] → [G-REL] (the hsplit
germ-read at a place: the H-germ at P over chart i vs h-c₀ via the G2'-transition +
hsplit — transported by VAL-TRANSPORT/EQUIV-TAU) → [ORD-G] (Finsupp.ext pointwise:
affine places by chart-dichotomy + DIV-PIN + pullbackDivisor_apply; ∞-place) →
[L1-assembly]. Next: recon the G-REL germ-algebra (how the hsplit-relation reads at
a single place through germToFunctionField).

[G-REL MECHANISM] (2026-08-17, cont.30w): the divisor of H := germ(h c₀) materialises
через the transitions: on [N]⁻¹(Wc i), hsplit gives H = germ(h i) · [N]♯(t_{i,c₀})⁻¹
(germ-restriction hops); h i is a unit ON THE WHOLE [N]⁻¹(Wc i) (germ-ord 0 at every
P over chart i); t_{i,c₀} = res(A i)·(u₂u₁⁻¹)·res(A c₀)⁻¹ [G2'] where A-parts are
units on FULL charts (germ-ord 0 over chart i for A i; over-chart-c₀-only for A c₀ —
at P over BOTH the A-germs die) and the u-germs, AS FF-ELEMENTS, are generator
ratios: u₁-germ = f₁i-germ / f₁c₀-germ (from the u-relation, an equality of sections
on the overlap ⟹ of FF-germs) — so ord_P(u₁-germ) = ord_P(f₁ i) − ord_P(f₁ c₀),
nonzero beyond the overlap. Hence at P over chart i (and over c₀ for the tails):
ord_P(H) = −ord_{[N]}(transported t) = [generator-ord differences] — the f-i-parts
give the local [N]*-section-indicators (DIV-PIN + the [N]-transfer), the f-c₀-parts
are a GLOBAL tail independent of i — cancelled by choosing r := the c₀-generator
ratio (div r = [Q]−[O]-shaped via DIV-PIN at c₀'s span data!) so that
div(H·[N]♯r) = pullbackDivisor [N] (kappaDivisor T) on the nose. The r-choice is
CONSTRUCTIVE: r := (transported f₂c₀-germ)/(transported f₁c₀-germ)-as-FF-element
(orientation per cont.30p watch). ORD-G-EXECUTION: state the per-chart germ identity
[G-REL], then Finsupp.ext w with the chart-dichotomy; every ord-computation is
DIV-PIN/:309/:483 + the ProjOrdTransport-[N]-transfer.

[SEC-ORD FINAL FORM] (2026-08-17, cont.30x): WARNING logged: chart generators have NO
global divisor claim (f lives only on V; div(:483) needs a GLOBAL maximalIdealAt
span) — the pointwise ORD-G design never needs one. The executable statement is
**[SEC-ORD]**: for a chart V of the L1-data with span J.ideal V = span {f}
(J = z.ker, z a Spec-K-section with image point P_z) and a place P lying over V:
ord_P (pullbackCurveFunctionFieldEquiv W (germToFunctionField V f-image-path)) =
if P = P_z then 1 else 0. PROOF SHAPE: transport the V-span to the STALK at P
(scheme-stalk ↔ localRingAt via isLocalization_stalk_zChartPoint
[ValuationTransport:179] + zChartLocalizationEquiv_compat); on-point: the stalk
span IS the DVR maximal ideal (section-kernel stalk at its own point) ⟹ the
RP-4a hgen-shape ⟹ ord 1 (mirror uniformizer_of_span_maximalIdealAt's core :203+
with the stalk-supply); off-point: the section-kernel stalk at P ≠ P_z is ⊤ ⟹
the germ is a stalk-unit ⟹ ord 0 (:309-shape via non-membership). zChartMaximalIdeal
:= Ideal.map (coordRingToZSection) (maximalIdealAt P) (:43) — the dictionary
direction for the roundtrips. G-REL then composes these per-chart ords per cont.30w.
NEXT WINDOW: state [SEC-ORD] in OrdPipeline (after GERM-Z), prove the two cases,
then [G-REL], then [ORD-G], then L1.

[SEC-ORD ALGEBRAIC ROUTE] (2026-08-17, cont.30y): skip scheme-stalks entirely —
RP-4a's own proof pattern (:203) is pure AtPrime-algebra from a maximalIdealAt-span;
SEC-ORD mirrors it with the LOCALIZED span supplied from the section-kernel:
z.ker.ideal at an affine = RingHom.ker of the section's app (the ker_subschemeι_app
family, CartierDivisor); at the section's own point the localized kernel IS the
maximal ideal of the localization (kernel of the local evaluation); the V-span
transports by Ideal.map through J.map_ideal + the zChart roundtrip
(coordRingToZSection + zChartMaximalIdeal :43 + primeCompl :80 +
zChartLocalizationEquiv :95/:116). ON-P_z: localized-span ⟹ intValuation_singleton
⟹ ord 1 (RP-4a's chain verbatim from the hgen-stage). OFF: f ∉ maximalIdealAt P
(the kernel evaluates ≠ 0 at P ≠ P_z through the span) ⟹ :309. zChartPoint (:168)
+ isLocalization_stalk_zChartPoint (:179) available if the scheme-side point-
identification is needed for the P_z-dictionary (fromSpec of zChartMaximalIdeal).
NEXT WINDOW: write [SEC-ORD] + its span-supply have-chain in OrdPipeline.

[SEC-ORD API PINS] (2026-08-17, cont.30z): Scheme.Hom.ker_apply (mathlib
IdealSheaf/Basic:702): (f.ker).ideal U = RingHom.ker (f.app U)-shape for affine U
[QuasiCompact f] — the section-kernel's chart-ideal IS the app-kernel ✓ the
SEC-ORD span-supply reads through it. sectionDivisor.ideal = Scheme.Hom.ker z
(CartierDivisor:194, rfl). SEC-ORD statement level: PULLBACK-side (match L1-data;
the fst-hop done once inside via functionFieldMap_germToFunctionField + GERM-Z +
zChartLocalizationEquiv_compat). All pins complete — next window writes it.

[SEC-ORD STATED] (2026-08-17, cont.30aa): ord_P_germ_sectionKer_generator lands in
OrdPipeline (after CONST-SECTION, before VAL-TRANSPORT; sorried). Spelling notes:
open scoped Classical ABOVE the docstring for the if-Decidable; the germ's Nonempty
as an instance BINDER `[Nonempty V.1]` (the haveI-spellings ↥(V.1 : Opens)/↥↑↑V do
NOT match the elaborator's instance-goal — binder-form resolves it; VAL-TRANSPORT's
`[Nonempty V]`-pattern); the P-point dictionary: (inv fst).base (zChartPoint W P)
with z.base default for the section point (Spec-K unique point). PROOF CAMPAIGN
(cont.30y): (1) the fst-hop: pullbackCurveFunctionFieldEquiv-germ = projModel-FF of
the transported germ (functionFieldMap_germToFunctionField + the equiv-def); (2)
the zChart-hop: germ-at-V → germ-at-V⊓zChart (restrict) → GERM-Z localization-read;
(3) ON-case: hspan → ker_apply → the AtPrime span (Ideal.map-chain через
coordRingToZSection/zChartMaximalIdeal) → RP-4a-core (intValuation_singleton chain);
(4) OFF-case: f ∉ maximalIdealAt (the kernel's evaluation ≠ 0 at P ≠ P_z) → :309.
Split cases on the if; each case its own private lemma per the budget rule.

[SEC-ORD PROOF REFINEMENT — SHRINK TO BASIC] (2026-08-17, cont.30ab): GERM-Z consumes
germs at the FULL zChart (t : Γ(zChart)); a chart V is not inside zChart in general.
The route: the ord at P only needs a neighbourhood — shrink to a BASIC open of the
affine zChart around P's zChart-point inside (inv fst)⁻¹V ⊓ zChart
(IsAffineOpen.exists_basicOpen_le, the same cofinality move as
isIso_idealGenHom_of_principal's basis argument); on a basic open D(s),
Γ(D(s)) = Localization.Away s of Γ(zChart) and the transported germ reads as a
FRACTION f₀/sⁿ with f₀ ∈ Γ(zChart) — then ord_P(germ) = ord_P(algebraMap f₀') −
n·ord_P(algebraMap s') with s' ∉ maximalIdealAt P (P ∈ D(s)!) ⟹ ord-s' = 0 (:309)
⟹ ord = ord_P(algebraMap f₀'). The span-data transports to the basic-open
localization (map_ideal + Away-localization) pinning f₀' up to units: ON-case
f₀'-span-of-the-localized-maximal-ideal → RP-4a-core; OFF-case f₀' ∉ maximalIdealAt
→ :309. The germ-to-fraction read: functionField_isFractionRing_of_isAffineOpen
(used in GERM-Z's proof) + the section-restriction algebra — ALL standard localization
API. This is the full SEC-ORD proof plan; execute in a fresh window (stage the
fst-hop + shrink as have-chains, then the dichotomy as two private case-lemmas).

[SEC-ORD S1 LANDED] (2026-08-17, cont.30ac): the fst-hop h1 proven inside
ord_P_germ_sectionKer_generator: pullbackCurveFunctionFieldEquiv-germ =
projModelFFEquiv (germ-((inv fst)⁻¹V) ((inv fst).app f)) — a single congrArg of
functionFieldMap_germToFunctionField across the RingEquiv.trans/ofRingHom def-layer
(exact-defeq). SPELLING LESSON: the Opens-CoeSort instance-goals appear at the
↥↑-unfolded form; haveI's recorded at ↥(folded) MISS the discrimination tree —
for germToFunctionField at computed opens pass the instance @-EXPLICITLY
(@Scheme.germToFunctionField X _ U hNe). NEXT [S2]: shrink-to-basic: the P-point's
zChart-membership (hZaff.range_fromSpec pattern from isLocalization_stalk :193),
then hZaff.exists_basicOpen_le (x := ⟨zChartPoint, mem-of-(inv-fst)⁻¹V⊓zChart⟩) →
D(s) ≤ (inv fst)⁻¹V ⊓ zChart with the point inside; germ-restrict to D(s)
(germToFunctionField_restrict, TheoremOfSquareField:275); then the fraction-read.

[SEC-ORD S2 LANDED] (2026-08-17, cont.30ad): hPz (range_fromSpec) + the shrink
obtain ⟨s, hsle, hPs⟩ (exists_basicOpen_le at (inv fst)⁻¹V ⊓ zChart) both green.
NEXT [S2c]: germ-restriction h2 : germ-((inv fst)⁻¹V)(x) = germ-D(s)(res x) via
germToFunctionField_restrict (TheoremOfSquareField:275) at hsle.trans inf_le_left.
Then [S3] fraction-read: Γ(D(s)) is the Away-s localization of Γ(zChart)
(IsAffineOpen.isLocalization_basicOpen); represent res-x = f₀/sⁿ
(IsLocalization.Away.surj), push through germ-D(s): germ-D(s)(f₀/sⁿ-form) =
algebraMap(f₀')·algebraMap(s')⁻ⁿ in the FF via GERM-Z (both f₀ s ∈ Γ(zChart);
germ-D(s)∘res-zChart→D(s) = germ-zChart by the restrict-identity) + map_mul/inv.
Then ord-additivity (ord_P is the valuation's exponent: multiplicative →
ord(product) adds; the file's SmoothPlaneCurve.ord_P-API — check add-lemmas), the
denominator ord-0 (s ∉ maximalIdealAt: hPs means the point is in D(s) ⟹ s
invertible at P — the membership-bridge через the zChart-dictionary), and the
f₀-dichotomy (ON: hspan-transport; OFF: :309).

[SEC-ORD S1-S2c LANDED] (2026-08-17, cont.30ae): inside ord_P_germ_sectionKer_generator:
h1 (fst-hop) + hPz + the ⟨s, hsle, hPs⟩-shrink + hNeD/hNeV'sch instances + h2
(germ-restriction to D(s) via presheaf.germ_res_apply — the |_ₗ⟪⟫ notation is scoped
in TheoremOfSquareField, use the primitive). REMAINING [S3+dichotomy]: (i) the
Away-representation: haveI := hZaff.isLocalization_basicOpen s (Γ(D(s)) =
Localization.Away (of Γ(zChart))); obtain ⟨⟨f₀, n⟩, hrep⟩ := IsLocalization.Away.surj
s (res-to-D(s)-of-transported-f) — hrep : res-x · s^n-image = f₀-image; (ii) apply
germToFunctionField-D(s) to hrep + map_mul + the zChart-germ-reads (germ-D(s) of a
res-from-zChart = germ-zChart via germ_res_apply again; then GERM-Z → algebraMap
CoordRing forms) ⟹ germ-x · algebraMap(s')^n = algebraMap(f₀') in the FF; (iii)
ord_P both sides: ord-additive (the ord_P of the DVR-valuation — find/state the
mul-add lemma: SmoothPlaneCurve.ord_P-API grep: ord_P_mul?? — HasseWeil has
ord_P-arithmetic in the divisor files — projectiveDivisorOf is Finsupp-of-ord ⟹
ord_P_mul exists-or-derive from Valuation.map_mul + the unzero-plumbing); s'-ord-0
via :309-shape (s' ∉ maximalIdealAt P: P ∈ D(s) ⟹ s invertible in the stalk ⟹ the
CoordRing-transport s' has nonzero eval — the zChartMaximalIdeal-membership-bridge:
s ∉ zChartMaximalIdeal W P ⟺ point-in-D(s) — a small bridge-lemma [D-MEM] to state:
zChartPoint W P ∈ basicOpen s ⟺ s ∉ zChartMaximalIdeal W P — via fromSpec/basicOpen
membership = not-in-the-prime, standard AffineScheme API); ⟹ ord(germ-x) = ord(f₀');
(iv) the f₀'-dichotomy: ON (point = section-point): the hspan-transport-chain
pins f₀' up to a unit times the maximal-ideal generator ⟹ ord 1 — the span-supply:
hspan + ker_apply + the Away-localization of the kernel + hrep — the algebra:
localized-J at the point = span(f-image) = span(f₀'-image·s^-n) ⟹ f₀'-spans ⟹
RP-4a-core; OFF: f₀'-eval ≠ 0 at P (else f-vanishes at P through hrep with s-unit ⟹
P in the kernel-locus = the section point, contra) ⟹ :309. Each (iii)/(iv)-piece a
private lemma per the budget rule.

[SEC-ORD S3 LANDED] (2026-08-17, cont.30af): hAway (isLocalization_basicOpen) + xD-set
+ hrep (Away.sec_spec: xD · alg(s^n) = alg(f₀), n := (sec s xD).2, f₀ := (sec s xD).1)
all green. NEXT [S3b]: apply germToFunctionField-D(s) to hrep (map_mul) and identify
germ-of-algebraMap-Γ(zChart)-elements: the Away-algebraMap IS the res-map from
Γ(zChart) (RingHom.algebraMap_toAlgebra via basicOpenSectionsToAffine — check
defeq or find the compat lemma), then germ-D(s)∘res-zChart = germ-zChart
(germ_res_apply) → GERM-Z gives algebraMap-CoordRing forms:
FF-eq: (germ xD) · alg(s')ⁿ = alg(f₀') with s' := coordRingToZSection.symm s,
f₀' := …symm f₀. THEN [S4] ord_P both sides: need ord_P-mul/pow-additivity — grep
SmoothPlaneCurve.ord_P arithmetic (ord_P_mul/ord_P_pow — HasseWeil divisor files;
projectiveDivisorOf-additivity exists since divisors add — find the primitive);
s'-ord-0 via the [D-MEM] bridge (hPs : zChartPoint ∈ D(s) ⟹ s ∉ zChartMaximalIdeal
⟹ s' ∉ maximalIdealAt via the Ideal.map-roundtrip :43) + :309; conclude
ord(germ-x) = ord(alg f₀'). [S5] the dichotomy on f₀' (cont.30ae-(iv)).

[SEC-ORD S3c LANDED] (2026-08-17, cont.30ag): hFFeq proven — the transported germ
satisfies projEquiv(germ-D(s) xD)·alg(s')ⁿ = alg(f₀') in W.toAffine.FunctionField
(s' := coordRingToZSection.symm s, f₀' := …symm (sec s xD).1). Spelling: BARE
`Nonempty (zChart W)` (no ↥ — the ↥-form misses the tree; GERM-Z's own preamble
form). Note h1+h2 tie the STATEMENT's germ to germ-D(s)-xD: statement-LHS-ord =
ord(projEquiv(germ-((inv fst)⁻¹V)…)) = [h2] ord(projEquiv(germ-D(s) xD)).
REMAINING: [S4] ord both sides of hFFeq: need ord_P-mul + ord_P-pow additivity
(grep/derive: SmoothPlaneCurve.ord_P via pointValuation — Valuation.map_mul +
the unzero-additivity; check HasseWeil for ord_P_mul — MulByIntUnramified /
DivisorPullback used sums ⟹ exists-or-quick); s'-ord-0: [D-MEM] hPs ⟹ s ∉
zChartMaximalIdeal (basicOpen-membership = not-in-the-prime under fromSpec:
zChartPoint := fromSpec ⟨zChartMaximalIdeal⟩; mem-basicOpen-fromSpec-iff — the
AffineScheme-API: IsAffineOpen.fromSpec_mem_basicOpen?? grep) ⟹ s' ∉ maximalIdealAt
(Ideal.map-roundtrip of :43) ⟹ ord 0 (:309-shape = ord_P_algebraMap_eq_zero_of_
notMem, ValuationTransport:309) ⟹ ord(germ) = ord(alg f₀'). [S5] dichotomy on f₀'
per cont.30ae-(iv) (the hspan/ker_apply supply + the section-point cases).

[SEC-ORD MICROS LANDED + TWO STORM LESSONS] (2026-08-17, cont.30ah):
secOrd_s_notMem_zChartMaximalIdeal [D-MEM] + secOrd_sPrime_ord_zero [s-unit] both
proven. LESSONS: (1) `h ▸ term` with the motive ranging over a HUGE definition
(zChartMaximalIdeal) storms in kabstract — use `by rw [h]; exact …` (goal-side
rewrite, single occurrence) instead of ▸; (2) PHANTOM LEMMA HAZARD:
Ideal.mem_map_equiv does NOT exist in mathlib — the name resolved into a Sublattice
lemma and stormed unifying; the working route is Ideal.mem_map_of_mem (equiv-as-
FunLike) + apply_symm_apply-rw. Also ord_P arithmetic CONFIRMED STOCKED:
ord_P_mul (Valuation.lean:126), ord_P_pow (:193), ord_P_inv (:170),
ord_P_eq_top_iff (:94). MAIN-decl state: S1+S2+S2c+S3+S3b+S3c green + sorry.
NEXT: in the main — consume s-unit (hs'ord := secOrd_sPrime_ord_zero W P s hPs),
take ord_P of hFFeq (ord_P_mul + ord_P_pow + hs'ord ⟹ ord(germ)+0 = ord(alg f₀')),
handle the ⊤-cases (germ ≠ 0 from hf через the equiv-injectivity), then [S5] the
f₀'-dichotomy (cont.30ae-(iv)) — likely as one more extracted private lemma
(fresh budget; the main is near its ceiling).

[SEC-ORD S4 LANDED — ONLY THE DICHOTOMY LEFT] (2026-08-17, cont.30ai): the main
ord_P_germ_sectionKer_generator is proven modulo ONE goal (the in-place sorry):
ord_P(alg((coordRingToZSection W).symm (Away.sec s xD).1)) = if (inv fst)(zChartPoint
W P) = z(default) then 1 else 0 — with the full context in scope (hspan : z.ker-span
at V, hrep : xD·alg(s^n) = alg(f₀) in Γ(D s), hsle, hPs, hPV, hf, h1, h2, hFFeq,
hordeq). [S5] PLAN: (ON) point-eq case: the section-kernel's stalk at its own point
is the maximal ideal; transport hspan через ker_apply + the localization at the
point (the zChart-side: f₀ spans the AtPrime-localized maximal ideal — derive from
hrep + the s-invertibility + the localized hspan) → mirror RP-4a's hgen-stage
(intValuation_singleton) → ord 1; (OFF) point-ne: f₀ ∉ zChartMaximalIdeal (else,
via hrep + s-unit, xD vanishes at the point ⟹ f vanishes ⟹ the point is in the
kernel-locus = the section point, contra) → :309-species → 0. Both need the
[SEC-STALK-CORE] bridge: the z.ker-vanishing-locus-membership at the zChart-point ⟺
the point-equation (inv fst)(zChartPoint) = z(default) — via the Spec-K-section =
single-closed-point dictionary (cont.30u). Extract [S5] as
secOrd_f0_dichotomy (fresh budget) with the data (z hz V f hspan hf s hsle hPs P
hPV + hrep-shape) — OR prove SEC-STALK-CORE as its own micro first and do the
dichotomy in-place if the main's budget allows (it is near ceiling: prefer extract).

[S5 MATHEMATICAL DERIVATION] (2026-08-17, cont.30aj): the dichotomy's two arguments,
fully derived: KEY-FACT [K-EVAL]: for the Spec-K-section z, ker_apply gives z.ker's
V-ideal = RingHom.ker (z.app V) where z.app V : Γ(V) → Γ(Spec K, z⁻¹V) ≅ K is the
K-EVALUATION at the section point ⟹ the kernel ideal IS the vanishing/maximal ideal
of the section point in Γ(V). (OFF, point ≠ section-point): suppose f₀ ∈
zChartMaximalIdeal W P (vanishes at our point); the alg-f₀-germ vanishes ⟹ by hrep,
xD·alg(sⁿ) vanishes at P; s ∉ the prime (D-MEM/hPs) ⟹ xD's germ ∈ the prime ⟹ f
vanishes at our point ⟹ (by K-EVAL + hspan: f generates the vanishing ideal of
EXACTLY the section point on V) our point = the section point — contradiction ⟹
f₀ ∉ zCMI ⟹ ord 0 (the s-unit-micro's shape at f₀). (ON, point = section-point):
f's germ generates the localized kernel = the localized maximal ideal at the point
(K-EVAL localized: the vanishing ideal localizes to the DVR maximal ideal); by hrep
and s-invertibility-at-the-point, f₀ = f-germ·sⁿ-unit-multiple also generates ⟹
the RP-4a hgen-stage (AtPrime map-span + intValuation_singleton) gives ord 1.
IMPLEMENTATION: extract secOrd_f0_dichotomy with binders (z hz V f hspan hf P +
the shrink data s n f₀ + hrep at the Γ(D s)-level + hPs hPV + the point-eq-if) —
inside: split_ifs; the OFF-case via the contrapositive membership-chase (all at
the Γ(zChart)/prime level — the localization-free part!); the ON-case via the
localized span (mirror RP-4a from the hgen-supply). The membership-chases need:
[VAL-BRIDGE] the germ-vanishing ⟺ prime-membership at basic/chart opens (the
:309-iff ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt-family + the D-MEM-iff)
and [K-EVAL] as its own micro (ker_apply + the Spec-K-eval-read + hspan ⟹ the
f-vanishing-locus on the shrink region = {section point}, stated as: for a point
pt ∈ D(s)-region, f₀-germ-vanishes-at-pt ⟺ pt = section-point).

[S5 DECISIVE SIMPLIFICATION — support_ker + basicOpen ALGEBRA] (2026-08-17,
cont.30ak): mathlib's Hom.support_ker (IdealSheaf/Basic:845): f.ker.support =
closure (range f) — for the Spec-K-section z (closed immersion): z.ker.support =
range z = {z default} (single point!). With mem_supportSet_iff_of_mem (:307):
for q ∈ V: q ∈ zeroLocus(z.ker.ideal V) ⟺ q = z default. THE MEMBERSHIP-IFF-CHAIN
(the whole OFF/ON-membership side is basic-open algebra): f₀ ∉ zChartMaximalIdeal
W P ⟺ [D-MEM-iff] zChartPoint ∈ basicOpen f₀ ⟺ [hPs + hrep + basicOpen_mul +
basicOpen_pow + basicOpen_res: bO(f₀)⊓D(s) = bO(xD)⊓D(s) = bO((inv fst).app f)⊓D(s)]
zChartPoint ∈ bO((inv fst).app f) ⟺ [Scheme.preimage_basicOpen]
(inv fst)(zChartPoint) ∈ basicOpen f ⟺ [hspan + zeroLocus-span + support_ker-chain]
(inv fst)(zChartPoint) ≠ z default. ⟹ OFF-case: point-ne ⟹ f₀ ∉ zCMI ⟹ ord 0
(the s-unit-micro's proof-shape at f₀ — REUSE secOrd_sPrime_ord_zero-generalized:
restate it for ANY t with zChartPoint ∈ basicOpen t — it ALREADY IS that (its hPs-arg
is exactly the membership)! ⟹ OFF = the iff-chain + secOrd_sPrime_ord_zero at f₀!!).
ON-case: point-eq ⟹ supply the hgen-stage directly (z.ker-V-localized at the point =
the max ideal via K-EVAL/AtPrime + hspan + hrep-localized s-unit) and run RP-4a's
second half (intValuation_singleton chain, :225-260 copyable). NEXT WINDOW: (1) the
iff-chain as a micro [BO-CHAIN]; (2) OFF via secOrd_sPrime_ord_zero at f₀; (3) ON
via the localized-span mirror; (4) close SEC-ORD.


## cont.30al — ★ SEC-ORD COMPLETE, AXIOM-CLEAN (session 11)

`ord_P_germ_sectionKer_generator` (OrdPipeline) proven end-to-end, `#print axioms` =
[propext, Classical.choice, Quot.sound]. The S5 dichotomy landed as SEVEN micros:

- **[BO-CHAIN]** `secOrd_f0_mem_basicOpen_iff` — mem bO f₀ ↔ point-off-section. Lessons:
  `Scheme.basicOpen_pow` carries `0 < n` (n = 0 IS possible for Away.sec — case-split via
  `Nat.eq_zero_or_pos`, zero-arm `pow_zero + basicOpen_one + basicOpen_le`); a
  metavar-pattern rw on Γ-section goals can fail where the FULLY-INSTANTIATED
  `have he := lemma (X := ..) (f := ..) (h := ..); rw [he]` succeeds (BO-CHAIN lesson,
  now hit twice); `Scheme.Hom.support_ker` is a SET-level equation (coe inserted on the
  LHS — grab it directly, no congrArg); `mem_zeroLocus_iff`'s conclusion is `∉ basicOpen`.
- **[D-MEM-IFF]** iff-version of D-MEM (same fromSpec chain, both directions defeq-cast).
- **[U-LOC]** `uniformizer_of_localized_span` (ValuationTransport, after RP-4a): RP-4a
  with hgen AT THE DVR LEVEL as hypothesis (`IsLocalRing.maximalIdeal`-spelled — the
  `IsDiscreteValuationRing.maximalIdeal`-spelling needs the DVR instance at statement
  elaboration and FAILS there; convert inside via `show IsLocalRing.maximalIdeal _ = _`).
  NO r ≠ 0 hypothesis — derived from hgen via `IsDiscreteValuationRing.not_a_field` +
  `Ideal.span_singleton_eq_bot`. REGION-SAFETY REMINDER: the hr'-block existed verbatim
  in BOTH RP-4a and U-LOC — a global text-replace hit both (caught at build).
- **[K-MAX]** `secOrd_span_isMaximal` — THE K-EVAL: hz : z ≫ snd = 𝟙 splits z's appLE-to-⊤
  (`appLE_comp_appLE` with middle V.1 + `appLE_top_top_of_eq_id` subst-micro), so
  Γ(V) →+* Γ(SpecK,⊤) ≅ K is surjective; ker-chain: `RingHom.ker_comp_of_injective`
  (ΓSpecIso inj; res-along-⊤=z⁻¹V inj via `Subsingleton.elim (homOfLE e₂) (eqToHom heq.symm)`
  + bijective_of_isIso) + `Scheme.Hom.ker_apply` + hspan; `RingHom.ker_isMaximal_of_surjective`.
- **[PT-KER]** section point ∉ bO f (support_ker + subset_closure — no IsClosedImmersion needed).
- **[SPAN-P']** span{app f} = point's prime (K-MAX transported via
  `(asIso ((inv fst).app V.1)).commRingCatIsoToRingEquiv` + `Ideal.map_isMaximal_of_equiv`
  + map_span; membership via REUSED `mem_basicOpen_iff_notMem_primeIdealOf` — ALREADY IN
  TheoremOfSquareField:1521 (dedup catch: the name clashed at build) + preimage_basicOpen
  + hcase; close `IsMaximal.eq_of_le` + `isPrime.ne_top`).
- **[SPAN-S]** `secOrd_maximalIdeal_stalk_eq_span_germ_f0` — maximalIdeal(stalk at q') =
  span{germ_zChart f₀}. KEY INFRA LESSONS: (a) the preimage chart's AMBIENT elaborates as
  `(modelEllipticCurve W).E` (defeq projModel but NOT reducibly) — spell the instance
  layer in E-form + `show`-bridge, final `rfl` crosses back; (b) `algebra_section_stalk`
  can NOT be found by instance synthesis at a BARE point (the subtype-coe ?x is not
  invertible) — spell stalk-points as `↑⟨q', h⟩` AND provide the algebra as **letI**
  (haveI-fvars are OPAQUE to unification — letI is the fix for DATA instances); the
  AtPrime instance itself is Prop so haveI is fine; (c) `IsLocalization.AtPrime.map_eq_maximalIdeal`
  (general-instance form, AtPrime/Basic:524) + `IsAffineOpen.isLocalization_stalk` +
  `preimage_of_isIso`; (d) germ-collapse via `germ_res_apply` mirrors the hFFeq flow;
  s-germ unit via `RingedSpace.mem_basicOpen` (NO second AtPrime needed);
  `Ideal.span_singleton_mul_right_unit (hunit.pow n)` absorbs the denominator.
- **[HGEN]** `secOrd_ord_f0_eq_one` — ONE-hop transport stalk → localRingAt via
  `IsLocalization.ringEquivOfRingEquiv (coordRingToZSection W).symm
  (primeCompl_map_zChartMaximalIdeal W P)` (stocked!) — do NOT two-hop through
  Localization.AtPrime (algEquiv.commutes dies under simpa → True; spellings blow the
  budget). Computation rule `IsLocalization.ringEquivOfRingEquiv_eq` gives hc pointwise;
  `RingHom.ext fun a => hc a` lifts to comp-level; congrArg-map + map_map + map_span
  chain h9; hround RP-4b-VERBATIM (equiv-form maps — coe-form breaks its simpa);
  hgen via trans-chain NOT `rw [← Localization.AtPrime.map_eq_maximalIdeal]` (dependent
  motive fails: the prime appears in the Localization TYPE); equiv-map vs coe-map
  mismatches cross by `exact`-defeq.
- **[S5-assembly]** in the main: hrep2 := `rw [← halg, ← halg]; exact hrep` (sec_spec has
  the pow INSIDE algebraMap — no map_pow); by_cases hcase; ON := secOrd_ord_f0_eq_one;
  OFF := BO-CHAIN.mpr + secOrd_sPrime_ord_zero AT f₀. The main gained
  `[IsClosedImmersion z]` (BO-CHAIN needs isClosedEmbedding for the support read) —
  consumers must supply it (sections of separated morphisms are closed immersions;
  discharge at ORD-G time).

NEXT: [G-REL] (cont.30w — the per-chart H-germ identity; u-germs = generator ratios;
constructive r := c₀-generator-ratio) → [ORD-G] (Finsupp.ext; chart dichotomy feeds
THIS SEC-ORD result; κ-orientation watch cont.30p) → [L1-assembly] (FieldLeaf:2340) →
L3/L5 activate → E4a-diagonal → leaves A+B.


## cont.30am — ORD-G/L1 INVENTORY (session 11, post-SEC-ORD)

**STOCKED AND AXIOM-CLEAN (all verified via #print axioms this session):**
- `exists_const_mul_of_projectiveDivisorOf_eq` (FieldLeaf) ✓
- `HasseWeil.WeilPairing.DivisorPullback.projectiveDivisorOf_pullback_eq_pullbackDivisor`
  (needs hcore + [Finite ker]) ✓
- `HasseWeil.WeilPairing.DivisorPullback.projOrdTransport_mulByInt` ✓ (hcore discharged!)
- `HasseWeil.WeilPairing.weilFunction_divisor_eq_pullbackDivisor_kappaDivisor` ✓
- `brick6_intertwining` (MulByHomDegree:1146) — THE L4-iii [N]-COMPARISON IS PROVEN:
  projModelFFEquiv ∘ (mulByHom N).functionFieldMap = mulByInt_pullbackAlgHom ∘ projModelFFEquiv,
  modulo instances [Flat] [IsFinite] [LocallyOfFinitePresentation] on mulByHom N (check their
  discharge sites — the KM-engine receipts should provide them; grep brick6 consumers).
- SEC-ORD `ord_P_germ_sectionKer_generator` ✓ (this session).
- DIV-PIN `divisorOf_algebraMap_eq_single_of_span` (ValuationTransport:483) ✓ (session 8).
- G2′ `exists_normalized_chart_dataset_perChart` (GlueDataset:798) — its ∃-output ALREADY
  CARRIES THE SPAN-SUPPLY: (V, f₁, f₂ span-generators of J₁/J₂ per chart c) + (ch : chart
  assignment) + (A i unit-dressings) + hnorm + hWch + per-overlap (u₁, u₂) with
  t_ij = A_i·(u₂u₁⁻¹)·A_j⁻¹ AND res f₁(ch i) = res f₁(ch j)·u₁, res f₂(ch i) = res f₂(ch j)·u₂.
- kappa-structure: kappa Q = (sectionToPicRel …).1 = picRelProj (picClass(sectionDivisor Q-sec)
  · picClass(sectionDivisor zero-sec)⁻¹) (SelfAdjointN:198 + DivisorClass:180);
  sectionDivisor.ideal = Scheme.Hom.ker z.

**THE FOUR MISSING PIECES for the L1 sorry (OrdPipeline:188):**
- **A [L1-SIG]**: extend exists_const_mul_weilFunction's hypotheses with the G2′-extras
  (V, f₁, f₂, ch, A, span/nonzd-facts, hWch, u-facts) + the two section-morphism span-links
  (zQm := Q-composite section, z0m := baseChangeZero, with (ker zQm).ideal (V c) = span {f₁-or-f₂}
  — κ-ORIENTATION (cont.30p): which of J₁/J₂ is the Q-side at the E4a-instantiation, fix when
  deriving e_dict from hM). Thread the SAME extras through the :1246-consumer
  (torsionSplittingEval→weilPairing theorem — it takes the same abstract dataset and passes it
  to L1 verbatim). The E4a-call-site later invokes G2′ to supply everything.
- **B [G-REL]**: the germ-ord decomposition at a place P over chart i: from hsplit (j := c₀) +
  germToFunctionField-hops: germFF(h c₀) = germFF(h i) · (mulByN).functionFieldMap-of-FF-germ
  (tUOC i c₀)⁻¹ [needs functionFieldMap for mulByN: IsDominant ✓ mulByHom_isDominant exists
  (MulByHomDegree, used at :1520)]; then tUOC-decomposition (G2′-u-facts) + ord-additivity +
  sectionUnits-elements have ord 0 at… (hn/hnorm-facts: h i is a UNIT on [N]⁻¹(Wc i) ⟹ its
  FF-germ has ord_P 0 for P over chart i — germ-of-unit is stalk-unit ⟹ RingedSpace.mem_basicOpen-
  style ⟹ ord 0 via :309-shape; A i similarly on Wc i) + u-germs = f-generator ratios (the
  G2′-u-relations at germ level) ⟹ ord_P(H_HW) = ord-difference formula in SEC-ORD-terms.
- **C [PT-DICT]**: the point dictionary: SEC-ORD's indicator [(inv fst)(zChartPoint P) = z.base
  default] ↔ the HW-arithmetic [N]•P-HW = T-shape. Ingredients: projModelPointsEquiv_zsmul
  (MulByHomDegree:75), the p/hxp-pattern (overPoint-composite = p.1), fst-vs-mulByN compat
  (mulByN := (E.baseChange t).mulByHom N; need fst ∘ mulByN-pullback = E-side mulByHom ∘ fst —
  grep CurveNaturality/pastingMap_mulByN + KMPairing mulByN_comp_snd :342). Also
  pullbackDivisor_apply's exact fibre-shape (DivisorPullback — read it) to match the
  Finsupp.ext-pointwise target.
- **D [∞-ORD]**: the ∞-place: zChartPoint/maximalIdealAt only cover AFFINE P (∞ ∉ zChart).
  The HW-∞ corresponds to the ZERO-SECTION image; div-H's ∞-coefficient = the zero-section-chart
  SEC-ORD read through the ∞-dictionary (kappaDivisor T = single T − single ∞?? — CHECK
  kappaDivisor's def (HasseWeil PicZero:232) + how DivisorPullback handles ∞
  (inftyOrdTransport_mulByInt)). Possibly needs an ∞-analogue of SEC-ORD on the y-chart
  (projModelYChart machinery in TheoremOfSquareField — mem_basicOpen_iff_notMem_primeIdealOf
  came from there, so the y-chart affine-dictionary exists).

**[R-DEF]**: r := transported (f-ratio at c₀): r := projEquiv-image of germ-ratio — div r via
DIV-PIN needs GLOBAL maximalIdealAt-spans — but f₁/f₂ c₀-spans are CHART-spans (V c₀) — the
divisorOf-single :483 needs the global span?? NO — re-check :483's exact hypotheses; if global,
r's div needs its own pointwise computation (same SEC-ORD machinery at the two sections,
applied at the c₀-chart data — r = f₂c₀-germ/f₁c₀-germ with div = [P_Q]−[P_0] pointwise
by SEC-ORD at zQm and z0m!) — NO new machinery: div r (w) = SEC-ORD-zQ-indicator −
SEC-ORD-z0-indicator at w for w over V c₀; away from V c₀ use the u-relations to re-express —
hmm, r is ONE global FF-element; its ord at P NOT over V c₀ still needs computing — the
u-relations give f-c₀-germ = f-(ch i)-germ · u-germ⁻¹-ish beyond the overlap ⟹ ord-formula
everywhere ✓ same G-REL mechanism. DESIGN [R-DIV] alongside B.

**ORDER OF WORK**: A (mechanical threading; unblocks stating B/C/D against the enriched
signature) → B+R-DIV (the germ-ord engine) → C → D → [L1-END assembly].

**[N]-COMPAT PIN (cont.30am addendum)**: `EllipticCurve.mulByHom_baseChange_fst E t (N : ℤ) :
mulByN E t N ≫ pullback.fst E.π t = pullback.fst E.π t ≫ E.mulByHom (N : ℤ)` EXISTS (used in
CurveNaturality.pastingMap_mulByN:77). Consequences: (i) PB-side dominance of mulByN derivable
(mulByN = fst ≫ mulByHom ≫ inv fst from the square + fst iso; dominant-composite); (ii) the
C-dictionary's scheme-side [N]-to-E-side hop is this square; (iii) G-REL-1's
(mulByN).functionFieldMap conjugates to (mulByHom).functionFieldMap via functionFieldMap_comp
on the square, meeting brick6 on the E-side. Also `baseChangeZero_pastingMap` (zero-sections
paste) at CurveNaturality:63. mulByHom takes the ℤ-arg (N : ℤ)-coercion.

**[PT-0 PIN] (cont.30am addendum 2)**: `Proj_fromSpec_awayToSection_awayι` (PoleFiltration:2253)
bridges `IsAffineOpen.fromSpec` and `Proj.awayι` chart machineries — the [PT-0] zChartPoint-vs-
chartSpecPoint dictionary routes through it + `chartHomEquiv_eq_of_specMap` (WeierstrassModel:793)
+ `eq_chartSpecPoint_of_projModelPointsEquiv_some` (MulByHomDegree:762). Session-11 additional
landings beyond SEC-ORD: [B-0] mulByN_id_isDominant, [G-REL-1] mulByN_functionFieldMap_germ_transitionUnit,
[U-ORD0] ord_P_germ_unit_section, [G-REL-3] germToFunctionField_eq_mul_of_res_rel,
[N-CONJ] pullbackCurveFunctionFieldEquiv_mulByN — all axiom-clean. DIV-H term-plan: unit-parts
avoid PT-DICT (same-chart U-ORD0); tUOC goes whole through N-CONJ + the proven pointwise
ProjOrdTransport; only the post-transfer chart-memberships at [N]P need PT-DICT.

**[DIV-H VOCABULARY PINS] (cont.30am addendum 3, session 11 end-of-window)**:
- `projectiveDivisorOf f = (divisorOf f).toProjective + single ∞ (ordAtInfty f).untopD 0`
  (ProjectiveDivisor:217); `projectiveDivisorOf_apply_affine : (projDiv f)(affine P) =
  (ord_P P f).untopD 0` — SEC-ORD's ord_P is literally the affine coefficient.
- `projOrdAt f (some x y h) = (ord_P ⟨x,y,h⟩ f).untopD 0` (DivisorPullback:75/77).
- `pullbackDivisor_apply (f hf D w) : pullbackDivisor f hf D w =
  D ((f w.toAffinePoint).toProjectiveSmoothPoint)` — UNIFORM all places (:200).
- `kappaDivisor T = single T.toProjectiveSmoothPoint 1 − single infinity 1` (PicZero:232).
- ProjOrdTransport (proven for mulByInt): `projectiveDivisorOf (φ.pullback h) w =
  projOrdAt h (φ w.toAffinePoint)` — the pointwise [N]-transfer.
- THE [DIV-H-w] OBLIGATION: div(H_HW)(w) + div r (([N]w).toProj) = kappaDivisor T (([N]w).toProj),
  proven per-place: w affine over [N]⁻¹Wc-chart-i → G-REL-1(i,c₀) + U-ORD0 + N-CONJ +
  the transfer + tUOC-decomposition (hu) + G-REL-3 + SEC-ORD at zQm/z0m with PT-0/PT-1
  chart-memberships; w = ∞ or [N]w = O → the [D]-rung (y-chart/zero-section).
- PT-DICT CORE LANDED: PT-0a (ker_chartSolutionHom = transported maximalIdealAt, 4 micros),
  PT-0 (chartSpecPoint-base = zChartPoint, 4 micros), PT-1 (mulByHom_base_zChartPoint).
  Lessons: coercion-ascriptions in Ideal.map storm (bare equiv!); Ideal.map_map is
  RingHom-only (rfl-coe-step first); IsIso (awayToSection) via inferInstanceAs on
  basicOpenIsoAway.hom; letI for defs-with-inner-haveI in show-defeq; Point-coe targets
  (modelEllipticCurve W).E (E-ambient lesson extends to Point-coes).

**[κ-ORIENTATION RESOLVED] (cont.30ap, session 11)**: the cont.30p watch is SETTLED by
computing the DIV-H ledger (shorthand: f-ords at the [N]P-point, a := ord(A_c₀-germ)):
D := T-DEC-ord(tUOC i c₀) = (f₂ords: (O_i − O_c)) − (f₁ords: (T_i − T_c)) − a under the
FINAL assignment **hspan₁ : ker zQm-spans (f₁ = Q-side ⟹ f₁-ord = [pt = T]-indicator),
hspan₂ : ker z0-spans (f₂ = zero-side ⟹ [pt = O]-indicator)**; ord H = −D (DIV-H-i);
**rr := pE(germ f₁ chc₀) · pE(germ f₂ chc₀)⁻¹ · pE(germ A c₀-val)⁻¹** has
ord@[N]P = T_c − O_c − a; then ord H + ord rr = T_i − O_i = κ@[N]P ✓ ON THE NOSE (the
A-terms and both c₀-tails cancel). Flip applied to the three signatures + skeleton
(25bf897f5 → this commit). REMAINING for hDIVW-fill: [DIV-H-AFF] the affine-arm micro
(assemble DIV-H-i + N-CONJ + the ProjOrdTransport pointwise transfer + T-DEC + U-RATIO
+ SEC-ORD×4 (f₁/f₂ at chi/chc₀) + U-ORD0 (A_i) + PT-1 memberships + untopD-arithmetic),
the [N]P = 0 / w = ∞ arms ([D]-rung), and the T-zero-case of the dictionary.

**[SOME-ARM FINAL PINS] (cont.30aq)**: `projModelZero_not_preimage_zChart` (WeierstrassModel:1205)
+ baseChangeZero-fst-leg (`pullback.lift_fst`: z0 ≫ fst = t ≫ zero; t = 𝟙 ⟹ = modelEllipticCurve.zero)
⟹ the z0-side SEC-ORD indicator vanishes at every affine place (zero-image avoids the zChart) —
matching κ's [affine ≠ ∞]. PT-2 chain complete (116373f9f): basePointCast_zsmul (subst-transport;
rw-on-▸ is motive-fragile — use exact), CAST-INJ, ns-reverse, mulByHom_base_zChartPoint_of_smul
(Point-typed pmod via set — SpecPoints has no SMul). 27 engine pieces; 3 sorries left
(AFF-some, AFF-zero, hDIVW-∞).

**[D-RUNG DESIGN LOCKED] (cont.30ar)**: `projectiveDivisorOf_degree_eq_zero`
(NormValuation:2278, [IsAlgClosed][IsIntegrallyClosed CR][IsElliptic]) is CLOSED ⟹
the ∞-ARM (w = ∞) is pure degree-arithmetic ONCE all affine arms hold: from
div-H + pb-rr = pb-κ at every affine w (some+zero arms) + degree-0 of div H (principal),
deg(pb D) = #ker·deg D with deg κ = 0 (kappaDivisor_degree) and deg div-rr = 0:
div-H(∞) + pb-rr(∞) = −Σ-affine(LHS) = −Σ-affine(RHS) = pb-κ(∞). Needs a
[DEG-SPLIT] micro (degree = ∞-coeff + affine-sum; projectiveDivisorOf_degree IS this
split for div-forms; pullbackDivisor-side via pullbackDivisor_apply + degree-lemmas).
The ZERO-ARM (w affine, [N]w = 0) needs ordAtInfty(Y := pE(germ tUOC)) — via ITS
degree-relation: ordAtInfty-Y = −Σ-affine-ords-of-Y (projectiveDivisorOf_degree_eq_zero
at Y + projectiveDivisorOf_degree) — the affine-sum of Y-ords: Finsupp-support-sum with
the ledger values — OR the direct ∞-family (y-chart mirror: chartYRingEquiv
PoleFiltration:1571 + projModelZero-point; a session-scale RP-∞-programme). PREFER the
degree-relation route for Y (one sum-computation) — the sum-over-places of the
SEC-ORD-indicator-differences telescopes to fibre-counts; alternatively keep the
zero-arm as the LAST sorry and reassess. Priority: D-2 (some-arm finale) first.


## cont.30as — SESSION-11 FINALE: the affine engine COMPLETE, L1 at 2 sorries

**FULL LIBRARY GREEN** (lake build ModularCurves, 0 errors). `exists_const_mul_weilFunction`
is proven modulo exactly TWO sorries, both ∞-places: the divH_affine_arm ZERO-arm
([N]P = 0 at an affine place) and the hDIVW INFINITY-arm (w = ∞).

**THE [INF]-PROGRAMME (the remaining [D]-rung, next session):**
1. [INF-VAL] the y-chart-stalk valuation IS ordAtInftyValuation: define w := the
   DVR-intValuation of the stalk at z∞ := projModelZero.base default over the yChart
   (projModelYChart PoleSheafModel:28; isLocalization_stalk; the smooth-point-DVR),
   comapped to FF through the identification; compute w(x_gen) = exp 2, w(y_gen) = exp 3,
   w(constants) = 1 (the infChart coordinate arithmetic — chartYRingEquiv
   PoleFiltration:1571; projModelZero_eq_fromSpec :2267); close by the anchor
   `eq_ordAtInftyValuation_of_x_y` (the inftyOrdTransport_mulByInt technique).
2. [INF-SEC-ORD] ordAtInfty(pE(germ-V f)) = [z∞ = z.base default]-indicator for
   section-kernel generators: SPAN-S at z∞ (the stalk-span machinery is section-generic)
   feeds [INF-VAL] directly: maximalIdeal(stalk-at-z∞) = span{germ f₀} ⟹ w = exp(−1)
   ⟹ ordAtInfty = 1; off-section: stalk-unit ⟹ 0.
3. [INF-U-ORD0] units over z∞-containing opens: stalk-unit ⟹ w-value 1 ⟹ ord 0.
4. The arms' assembly = the some-arm patterns at ∞ (ZERO-arm: z0-indicator TRUE at ∞,
   zQm = [T=0], the ∞-ledger + omega; INFINITY-arm: G-REL-1 at a z∞-chart +
   INF-U-ORD0 + N-CONJ + the PROVEN InftyOrdTransport + the ledger).

Session-11 total: ~40 green commits; every landing pushed; the affine divisor engine
(SEC-ORD + L1-skeleton + PT-dictionary + both dictionary-arms) complete.

**[INF-VAL COORDINATE PINS] (cont.30as addendum)**: the y-chart (t,s)-coordinates
(infChartCubic PoleFiltration:377: s³ + a₂ts² + (a₄t²−a₁t)s + (a₆t³−a₃t²−t), monic in s):
z∞ = (t,s) = (0,0); the cubic-relation rearranges to t·(1 + a₃t + a₁s − a₆t² − a₄ts − a₂s²)-ish
= s³-forms ⟹ in the z∞-stalk t = s³·unit ⟹ the stalk is a DVR with uniformizer s;
w(s) = exp(−1), w(t) = exp(−3); x_gen = s/t (w = exp 2 ✓), y_gen = 1/t (w = exp 3 ✓) —
matching the eq_ordAtInftyValuation_of_x_y anchor. The generator-read stock:
chartYRingEquiv_isLocalizationElem (PoleFiltration:1595: the X₁X₂-localization elem ↦
infChartTElem); sectionUnitElem (:3684) may be the 1+…-unit already. The z∞-prime =
⟨s,t⟩-image = ker(evaluation-at-(0,0)) — K-MAX-style via the augmentation infChartAug
(:3728 — the (0,0)-evaluation hom?!) — CHECK infChartAug's def first next window.

**[INF-VAL STOCK-FIND] (cont.30as addendum 2)**: the ∞-uniformizer algebra is ALREADY
BUILT in PoleFiltration (:3680-3750, the T-W7.0i pole-sheaf work): `sectionUnitElem`
(U ≡ 1 mod (s,t)), `tel_mul_sectionUnitElem` (t·U = s²·(s + a₂t) — THE t~s³-relation),
`sectionUnitElem_sub_one_mem`, `infChartAug` (the (0,0)-evaluation with root/poly-lemmas),
`infChart_root_relation`. The [INF]-session ASSEMBLES rather than builds: the z∞-prime =
ker(infChartAug ∘ chartYRingEquiv-forms) [K-MAX-shape]; the stalk-DVR-uniformizer = s
(t = s³·unit via tel_mul + U-invertibility-near-the-section); w(x_gen/y_gen)-values via
the yChart-fraction-reads; the anchor closes [INF-VAL]; then INF-SEC-ORD/INF-U-ORD0
via the SPAN-S-at-z∞ mirror; then the two arms per the some-arm patterns.

**[D-RUNG COLLAPSE] (cont.30at — MAJOR)**: `ord_P_negSmoothPoint_translateAlgEquivOfPoint_eq_ordAtInfty_some`
(TranslateOrdInfty:440, PROVEN): ord_P(−T)(τ_T f) = ordAtInfty f for ANY affine T = (xk,yk)
and f ≠ 0. ⟹ THE ∞-ARMS REDUCE TO THE AFFINE ENGINE: pick any affine T₀; then
ordAtInfty(engine-term) = ord_{−T₀}(τ_{T₀}(term)); and τ_{T₀} ∘ pE = pE ∘ (scheme-translation-♭)
(the U5c-2 bridge `functionFieldMap_translateBy` FieldComparisonBridge:372 — pE intertwines
translateByIso with translateAlgEquivOfPoint) ⟹ τ-images of the germ-terms are germs of the
TRANSLATED dataset ⟹ [INF-U-ORD0] = U-ORD0 at the translated unit; [INF-SEC-ORD] = SEC-ORD
at the translation-conjugated section (z' := τ-scheme ∘ z with ker-conjugation). Remaining
work = the τ-dataset plumbing (translateByPoint app-action on germs, section conjugation,
membership transports — the L2e machinery family). NO new valuation theory needed.

**[D-EXECUTION CHAIN] (cont.30at addendum — all pieces PROVEN & axiom-clean)**:
ordAtInfty(pE(germ-U x)) = ord_{−T₀}(τ_{T₀}(pE(germ-U x)))   [TranslateOrdInfty:440 ✓]
  = ord_{−T₀}(pE(translateByPoint-♭(germ-U x)))              [EQUIV-TAU = pullbackCurveFunctionFieldEquiv_translateByPoint, OrdPipeline:2395 ✓ proven in-file]
  = ord_{−T₀}(pE(germ-τp⁻¹U (τp.app x)))                     [functionFieldMap_germToFunctionField ✓]
then the AFFINE ENGINE at P := −T₀: U-ORD0 for units (τp.app-of-unit is a unit ✓);
SEC-ORD for the τ-conjugated section-kernels (ker(τ-scheme ∘ z)-spans = τp.app-images
of the spans — the ideal-pullback along the iso τp); memberships via the τp-point-action
(−T₀-pt ∈ τp⁻¹U ⟺ τp(−T₀) = z∞ ∈ U — the PT-2-analogue for translateBy via
projModelPointsEquiv_add MulByHomDegree:54 + the translateBy-point-action). T₀-supply:
any affine point (alg-closed existence) + IsDominant-translateByPoint (an iso — derive);
thread as ∃-obtained INSIDE the arms (no L1-SIG growth) or reuse the p-data when T≠0.
CAUTION: τp for the arms is the translateBy at T₀-generic — the EQUIV-TAU's binders
(P' pS hxpS τp hτp [IsDominant]) must be instantiated at the T₀-dataset — construct
P'₀ := the (baseChange).Point of T₀ via the dictionary (basePointCast-preimage).

**[TAU-INSTANTIATION ANALYSIS] (cont.30au)**: EQUIV-TAU's binders (P' pS hxpS τp hτp
[IsDominant]) need for the arms' T₀: (i) when T := basePointCast(equiv p) is AFFINE —
instantiate with the L1's OWN (p, hxp)-data (T₀ := T; the −T-point is affine; the
zero-arm and ∞-arm ledgers run the affine engine at −T with the τ-conjugated dataset);
(ii) when T = 0 — τ_T unavailable; pick T₀ := the place-P itself via pmod :=
chartSpecPoint(P.x, P.y) (dictionary-value ✓ projModelPointsEquiv_chartSpecPoint);
the GAP: hxpS₀ — the overPoint-composite-identity ((overPoint … P'₀ ≫
baseChangeIdFstOver).left = pmod.1) for P'₀ := pmod-as-Point — likely provable
(pointEquivOverHom-def + fst-projection unfold; grep pointEquivOverHom readouts /
Point.asSection GroupLaw:244) but is its own micro [OVERPT]. NEXT WINDOW ORDER:
[OVERPT] micro → the τ-conjugated U-ORD0/SEC-ORD wrappers → the two arms' ledgers
(some-arm patterns). Also: IsDominant (translateByPoint) — derive from iso (grep
IsIso-translateBy); the τp-app-germ-push is stocked (functionFieldMap_germToFunctionField).

**[TAU-PT ROUTE] (cont.30au addendum)**: [OVERPT] LANDED (toBaseChangePoint +
overPoint_toBaseChangePoint_comp_fst + specMap_algebraMap_self_eq_id). The [TAU-PT]
point-action route: work at the (baseChange)-Point-𝟙 level: Q₀ := toBaseChangePoint(pmodA),
P'₀ := toBaseChangePoint(pmodT); `overPoint_comp_translateBy` (Translation:172) + rfl-lefts
⟹ Q₀.1 ≫ translateByPoint P'₀ = (Q₀ + P'₀).1; base-at-default + PT-0 gives the τp-action
on (inv fst)(zChartPoint A)-points. THE REMAINING LINK: (Q₀ + P'₀) vs toBaseChangePoint
(pmodA + pmodT) — toBaseChangePoint-additivity OR the stocked `Point.baseChangeEquiv`
(GroupLaw:411, an ≃+ between (E.baseChange σ).Point t and E.Point (t ≫ σ)) with the
g-typing collapse (Spec.map-alg = 𝟙 propositionally — specMap_algebraMap_self_eq_id +
a Point-transport). Alternatively prove toBaseChangePoint-add directly (the lift-of-sums:
both sides are pullback.lifts of the same E-side data — pullback.hom_ext + lift_fst/snd +
the E-side add-composite… the E-side sum's .1-realization needs the E-Point-add-def —
routes through the same Hom-group — CHECK Point.asSection-additivity-lemmas first (the
asSection-family may carry them: grep asSection.*add)). THEN [TAU-SEC-ORD]/[TAU-U-ORD0]
wrappers + the two arms.

**[WRAPPER PINS COMPLETE] (cont.30av)**: the τ-toolkit is done (OVERPT, asSection_add′,
CAST-G, FST-INV, TAU-PT, TAU-PT-ZERO, TAU-ISO — all green, HEAD 64a8954b9). The
[TAU-U-ORD0]-recipe is fully pinned in the sentinel (the bridge at (xt,yt,ns) +
EQUIV-TAU at toBaseChangePoint/OVERPT-data + the germ-push + U-ORD0 at negSmoothPoint
with the TAU-PT-ZERO-membership via pmodneg := chartSpecPoint(xt, negY xt yt) and the
neg-dictionary = map_neg). negSmoothPoint (TranslationOrd:48) and Point.neg_some
(mathlib, rfl) stocked. [TAU-SEC-ORD]: same chain with the conjugated section
zc := z ≫ (translateByPoint)⁻¹ (section-property via translateByPoint_comp_snd +
iso-inv; the ker-transport along the iso-app — design the span-supply at write-time,
the SPAN-P′-pattern). Then the ZERO-arm and INF-arm ledgers (some-arm patterns;
z0-at-∞-indicator TRUE; κ(∞) = [T-proj = ∞] − 1).

**[TAU-U-ORD0 LANDED] (cont.30aw)**: `tau_ordAtInfty_germ_unit` GREEN (55f44592c) — the
first ∞-ord computation through the collapsed D-chain, validating the entire τ-machinery:
the bridge (hbr RE-ASCRIBED at the ⟨W⟩-spelling — W_smooth-vs-⟨W⟩ defeq-not-syntactic!)
+ EQUIV-TAU at (toBaseChangePoint pmodT, OVERPT-hxpS, τE with rfl-hτp, iso-dominances)
+ the −T-membership via TAU-PT-ZERO (pmodneg := chartSpecPoint(xt, W-negY) Point-ASCRIBED
(SpecPoints has no +!); the neg-dictionary-sum-zero: neg_some-rw then RFL closes the
negY-spelling-gap (bc-coefficients are defeq to W's!); toBaseChangePoint_eq_asSection
crossing) + the germ-push + U-ORD0. TEMPLATE FOR [TAU-SEC-ORD]: same chain with
SEC-ORD at the τ-conjugated section — remaining design: the conjugated-section
ker-span-supply (zc := z ≫ (τPB)⁻¹-inverse-forms; its ker-ideal at τ⁻¹V = the τ.app-image
of ker-z's at V — the SPAN-P′-transport-pattern along the iso-app; OR observe SEC-ORD's
INPUT is just (z, hz-section, hspan) — CONJUGATE THE WHOLE DATA: zc's span at τ⁻¹V-charts
:= Ideal.map (τ.app V) (span f) = span (τ.app f) via the iso — the K-MAX-style transport).
Then the ZERO-arm ledger (all values now computable at ∞: f₂/z0-SEC-ORD-value = 1 via
TAU-SEC-ORD (the ∞-pt IS the z0-image ⟹ the indicator-TRUE-case of the conjugated
SEC-ORD), f₁/zQm-value = [T=0], A/u-values via TAU-U-ORD0 + the ratio-machinery) and
the INF-arm.

**★★★ [L1 COMPLETE AXIOM-CLEAN] (cont.30ax, 49da67420)**: `exists_const_mul_weilFunction`,
`torsionSplittingEval_eq_weilPairing`, `torsionSplittingEval_self_eq_one` ALL verified
[propext, Classical.choice, Quot.sound]. OrdPipeline.lean is SORRY-FREE. The final wave
(this session): [TAU-U-ORD0] (unit germs at ∞ = 0) → [KER-CONJ] (section-kernel span
conjugation along an automorphism — generic {X Y : Scheme}; comp_app-rfl + app_eq +
congr_app roundtrips + element chase; Scheme.Hom-namespace for comp_app/app_eq/congr_app/
id_app) → [TAU-SEC-ORD] (kernel-generator germs at ∞ = section indicator; open scoped
Classical for the ite; hoist the IsIso-τ haveI OUT of by-blocks) → [ORD-LEDGER-∞]
(7-term ledger with per-factor nonzeros for ordAtInfty_mul) → [PT-2-ZERO] (N-torsion
chart point ↦ zero-section image) → [AFF-ZERO-ARM] (divH_affine_arm_zero as a SPLIT
DECL — the 200k heartbeat budget is per-decl and the parent was full; hand-write the
helper signature, never extract_goal on a monster context) → [Z∞-FIX] (mulByN fixes the
∞-point: N•zero-Point = zero + point_smul_eq_comp_mulBy + fst-conjugation) → [HORD-∞]
(the ordAtInfty mirror of ord_H_eq_neg_ord_transition through tau_ordAtInfty_germ_unit)
→ [DIV-H-INF] (divH_infinity_arm: pushed place ∞→∞ via toAffinePoint_infinity+map_zero;
THE τ-POINT FOR THE ∞-ARM = ANY affine point, existing by smoothPoint_infinite since K
is alg-closed — import HasseWeil.Foundation.Curves.Fiber.GenericFiber; the T-split +
finales copy the zero-arm VERBATIM — same hledZ shapes vt+vb+{1,0}+vc = 0+1+va, htrYZ
v1 = vt via InftyOrdTransport untopD-eq). NEXT: the L1-consumers — L3/L5 (the E4a plan
doc chain) → E4a-diagonal → leaves A (weilPairingEval_self) + B
(weilPairingEval_nondegenerate). Leaf C (IsOfficialCartier.isFinite) separate.

**[U1-CAMPAIGN WAVE 2] (cont.30bb-30bc, af0fffc87)**: after L1, the U1-transport campaign
(weilPairingEval_mapIso, gating U5-AC) is 9/11 green: Point.mapIso+killedBy,
zero_comp_left_of_isMonHom, PB-ISO (pullbackMapIso+legs+zero-compat), ASSEC-MAPISO,
KER-MAPISO (ker_comap_iso), SECTIONCLS-MAPISO, ZEROCLS-MAPISO, KAPPA-MAPISO,
HM/HNORM-MAPISO, MULBYN-PBISO, UMAP-SQ, RES-UMAP-RES, and the TSE-MAPISO skeleton
(E6-d mirror; hn′/hC/assembly green). REMAINING: the 2 hsplit′-branch collapses
(mixed inf-preimage spellings blow isDefEq — fix = rfl-show spelling normalization
then RES-UMAP-RES application; pinned in sentinel) + the (g)-pin. KEY-LESSONS:
per-decl 200k-budgets (split big arms as private theorems with hand-written
signatures); the TWO-π-projection-path split (direct-field vs toEllipticCurveGeom)
makes rw/simp miss across files — congrArg-term-chains cross by defeq; open MonObj
steals ι; KMNaturality is rw-friendly, SelfUniversal is not.

**★★ [U1 COMPLETE AXIOM-CLEAN] (cont.30bd, d526b32bc)**: `weilPairingEval_mapIso`,
`torsionSplittingEval_mapIso`, `kappa_mapIso` all [propext, Classical.choice, Quot.sound].
The full U1-transport campaign (11 pieces) is green: the pairing is invariant under
pointed record isos over the same base. Final pieces this wave: TSE-MAPISO branch
collapses (typed-le-haves + RES-UMAP-RES — explicit args eliminate the unifier search;
the mixed inf-preimage spelling crossed by one by-exact le_of_eq) and the (g)-pin
(weilPairingEval_eq_weilPairingKM ×2 + weilPairingKM_congr at Subtype.ext-crossings +
KM-pins at the F-dataset and its PB-ISO pullback + TSE-MAPISO.symm + case-closers for
the ▸-mem side-goals; localPullbackTrivializationT needs the Scheme.Modules-FQN in
SelfUniversal). NEXT: U5-AC — weilPairingEval_self_of_field: at K alg-closed:
exists_projModelIso_of_field → Φ pointed-iso → U1-transport to the model → the dataset
(kappa-dict + G2′) → L4-plumbing (weilPairingEval_eq_torsionSplittingEval) → L5
(torsionSplittingEval_self_eq_one); then the K→K̄ descent (Γ-injectivity). Then U4,
assembly, leaf A.

**★★★ [U5-AC COMPLETE AXIOM-CLEAN] (cont.30be, cc08f5789)**: `weilPairingEval_self_of_isAlgClosed`
(SelfField.lean, sorry-free) — [propext, Classical.choice, Quot.sound]. e_N(x,x) = 1 over any
algebraically closed field with (N:K) ≠ 0, for ANY elliptic-curve record E. The assembly:
stage-1 model transport (exists_projModelIso_of_field + Over.isoMk + isMonHom_of_pointed +
mapIso_killedBy + ← weilPairingEval_mapIso); stage-2 record-level instances; stage-3 the
dataset (exists_module_kappa + nonempty_tensorObj_sectionIdeal_iso_zeroIdeal_of_field +
sectionDivisor_isOfficial.locallyPrincipal ×2 + the terminal-separation/affine-diagonal
chain + exists_normalized_chart_dataset_perChart); stage-4 the D4-pipe splittings + the
SpecPoints p (term-mode component) + the ξ-torsion-transfer hT (baseChangeEquiv.trans
pointCongr; local copies of the cast micros); stage-5 QC/ICI on the section +
translateByIso-dominance + the chart choice + L4-pin + L5-close through ΓSpecIso-injectivity.
DEBUG-LESSONS: the zQm-instance-keys need a set-FVAR-ATOM (haveI at any spelling of
Subtype.val-terms misses — set zQm := … then haveI : P zQm); the hxiQ show was a SILENT
sorryAx (memory-pattern tells: uses-sorry + tactic-does-nothing + never-executed) — fixed
by the hξdef/AddEquiv.trans_apply/apply_coe rw-chain; ALWAYS #print axioms after assembly.
SESSION-TOTAL: THREE campaigns landed axiom-clean — L1 (the E4a ord-engine), U1 (mapIso
transport), U5-AC (the field leaf). REMAINING for leaf A: [U5-DESCENT] (K→K̄:
weilPairingEval_restrict along Spec K̄ → Spec K + Γ-injectivity of the field extension +
(N:K̄)≠0-transport — fills SelfUniversal weilPairingEval_self_of_field), [U4] (tautTorsionPoint
rfl-sorries + the universal vanishing: affine/ℤ-flat/N-inverted-reduced route), [assembly]
(weilPairingEval_self' via U2-localModel + U1 + U3-gluing + U4), then wire Basic:372.

**★★★ [U5 COMPLETE AXIOM-CLEAN] (cont.30bf, b0d8a54fd)**: `weilPairingEval_self_of_field'`
(SelfField.lean) — e_N(x,x) = 1 over **any** field with N invertible, [propext,
Classical.choice, Quot.sound]. Route: U5-AC (alg-closed) + the descent = [GAMMA-INJ]
(`injective_appTop_specMap`, ΓSpecIso-naturality conjugation) + `weilPairingEval_restrict`
+ the **BC-SWAP campaign** (7 pieces in KMNaturality: `bcSwapIso` (the identity-pullback
collapse), sectionCls/zeroCls/kappa/hM/hnorm-bcSwap, the mulByN + UMAP squares,
`torsionSplittingEval_bcSwap`, `weilPairingKM_bcSwap`) + `asSection_eq_bcSwap`.
New reusable micros: `sectionEval_congr_morphism`, `resUnit_unitsMap_app_resUnit`,
`map_mul_inv_transport` (abstract CommGroup transport — the cheapest fix for calc
blowups on giant scheme terms), `injective_appTop_specMap`.
REMAINING for leaf A: **U4** (SelfUniversal: tautTorsionPoint rfl-sorries + the universal
vanishing over X_N: affine / ℤ-flat / N-inverted-reduced route, fully specified in the
U4a–U4f notes above) and the **assembly** (`weilPairingEval_self'` = U2-localModel + U1 +
U3-gluing + U4 + U5), then wire `Basic.lean:372`; `AlternationReduction` then closes
leaf A. NOTE: SelfUniversal's own `weilPairingEval_self_of_field` sorry is now redundant —
the real theorem lives in SelfField (primed name); wire or delete at assembly time.

**[U4 ROUTE REFINED — scheme-side, cont.30bg]**: the tensor-chain of the original U4d/U4f
notes is superseded. New route, all tools verified present:
1. `X_N` affine (U4a ✓), its ring `ℤ`-flat (U4b/U4c ✓), so `N` is a nonzerodivisor there
   (`natCast_mem_nonZeroDivisors_universalTorsionRing` ✓) — this gives the **injectivity**
   of restriction to the basic open `D(N) ⊆ X_N` (RegularSectionDensity's
   `Localization.Away.ker_algebraMap_eq_bot` / `ker_basicOpenι_eq_bot` machinery).
2. `D(N)` is the torsion over the `N`-inverted base, so `torsionπ` there is **étale**;
   its **geometric** fibres are the torsion rings of the fibre curves, reduced by
   `isReduced_torsion_sections_of_field` (U4d-i ✓ landed) + `torsion_baseChange_isPullback`
   (TorsionFibre:251) ⟹ `GeometricallyReduced`.
3. `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` (mathlib,
   Geometrically/Reduced.lean:109) + `Flat` (étale) + reduced/noetherian base ⟹
   `IsReduced D(N)`.
4. The universal value `u` satisfies: `u - 1` vanishes in every residue field of `D(N)`
   (U4e: `weilPairingEval_restrict` + `weilPairingEval_self_of_field'` ✓ + the
   BC-SWAP/asSection plumbing already built for U5-DESCENT) ⟹ `basicOpen (u-1) = ⊥` ⟹
   `eq_zero_of_basicOpen_eq_bot` (mathlib Properties.lean:179) ⟹ `u = 1` on `D(N)` ⟹
   `u = 1` on `X_N` by step 1.
Then the assembly (U2 classification + U1 + U3 + U4) closes leaf A.

**★★★ [U4 REDUCED-BASE FORM COMPLETE AXIOM-CLEAN] (cont.30bh, 900b8717e)**:
`weilPairingEval_self_of_reduced` (SelfUniversalVanishing.lean) — over ANY reduced base on
which `N` is invertible, e_N(x,x) = 1, for any record and any N-torsion point.
[propext, Classical.choice, Quot.sound]. Pieces: U4a `isAffine_torsion_universal`;
U4b `flat_universalTorsionRing`; U4c `flat_int_weierstrassAtlasRingU` +
`flat_int_universalTorsionRing` + `natCast_mem_nonZeroDivisors_universalTorsionRing`;
U4d `isReduced_torsion_sections_of_field` + `geometricallyReduced_torsionpi` +
`isReduced_torsion`; U4e `evaluation_eq_fromSpecResidueField` +
`weilPairingEval_self_evaluation_eq_one`; U4f `eq_zero_of_forall_evaluation_eq_zero` +
`eq_one_of_forall_evaluation_eq_one`; plus the SelfField extraction
`weilPairingEval_self_of_pointOverField` (the point-over-a-field leaf, the U4e engine).
REMAINING for leaf A over an ARBITRARY base: the universal-family step — classify (E, x)
by a map into X_N, pull the universal value back, and evaluate it by U4-reduced on the
N-inverted locus plus the schematic-density injection.

**[U4-REGULAR + DENSITY] (cont.30bi, e1eb8fa24)**: `injective_res_basicOpen_of_nonZeroDivisor`
(affine sections inject into the basic open of a nonzerodivisor) and
`weilPairingEval_self_of_nonZeroDivisor` (over an AFFINE base where `N` is a nonzerodivisor
and the `N`-inverted locus is reduced, e_N(x,x) = 1) — both axiom-clean. This is the form
the universal family consumes: `X_N` is affine (U4a), `N` is a nonzerodivisor on its ring
(U4c), and `D(N) subset X_N` is the torsion over the `N`-inverted atlas, reduced by
`isReduced_torsion` (U4d). What remains for leaf A: (i) instantiate at the universal
`(X_N, tautTorsionPoint)` to get the universal value = 1 — needs `IsReduced (D(N))` for
the universal X_N, i.e. identify `D(N)` with the torsion over `Spec A[1/N]` (base-change of
the torsion along the open immersion, `torsion_baseChange_isPullback`); (ii) the
classification/gluing step: every `(E, x, hx)` over `T` is locally a pullback of the
universal one, so its value is the pullback of 1 (via `weilPairingEval_restrict` + U1);
(iii) wire `weilPairingEval_self'` and `Basic.lean:372`.

**★★★ [U4 COMPLETE — THE UNIVERSAL VALUE IS 1] (cont.30bj, b1ede9c62)**:
`weilPairingEval_self_universal_eq_one` — the diagonal pairing value of the tautological
point over the universal N-torsion base is 1, [propext, Classical.choice, Quot.sound].
The chain: `isReduced_basicOpen_natCast_torsion` (the N-locus of any torsion base is
reduced: preimage_basicOpen + torsion_baseChange_isPullback range identification +
isoOpensRange transport) + `natCast_mem_nonZeroDivisors_universalTorsionRing` +
`weilPairingEval_self_of_nonZeroDivisor` (affine base, N regular, reduced N-locus).
LEAF A now needs ONLY the classification/gluing step: every (E, x, hx) over T is locally
the pullback of the universal pair, so its value is the pullback of the universal 1.
Ingredients present: `localModel` (U2), `classifyRingHomU` +
`universalWeierstrassLocU_map_classifyRingHomU`, `pointToTorsion` (T ⟶ X_N),
`weilPairingEval_restrict` (U3), `weilPairingEval_mapIso` (U1), and the model
base-change iso `modelBaseChangeIsoAsOver`.
