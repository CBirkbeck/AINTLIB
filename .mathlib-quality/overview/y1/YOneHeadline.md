# /overview Phase-1 inventory — Y₁(N) headline files

Scope (read in full, branch `main`, 2026-07-12):
1. `projects/ModularCurves/ModularCurves/ModularCurve/YOneTatePoint.lean` (1,436 lines)
2. `projects/ModularCurves/ModularCurves/ModularCurve/YOneAssembly.lean` (802 lines)
3. `projects/ModularCurves/ModularCurves/Moduli/Representability.lean` (206 lines)

Conventions: "Used by" is scoped to these three files (declaration-level users; external
project users noted under Notes where load-bearing). "Uses from project" lists
ModularCurves-project dependencies (mathlib lemmas are named inside **How** where they carry
the argument). CODE-sorry means an actual `sorry` term in code — prose mentions in
docstrings/comments do NOT count. Line counts are whole-declaration (docstring excluded).

---

## 1. ModularCurve/YOneTatePoint.lean (1,436 lines)

Import spine: `YOneAtlasClassify`, `EllipticCurve/MulByHomEtale`, `YFullRoute`.
File-level: `attribute [local instance] MvPolynomial.gradedAlgebra` (L38); no `set_option`;
no CODE-sorry (verified — grep hits at L25/L30/L1370 are docstring prose only).

#### `exists_tatePoint` (L66–75)
- **Type**: theorem
- **What**: Y1-B2 = L-ATLAS master atlas leaf (Loeffler Cor 3.3.5 at scheme level): there is a marked point `P₀` of the universal Tate curve, nowhere of geometric order ≤ 3, such that every `(Y, P)` in `Ell/R` with `P` nowhere of order ≤ 3 arises from a **unique** `Ell/R`-morphism to the atlas by pulling back `P₀`.
- **How**: term-mode anonymous constructor — witness `tateMarkedPoint R`; first conjunct `tateMarkedPoint_nowhereGeomOrderLEThree`; classifying ∀-clause `MarkedChartData.tateMarkedPoint_classifies` (YOneAtlasClassify, PR #5225).
- **Hypotheses**: `R : CommRingCat.{u}`.
- **Uses from project**: [tateUniversal, tateMarkedPoint, tateMarkedPoint_nowhereGeomOrderLEThree, EllipticCurve.NowhereGeomOrderLEThree, tateEllObj (YOneAssembly); EllObj/EllHom (Moduli/EllCategory); EllHom.pullSection (Moduli/Representability); MarkedChartData.tateMarkedPoint_classifies (ModularCurve/YOneAtlasClassify)]
- **Used by**: [tatePoint, tatePoint_nowhereGeomOrderLEThree, tatePoint_classifies]
- **Visibility**: public — **Lines**: 66–75 (proof 4 lines, term mode)
- **Notes**: statement byte-identical to its former YOneAssembly site (v10.117 relocation); the former `sorry` was DISCHARGED by relocation. Docstring records the v10.152 axiom audit `{propext, Classical.choice, Quot.sound}`.

#### `tatePoint` (L80–81)
- **Type**: noncomputable def
- **What**: the marked point `(0,0)` of the universal Tate curve, extracted as `(exists_tatePoint R).choose`.
- **How**: `Exists.choose`. — **Hypotheses**: `R`.
- **Uses from project**: [exists_tatePoint, tateUniversal (YOneAssembly)]
- **Used by**: [tatePoint_nowhereGeomOrderLEThree, tatePoint_classifies, yOneSet, yOneBase, factors_yOne_iff_exists_range, factors_yOne_iff, yOne_representableBy, yOne_isAffine, yOneStructMap_locallyOfFinitePresentation, pullAsSection_dict, exists_tateAlgLift_core, yOne_infinitesimal_lifting] (≥12 users — key API)
- **Visibility**: public — **Lines**: 80–81

#### `tatePoint_nowhereGeomOrderLEThree` (L85–87)
- **Type**: theorem — **What**: opaque interface: the marked point is nowhere of order ≤ 3 (Loeffler p. 13 display).
- **How**: `(exists_tatePoint R).choose_spec.1`. — **Hypotheses**: `R`.
- **Uses from project**: [exists_tatePoint, tatePoint, NowhereGeomOrderLEThree (YOneAssembly)]
- **Used by**: [factors_yOne_iff (L215), exists_tateAlgLift_core (L834, L915)]
- **Visibility**: public — **Lines**: 85–87

#### `tatePoint_classifies` (L91–94)
- **Type**: theorem — **What**: opaque interface: the classifying universal property of the marked atlas (Loeffler Cor 3.3.5).
- **How**: `(exists_tatePoint R).choose_spec.2`. — **Hypotheses**: `R`.
- **Uses from project**: [exists_tatePoint, tatePoint, tateEllObj, NowhereGeomOrderLEThree, EllHom.pullSection]
- **Used by**: [yOne_representableBy (L309, L318), exists_tateAlgLift_core (L845, L947)]
- **Visibility**: public — **Lines**: 91–94

#### `yOneSet` (L102–105)
- **Type**: def
- **What**: underlying set of `Y₁(N)` inside `Y_N`: complement of `⋃_{d ∣ N, 4 ≤ d < N}` of the preimages of the ranges of `killedLocusπ d` (Loeffler Def 3.3.6 with his exact index set).
- **How**: set complement of a `Finset`-indexed biUnion over `N.properDivisors.filter (4 ≤ ·)`.
- **Hypotheses**: `R`, `N : ℕ`.
- **Uses from project**: [EllipticCurve.killedLocus, killedLocusπ (YOneAssembly), tateUniversal, tatePoint]
- **Used by**: [yOneSet_isOpen, yOneOpens, factors_yOne_iff_exists_range, factors_yOne_iff, yOne_isAffine] (5 — key API)
- **Visibility**: public — **Lines**: 102–105

#### `yOneSet_isOpen` (L109–114)
- **Type**: theorem — **What**: Y1-C5: `Y₁(N)` is open in `Y_N`.
- **How**: complement of a finite union of closed sets — `isClosed_biUnion_finset`, `IsClosed.preimage`, and `killedLocusπ_isClosedImmersion → isClosedEmbedding.isClosed_range`.
- **Hypotheses**: `R`, `N`. — **Uses from project**: [yOneSet, killedLocusπ, killedLocusπ_isClosedImmersion (YOneAssembly), tatePoint]
- **Used by**: [yOneOpens, yOne_isAffine] — **Visibility**: public — **Lines**: 109–114

#### `yOneOpens` (L117–118)
- **Type**: noncomputable def — **What**: `Y₁(N)` as an open of `Y_N`: `⟨yOneSet, yOneSet_isOpen⟩`.
- **How**: anonymous constructor. — **Hypotheses**: `R`, `N`.
- **Uses from project**: [yOneSet, yOneSet_isOpen, killedLocus, tatePoint]
- **Used by**: [yOne, yOneBase, factors_yOne_iff_exists_range, yOne_representableBy, yOne_isAffine, yOneStructMap_locallyOfFinitePresentation] (6 — key API)
- **Visibility**: public — **Lines**: 117–118

#### `yOne` (L124–125)
- **Type**: `@[reducible]` noncomputable def — **What**: **the scheme `Y₁(N)` over `R`** = `(yOneOpens R N).toScheme` (Loeffler Def 3.3.6).
- **How**: `Opens.toScheme`. `@[reducible]` so `yOne R N` unifies with `↑(yOneOpens R N)` without whnf (mirrors `@[reducible] tateBase`, v10.72(b)).
- **Hypotheses**: `R`, `N`. — **Uses from project**: [yOneOpens]
- **Used by**: [yOneBase, yOneStructMap, yOneEllObj, factors_yOne_iff_exists_range, factors_yOne_iff, yOne_representableBy, yOne_isAffine, yOneStructMap_isAffineHom, yOne_infinitesimal_lifting, yOneStructMap_smooth] (10+ — key API)
- **Visibility**: public — **Lines**: 124–125

#### `yOneBase` (L129–130)
- **Type**: noncomputable def — **What**: locally closed inclusion `Y₁(N) ⟶ 𝒴` (open into `Y_N`, closed into `𝒴`): `(yOneOpens).ι ≫ killedLocusπ`.
- **How**: composite. — **Hypotheses**: `R`, `N`.
- **Uses from project**: [yOne, yOneOpens, killedLocusπ, tateUniversal, tatePoint, tateBase]
- **Used by**: [yOneStructMap, factors_yOne_iff_exists_range, factors_yOne_iff, yOne_representableBy, yOne_infinitesimal_lifting] (5 — key API)
- **Visibility**: public — **Lines**: 129–130

#### `yOneStructMap` (L133–134)
- **Type**: noncomputable def — **What**: structure morphism `Y₁(N) ⟶ Spec R` = `yOneBase ≫ tateStructMap`.
- **How**: composite. — **Hypotheses**: `R`, `N`. — **Uses from project**: [yOneBase, tateStructMap (YOneAssembly)]
- **Used by**: [yOneEllObj, yOneStructMap_isAffineHom, yOneStructMap_locallyOfFinitePresentation, yOne_infinitesimal_lifting, yOneStructMap_smooth, yOne_representable_smooth_affine] (6 — key API)
- **Visibility**: public — **Lines**: 133–134

#### `yOneEllObj` (L141–144)
- **Type**: noncomputable def — **What**: `Y₁(N)` with its universal elliptic curve as an `EllObj R` (curve = base change of `tateUniversal` along `yOneBase`) — Loeffler's Remark after Def 3.3.6.
- **How**: structure literal. — **Hypotheses**: `R`, `N`.
- **Uses from project**: [yOne, yOneStructMap, yOneBase, tateUniversal + `.baseChange` (EllipticCurve record API), EllObj]
- **Used by**: [yOne_representableBy, gammaOneNaive_representable_assembly, yOne_representable_smooth_affine] (3 — key API)
- **Visibility**: public — **Lines**: 141–144

#### `factors_yOne_iff_exists_range` (L152–168)
- **Type**: theorem — **What**: Y1-D1 open-factoring split: `t : T ⟶ 𝒴` factors through `Y₁(N)` iff it factors through the closed `Y_N` with topological image inside the open `yOneSet`.
- **How** (proof ~14 lines): forward — precompose with `(yOneOpens).ι` and compute the range via `Scheme.Opens.range_ι` and `Set.range_comp`; backward — `IsOpenImmersion.lift` + `IsOpenImmersion.lift_fac`.
- **Hypotheses**: `R`, `N`, `t : T ⟶ tateBase R`.
- **Uses from project**: [yOne, yOneBase, yOneOpens, yOneSet, killedLocus(π), tateUniversal, tatePoint, tateBase]
- **Used by**: [factors_yOne_iff] — **Visibility**: public — **Lines**: 152–168

#### `factors_yOne_iff` (L181–268)
- **Type**: theorem
- **What**: Y1-D1, the locus ↔ functor comparison (the "by construction" core of Loeffler Def 3.3.6): `t` factors through `Y₁(N)` iff the pulled-back marked point is a naive `Γ₁(N)` structure on the pulled-back Tate curve.
- **How** (proof ~82 lines): through `factors_yOne_iff_exists_range`. Forward: the global `N`-kill from `killedLocus_spec` + `zsmul_asSection_pull_eq_zero_iff`; fibrewise clause 2b by contradiction — a killing multiple `a < N` yields a proper divisor kill via `exists_properDivisor_smul_eq_zero`, split into `d ≤ 3` (killed by `tatePoint_nowhereGeomOrderLEThree`) and `d ≥ 4` (transported to the residue fibre by `pull_smul_eq_zero_iff_residue` + `mem_killedLocus_range_iff` and contradicting `yOneSet`-membership). Backward: rebuild `g` by `killedLocus_spec`, and rule out membership in a removed `Y_d` by passing to the geometric point `Spec (AlgebraicClosure (T.residueField x))` and `zsmul_pull_baseChange_asSection_iff`.
- **Hypotheses**: `[NeZero N]`, `hN : 4 ≤ N`, `hinv : IsUnit (N : R)`, `t : T ⟶ tateBase R`.
- **Uses from project**: [factors_yOne_iff_exists_range, yOneSet, yOne, yOneBase, tatePoint, tatePoint_nowhereGeomOrderLEThree; from YOneAssembly: killedLocus_spec, zsmul_asSection_pull_eq_zero_iff, zsmul_pull_baseChange_asSection_iff, smul_eq_zero_iff_comp_mulByHom, pull_smul_eq_zero_iff_residue, mem_killedLocus_range_iff, exists_properDivisor_smul_eq_zero; IsNaiveGammaOne (LevelStructure/Basic); Point.pull/asSection (EllipticCurve API)]
- **Used by**: [yOne_representableBy (the D2+D1 bridge), yOne_infinitesimal_lifting (L1046, L1268)]
- **Visibility**: public — **Lines**: 181–268 — **Notes**: proof >30 lines (~82).

#### `yOne_representableBy` (L282–328)
- **Type**: theorem
- **What**: Y1-D3, representability half of T-E7: `(Y₁(N), universal curve, (0,0))` represents the naive `Γ₁(N)` moduli problem — `Nonempty ((gammaOneNaiveProblem R N).RepresentableBy (yOneEllObj R N))`.
- **How** (proof ~46 lines): `bridge` = `isNaiveGammaOne_pullSection_iff` (NaiveProblems) trans `(factors_yOne_iff …).symm`; `e2` = `Equiv.ofBijective` between pairs `(g : X ⟶ tateEllObj, factorisation h)` and naive `Γ₁(N)` sections, injective by the `tatePoint_classifies` uniqueness clause + `cancel_mono (yOneBase)` (mono since closed ∘ open immersion), surjective by classifier existence + the bridge; `homEquiv := EllObj.homPullbackAlongEquiv.trans e2`; naturality by `EllHom.pullSection_comp`.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`.
- **Uses from project**: [gammaOneNaiveProblem + isNaiveGammaOne_pullSection_iff (Moduli/NaiveProblems), EllObj.homPullbackAlongEquiv (Moduli/QuotientProblem), IsNaiveGammaOne.nowhereGeomOrderLEThree + killedLocusπ_isClosedImmersion (YOneAssembly), EllHom.pullSection + pullSection_comp (Representability), tatePoint_classifies, factors_yOne_iff, yOneEllObj, yOneBase, yOneOpens, tateEllObj, pullbackAlongπ (EllCategory/QuotientProblem)]
- **Used by**: [representableBy_smooth_isAffineHom, gammaOneNaive_representable_assembly, yOne_representable_smooth_affine] (3 — key API)
- **Visibility**: public — **Lines**: 282–328 — **Notes**: proof >30 lines (~46).

#### `killedLocus_preimage_isOpen` (L357–453)
- **Type**: theorem
- **What**: Y1-E1 clopen split (gate [BB-DIFF], now proven): with `N` invertible on `S` and `d ∣ N`, each sub-killed-locus `{d•P = 0}` is **open** inside `{N•P = 0}` (as well as closed). Generic in `E : EllipticCurve S`, `P`.
- **How** (proof ~94 lines): classify the tautological `d`-multiple point of `Y_N` into the torsion via `pointToTorsion` (`gd`); the zero section `zT` of the étale torsion family is an open immersion — `torsionπ_etale'` (Loeffler Lemma 3.4.2(2)) + mathlib `AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal` + `Limits.pullback_lift_diagonal_isPullback` + `MorphismProperty.of_isPullback`; identify `range zT = (torsionι)⁻¹(range zero)` and, via `AlgebraicGeometry.Scheme.Pullback.range_fst`, the target preimage with `gd ⁻¹' (range zT)`; conclude by `IsOpenImmersion.isOpen_range` + continuity.
- **Hypotheses**: `S`, `E`, `P`, `[NeZero N]`, `NIsInvertible S N`, `d ∣ N`.
- **Uses from project**: [killedLocus(π), killedLocus_spec, smul_eq_zero_iff_comp_mulByHom, point_zero_val, point_smul_eq_comp_mulBy (record API); pointToTorsion(_torsionπ/_torsionι), torsionι_isClosedImmersion (EllipticCurve/TorsionFibre); torsionπ_etale' (EllipticCurve/MulByHomEtale); mulByHom_π, zero_π, NIsInvertible]
- **Used by**: [yOne_isAffine (L483)] — **Visibility**: public — **Lines**: 357–453 — **Notes**: proof >30 lines (~94); longest E-track leaf outside the E5 pair; `/decompose-proof` candidate.

#### `yOne_isAffine` (L460–507)
- **Type**: theorem — **What**: Y1-E2: `Y₁(N)` is affine (derived — Loeffler's `Spec` display is verbatim only for `N = 5`; QUOTE-PARTIAL note).
- **How** (proof ~46 lines): `Y_N` affine (closed immersion into the affine `tateBase`, `isAffine_of_isAffineHom`); `N` invertible on the atlas by transporting `hinv` along `algebraMap` + `Scheme.ΓSpecIso`; `yOneSet` clopen (open by construction, closed since each removed locus is open by `killedLocus_preimage_isOpen`); a clopen of an affine scheme is an idempotent basic open — `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`, transported through `X.toSpecΓ` (iso) and `toΓSpec_preimage_basicOpen_eq`; `IsAffineOpen.basicOpen` closes.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`.
- **Uses from project**: [killedLocusπ_isClosedImmersion, killedLocus, yOneSet, yOneSet_isOpen, yOneOpens, killedLocus_preimage_isOpen, tateRingOver, tateBase, tatePoint, NIsInvertible]
- **Used by**: [yOneStructMap_isAffineHom, yOneStructMap_smooth] — **Visibility**: public — **Lines**: 460–507 — **Notes**: proof >30 lines (~46).

#### `yOneStructMap_isAffineHom` (L511–514)
- **Type**: theorem — **What**: Y1-E3: the structure morphism of `Y₁(N)` is an affine morphism.
- **How**: source affine (`yOne_isAffine`) + target `Spec R` affine, `HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)`.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`. — **Uses from project**: [yOne_isAffine, yOneStructMap]
- **Used by**: [representableBy_smooth_isAffineHom, yOne_representable_smooth_affine] — **Visibility**: public — **Lines**: 511–514

#### `yOneStructMap_locallyOfFinitePresentation` (L524–548)
- **Type**: theorem — **What**: Y1-E4: `Y₁(N) ⟶ Spec R` is locally of finite presentation (over general `R`, fp is the right form for `RingHom.Smooth`).
- **How** (proof ~24 lines): zero section lfp by cancellation — `LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType` with `zero_π` and `Smooth π` from `SmoothOfRelativeDimension.smooth (n := 1)`; `Y_N ⟶ 𝒴` = pullback of the zero section (`MorphismProperty.pullback_fst`); open immersion lfp; `tateStructMap` = Spec of `R → R[A,B] → R[A,B][Δ⁻¹]` — `RingHom.FinitePresentation.comp` + `IsLocalization.Away.finitePresentation` + `MvPolynomial.algebraMap_eq`; `MorphismProperty.comp_mem` assembles.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`.
- **Uses from project**: [tateUniversal (π, zero, zero_π), killedLocusπ, yOneOpens, tateStructMap, tateCurveOver, tatePoint]
- **Used by**: [yOneStructMap_smooth] — **Visibility**: public — **Lines**: 524–548

#### `exists_section_lift_of_smooth` (L553–606)
- **Type**: theorem
- **What**: E5/E6 shared plumbing: sections of a smooth morphism from an affine scheme to an affine base lift along nilpotent thickenings — the Γ–Spec transport of `Algebra.FormallySmooth.lift`.
- **How** (proof ~52 lines): factor `f` through `X.toSpecΓ` (`Scheme.toSpecΓ_naturality` + `Scheme.isoSpec_Spec_hom`, the `hftri` triangle); read `s₀` as a `B`-algebra map `q₀` via `Spec.preimage` + `Spec.map_injective`; get `Algebra.FormallySmooth ↑B ↑Γ(X,⊤)` from `Smooth f` by `MorphismProperty.cancel_left_of_respectsIso` + `HasRingHomProperty.Spec_iff (P := @Smooth)`; lift with `Algebra.FormallySmooth.lift`/`comp_lift`; both triangle identities by `Spec.map_comp` bookkeeping.
- **Hypotheses**: `X` affine, `f : X ⟶ Spec B` smooth, `I : Ideal B` nilpotent, `s₀` a section mod `I`.
- **Uses from project**: [] (pure mathlib content over scheme/ring API)
- **Used by**: [exists_tateAlgLift_core (L729)] — **Visibility**: public — **Lines**: 553–606 — **Notes**: proof >30 lines (~52); fully generic — `/mathlibable` candidate.

#### `pullAsSection_dict` (L610–621)
- **Type**: private theorem — **What**: `baseChangeEquiv` dictionary at any base point: `bcEquiv s τ (pull τ (asSection s (pull s P₀))) = pull (τ ≫ s) P₀`.
- **How** (proof ~7 lines): `Subtype.ext`, `Point.baseChangeEquiv_apply_coe`, `Point.asSection_val_fst`.
- **Hypotheses**: `s : T' ⟶ tateBase R`, `τ : T ⟶ T'`.
- **Uses from project**: [Point.baseChangeEquiv/pull/asSection (EllipticCurve API), tateUniversal, tatePoint, tateBase]
- **Used by**: [exists_tateAlgLift_core (L923), yOne_infinitesimal_lifting (L1264 ×2)]
- **Visibility**: private — **Lines**: 610–621

#### `pullSection_pullbackAlongπ` (L627–637)
- **Type**: theorem — **What**: `pullSection (pullbackAlongπ g) P = asSection g (pull g P)` — companion to `YFull.pullSection_asSection` (the `pullbackAlongMap` case), stated generically in `X : EllObj R`.
- **How** (proof ~8 lines): `Subtype.ext` + `Limits.pullback.hom_ext`; `isPullback.lift_fst` and `asSection_val_fst`.
- **Hypotheses**: `X : EllObj R`, `g : T ⟶ X.base`, `P : X.curve.Section`.
- **Uses from project**: [EllHom.pullSection (Representability), EllObj.pullbackAlongπ (QuotientProblem), Point.asSection/pull]
- **Used by**: [exists_tateAlgLift_core (L946)] — **Visibility**: public — **Lines**: 627–637

#### `bcEquiv_zsmul` (L642–646)
- **Type**: private theorem — **What**: `baseChangeEquiv` commutes with ℤ-scalars, concrete-hom form (avoids `AddMonoidHomClass`-with-metavariable synthesis timeouts under heavy import closures).
- **How**: `map_zsmul (….toAddMonoidHom)`. — **Hypotheses**: generic `E`, `σ`, `t`, `n : ℤ`.
- **Uses from project**: [Point.baseChangeEquiv] — **Used by**: [exists_tateAlgLift_core (L707, L737, L815, L922), yOne_infinitesimal_lifting (L1182, L1249–1262)]
- **Visibility**: private — **Lines**: 642–646

#### `bcEquiv_zero` (L648–651)
- **Type**: private theorem — **What**: `baseChangeEquiv 0 = 0`, concrete-hom form.
- **How**: `map_zero (….toAddMonoidHom)`. — **Uses from project**: [Point.baseChangeEquiv]
- **Used by**: [exists_tateAlgLift_core, yOne_infinitesimal_lifting (same sites as bcEquiv_zsmul)]
- **Visibility**: private — **Lines**: 648–651

#### `bcEquiv_nsmul` (L653–657)
- **Type**: private theorem — **What**: `baseChangeEquiv` commutes with ℕ-scalars.
- **How**: `map_nsmul`. — **Uses from project**: [Point.baseChangeEquiv]
- **Used by**: [] — **UNUSED anywhere (private ⇒ dead code)**
- **Visibility**: private — **Lines**: 653–657 — **Notes**: delete-candidate.

#### `exists_tateAlgLift_core` (L664–970)
- **Type**: private theorem
- **What**: Y1-E5 pure core: an atlas algebra map to `A⧸I` whose marked point is `N`-killed lifts — after renormalisation through the classifying morphism of the lifted torsion point — to an atlas algebra map to `A` with `N`-killed marked point. Ring-level interface (keeps the caller's `letI` diamonds outside).
- **How** (proof ~305 lines): étale torsion-point lift against the nilpotent `I`. (i) `N` invertible on `Spec A` ⟹ `torsionπ` of the base-changed universal curve is étale + finite (`torsionπ_etale'`, `torsionπ_isFinite_of_nIsInvertible`), hence the torsion scheme is affine; (ii) transport the killed `A⧸I`-point into a section of the torsion via `torsionPointsEquiv` and `baseChangeEquiv` (`bcEquiv_zsmul/zero`); (iii) lift the section along the thickening by `exists_section_lift_of_smooth`; (iv) the lifted point `PA := asSection … PT` is `N`-killed (`asSection_zsmul`) and nowhere of order ≤ 3 — the order condition transports because every geometric point of `Spec A` factors through `Spec (A⧸I)` (nilpotents die in fields: `Ideal.Quotient.lift` of `Spec.preimage τ`), reducing to `tatePoint_nowhereGeomOrderLEThree`; (v) classify `(pullbackAlong t, PA)` through `tatePoint_classifies`, extract the algebra map by `Spec.preimage`; clause (b) `N`-kill via ℤ-linearity of `pullSection` (`EllHom.pullSection_add`, `map_zsmul` on `AddMonoidHom.mk'`); clause (a) reduction mod `I` by classifier **uniqueness**: both `ι₀ ≫ fc` and the tautological projection classify the restricted point (`YFull.pullSection_asSection`, `pullSection_pullbackAlongπ`, `pullAsSection_dict`), so they agree, and `Spec.map_injective` closes.
- **Hypotheses**: `N` with `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`; `A` an `R`-algebra, `I` nilpotent; `ψ₀r`, `ψ` with `mk I ∘ ψ = ψ₀r`; `N` unit in `A`; marked point of `ψ₀r` `N`-killed.
- **Uses from project**: [exists_section_lift_of_smooth, pullAsSection_dict, pullSection_pullbackAlongπ, bcEquiv_zsmul/zero, tatePoint(+_classifies, _nowhereGeomOrderLEThree), tateEllObj, tateUniversal, tateBase, tateStructMap, tateRingOver, NowhereGeomOrderLEThree; torsionπ_etale' (MulByHomEtale), torsionπ_isFinite_of_nIsInvertible, torsionPointsEquiv, torsionι (TorsionFibre); tateBaseSpecMap(+_tateStructMap) (YOneAtlasClassify); EllHom.pullSection_add (NaiveProblems); YFull.pullSection_asSection (YFullRoute); EllObj.pullbackAlong/pullbackAlongMap/pullbackAlongπ (QuotientProblem); record API point_smul_eq_comp_mulBy, point_zero_val, NIsInvertible]
- **Used by**: [yOne_infinitesimal_lifting (L1159)]
- **Visibility**: private — **Lines**: 664–970 — **Notes**: proof >30 lines (~305 — the longest in all three files); prime `/decompose-proof` target.

#### `yOne_infinitesimal_lifting` (L992–1272)
- **Type**: theorem
- **What**: Y1-E5 = Loeffler Thm 3.4.4's proof body: points of `Y₁(N)` lift along nilpotent thickenings of affines over `R`.
- **How** (proof ~280 lines, guided by the 40-line in-proof "E5 EXECUTION LEDGER" comment): (1) classify `t₀ := f₀ ≫ yOneBase` into an `R`-algebra map `ψ₀` via `Spec.preimage`, with naive structure from `factors_yOne_iff`; (2) lift coefficients `(α₀, β₀)` arbitrarily (`Ideal.Quotient.mk_surjective`) — `Δ(α,β)` unit since unit mod nilpotent (`IsNilpotent.isUnit_quotient_mk_iff`); (3) build the raw lift `ψ := tateRingOverAlgLift R α β hΔ` (identities `tateRingOverAlgLift_X_zero/_X_one`, extensionality `tateRingOver_algHom_ext`); (4) the core lift `exists_tateAlgLift_core` produces the renormalised `ψ'` (restriction = `ψ₀`, marked point `N`-killed); (5) naive structure of `t' := tateBaseSpecMap R ψ'`: killing via `baseChangeEquiv` bookkeeping, fibrewise clauses transported from `hstruct₀` because geometric points of `Spec A` factor through `Spec (A⧸I)` (`Ideal.Quotient.lift`, `pullAsSection_dict` bridge); (6) land in `Y₁(N)` by `factors_yOne_iff`; restriction and over-triangles by `cancel_mono (yOneBase)` (mono: closed ∘ open immersion).
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`, `φ : R ⟶ of A`, `I` nilpotent, `f₀` over the quotient.
- **Uses from project**: [exists_tateAlgLift_core, factors_yOne_iff, pullAsSection_dict, bcEquiv_zsmul/zero, yOneBase, yOne, yOneStructMap, tatePoint, tateUniversal, tateStructMap, tateBase, tateCurveOver, tateRingOver, killedLocusπ_isClosedImmersion, zsmul_asSection_pull_eq_zero_iff (YOneAssembly); tateRingOverAlgLift(+_X_zero/_X_one), tateRingOver_algHom_ext, tateBaseSpecMap(+_tateStructMap) (YOneAtlasClassify); IsNaiveGammaOne]
- **Used by**: [yOneStructMap_smooth (L1327)]
- **Visibility**: public — **Lines**: 992–1272 — **Notes**: proof >30 lines (~280); contains the E5 EXECUTION LEDGER block comment (L1000–1039) whose steps 3–4 prose no longer matches the executed route exactly (core extracted to `exists_tateAlgLift_core`).

#### `yOneStructMap_smooth` (L1282–1350)
- **Type**: theorem — **What**: Y1-E6 = Loeffler Thm 3.4.4: `Y₁(N) ⟶ Spec R` is smooth.
- **How** (proof ~68 lines): affine case reduction `HasRingHomProperty.iff_of_isAffine (P := @Smooth)`; `RingHom.Smooth` = `FormallySmooth` + `FinitePresentation` (the latter from `yOneStructMap_locallyOfFinitePresentation`); `FormallySmooth` via `Algebra.FormallySmooth.iff_comp_surjective` over square-zero test pairs, transporting `yOne_infinitesimal_lifting` through the Γ–Spec adjunction — the `hytri` structure triangle (`Scheme.toSpecΓ_naturality`, `Scheme.isoSpec_Spec_hom`), `Spec.preimage`/`Spec.map_injective` both ways.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`.
- **Uses from project**: [yOne_isAffine, yOneStructMap_locallyOfFinitePresentation, yOne_infinitesimal_lifting, yOneStructMap, yOne]
- **Used by**: [representableBy_smooth_isAffineHom, yOne_representable_smooth_affine]
- **Visibility**: public — **Lines**: 1282–1350 — **Notes**: proof >30 lines (~68).

#### `representableBy_smooth_isAffineHom` (L1359–1364)
- **Type**: theorem — **What**: Y1-F1: any object representing the naive `Γ₁(N)` problem has smooth affine structure morphism.
- **How**: instantiate `YFull.smooth_affine_of_representableBy` (YFullRoute — uniqueness of representing objects up to iso + `Smooth`/`IsAffineHom` respect isos) at the explicit representative `yOneEllObj` with Y1-E6 + Y1-E3.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`, `X`, `hX`.
- **Uses from project**: [yOne_representableBy, YFull.smooth_affine_of_representableBy (YFullRoute), yOneStructMap_smooth, yOneStructMap_isAffineHom, gammaOneNaiveProblem]
- **Used by**: [gammaOneNaive_representable_assembly] — **Visibility**: public — **Lines**: 1359–1364

#### `gammaOneNaive_representable_assembly` (L1372–1378)
- **Type**: theorem — **What**: Y1-MASTER, the T-E7 bridge (statement identical to the formerly-held `gammaOneNaive_representable`): representability + smooth-affine for every representing object.
- **How**: term-mode pair `⟨⟨⟨yOneEllObj, yOne_representableBy⟩⟩, representableBy_smooth_isAffineHom⟩`.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`.
- **Uses from project**: [yOneEllObj, yOne_representableBy, representableBy_smooth_isAffineHom, gammaOneNaiveProblem]
- **Used by**: [gammaOneNaive_representable_closure, gammaOneNaive_representable]
- **Visibility**: public — **Lines**: 1372–1378 — **Notes**: docstring pointer "Moduli/Representability.lean:250" is STALE (that file is 206 lines; the held statement was relocated).

#### `gammaOneNaive_representable_closure` (L1386–1391)
- **Type**: theorem — **What**: T-E7 MASTER closure-prep (v10.117): the held target's statement, byte-identical, closed by the bridge.
- **How**: `:= gammaOneNaive_representable_assembly R N hN hinv`.
- **Hypotheses**: same. — **Uses from project**: [gammaOneNaive_representable_assembly]
- **Used by**: [] — unused in these files AND project-wide.
- **Visibility**: public — **Lines**: 1386–1391 — **Notes**: **relocation-era relic**: statement is byte-identical to both `gammaOneNaive_representable_assembly` and `gammaOneNaive_representable`; with the master now landed at L1404 this intermediate duplicate serves no consumer — consolidation candidate (3 identical statements in one file).

#### `gammaOneNaive_representable` (L1404–1408)
- **Type**: theorem — **What**: **THE T-E7 MASTER** (relocated here per v10.111/v10.117, Y1-CLOSER S6): for `N ≥ 4` invertible in `R`, the naive `Γ₁(N)` problem is representable and every representing object is smooth and affine over `Spec R` (Loeffler Def 3.3.6 + Thm 3.4.4).
- **How**: `:= gammaOneNaive_representable_assembly R N hN hinv`.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `IsUnit (N : R)`.
- **Uses from project**: [gammaOneNaive_representable_assembly]
- **Used by**: [gammaOneNaive_representable_zInv]
- **Visibility**: public — **Lines**: 1404–1408 — **Notes**: docstring has a duplicated-parenthesis typo in the header line ("— Y1-CLOSER S6)** = Loeffler…)**"); records the 2026-07-06 adversarial fix (global killing clause) and the QUOTE-PARTIAL affineness caveat.

#### `yOne_representable_smooth_affine` (L1415–1420)
- **Type**: theorem — **What**: display form naming the scheme: `yOneEllObj` represents, and `yOneStructMap` is smooth and affine.
- **How**: triple of `yOne_representableBy`, `yOneStructMap_smooth`, `yOneStructMap_isAffineHom`.
- **Hypotheses**: same trio. — **Uses from project**: [yOne_representableBy, yOneStructMap_smooth, yOneStructMap_isAffineHom, yOneEllObj, gammaOneNaiveProblem]
- **Used by**: [] — terminal display corollary (no users in repo).
- **Visibility**: public — **Lines**: 1415–1420

#### `gammaOneNaive_representable_zInv` (L1426–1434)
- **Type**: theorem — **What**: Loeffler Thm 3.4.4 in literal arithmetic form: the master specialised at `R = ℤ[1/N] = Localization.Away (N : ℤ)`.
- **How**: apply `gammaOneNaive_representable`; the unit hypothesis from `IsLocalization.Away.algebraMap_isUnit` + `eq_intCast`/`Int.cast_natCast` cast juggling.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`.
- **Uses from project**: [gammaOneNaive_representable, gammaOneNaiveProblem]
- **Used by**: [] — terminal display corollary.
- **Visibility**: public — **Lines**: 1426–1434

### File Summary — YOneTatePoint.lean
- **Total declarations**: 33 (28 public, 5 private: `pullAsSection_dict`, `bcEquiv_zsmul`, `bcEquiv_zero`, `bcEquiv_nsmul`, `exists_tateAlgLift_core`).
- **Key API (3+ in-files users)**: `tatePoint` (≥12), `yOne` (10+), `yOneOpens` (6), `yOneStructMap` (6), `yOneSet` (5), `yOneBase` (5), `exists_tatePoint` (3), `yOneEllObj` (3), `yOne_representableBy` (3).
- **Unused within the three files**: `bcEquiv_nsmul` (private ⇒ genuinely dead), `gammaOneNaive_representable_closure` (also project-wide unused; byte-duplicate statement), `yOne_representable_smooth_affine`, `gammaOneNaive_representable_zInv` (both terminal display corollaries — intended leaves).
- **CODE-sorry list**: **NONE — verified** (grep: the only `sorry` strings are docstring prose at L25, L30, L1370). The MASTER `gammaOneNaive_representable` and its whole in-file input chain are sorry-free.
- **set_option list**: none.
- **Proofs >30 lines** (8): `factors_yOne_iff` (~82), `yOne_representableBy` (~46), `killedLocus_preimage_isOpen` (~94), `yOne_isAffine` (~46), `exists_section_lift_of_smooth` (~52), `exists_tateAlgLift_core` (~305), `yOne_infinitesimal_lifting` (~280), `yOneStructMap_smooth` (~68).
- **Private/public**: 5 / 28.
- **Relocation-relic notes**: L270–273 pointer comment (`pull_transportSection_eq_zero_iff` / `isNaiveGammaOne_pullSection_iff` → `Moduli/NaiveProblems.lean`); stale `Moduli/Representability.lean:250` pointers in the docstrings of `gammaOneNaive_representable_assembly` (L1367) — that file is now 206 lines; `gammaOneNaive_representable_closure` is itself a v10.117 closure-prep relic (three byte-identical statements: `_assembly` L1372, `_closure` L1386, master L1404 — consolidation candidate).

---

## 2. ModularCurve/YOneAssembly.lean (802 lines)

Import spine: `Moduli/Representability`, `Moduli/GammaH`, `Moduli/PullSectionCanonicity`,
`Moduli/QuotientProblem`, `EllipticCurve/TorsionFibre`, `EllipticCurve/GroupLawConstruction`,
`ForMathlib/GeometricFibreComparison`, `Moduli/NaiveProblems`, mathlib `NumberTheory.Divisors`.
File-level: `attribute [local instance] MvPolynomial.gradedAlgebra` (L59); no `set_option`;
no CODE-sorry (all grep hits L51/L54/L492/L503/L582/L617 are docstring/comment prose).

#### `EllipticCurve.NowhereGeomOrderLEThree` (L81–83)
- **Type**: def (Prop) — **What**: Loeffler's "`P, 2P, 3P ≠ 0` in any fibre" (Prop 3.3.4 hypothesis): on every geometric fibre no `a • P` with `1 ≤ a ≤ 3` vanishes; quantifier shape mirrors `IsNaiveGammaOne`.
- **How**: ∀ over alg. closed `k : Type u`, `t : Spec k ⟶ S`, `a ∈ [1,3]`.
- **Hypotheses**: `E : EllipticCurve S`, `P : E.Section`.
- **Uses from project**: [EllipticCurve.Point.pull (EllipticCurve record API)]
- **Used by**: [IsNaiveGammaOne.nowhereGeomOrderLEThree, tateMarkedPoint_nowhereGeomOrderLEThree; in YOneTatePoint: exists_tatePoint, tatePoint_nowhereGeomOrderLEThree, tatePoint_classifies (statements), exists_tateAlgLift_core (hordPA/hord₀sec)] (≥6 — key API)
- **Visibility**: public — **Lines**: 81–83

#### `IsNaiveGammaOne.nowhereGeomOrderLEThree` (L89–93)
- **Type**: theorem — **What**: Y1-A2 pivot: a naive `Γ₁(N)` structure with `N ≥ 4` is nowhere of order ≤ 3 (admits classified pairs into the Tate atlas).
- **How**: pure logic — clause 2 of `IsNaiveGammaOne` at `a ∈ {1,2,3}` with `omega` for `a < N`.
- **Hypotheses**: `[NeZero N]`, `4 ≤ N`, `h : E.IsNaiveGammaOne N P`.
- **Uses from project**: [IsNaiveGammaOne (LevelStructure/Basic), NowhereGeomOrderLEThree]
- **Used by**: [yOne_representableBy (L310, L318)] — **Visibility**: public — **Lines**: 89–93

#### `exists_properDivisor_smul_eq_zero` (L102–114)
- **Type**: theorem — **What**: Y1-A3 divisor pivot: in an `AddCommGroup`, `N•x = 0` and `a•x = 0` with `0 < a < N` force `d•x = 0` for a proper divisor `d = gcd a N` of `N` — why Loeffler's removed loci range over proper divisors only.
- **How** (proof ~11 lines): `addOrderOf_dvd_iff_nsmul_eq_zero` both ways + `Nat.dvd_gcd`; membership by `Nat.mem_properDivisors` and `Nat.gcd_le_left`; `exact_mod_cast` glue.
- **Hypotheses**: `[AddCommGroup G]`, kills as stated.
- **Uses from project**: [] — **Used by**: [factors_yOne_iff (L212)]
- **Visibility**: public — **Lines**: 102–114

#### `tateCurveOver` (L137–138)
- **Type**: noncomputable def — **What**: universal Tate-normal curve `E(A,B)` over `R[A,B]` = `tateCurve.map (MvPolynomial.map (Int.castRingHom R))`.
- **How**: `WeierstrassCurve.map`. — **Hypotheses**: `R`.
- **Uses from project**: [tateCurve (Representability)]
- **Used by**: [tateRingOver, tateCurveLocOver, tateB_cube_dvd_Δ; in YOneTatePoint: yOneStructMap_locallyOfFinitePresentation (L544), yOne_infinitesimal_lifting (Δ-unit computations L1084–1121)] (5 — key API)
- **Visibility**: public — **Lines**: 137–138

#### `tateRingOver` (L142–143)
- **Type**: noncomputable abbrev — **What**: the atlas ring `R[A,B][Δ(A,B)⁻¹]` = `Localization.Away (tateCurveOver R).Δ`.
- **How**: abbrev. — **Uses from project**: [tateCurveOver]
- **Used by**: [tateCurveLocOver, isUnit_algebraMap_tateB, tateBase, tateStructMap, tateP0sol, tateP0_chartCoord_eq_zero, tateP0mor_factor, tateMarkedPoint_pull_fst/_factor, projModelPointsEquiv_pull_tateMarkedPoint, tateMarkedPoint_nowhereGeomOrderLEThree, all baseChange_* lemmas; in YOneTatePoint: yOne_isAffine, exists_tateAlgLift_core, yOne_infinitesimal_lifting] (key API)
- **Visibility**: public — **Lines**: 142–143

#### `tateCurveLocOver` (L146–147)
- **Type**: noncomputable def — **What**: the universal Tate curve pushed to the atlas ring (Δ inverted).
- **How**: `map (algebraMap _ _)`. — **Uses from project**: [tateCurveOver, tateRingOver]
- **Used by**: [instance IsElliptic, isUnit_tateA₂/A₃, tateA₄/A₆_eq_zero, tateGeom, tateUniversal, tateUniversal_E_eq, tateP0sol, tateP0mor(+_π, _factor), tateP0_chartCoord_eq_zero, tateMarkedPoint_pull_fst/_factor, projModelPointsEquiv_pull_tateMarkedPoint, tateMarkedPoint_nowhereGeomOrderLEThree, baseChange_* lemmas] (key API)
- **Visibility**: public — **Lines**: 146–147

#### `instance : (tateCurveLocOver R).IsElliptic` (L151–155)
- **Type**: instance (anonymous) — **What**: over the atlas ring the discriminant is a unit, so the curve is elliptic (Loeffler Def 3.3.3).
- **How**: `WeierstrassCurve.IsElliptic.mk`, `map_Δ`, `IsLocalization.map_units` at the powers submonoid.
- **Uses from project**: [tateCurveLocOver, tateCurveOver, tateRingOver]
- **Used by**: [implicitly: tateGeom (projModel machinery), tateUniversal (modelEllipticCurve), the baseChange `IsElliptic` inference in tateMarkedPoint_nowhereGeomOrderLEThree (L592–593)]
- **Visibility**: public — **Lines**: 151–155

#### `tateB_cube_dvd_Δ` (L159–166)
- **Type**: lemma — **What**: `B³ ∣ Δ` for the Tate-normal discriminant (`Δ = B³·(A⁴ − A³ + 8A²B − 36AB + 16B² + 27B)`).
- **How**: explicit cofactor witness, `simp only` unfold of `Δ/b₂/b₄/b₆/b₈` + `ring`.
- **Uses from project**: [tateCurveOver, tateCurve (Representability)]
- **Used by**: [isUnit_algebraMap_tateB] — **Visibility**: public — **Lines**: 159–166

#### `isUnit_algebraMap_tateB` (L171–178)
- **Type**: lemma — **What**: the atlas marking engine: `B = a₃` is a unit of the atlas ring (`B³ ∣ Δ`, `Δ` inverted).
- **How**: `IsLocalization.Away.algebraMap_isUnit`, `isUnit_of_dvd_unit`, `(isUnit_pow_iff …).mp`.
- **Uses from project**: [tateB_cube_dvd_Δ, tateRingOver, tateCurveOver]
- **Used by**: [isUnit_tateA₃, isUnit_tateA₂] — **Visibility**: public — **Lines**: 171–178

#### `isUnit_tateA₃` (L181–185) / `isUnit_tateA₂` (L188–192)
- **Type**: lemma ×2 — **What**: `a₃` (resp. `a₂`) of the atlas curve is a unit (both `= B` in Tate normal form).
- **How**: identify with `algebraMap … (X 1)` by `simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map, tateCurve]`, then `isUnit_algebraMap_tateB`.
- **Uses from project**: [isUnit_algebraMap_tateB, tateCurveLocOver, tateCurve]
- **Used by**: [baseChange_isUnit_tateA₃ / baseChange_isUnit_tateA₂ respectively]
- **Visibility**: public — **Lines**: 181–185 / 188–192

#### `tateA₄_eq_zero` (L195–196) / `tateA₆_eq_zero` (L199–200)
- **Type**: lemma ×2 — **What**: `a₄ = 0` / `a₆ = 0` for the atlas curve (so `(0,0)` lies on it).
- **How**: `simp only` + `simp [tateCurve]`.
- **Uses from project**: [tateCurveLocOver, tateCurve]
- **Used by**: [baseChange_tateA₄_eq_zero / baseChange_tateA₆_eq_zero]
- **Visibility**: public — **Lines**: 195–196 / 199–200 — **Notes**: `tateP0sol` (L325–330) re-derives both facts inline by the same `simp` instead of citing these lemmas — dedup/golf opportunity.

#### `tateBase` (L206–207)
- **Type**: `@[reducible]` noncomputable def — **What**: the atlas base `𝒴 = Spec R[A,B][Δ⁻¹]`.
- **How**: `Spec (CommRingCat.of (tateRingOver R))`; `@[reducible]` for whnf-cheap unification with `Spec (of _)` (needed by `pointSpecPointsEquiv`/`geomFibrePointAddEquiv` leaves).
- **Uses from project**: [tateRingOver]
- **Used by**: [tateStructMap, tateP0mor, tateP0mor_π, tateMarkedPoint, tateEllObj; in YOneTatePoint: yOneBase, factors_yOne_iff(_exists_range), pullAsSection_dict, exists_tateAlgLift_core, yOne_infinitesimal_lifting (statements/bodies)] (key API)
- **Visibility**: public — **Lines**: 206–207

#### `tateStructMap` (L210–212)
- **Type**: noncomputable def — **What**: `𝒴 ⟶ Spec R`, Spec of `R → R[A,B] → R[A,B][Δ⁻¹]`.
- **How**: `Spec.map (ofHom (algebraMap.comp C))`. — **Uses from project**: [tateBase, tateRingOver]
- **Used by**: [tateEllObj; in YOneTatePoint: yOneStructMap, yOneStructMap_locallyOfFinitePresentation, exists_tateAlgLift_core, yOne_infinitesimal_lifting] (5 — key API)
- **Visibility**: public — **Lines**: 210–212

#### `isAffineOpen_top_isoSpec_hom_scheme_isoSpec_inv` (L216–219)
- **Type**: theorem — **What**: generic form of the T-W5a `crux_test`: on an affine scheme, the top-chart `isoSpec.hom` composed with the scheme's `isoSpec.inv` is the top inclusion.
- **How**: `IsAffineOpen.fromSpec_top`, `IsAffineOpen.isoSpec_inv_ι`, `Iso.hom_inv_id_assoc`.
- **Hypotheses**: `[IsAffine X]`, `h : IsAffineOpen ⊤`.
- **Uses from project**: [] — **Used by**: [projModel_locallyWeierstrass (L257)]
- **Visibility**: public — **Lines**: 216–219

#### `projModel_locallyWeierstrass` (L226–283)
- **Type**: theorem
- **What**: Y1-B1 (generalises the proven T-W5a `universalCurve_localModel`): the projective model of **any** elliptic Weierstrass curve over a ring is locally Weierstrass, witnessed on the single chart `⊤`.
- **How** (proof ~56 lines): witness `⟨⊤, isAffineOpen_top⟩` and curve `W.map (algebraMap A Γ)`; the comparison iso is assembled from `asIso (pullback.fst …)` twice and `(isPullback_projModelBaseChange W).isoPullback.symm`; side conditions `c1`/`c2` by `cancel_mono`, the `hcrux` equalities (via `isAffineOpen_top_isoSpec_hom_scheme_isoSpec_inv` and `Scheme.isoSpec_Spec_inv`), `pullback.condition`, and `reassoc_of% projModelZero_baseChange`.
- **Hypotheses**: `W : WeierstrassCurve A`, `[W.IsElliptic]`.
- **Uses from project**: [LocallyWeierstrass, projModel/projModelπ/projModelZero(+ _projModelπ), isPullback_projModelBaseChange, projModelZero_baseChange (EllipticCurve/WeierstrassModel · ModelRecord), isAffineOpen_top_isoSpec_hom_scheme_isoSpec_inv]
- **Used by**: [tateGeom]
- **Visibility**: public — **Lines**: 226–283 — **Notes**: proof >30 lines (~56); contains 3 `erw`s (style flag).

#### `tateGeom` (L287–294)
- **Type**: noncomputable def — **What**: the universal Tate curve over the atlas as a geometric record (`EllipticCurveGeom`): projective model + smoothness/properness/local-model witnesses.
- **How**: structure literal from `projModel(π/Zero/…)`, `projModel_smooth`, `projModelπ_isProper`, `projModel_locallyWeierstrass`.
- **Uses from project**: [EllipticCurveGeom (EllipticCurve/Basic), projModel API (WeierstrassModel/ModelRecord), projModel_locallyWeierstrass, tateCurveLocOver, tateBase]
- **Used by**: [tateUniversal_geom (statement)] — **Visibility**: public — **Lines**: 287–294

#### `tateUniversal` (L301–302)
- **Type**: noncomputable def — **What**: the universal Tate curve as a **working record** with group law: `modelEllipticCurve (tateCurveLocOver R)` (Y1-CLOSER S3 — the [T-A6b] gate is off this trail; global model needs no descent).
- **How**: `modelEllipticCurve` (EllipticCurve/ModelRecord).
- **Uses from project**: [modelEllipticCurve (EllipticCurve/ModelRecord), tateCurveLocOver, tateBase]
- **Used by**: [everything downstream in both Y₁ files: tateUniversal_geom/_E_eq/_hz/_eqToHom_π/_π_eq, tateMarkedPoint(+all vi-chain), tateEllObj, tateMarkedPoint_nowhereGeomOrderLEThree; YOneTatePoint: exists_tatePoint … yOne_infinitesimal_lifting] (the central object — key API)
- **Visibility**: public — **Lines**: 301–302

#### `tateUniversal_geom` (L306–307)
- **Type**: theorem — **What**: opaque-interface pin: `(tateUniversal R).toEllipticCurveGeom = tateGeom R` (v10.24(b) discipline).
- **How**: `rfl`. — **Uses from project**: [tateUniversal, tateGeom]
- **Used by**: [tateUniversal_E_eq, tateUniversal_eqToHom_π, tateUniversal_π_eq]
- **Visibility**: public — **Lines**: 306–307

#### `tateP0sol` (L320–330, with `open MvPolynomial in`)
- **Type**: noncomputable def — **What**: the `(0,0)` affine solution of the atlas curve in chart `X₂` (constant term `−a₆ = 0`).
- **How**: constant-zero assignment; the equation check `simp`s the dehomogenised cubic using inline re-derivations of `a₄ = 0`, `a₆ = 0`.
- **Uses from project**: [tateCurveLocOver, tateRingOver, dehomogenizeAux + `.toProjective.polynomial` (chart machinery, EllipticCurve/WeierstrassModel), tateCurve]
- **Used by**: [tateP0mor, tateP0_chartCoord_eq_zero, tateP0mor_factor, tateMarkedPoint_pull_factor, projModelPointsEquiv_pull_tateMarkedPoint] (5 — key API of the vi-chain)
- **Visibility**: public — **Lines**: 320–330 — **Notes**: re-proves `tateA₄_eq_zero`/`tateA₆_eq_zero` inline (dedup flag).

#### `tateP0mor` (L334–336)
- **Type**: noncomputable def — **What**: `P₀ = (0,0)` as a morphism `tateBase ⟶ projModel`, via the chart-`X₂` dictionary.
- **How**: `(chartHomEquiv …).symm ((chartSolutionsEquiv …).symm (tateP0sol R))`, first component.
- **Uses from project**: [chartHomEquiv, chartSolutionsEquiv (EllipticCurve/WeierstrassModel), tateP0sol, projModel, tateBase]
- **Used by**: [tateP0mor_π, tateMarkedPoint, tateP0mor_factor, tateMarkedPoint_pull_fst] (4 — key API)
- **Visibility**: public — **Lines**: 334–336

#### `tateP0mor_π` (L339–343)
- **Type**: lemma — **What**: `P₀` splits `projModelπ` (is a section).
- **How**: the `.2` field of the chart-hom subtype + `simp [tateBase]`.
- **Uses from project**: [tateP0mor, chartHomEquiv/chartSolutionsEquiv, projModelπ]
- **Used by**: [tateMarkedPoint] — **Visibility**: public — **Lines**: 339–343

#### `eqToHom_toGeom_π` (L347–349) / `eqToHom_toGeom_π'` (L352–354)
- **Type**: private lemma ×2 — **What**: transport compatibility for equal geometric records: the `eqToHom` bridge on total spaces intertwines the structure morphisms (two orientations).
- **How**: `subst h; simp`.
- **Uses from project**: [EllipticCurveGeom]
- **Used by**: [tateUniversal_eqToHom_π / tateUniversal_π_eq respectively]
- **Visibility**: private — **Lines**: 347–349 / 352–354

#### `tateUniversal_E_eq` (L357–358)
- **Type**: lemma — **What**: total space of `tateUniversal` = projective atlas model (through the bridge).
- **How**: `congrArg EllipticCurveGeom.E (tateUniversal_geom R)`.
- **Uses from project**: [tateUniversal_geom, projModel, tateCurveLocOver]
- **Used by**: [tateUniversal_hz, tateUniversal_eqToHom_π, tateUniversal_π_eq, tateMarkedPoint, tateMarkedPoint_pull_fst, projModelPointsEquiv_pull_tateMarkedPoint, tateMarkedPoint_nowhereGeomOrderLEThree] (7 — key API)
- **Visibility**: public — **Lines**: 357–358

#### `tateUniversal_hz` (L362–366)
- **Type**: theorem — **What**: the zero pin: `zero ≫ eqToHom = projModelZero` (the `hz` hypothesis of `geomFibrePointAddEquiv`, B2 EVENT #3) — definitional after the S3 model-record swap.
- **How**: `show` with `eqToHom rfl`, `eqToHom_refl`, `Category.comp_id`, `rfl`.
- **Uses from project**: [tateUniversal, tateUniversal_E_eq, projModelZero]
- **Used by**: [tateMarkedPoint_nowhereGeomOrderLEThree (L596, L607)] — **Visibility**: public — **Lines**: 362–366

#### `tateUniversal_eqToHom_π` (L369–372)
- **Type**: lemma — **What**: atlas `π` through the bridge is `projModelπ`.
- **How**: `eqToHom_toGeom_π (tateUniversal_geom R)`. — **Uses from project**: [eqToHom_toGeom_π, tateUniversal_geom, tateUniversal_E_eq]
- **Used by**: [tateMarkedPoint] — **Visibility**: public — **Lines**: 369–372

#### `tateUniversal_π_eq` (L376–379)
- **Type**: lemma — **What**: `π = eqToHom hE ≫ projModelπ` (the `hπ` datum of `geomFibrePointAddEquiv`/`pointSpecPointsEquiv`).
- **How**: `eqToHom_toGeom_π' (tateUniversal_geom R)`. — **Uses from project**: [eqToHom_toGeom_π', tateUniversal_geom, tateUniversal_E_eq]
- **Used by**: [tateMarkedPoint_pull_fst, projModelPointsEquiv_pull_tateMarkedPoint, tateMarkedPoint_nowhereGeomOrderLEThree] (3 — key API)
- **Visibility**: public — **Lines**: 376–379

#### `tateMarkedPoint` (L384–387)
- **Type**: noncomputable def — **What**: **the marked point `P₀ = (0,0)`** of `tateUniversal R` (the `exists_tatePoint` witness), transported from the chart construction across the bridge.
- **How**: `⟨tateP0mor ≫ eqToHom (tateUniversal_E_eq).symm, …⟩` with section property via `tateUniversal_eqToHom_π` + `tateP0mor_π`.
- **Uses from project**: [tateP0mor, tateP0mor_π, tateUniversal_E_eq, tateUniversal_eqToHom_π, tateUniversal]
- **Used by**: [tateMarkedPoint_pull_fst, tateMarkedPoint_pull_factor, projModelPointsEquiv_pull_tateMarkedPoint, tateMarkedPoint_nowhereGeomOrderLEThree; in YOneTatePoint: exists_tatePoint (the witness)] (5 — key API)
- **Visibility**: public — **Lines**: 384–387

#### `tateEllObj` (L390–393)
- **Type**: noncomputable def — **What**: the marked Tate atlas as an object of `Ell/R`.
- **How**: structure literal (base `tateBase`, structMap `tateStructMap`, curve `tateUniversal`).
- **Uses from project**: [tateBase, tateStructMap, tateUniversal, EllObj]
- **Used by**: [in YOneTatePoint: exists_tatePoint, tatePoint_classifies, yOne_representableBy, exists_tateAlgLift_core] (4 — key API)
- **Visibility**: public — **Lines**: 390–393

#### `baseChange_tateA₄_eq_zero` (L404–407) / `baseChange_tateA₆_eq_zero` (L410–413)
- **Type**: lemma ×2 — **What**: base change to a fibre keeps `a₄ = 0` / `a₆ = 0`.
- **How**: `show` map-form, `WeierstrassCurve.map_a₄/a₆`, `tateA₄/₆_eq_zero`, `map_zero`.
- **Uses from project**: [tateA₄_eq_zero / tateA₆_eq_zero, tateCurveLocOver, tateRingOver]
- **Used by**: [tateMarkedPoint_nowhereGeomOrderLEThree / baseChange_nonsingular_zero respectively]
- **Visibility**: public — **Lines**: 404–407 / 410–413

#### `baseChange_isUnit_tateA₂` (L416–420) / `baseChange_isUnit_tateA₃` (L423–427)
- **Type**: lemma ×2 — **What**: base change keeps `a₂` / `a₃` a unit.
- **How**: `map_a₂/a₃` + `IsUnit.map`.
- **Uses from project**: [isUnit_tateA₂ / isUnit_tateA₃, tateCurveLocOver, tateRingOver]
- **Used by**: [tateMarkedPoint_nowhereGeomOrderLEThree / (baseChange_nonsingular_zero + tateMarkedPoint_nowhereGeomOrderLEThree)]
- **Visibility**: public — **Lines**: 416–420 / 423–427

#### `baseChange_nonsingular_zero` (L430–433)
- **Type**: lemma — **What**: the affine marked point `(0,0)` is nonsingular on every fibre (`a₆ = 0`, `a₃` a unit).
- **How**: `WeierstrassCurve.Affine.nonsingular_zero` + the two baseChange lemmas.
- **Uses from project**: [baseChange_tateA₆_eq_zero, baseChange_isUnit_tateA₃, tateCurveLocOver]
- **Used by**: [tateMarkedPoint_nowhereGeomOrderLEThree (L594; feeds the `hns` hypothesis of projModelPointsEquiv_pull_tateMarkedPoint)]
- **Visibility**: public — **Lines**: 430–433

#### `tateP0_chartCoord_eq_zero` (L439–449)
- **Type**: private lemma — **What**: the chart-`X₂` coordinates of the marked point's chart hom are `0` (the round-trip read-off). Standalone so the heavy `chartSolutionsEquiv` whnf is spent here, not in the consuming proof.
- **How**: `hrfl : … = (chartSolutionsEquiv (… .symm …)).1 j` by `rfl`, then `Equiv.apply_symm_apply`, `rfl`.
- **Hypotheses**: takes explicit `R` (shadows the section variable), `j : {j : Fin 3 // j ≠ 2}`.
- **Uses from project**: [chartSolutionsEquiv, chartCoordEquiv (WeierstrassModel), tateP0sol, tateCurveLocOver, tateRingOver]
- **Used by**: [projModelPointsEquiv_pull_tateMarkedPoint (L574)] — **Visibility**: private — **Lines**: 439–449

#### `tateP0mor_factor` (L457–464)
- **Type**: private lemma — **What**: [Y1-vi setup] `tateP0mor` factors through the `Z`-chart via its chart hom `φ_B`: `tateP0mor = Spec.map (ofHom φ_B) ≫ Proj.awayι …`.
- **How**: `hdef : … = …` by `rfl` on the shared `chartHomEquiv` head, then `Eq.trans` with `chartHomEquiv_symm_coe` **as a term, never `rw`** (whose matching would whnf-explode the `ofBijective` equiv — documented discipline).
- **Uses from project**: [tateP0mor, tateP0sol, chartHomEquiv(+_symm_coe), chartSolutionsEquiv, quotientGrading/projIdeal/quotientGradingHom/mk_X_mem_quotientGrading_one (WeierstrassModel/proj machinery), tateCurveLocOver]
- **Used by**: [tateMarkedPoint_pull_factor (L519)] — **Visibility**: private — **Lines**: 457–464

#### `tateMarkedPoint_pull_fst` (L468–478)
- **Type**: private lemma — **What**: [Y1-vi setup] the pulled marked point's underlying model morphism is `geomPoint ≫ tateP0mor` (the two `eqToHom` bridges cancel).
- **How**: `show` + `eqToHom_trans`, `eqToHom_refl`, `Category.comp_id`.
- **Uses from project**: [pointSpecPointsEquiv, geomPoint (ForMathlib/GeometricFibreComparison), tateUniversal(+_E_eq, _π_eq), tateMarkedPoint, tateP0mor, tateCurveLocOver, tateRingOver]
- **Used by**: [tateMarkedPoint_pull_factor (L520)] — **Visibility**: private — **Lines**: 468–478

#### `spec_map_ofHom_comp_awayι` (L483–487)
- **Type**: private lemma — **What**: generic `Spec.map`/`ofHom` composition-associativity fold, isolated in its own heartbeat budget (the whnf-heavy chart hom `φ` is passed as an opaque fvar).
- **How**: `← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp`.
- **Uses from project**: [] — **Used by**: [tateMarkedPoint_pull_factor (L522)]
- **Visibility**: private — **Lines**: 483–487

#### `tateMarkedPoint_pull_factor` (L504–522)
- **Type**: private lemma — **What**: [Y1-vi setup] the pulled marked point factors through the `Z`-chart via `(algebraMap) ∘ φ_B`.
- **How** (proof ~9 lines): `set φ` opaque; rewrite with `tateMarkedPoint_pull_fst` and `tateP0mor_factor`; `simp only [EllipticCurve.geomPoint]`; close with `spec_map_ofHom_comp_awayι`.
- **Uses from project**: [tateMarkedPoint_pull_fst, tateP0mor_factor, spec_map_ofHom_comp_awayι, pointSpecPointsEquiv, geomPoint, chartSolutionsEquiv, tateP0sol, Proj-machinery names]
- **Used by**: [projModelPointsEquiv_pull_tateMarkedPoint (L554)]
- **Visibility**: private — **Lines**: 504–522 — **Notes**: **STALE GAP DOCSTRING** — the docstring (L489–503) still declares this "**GAP [Y1-vi-FACTOR]** — the *only* `sorry` in the vi assembly" with a whnf-explosion discharge-route discussion, but the proof is filled and sorry-free. Docstring relic to rewrite.

#### `projModelPointsEquiv_pull_tateMarkedPoint` (L537–576)
- **Type**: theorem
- **What**: [Y1-vi] transfer pin (chart naturality): over any fibre field `k`, the affine image of the pulled marked point is the affine origin `some 0 0`. Stated on the composite `projModelPointsEquiv ∘ pointSpecPointsEquiv` (v10.72 deviation (a), APPROVED — definitionally the `geomFibrePointAddEquiv` underlying map) to avoid an `IsElliptic` obligation.
- **How** (proof ~31 lines): `InZChart` witness from `tateMarkedPoint_pull_factor`; identify the chart hom by the `chartHomEquiv` round-trip (`chartHomEquiv_symm_coe`, `Equiv.symm_apply_apply`, `cancel_mono (Proj.awayι …)`, `Spec.map_injective`); coordinates by `coord_val` + `tateP0_chartCoord_eq_zero` + `map_zero`; conclude with `projModelPointsEquiv_some`.
- **Hypotheses**: `k` field, `[Algebra (tateRingOver R) k]`, `[DecidableEq k]`, `hns`.
- **Uses from project**: [tateMarkedPoint_pull_factor, tateP0_chartCoord_eq_zero, projModelPointsEquiv(+_some), coord_val, InZChart, chartHomEquiv(+_symm_coe), chartSolutionsEquiv (WeierstrassModel/PointsDictionary), pointSpecPointsEquiv, geomPoint (GeometricFibreComparison), tateUniversal(+_E_eq, _π_eq), tateMarkedPoint, tateP0sol, tateCurveLocOver, tateRingOver]
- **Used by**: [tateMarkedPoint_nowhereGeomOrderLEThree (L600)]
- **Visibility**: public — **Lines**: 537–576 — **Notes**: proof just over 30 lines (~31).

#### `tateMarkedPoint_nowhereGeomOrderLEThree` (L583–612)
- **Type**: theorem — **What**: **[Y1-vi]** the marked point `(0,0)` is nowhere of order ≤ 3 (first conjunct of `exists_tatePoint`).
- **How** (proof ~29 lines): give `k` the `tateRingOver R`-algebra structure via `Spec.preimage t` so `t = geomPoint`; transfer through the `[T-B6′]` group iso `geomFibrePointAddEquiv` (`geomFibrePointAddEquiv_apply` + `projModelPointsEquiv_pull_tateMarkedPoint`, `map_zsmul`/`map_zero`); kill the affine origin's small orders with `affine_origin_order_gt_three` fed by `baseChange_tateA₄_eq_zero`, `baseChange_isUnit_tateA₂/₃`, `baseChange_nonsingular_zero`.
- **Hypotheses**: `R`.
- **Uses from project**: [NowhereGeomOrderLEThree, tateMarkedPoint, tateUniversal(+_E_eq, _π_eq, _hz), geomFibrePointAddEquiv(+_apply), geomPoint (GeometricFibreComparison), affine_origin_order_gt_three (GeometricFibreComparison), projModelPointsEquiv_pull_tateMarkedPoint, baseChange_nonsingular_zero, baseChange_tateA₄_eq_zero, baseChange_isUnit_tateA₂, baseChange_isUnit_tateA₃, tateCurveLocOver, tateRingOver]
- **Used by**: [exists_tatePoint (YOneTatePoint L74)]
- **Visibility**: public — **Lines**: 583–612 — **Notes**: docstring says `geomFibrePointAddEquiv`'s `map_add'` "carries the tracked T-B6 `sorry`" — stale per YOneTatePoint's v10.152 header (trail retired; chain audits clean).

#### `EllipticCurve.killedLocus` (L638–639)
- **Type**: noncomputable def — **What**: the killed locus `{d•P = 0} ⊆ S` = `pullback ((d:ℤ)•P).1 E.zero` (Loeffler's `Y_d`). Generic in `E`, `P`.
- **How**: `pullback`. — **Uses from project**: [E.Section smul (GroupLawConstruction record API), E.zero]
- **Used by**: [killedLocusπ; in YOneTatePoint: yOneSet, yOneOpens, factors_yOne_iff_exists_range, yOne_isAffine (statements/bodies)] (key API)
- **Visibility**: public — **Lines**: 638–639

#### `EllipticCurve.killedLocusπ` (L642–643)
- **Type**: noncomputable def — **What**: the (closed) inclusion `Y_d ⟶ S` = `pullback.fst`.
- **How**: projection. — **Uses from project**: [killedLocus]
- **Used by**: [killedLocusπ_isClosedImmersion, killedLocus_spec, mem_killedLocus_range_iff; in YOneTatePoint: yOneSet, yOneSet_isOpen, yOneBase, factors_yOne_iff(_exists_range), killedLocus_preimage_isOpen, yOne_isAffine, yOneStructMap_locallyOfFinitePresentation] (key API)
- **Visibility**: public — **Lines**: 642–643

#### `killedLocusπ_isClosedImmersion` (L648–654)
- **Type**: theorem — **What**: Y1-C1: `Y_d ⟶ S` is a closed immersion.
- **How**: zero section of the separated family is a closed immersion (`IsClosedImmersion.of_comp` with `zero_π`, T-B3 pattern); closed immersions pull back (`MorphismProperty.pullback_fst`).
- **Uses from project**: [killedLocusπ, E.zero/π/zero_π (record API)]
- **Used by**: [in YOneTatePoint: yOneSet_isOpen, yOne_representableBy, yOne_isAffine, yOne_infinitesimal_lifting] (4 — key API)
- **Visibility**: public — **Lines**: 648–654

#### `killedLocus_spec` (L662–690)
- **Type**: theorem — **What**: Y1-C2, universal property: `t` factors through `Y_d` iff `(d:ℤ) • pull t P = 0` — the **global killing clause** of `IsNaiveGammaOne` (required per the 2026-07-06 adversarial pass).
- **How** (proof ~27 lines): translate via `smul_eq_zero_iff_comp_mulByHom` + `point_smul_eq_comp_mulBy`; the `hfs` computation `pullback.fst = pullback.snd` from `pullback.condition` and the section property; forward by rewriting along the factoring, backward by `pullback.lift`.
- **Uses from project**: [killedLocus(π), smul_eq_zero_iff_comp_mulByHom, point_smul_eq_comp_mulBy, Point.pull, E.zero_π (record API)]
- **Used by**: [in YOneTatePoint: factors_yOne_iff (L191, L238), killedLocus_preimage_isOpen (L363); in-file: mem_killedLocus_range_iff (L743, L752)] (3 — key API)
- **Visibility**: public — **Lines**: 662–690

#### `pull_smul_eq_zero_iff_residue` (L699–728)
- **Type**: theorem — **What**: Y1-C4 geometric-point/residue-point bridge: vanishing of a pulled section along any field-valued point is detected at the residue field of its image.
- **How** (proof ~27 lines): the `key` iff via `point_smul_eq_comp_mulBy`/`point_zero_val`; factor through `Spec κ(x)` by `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`; `Spec` of a field embedding is epi — `Scheme.hom_ext_of_comp_specMap_field`.
- **Uses from project**: [point_smul_eq_comp_mulBy, point_zero_val, Point.pull (record API); Scheme.hom_ext_of_comp_specMap_field (ForMathlib)]
- **Used by**: [in YOneTatePoint: factors_yOne_iff (L220, L263); in-file: mem_killedLocus_range_iff (L750)]
- **Visibility**: public — **Lines**: 699–728

#### `mem_killedLocus_range_iff` (L736–755)
- **Type**: theorem — **What**: Y1-C3 range/residue dictionary: `x ∈ range (killedLocusπ d)` iff the section dies on the residue-field fibre at `x`.
- **How** (proof ~18 lines): forward — tautological killed point over a preimage `x'`, fed through `pull_smul_eq_zero_iff_residue`; backward — `killedLocus_spec` at `fromSpecResidueField x` + `fromSpecResidueField_apply`.
- **Uses from project**: [killedLocus_spec, pull_smul_eq_zero_iff_residue, killedLocus(π)]
- **Used by**: [factors_yOne_iff (YOneTatePoint L224, L251)]
- **Visibility**: public — **Lines**: 736–755

#### `zsmul_pull_baseChange_asSection_iff` (L760–774)
- **Type**: theorem — **What**: Y1-D1 fibrewise bridge: `a`-torsion of the base-changed marked section pulled along a geometric point `τ` is detected on the fibre over `τ ≫ t`.
- **How** (proof ~13 lines): `Point.baseChangeEquiv` + `map_eq_zero_iff`, `map_zsmul`; coefficient computation by `baseChangeEquiv_apply_coe` + `asSection_val_fst`.
- **Uses from project**: [Point.baseChangeEquiv(+_apply_coe), Point.asSection(+_val_fst), Point.pull (record API)]
- **Used by**: [factors_yOne_iff (YOneTatePoint L200, L267)]
- **Visibility**: public — **Lines**: 760–774

#### `zsmul_asSection_pull_eq_zero_iff` (L779–792)
- **Type**: theorem — **What**: Y1-D1 killing bridge: the base-changed marked section is `a`-killed iff the pulled point is.
- **How** (proof ~13 lines): `asSection_zsmul`; `asSection` is injective (`asSection_val_fst`) and preserves `0` (from `asSection_zsmul` at `0`).
- **Uses from project**: [Point.asSection(+_zsmul, _val_fst), Point.pull]
- **Used by**: [factors_yOne_iff (YOneTatePoint L194, L237), yOne_infinitesimal_lifting (L1157)]
- **Visibility**: public — **Lines**: 779–792

### File Summary — YOneAssembly.lean
- **Total declarations**: 51 (44 public incl. 1 anonymous `IsElliptic` instance, 7 private: `eqToHom_toGeom_π`, `eqToHom_toGeom_π'`, `tateP0_chartCoord_eq_zero`, `tateP0mor_factor`, `tateMarkedPoint_pull_fst`, `spec_map_ofHom_comp_awayι`, `tateMarkedPoint_pull_factor`).
- **Key API (3+ in-files users)**: `tateUniversal` (dozens), `tateRingOver`, `tateCurveLocOver`, `tateBase`, `tateCurveOver` (5), `tateStructMap` (5), `tateUniversal_E_eq` (7), `tateUniversal_π_eq` (3), `tateMarkedPoint` (5), `tateEllObj` (4), `tateP0sol` (5), `tateP0mor` (4), `NowhereGeomOrderLEThree` (≥6), `killedLocus`/`killedLocusπ` (many), `killedLocusπ_isClosedImmersion` (4), `killedLocus_spec` (3).
- **Unused within the three files**: **none** — every declaration has at least one consumer here (the file is the upstream supplier of the Y₁ tower).
- **CODE-sorry list**: **NONE** (grep hits L51/L54/L492/L503/L582/L617 are all docstring/comment prose). Note in particular `tateMarkedPoint_pull_factor` (L504): its docstring still claims to be "the only `sorry` in the vi assembly" — the proof is in fact complete.
- **set_option list**: none.
- **Proofs >30 lines** (2): `projModel_locallyWeierstrass` (~56), `projModelPointsEquiv_pull_tateMarkedPoint` (~31). (`tateMarkedPoint_nowhereGeomOrderLEThree` is ~29, just under.)
- **Private/public**: 7 / 44.
- **Relocation-relic notes (v10.111/v10.117)**: two pointer-comment blocks — L614–618 (`exists_tatePoint` + the opaque `tatePoint` trio → `ModularCurve/YOneTatePoint.lean`) and L796–800 (the whole `yOneSet`…`gammaOneNaive_representable_assembly` tail → `YOneTatePoint.lean`). Stale header prose: L20–21 points the held target at "`Moduli/Representability.lean:250`" (file is 206 lines; statement relocated); L54 "planning-only skeleton, all leaves `sorry`" (all leaves proven); the "Named gates consumed" register (L43–53) still lists [T-A6b]/[BB-DIFF]/[T-B6′]-era gates that YOneTatePoint's v10.152 header records as retired.

---

## 3. Moduli/Representability.lean (206 lines)

Imports: `Moduli/EllCategory`, `ForMathlib/TateNormalForm`, mathlib `DivisionPolynomial.Basic`,
`Localization.Away.Basic`. File-level: `attribute [local instance]
Over.cartesianMonoidalCategory, Over.braidedCategory` (L32–33); no `set_option`.
**No copyright header** (file starts at `import` — mathlib-style violation).

#### `WeierstrassCurve.IsTateNormal` (L45–46)
- **Type**: def (Prop, `_root_`) — **What**: Tate normal form `Y² + αXY + βY = X³ + βX²`: `a₂ = a₃ ∧ a₄ = 0 ∧ a₆ = 0` (Loeffler Def 3.3.3).
- **How**: conjunction. — **Hypotheses**: `W : WeierstrassCurve R`.
- **Uses from project**: [] — **Used by**: [exists_unique_variableChange_isTateNormal, tateCurve_isTateNormal]
- **Visibility**: public — **Lines**: 45–46 — **Notes**: external user: YOneAtlasClassify.

#### `NowhereOrderLEThree` (L56–57)
- **Type**: def (Prop) — **What**: ring-level "nowhere of order 1, 2, 3": `IsUnit ((W.Ψ 2).evalEval x y * (W.Ψ 3).evalEval x y)` via mathlib division polynomials.
- **How**: `IsUnit` of a product. — **Uses from project**: []
- **Used by**: [exists_unique_variableChange_isTateNormal] — **Visibility**: public — **Lines**: 56–57 — **Notes**: external user: YOneAtlasClassify. Scheme-level counterpart is `EllipticCurve.NowhereGeomOrderLEThree` (YOneAssembly L81) — deliberate ring/scheme pair, not a duplicate.

#### `exists_unique_variableChange_isTateNormal` (L67–82, with `open WeierstrassCurve.Affine in`)
- **Type**: theorem — **What**: **T-E1** = Loeffler Prop 3.3.4 ring level: for elliptic `W/R` and a rational point `(x,y)` nowhere of order ≤ 3, there is a **unique** variable change putting `(W,(x,y))` in Tate normal form with the point at `(0,0)`.
- **How** (proof ~15 lines): subsingleton case by `Subsingleton.elim`; else split `hord` by `IsUnit.mul_iff`, `Ψ_two`/`Ψ_three` evaluation, nonsingularity from the equation + `ψ₂`-unit; instances `Point.NeZero`/`TwiceNeZero`/`ThriceNeZero` via `Point.twiceNeZero_of_isUnit`, `thriceNeZero_of_isUnit`; witness `W.toAffine.toTateNF` with `toTateNF_a₂₃/a₄/a₆` and uniqueness `toTateNF_unique` (ForMathlib/TateNormalForm).
- **Hypotheses**: `[W.IsElliptic]`, `Equation x y`, `NowhereOrderLEThree W x y`.
- **Uses from project**: [IsTateNormal, NowhereOrderLEThree, toTateNF(+_a₂₃/_a₄/_a₆/_unique), Point.twiceNeZero_of_isUnit, Point.thriceNeZero_of_isUnit (ForMathlib/TateNormalForm)]
- **Used by**: [] in these three files (cited only in YOneTatePoint prose L987, L1027) — **external code user: YOneAtlasClassify** (T-E1 renormalisation).
- **Visibility**: public — **Lines**: 67–82

#### `tateCurve` (L86–91)
- **Type**: noncomputable def — **What**: the universal Tate-normal curve `E(A,B)` over `ℤ[A,B]` (`a₁ = X 0`, `a₂ = a₃ = X 1`, `a₄ = a₆ = 0`).
- **How**: structure literal. — **Uses from project**: []
- **Used by**: [tateCurve_isTateNormal, tateRing, tateRing_eval₂Hom_comp, tateRing_homEquiv; in YOneAssembly: tateCurveOver (L138) + `simp [tateCurve]` unfolds in isUnit_tateA₂/₃, tateA₄/₆_eq_zero, tateP0sol] (key API)
- **Visibility**: public — **Lines**: 86–91

#### `tateCurve_isTateNormal` (L94)
- **Type**: theorem — **What**: sanity pin: the universal Tate curve is in Tate normal form.
- **How**: `⟨rfl, rfl, rfl⟩`. — **Uses from project**: [tateCurve, IsTateNormal]
- **Used by**: [] — **unused project-wide** (pure sanity pin).
- **Visibility**: public — **Lines**: 94

#### `tateRing` (L99–100)
- **Type**: noncomputable abbrev — **What**: `ℤ[A,B][Δ(A,B)⁻¹] = Localization.Away tateCurve.Δ` (Loeffler Cor 3.3.5's ring).
- **How**: abbrev. — **Uses from project**: [tateCurve]
- **Used by**: [tateRing_eval₂Hom_comp, tateRing_homEquiv] — **Visibility**: public — **Lines**: 99–100 — **Notes**: lands in `Type` (not `Type u`); YOneAssembly's `tateRingOver` (over `R`, `Type u`) is the parallel construction actually consumed by the tower — near-duplicate pair worth a consolidation look.

#### `tateRing_eval₂Hom_comp` (L102–107)
- **Type**: private lemma — **What**: the evaluation `eval₂Hom` at `(φA, φB)` equals `φ ∘ algebraMap` on `ℤ[A,B]`.
- **How**: `MvPolynomial.ringHom_ext'` + `RingHom.ext_int` + `fin_cases i <;> simp`.
- **Uses from project**: [tateRing, tateCurve] — **Used by**: [tateRing_homEquiv (L133, L136)]
- **Visibility**: private — **Lines**: 102–107

#### `tateRing_homEquiv` (L120–137)
- **Type**: theorem — **What**: **T-E2** = Loeffler Cor 3.3.5 ring level: `(tateRing →+* A) ≃ {(α,β) : A² // IsUnit Δ(α,β)}`, **pinned** to the canonical evaluation `φ ↦ (φA, φB)` (the 2026-07-06 ADVERSARIAL FIX: the bare `Nonempty (≃)` form was a cardinality-only claim).
- **How** (proof ~17 lines): forward well-defined by `map_Δ` + `tateRing_eval₂Hom_comp` + `IsLocalization.Away.algebraMap_isUnit`; inverse `IsLocalization.Away.lift`; left inverse by `IsLocalization.ringHom_ext` + `Away.lift_comp`; right inverse `simp`; pin `fun φ ↦ rfl`.
- **Hypotheses**: `A : Type u`, `[CommRing A]`.
- **Uses from project**: [tateRing, tateCurve, tateRing_eval₂Hom_comp]
- **Used by**: [] in these three files — and **no code user project-wide** (grep: only prose citations in YOneTatePoint's E5 ledger L1001/L1010/L1038; the executed route uses `tateRingOverAlgLift` from YOneAtlasClassify instead).
- **Visibility**: public — **Lines**: 120–137 — **Notes**: headline T-E2 deliverable that ended up bypassed by the `R`-relative `tateRingOverAlgLift` machinery — candidate for cross-linking or consolidation, not deletion (it is the literal Loeffler Cor 3.3.5).

#### `EllHom.pullSection` (L148–152)
- **Type**: noncomputable def — **What**: sections pull back contravariantly along `Ell/R`-morphisms: `f.isPullback.lift (f.baseHom ≫ P.1) (𝟙 _)`.
- **How**: pullback lift; second component by `lift_snd`.
- **Hypotheses**: `f : X ⟶ Y` in `Ell/R`, `P : Y.curve.Section`.
- **Uses from project**: [EllHom.isPullback/baseHom (Moduli/EllCategory), EllObj]
- **Used by**: [pullSection_id, pullSection_comp; in YOneTatePoint: exists_tatePoint, tatePoint_classifies, yOne_representableBy, exists_tateAlgLift_core, pullSection_pullbackAlongπ] (key API; also external: GammaH, NaiveProblems, YFullRoute)
- **Visibility**: public — **Lines**: 148–152

#### `EllHom.pullSection_id` (L155–165)
- **Type**: theorem — **What**: identity law: `pullSection (𝟙 X) P = P`.
- **How** (proof ~10 lines): `Subtype.ext` + `isPullback.hom_ext`; first leg by `lift_fst` + `show`/`Category.id_comp/comp_id`; second by the section fields.
- **Uses from project**: [EllHom.pullSection, EllHom API]
- **Used by**: [] in these three files — external users: Moduli/GammaH.lean, Moduli/NaiveProblems.lean.
- **Visibility**: public — **Lines**: 155–165

#### `EllHom.pullSection_comp` (L168–194)
- **Type**: theorem — **What**: composition law: `pullSection (f ≫ g) = pullSection f ∘ pullSection g`.
- **How** (proof ~25 lines): `Subtype.ext` + `isPullback.hom_ext`; the first-projection leg by a 6-step `calc` chain through `lift_fst` for `f`, `g`, and `f ≫ g`; the second leg by the section fields.
- **Uses from project**: [EllHom.pullSection, EllHom API]
- **Used by**: [yOne_representableBy (naturality, L328), exists_tateAlgLift_core (L937)]
- **Visibility**: public — **Lines**: 168–194

### File Summary — Moduli/Representability.lean
- **Total declarations**: 11 (10 public, 1 private: `tateRing_eval₂Hom_comp`).
- **Key API (3+ in-files users)**: `tateCurve` (≥5 in-files users incl. YOneAssembly's `tateCurveOver` and simp-unfolds), `EllHom.pullSection` (≥5).
- **Unused within the three files**: `exists_unique_variableChange_isTateNormal` (T-E1 — external code user YOneAtlasClassify; here cited in prose only), `tateRing_homEquiv` (T-E2 — **no code user project-wide**, bypassed by `tateRingOverAlgLift`), `tateCurve_isTateNormal` (sanity pin, unused project-wide), `EllHom.pullSection_id` (external users GammaH, NaiveProblems).
- **CODE-sorry list**: **NONE** — the anticipated sorry-carrier is not in this file anymore. The held `gammaOneNaive_representable` (formerly `Representability.lean:250`, carrying one of the "three parked `sorry`s") was **relocated out** per the L196–202 RELOCATED comment (Y1-CLOSER S4, v10.117 doctrine): `EllHom.pullSection_add`, `gammaOneNaiveProblem`/`gammaFullNaiveProblem`, and `gammaOneNaive_representable`/`gammaFullNaive_representable` now live in `Moduli/NaiveProblems.lean`, and the `Γ₁` master is proven in `ModularCurve/YOneTatePoint.lean:1404`. The only "sorry" string here (L199) is prose inside that comment. **Exact answer for the board: no declaration in this file carries a CODE-sorry.**
- **set_option list**: none.
- **Proofs >30 lines**: none (longest: `EllHom.pullSection_comp`, ~25).
- **Private/public**: 1 / 10.
- **Relocation-relic notes**: L196–202 pointer comment (v10.117) as above; header docstring (L19–21) still advertises `Y₁(N)`/`Y(N)` representability targets that now live elsewhere — the file is really "T-E1/T-E2 ring spine + `EllHom.pullSection` kernel"; also **missing copyright header** (starts at `import`).

---

## Cross-file observations (for the consolidation pass)
1. **Triple-duplicate master statement** in YOneTatePoint: `gammaOneNaive_representable_assembly` (L1372), `gammaOneNaive_representable_closure` (L1386, zero users), `gammaOneNaive_representable` (L1404) share a byte-identical statement, the latter two being `:= assembly`. Collapse to bridge + master (or master alone) once the board ratifies.
2. **Stale prose cluster** left by the v10.111/v10.117 relocations: `Representability.lean:250` pointers (YOneAssembly L20, YOneTatePoint L1367); YOneAssembly L54 "all leaves `sorry`"; the `tateMarkedPoint_pull_factor` GAP docstring; the T-B6-sorry mention at YOneAssembly L582; YOneAssembly's gate register L43–53 (gates retired at v10.152).
3. **Dead code**: `bcEquiv_nsmul` (private, YOneTatePoint) — no users.
4. **Bypassed headline**: `tateRing_homEquiv` (T-E2) has no code consumer anywhere; the tower uses YOneAtlasClassify's `tateRingOverAlgLift` route instead.
5. **Micro-dedup**: `tateP0sol` re-derives `tateA₄_eq_zero`/`tateA₆_eq_zero` inline; `baseChange_tateA₄/₆/₂/₃` are a uniform family that could be one lemma over the four invariants.
6. **Decompose targets**: `exists_tateAlgLift_core` (~305-line proof) and `yOne_infinitesimal_lifting` (~280) dominate YOneTatePoint; `killedLocus_preimage_isOpen` (~94) next.
7. **Mathlib-able candidates**: `exists_section_lift_of_smooth` (generic smooth-section nilpotent lifting via Γ–Spec), `exists_properDivisor_smul_eq_zero` (pure group theory), `projModel_locallyWeierstrass` (generic over any elliptic Weierstrass curve).
