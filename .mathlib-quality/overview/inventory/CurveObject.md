# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/CurveObject.lean`

File length: 1781 lines. Imports: `«Adic spaces».FarguesFontaine.FrobeniusValuation`,
`«Adic spaces».FarguesFontaine.Curve`.

File-level `set_option linter.overlappingInstances false` (line 23). Whole file is inside
`noncomputable section` (25) … `end` (1781). Two namespaces: `ValuationSpectrum` (27–73) and
`FarguesFontaine` (75–1779).

Standing variables in `ValuationSpectrum` block: `{A : Type*} [CommRing A] [TopologicalSpace A]
[IsTopologicalRing A] [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
[IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A]`.

Standing variables in `FarguesFontaine` block: `(p : ℕ) [Fact (Nat.Prime p)] (F : Type*) [Field F]
[TopologicalSpace F] [IsTopologicalRing F] [UniformSpace F] [NonarchimedeanRing F]
[IsPerfectoidField p F] [CharP F p] (ϖ : PseudoUniformizer F)`. Every `FarguesFontaine`
declaration below carries these; they are not repeated in each "Hypotheses" field unless
something extra is needed.

---

### `theorem presheafValue_subsingleton_of_rationalOpen_empty_huber`
- **Type**: `(E : RationalLocData A) (hempty : rationalOpen E.T E.s = ∅) → Subsingleton (presheafValue E)`
- **What**: Wedhorn's `𝒪(∅) = 0` at the level of a single rational localization datum: if the
  rational subset cut out by `(T, s)` is empty, the completed localization `A⟨T/s⟩` is the zero ring.
- **How**: Equips `presheafValue E` with its Huber-ring structure and adically-complete pair of
  definition (`presheafValue_isHuberRing_huber`, `presheafValue_concretePair`,
  `presheafValue_isAdicComplete`), then applies the complete-pair unit criterion
  `isUnit_iff_forall_not_vle_zero_of_completePair` to the element `0`: a witnessing `Spa`-point `w`
  of `presheafValue E` would push forward along `D.canonicalMap` into `rationalOpen E.T E.s`
  (`comap_canonicalMap_mem_rationalOpen` + `canonicalMap_continuous`), contradicting `hempty`; so
  `0` is a unit and `subsingleton_of_zero_eq_one ∘ isUnit_zero_iff.mp` concludes.
- **Hypotheses**: `A` a complete Huber ring with the standing `PlusSubring` /
  `IsRingOfIntegralElements` / `T2Space` / `NonarchimedeanRing` / `HasLocLiftPowerBounded` package;
  the rational open of `E` is empty.
- **Uses from project**: `presheafValue`, `presheafValue_isHuberRing_huber`,
  `presheafValue_concretePair`, `presheafValue_isAdicComplete`,
  `isUnit_iff_forall_not_vle_zero_of_completePair`, `comap_canonicalMap_mem_rationalOpen`,
  `canonicalMap_continuous`, `rationalOpen`, `RationalLocData`, `PairOfDefinition`
- **Used by**: `limitSections_subsingleton_of_empty`
- **Visibility**: public
- **Lines**: 37–51 (proof 39–51, 13 lines)
- **Notes**: none

### `theorem rationalOpen_eq_empty_of_index`
- **Type**: `{V : Opens ↥(Spa A A⁺)} (hV : (V : Set ↥(Spa A A⁺)) = ∅) (i : RationalIndex V) → rationalOpen i.D.T i.D.s = ∅`
- **What**: Every rational index of an open whose trace in `Spa A A⁺` is empty has an empty rational
  open — there are no valid indices with nonempty value.
- **How**: `Set.eq_empty_of_forall_notMem`: a point `v` of `rationalOpen i.D.T i.D.s` lifts to
  `Spa A A⁺` by `rationalOpen_subset_spa`, lands in `spaOpen i.D`, hence in `V` by the index's
  `subset` field, and `hV` rewrites that membership to membership in `∅`.
- **Hypotheses**: `V` has empty underlying set; `i` a `RationalIndex V` (valid rational datum whose
  `spaOpen` sits inside `V`).
- **Uses from project**: `RationalIndex` (fields `.D`, `.subset`), `rationalOpen`,
  `rationalOpen_subset_spa`, `spaOpen`
- **Used by**: `limitSections_subsingleton_of_empty`
- **Visibility**: public
- **Lines**: 54–62 (proof 56–62, 7 lines)
- **Notes**: none

### `theorem limitSections_subsingleton_of_empty`
- **Type**: `{V : Opens ↥(Spa A A⁺)} (hV : (V : Set ↥(Spa A A⁺)) = ∅) → Subsingleton ↥(limitSections V)`
- **What**: The concrete projective-limit sections over an open with empty trace form the zero ring.
- **How**: Two sections are equal iff all their components are (`Subtype.ext ∘ funext`); at each
  rational index `i`, `rationalOpen_eq_empty_of_index` supplies the empty rational open and
  `presheafValue_subsingleton_of_rationalOpen_empty_huber` makes `presheafValue i.D` a subsingleton,
  so `Subsingleton.elim` closes the component goal.
- **Hypotheses**: `V` has empty underlying set; the standing complete-Huber package on `A`.
- **Uses from project**: `limitSections`, `rationalOpen_eq_empty_of_index`,
  `presheafValue_subsingleton_of_rationalOpen_empty_huber`, `RationalIndex`
- **Used by**: `exists_translateFam_glue` (as `ValuationSpectrum.limitSections_subsingleton_of_empty`,
  line 589)
- **Visibility**: public
- **Lines**: 65–71 (proof 67–71, 5 lines)
- **Notes**: none

### `instance (anonymous local) : DecidableEq (Ainf p F)`
- **Type**: `noncomputable local instance : DecidableEq (Ainf p F)`
- **What**: Supplies classical decidable equality on `A_inf = W(𝒪_F^♭)` so that the sheaf-theoretic
  machinery downstream (which is stated with `DecidableEq` side conditions) type-checks in this file.
- **How**: `Classical.decEq _`.
- **Hypotheses**: none beyond the standing `p`, `F` package; classical choice.
- **Uses from project**: `Ainf`
- **Used by**: used implicitly by typeclass inference throughout the `FarguesFontaine` section
  (notably by anything invoking `isLimitSheafOn_Y` / `limitSections` machinery)
- **Visibility**: `local instance` (file-local)
- **Lines**: 82 (1 line)
- **Notes**: `noncomputable`, `local`

### `def yTopToY`
- **Type**: `(y : ↥(yTop p F ϖ)) → ↥(Y p F ϖ)`
- **What**: The carrier bridge: a point of the `𝒴`-topological carrier (a point of
  `Spa(A_inf, A_inf)` lying in the `𝒴`-trace) is regarded as a point of `↥(Y p F ϖ)`, the
  `Spv`-level subtype on which the curve quotient is formed.
- **How**: Strips one layer of subtype: `⟨y.1.1, y.2⟩` — the underlying `Spv`-valuation together with
  the (definitionally identical) membership proof.
- **Hypotheses**: none beyond the standing package; relies on `ySpaSet = Subtype.val ⁻¹' Y`.
- **Uses from project**: `yTop`, `Y`, `ySpaSet`
- **Used by**: `yTopToCurve`, `yTopToY_yFrobTop`, `yTopToCurve_yFrobTop`, `continuous_yTopToY`,
  `piYHom` (indirectly), `yTopToY_bijective`, `yTopToY_isInducing`, `curvePreimage_xImage`
- **Visibility**: public
- **Lines**: 86–87 (2 lines, definitional)
- **Notes**: none

### `def yTopToCurve`
- **Type**: `(y : ↥(yTop p F ϖ)) → Curve p F ϖ`
- **What**: The projection of the `𝒴`-carrier onto the adic Fargues–Fontaine curve `𝒳 = 𝒴/φ^ℤ`.
- **How**: Composite `toCurve ∘ yTopToY` — the orbit-quotient map of the `Multiplicative ℤ`-action
  applied to the bridged point.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToY`, `toCurve`, `Curve`, `yTop`
- **Used by**: `yTopToCurve_yFrobTop`, `continuous_yTopToCurve`, `curvePreimage`,
  `map_yFrobTop_curvePreimage`, `yTopToCurveTop`, `isOpenQuotientMap_yTopToCurve`, `xImage`,
  `curvePreimage_xImage`, `ringStalkMap_piYHom_germ`, `ringStalkMap_piYHom_surjective`,
  `ringStalkMap_piYHom_injective`, `yTopToCurve_fiberPoint`, `curvePreimage_iSup`
- **Visibility**: public
- **Lines**: 90–91 (2 lines, definitional)
- **Notes**: none

### `theorem yTopToY_yFrobTop`
- **Type**: `(k : ℤ) (y : ↥(yTop p F ϖ)) → yTopToY p F ϖ (yFrobTop p F ϖ k y) = (Multiplicative.ofAdd (-k)) • yTopToY p F ϖ y`
- **What**: Under the carrier bridge, the `k`-th Frobenius on the `𝒴`-carrier becomes the
  `(-k)`-action of `Multiplicative ℤ` on `↥(Y p F ϖ)` (the sign is the `comap`-versus-pushforward
  convention).
- **How**: `Subtype.ext` reduces to the underlying `Spv`-valuations, and `spaFrob_coe` identifies
  `(spaFrob p F k v).1` with `(ofAdd (-k)) • v.1`.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToY`, `yFrobTop`, `spaFrob`, `spaFrob_coe`, `yTop`
- **Used by**: `yTopToCurve_yFrobTop`, `curvePreimage_xImage`
- **Visibility**: public
- **Lines**: 94–100 (proof 96–100, 5 lines)
- **Notes**: none

### `theorem yTopToCurve_yFrobTop`
- **Type**: `(k : ℤ) (y : ↥(yTop p F ϖ)) → yTopToCurve p F ϖ (yFrobTop p F ϖ k y) = yTopToCurve p F ϖ y`
- **What**: The Frobenius acts along the fibers of the quotient map: translating a `𝒴`-point by
  `φ^k` does not change its image on the curve.
- **How**: Unfolds to `toCurve (yTopToY (yFrobTop k y))`, rewrites with `yTopToY_yFrobTop`, and then
  `Quotient.sound` applied to `MulAction.orbitRel_apply.mpr (MulAction.mem_orbit …)` — the two points
  lie in the same `φ^ℤ`-orbit by construction.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToCurve`, `yTopToY`, `yTopToY_yFrobTop`, `toCurve`, `yFrobTop`
- **Used by**: `map_yFrobTop_curvePreimage`, `curvePreimage_xImage`
- **Visibility**: public
- **Lines**: 103–108 (proof 104–108, 5 lines)
- **Notes**: none

### `theorem continuous_yTopToY`
- **Type**: `Continuous (yTopToY p F ϖ)`
- **What**: The carrier bridge is continuous.
- **How**: Both sides carry subspace topologies from `Spv (Ainf p F)`, so the map is
  `Continuous.subtype_mk` of the double `continuous_subtype_val` composite.
- **Hypotheses**: standing package; `yTop`/`Y` both carry `Spv`-subspace topologies.
- **Uses from project**: `yTopToY`
- **Used by**: `continuous_yTopToCurve`, `yTopToY_isInducing`
- **Visibility**: public
- **Lines**: 110–112 (term proof, 3 lines)
- **Notes**: none

### `theorem continuous_yTopToCurve`
- **Type**: `Continuous (yTopToCurve p F ϖ)`
- **What**: The projection from the `𝒴`-carrier to the curve is continuous.
- **How**: `(isOpenQuotientMap_toCurve p F ϖ).continuous.comp (continuous_yTopToY p F ϖ)` — the
  quotient map is continuous (as an open quotient map) and precomposition with the continuous bridge
  preserves that.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToCurve`, `continuous_yTopToY`, `isOpenQuotientMap_toCurve`
- **Used by**: `curvePreimage`, `yTopToCurveTop`
- **Visibility**: public
- **Lines**: 114–116 (term proof, 3 lines)
- **Notes**: none

### `def curvePreimage`
- **Type**: `(V : Opens (Curve p F ϖ)) → Opens ↥(yTop p F ϖ)`
- **What**: The saturated preimage of a curve open — the `φ^ℤ`-stable open of the `𝒴`-carrier lying
  over `V`. This is the index on which the curve's structure presheaf is computed.
- **How**: Bundles `yTopToCurve ⁻¹' V` with openness from `V.2.preimage (continuous_yTopToCurve …)`.
- **Hypotheses**: standing package; `V` open in the quotient topology.
- **Uses from project**: `yTopToCurve`, `continuous_yTopToCurve`, `Curve`, `yTop`
- **Used by**: `map_yFrobTop_curvePreimage`, `frobOpens_yFunctor_curvePreimage`, `frobFixed`,
  `mem_frobFixed`, `isClosed_frobFixed`, `yFunctor_curvePreimage_mono`, `frobFixed_restrict`,
  `curvePreimage_eq_opensMap`, `piComponent`, `curvePreimage_xImage`,
  `translate_le_curvePreimage_xImage`, `yFunctor_translate_le`, `exists_translateFam_glue`,
  `exists_glue_extending`, `piece_le_frobOpens_sat`, `pieces_cover_frobOpens_sat`, `glue_piece_eq`,
  `glue_invariant`, `piece_le_frobOpens_general`, `invariant_piece_transport`,
  `invariant_piece_step`, `invariant_piece_step'`, `invariant_piece_back'`, `invariant_pieces_eq`,
  `xImage_le`, `invariant_sections_eq_of_zero_piece`, `ringStalkMap_piYHom_injective`,
  `curvePreimage_inf`, `curvePreimage_iSup`, `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 119–121 (3 lines, definitional)
- **Notes**: none

### `theorem map_yFrobTop_curvePreimage`
- **Type**: `(k : ℤ) (V : Opens (Curve p F ϖ)) → (Opens.map (yFrobTop p F ϖ k)).obj (curvePreimage p F ϖ V) = curvePreimage p F ϖ V`
- **What**: Frobenius stability of saturated preimages at the carrier level: `φ^{-k}` of a saturated
  open is itself.
- **How**: `Opens.ext` + pointwise `ext`; the membership goal becomes
  `yTopToCurve (yFrobTop k y) ∈ V ↔ yTopToCurve y ∈ V`, closed by rewriting with
  `yTopToCurve_yFrobTop`.
- **Hypotheses**: standing package; `V` an open of the curve (i.e. saturated by construction).
- **Uses from project**: `curvePreimage`, `yTopToCurve`, `yTopToCurve_yFrobTop`, `yFrobTop`
- **Used by**: `frobOpens_yFunctor_curvePreimage`
- **Visibility**: public
- **Lines**: 124–131 (proof 126–131, 6 lines)
- **Notes**: none

### `theorem frobOpens_yFunctor_curvePreimage`
- **Type**: `(k : ℤ) (V : Opens (Curve p F ϖ)) → frobOpens p F k ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)) = (yFunctor p F ϖ).obj (curvePreimage p F ϖ V)`
- **What**: Frobenius stability of saturated preimages at the *ambient* `Spa(A_inf, A_inf)` level —
  the equality of opens that makes the `φ`-equalizer defining `frobFixed` type-check.
- **How**: Transports the carrier-level statement through the open-image functor: rewrite with
  `yFunctor_frobOpens` (Frobenius preimage commutes with the `𝒴`-image functor) and then with
  `map_yFrobTop_curvePreimage`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobOpens`, `yFunctor`, `yFunctor_frobOpens`, `curvePreimage`,
  `map_yFrobTop_curvePreimage`
- **Used by**: `frobFixed`, `mem_frobFixed`, `frobFixed_restrict`, `pieces_cover_frobOpens_sat`,
  `glue_piece_eq`, `glue_invariant`, `invariant_piece_transport`,
  `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 134–138 (proof 136–138, 3 lines)
- **Notes**: none

### `def frobFixed`
- **Type**: `(V : Opens (Curve p F ϖ)) → Subring ↥(limitSections ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)))`
- **What**: **The value of the curve's structure presheaf**: the `φ`-fixed subring of the
  `𝒴`-sections over the saturated preimage of `V`, i.e. `𝒪_𝒳(V) = 𝒪_𝒴(π^{-1}V)^{φ = 1}`.
- **How**: `RingHom.eqLocus` of the Frobenius transport `limitFrobHom p F 1` against the restriction
  `limitRestrict` along the stability equality `frobOpens_yFunctor_curvePreimage p F ϖ 1 V` — an
  equalizer of two ring homomorphisms with the same source and target.
- **Hypotheses**: standing package; the ambient-level stability of `π^{-1}V` (supplied by
  `frobOpens_yFunctor_curvePreimage`).
- **Uses from project**: `limitSections`, `yFunctor`, `curvePreimage`, `limitFrobHom`,
  `limitRestrict`, `frobOpens_yFunctor_curvePreimage`
- **Used by**: `mem_frobFixed`, `isClosed_frobFixed`, `frobFixed_restrict`,
  `frobFixed.completeSpace`, `frobFixed.isUniformAddGroup`, `frobFixedRestrict`,
  `frobFixedRestrict_continuous`, `xStructurePresheaf`, `piComponent`,
  `exists_invariant_extension`, `invariant_piece_transport`, `invariant_piece_step`,
  `invariant_piece_step'`, `invariant_piece_back'`, `invariant_pieces_eq`,
  `invariant_sections_eq_of_zero_piece`, `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 143–149 (7 lines, definitional)
- **Notes**: `noncomputable`

### `theorem mem_frobFixed`
- **Type**: `(V : Opens (Curve p F ϖ)) (s : ↥(limitSections ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)))) → s ∈ frobFixed p F ϖ V ↔ limitFrobHom p F 1 … s = limitRestrict (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 V)) s`
- **What**: The membership characterisation of the `φ`-fixed subring: `s` is invariant iff its
  Frobenius transport equals its restriction along the stability equality.
- **How**: `Iff.rfl` — `RingHom.eqLocus` membership is definitionally the equation.
- **Hypotheses**: standing package.
- **Uses from project**: `frobFixed`, `limitFrobHom`, `limitRestrict`, `curvePreimage`, `yFunctor`,
  `frobOpens_yFunctor_curvePreimage`, `limitSections`
- **Used by**: `frobFixed_restrict`, `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 151–158 (term proof, 1 line)
- **Notes**: none

### `theorem isClosed_frobFixed`
- **Type**: `(V : Opens (Curve p F ϖ)) → IsClosed ((frobFixed p F ϖ V : Set ↥(limitSections …)))`
- **What**: The `φ`-fixed subring is topologically closed in the section ring.
- **How**: An equalizer of two continuous maps into a Hausdorff target is closed:
  `isClosed_eq (limitFrobHom_continuous p F 1 _) (limitRestrict_continuous _)`.
- **Hypotheses**: standing package; Hausdorffness of the limit-sections topology (inherited from the
  product of the `presheafValue`s).
- **Uses from project**: `frobFixed`, `limitFrobHom_continuous`, `limitRestrict_continuous`,
  `limitSections`, `curvePreimage`, `yFunctor`
- **Used by**: `frobFixed.completeSpace`
- **Visibility**: public
- **Lines**: 162–166 (term proof, 2 lines)
- **Notes**: none

### `theorem yFunctor_curvePreimage_mono`
- **Type**: `{V' V : Opens (Curve p F ϖ)} (h : V' ≤ V) → (yFunctor p F ϖ).obj (curvePreimage p F ϖ V') ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ V)`
- **What**: Monotonicity of the composite "saturated preimage, then ambient open image".
- **How**: Functoriality: `leOfHom ((yFunctor p F ϖ).map (homOfLE (fun _ hy => h hy)))` — the
  preimage is monotone pointwise, and `yFunctor` (an `IsOpenMap.functor`) preserves the order.
- **Hypotheses**: `V' ≤ V`.
- **Uses from project**: `yFunctor`, `curvePreimage`
- **Used by**: `frobFixed_restrict`, `frobFixedRestrict`, `frobFixedRestrict_continuous`,
  `ringStalkMap_piYHom_injective`, `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 169–173 (term proof, 1 line)
- **Notes**: none

### `theorem frobFixed_restrict`
- **Type**: `{V' V : Opens (Curve p F ϖ)} (h : V' ≤ V) {s : ↥(limitSections …V…)} (hs : s ∈ frobFixed p F ϖ V) → limitRestrict (yFunctor_curvePreimage_mono p F ϖ h) s ∈ frobFixed p F ϖ V'`
- **What**: **Restriction preserves `φ`-invariance** — the key well-definedness fact making the fixed
  subrings into a presheaf.
- **How**: Rewrites both memberships with `mem_frobFixed`; naturality of the transport
  (`limitFrobHom_limitRestrict`) moves `limitFrobHom 1` past the restriction, `hs` replaces the
  transport by the stability restriction, and then two applications of `limitRestrict_comp` (one via
  `frobOpens_mono p F 1 …`, one via the stability equality for `V'`) show the two composite
  restrictions from `V` down to `φ^{-1}(π^{-1}V')` agree.
- **Hypotheses**: `V' ≤ V`; `s` invariant over `V`.
- **Uses from project**: `frobFixed`, `mem_frobFixed`, `limitRestrict`, `limitRestrict_comp`,
  `limitFrobHom_limitRestrict`, `frobOpens_mono`, `frobOpens_yFunctor_curvePreimage`,
  `yFunctor_curvePreimage_mono`, `curvePreimage`, `yFunctor`, `limitSections`
- **Used by**: `frobFixedRestrict`
- **Visibility**: public
- **Lines**: 176–193 (proof 181–193, 13 lines)
- **Notes**: none

### `instance frobFixed.completeSpace`
- **Type**: `(V : Opens (Curve p F ϖ)) → CompleteSpace ↥(frobFixed p F ϖ V)`
- **What**: The `φ`-fixed section ring is complete — required for it to be an object of
  `CompleteTopCommRingCat`.
- **How**: A closed subspace of a complete space is complete:
  `(isClosed_frobFixed p F ϖ V).completeSpace_coe`.
- **Hypotheses**: standing package; completeness of the ambient limit-sections space.
- **Uses from project**: `frobFixed`, `isClosed_frobFixed`
- **Used by**: `xStructurePresheaf`
- **Visibility**: public instance
- **Lines**: 195–197 (term proof, 1 line)
- **Notes**: none

### `instance frobFixed.isUniformAddGroup`
- **Type**: `(V : Opens (Curve p F ϖ)) → IsUniformAddGroup ↥(frobFixed p F ϖ V)`
- **What**: The `φ`-fixed subring is a uniform additive group in the subspace uniformity — the other
  half of the `CompleteTopCommRingCat` data.
- **How**: `IsUniformInducing.isUniformAddGroup` applied to the subring inclusion
  `(frobFixed p F ϖ V).subtype`, whose uniform-inducing property comes from
  `isUniformEmbedding_subtype_val.isUniformInducing`.
- **Hypotheses**: standing package; ambient uniform-additive-group structure on limit sections.
- **Uses from project**: `frobFixed`
- **Used by**: `xStructurePresheaf`
- **Visibility**: public instance
- **Lines**: 199–202 (term proof, 2 lines)
- **Notes**: none

### `def CurveTop`
- **Type**: `TopCat`
- **What**: The adic Fargues–Fontaine curve packaged as an object of `TopCat`.
- **How**: `TopCat.of (Curve p F ϖ)` using the quotient topology instance from `Curve.lean`.
- **Hypotheses**: standing package.
- **Uses from project**: `Curve`, `instTopologicalSpaceCurve`
- **Used by**: `xStructurePresheaf`, `curveSpace`, `yTopToCurveTop`
- **Visibility**: public
- **Lines**: 205–206 (1 line)
- **Notes**: none

### `def frobFixedRestrict`
- **Type**: `{V' V : Opens (Curve p F ϖ)} (h : V' ≤ V) → ↥(frobFixed p F ϖ V) →+* ↥(frobFixed p F ϖ V')`
- **What**: The restriction map of the curve's structure presheaf, as a ring homomorphism between
  `φ`-fixed section rings.
- **How**: `RingHom.codRestrict` of `(limitRestrict (yFunctor_curvePreimage_mono …)).comp
  (frobFixed p F ϖ V).subtype` along the codomain-membership witness supplied by
  `frobFixed_restrict`.
- **Hypotheses**: `V' ≤ V`.
- **Uses from project**: `frobFixed`, `frobFixed_restrict`, `limitRestrict`,
  `yFunctor_curvePreimage_mono`
- **Used by**: `frobFixedRestrict_continuous`, `xStructurePresheaf`, `curveRingPresheaf_map_apply`,
  `ringStalkMap_piYHom_injective`, `xPresheaf_map_apply`
- **Visibility**: public
- **Lines**: 208–215 (5 lines, definitional)
- **Notes**: `noncomputable`

### `theorem frobFixedRestrict_continuous`
- **Type**: `{V' V : Opens (Curve p F ϖ)} (h : V' ≤ V) → Continuous (frobFixedRestrict p F ϖ h)`
- **What**: The presheaf restriction between fixed subrings is continuous.
- **How**: `continuous_induced_rng` reduces to continuity of the composite into the ambient sections;
  an `rfl`-level `have` identifies `Subtype.val ∘ frobFixedRestrict h` with
  `fun s => limitRestrict (yFunctor_curvePreimage_mono … h) s.1`, which is
  `(limitRestrict_continuous _).comp continuous_subtype_val`.
- **Hypotheses**: `V' ≤ V`.
- **Uses from project**: `frobFixedRestrict`, `frobFixed`, `limitRestrict`,
  `limitRestrict_continuous`, `yFunctor_curvePreimage_mono`
- **Used by**: `xStructurePresheaf`
- **Visibility**: public
- **Lines**: 217–224 (proof 218–224, 7 lines)
- **Notes**: none

### `def xStructurePresheaf`
- **Type**: `TopCat.Presheaf CompleteTopCommRingCat.{u_1} (CurveTop p F ϖ)`
- **What**: **The structure presheaf of the adic Fargues–Fontaine curve** (D-iv-2): its value on an
  open `V` is the complete topological ring of `φ`-fixed sections `frobFixed p F ϖ V`.
- **How**: `obj V := CompleteTopCommRingCat.of ↥(frobFixed p F ϖ V.unop)` after installing the two
  instances `frobFixed.isUniformAddGroup` and `frobFixed.completeSpace`; `map i` is the bundled
  `⟨frobFixedRestrict …, frobFixedRestrict_continuous …⟩`; the functor laws `map_id`/`map_comp` are
  proved by peeling the bundling (`Subtype.ext`, `RingHom.ext`, two `Subtype.ext`, `funext`) down to
  the componentwise level, where both sides are `rfl` (all restrictions are reindexings of the same
  compatible family).
- **Hypotheses**: standing package.
- **Uses from project**: `CurveTop`, `frobFixed`, `frobFixed.completeSpace`,
  `frobFixed.isUniformAddGroup`, `frobFixedRestrict`, `frobFixedRestrict_continuous`,
  `CompleteTopCommRingCat`
- **Used by**: `curveSpace`
- **Visibility**: public
- **Lines**: 228–243 (16 lines; functor-law proofs 4 + 4 lines)
- **Notes**: `noncomputable`; universe-polymorphic in `u_1` (auto-bound)

### `def curveSpace`
- **Type**: `TopRingPresheafedSpace`
- **What**: **The adic curve as a presheafed space of complete topological rings** — the object
  `(𝒳, 𝒪_𝒳)` on which the whole `𝒱`-object package is built.
- **How**: Record with `carrier := CurveTop p F ϖ` and `presheaf := xStructurePresheaf p F ϖ`.
- **Hypotheses**: standing package.
- **Uses from project**: `CurveTop`, `xStructurePresheaf`, `TopRingPresheafedSpace`
- **Used by**: `piYHom`, `ringStalkMap_piYHom_germ`, `ringStalkMap_piYHom_surjective`,
  `curveRingPresheaf_map_apply`, `ringStalkMap_piYHom_injective`, `xStalkEquiv`,
  `isLocalRing_xStalk`, `xVPreObj`, `xPresheaf_map_apply`, `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 246–248 (3 lines)
- **Notes**: `noncomputable`

### `def yTopToCurveTop`
- **Type**: `yTop p F ϖ ⟶ CurveTop p F ϖ`
- **What**: The quotient projection as a morphism in `TopCat`.
- **How**: `TopCat.ofHom ⟨yTopToCurve p F ϖ, continuous_yTopToCurve p F ϖ⟩`.
- **Hypotheses**: standing package.
- **Uses from project**: `yTop`, `CurveTop`, `yTopToCurve`, `continuous_yTopToCurve`
- **Used by**: `curvePreimage_eq_opensMap`, `piYHom`, `ringStalkMap_piYHom_germ`,
  `ringStalkMap_piYHom_surjective`, `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 251–252 (2 lines)
- **Notes**: none

### `theorem curvePreimage_eq_opensMap`
- **Type**: `(V : Opens (Curve p F ϖ)) → curvePreimage p F ϖ V = (Opens.map (yTopToCurveTop p F ϖ)).obj V`
- **What**: The hand-rolled saturated preimage agrees with the categorical `Opens.map` preimage of
  the projection morphism.
- **How**: `rfl` — both are the same set-theoretic preimage bundled with the same openness proof.
- **Hypotheses**: standing package.
- **Uses from project**: `curvePreimage`, `yTopToCurveTop`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 255–257 (term proof, 1 line)
- **Notes**: none

### `def piComponent`
- **Type**: `(V : Opens (Curve p F ϖ)) → ↥(frobFixed p F ϖ V) →+* ↥(limitSections ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V)))`
- **What**: **The comparison component of the projection**: an invariant section of `𝒪_𝒳(V)` is in
  particular a section of `𝒪_𝒴` over the saturated preimage.
- **How**: The subring inclusion `(frobFixed p F ϖ V).subtype`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobFixed`, `limitSections`, `yFunctor`, `curvePreimage`
- **Used by**: `piYHom`, `ringStalkMap_piYHom_germ`, `ringStalkMap_piYHom_surjective`,
  `ringStalkMap_piYHom_injective`, `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 261–264 (4 lines)
- **Notes**: `noncomputable`

### `def piYHom`
- **Type**: `yPresheafedSpace p F ϖ ⟶ curveSpace p F ϖ`
- **What**: **The curve projection `π : 𝒴 → 𝒳` as a morphism of presheafed spaces** (D-iv-3(i)):
  base the quotient map, comparison the inclusion of invariants.
- **How**: Record with `base := yTopToCurveTop p F ϖ` and comparison natural transformation whose
  components are `⟨piComponent p F ϖ V.unop, continuous_subtype_val⟩`; naturality is proved by
  `Subtype.ext`/`RingHom.ext`/`Subtype.ext`/`funext` down to components, where both routes are the
  identical reindexing (`rfl`).
- **Hypotheses**: standing package.
- **Uses from project**: `yPresheafedSpace`, `curveSpace`, `yTopToCurveTop`, `piComponent`
- **Used by**: `ringStalkMap_piYHom_germ`, `ringStalkMap_piYHom_surjective`,
  `ringStalkMap_piYHom_injective`, `ringStalkMap_piYHom_bijective`, `xStalkEquiv`
- **Visibility**: public
- **Lines**: 268–275 (8 lines; naturality proof 4 lines)
- **Notes**: `noncomputable`

### `theorem yTopToY_bijective`
- **Type**: `Function.Bijective (yTopToY p F ϖ)`
- **What**: The carrier bridge is a bijection — the two subtype presentations of `𝒴` (as a subset of
  `Spa(A_inf, A_inf)` and as a subset of `Spv(A_inf)`) have the same points.
- **How**: Injectivity: two `yTop`-points with the same image have equal underlying `Spv`-elements
  (`congrArg` on the coercion), and `Subtype.ext` twice recovers equality. Surjectivity: a point
  `z : ↥(Y p F ϖ)` has `z.1 ∈ Spa (Ainf p F) (ringPlus (Ainf p F))` from `z.2.1` (the `Y`-membership
  packages the `Spa`-condition), giving the preimage `⟨⟨z.1, hz⟩, z.2⟩` with `rfl`.
- **Hypotheses**: standing package; `Y ⊆ Spa` (the `Y`-membership predicate includes continuity/
  integrality data).
- **Uses from project**: `yTopToY`, `Y`, `Spa`, `ringPlus`, `Ainf`, `yTop`
- **Used by**: `yTopToYHomeo`, `curvePreimage_xImage`
- **Visibility**: public
- **Lines**: 278–286 (proof 278–286, 9 lines)
- **Notes**: none

### `theorem yTopToY_isInducing`
- **Type**: `Topology.IsInducing (yTopToY p F ϖ)`
- **What**: The bridge is topologically inducing: the `yTop` topology is the pullback of the
  `↥(Y p F ϖ)` topology.
- **How**: `le_antisymm` on the two topologies. One direction is `(continuous_yTopToY …).le_induced`.
  The other unfolds a basic open of `yTop` as a double `Subtype.val`-preimage of an open `S` of
  `Spv (Ainf p F)` (two `obtain … rfl`), and exhibits it as the induced-preimage of
  `Subtype.val ⁻¹' S`, an open of `↥(Y p F ϖ)`; the equality is `rfl`.
- **Hypotheses**: standing package; both subtypes carry the `Spv`-subspace topology.
- **Uses from project**: `yTopToY`, `continuous_yTopToY`
- **Used by**: `yTopToYHomeo`
- **Visibility**: public
- **Lines**: 289–297 (proof 289–297, 9 lines)
- **Notes**: none

### `def yTopToYHomeo`
- **Type**: `↥(yTop p F ϖ) ≃ₜ ↥(Y p F ϖ)`
- **What**: The bridge as a homeomorphism — the two presentations of `𝒴` agree as topological spaces.
- **How**: `(Equiv.ofBijective _ (yTopToY_bijective …)).toHomeomorphOfIsInducing
  (yTopToY_isInducing …)`.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToY`, `yTopToY_bijective`, `yTopToY_isInducing`, `yTop`, `Y`
- **Used by**: `isOpenQuotientMap_yTopToCurve`
- **Visibility**: public
- **Lines**: 301–303 (3 lines)
- **Notes**: `noncomputable`

### `theorem isOpenQuotientMap_yTopToCurve`
- **Type**: `IsOpenQuotientMap (yTopToCurve p F ϖ)`
- **What**: The projection from the `𝒴`-carrier to the curve is an open quotient map (surjective,
  continuous, open) — this is what makes images of carrier opens curve opens.
- **How**: Factors `yTopToCurve = toCurve ∘ yTopToYHomeo` (`rfl`), then composes the two open
  quotient maps: `(isOpenQuotientMap_toCurve p F ϖ).comp (yTopToYHomeo p F ϖ).isOpenQuotientMap`.
- **Hypotheses**: standing package; `toCurve` is an open quotient map (orbit map of a continuous
  group action).
- **Uses from project**: `yTopToCurve`, `toCurve`, `yTopToYHomeo`, `isOpenQuotientMap_toCurve`
- **Used by**: `xImage`, `fiberPoint`, `yTopToCurve_fiberPoint`
- **Visibility**: public
- **Lines**: 306–312 (proof 308–312, 5 lines)
- **Notes**: none

### `def xImage`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) → Opens (Curve p F ϖ)`
- **What**: The image on the curve of an open of the `𝒴`-carrier, as an open — the "saturating open"
  attached to any `W`.
- **How**: Bundles `yTopToCurve '' W` with openness from
  `(isOpenQuotientMap_yTopToCurve p F ϖ).isOpenMap _ W.2`.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToCurve`, `isOpenQuotientMap_yTopToCurve`, `Curve`, `yTop`
- **Used by**: `curvePreimage_xImage`, `translate_le_curvePreimage_xImage`, `yFunctor_translate_le`,
  `exists_translateFam_glue`, `exists_glue_extending`, `piece_le_frobOpens_sat`,
  `pieces_cover_frobOpens_sat`, `glue_piece_eq`, `glue_invariant`, `exists_invariant_extension`,
  `ringStalkMap_piYHom_surjective`, `xImage_le`, `invariant_sections_eq_of_zero_piece`,
  `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 315–317 (3 lines)
- **Notes**: none

### `theorem curvePreimage_xImage`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) → curvePreimage p F ϖ (xImage p F ϖ W) = ⨆ k : ℤ, (Opens.map (yFrobTop p F ϖ k)).obj W`
- **What**: **The saturation identity**: `π^{-1}(π(W))` is exactly the union of all Frobenius
  translates `φ^{-k}(W)`, `k ∈ ℤ`.
- **How**: `Opens.ext`, then a two-way membership chase. (⊆) A point `y` in the preimage has some
  `w ∈ W` with `yTopToCurve w = yTopToCurve y`, so `yTopToY w` lies in the `Multiplicative ℤ`-orbit
  of `yTopToY y` (`MulAction.orbitRel_apply` + `Quotient.eq''`); taking `g` with
  `g • yTopToY y = yTopToY w`, `yTopToY_yFrobTop` (plus `neg_neg`, `ofAdd_toAdd`) shows
  `yTopToY (yFrobTop (-(toAdd g)) y) = yTopToY w`, whence `yFrobTop (-(toAdd g)) y = w ∈ W` by
  `yTopToY_bijective.1`, i.e. `y ∈ φ^{-(toAdd g)}(W)`. (⊇) If `yFrobTop k y ∈ W`, then
  `yTopToCurve_yFrobTop` gives `yTopToCurve y = yTopToCurve (yFrobTop k y) ∈ xImage W`.
- **Hypotheses**: standing package.
- **Uses from project**: `curvePreimage`, `xImage`, `yFrobTop`, `yTopToY`, `yTopToY_yFrobTop`,
  `yTopToY_bijective`, `yTopToCurve`, `yTopToCurve_yFrobTop`
- **Used by**: `translate_le_curvePreimage_xImage`, `exists_translateFam_glue`,
  `pieces_cover_frobOpens_sat`, `invariant_sections_eq_of_zero_piece`
- **Visibility**: public
- **Lines**: 321–349 (proof 324–349, 26 lines)
- **Notes**: none

### `theorem exists_disjoint_translates`
- **Type**: `(y : ↥(yTop p F ϖ)) → ∃ W : Opens ↥(yTop p F ϖ), y ∈ W ∧ ∀ k : ℤ, k ≠ 0 → Disjoint ((Opens.map (yFrobTop p F ϖ k)).obj W : Set _) (W : Set _)`
- **What**: **Wandering (proper discontinuity) at the `𝒴`-carrier**: every point has an open
  neighbourhood whose nontrivial Frobenius translates miss it. This is the geometric input that makes
  the quotient presheaf behave.
- **How**: Pulls back the `Spv`-level wandering statement `exists_nhd_smul_disjoint` (from
  `Curve.lean`, proved with the window covering `U_n`/`V_n`) along the double `Subtype.val`, then
  converts the `Multiplicative ℤ`-smul disjointness into `yFrobTop`-preimage disjointness: for
  `z` in both sets, `spaFrob_coe` shows `ofAdd (-k) • z.1.1 ∈ W₀`, and applying `ofAdd k •` with
  `smul_smul`, `← ofAdd_add` and `one_smul` puts `z.1.1` into `ofAdd k • W₀`, contradicting
  `hdis k hk` against `z.1.1 ∈ W₀`.
- **Hypotheses**: standing package (perfectoid `F`, pseudo-uniformizer `ϖ`) — needed for
  `exists_nhd_smul_disjoint`.
- **Uses from project**: `yFrobTop`, `spaFrob_coe`, `exists_nhd_smul_disjoint`, `Ainf`, `yTop`
- **Used by**: `ringStalkMap_piYHom_surjective`, `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 353–385 (proof 359–385, 27 lines)
- **Notes**: none

### `theorem frobPow_zero`
- **Type**: `frobPow p F 0 = RingEquiv.refl (Ainf p F)`
- **What**: The zeroth Frobenius power on `A_inf` is the identity ring equivalence.
- **How**: `show` the coercion of `frob p F ^ (0 : ℤ)` in `RingAut`, then `zpow_zero` + `rfl`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobPow`, `frob`, `Ainf`
- **Used by**: `spaFrob_zero`, `frobPow_neg_zero_eq_refl`
- **Visibility**: public
- **Lines**: 387–390 (proof 387–390, 4 lines)
- **Notes**: none

### `theorem spaFrob_zero`
- **Type**: `(v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) → spaFrob p F 0 v = v`
- **What**: The zeroth Frobenius on the adic spectrum is the identity.
- **How**: `Subtype.ext`, then `spaFrob 0 v = comap (frobPow 0).toRingHom v.1`; rewriting with
  `frobPow_zero` and applying `comap_id` pointwise gives `v.1`.
- **Hypotheses**: standing package.
- **Uses from project**: `spaFrob`, `frobPow`, `frobPow_zero`, `comap`, `comap_id`, `Ainf`,
  `ringPlus`
- **Used by**: `frobOpens_zero`, `yFrobTop_zero`
- **Visibility**: public
- **Lines**: 392–397 (proof 393–397, 5 lines)
- **Notes**: none

### `theorem frobOpens_zero`
- **Type**: `(W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) → frobOpens p F 0 W = W`
- **What**: The zeroth Frobenius preimage of an open is the open itself.
- **How**: `Opens.ext` + `ext v`; the membership goal `spaFrob 0 v ∈ W ↔ v ∈ W` closes by rewriting
  with `spaFrob_zero`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobOpens`, `spaFrob`, `spaFrob_zero`
- **Used by**: `limitFrobHom_zero`, `translateFam_zero`, `frobOpens_inv_collapse`,
  `limitFrobHom_leftInv`
- **Visibility**: public
- **Lines**: 399–404 (proof 400–404, 5 lines)
- **Notes**: none

### `theorem frobPow_neg_zero_eq_refl`
- **Type**: `frobPow p F (-0) = RingEquiv.refl (Ainf p F)`
- **What**: The `(-0)`-spelling of the Frobenius power is also the identity — needed because
  `limitFrobHom` transports along `frobPow (-k)`.
- **How**: `rw [neg_zero, frobPow_zero]`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobPow`, `frobPow_zero`, `Ainf`
- **Used by**: `limitFrobHom_zero`
- **Visibility**: public
- **Lines**: 406–408 (proof 407–408, 2 lines)
- **Notes**: none

### `theorem limitFrobHom_zero`
- **Type**: `(W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (s : ↥(limitSections W)) → limitFrobHom p F 0 W s = limitRestrict (le_of_eq (frobOpens_zero p F W)) s`
- **What**: **The zero-power transport is the restriction along the preimage collapse** — the base
  case of the transport calculus.
- **How**: Componentwise (`Subtype.ext (funext fun E => …)`). First `RationalLocData.mapHuber_eq_of_eq_refl`
  (with `frobPow_neg_zero_eq_refl`) shows the transported datum `E.D.mapHuber (frobPow (-0)) …` is
  literally `E.D`, giving both inclusions `hle`/`hle'` of rational opens by `rw`. Then
  `presheafValueRingEquivHuber_symm_apply_of_eq_refl` identifies the value-level transport with the
  restriction map, `frobOpens_zero` identifies the two index sets, and the compatibility field `s.2`
  of the section (between `frobIndex p F 0 E` and the reindexed `E`) finishes; the three steps are
  chained through `limitFrobHom_component`.
- **Hypotheses**: standing package; `s` a compatible family over `W`.
- **Uses from project**: `limitFrobHom`, `limitFrobHom_component`, `limitRestrict`, `frobOpens_zero`,
  `frobPow`, `frobPow_neg_zero_eq_refl`, `continuous_frobPow`, `continuous_frobPow_symm`,
  `RationalLocData.mapHuber_eq_of_eq_refl`, `presheafValueRingEquivHuber_symm_apply_of_eq_refl`,
  `frobIndex`, `rationalOpen`, `presheafValue`, `RationalIndex`, `limitSections`
- **Used by**: `translateFam_zero`, `limitFrobHom_eq_zero_of`
- **Visibility**: public
- **Lines**: 412–449 (proof 416–449, **34 lines**)
- **Notes**: proof >30 lines

### `theorem yFrobTop_zero`
- **Type**: `(y : ↥(yTop p F ϖ)) → yFrobTop p F ϖ 0 y = y`
- **What**: The zeroth Frobenius on the `𝒴`-carrier is the identity map.
- **How**: `Subtype.ext` reduces to `spaFrob p F 0 y.1 = y.1`, which is `spaFrob_zero`.
- **Hypotheses**: standing package.
- **Uses from project**: `yFrobTop`, `spaFrob`, `spaFrob_zero`
- **Used by**: `map_yFrobTop_zero`, `ringStalkMap_piYHom_surjective`
- **Visibility**: public
- **Lines**: 451–455 (proof 452–455, 4 lines)
- **Notes**: none

### `theorem map_yFrobTop_zero`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) → (Opens.map (yFrobTop p F ϖ 0)).obj W = W`
- **What**: The zeroth translate of a carrier open is the open itself.
- **How**: `Opens.ext` + `ext y`; rewrite the membership with `yFrobTop_zero`.
- **Hypotheses**: standing package.
- **Uses from project**: `yFrobTop`, `yFrobTop_zero`
- **Used by**: `yFunctor_translate_zero_le`, `ringStalkMap_piYHom_surjective`,
  `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 457–462 (proof 458–462, 5 lines)
- **Notes**: none

### `theorem frobPow_toRingHom_comp`
- **Type**: `(k l : ℤ) → (frobPow p F (k + l)).toRingHom = (frobPow p F k).toRingHom.comp (frobPow p F l).toRingHom`
- **What**: Additivity of Frobenius powers on `A_inf` at the level of ring homomorphisms.
- **How**: `RingHom.ext`, then `show` both sides as `RingAut`-coercions and apply `zpow_add`
  followed by `rfl`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobPow`, `frob`, `Ainf`
- **Used by**: `spaFrob_add`, `frobPow_trans`
- **Visibility**: public
- **Lines**: 464–472 (proof 467–472, 6 lines)
- **Notes**: none

### `theorem spaFrob_add`
- **Type**: `(k l : ℤ) (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) → spaFrob p F (k + l) v = spaFrob p F l (spaFrob p F k v)`
- **What**: Additivity of the `Spa`-level Frobenius action (with the order reversed, since `comap` is
  contravariant).
- **How**: `Subtype.ext` reduces to `comap`s; rewriting with `frobPow_toRingHom_comp` and applying
  `ValuationSpectrum.comap_comp` pointwise gives the composite.
- **Hypotheses**: standing package.
- **Uses from project**: `spaFrob`, `frobPow`, `frobPow_toRingHom_comp`, `comap`, `comap_comp`
- **Used by**: `yFrobTop_add`, `frobOpens_add`
- **Visibility**: public
- **Lines**: 475–483 (proof 478–483, 6 lines)
- **Notes**: none

### `theorem yFrobTop_add`
- **Type**: `(k l : ℤ) (y : ↥(yTop p F ϖ)) → yFrobTop p F ϖ (k + l) y = yFrobTop p F ϖ l (yFrobTop p F ϖ k y)`
- **What**: Additivity of the `𝒴`-carrier Frobenius.
- **How**: `Subtype.ext` reduces to the `Spa`-statement `spaFrob_add`.
- **Hypotheses**: standing package.
- **Uses from project**: `yFrobTop`, `spaFrob`, `spaFrob_add`
- **Used by**: `translates_pairwise_disjoint`, `map_yFrobTop_shift`
- **Visibility**: public
- **Lines**: 486–491 (proof 487–491, 5 lines)
- **Notes**: none

### `theorem translates_pairwise_disjoint`
- **Type**: `{W : Opens ↥(yTop p F ϖ)} (hdis : ∀ k ≠ 0, Disjoint (φ^{-k}W) W) {i j : ℤ} (hij : i ≠ j) → Disjoint ((Opens.map (yFrobTop p F ϖ i)).obj W : Set _) ((Opens.map (yFrobTop p F ϖ j)).obj W : Set _)`
- **What**: **Pairwise disjointness of distinct Frobenius translates** — upgrades wandering
  (disjointness from `W` itself) to full pairwise disjointness of the translate family.
- **How**: `Set.disjoint_left`: a point `y` in both translates has `yFrobTop i y ∈ W` and
  `yFrobTop j y ∈ W`. Additivity `yFrobTop_add` (with `norm_num` on `i + (j - i) = j`) shows
  `yFrobTop (j-i) (yFrobTop i y) = yFrobTop j y ∈ W`, i.e. `yFrobTop i y ∈ φ^{-(j-i)}W`, which
  contradicts `hdis (j-i) (by omega)` against `yFrobTop i y ∈ W`.
- **Hypotheses**: `W` wandering (`hdis`); `i ≠ j`.
- **Uses from project**: `yFrobTop`, `yFrobTop_add`
- **Used by**: `exists_translateFam_glue`
- **Visibility**: public
- **Lines**: 494–518 (proof 505–518, 14 lines)
- **Notes**: none

### `theorem translate_le_curvePreimage_xImage`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (k : ℤ) → (Opens.map (yFrobTop p F ϖ k)).obj W ≤ curvePreimage p F ϖ (xImage p F ϖ W)`
- **What**: Each Frobenius translate of `W` sits inside the saturation `π^{-1}(π(W))`.
- **How**: Rewrite with the saturation identity `curvePreimage_xImage` and apply `le_iSup` at index
  `k`.
- **Hypotheses**: standing package.
- **Uses from project**: `curvePreimage`, `xImage`, `curvePreimage_xImage`, `yFrobTop`
- **Used by**: `yFunctor_translate_le`, `ringStalkMap_piYHom_surjective`,
  `invariant_sections_eq_of_zero_piece`, `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 521–525 (proof 524–525, 2 lines)
- **Notes**: none

### `def translateFam`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) (k : ℤ) → ↥(limitSections ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ k)).obj W)))`
- **What**: **The translated-piece family** of a section `s` over `W`: the `k`-th member is the
  Frobenius transport of `s` to the `k`-th translate of `W`. This is the candidate family that will
  be glued into the `φ`-invariant extension.
- **How**: `limitFrobHom p F k` applied to `s`, then `limitRestrict` along the (equality)
  identification `yFunctor_frobOpens p F ϖ k W : frobOpens k (yFunctor W) = yFunctor (φ^{-k}W)`.
- **Hypotheses**: standing package.
- **Uses from project**: `limitSections`, `yFunctor`, `yFunctor_frobOpens`, `limitFrobHom`,
  `limitRestrict`, `yFrobTop`
- **Used by**: `exists_translateFam_glue`, `translateFam_zero`, `exists_glue_extending`,
  `translateFam_succ`, `glue_piece_eq`, `glue_invariant`
- **Visibility**: public
- **Lines**: 528–533 (6 lines)
- **Notes**: `noncomputable`

### `theorem yFunctor_translate_le`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (k : ℤ) → (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ k)).obj W) ≤ (yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W))`
- **What**: The ambient (image-of-open) form of "each translate sits in the saturation".
- **How**: Functoriality: `leOfHom ((yFunctor p F ϖ).map (homOfLE (translate_le_curvePreimage_xImage …)))`.
- **Hypotheses**: standing package.
- **Uses from project**: `yFunctor`, `translate_le_curvePreimage_xImage`, `curvePreimage`, `xImage`,
  `yFrobTop`
- **Used by**: `exists_translateFam_glue`, `exists_glue_extending`, `piece_le_frobOpens_sat`,
  `glue_piece_eq`, `glue_invariant`, `exists_invariant_extension`,
  `ringStalkMap_piYHom_surjective`
- **Visibility**: public
- **Lines**: 536–540 (term proof, 2 lines)
- **Notes**: none

### `theorem exists_translateFam_glue`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (hdis : ∀ k ≠ 0, Disjoint (φ^{-k}W) W) (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) → ∃ g : ↥(limitSections ((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))), ∀ k, limitRestrict (yFunctor_translate_le p F ϖ W k) g = translateFam p F ϖ W s k`
- **What**: **The glued invariant-candidate section over the saturation** (D-iv-3(ii-c β)): the
  translate family `translateFam` glues to a single section over `π^{-1}(π(W))`.
- **How**: Applies the `𝒴`-relative sheaf axiom `(isLimitSheafOn_Y p F ϖ).glue`. Its three inputs:
  the trace condition from `yFunctor_trace`; the cover condition, obtained by rewriting the
  saturation with `curvePreimage_xImage` and `Opens.coe_iSup` so every point of the saturation lies
  in some translate; and compatibility, which is `rfl` on the diagonal `i = j` and *vacuous*
  off-diagonal — there `translates_pairwise_disjoint` makes the intersection open empty, so
  `ValuationSpectrum.limitSections_subsingleton_of_empty` makes the overlap ring a subsingleton and
  `hsub.elim` closes the goal. The index type is lifted to `ULift ℤ` to meet the universe
  constraint of `IsLimitSheafOn`.
- **Hypotheses**: `W` wandering (`hdis`); standing package (so `isLimitSheafOn_Y` applies).
- **Uses from project**: `isLimitSheafOn_Y`, `yFunctor`, `yFunctor_trace`, `curvePreimage`,
  `xImage`, `curvePreimage_xImage`, `translateFam`, `yFunctor_translate_le`,
  `translates_pairwise_disjoint`, `limitSections_subsingleton_of_empty`, `limitRestrict`,
  `limitSections`, `SpaTop`, `Y`, `yFrobTop`
- **Used by**: `exists_glue_extending`
- **Visibility**: public
- **Lines**: 545–616 (proof 555–616, **62 lines**)
- **Notes**: proof >30 lines; `ULift ℤ` universe lift for the cover index

### `theorem yFunctor_translate_zero_le`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) → (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ 0)).obj W) ≤ (yFunctor p F ϖ).obj W`
- **What**: The zero-translate ambient open sits inside `W`'s ambient open (in fact they are equal).
- **How**: Functoriality applied to `le_of_eq (map_yFrobTop_zero p F ϖ W)`.
- **Hypotheses**: standing package.
- **Uses from project**: `yFunctor`, `map_yFrobTop_zero`, `yFrobTop`
- **Used by**: `translateFam_zero`, `exists_glue_extending`, `exists_invariant_extension`,
  `ringStalkMap_piYHom_surjective`
- **Visibility**: public
- **Lines**: 619–623 (term proof, 2 lines)
- **Notes**: none

### `theorem translateFam_zero`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) → translateFam p F ϖ W s 0 = limitRestrict (yFunctor_translate_zero_le p F ϖ W) s`
- **What**: **The zero piece of the translate family is just the plain restriction of `s`** — the
  anchoring fact for "the glued section extends `s`".
- **How**: Unfolds `translateFam` via `show`, rewrites the zero transport with `limitFrobHom_zero`,
  and then composes the two restrictions using `limitRestrict_comp` (along
  `yFunctor_frobOpens p F ϖ 0 W` and `frobOpens_zero`).
- **Hypotheses**: standing package.
- **Uses from project**: `translateFam`, `limitFrobHom`, `limitFrobHom_zero`, `limitRestrict`,
  `limitRestrict_comp`, `yFunctor`, `yFunctor_frobOpens`, `frobOpens_zero`,
  `yFunctor_translate_zero_le`
- **Used by**: `exists_glue_extending`
- **Visibility**: public
- **Lines**: 626–636 (proof 630–636, 7 lines)
- **Notes**: none

### `theorem exists_glue_extending`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (hdis : …) (s : …) → ∃ g, (∀ k, limitRestrict (yFunctor_translate_le … k) g = translateFam … k) ∧ limitRestrict (yFunctor_translate_le … 0) g = limitRestrict (yFunctor_translate_zero_le …) s`
- **What**: **Invariant-extension existence, extension form** (first half of D-iv-3(ii-c β)): the
  glued candidate restricts on the zero translate back to `s`.
- **How**: Takes `g` from `exists_translateFam_glue`, then chains `hg 0` with `translateFam_zero`.
- **Hypotheses**: `W` wandering.
- **Uses from project**: `exists_translateFam_glue`, `translateFam`, `translateFam_zero`,
  `yFunctor_translate_le`, `yFunctor_translate_zero_le`, `limitRestrict`, `curvePreimage`,
  `xImage`, `yFunctor`, `limitSections`
- **Used by**: `exists_invariant_extension`
- **Visibility**: public
- **Lines**: 640–653 (proof 652–653, 2 lines)
- **Notes**: none

### `theorem frobOpens_add`
- **Type**: `(k l : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) → frobOpens p F (k + l) W = frobOpens p F k (frobOpens p F l W)`
- **What**: Additivity of the Frobenius preimage operation on opens.
- **How**: `Opens.ext` + `ext v`; rewrite the membership statement with `spaFrob_add`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobOpens`, `spaFrob`, `spaFrob_add`
- **Used by**: `limitFrobHom_add`, `limitFrobHom_double`, `translateFam_succ`,
  `frobOpens_inv_collapse`, `limitFrobHom_leftInv`
- **Visibility**: public
- **Lines**: 656–663 (proof 658–663, 6 lines)
- **Notes**: none

### `theorem frobPow_trans`
- **Type**: `(a b : ℤ) → (frobPow p F a).trans (frobPow p F b) = frobPow p F (a + b)`
- **What**: Frobenius powers compose as ring equivalences (`trans` form).
- **How**: `RingEquiv.ext` reduces to pointwise; `frobPow_toRingHom_comp p F b a` gives the
  composite for `b + a`, and `add_comm` rewrites the exponent to `a + b`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobPow`, `frobPow_toRingHom_comp`
- **Used by**: `frobPow_trans_neg`
- **Visibility**: public
- **Lines**: 666–673 (proof 668–673, 6 lines)
- **Notes**: none

### `theorem frobPow_trans_neg`
- **Type**: `(k l : ℤ) → (frobPow p F (-k)).trans (frobPow p F (-l)) = frobPow p F (-(k + l))`
- **What**: The negated-exponent form of composition, matching the sign convention of
  `limitFrobHom` (which transports along `frobPow (-k)`).
- **How**: `rw [frobPow_trans p F (-k) (-l)]` then `congr 1` + `omega` on the integer exponent.
- **Hypotheses**: standing package.
- **Uses from project**: `frobPow`, `frobPow_trans`
- **Used by**: `mapHuber_frobPow_add`, `limitFrobHom_add`
- **Visibility**: public
- **Lines**: 676–680 (proof 678–680, 3 lines)
- **Notes**: none

### `theorem mapHuber_frobPow_add`
- **Type**: `(k l : ℤ) (D : RationalLocData (Ainf p F)) → (D.mapHuber (frobPow p F (-k)) … ).mapHuber (frobPow p F (-l)) … = D.mapHuber (frobPow p F (-(k+l))) …`
- **What**: The double transport of a rational localization datum equals the single transport along
  the summed exponent.
- **How**: `RationalLocData.mapHuber_comp` collapses the two transports into one along the composite
  equivalence, and `RationalLocData.mapHuber_congr_e` with `frobPow_trans_neg` replaces the
  composite by `frobPow (-(k+l))`.
- **Hypotheses**: standing package; continuity of `frobPow` and its inverse (supplied by
  `continuous_frobPow`, `continuous_frobPow_symm`).
- **Uses from project**: `RationalLocData`, `RationalLocData.mapHuber`,
  `RationalLocData.mapHuber_comp`, `RationalLocData.mapHuber_congr_e`, `frobPow`,
  `frobPow_trans_neg`, `continuous_frobPow`, `continuous_frobPow_symm`
- **Used by**: `limitFrobHom_add`
- **Visibility**: public
- **Lines**: 683–695 (proof 689–695, 7 lines)
- **Notes**: none

### `theorem limitFrobHom_add`
- **Type**: `(k l : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (s : ↥(limitSections W)) → limitFrobHom p F (k + l) W s = limitRestrict (le_of_eq (frobOpens_add p F k l W)) (limitFrobHom p F k (frobOpens p F l W) (limitFrobHom p F l W s))`
- **What**: **Additivity of the limit transport**: transporting by `k + l` is the same as
  transporting by `l` then by `k` (up to the canonical identification of the two preimage opens).
- **How**: Componentwise (`Subtype.ext (funext fun E => …)`) at a rational index `E`. Sets up the
  reindexed `Elift`, and establishes four inclusions of rational opens by `rw` with
  `RationalLocData.mapHuber_comp` / `mapHuber_frobPow_add` / `RationalLocData.mapHuber_congr_e`.
  Then the value-level composition law
  `ValuationSpectrum.presheafValueRingEquivHuber_comp_symm_apply` (h1) turns the double
  `presheafValueRingEquivHuber…symm` into the transport along the composite equivalence, and
  `presheafValueRingEquivHuber_congr_e_symm` (h2, via `frobPow_trans_neg`) rewrites that composite
  as the `-(k+l)` transport; finally `restrictionMap_comp` (h3) plus the section's compatibility
  field `s.2` between `frobIndex l (frobIndex k Elift)` and `frobIndex (k+l) E` (h4) identify the two
  coordinate values. The final `show` spells out both sides in `presheafValueRingEquivHuber…symm`
  form before `rw [h1, h2]` and `congrArg`.
- **Hypotheses**: standing package; `s` a compatible family.
- **Uses from project**: `limitFrobHom`, `limitRestrict`, `frobOpens`, `frobOpens_add`, `frobPow`,
  `frobPow_trans_neg`, `mapHuber_frobPow_add`, `continuous_frobPow`, `continuous_frobPow_symm`,
  `RationalLocData.mapHuber`, `RationalLocData.mapHuber_comp`, `RationalLocData.mapHuber_congr_e`,
  `presheafValueRingEquivHuber`, `presheafValueRingEquivHuber_comp_symm_apply`,
  `presheafValueRingEquivHuber_congr_e_symm`, `restrictionMap`, `restrictionMap_comp`, `frobIndex`,
  `RationalIndex`, `rationalOpen`, `presheafValue`, `limitSections`
- **Used by**: `limitFrobHom_double`
- **Visibility**: public
- **Lines**: 699–827 (proof 706–827, **122 lines**)
- **Notes**: proof >30 lines — the longest single computation in the file

### `theorem map_yFrobTop_shift`
- **Type**: `(m : ℤ) (W : Opens ↥(yTop p F ϖ)) → (Opens.map (yFrobTop p F ϖ 1)).obj ((Opens.map (yFrobTop p F ϖ m)).obj W) = (Opens.map (yFrobTop p F ϖ (1 + m))).obj W`
- **What**: The carrier-level translate shift, written subtraction-free: applying `φ` to the `m`-th
  translate gives the `(1+m)`-th.
- **How**: `Opens.ext` + `ext y`; the membership goal is closed by rewriting with
  `← yFrobTop_add p F ϖ 1 m y`.
- **Hypotheses**: standing package.
- **Uses from project**: `yFrobTop`, `yFrobTop_add`
- **Used by**: `piece_shift`
- **Visibility**: public
- **Lines**: 830–838 (proof 833–838, 6 lines)
- **Notes**: subtraction-free formulation is deliberate (keeps `Int.induction_on` steps clean)

### `theorem piece_shift`
- **Type**: `(m : ℤ) (W : Opens ↥(yTop p F ϖ)) → frobOpens p F 1 ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ m)).obj W)) = (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W)`
- **What**: **The piece shift** at the ambient level: the Frobenius preimage of the `m`-th translate
  piece is the `(1+m)`-th piece.
- **How**: `rw [yFunctor_frobOpens p F ϖ 1 …]` moves the Frobenius preimage inside the image functor,
  then `map_yFrobTop_shift` collapses the doubled `Opens.map`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobOpens`, `yFunctor`, `yFunctor_frobOpens`, `map_yFrobTop_shift`,
  `yFrobTop`
- **Used by**: `translateFam_succ`, `piece_le_frobOpens_sat`, `glue_piece_eq`,
  `piece_le_frobOpens_general`, `invariant_piece_transport`, `invariant_piece_back'`
- **Visibility**: public
- **Lines**: 842–847 (proof 846–847, 2 lines)
- **Notes**: none

### `theorem limitFrobHom_double`
- **Type**: `(k l : ℤ) (W : …) (s : ↥(limitSections W)) → limitFrobHom p F k (frobOpens p F l W) (limitFrobHom p F l W s) = limitRestrict (le_of_eq (frobOpens_add p F k l W).symm) (limitFrobHom p F (k + l) W s)`
- **What**: The inverted form of additivity: the double transport is the *restriction* of the sum
  transport (rather than the sum transport being a restriction of the double).
- **How**: Rewrites with `limitFrobHom_add`, then cancels the two opposite restrictions using
  `limitRestrict_comp` (along `frobOpens_add …` and its symm) followed by `limitRestrict_id`.
- **Hypotheses**: standing package.
- **Uses from project**: `limitFrobHom`, `limitFrobHom_add`, `limitRestrict`, `limitRestrict_comp`,
  `limitRestrict_id`, `frobOpens`, `frobOpens_add`, `limitSections`
- **Used by**: `translateFam_succ`, `limitFrobHom_leftInv`
- **Visibility**: public
- **Lines**: 851–865 (proof 857–865, 9 lines)
- **Notes**: none

### `theorem translateFam_succ`
- **Type**: `(m : ℤ) (W : Opens ↥(yTop p F ϖ)) (s : …) → limitRestrict (le_of_eq (piece_shift p F ϖ m W)) (translateFam p F ϖ W s (1 + m)) = limitFrobHom p F 1 ((yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ m)).obj W)) (translateFam p F ϖ W s m)`
- **What**: **The translate-family recurrence**: the generator transport `φ` carries the `m`-th piece
  of the family to the `(1+m)`-th piece.
- **How**: `show` both sides unfolded through `translateFam`, then push `limitFrobHom 1` past the
  restriction with `limitFrobHom_limitRestrict`, replace the double transport by the sum transport
  with `limitFrobHom_double p F 1 m`, and finally compare the two remaining restriction composites
  via two `limitRestrict_comp` instances (one through `piece_shift`/`yFunctor_frobOpens (1+m)`, the
  other through `frobOpens_mono` and `frobOpens_add 1 m`).
- **Hypotheses**: standing package.
- **Uses from project**: `translateFam`, `piece_shift`, `limitFrobHom`, `limitFrobHom_double`,
  `limitFrobHom_limitRestrict`, `limitRestrict`, `limitRestrict_comp`, `frobOpens_mono`,
  `frobOpens_add`, `yFunctor`, `yFunctor_frobOpens`, `yFrobTop`
- **Used by**: `glue_piece_eq`
- **Visibility**: public
- **Lines**: 869–896 (proof 876–896, 21 lines)
- **Notes**: none

### `theorem piece_le_frobOpens_sat`
- **Type**: `(m : ℤ) (W : Opens ↥(yTop p F ϖ)) → (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1 + m))).obj W) ≤ frobOpens p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))`
- **What**: The `(1+m)`-th piece lies inside the Frobenius preimage of the saturation — the
  inclusion needed to state the per-piece invariance computation.
- **How**: `rw [← piece_shift p F ϖ m W]` turns the goal into a Frobenius preimage of an inclusion,
  discharged by `frobOpens_mono p F 1 (yFunctor_translate_le p F ϖ W m)`.
- **Hypotheses**: standing package.
- **Uses from project**: `piece_shift`, `frobOpens`, `frobOpens_mono`, `yFunctor`,
  `yFunctor_translate_le`, `curvePreimage`, `xImage`, `yFrobTop`
- **Used by**: `glue_piece_eq`, `glue_invariant`
- **Visibility**: public
- **Lines**: 900–905 (proof 904–905, 2 lines)
- **Notes**: none

### `theorem pieces_cover_frobOpens_sat`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (hv : v ∈ frobOpens p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W)))) → ∃ m : ℤ, v ∈ (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1+m))).obj W)`
- **What**: The shifted pieces `{φ^{-(1+m)}W}_{m ∈ ℤ}` cover the Frobenius preimage of the saturation
  (membership form) — the cover needed for the separation argument in `glue_invariant`.
- **How**: `frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage W)` collapses the Frobenius preimage of
  the saturation back to the saturation itself; then unpack `v` as an image point `y`, use
  `curvePreimage_xImage` + `Opens.coe_iSup` to get `y ∈ φ^{-k}W` for some `k`, and take `m = k - 1`
  after rewriting `1 + (k - 1) = k` with `omega`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobOpens`, `frobOpens_yFunctor_curvePreimage`, `yFunctor`,
  `curvePreimage`, `curvePreimage_xImage`, `xImage`, `yFrobTop`
- **Used by**: `glue_invariant`
- **Visibility**: public
- **Lines**: 909–928 (proof 915–928, 14 lines)
- **Notes**: none

### `theorem glue_piece_eq`
- **Type**: `(W) (s) (g) (hg : ∀ k, limitRestrict (yFunctor_translate_le p F ϖ W k) g = translateFam p F ϖ W s k) (m : ℤ) → limitRestrict (piece_le_frobOpens_sat p F ϖ m W) (limitFrobHom p F 1 … g) = limitRestrict (piece_le_frobOpens_sat p F ϖ m W) (limitRestrict (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W))) g)`
- **What**: **The per-piece invariance computation**: on each shifted piece, the Frobenius transport
  of the glued section agrees with its restriction along the stability equality.
- **How**: A six-step `calc`. Left side: `limitRestrict_comp` splits the piece inclusion through
  `piece_shift`/`frobOpens_mono`; `limitFrobHom_limitRestrict` moves the transport inside;
  `hg m` replaces the restricted `g` by `translateFam … m`; `translateFam_succ` (backwards) turns
  the transported `m`-piece into the restricted `(1+m)`-piece; the two opposite `piece_shift`
  restrictions cancel by `limitRestrict_comp` + `limitRestrict_id`, leaving `translateFam … (1+m)`.
  Right side: `hg (1+m)` (backwards) rewrites that as the `(1+m)`-restriction of `g`, and a final
  `limitRestrict_comp` regroups it through `frobOpens_yFunctor_curvePreimage`.
- **Hypotheses**: `g` glues the translate family (`hg`); standing package.
- **Uses from project**: `limitRestrict`, `limitRestrict_comp`, `limitRestrict_id`, `limitFrobHom`,
  `limitFrobHom_limitRestrict`, `piece_shift`, `piece_le_frobOpens_sat`, `frobOpens_mono`,
  `frobOpens_yFunctor_curvePreimage`, `yFunctor`, `yFunctor_translate_le`, `translateFam`,
  `translateFam_succ`, `curvePreimage`, `xImage`, `yFrobTop`, `limitSections`
- **Used by**: `glue_invariant`
- **Visibility**: public
- **Lines**: 932–994 (proof 945–994, **50 lines**)
- **Notes**: proof >30 lines

### `theorem glue_invariant`
- **Type**: `(W) (s) (g) (hg : ∀ k, limitRestrict (yFunctor_translate_le p F ϖ W k) g = translateFam p F ϖ W s k) → limitFrobHom p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ (xImage p F ϖ W))) g = limitRestrict (le_of_eq (frobOpens_yFunctor_curvePreimage p F ϖ 1 (xImage p F ϖ W))) g`
- **What**: **The glued section is `φ`-invariant** (D-iv-3(ii-c β), completed) — i.e. `g` lies in
  `frobFixed`.
- **How**: Sheaf separation: applies `(isLimitSheafOn_Y p F ϖ).injective` on the open
  `frobOpens 1 (yFunctor (π^{-1}(π W)))` with the cover by shifted pieces. The trace hypothesis comes
  from `frobOpens_yFunctor_curvePreimage` + `yFunctor_trace`, the cover from
  `pieces_cover_frobOpens_sat` (lifted to `ULift ℤ`), and the per-piece agreement is exactly
  `glue_piece_eq`.
- **Hypotheses**: `g` glues the translate family; standing package.
- **Uses from project**: `isLimitSheafOn_Y`, `yFunctor`, `yFunctor_trace`, `yFunctor_translate_le`,
  `frobOpens`, `frobOpens_yFunctor_curvePreimage`, `piece_le_frobOpens_sat`,
  `pieces_cover_frobOpens_sat`, `glue_piece_eq`, `limitFrobHom`, `limitRestrict`, `translateFam`,
  `curvePreimage`, `xImage`, `yFrobTop`, `Y`
- **Used by**: `exists_invariant_extension`
- **Visibility**: public
- **Lines**: 998–1029 (proof 1008–1029, 22 lines)
- **Notes**: `ULift ℤ` universe lift for the cover index

### `theorem exists_invariant_extension`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (hdis : ∀ k ≠ 0, Disjoint (φ^{-k}W) W) (s : ↥(limitSections ((yFunctor p F ϖ).obj W))) → ∃ g : ↥(frobFixed p F ϖ (xImage p F ϖ W)), limitRestrict (yFunctor_translate_le p F ϖ W 0) g.1 = limitRestrict (yFunctor_translate_zero_le p F ϖ W) s`
- **What**: **The invariant extension** (D-iv-3(ii-c β), bundled): every `𝒴`-section over a
  wandering-separated open `W` extends to a `φ`-invariant section of the curve presheaf over
  `xImage W`, restricting back to `s` on the zero translate.
- **How**: Combines `exists_glue_extending` (which produces the glued `g` together with the
  zero-translate identity) with `glue_invariant` (which certifies `g ∈ frobFixed`), packaging the
  pair as a subtype element.
- **Hypotheses**: `W` wandering (`hdis`).
- **Uses from project**: `exists_glue_extending`, `glue_invariant`, `frobFixed`, `xImage`,
  `yFunctor_translate_le`, `yFunctor_translate_zero_le`, `limitRestrict`, `yFunctor`,
  `limitSections`, `yFrobTop`
- **Used by**: `ringStalkMap_piYHom_surjective`
- **Visibility**: public
- **Lines**: 1035–1045 (proof 1044–1045, 2 lines)
- **Notes**: none

### `theorem ringStalkMap_piYHom_germ`
- **Type**: `(y : ↥(yTop p F ϖ)) (V : Opens (Curve p F ϖ)) (hy : yTopToCurve p F ϖ y ∈ V) (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op V))) → (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom ((curveSpace p F ϖ).ringPresheaf.germ V (yTopToCurve p F ϖ y) hy t) = (yPresheafedSpace p F ϖ).ringPresheaf.germ ((Opens.map (yTopToCurveTop p F ϖ)).obj V) y hy (piComponent p F ϖ V t)`
- **What**: **Germ naturality of the projection stalk map**: the stalk map of `π` sends the germ of
  an invariant section to the germ of its underlying `𝒴`-section.
- **How**: Unfolds `ringStalkMap` (an `rfl`-level `hunfold`) into
  `stalkFunctor.map (whiskerRight (piYHom).c forgetToCommRingCat) ≫ stalkPushforward`, then applies
  the two mathlib germ lemmas in sequence: `TopCat.Presheaf.stalkFunctor_map_germ_apply` (h1) and
  `TopCat.Presheaf.stalkPushforward_germ_apply` (h2). An `rfl`-level `hsplit` factors the
  `ConcreteCategory.hom` of the composite into the composite of the two `ConcreteCategory.hom`s, so
  the two lemmas can be applied one after the other via `congrArg`/`trans`.
- **Hypotheses**: standing package; `y` a point over `V`.
- **Uses from project**: `ringStalkMap`, `piYHom`, `curveSpace`, `yPresheafedSpace`,
  `yTopToCurve`, `yTopToCurveTop`, `piComponent`, `TopRingPresheafedSpace.ringPresheaf`,
  `CompleteTopCommRingCat.forgetToCommRingCat`
- **Used by**: `ringStalkMap_piYHom_surjective`, `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 1050–1108 (proof 1058–1108, **51 lines**)
- **Notes**: proof >30 lines; almost entirely bookkeeping of `ConcreteCategory.hom` layers

### `theorem yRingPresheaf_map_apply`
- **Type**: `{V' V : Opens ↥(yTop p F ϖ)} (h : V' ≤ V) (f : ToType ((yPresheafedSpace p F ϖ).ringPresheaf.obj (op V))) → (ConcreteCategory.hom ((yPresheafedSpace p F ϖ).ringPresheaf.map (homOfLE h).op)) f = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE h))) f`
- **What**: The `𝒴`-presheaf's restriction map, applied to an element, is the concrete
  `limitRestrict` at the `yFunctor` level.
- **How**: Directly `structurePresheaf_map (((yFunctor p F ϖ).map (homOfLE h)).op) f` — the ambient
  structure presheaf's map is by definition `limitRestrict`.
- **Hypotheses**: `V' ≤ V`.
- **Uses from project**: `yPresheafedSpace`, `yFunctor`, `limitRestrict`, `structurePresheaf_map`,
  `TopRingPresheafedSpace.ringPresheaf`
- **Used by**: `yGerm_limitRestrict`, `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 1112–1117 (term proof, 1 line)
- **Notes**: none

### `theorem yGerm_limitRestrict`
- **Type**: `{V' V : Opens ↥(yTop p F ϖ)} (h : V' ≤ V) {y : ↥(yTop p F ϖ)} (hy : y ∈ V') (f : …) → (yPresheafedSpace p F ϖ).ringPresheaf.germ V' y hy (limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE h))) f) = (yPresheafedSpace p F ϖ).ringPresheaf.germ V y (h hy) f`
- **What**: Germ-restriction collapse: taking the germ of a restricted section is the same as taking
  the germ upstairs.
- **How**: `rw [← yRingPresheaf_map_apply p F ϖ h f]` puts the restriction back into presheaf-map
  form, then mathlib's `TopCat.Presheaf.germ_res_apply` applies.
- **Hypotheses**: `V' ≤ V`, `y ∈ V'`.
- **Uses from project**: `yPresheafedSpace`, `yRingPresheaf_map_apply`, `limitRestrict`, `yFunctor`,
  `TopRingPresheafedSpace.ringPresheaf`
- **Used by**: `ringStalkMap_piYHom_surjective`
- **Visibility**: public
- **Lines**: 1121–1129 (proof 1127–1129, 3 lines)
- **Notes**: none

### `theorem ringStalkMap_piYHom_surjective`
- **Type**: `(y : ↥(yTop p F ϖ)) → Function.Surjective (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom`
- **What**: **Surjectivity of the projection stalk map** (D-iv-3(γ ii)): every germ of the
  `𝒴`-presheaf lifts to a germ of the curve's (invariant) structure presheaf.
- **How**: Writes the target germ as `germ U y f` (`exists_germ_eq`), shrinks `U` by intersecting
  with a wandering neighbourhood `W₀` from `exists_disjoint_translates` (so `W = U ⊓ W₀` still
  contains `y` and is wandering — `Disjoint.mono` on the two projections), restricts `f` to `fW`, and
  applies `exists_invariant_extension` to get an invariant `t` over `xImage W` with
  `limitRestrict … t.1 = limitRestrict … fW` on the zero translate. The candidate preimage germ is
  `germ (xImage W) (yTopToCurve y) hmem t`; `ringStalkMap_piYHom_germ` computes its image, and a
  three-step chain of `yGerm_limitRestrict` (through the zero-translate inclusion
  `translate_le_curvePreimage_xImage … 0`, through `map_yFrobTop_zero`, and through `inf_le_left`)
  identifies it with `germ U y f`; `yFrobTop_zero` supplies the zero-translate membership `hy0`.
- **Hypotheses**: standing package; wandering at `y` (via `exists_disjoint_translates`).
- **Uses from project**: `ringStalkMap`, `piYHom`, `yPresheafedSpace`, `curveSpace`,
  `exists_disjoint_translates`, `exists_invariant_extension`, `ringStalkMap_piYHom_germ`,
  `yGerm_limitRestrict`, `yFrobTop`, `yFrobTop_zero`, `map_yFrobTop_zero`, `xImage`, `yTopToCurve`,
  `yTopToCurveTop`, `piComponent`, `limitRestrict`, `yFunctor`, `yFunctor_translate_le`,
  `yFunctor_translate_zero_le`, `translate_le_curvePreimage_xImage`
- **Used by**: `ringStalkMap_piYHom_bijective`
- **Visibility**: public
- **Lines**: 1133–1192 (proof 1136–1192, **57 lines**)
- **Notes**: proof >30 lines

### `theorem piece_le_frobOpens_general`
- **Type**: `(V : Opens (Curve p F ϖ)) (m : ℤ) {W : Opens ↥(yTop p F ϖ)} (hWle : ∀ k, (Opens.map (yFrobTop p F ϖ k)).obj W ≤ curvePreimage p F ϖ V) → (yFunctor p F ϖ).obj ((Opens.map (yFrobTop p F ϖ (1+m))).obj W) ≤ frobOpens p F 1 ((yFunctor p F ϖ).obj (curvePreimage p F ϖ V))`
- **What**: The general (not just `xImage`) piece inclusion into the Frobenius preimage of a
  saturated open.
- **How**: `rw [← piece_shift p F ϖ m W]` then `frobOpens_mono p F 1` applied to the functorial image
  of `hWle m`.
- **Hypotheses**: every translate of `W` lies in `π^{-1}V` (`hWle`).
- **Uses from project**: `piece_shift`, `frobOpens`, `frobOpens_mono`, `yFunctor`, `curvePreimage`,
  `yFrobTop`
- **Used by**: `invariant_piece_transport`
- **Visibility**: public
- **Lines**: 1196–1204 (proof 1202–1204, 3 lines)
- **Notes**: none

### `theorem invariant_piece_transport`
- **Type**: `(V : Opens (Curve p F ϖ)) (t : ↥(frobFixed p F ϖ V)) (m : ℤ) {W} (hWle : ∀ k, φ^{-k}W ≤ curvePreimage p F ϖ V) → limitRestrict (…hWle (1+m)…) t.1 = limitRestrict (le_of_eq (piece_shift p F ϖ m W).symm) (limitFrobHom p F 1 (…m-piece…) (limitRestrict (…hWle m…) t.1))`
- **What**: **The invariant piece transport**: for a `φ`-invariant section `t`, its restriction to the
  `(1+m)`-th piece is the Frobenius transport of its restriction to the `m`-th piece.
- **How**: A four-step `calc`. Starting from the `(1+m)`-restriction, `limitRestrict_comp`
  (through `piece_le_frobOpens_general` and the stability equality
  `frobOpens_yFunctor_curvePreimage`) rewrites it as a restriction of the stability restriction;
  the invariance hypothesis `t.2` (unfolded as `hinv`) replaces that by the Frobenius transport;
  `limitRestrict_comp` through `piece_shift`/`frobOpens_mono` regroups; and
  `limitFrobHom_limitRestrict` moves the transport inside the `m`-piece restriction.
- **Hypotheses**: `t` invariant; all translates of `W` inside `π^{-1}V`.
- **Uses from project**: `frobFixed`, `limitRestrict`, `limitRestrict_comp`, `limitFrobHom`,
  `limitFrobHom_limitRestrict`, `piece_shift`, `piece_le_frobOpens_general`, `frobOpens_mono`,
  `frobOpens_yFunctor_curvePreimage`, `yFunctor`, `curvePreimage`, `yFrobTop`
- **Used by**: `invariant_piece_step`, `invariant_piece_back'`
- **Visibility**: public
- **Lines**: 1208–1254 (proof 1219–1254, **36 lines**)
- **Notes**: proof >30 lines

### `theorem invariant_piece_step`
- **Type**: `(V) (t t' : ↥(frobFixed p F ϖ V)) (m : ℤ) {W} (hWle) (hm : t, t' agree on the m-piece) → t, t' agree on the (1+m)-piece`
- **What**: **The piece step**: two invariant sections agreeing on the `m`-th piece agree on the
  `(1+m)`-th.
- **How**: `rw` with `invariant_piece_transport` for both `t` and `t'`, then `hm` — both sides become
  the transport of the same `m`-piece restriction.
- **Hypotheses**: `t`, `t'` invariant; translates inside `π^{-1}V`; agreement on the `m`-piece.
- **Uses from project**: `frobFixed`, `invariant_piece_transport`, `limitRestrict`, `yFunctor`,
  `curvePreimage`, `yFrobTop`
- **Used by**: `invariant_piece_step'`, `invariant_pieces_eq`
- **Visibility**: public
- **Lines**: 1258–1272 (proof 1271–1272, 2 lines)
- **Notes**: none

### `theorem frobOpens_inv_collapse`
- **Type**: `(a : ℤ) (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) → frobOpens p F (-a) (frobOpens p F a U) = U`
- **What**: The Frobenius preimage operation is invertible on opens: `φ^{-(-a)} ∘ φ^{-a} = id`.
- **How**: `← frobOpens_add p F (-a) a U`, then `(-a) + a = 0` by `omega`, then `frobOpens_zero`.
- **Hypotheses**: standing package.
- **Uses from project**: `frobOpens`, `frobOpens_add`, `frobOpens_zero`
- **Used by**: `limitFrobHom_leftInv`, `limitFrobHom_injective`
- **Visibility**: public
- **Lines**: 1278–1283 (proof 1280–1283, 4 lines)
- **Notes**: opens the "transport inversion toolkit" section (D-iv-3 γ-iii)

### `theorem limitFrobHom_eq_zero_of`
- **Type**: `(c : ℤ) (hc : c = 0) (U : …) (s : ↥(limitSections U)) (hUc : frobOpens p F c U = U) → limitFrobHom p F c U s = limitRestrict (le_of_eq hUc) s`
- **What**: The zero-sum transport collapse in an index-generalised form (the exponent is only
  *propositionally* zero, and the stability proof is an arbitrary one).
- **How**: `subst hc` reduces to `limitFrobHom_zero`; proof-irrelevance for `hUc` is automatic since
  the restriction depends only on the `≤`.
- **Hypotheses**: `c = 0`; a stability witness `hUc`.
- **Uses from project**: `limitFrobHom`, `limitFrobHom_zero`, `limitRestrict`, `frobOpens`,
  `limitSections`
- **Used by**: `limitFrobHom_leftInv`
- **Visibility**: public
- **Lines**: 1286–1292 (proof 1291–1292, 2 lines)
- **Notes**: none

### `theorem limitFrobHom_leftInv`
- **Type**: `(a : ℤ) (U : …) (s : ↥(limitSections U)) → limitFrobHom p F (-a) (frobOpens p F a U) (limitFrobHom p F a U s) = limitRestrict (le_of_eq (frobOpens_inv_collapse p F a U)) s`
- **What**: **The left inverse of the limit transport**: transporting by `a` and then by `-a` returns
  `s` (up to the canonical open identification).
- **How**: `limitFrobHom_double p F (-a) a` turns the double transport into a restriction of the
  `((-a)+a)`-transport; `limitFrobHom_eq_zero_of` (with `omega` for `(-a)+a = 0` and the stability
  witness built from `frobOpens_zero`) collapses that to a restriction; and `limitRestrict_comp`
  merges the two restrictions.
- **Hypotheses**: standing package.
- **Uses from project**: `limitFrobHom`, `limitFrobHom_double`, `limitFrobHom_eq_zero_of`,
  `limitRestrict`, `limitRestrict_comp`, `frobOpens`, `frobOpens_add`, `frobOpens_zero`,
  `frobOpens_inv_collapse`, `limitSections`
- **Used by**: `limitFrobHom_injective`
- **Visibility**: public
- **Lines**: 1295–1307 (proof 1300–1307, 8 lines)
- **Notes**: none

### `theorem limitRestrict_eq_injective`
- **Type**: `{U U' : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} (h : U = U') → Function.Injective (limitRestrict (A := Ainf p F) (le_of_eq h))`
- **What**: Restriction along an *equality* of opens is injective (it is in fact an isomorphism, but
  injectivity is all that is needed).
- **How**: A three-step `calc`: apply `limitRestrict (le_of_eq h.symm)` to the assumed equation, and
  use `limitRestrict_comp` followed by `limitRestrict_id U'` to see that the round trip is the
  identity on both `X` and `X'`.
- **Hypotheses**: `U = U'`.
- **Uses from project**: `limitRestrict`, `limitRestrict_comp`, `limitRestrict_id`, `Ainf`,
  `ringPlus`
- **Used by**: `limitFrobHom_injective`, `invariant_piece_back'`
- **Visibility**: public
- **Lines**: 1310–1324 (proof 1313–1324, 12 lines)
- **Notes**: none

### `theorem limitFrobHom_injective`
- **Type**: `(a : ℤ) (U : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) → Function.Injective (limitFrobHom p F a U)`
- **What**: **The limit transport is injective** — the fact that makes an invariant section
  determined by its zero piece.
- **How**: Apply the `(-a)`-transport to the assumed equality, rewrite both sides with
  `limitFrobHom_leftInv` (so both become restrictions along `frobOpens_inv_collapse`), and conclude
  with `limitRestrict_eq_injective`.
- **Hypotheses**: standing package.
- **Uses from project**: `limitFrobHom`, `limitFrobHom_leftInv`, `limitRestrict_eq_injective`,
  `frobOpens`, `frobOpens_inv_collapse`
- **Used by**: `invariant_piece_back'`
- **Visibility**: public
- **Lines**: 1327–1333 (proof 1329–1333, 5 lines)
- **Notes**: none

### `theorem invariant_piece_step'`
- **Type**: `(V) (t t' : ↥(frobFixed p F ϖ V)) (m k : ℤ) (hk : 1 + m = k) {W} (hWle) (hm : agreement on m-piece) → agreement on k-piece`
- **What**: The forward piece step in index-flexible form (the successor index is given
  propositionally, so it can be `n + 1` rather than `1 + n`).
- **How**: `subst hk` then `invariant_piece_step`.
- **Hypotheses**: `1 + m = k`; the same invariance/inclusion/agreement hypotheses as
  `invariant_piece_step`.
- **Uses from project**: `frobFixed`, `invariant_piece_step`, `limitRestrict`, `yFunctor`,
  `curvePreimage`, `yFrobTop`
- **Used by**: `invariant_pieces_eq`
- **Visibility**: public
- **Lines**: 1336–1349 (proof 1348–1349, 2 lines)
- **Notes**: none

### `theorem invariant_piece_back'`
- **Type**: `(V) (t t' : ↥(frobFixed p F ϖ V)) (m k : ℤ) (hk : 1 + m = k) {W} (hWle) (hkeq : agreement on k-piece) → agreement on m-piece`
- **What**: **The backward piece step**: agreement on the `(1+m)`-th piece forces agreement on the
  `m`-th — the descending half of the induction.
- **How**: `subst hk`; rewrite both sides of `hkeq` with `invariant_piece_transport`; then peel the
  two wrappers: `limitRestrict_eq_injective` (through `(piece_shift … m W).symm`) removes the
  restriction, and `limitFrobHom_injective p F 1` removes the transport.
- **Hypotheses**: `1 + m = k`; `t`, `t'` invariant; translates inside `π^{-1}V`; agreement on the
  `k`-piece.
- **Uses from project**: `frobFixed`, `invariant_piece_transport`, `limitRestrict_eq_injective`,
  `limitFrobHom_injective`, `piece_shift`, `limitRestrict`, `yFunctor`, `curvePreimage`, `yFrobTop`
- **Used by**: `invariant_pieces_eq`
- **Visibility**: public
- **Lines**: 1352–1370 (proof 1364–1370, 7 lines)
- **Notes**: none

### `theorem invariant_pieces_eq`
- **Type**: `(V) (t t' : ↥(frobFixed p F ϖ V)) {W} (hWle : ∀ j, φ^{-j}W ≤ curvePreimage p F ϖ V) (h0 : agreement on the 0-piece) (k : ℤ) → agreement on the k-piece`
- **What**: **Invariant sections agreeing on the zero piece agree on every piece** — the heart of the
  separation argument.
- **How**: `Int.induction_on` on `k`: the base case is `h0`; the successor case is
  `invariant_piece_step'` with `(n, n+1)` and `omega`; the predecessor case is
  `invariant_piece_back'` with `(-n-1, -n)` and `omega`.
- **Hypotheses**: `t`, `t'` invariant; all translates of `W` inside `π^{-1}V`; agreement on the
  zero piece.
- **Uses from project**: `frobFixed`, `invariant_piece_step`, `invariant_piece_step'`,
  `invariant_piece_back'`, `limitRestrict`, `yFunctor`, `curvePreimage`, `yFrobTop`
- **Used by**: `invariant_sections_eq_of_zero_piece`
- **Visibility**: public
- **Lines**: 1373–1390 (proof 1384–1390, 7 lines)
- **Notes**: none

### `theorem xImage_le`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (V : Opens (Curve p F ϖ)) (h : W ≤ curvePreimage p F ϖ V) → xImage p F ϖ W ≤ V`
- **What**: The image bound: if an open of the carrier lies inside a saturated preimage, its image on
  the curve lies inside the saturating open.
- **How**: `rintro x ⟨w, hw, rfl⟩` — a point of `xImage W` is `yTopToCurve w` for `w ∈ W`, and `h hw`
  says precisely that `yTopToCurve w ∈ V`.
- **Hypotheses**: `W ≤ curvePreimage V`.
- **Uses from project**: `xImage`, `curvePreimage`, `yTopToCurve`
- **Used by**: `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 1394–1397 (proof 1395–1397, 2 lines)
- **Notes**: none

### `theorem invariant_sections_eq_of_zero_piece`
- **Type**: `(W : Opens ↥(yTop p F ϖ)) (t t' : ↥(frobFixed p F ϖ (xImage p F ϖ W))) (h0 : t, t' agree on the zero translate) → t = t'`
- **What**: **Separation of invariant sections** (D-iv-3(γ iii), section level): two `φ`-invariant
  sections over a saturation that agree on the zero translate are equal.
- **How**: `invariant_pieces_eq` (with `hWle := translate_le_curvePreimage_xImage`) upgrades the
  zero-piece agreement to agreement on every translate; then `Subtype.ext` and
  `(isLimitSheafOn_Y p F ϖ).injective` over the translate cover — the cover condition comes from
  rewriting `curvePreimage (xImage W)` with `curvePreimage_xImage` and `Opens.coe_iSup`, and the
  trace condition from `yFunctor_trace`. Index type lifted to `ULift ℤ`.
- **Hypotheses**: `t`, `t'` invariant over `xImage W`; agreement on the zero translate.
- **Uses from project**: `frobFixed`, `xImage`, `invariant_pieces_eq`,
  `translate_le_curvePreimage_xImage`, `curvePreimage`, `curvePreimage_xImage`, `isLimitSheafOn_Y`,
  `yFunctor`, `yFunctor_trace`, `limitRestrict`, `SpaTop`, `Ainf`, `yFrobTop`
- **Used by**: `ringStalkMap_piYHom_injective`
- **Visibility**: public
- **Lines**: 1402–1432 (proof 1409–1432, 24 lines)
- **Notes**: `ULift ℤ` universe lift

### `theorem curveRingPresheaf_map_apply`
- **Type**: `{V' V : Opens (Curve p F ϖ)} (h : V' ≤ V) (t : ToType ((curveSpace p F ϖ).ringPresheaf.obj (op V))) → (ConcreteCategory.hom ((curveSpace p F ϖ).ringPresheaf.map (homOfLE h).op)) t = frobFixedRestrict p F ϖ h t`
- **What**: The curve ring presheaf's restriction map, applied to an element, is the concrete
  `frobFixedRestrict`.
- **How**: `rfl` — the presheaf's `map` field was defined as exactly that bundled morphism.
- **Hypotheses**: `V' ≤ V`.
- **Uses from project**: `curveSpace`, `frobFixedRestrict`, `TopRingPresheafedSpace.ringPresheaf`
- **Used by**: unused in file (the bundled variant `xPresheaf_map_apply` is used instead)
- **Visibility**: public
- **Lines**: 1436–1441 (term proof, 1 line)
- **Notes**: none

### `theorem ringStalkMap_piYHom_injective`
- **Type**: `(y : ↥(yTop p F ϖ)) → Function.Injective (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom`
- **What**: **Injectivity of the projection stalk map** (D-iv-3(γ iii)): an invariant germ is
  determined by its underlying `𝒴`-germ.
- **How**: Represents both stalk elements as germs `germ V₁ … t₁`, `germ V₂ … t₂`
  (`exists_germ_eq`); `ringStalkMap_piYHom_germ` turns the hypothesis into an equality of
  `𝒴`-germs, and `TopCat.Presheaf.germ_eq` produces a common open `U` on which the two underlying
  sections restrict equally. Shrinking to `U ⊓ W₀` with `W₀` a wandering neighbourhood
  (`exists_disjoint_translates`), `xImage_le` gives `xImage (U ⊓ W₀) ≤ V₁, V₂`. The two invariant
  restrictions `frobFixedRestrict hle₁ t₁` and `frobFixedRestrict hle₂ t₂` are then shown equal by
  `invariant_sections_eq_of_zero_piece`, whose zero-piece hypothesis is obtained by translating
  `hres` through `yRingPresheaf_map_apply` and regrouping restrictions with three
  `limitRestrict_comp` applications (via `map_yFrobTop_zero` for the zero-translate inclusion and
  `yFunctor_curvePreimage_mono` for the expansion). Finally `TopCat.Presheaf.germ_res_apply` collapses
  both original germs to the common germ at `xImage (U ⊓ W₀)`.
- **Hypotheses**: standing package; wandering at `y`.
- **Uses from project**: `ringStalkMap`, `piYHom`, `curveSpace`, `yPresheafedSpace`,
  `ringStalkMap_piYHom_germ`, `piComponent`, `yTopToCurveTop`, `yTopToCurve`,
  `exists_disjoint_translates`, `xImage`, `xImage_le`, `curvePreimage`, `frobFixedRestrict`,
  `invariant_sections_eq_of_zero_piece`, `yRingPresheaf_map_apply`, `map_yFrobTop_zero`,
  `yFunctor`, `yFunctor_curvePreimage_mono`, `translate_le_curvePreimage_xImage`, `limitRestrict`,
  `limitRestrict_comp`, `yFrobTop`
- **Used by**: `ringStalkMap_piYHom_bijective`
- **Visibility**: public
- **Lines**: 1445–1525 (proof 1448–1525, **78 lines**)
- **Notes**: proof >30 lines

### `def fiberPoint`
- **Type**: `(x : Curve p F ϖ) → ↥(yTop p F ϖ)`
- **What**: A chosen point of the `𝒴`-fiber over a curve point (a section of the quotient map at the
  level of points, via choice).
- **How**: `((isOpenQuotientMap_yTopToCurve p F ϖ).surjective x).choose`.
- **Hypotheses**: standing package; surjectivity of the projection.
- **Uses from project**: `isOpenQuotientMap_yTopToCurve`, `Curve`, `yTop`
- **Used by**: `yTopToCurve_fiberPoint`, `xStalkEquiv`, `isLocalRing_xStalk`, `xVPreObj`
- **Visibility**: public
- **Lines**: 1530–1531 (2 lines)
- **Notes**: `noncomputable` (uses `Exists.choose`)

### `theorem yTopToCurve_fiberPoint`
- **Type**: `(x : Curve p F ϖ) → yTopToCurve p F ϖ (fiberPoint p F ϖ x) = x`
- **What**: The chosen fiber point does lie over `x`.
- **How**: `((isOpenQuotientMap_yTopToCurve p F ϖ).surjective x).choose_spec`.
- **Hypotheses**: standing package.
- **Uses from project**: `yTopToCurve`, `fiberPoint`, `isOpenQuotientMap_yTopToCurve`
- **Used by**: `xStalkEquiv`
- **Visibility**: public
- **Lines**: 1533–1535 (term proof, 1 line)
- **Notes**: none

### `theorem ringStalkMap_piYHom_bijective`
- **Type**: `(y : ↥(yTop p F ϖ)) → Function.Bijective (ValuationSpectrum.ringStalkMap (piYHom p F ϖ) y).hom`
- **What**: **Bijectivity of the projection stalk map** (D-iv-3(γ), assembled): the stalk of the
  curve presheaf maps isomorphically onto the `𝒴`-stalk.
- **How**: Pairs `ringStalkMap_piYHom_injective` with `ringStalkMap_piYHom_surjective`.
- **Hypotheses**: standing package.
- **Uses from project**: `ringStalkMap`, `piYHom`, `ringStalkMap_piYHom_injective`,
  `ringStalkMap_piYHom_surjective`
- **Used by**: `xStalkEquiv`
- **Visibility**: public
- **Lines**: 1539–1543 (term proof, 2 lines)
- **Notes**: none

### `def xStalkEquiv`
- **Type**: `(x : Curve p F ϖ) → ToType ((curveSpace p F ϖ).ringStalk x) ≃+* ToType ((yPresheafedSpace p F ϖ).ringStalk (fiberPoint p F ϖ x))`
- **What**: **The stalk comparison of the curve** (D-iv-3(γ), packaged): the stalk of `𝒪_𝒳` at `x` is
  identified with the `𝒴`-stalk at the chosen fiber point.
- **How**: Composite of two isomorphisms: `(curveSpace).ringPresheaf.stalkCongr` along
  `Inseparable.of_eq (yTopToCurve_fiberPoint … ).symm` (moving the base point from `x` to
  `π(fiberPoint x)`), converted to a `RingEquiv` by `commRingCatIsoToRingEquiv`, then
  `RingEquiv.ofBijective` of the projection stalk map using
  `ringStalkMap_piYHom_bijective`.
- **Hypotheses**: standing package.
- **Uses from project**: `curveSpace`, `yPresheafedSpace`, `fiberPoint`, `yTopToCurve_fiberPoint`,
  `ringStalkMap`, `piYHom`, `ringStalkMap_piYHom_bijective`, `TopRingPresheafedSpace.ringStalk`
- **Used by**: `isLocalRing_xStalk`, `xVPreObj`
- **Visibility**: public
- **Lines**: 1549–1559 (11 lines)
- **Notes**: `noncomputable`

### `theorem isLocalRing_xStalk`
- **Type**: `(x : Curve p F ϖ) → IsLocalRing (ToType ((curveSpace p F ϖ).ringStalk x))`
- **What**: **The stalks of the curve are local rings** — the first `𝒱^pre` axiom.
- **How**: Installs `isLocalRing_yStalk p F ϖ (fiberPoint p F ϖ x)` as an instance and transports it
  backwards along `(xStalkEquiv p F ϖ x).symm.isLocalRing`.
- **Hypotheses**: standing package; locality of the `𝒴`-stalks (proved upstream in `YStalks.lean`).
- **Uses from project**: `curveSpace`, `yPresheafedSpace`, `xStalkEquiv`, `fiberPoint`,
  `isLocalRing_yStalk`, `TopRingPresheafedSpace.ringStalk`
- **Used by**: `xVPreObj`
- **Visibility**: public
- **Lines**: 1563–1568 (proof 1564–1568, 5 lines)
- **Notes**: none

### `def yStalkValue`
- **Type**: `(y : ↥(yTop p F ϖ)) → Spv (ToType ((yPresheafedSpace p F ϖ).ringStalk y))`
- **What**: The valuation on the `𝒴`-stalk at `y` (the value of `yVPreObj.val`, extracted here as a
  standalone definition so the curve's valuation can be defined by pullback).
- **How**: `comap` of the stalk valuation `stalkValue (ySpaPoint p F ϖ y)` along the ring
  homomorphism underlying `yRingStalkEquiv p F ϖ y` (the identification of the `𝒴`-stalk with the
  ambient `Spa`-stalk).
- **Hypotheses**: standing package.
- **Uses from project**: `yPresheafedSpace`, `yRingStalkEquiv`, `ySpaPoint`, `stalkValue`, `comap`,
  `TopRingPresheafedSpace.ringStalk`
- **Used by**: `yStalkValue_supp`, `xVPreObj`
- **Visibility**: public
- **Lines**: 1571–1574 (4 lines)
- **Notes**: `noncomputable`

### `theorem yStalkValue_supp`
- **Type**: `(y : ↥(yTop p F ϖ)) → (yStalkValue p F ϖ y).supp = @IsLocalRing.maximalIdeal _ _ (isLocalRing_yStalk p F ϖ y)`
- **What**: The support of the `𝒴`-stalk valuation is the maximal ideal — the `val_supp` axiom of
  `𝒱^pre` at the `𝒴`-level, isolated for reuse.
- **How**: Installs locality of the ambient `Spa`-stalk (`isLocalRing_stalk_Y` at
  `ySpaPoint p F ϖ y`, using `ySpaPoint_mem_Y`); then `supp_comap` turns the support of the
  comap into the comap of the support, `maximalIdeal_stalk_Y` identifies the ambient stalk's
  support with its maximal ideal, and `IsLocalRing.maximalIdeal_comap` transfers the maximal ideal
  along the ring equivalence — whose local-hom property comes from `isLocalHom_equiv
  (yRingStalkEquiv p F ϖ y)`.
- **Hypotheses**: standing package; `ySpaPoint p F ϖ y ∈ Y` (from `ySpaPoint_mem_Y`).
- **Uses from project**: `yStalkValue`, `yRingStalkEquiv`, `ySpaPoint`, `ySpaPoint_mem_Y`,
  `stalkValue`, `isLocalRing_yStalk`, `isLocalRing_stalk_Y`, `maximalIdeal_stalk_Y`, `supp_comap`,
  `comap`, `spaRingPresheaf`, `Ainf`
- **Used by**: `xVPreObj`
- **Visibility**: public
- **Lines**: 1578–1594 (proof 1580–1594, 15 lines)
- **Notes**: uses `@`-explicit `IsLocalRing` instance arguments throughout to avoid instance clashes

### `def xVPreObj`
- **Type**: `VPreObj`
- **What**: **The adic Fargues–Fontaine curve as an object of `𝒱^pre`** (Wedhorn Definition 8.5):
  the `φ`-invariant structure presheaf on the quotient, with local stalks and a stalk valuation
  whose support is the maximal ideal.
- **How**: `toPresheafedSpace := curveSpace`; `isLocalRing_stalk := isLocalRing_xStalk`;
  `val x := comap (xStalkEquiv p F ϖ x) (yStalkValue p F ϖ (fiberPoint p F ϖ x))` — the `𝒴`-stalk
  valuation pulled back along the stalk comparison; `val_supp` by `supp_comap`, then
  `yStalkValue_supp` to identify the `𝒴`-side support with the maximal ideal, then
  `IsLocalRing.maximalIdeal_comap` along `xStalkEquiv`, whose local-hom property comes from
  `isLocalHom_equiv`.
- **Hypotheses**: standing package (the full perfectoid/pseudo-uniformizer package feeding
  `isLocalRing_yStalk`, `maximalIdeal_stalk_Y`, etc.).
- **Uses from project**: `VPreObj`, `curveSpace`, `isLocalRing_xStalk`, `xStalkEquiv`,
  `yStalkValue`, `yStalkValue_supp`, `fiberPoint`, `isLocalRing_yStalk`, `yPresheafedSpace`,
  `supp_comap`, `comap`, `TopRingPresheafedSpace.ringStalk`
- **Used by**: `xVObj`
- **Visibility**: public
- **Lines**: 1600–1615 (16 lines; `val_supp` proof 11 lines)
- **Notes**: `noncomputable`

### `theorem curvePreimage_inf`
- **Type**: `(V₁ V₂ : Opens (Curve p F ϖ)) → curvePreimage p F ϖ (V₁ ⊓ V₂) = curvePreimage p F ϖ V₁ ⊓ curvePreimage p F ϖ V₂`
- **What**: Saturated preimages commute with binary intersections.
- **How**: `Opens.ext`, `rw [Opens.coe_inf]`, then `rfl` — preimage of an intersection is the
  intersection of preimages, definitionally.
- **Hypotheses**: standing package.
- **Uses from project**: `curvePreimage`, `Curve`
- **Used by**: `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 1618–1623 (proof 1620–1623, 3 lines)
- **Notes**: none

### `theorem curvePreimage_iSup`
- **Type**: `{ι : Type*} (U : ι → Opens (Curve p F ϖ)) → curvePreimage p F ϖ (iSup U) = ⨆ i, curvePreimage p F ϖ (U i)`
- **What**: Saturated preimages commute with arbitrary unions — needed to turn a curve cover into a
  `𝒴`-cover.
- **How**: `Opens.ext`, `Opens.coe_iSup` on both sides, then `Set.preimage_iUnion` and `rfl`.
- **Hypotheses**: standing package.
- **Uses from project**: `curvePreimage`, `yTopToCurve`, `Curve`, `yTop`
- **Used by**: `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 1626–1634 (proof 1628–1634, 7 lines)
- **Notes**: none

### `theorem xPresheaf_map_apply`
- **Type**: `{V' V : Opens (Curve p F ϖ)} (h : V' ≤ V) (t : ((curveSpace p F ϖ).presheaf.obj (op V) : Type _)) → ((curveSpace p F ϖ).presheaf.map (homOfLE h).op).1 t = frobFixedRestrict p F ϖ h t`
- **What**: The bundled-morphism form of "the curve presheaf's action is the invariant restriction".
- **How**: `rfl`.
- **Hypotheses**: `V' ≤ V`.
- **Uses from project**: `curveSpace`, `frobFixedRestrict`, `xStructurePresheaf`
- **Used by**: `xPresheaf_isSheafOfTopologicalRings`
- **Visibility**: public
- **Lines**: 1638–1641 (term proof, 1 line)
- **Notes**: none

### `theorem xPresheaf_isSheafOfTopologicalRings`
- **Type**: `TopCat.Presheaf.IsSheafOfTopologicalRings (curveSpace p F ϖ).presheaf`
- **What**: **The curve presheaf is a sheaf of topological rings** (D-iv-4, Wedhorn Remark 8.20 in the
  `Hom_cont(T, −)` form): for every topological test ring `T`, compatible continuous families of
  `T`-points of the invariant section rings over a cover glue uniquely.
- **How**: Transfers the problem to `𝒴`. Sets `V' := yFunctor (π^{-1}(⨆U))`, `U' i := yFunctor
  (π^{-1}(U i))`; the cover condition uses `curvePreimage_iSup` and `yFunctor_cov`, the trace
  condition `yFunctor_trace`, and stability `frobOpens_yFunctor_curvePreimage`. Compatibility of the
  underlying `𝒴`-family is deduced from the curve-level compatibility via `xPresheaf_map_apply` plus
  `ValuationSpectrum.limitRestrict_cross_eq_of_opens_eq`, whose "same open" input is
  `curvePreimage_inf` + `yFunctor_inf`. Then `(isLimitSheafOn_Y p F ϖ).homGlue` produces a unique
  continuous glued ring hom `g : T →+* limitSections V'`. Invariance of `g t` is checked with
  `mem_frobFixed` and a second separation argument, `(isLimitSheafOn_Y).injective` over the same
  cover (pushed into `frobOpens 1 V'` by `stabV`): on each piece, `limitRestrict_comp`,
  `limitFrobHom_limitRestrict`, the piece-level equation `hg i`, the invariance of `(f i).1 t`, and
  `limitRestrict_id` show both sides equal `((f i).1 t).1`. The glued section is packaged with
  `RingHom.codRestrict` into `frobFixed (⨆U)`, continuity via `continuous_induced_rng`, and the
  uniqueness clause is transported back through `huniq` and `xPresheaf_map_apply`.
- **Hypotheses**: standing package; the `𝒴`-relative all-open sheaf condition `isLimitSheafOn_Y`;
  `T` a topological commutative ring in the working universe.
- **Uses from project**: `curveSpace`, `xStructurePresheaf`, `xPresheaf_map_apply`, `frobFixed`,
  `mem_frobFixed`, `curvePreimage`, `curvePreimage_inf`, `curvePreimage_iSup`,
  `yFunctor_curvePreimage_mono`, `frobOpens_yFunctor_curvePreimage`, `piComponent`, `yFunctor`,
  `yFunctor_trace`, `yFunctor_cov`, `yFunctor_inf`, `isLimitSheafOn_Y`
  (`.homGlue`, `.injective`), `limitRestrict`, `limitRestrict_comp`, `limitRestrict_id`,
  `limitRestrict_cross_eq_of_opens_eq`, `limitFrobHom`, `limitFrobHom_limitRestrict`, `frobOpens`,
  `frobOpens_mono`, `SpaTop`, `Ainf`, `ringPlus`, `Y`
- **Used by**: `xVObj`
- **Visibility**: public
- **Lines**: 1648–1770 (proof 1651–1770, **120 lines**)
- **Notes**: proof >30 lines; the second-longest proof in the file

### `def xVObj`
- **Type**: `ValuationSpectrum.VObj`
- **What**: **The headline result of the file — the adic Fargues–Fontaine curve as an object of
  Wedhorn's category `𝒱`** (D-iv-5): the `𝒱^pre`-object `xVPreObj` together with the
  sheaf-of-topological-rings condition.
- **How**: Structure-update syntax `{ xVPreObj p F ϖ with isSheafTopRings :=
  xPresheaf_isSheafOfTopologicalRings p F ϖ }`.
- **Hypotheses**: standing package (`p` prime, `F` a perfectoid field of characteristic `p`, `ϖ` a
  pseudo-uniformizer).
- **Uses from project**: `VObj`, `xVPreObj`, `xPresheaf_isSheafOfTopologicalRings`
- **Used by**: unused in file (this is the file's terminal export)
- **Visibility**: public
- **Lines**: 1775–1777 (3 lines)
- **Notes**: `noncomputable`

---

### File Summary

- **Total declarations: 100** — **19 defs** (6 `def` + 13 `noncomputable def`), **78
  lemmas/theorems** (all `theorem`; no `lemma`), **3 instances** (`frobFixed.completeSpace`,
  `frobFixed.isUniformAddGroup`, and 1 anonymous file-local `DecidableEq (Ainf p F)`).
  No `structure`, `class` or `abbrev` declarations.
  The 19 defs: `yTopToY`, `yTopToCurve`, `curvePreimage`, `frobFixed`, `CurveTop`,
  `frobFixedRestrict`, `xStructurePresheaf`, `curveSpace`, `yTopToCurveTop`, `piComponent`,
  `piYHom`, `yTopToYHomeo`, `xImage`, `translateFam`, `fiberPoint`, `xStalkEquiv`, `yStalkValue`,
  `xVPreObj`, `xVObj`.

- **Key API (used by 3+ other declarations in this file)**:
  `curvePreimage` (30), `frobFixed` (17), `xImage` (14), `yTopToCurve` (13),
  `curveSpace` (10), `frobOpens_yFunctor_curvePreimage` (8), `yTopToY` (8),
  `yFunctor_translate_le` (7), `piece_shift` (6), `translateFam` (6),
  `yTopToCurveTop` (5), `frobOpens_add` (5), `piYHom` (5), `frobFixedRestrict` (5),
  `piComponent` (5), `yFunctor_curvePreimage_mono` (5), `translate_le_curvePreimage_xImage` (4),
  `frobOpens_zero` (4), `yFunctor_translate_zero_le` (4), `curvePreimage_xImage` (4),
  `fiberPoint` (4), `limitFrobHom_zero`/`map_yFrobTop_zero`/`isOpenQuotientMap_yTopToCurve` (3 each).

- **Unused declarations (within this file)**: `curvePreimage_eq_opensMap`,
  `curveRingPresheaf_map_apply`, `xVObj` (the file's terminal export — used downstream, not here).
  The anonymous `DecidableEq (Ainf p F)` local instance is used only through typeclass inference.

- **Declarations with `sorry`**: none. The file is sorry-free.

- **Declarations with `set_option`**: none at declaration level. One file-level
  `set_option linter.overlappingInstances false` (line 23) governs the whole file. **No
  `maxHeartbeats` / `maxRecDepth` bumps anywhere.**

- **Proofs >30 lines**:
  - `limitFrobHom_add` — 122 lines (699–827)
  - `xPresheaf_isSheafOfTopologicalRings` — 120 lines (1648–1770)
  - `ringStalkMap_piYHom_injective` — 78 lines (1445–1525)
  - `exists_translateFam_glue` — 62 lines (545–616)
  - `ringStalkMap_piYHom_surjective` — 57 lines (1133–1192)
  - `ringStalkMap_piYHom_germ` — 51 lines (1050–1108)
  - `glue_piece_eq` — 50 lines (932–994)
  - `invariant_piece_transport` — 36 lines (1208–1254)
  - `limitFrobHom_zero` — 34 lines (412–449)

  Just under the bar (20–30 lines), for completeness: `exists_disjoint_translates` (27),
  `curvePreimage_xImage` (26), `invariant_sections_eq_of_zero_piece` (24), `glue_invariant` (22),
  `translateFam_succ` (21).
</content>
</invoke>
