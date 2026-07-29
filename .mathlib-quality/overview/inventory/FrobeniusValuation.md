# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/FrobeniusValuation.lean`

626 lines. Imports `«Adic spaces».FarguesFontaine.FrobeniusLimit`.
File-level `set_option linter.overlappingInstances false` (line 18); whole file is inside
`noncomputable section` (line 20). Two namespaces: `ValuationSpectrum` (lines 22–119) and
`FarguesFontaine` (lines 121–end).

Local instance (line 128, not a named declaration):
`noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _`.

Shared section variables in `FarguesFontaine`: `(p : ℕ) [Fact p.Prime]`,
`(F : Type*)` a perfectoid field of characteristic `p` (topological/uniform/nonarchimedean),
`(ϖ : PseudoUniformizer F)`.

---

### `theorem ValuationSpectrum.comap_presheafValueRingEquivHuber_pointValue`
- **Type**: `(e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) (hplus : (B⁺ : Subring B) = (A⁺ : Subring A).map e.toRingHom) (D : RationalLocData A) {v' : Spv B} (hv' : v' ∈ rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s ∩ Spa B B⁺) : comap (presheafValueRingEquivHuber e he he' D).toRingHom (pointValue (D.mapHuber e he he') hv') = pointValue D ⟨…, …⟩`
- **What**: Transporting a rational-localisation datum `D` along a topological ring isomorphism `e : A ≃+* B` induces an isomorphism of the two rational-localisation value rings; this says that isomorphism intertwines the point valuations — pulling back the point valuation of the transported datum gives the point valuation of `D` at the pulled-back point.
- **How**: Uses the characterisation `eq_pointValue_of_comap_eq` (a continuous valuation on the localisation restricting to `v` along the canonical map *is* the point valuation), then a four-step `calc` on `comap` of the canonical map, using the naturality square `presheafValueRingEquivHuber_canonicalMap` and functoriality `ValuationSpectrum.comap_comp`, ending at `comap_pointValue`.
- **Hypotheses**: `e` a ring isomorphism continuous both ways; the plus-subrings correspond under `e` (`hplus`); `v'` lies in the rational open of the transported datum intersected with `Spa B B⁺`.
- **Uses from project**: `eq_pointValue_of_comap_eq`, `comap_isContinuous`, `presheafValueRingEquivHuber_continuous`, `pointValue_isContinuous`, `presheafValueRingEquivHuber`, `presheafValueRingEquivHuber_canonicalMap`, `RationalLocData.mapHuber`, `RationalLocData.canonicalMap`, `ValuationSpectrum.comap_comp`, `comap_pointValue`, `mem_rationalOpen_mapHuber_iff`, `comap_mem_spa_map`, `rationalOpen`, `pointValue`, `comap`
- **Used by**: unused in file (the file only ever uses the `symm` version)
- **Visibility**: public
- **Lines**: 33–65 (proof 43–65, ~23 lines)
- **Notes**: proof is a 4-step `calc`; no `sorry`, no `set_option`.

### `theorem ValuationSpectrum.presheafValueRingEquivHuber_symm_canonicalMap`
- **Type**: `(e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) (D : RationalLocData A) (b : B) : (presheafValueRingEquivHuber e he he' D).symm ((D.mapHuber e he he').canonicalMap b) = D.canonicalMap (e.symm b)`
- **What**: The `symm` direction of the naturality square for the Huber value-ring equivalence: the inverse equivalence commutes with the canonical maps from the base rings, twisted by `e.symm`.
- **How**: Move the `symm` across with `RingEquiv.symm_apply_eq` and close with the forward naturality lemma `presheafValueRingEquivHuber_canonicalMap` applied to `e.symm b`, plus `e.apply_symm_apply`.
- **Hypotheses**: `e` continuous both ways; `D` a rational-localisation datum on `A`.
- **Uses from project**: `presheafValueRingEquivHuber`, `presheafValueRingEquivHuber_canonicalMap`, `RationalLocData.mapHuber`, `RationalLocData.canonicalMap`
- **Used by**: `comap_presheafValueRingEquivHuber_symm_pointValue` (line 101)
- **Visibility**: public
- **Lines**: 69–77 (proof 75–77, 3 lines)
- **Notes**: []

### `theorem ValuationSpectrum.comap_presheafValueRingEquivHuber_symm_pointValue`
- **Type**: `(e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) (D : RationalLocData A) {v : Spv A} (hv : v ∈ rationalOpen D.T D.s ∩ Spa A A⁺) {v' : Spv B} (hv' : v' ∈ rationalOpen (D.mapHuber e he he').T (D.mapHuber e he he').s ∩ Spa B B⁺) (hcom : comap e.toRingHom v' = v) : comap (presheafValueRingEquivHuber e he he' D).symm.toRingHom (pointValue D hv) = pointValue (D.mapHuber e he he') hv'`
- **What**: The `symm`-direction point-valuation equivariance: pulling `D`'s point valuation back along the inverse of the value-ring equivalence yields the transported datum's point valuation at the corresponding point `v'`.
- **How**: Again `eq_pointValue_of_comap_eq` (with continuity from `presheafValueRingEquivHuber_symm_continuous`), then a five-step `calc` using the naturality square `presheafValueRingEquivHuber_symm_canonicalMap`, `ValuationSpectrum.comap_comp`, `comap_pointValue`, and finally `comap_comap_of_ringEquiv` to undo the `e`/`e.symm` roundtrip.
- **Hypotheses**: `e` continuous both ways; `v` in the rational open of `D`, `v'` in that of the transported datum, and the two are related by `comap e = ·` (`hcom`). Notably this version needs **no** `hplus` hypothesis, unlike the forward direction.
- **Uses from project**: `eq_pointValue_of_comap_eq`, `comap_isContinuous`, `presheafValueRingEquivHuber_symm_continuous`, `pointValue_isContinuous`, `presheafValueRingEquivHuber`, `presheafValueRingEquivHuber_symm_canonicalMap`, `RationalLocData.mapHuber`, `RationalLocData.canonicalMap`, `ValuationSpectrum.comap_comp`, `comap_pointValue`, `comap_comap_of_ringEquiv`, `rationalOpen`, `pointValue`, `comap`
- **Used by**: `stepMid` (line 194)
- **Visibility**: public
- **Lines**: 82–117 (proof 93–117, ~25 lines)
- **Notes**: 5-step `calc`; near-verbatim mirror of `comap_presheafValueRingEquivHuber_pointValue` (see repeated-preamble note in the summary).

### `theorem FarguesFontaine.spaFrob_mem_frobIndex_datum`
- **Type**: `(k : ℤ) {W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} (E : RationalIndex (frobOpens p F k W)) {v : ↥(Spa (Ainf p F) …)} (hvE : (v : Spv (Ainf p F)) ∈ rationalOpen E.D.T E.D.s ∩ Spa (Ainf p F) ((Ainf p F)⁺)) : (spaFrob p F k v).1 ∈ rationalOpen (frobIndex p F k E).D.T (frobIndex p F k E).D.s ∩ Spa (Ainf p F) ((Ainf p F)⁺)`
- **What**: If `v` lies in the rational open cut out by the rational index `E` on `frobOpens p F k W`, then the Frobenius image `spaFrob p F k v` lies in the rational open cut out by the transported index `frobIndex p F k E`.
- **How**: Uses the roundtrip identity `spaFrob_spaFrob` (in the form `comap (frobPow p F (-k)) (spaFrob p F k v) = v`) to transfer each of the three defining conditions (spa-membership, the `≤`-conditions `v t ≤ v s`, and non-vanishing of `s`) across `comap_vle`; the generator set of the transported datum is `E.D.T.image (frobPow p F (-k))`, unpacked with `Finset.mem_image`.
- **Hypotheses**: `hvE`: `v` in `E`'s rational open intersected with `Spa`; `v` is already a point of `Spa (Ainf p F) (ringPlus …)`.
- **Uses from project**: `spaFrob`, `spaFrob_spaFrob`, `frobPow`, `frobOpens`, `frobIndex`, `RationalIndex`, `rationalOpen`, `comap`, `comap_vle`, `Spa`, `Ainf`, `ringPlus`
- **Used by**: `stepMid` (lines 190, 197, 228), `comap_limitFrobHom_openValue` (line 245)
- **Visibility**: public
- **Lines**: 132–155 (proof 141–155, ~15 lines)
- **Notes**: docstring says it is the "inlined backward direction of the transport iff, **split for kernel budget**" — i.e. deliberately factored out for elaboration cost.

### `private theorem FarguesFontaine.limitEvalHom_limitFrobHom`
- **Type**: `(k : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (E : RationalIndex (frobOpens p F k W)) : (limitEvalHom E).comp (limitFrobHom p F k W) = ((presheafValueRingEquivHuber (frobPow p F (-k)) … E.D).symm.toRingHom).comp (limitEvalHom (frobIndex p F k E))`
- **What**: The commuting square relating the Frobenius transport of limit sections to evaluation at a rational index: evaluating a transported section at `E` equals applying the inverse Huber value equivalence to the evaluation of the original section at the transported index `frobIndex p F k E`.
- **How**: Pointwise `RingHom.ext`, then chain `limitEvalHom_apply` (evaluation unfolds to the component), the component formula `limitFrobHom_component`, and `limitEvalHom_apply` again on the transported index.
- **Hypotheses**: none beyond the section variables and `E` being a rational index of `frobOpens p F k W`.
- **Uses from project**: `limitEvalHom`, `limitEvalHom_apply`, `limitFrobHom`, `limitFrobHom_component`, `presheafValueRingEquivHuber`, `frobPow`, `continuous_frobPow`, `continuous_frobPow_symm`, `frobIndex`, `frobOpens`, `RationalIndex`
- **Used by**: `stepMid` (line 211)
- **Visibility**: private
- **Lines**: 157–174 (proof 164–174, ~11 lines)
- **Notes**: term-mode after `refine`/`show`; the `show` is needed to expose the `RingHom` application form.

### `private theorem FarguesFontaine.comap_comp_apply`
- **Type**: `{R S T' : Type*} [CommRing R] [CommRing S] [CommRing T'] (f : R →+* S) (g : S →+* T') (w : Spv T') : comap (g.comp f) w = comap f (comap g w)`
- **What**: Functoriality of `comap` on the valuation spectrum, stated as a definitional identity for composition of ring homomorphisms.
- **How**: `rfl` — `comap` of a composite is definitionally the composite of `comap`s.
- **Hypotheses**: `R, S, T'` commutative rings.
- **Uses from project**: `comap`, `Spv`
- **Used by**: `stepMid` (lines 202, 220)
- **Visibility**: private
- **Lines**: 176–178 (proof: `rfl`, 1 line)
- **Notes**: duplicated later as `comap_comp_apply'` (line 544) with a different universe/argument arrangement — see summary.

### `private theorem FarguesFontaine.stepMid`
- **Type**: `(k : ℤ) (W : Opens ↥(Spa (Ainf p F) …)) {v : ↥(Spa (Ainf p F) …)} (E : RationalIndex (frobOpens p F k W)) (hvE : (v : Spv (Ainf p F)) ∈ rationalOpen E.D.T E.D.s ∩ Spa (Ainf p F) ((Ainf p F)⁺)) : comap (limitFrobHom p F k W) (comap (limitEvalHom E) (pointValue E.D hvE)) = comap (limitEvalHom (frobIndex p F k E)) (pointValue (frobIndex p F k E).D (spaFrob_mem_frobIndex_datum …))`
- **What**: The middle step of the open-valuation equivariance proof: pulling a point valuation back through evaluation-then-Frobenius-transport equals pulling it back through evaluation at the transported index.
- **How**: Four explicit `have`s glued by `trans`: `comap_comp_apply` to fuse the two comaps, `limitEvalHom_limitFrobHom` to rewrite the composite hom, `comap_comp_apply` again to split, and finally `comap_presheafValueRingEquivHuber_symm_pointValue` (fed the roundtrip `spaFrob_spaFrob`) to identify the inner point valuations.
- **Hypotheses**: `hvE` as above; the roundtrip hypothesis needed by the point-valuation lemma is produced internally from `spaFrob_spaFrob`.
- **Uses from project**: `comap_comp_apply`, `limitEvalHom_limitFrobHom`, `ValuationSpectrum.comap_presheafValueRingEquivHuber_symm_pointValue`, `spaFrob_mem_frobIndex_datum`, `spaFrob_spaFrob`, `limitFrobHom`, `limitEvalHom`, `pointValue`, `presheafValueRingEquivHuber`, `frobPow`, `continuous_frobPow`, `continuous_frobPow_symm`, `frobIndex`, `frobOpens`, `comap`
- **Used by**: `comap_limitFrobHom_openValue` (line 243)
- **Visibility**: private
- **Lines**: 180–231 (proof 191–231, ~41 lines)
- **Notes**: >30-line proof; entirely `have`-chaining with fully spelled-out statements (no `simp`/`rw` automation) — this is the "typed haves" idiom used in place of heartbeat bumps.

### `theorem FarguesFontaine.comap_limitFrobHom_openValue`
- **Type**: `(k : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) {v : ↥(Spa (Ainf p F) …)} (hv : v ∈ frobOpens p F k W) : comap (limitFrobHom p F k W) (openValue (frobOpens p F k W) hv) = openValue W (show spaFrob p F k v ∈ W from hv)`
- **What**: **Equivariance of the open valuation under the Frobenius transport** — the headline section-level result of the file: the Frobenius transport of limit sections pulls the open valuation at `v` back to the open valuation at `spaFrob p F k v`.
- **How**: Choose a rational index `E` containing `v` via `exists_rationalIndex_mem`, rewrite both open valuations as point valuations via `comap_limitEvalHom_pointValue`, and apply `stepMid` in the middle.
- **Hypotheses**: `hv : v ∈ frobOpens p F k W` (equivalently `spaFrob p F k v ∈ W`, definitionally).
- **Uses from project**: `exists_rationalIndex_mem`, `comap_limitEvalHom_pointValue`, `stepMid`, `spaFrob_mem_frobIndex_datum`, `frobIndex`, `limitFrobHom`, `openValue`, `frobOpens`, `spaFrob`, `comap`
- **Used by**: `openValue_vle_frobTransport` (line 309)
- **Visibility**: public
- **Lines**: 235–245 (proof 241–245, 5 lines)
- **Notes**: named in the module docstring as one of the file's two goals.

### `theorem FarguesFontaine.frobOpens_frobOpens`
- **Type**: `(k : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : frobOpens p F k (frobOpens p F (-k) W) = W`
- **What**: The Frobenius preimage operation on opens roundtrips: taking the `(-k)`-preimage then the `k`-preimage of an open recovers the open.
- **How**: Extensionality of `Opens` and of the underlying set, reducing to the pointwise roundtrip `spaFrob_spaFrob p F k v : spaFrob p F (-k) (spaFrob p F k v) = v`.
- **Hypotheses**: none beyond section variables.
- **Uses from project**: `frobOpens`, `spaFrob`, `spaFrob_spaFrob`, `Spa`, `Ainf`, `ringPlus`
- **Used by**: `frobOpens_frobOpens'` (line 297), `comap_ringStalkMap_ambientFrob_stalkValue` (line 345)
- **Visibility**: public
- **Lines**: 248–254 (proof 250–254, 4 lines)
- **Notes**: []

### `theorem FarguesFontaine.ringStalkMap_ambientFrob_germ`
- **Type**: `(k : ℤ) (x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (U : Opens …) (hx : spaFrob p F k x ∈ U) (f : ↥(limitSections U)) : (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom ((yAmbientPresheafedSpace p F).ringPresheaf.germ U (spaFrob p F k x) hx f) = (yAmbientPresheafedSpace p F).ringPresheaf.germ (frobOpens p F k U) x hx (limitFrobHom p F k U f)`
- **What**: **Germ naturality of the ambient Frobenius stalk transport**: the induced map on stalks sends the germ of a section `f` at the image point to the germ of the Frobenius-transported section at `x`.
- **How**: Unfolds `ringStalkMap` into its two categorical factors and applies mathlib's `TopCat.Presheaf.stalkFunctor_map_germ_apply` (the whiskered-`c`-component step) followed by `TopCat.Presheaf.stalkPushforward_germ_apply` (the pushforward step), with a `show` to put the goal in the exactly-matching composite form.
- **Hypotheses**: `hx : spaFrob p F k x ∈ U`, which is definitionally `x ∈ frobOpens p F k U`.
- **Uses from project**: `ValuationSpectrum.ringStalkMap`, `ambientFrobHom`, `yAmbientPresheafedSpace`, `limitSections`, `limitFrobHom`, `frobOpens`, `spaFrob`, `CompleteTopCommRingCat.forgetToCommRingCat`
- **Used by**: `comap_ringStalkMap_ambientFrob_stalkValue` (lines 336, 341, 394, 399), `yFrob_val_compat` (line 533)
- **Visibility**: public
- **Lines**: 257–291 (proof 266–291, ~26 lines)
- **Notes**: the `show` block (lines 276–289) is a giant fully-elaborated term used to make `rw [h1]` fire — a defeq-shaping device rather than mathematics.

### `theorem FarguesFontaine.frobOpens_frobOpens'`
- **Type**: `(k : ℤ) (W : Opens ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : frobOpens p F (-k) (frobOpens p F k W) = W`
- **What**: The other-order roundtrip of Frobenius preimages of opens.
- **How**: Instantiate `frobOpens_frobOpens` at `-k` and cancel the double negation with `neg_neg`.
- **Hypotheses**: none beyond section variables.
- **Uses from project**: `frobOpens_frobOpens`, `frobOpens`
- **Used by**: `comap_ringStalkMap_ambientFrob_stalkValue` (line 350)
- **Visibility**: public
- **Lines**: 294–298 (proof 296–298, 2 lines)
- **Notes**: []

### `theorem FarguesFontaine.openValue_vle_frobTransport`
- **Type**: `(k : ℤ) (U' : Opens …) {x : ↥(Spa (Ainf p F) …)} (hx : x ∈ frobOpens p F k U') (s t : ↥(limitSections U')) : ((openValue (frobOpens p F k U') hx).vle (limitFrobHom p F k U' s) (limitFrobHom p F k U' t)) = ((openValue U' (show spaFrob p F k x ∈ U' from hx)).vle s t)`
- **What**: The comparison relation `vle` of the open valuation is preserved by the Frobenius transport — stated as a propositional *equality* of the two `vle` propositions so it can be moved with `Eq.mp`/`Eq.mpr`.
- **How**: Rewrite the left open valuation as a `comap` via `comap_limitFrobHom_openValue`, then apply `comap_vle` (the `vle` of a pulled-back valuation is the `vle` of the images).
- **Hypotheses**: `hx : x ∈ frobOpens p F k U'`; `s, t` limit sections on `U'`.
- **Uses from project**: `comap_limitFrobHom_openValue`, `comap_vle`, `openValue`, `limitFrobHom`, `limitSections`, `frobOpens`, `spaFrob`
- **Used by**: `comap_ringStalkMap_ambientFrob_stalkValue` (lines 375, 387 — used in both directions)
- **Visibility**: public
- **Lines**: 302–310 (proof 309–310, 2 lines)
- **Notes**: deliberately an `=` of `Prop`s rather than an `↔`, so both `Eq.mp` and `Eq.mpr` are available.

### `theorem FarguesFontaine.stalkVle_congr`
- **Type**: `{v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))} {a a' b b' : ToType ((spaRingPresheaf (Ainf p F)).stalk v)} (ha : a = a') (hb : b = b') (h : stalkVle v a b) : stalkVle v a' b'`
- **What**: Congruence/transport lemma: the stalk comparison relation `stalkVle` may be rewritten along equalities of either argument.
- **How**: `subst` both equalities and return the hypothesis.
- **Hypotheses**: `a = a'`, `b = b'`.
- **Uses from project**: `stalkVle`, `spaRingPresheaf`, `Ainf`, `ringPlus`, `Spa`
- **Used by**: `comap_ringStalkMap_ambientFrob_stalkValue` (lines 342, 379, 414)
- **Visibility**: public
- **Lines**: 313–318 (proof 316–318, 3 lines)
- **Notes**: exists because `stalkVle` arguments sit under a motive that `rw` cannot abstract cleanly.

### `theorem FarguesFontaine.comap_ringStalkMap_ambientFrob_stalkValue`
- **Type**: `(k : ℤ) (x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : comap (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom (stalkValue x) = stalkValue (spaFrob p F k x)`
- **What**: **The ambient stalk-value equivariance** (D-iii-4b): the stalk valuation at `x`, pulled back along the Frobenius map on stalks, is exactly the stalk valuation at the Frobenius image `spaFrob p F k x`. This is the ambient core of `val_compat`.
- **How**: `ValuationSpectrum.ext` reduces to a pointwise `↔` of `vle`-relations, proved in both directions. Both directions pick a common representing open `U` and sections `f, g` via `exists_common_rep`, convert germs across the Frobenius using `ringStalkMap_ambientFrob_germ`, shrink to a witnessing open with `stalkVle_elim`, transport the `vle` with `openValue_vle_frobTransport` (`Eq.mp` forward, `Eq.mpr` backward), and rebuild with `stalkVle_intro` + `stalkVle_congr`. The forward direction additionally needs the open roundtrips `frobOpens_frobOpens`/`frobOpens_frobOpens'`, monotonicity `frobOpens_mono`, restriction functoriality `limitRestrict_comp`, and the commutation `limitFrobHom_limitRestrict`.
- **Hypotheses**: none beyond section variables (`x` an arbitrary point of the adic spectrum).
- **Uses from project**: `ValuationSpectrum.ringStalkMap`, `ambientFrobHom`, `stalkValue`, `spaFrob`, `exists_common_rep`, `ringStalkMap_ambientFrob_germ`, `stalkVle_congr`, `stalkVle_elim`, `stalkVle_intro`, `frobOpens`, `frobOpens_frobOpens`, `frobOpens_frobOpens'`, `frobOpens_mono`, `openValue_vle_restrict`, `openValue_vle_frobTransport`, `openValue`, `limitRestrict`, `limitRestrict_comp`, `limitFrobHom`, `limitFrobHom_limitRestrict`, `germ_limitRestrict`, `yAmbientPresheafedSpace`, `spaRingPresheaf`, `comap`
- **Used by**: `yFrob_val_compat` (line 568)
- **Visibility**: public
- **Lines**: 323–414 (proof 328–414, ~87 lines)
- **Notes**: longest proof in the file (>30 lines). The two branches share a near-verbatim `hMa`/`hMb` germ-conversion block (lines 332–341 vs 390–399) — an extraction candidate.

### `theorem FarguesFontaine.ringStalkMap_yFrob_germ`
- **Type**: `(k : ℤ) (x : yTop p F ϖ) (V : Opens ↥(yTop p F ϖ)) (hx : yFrobTop p F ϖ k x ∈ V) (s : ToType ((yPresheafedSpace p F ϖ).ringPresheaf.obj (op V))) : (ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) x).hom ((yPresheafedSpace p F ϖ).ringPresheaf.germ V (yFrobTop p F ϖ k x) hx s) = (yPresheafedSpace p F ϖ).ringPresheaf.germ ((Opens.map (yFrobTop p F ϖ k)).obj V) x hx (yLimitFrobHom p F ϖ k V s)`
- **What**: **Germ naturality of the `𝒴`-Frobenius stalk transport** — the restricted-space analogue of `ringStalkMap_ambientFrob_germ`, on the curve-side presheafed space `yPresheafedSpace p F ϖ`.
- **How**: An explicit `rfl` unfolding (`hunfold`) of `ringStalkMap (yFrobHom …)` into `stalkFunctor.map (whiskerRight c) ≫ stalkPushforward`, a `hsplit : ∀ y, … = …` (also `rfl`) turning composite application into nested application, then mathlib's `TopCat.Presheaf.stalkFunctor_map_germ_apply` and `TopCat.Presheaf.stalkPushforward_germ_apply`, chained with `congrArg`/`trans` in term mode.
- **Hypotheses**: `hx : yFrobTop p F ϖ k x ∈ V`; `s` a section of the `𝒴`-ring presheaf on `V`.
- **Uses from project**: `ValuationSpectrum.ringStalkMap`, `yFrobHom`, `yFrobTop`, `yPresheafedSpace`, `yLimitFrobHom`, `yTop`, `CompleteTopCommRingCat.forgetToCommRingCat`
- **Used by**: `ringStalkMap_yFrob_conj` (line 519)
- **Visibility**: public
- **Lines**: 418–477 (proof 427–477, ~51 lines)
- **Notes**: >30 lines; almost all of it is defeq plumbing (`hunfold`, `hsplit` are both `rfl`) written out to control elaboration, not mathematics.

### `theorem FarguesFontaine.limitFrobHom_bridge`
- **Type**: `(k : ℤ) (V : Opens ↥(yTop p F ϖ)) (s : ↥(limitSections ((yFunctor p F ϖ).obj V))) : limitRestrict (le_of_eq (yFunctor_frobOpens p F ϖ k V).symm) (limitFrobHom p F k ((yFunctor p F ϖ).obj V) s) = yLimitFrobHom p F ϖ k V s`
- **What**: The ambient Frobenius transport of a section, restricted along the `yFunctor`/`frobOpens` commutation, agrees with the `𝒴`-level Frobenius transport `yLimitFrobHom`.
- **How**: Both sides are componentwise definitionally equal; proved by `Subtype.ext (funext fun _ => rfl)`.
- **Hypotheses**: uses `yFunctor_frobOpens` to identify the two opens.
- **Uses from project**: `limitRestrict`, `limitFrobHom`, `yLimitFrobHom`, `yFunctor`, `yFunctor_frobOpens`, `limitSections`, `yTop`
- **Used by**: `yFrob_val_compat` (line 541)
- **Visibility**: public
- **Lines**: 481–486 (proof 486, 1 line)
- **Notes**: []

### `theorem FarguesFontaine.yRingStalkIso_hom_germ`
- **Type**: `(x : yTop p F ϖ) (V : Opens ↥(yTop p F ϖ)) (hx : x ∈ V) (s : ToType ((yPresheafedSpace p F ϖ).ringPresheaf.obj (op V))) : (ConcreteCategory.hom (yRingStalkIso p F ϖ x).hom) ((yPresheafedSpace p F ϖ).ringPresheaf.germ V x hx s) = (spaRingPresheaf (Ainf p F)).germ ((yFunctor p F ϖ).obj V) (ySpaPoint p F ϖ x) ⟨x, hx, rfl⟩ s`
- **What**: The restriction-along-an-open-embedding stalk isomorphism sends the germ of `s` on `V` in `𝒴` to the germ of `s` on the ambient image open `(yFunctor p F ϖ).obj V` at the ambient image point.
- **How**: Direct application of mathlib's `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply` at the ambient ring space `yAmbientRingSpace p F` and the open embedding `yIncl_isOpenEmbedding`.
- **Hypotheses**: `hx : x ∈ V`; `yIncl` is an open embedding.
- **Uses from project**: `yRingStalkIso`, `yPresheafedSpace`, `yFunctor`, `ySpaPoint`, `yAmbientRingSpace`, `yIncl_isOpenEmbedding`, `spaRingPresheaf`, `yTop`, `Ainf`
- **Used by**: `ringStalkMap_yFrob_conj` (lines 520, 522)
- **Visibility**: public
- **Lines**: 489–497 (proof 496–497, 2 lines, term mode)
- **Notes**: `𝒴`-spelling wrapper around a mathlib lemma.

### `theorem FarguesFontaine.ringStalkMap_yFrob_conj`
- **Type**: `(k : ℤ) (x : yTop p F ϖ) : ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) x ≫ (yRingStalkIso p F ϖ x).hom = (yRingStalkIso p F ϖ (yFrobTop p F ϖ k x)).hom ≫ ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) (ySpaPoint p F ϖ x)`
- **What**: **The conjugation square** (D-iii-4c): the `𝒴`-Frobenius stalk map, conjugated by the restriction stalk isomorphisms, is the ambient Frobenius stalk map. This is what lets the curve-level statement be reduced to the ambient one.
- **How**: `TopCat.Presheaf.stalk_hom_ext` reduces to germs on an open `V`, then `CommRingCat.hom_ext`/`RingHom.ext` to elements; the germ is pushed across both routes by `ringStalkMap_yFrob_germ`, `yRingStalkIso_hom_germ` (twice) and `ringStalkMap_ambientFrob_germ` (supplied as a `rw [show … from …]`), and the two results are matched using `germ_limitRestrict` plus `limitFrobHom_bridge` to identify `yLimitFrobHom` with the restricted ambient `limitFrobHom`.
- **Hypotheses**: none beyond section variables.
- **Uses from project**: `ValuationSpectrum.ringStalkMap`, `yFrobHom`, `yFrobTop`, `yRingStalkIso`, `yRingStalkIso_hom_germ`, `ringStalkMap_yFrob_germ`, `ringStalkMap_ambientFrob_germ`, `ambientFrobHom`, `ySpaPoint`, `yPresheafedSpace`, `yFunctor`, `yFunctor_frobOpens`, `yLimitFrobHom`, `limitFrobHom`, `limitFrobHom_bridge`, `germ_limitRestrict`, `frobOpens`, `spaRingPresheaf`, `yTop`, `Ainf`
- **Used by**: `yFrob_val_compat` (line 561)
- **Visibility**: public
- **Lines**: 501–542 (proof 507–542, ~36 lines)
- **Notes**: >30 lines; includes a 12-line `show` to align spellings and a 12-line `rw [show … from ringStalkMap_ambientFrob_germ …]`.

### `private theorem FarguesFontaine.comap_comp_apply'`
- **Type**: `{R S T' : Type*} [CommRing R] [CommRing S] [CommRing T'] (f : R →+* S) (g : S →+* T') (w : Spv T') : comap (g.comp f) w = comap f (comap g w)`
- **What**: Functoriality of `comap` for composites of ring homomorphisms — a second copy of `comap_comp_apply`, restated locally later in the file.
- **How**: `rfl`.
- **Hypotheses**: `R, S, T'` commutative rings.
- **Uses from project**: `comap`, `Spv`
- **Used by**: `yFrob_val_compat` (lines 573, 580)
- **Visibility**: private
- **Lines**: 544–546 (proof: `rfl`, 1 line)
- **Notes**: **byte-identical statement and proof to `comap_comp_apply` (line 176)** apart from the name — a straightforward dedup target.

### `theorem FarguesFontaine.yFrob_val_compat`
- **Type**: `(k : ℤ) (x : yTop p F ϖ) : (yVPreObj p F ϖ).val (ConcreteCategory.hom (yFrobHom p F ϖ k).base x) = ((yVPreObj p F ϖ).val x).comap (ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) x).hom'`
- **What**: **Valuation compatibility of the `𝒴`-Frobenius** — the `val_compat` field of a `VPreHom`: the stalk valuation at the Frobenius image point is the pull-back of the stalk valuation at `x` along the Frobenius stalk map.
- **How**: A `show` transports both sides through the stalk equivalence `yRingStalkEquiv`; then the ambient equivariance `comap_ringStalkMap_ambientFrob_stalkValue` supplies the ambient identity, and the conjugation square `ringStalkMap_yFrob_conj` (turned into a `RingHom` equation by `congrArg CommRingCat.Hom.hom`) is inserted between two applications of `comap_comp_apply'`.
- **Hypotheses**: none beyond section variables.
- **Uses from project**: `yVPreObj`, `yFrobHom`, `yFrobTop`, `yRingStalkEquiv`, `ySpaPoint`, `stalkValue`, `ValuationSpectrum.ringStalkMap`, `ambientFrobHom`, `comap_ringStalkMap_ambientFrob_stalkValue`, `ringStalkMap_yFrob_conj`, `comap_comp_apply'`, `comap`, `yTop`
- **Used by**: `yFrob_isLocalHom` (line 601), `yFrobVPreHom` (line 622)
- **Visibility**: public
- **Lines**: 551–583 (proof 556–583, ~28 lines)
- **Notes**: pure `refine … ?_` chaining of `congrArg`/`trans` — no `simp`, no heartbeat bumps.

### `theorem FarguesFontaine.yFrob_isLocalHom`
- **Type**: `(k : ℤ) (x : yTop p F ϖ) : IsLocalHom (ValuationSpectrum.ringStalkMap (yFrobHom p F ϖ k) x).hom'`
- **What**: **The `𝒴`-Frobenius stalk map is a local homomorphism**: if the image of `a` is a unit in the target stalk, then `a` was already a unit.
- **How**: Contrapositive through the supports. The `VPreObj` package identifies the support of the stalk valuation with the maximal ideal (`(yVPreObj p F ϖ).val_supp` plus `isLocalRing_stalk` and `IsLocalRing.mem_maximalIdeal`/`mem_nonunits_iff`); `yFrob_val_compat` turns the support at the image point into the `Ideal.comap` of the support at `x` via `supp_comap`, so a non-unit would land in the support and contradict `ha`.
- **Hypotheses**: none beyond section variables; relies on the stalks being local rings and on support = maximal ideal.
- **Uses from project**: `ValuationSpectrum.ringStalkMap`, `yFrobHom`, `yVPreObj` (fields `val`, `val_supp`, `isLocalRing_stalk`), `yFrob_val_compat`, `supp_comap`, `yTop`
- **Used by**: `yFrobVPreHom` (line 621)
- **Visibility**: public
- **Lines**: 587–613 (proof 590–613, ~24 lines)
- **Notes**: uses `@IsLocalRing.mem_maximalIdeal` with an explicitly-supplied local-ring instance (twice) because the instance is not found by TC search.

### `noncomputable def FarguesFontaine.yFrobVPreHom`
- **Type**: `(k : ℤ) : ValuationSpectrum.VPreHom (yVPreObj p F ϖ) (yVPreObj p F ϖ)`
- **What**: **The Frobenius as a morphism of `𝒱^pre`** (goal D-iii): packages the `𝒴`-Frobenius presheafed-space endomorphism together with locality of its stalk maps and valuation compatibility into a morphism of valued presheafed spaces.
- **How**: Structure instance — `toHom := yFrobHom p F ϖ k`, `isLocalHom_stalkMap := yFrob_isLocalHom`, `val_compat := yFrob_val_compat`.
- **Hypotheses**: none beyond section variables.
- **Uses from project**: `ValuationSpectrum.VPreHom`, `yVPreObj`, `yFrobHom`, `yFrob_isLocalHom`, `yFrob_val_compat`
- **Used by**: unused in file (it is the file's terminal export)
- **Visibility**: public
- **Lines**: 618–622 (definition body 620–622, 3 lines)
- **Notes**: `noncomputable` (redundantly, since the whole file is a `noncomputable section`).

---

### File Summary

**Totals.** 22 declarations: **1 def** (`yFrobVPreHom`), **21 theorems** (no lemmas, no
instances, no structures/classes/abbrevs). 4 are `private`
(`limitEvalHom_limitFrobHom`, `comap_comp_apply`, `stepMid`, `comap_comp_apply'`); the other
18 are public. 3 live in namespace `ValuationSpectrum`, 19 in `FarguesFontaine`. There is one
anonymous `local instance` (`DecidableEq (Ainf p F) := Classical.decEq _`, line 128) which is
not a named declaration.

**The spine of the file** (each step feeds the next):
`comap_presheafValueRingEquivHuber_symm_pointValue` → `stepMid` →
`comap_limitFrobHom_openValue` → `openValue_vle_frobTransport` →
`comap_ringStalkMap_ambientFrob_stalkValue` → `yFrob_val_compat` → `yFrob_isLocalHom` →
`yFrobVPreHom`.

**Key API used by 3+ in-file consumers:**
- `spaFrob_mem_frobIndex_datum` — 4 uses (lines 190, 197, 228, 245).
- `ringStalkMap_ambientFrob_germ` — 5 uses (336, 341, 394, 399, 533).
- `stalkVle_congr` — 3 uses (342, 379, 414).
- (Borderline, 2 uses each but load-bearing: `openValue_vle_frobTransport`, `comap_comp_apply`,
  `comap_comp_apply'`, `yRingStalkIso_hom_germ`, `frobOpens_frobOpens`.)

**Unused in file (2):**
- `ValuationSpectrum.comap_presheafValueRingEquivHuber_pointValue` (lines 33–65) — a public
  `theorem`, **not** an `instance` and **not** `@[simp]`, and it has no in-file consumer: the
  whole file goes through the `symm` direction. It is either genuinely dead here or intended
  for downstream files; worth a repo-wide consumer check before removal.
- `FarguesFontaine.yFrobVPreHom` (lines 618–622) — a public `def`, not an instance/`@[simp]`,
  but it is the file's **terminal export** (goal D-iii), so "unused in file" is expected.

**Declarations with `sorry`:** none. The file contains no `sorry`, `admit`, or `TODO`.

**Declarations with `set_option`:** none per-declaration. There is exactly one **file-level**
`set_option linter.overlappingInstances false` (line 18). No `maxHeartbeats`/`maxRecDepth`
bumps anywhere — consistent with the project's no-heartbeat-bumps rule; the cost control is
instead done by splitting (`spaFrob_mem_frobIndex_datum` is documented as "split for kernel
budget") and by hand-written `show`/typed-`have` chains.

**Proofs longer than 30 lines (4):**
| decl | lines | proof length |
|---|---|---|
| `comap_ringStalkMap_ambientFrob_stalkValue` | 323–414 | ~87 |
| `ringStalkMap_yFrob_germ` | 418–477 | ~51 |
| `stepMid` | 180–231 | ~41 |
| `ringStalkMap_yFrob_conj` | 501–542 | ~36 |
Two more are in the 20–30 band: `yFrob_val_compat` (~28), `ringStalkMap_ambientFrob_germ`
(~26), `comap_presheafValueRingEquivHuber_symm_pointValue` (~25), `yFrob_isLocalHom` (~24),
`comap_presheafValueRingEquivHuber_pointValue` (~23).

**Repeated proof preambles / duplication (the ArCompletion.lean pattern).** This file is
*much* lighter than ArCompletion.lean — there is no 3+-occurrence verbatim multi-line block
(checked mechanically over 3–6 line windows). What there is:

1. **The germ-conversion block, 4 occurrences (~20 lines), all inside
   `comap_ringStalkMap_ambientFrob_stalkValue`** — verbatim up to the section name `f`/`g`,
   at lines 332–336, 337–341, 390–394, 395–399:
   ```
   have hM? : (ValuationSpectrum.ringStalkMap (ambientFrobHom p F k) x).hom ?
       = (yAmbientPresheafedSpace p F).ringPresheaf.germ
           (frobOpens p F k U) x hxU (limitFrobHom p F k U ?) := by
     rw [← h?]
     exact ringStalkMap_ambientFrob_germ p F k x U hxU ?
   ```
   One private helper `hM : ∀ (a : stalk) (f) (hf : germ … = a), … = …` would collapse all
   four. This is the single clearest extraction in the file.
2. **The `rw [ValuationSpectrum.comap_comp]; rfl` calc step, 4 occurrences** (lines 55–56,
   62–63, 107–108, 112–113) across the two `ValuationSpectrum` point-valuation theorems —
   these are exactly what the later `comap_comp_apply` (`rfl`) does, so the two `calc` proofs
   could be rewritten in the `comap_comp_apply` style used in `stepMid`.
3. **`comap_comp_apply` (176–178) and `comap_comp_apply'` (544–546) are byte-identical**
   (same statement, same `rfl` proof, different names, both `private`). Straight dedup: delete
   `comap_comp_apply'` and retarget lines 573/580.
4. **The two `ValuationSpectrum` point-valuation theorems (33–65 and 82–117) are structural
   mirrors** — same `eq_pointValue_of_comap_eq` opener, same 4/5-step `calc` skeleton, only
   the direction of `e` differs. Sharing is plausible but not mechanical.
5. **Two intra-proof `f`/`g` twin pairs** (2 occurrences each, so below the 3+ bar but still
   copy-paste): `hcolf`/`hcolg` (354–369, ~16 lines) and `hgf`/`hgg` (400–413, ~14 lines),
   both in `comap_ringStalkMap_ambientFrob_stalkValue`.
6. **The `hround` roundtrip preamble** `congrArg Subtype.val (spaFrob_spaFrob p F k v)`
   appears in both `spaFrob_mem_frobIndex_datum` (141–143) and `stepMid` (191–193) — 2
   occurrences, trivially a one-line named lemma.

Realistic extractable total: ~40–50 lines (items 1 + 3 + 5), versus the 200+ in
ArCompletion.lean. The heavy proofs here are long because of *defeq plumbing*
(`show` blocks re-spelling elaborated categorical terms, `rfl`-`have`s like `hunfold`/`hsplit`
in `ringStalkMap_yFrob_germ`), not because of duplicated preambles.
