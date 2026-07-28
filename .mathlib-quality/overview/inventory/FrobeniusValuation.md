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
