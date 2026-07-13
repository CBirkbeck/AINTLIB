# [HG-C2] geometric heart — battle plan (v10.197-G0, STREAM-G0)

Target: `chartPrecursorSpec_isClosedImmersion` (StableChartData.lean:134) — the LAST sorry
under the whole quotient tower. Reduction already in-file: suffices IsClosedImmersion
(Spec.map β), β = productMap incL chartCoaction : C⊗C → C⊗G (key_incL/key_incR proven).

## Steps
1. **UUSpecIso** : pullback P.chartToBase P.chartToBase ≅ Spec (.of (C ⊗[R] C)) — mirror
   `kunnethToSpec` at the (U,U)-pair (asIso (pullback.map … toSpecΓ …) with the two
   appLE-naturality squares, both legs = chart side) ≪≫ pullbackSpecIso R C C.
   Leg lemmas: UUSpecIso.hom/inv vs fst/snd — mirror `pullbackSpecIso_inv_fst/snd` chains.
2. **chartActPair** : (actionProj.left ⁻¹ᵁ U).toScheme ⟶ pullback chartToBase chartToBase :=
   pullback.lift (G.restrictedProj P.U) (G.restrictedAction P.hstable) w
   [fst = PROJECTION (incL-dual), snd = ACTION (chartCoaction-dual) — matches key_incL/incR].
   w: both ≫ chartToBase agree — cancel_mono V.ι + resLE_comp_ι + Over-w (cf. isInvariant_structure).
3. **hconj** : chartTensorIso.hom ≫ Spec.map (ofHom β) ≫ UUSpecIso.inv = chartActPair —
   pullback.hom_ext; fst-leg: Spec.map_comp + key_incL + **chartTensorIso_hom_specMap_includeLeft**
   (S4-K1 bridge = restrictedProj ≫ isoSpec.hom) + isoSpec_hom/toSpecΓ alignment through
   UUSpecIso's fst-triangles; snd-leg: key_incR + **chartTensorIso_hom_specMap_chartCoaction**.
   Then IsClosedImmersion (Spec.map β) ⟺ IsClosedImmersion chartActPair (iso conjugation).
4. **IsClosedImmersion chartActPair** — the geometric content:
   (4a) productOpen := (fst E.asOver E.asOver).left ⁻¹ᵁ U ⊓ (snd …).left ⁻¹ᵁ U.
   (4b) hpre : actPair.left ⁻¹ᵁ productOpen = actionProj.left ⁻¹ᵁ U — comp_preimage +
        actPair_fst/actPair_snd (Over-left rfl) + inf-absorb by STABILITY (P.hstable).
   (4c) IsClosedImmersion (actPair.left ∣_ productOpen) — IsLocalAtTarget for
        IsClosedImmersion (check instance name; `IsLocalAtTarget.restrict`).
   (4d) transport ∣_-form to chartActPair: morphismRestrict ↔ resLE dictionary + an iso
        productOpen.toScheme ≅ pullback chartToBase chartToBase (iterated
        pullbackRestrictIsoRestrict / hand-rolled isoOfRangeEq through E×E) + hpre ▸ source.
        Verify by hom_ext on the two chartToBase-legs (each an established resLE triangle).

Then `chartCoaction_productMap_surjective` closes (already wired to consume it), M6 becomes
axiom-clean, and the ENTIRE glued quotient (v10.196/197 six pin-facts) goes sorry-free.
