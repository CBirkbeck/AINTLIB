import ModularCurves.ForMathlib.StandardSmoothMaximalDVR
import ModularCurves.EllipticCurve.MulByHomFibresGlobal
import ModularCurves.EllipticCurve.AdditionChartDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# BB-FLAT fibre leg: `[N]` on the model over a field is flat ([BBF-A1])

The fibre case of KM 2.3.1's flatness of `[N]`: over a field `k`, the projective model
`projModel W` is an integral curve whose affine charts are standard-smooth of relative
dimension `1` (`RingHom.Locally`), and `[N] : projModel W ⟶ projModel W` is a finite
dominant self-morphism. On each standard-smooth affine piece the pushforward coordinate
ring is a finite torsion-free (domain + dominance-injective) module, hence flat by
`flat_of_isDomain_of_injective_of_isStandardSmooth` (the ValuationRing-localization
criterion). `Flat` is local at the target, so `[N]` is flat.

This supplies the "flat on fibres" hypothesis [BBF-A1] of the fibrewise-flatness criterion
[BBF-A3] (EGA IV 11.3.10) that discharges the general-base `Torsion.mulByHom_flat`; the
criterion assembly itself is the separately-boarded Buchsbaum–Eisenbud flat-locus chain.

## Banked ingredients
* `flat_of_isDomain_of_injective_of_isStandardSmooth` (ForMathlib): the ring-level heart.
* `AdditionChartDomain`: the chart rings of `projModel W` over a field are domains.
* `locally_isStandardSmooth_algebraMap_gradeZero_away` (WeierstrassModel): the charts are
  `RingHom.Locally` standard-smooth of relative dimension `1`.
* `injective_of_denseRange_comap` (below): dominance ⟹ injective on (reduced) sections.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- **Dominance ⟹ injectivity on reduced sections** (ring level). If the induced map of
prime spectra has dense range and the source ring is reduced, the ring map is injective:
dense range forces `ker f ≤ nilradical = ⊥`. -/
theorem injective_of_denseRange_comap {R S : Type*} [CommRing R] [CommRing S] [IsReduced R]
    {f : R →+* S} (h : DenseRange (PrimeSpectrum.comap f)) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot, ← le_bot_iff]
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical] at h
  rwa [nilradical_eq_bot_iff.mpr ‹IsReduced R›] at h

open EllipticCurve WeierstrassCurve

variable {k : Type u} [Field k]

/-- **The model `[N]` is surjective over any field.** `[N]` has finite fibres
(`mulByHom_finite_preimage_singleton`, any base) and `projModel W` is infinite, so the
range is infinite; it is closed (`[N]` proper) and irreducible (continuous image of the
integral `projModel W`), hence — by the `finite-or-univ` classification of closed
irreducibles on the dim-≤1 curve — the whole space. -/
theorem modelMulByHom_surjective (W : WeierstrassCurve k) [W.IsElliptic]
    (N : ℕ) [NeZero N] :
    Function.Surjective ⇑((modelEllipticCurve W).mulByHom (N : ℤ)).base := by
  haveI hpr : IsProper ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
    (modelEllipticCurve W).mulByHom_isProper (N : ℤ)
  haveI : IrreducibleSpace (projModel W) := inferInstance
  haveI : Infinite (projModel W) := projModel_infinite W
  set f : (modelEllipticCurve W).E → (modelEllipticCurve W).E :=
    ⇑((modelEllipticCurve W).mulByHom (N : ℤ)).base with hf
  have hcont : Continuous f := ((modelEllipticCurve W).mulByHom (N : ℤ)).continuous
  have hcl : IsClosed (Set.range f) :=
    ((modelEllipticCurve W).mulByHom (N : ℤ)).isClosedMap.isClosed_range
  have hirr : IsIrreducible (Set.range f) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (projModel W)).image f hcont.continuousOn
  have hfibre : ∀ y, (f ⁻¹' {y}).Finite := fun y =>
    ModularCurves.EllipticCurve.mulByHom_finite_preimage_singleton (modelEllipticCurve W) N y
  have hinf : (Set.range f).Infinite := by
    intro hfinr
    have hufin : (Set.univ : Set (projModel W)).Finite :=
      (hfinr.biUnion fun y _ => hfibre y).subset fun x _ =>
        Set.mem_biUnion (Set.mem_range_self x) rfl
    exact (Set.infinite_univ (α := projModel W)) hufin
  rcases projModel_isClosed_isIrreducible_finite_or_univ W hcl hirr with hfin | huniv
  · exact absurd hfin hinf
  · exact Set.range_eq_univ.mp huniv

/-! ### The field-level BB-FLAT assembly: `[N]` on the model over a field is FLAT

Assembly of the banked substrate ([FF-alg] + `modelMulByHom_surjective` + BB-QF finiteness)
over the standard-smooth chart cover supplied by the `SmoothOfRelativeDimension 1 E.π`
class field (each point of the target has an affine chart `V` with `Γ(E, V)` honestly
standard-smooth of relative dimension 1 over the base sections — no `RingHom.Locally`
unfolding needed). Per piece: `Γ(E, V) → Γ(E, [N]⁻¹V)` is a map of domains (the model is
integral), injective because `[N]` is surjective (comap of the section map is surjective
through the `fromSpec` square), hence flat by [FF-alg]. `Flat` is Zariski-local at the
target, so `[N]` is flat. -/

section FieldLevelFlat

/-- **(per-piece, ring level)** For a morphism `f` with affine `V` and affine preimage,
integral section rings, standard-smooth-of-relative-dimension-1 (over a field `k`) target
sections, and `f` surjective onto `V`, the section ring map `Γ(Y, V) ⟶ Γ(X, f⁻¹V)` is
flat — the [FF-alg] criterion (`flat_of_isDomain_of_injective_of_isStandardSmooth`), with
injectivity from surjectivity of the comap (via the `fromSpec` square
`IsAffineOpen.SpecMap_appLE_fromSpec`). -/
theorem flat_appLE_of_isDomain_of_isStandardSmooth
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) (hpre : IsAffineOpen (f ⁻¹ᵁ V))
    [IsDomain Γ(Y, V)] [IsDomain Γ(X, f ⁻¹ᵁ V)]
    [Algebra k Γ(Y, V)] [Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(Y, V)]
    (hsurj : ∀ w, w ∈ V → ∃ x, f.base x = w) :
    RingHom.Flat (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom := by
  -- comap surjectivity through the `fromSpec` square
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f hV hpre le_rfl
  have hcomap : Function.Surjective ⇑(Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)).base := by
    intro z
    have hzV : hV.fromSpec.base z ∈ V := by
      have hmem : hV.fromSpec.base z ∈ Set.range hV.fromSpec.base := Set.mem_range_self z
      rwa [hV.range_fromSpec] at hmem
    obtain ⟨x, hx⟩ := hsurj _ hzV
    have hxpre : x ∈ f ⁻¹ᵁ V := by
      show f.base x ∈ V
      rw [hx]; exact hzV
    obtain ⟨x', hx'⟩ : x ∈ Set.range hpre.fromSpec.base := by
      rw [hpre.range_fromSpec]; exact hxpre
    refine ⟨x', hV.fromSpec.isOpenEmbedding.injective ?_⟩
    have hpt := congrArg (fun g : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => g.base x') hsq
    simp only [Scheme.Hom.comp_apply] at hpt
    rw [hpt, hx', hx]
  have hd : DenseRange (PrimeSpectrum.comap (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom) := by
    have : Function.Surjective (PrimeSpectrum.comap (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom) := by
      intro z
      obtain ⟨w, hw⟩ := hcomap z
      exact ⟨w, hw⟩
    exact this.denseRange
  have hinj : Function.Injective (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
    injective_of_denseRange_comap hd
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  show Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  exact flat_of_isDomain_of_injective_of_isStandardSmooth k Γ(Y, V) Γ(X, f ⁻¹ᵁ V) hinj

/-- **(per-piece, scheme level)** Under the hypotheses of
`flat_appLE_of_isDomain_of_isStandardSmooth`, the restriction `f ∣_ V` is a flat morphism:
it is arrow-isomorphic (through `IsAffineOpen.isoSpec`) to `Spec.map` of the flat section
map. -/
theorem flat_morphismRestrict_of_isDomain_of_isStandardSmooth
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (hV : IsAffineOpen V) (hpre : IsAffineOpen (f ⁻¹ᵁ V))
    [IsDomain Γ(Y, V)] [IsDomain Γ(X, f ⁻¹ᵁ V)]
    [Algebra k Γ(Y, V)] [Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(Y, V)]
    (hsurj : ∀ w, w ∈ V → ∃ x, f.base x = w) :
    Flat (f ∣_ V) := by
  have hflat : RingHom.Flat (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom :=
    flat_appLE_of_isDomain_of_isStandardSmooth (k := k) f V hV hpre hsurj
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f hV hpre le_rfl
  -- the commuting square, inverse form: `Spec.map appLE ≫ isoSpec⁻¹ = isoSpec⁻¹ ≫ (f ∣_ V)`
  have hw : Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) ≫ hV.isoSpec.inv =
      hpre.isoSpec.inv ≫ (f ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hV.isoSpec_inv_ι,
      morphismRestrict_ι, ← Category.assoc, hpre.isoSpec_inv_ι, hsq]
  -- upgrade to the hom-form square and transport flatness through the arrow iso
  have hw' : hpre.isoSpec.hom ≫ Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) =
      (f ∣_ V) ≫ hV.isoSpec.hom := by
    rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq]
    exact hw
  have harrow : Arrow.mk (f ∣_ V) ≅
      Arrow.mk (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) :=
    Arrow.isoMk hpre.isoSpec hV.isoSpec hw'
  rw [MorphismProperty.arrow_mk_iso_iff (P := @Flat) harrow]
  exact Flat.SpecMap_iff.mpr hflat

open WeierstrassCurve in
/-- **(BB-FLAT fibre leg — the field-level flatness, [BBF-A1])** Over any field `k`,
multiplication by `N ≥ 1` on the projective model of an elliptic Weierstrass curve is
**flat**. Assembly: `Flat` is Zariski-local at the target; the target is covered by the
standard-smooth affine charts of `SmoothOfRelativeDimension 1 π` (the class field gives,
at every point, an affine `V` with `Γ(E, V)` honestly standard-smooth of relative
dimension 1 over `k`), and on each chart the section map is flat by [FF-alg]
(`flat_of_isDomain_of_injective_of_isStandardSmooth`: domains from integrality of the
model, injectivity from surjectivity of `[N]`). Finiteness of `[N]` (BB-QF + ZMT)
supplies the affine preimages. -/
theorem modelMulByHom_flat_of_field (W : WeierstrassCurve k) [W.IsElliptic]
    (N : ℕ) [NeZero N] :
    Flat ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
  haveI hLQF : LocallyQuasiFinite ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
    modelMulByHom_locallyQuasiFinite_of_field W N
  haveI hfin : IsFinite ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : IsIntegral (modelEllipticCurve W).E := inferInstanceAs (IsIntegral (projModel W))
  have hsurj : Function.Surjective ⇑((modelEllipticCurve W).mulByHom (N : ℤ)).base :=
    modelMulByHom_surjective W N
  have hexists := fun y : (modelEllipticCurve W).E =>
    (modelEllipticCurve W).smooth.exists_isStandardSmoothOfRelativeDimension y
  choose U hU V hV hyV e hss using hexists
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @Flat) (f := (modelEllipticCurve W).mulByHom (N : ℤ)) V ?_ ?_
  · rw [eq_top_iff]
    exact fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  · intro y
    haveI hpre : IsAffineOpen ((modelEllipticCurve W).mulByHom (N : ℤ) ⁻¹ᵁ V y) :=
      (hV y).preimage _
    haveI : Nonempty (V y) := ⟨⟨y, hyV y⟩⟩
    haveI : Nonempty ((modelEllipticCurve W).mulByHom (N : ℤ) ⁻¹ᵁ V y) := by
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨⟨x, show ((modelEllipticCurve W).mulByHom (N : ℤ)).base x ∈ V y by
        rw [hx]; exact hyV y⟩⟩
    -- the base chart is the whole `Spec k`
    have hUtop : U y = ⊤ := by
      refine TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.mpr fun z => ?_)
      have hz : z = (modelEllipticCurve W).π.base y :=
        Subsingleton.elim (α := PrimeSpectrum k) z _
      rw [hz]; exact e y (hyV y)
    -- the honest standard-smooth structure over `k` on the chart sections
    have hss' : RingHom.IsStandardSmoothOfRelativeDimension 1
        ((modelEllipticCurve W).π.appLE ⊤ (V y) (hUtop ▸ e y)).hom :=
      ((modelEllipticCurve W).π.appLE_congr (e y) hUtop rfl
        (fun φ => RingHom.IsStandardSmoothOfRelativeDimension 1 φ.hom)).mp (hss y)
    letI algk : Algebra k Γ((modelEllipticCurve W).E, V y) :=
      (((modelEllipticCurve W).π.appLE ⊤ (V y) (hUtop ▸ e y)).hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
    haveI hssk : Algebra.IsStandardSmoothOfRelativeDimension 1 k
        Γ((modelEllipticCurve W).E, V y) := by
      have h0 : RingHom.IsStandardSmoothOfRelativeDimension 0
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
        have := RingHom.IsStandardSmoothOfRelativeDimension.equiv
          ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
        rwa [CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom, Iso.symm_hom] at this
      exact hss'.comp h0
    exact flat_morphismRestrict_of_isDomain_of_isStandardSmooth (k := k)
      ((modelEllipticCurve W).mulByHom (N : ℤ)) (V y) (hV y) hpre
      (fun w _ => hsurj w)

end FieldLevelFlat

end ModularCurves
