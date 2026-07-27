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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

/-! ### Flat transport across pointed group-object isos + arbitrary field-valued points

The `Flat` analogue of `finite_fibres_mulByHom_of_isMonHom_iso` /
`locallyQuasiFinite_mulByHom_of_isMonHom_iso`, and the master fibre input for the
general-base BB-FLAT: `[N]` on the base change of `E/S` along ANY field-valued point
`Spec K ⟶ S` is flat. -/

end FieldLevelFlat

section FlatTransport

open EllipticCurve

variable {S : Scheme.{u}}

/-- **(Flat transport across a group-object iso)** If `φ : E ≅ F` as group objects over `S`
(`IsMonHom`), flatness of `[n]` transports from `F` to `E`: `[n]_E` is the conjugate
`φ ≫ [n]_F ≫ φ⁻¹`. -/
theorem flat_mulByHom_of_isMonHom_iso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] (n : ℤ)
    (hF : Flat (F.mulByHom n)) : Flat (E.mulByHom n) := by
  -- ascribe the underlying scheme morphisms to the `.E`-types (defeq)
  let ψ : E.E ⟶ F.E := φ.hom.left
  let ψ' : F.E ⟶ E.E := φ.inv.left
  have hc : E.mulByHom n ≫ ψ = ψ ≫ F.mulByHom n :=
    mulByHom_comp_left_of_isMonHom E F φ.hom n
  have hinv : ψ ≫ ψ' = 𝟙 E.E := by
    show φ.hom.left ≫ φ.inv.left = 𝟙 _
    rw [← Over.comp_left, φ.hom_inv_id, Over.id_left]
  have hinv' : ψ' ≫ ψ = 𝟙 F.E := by
    show φ.inv.left ≫ φ.hom.left = 𝟙 _
    rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  let eIso : E.E ≅ F.E := ⟨ψ, ψ', hinv, hinv'⟩
  exact (MorphismProperty.arrow_mk_iso_iff (P := @Flat)
    (Arrow.isoMk eIso eIso hc.symm)).mpr hF

/-- **(fibre input at residue points)** `[N]` on the fibre curve `E ×_S Spec κ(s)` is flat:
the fibre is pointed-isomorphic to a projective Weierstrass model over `κ(s)`
(`fibreModelIsoAsOver`), whose `[N]` is flat by the field-level theorem. -/
theorem flat_mulByHom_baseChange_residueField (E : EllipticCurve S) (N : ℕ) [NeZero N]
    (s : S) :
    Flat ((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) := by
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  exact flat_mulByHom_of_isMonHom_iso φ (N : ℤ) (modelMulByHom_flat_of_field W N)

/-- **(the `[N]` base-change square)** For any `g : T ⟶ S`, the `[N]` of the base-changed
curve is the pullback of the `[N]` of `E` along the projections — packaged as an
`IsPullback` square (by cancelling the `π`-square off the base-change rectangle). -/
theorem isPullback_mulByHom_baseChange (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (n : ℤ) :
    IsPullback ((E.baseChange g).mulByHom n) (pullback.fst E.π g)
      (pullback.fst E.π g) (E.mulByHom n) := by
  refine IsPullback.of_right ?_ (mulByHom_baseChange_fst E g n)
    ((IsPullback.of_hasPullback E.π g).flip)
  have e1 : (E.baseChange g).mulByHom n ≫ pullback.snd E.π g = pullback.snd E.π g :=
    mulByHom_π (E.baseChange g) n
  have e2 : E.mulByHom n ≫ E.π = E.π := mulByHom_π E n
  rw [e1, e2]
  exact (IsPullback.of_hasPullback E.π g).flip

/-- **(flat base-change stability of the fibre input)** If `[N]` of `E ×_S T` is flat
then so is `[N]` of `E ×_S T'` for any `h : T' ⟶ T`: the two `[N]`-base-change squares
paste, exhibiting the latter as a pullback of the former. -/
theorem flat_mulByHom_baseChange_comp (E : EllipticCurve S) (N : ℤ)
    {T T' : Scheme.{u}} (h : T' ⟶ T) (ι : T ⟶ S)
    (hflat : Flat ((E.baseChange ι).mulByHom N)) :
    Flat ((E.baseChange (h ≫ ι)).mulByHom N) := by
  have sq₁ := isPullback_mulByHom_baseChange E ι N
  have sq₂ := isPullback_mulByHom_baseChange E (h ≫ ι) N
  -- the comparison morphism between the two pullbacks, ascribed to the record types
  let β : (E.baseChange (h ≫ ι)).E ⟶ (E.baseChange ι).E :=
    pullback.map E.π (h ≫ ι) E.π ι (𝟙 _) h (𝟙 _) (by simp) (by simp)
  have hβfst : β ≫ pullback.fst E.π ι = pullback.fst E.π (h ≫ ι) := by
    show pullback.lift _ _ _ ≫ pullback.fst E.π ι = _
    rw [pullback.lift_fst, Category.comp_id]
  have hβsnd : β ≫ pullback.snd E.π ι = pullback.snd E.π (h ≫ ι) ≫ h := by
    show pullback.lift _ _ _ ≫ pullback.snd E.π ι = _
    rw [pullback.lift_snd]
  -- the comparison square commutes with `[N]`
  have hcomm : (E.baseChange (h ≫ ι)).mulByHom N ≫ β
      = β ≫ (E.baseChange ι).mulByHom N := by
    apply pullback.hom_ext
    · have l1 : (E.baseChange (h ≫ ι)).mulByHom N ≫ β ≫ pullback.fst E.π ι
          = pullback.fst E.π (h ≫ ι) ≫ E.mulByHom N := by
        rw [hβfst, mulByHom_baseChange_fst]
      have l2 : β ≫ (E.baseChange ι).mulByHom N ≫ pullback.fst E.π ι
          = pullback.fst E.π (h ≫ ι) ≫ E.mulByHom N := by
        rw [mulByHom_baseChange_fst]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ E.mulByHom N) hβfst)
      exact (Category.assoc _ _ _).trans (l1.trans (l2.symm.trans
        (Category.assoc _ _ _).symm))
    · have l1 : (E.baseChange (h ≫ ι)).mulByHom N ≫ β ≫ pullback.snd E.π ι
          = pullback.snd E.π (h ≫ ι) ≫ h := by
        rw [hβsnd]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ h) (mulByHom_baseChange_snd E (h ≫ ι) N))
      have l2 : β ≫ (E.baseChange ι).mulByHom N ≫ pullback.snd E.π ι
          = pullback.snd E.π (h ≫ ι) ≫ h := by
        rw [mulByHom_baseChange_snd, hβsnd]
      exact (Category.assoc _ _ _).trans (l1.trans (l2.symm.trans
        (Category.assoc _ _ _).symm))
  -- vertical pasting cancellation: `[N]_{h ≫ ι}` is the pullback of `[N]_ι` along `β`
  have sqβ : IsPullback ((E.baseChange (h ≫ ι)).mulByHom N) β β
      ((E.baseChange ι).mulByHom N) := by
    refine IsPullback.of_bot ?_ hcomm sq₁
    have hleg : β ≫ pullback.fst E.π ι = pullback.fst E.π (h ≫ ι) := hβfst
    rw [hleg]
    exact sq₂
  exact MorphismProperty.of_isPullback sqβ.flip hflat

/-- **(fibre input at arbitrary field-valued points — the BB-FLAT fibre master)**
`[N]` on the base change of `E/S` along ANY morphism `Spec K ⟶ S` from the spectrum
of a field is flat: the point factors through the residue field of the image of the
closed point (`SpecToEquivOfField`), the residue-point case is
`flat_mulByHom_baseChange_residueField`, and flatness passes to the further base
change `Spec K ⟶ Spec κ(s)`. -/
theorem flat_mulByHom_baseChange_of_field (E : EllipticCurve S) (N : ℕ) [NeZero N]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ S) :
    Flat ((E.baseChange g).mulByHom (N : ℤ)) := by
  rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S g]
  exact flat_mulByHom_baseChange_comp E (N : ℤ) _ _
    (flat_mulByHom_baseChange_residueField E N _)

end FlatTransport

end ModularCurves
