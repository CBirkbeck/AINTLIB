import ModularCurves.EllipticCurve.MulByHomFibres
import ModularCurves.EllipticCurve.ModelFibreCount
import ModularCurves.ForMathlib.QuasiFiniteDescent

/-!
# BB-QF BETA global assembly — `[N]` locally quasi-finite from the per-fibre transport

The BETA half of the BB-QF wall-break pipeline (partition ALPHA = model fibre-count in
`ModelFibreCount.lean`; BETA = transport assembly). This file wires the **global reduction**:
`[N] : E ⟶ E` is locally quasi-finite as soon as each residue-field fibre is
(`AlgebraicGeometry.LocallyQuasiFinite.of_fiberToSpecResidueField`), and isolates the single
remaining per-fibre obligation `fiber_mulByHom_locallyQuasiFinite` as the clean sub-leaf.

That sub-leaf is discharged (not `abelEnrichment_exists`-gated) by transporting ALPHA's field-level
model fibre-count across the *pointed* comparison `E_s ≅ modelEllipticCurve W_s` — via the PROVEN
`abelEnrichment_unique_of_isLocallyNoetherian` + GIT 6.4 rigidity + power-naturality
(`mulBy_comp_of_isMonHom`), fed to `locallyQuasiFinite_mulByHom_of_isMonHom_iso`. See
`.mathlib-quality/decomposition-bbqf.md`.

Once `fiber_mulByHom_locallyQuasiFinite` lands, `mulByHom_locallyQuasiFinite_assembled` closes, and
(by the boarded mechanical relocation below `Torsion`) the `Torsion.mulByHom_locallyQuasiFinite` sorry
closes ⟹ `mulByHom_isFinite` ⟹ `torsionπ_isFinite` (the whole E[N]-finiteness trail).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- **(BETA transport building block — GIT 6.4 rigidity, general `E ⟶ F`)** Over a locally
noetherian base, a **pointed** hom of elliptic-curve records `φ : E.asOver ⟶ F.asOver` (fixing the
zero section, `η ≫ φ = η`) is a monoid-object homomorphism. Generalises
`EndomorphismDegree.endMonHom` (the `E = F` case) to distinct records by feeding the source's
`EllipticCurveGeom.universallyOConnected` (+ proper/flat, and the target's separatedness) to the
sorry-free rigidity engine `isMonHom_of_one_comp_eq'`. This discharges the `[IsMonHom φ]` hypothesis
of `locallyQuasiFinite_mulByHom_of_isMonHom_iso` for the localModel fibre comparison
`E_s ≅ modelEllipticCurve W_s` (whose pointedness is `localModel`'s `compat_zero`). -/
theorem isMonHom_of_pointed [IsLocallyNoetherian S] {E F : EllipticCurve S}
    (φ : E.asOver ⟶ F.asOver) (hη : η[E.asOver] ≫ φ = η[F.asOver]) : IsMonHom φ where
  one_hom := hη
  mul_hom := by
    haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
    haveI : IsProper E.asOver.hom := inferInstanceAs (IsProper E.π)
    haveI : Flat E.asOver.hom := inferInstanceAs (Flat E.π)
    haveI : IsSeparated F.asOver.hom := inferInstanceAs (IsSeparated F.π)
    exact isMonHom_of_one_comp_eq' E.toEllipticCurveGeom.universallyOConnected φ hη

/-- **(BETA topological transport)** Finite fibres of `[n]` transport across a pointed monoid-object
iso `φ : E.asOver ≅ F.asOver` of elliptic records: if every fibre of `[n]_F` is finite, so is every
fibre of `[n]_E`. The homeomorphism `φ.hom.left.base` conjugates `[n]_E` to `[n]_F` (power-naturality
`mulByHom_comp_left_of_isMonHom`), embedding the `E`-fibre over `x` into the finite `F`-fibre over
`φ.hom.left.base x`. Feeds the topological `mulByHom_finite_fibres` route (ALPHA supplies the model
finite fibres; `FibrewiseElliptic` + `isMonHom_of_pointed` supply the pointed iso). -/
theorem finite_fibres_mulByHom_of_isMonHom_iso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] (n : ℤ)
    (hF : ∀ y, (⇑(F.mulByHom n) ⁻¹' {y}).Finite) (x : E.E) :
    (⇑(E.mulByHom n) ⁻¹' {x}).Finite := by
  have hc := mulByHom_comp_left_of_isMonHom E F φ.hom n
  have hbase : ∀ x' : E.E,
      (F.mulByHom n) (φ.hom.left x') = φ.hom.left ((E.mulByHom n) x') := by
    intro x'
    exact (congrArg (fun f : E.E ⟶ F.E => f x') hc).symm
  have hinj : Function.Injective (⇑φ.hom.left) := by
    have h1 : φ.hom.left ≫ φ.inv.left = 𝟙 _ := by
      rw [← Over.comp_left, φ.hom_inv_id, Over.id_left]
    refine Function.LeftInverse.injective (g := ⇑φ.inv.left) fun z => ?_
    rw [← Scheme.Hom.comp_apply, h1]; simp
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine (hF (φ.hom.left x)).subset ?_
  rintro _ ⟨x', hx', rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx' ⊢
  rw [hbase x', hx']

/-- **(BETA assembly entry point)** An elliptic curve `E/S` is fibrewise elliptic: every fibre of `E.π`,
pointed by the zero section, is pointed-isomorphic (as a `κ(s)`-scheme) to the projective model of an
elliptic Weierstrass curve over the residue field. Immediate from the record's `localModel`
(`LocallyWeierstrass.fibrewiseElliptic`). Supplies, per `s`, the pointed iso
`e : E.π.fiber s ≅ projModel W` (`heπ` = structure-map compat, `hez` = zero-section compat) that the
transport assembly wraps into an `asOver` iso + `isMonHom_of_pointed hez` to feed
`finite_fibres_mulByHom_of_isMonHom_iso` on ALPHA's model finite fibres. -/
theorem fibrewiseElliptic (E : EllipticCurve S) :
    FibrewiseElliptic E.π E.zero E.zero_π :=
  E.localModel.fibrewiseElliptic

/-- **(BETA raw-iso→asOver wrapping — g5-independent)** At each `s : S`, the geometric fibre of `E`
(as the base-changed record `E.baseChange (fromSpecResidueField s)`) is isomorphic **as a group object**
to the model `modelEllipticCurve W`: `FibrewiseElliptic`'s raw pointed iso `e` lifts to an `asOver` iso
(`Over.isoMk e heπ`), and it is `IsMonHom` by `isMonHom_of_pointed` — the pointedness comes from `hez`
(`(E.baseChange _).zero` is defeq `sectionFiberPoint`) transported through `one_eq_zero` (unit = zero) on
both sides. This is the wrapping the transport (`finite_fibres_mulByHom_of_isMonHom_iso`) consumes to move
ALPHA's model fibre-count onto the geometric fibre. -/
theorem fibreModelIsoAsOver (E : EllipticCurve S) (s : S)
    (W : WeierstrassCurve (S.residueField s)) [W.IsElliptic]
    (e : E.π.fiber s ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = E.π.fiberToSpecResidueField s)
    (hez : sectionFiberPoint E.π E.zero E.zero_π s ≫ e.hom = projModelZero W) :
    ∃ φ : (E.baseChange (S.fromSpecResidueField s)).asOver ≅ (modelEllipticCurve W).asOver,
      IsMonHom φ.hom := by
  haveI : IsLocallyNoetherian (Spec (S.residueField s)) := inferInstance
  -- ascribe `e` to the `asOver.left` types (defeq) so `Over.isoMk_hom_left` fires without cast friction
  let e' : (E.baseChange (S.fromSpecResidueField s)).asOver.left ≅ (modelEllipticCurve W).asOver.left := e
  have heπ' : e'.hom ≫ (modelEllipticCurve W).asOver.hom
      = (E.baseChange (S.fromSpecResidueField s)).asOver.hom := heπ
  refine ⟨Over.isoMk e' heπ', isMonHom_of_pointed _ ?_⟩
  -- η-matching: `one_eq_zero` (both) turns `η.left` into `𝟙_.hom ≫ zero`; `(E.baseChange _).zero` is
  -- defeq `sectionFiberPoint`, so `hez` (`sectionFiberPoint ≫ e.hom = projModelZero W`) closes it.
  ext1
  rw [Over.comp_left, show (Over.isoMk e' heπ').hom.left = e'.hom from rfl,
    (E.baseChange (S.fromSpecResidueField s)).one_eq_zero, (modelEllipticCurve W).one_eq_zero]
  exact (Category.assoc _ _ _).trans
    (congrArg _ (show (E.baseChange (S.fromSpecResidueField s)).zero ≫ e'.hom
      = (modelEllipticCurve W).zero from hez))

/-! ### κ̄-wiring: the model LQF over an arbitrary field (seam-i application)

Base-change the model to the algebraic closure (T-A5a: `projModel (W.baseChange κ̄)` IS
the pullback of `projModel W`), transport ALPHA's algebraically-closed LQF through the
pointed iso, and descend along the fppf `Spec κ̄ → Spec k` with the new
`DescendsAlong @LocallyQuasiFinite` instance. -/

section KappaBarWiring

open WeierstrassCurve

variable {k : Type u} [Field k]

/-- **(κ̄-wiring, pointed iso)** The base change of the model record along a field
extension is pointed-isomorphic, as a group object, to the model record of the
base-changed Weierstrass curve: the T-A5a pullback + the `projModelZero_baseChange`
zero-leg, upgraded by GIT 6.4 (`isMonHom_of_pointed`). -/
theorem modelBaseChangeIsoAsOver (W : WeierstrassCurve k) [W.IsElliptic]
    (k' : Type u) [Field k'] [Algebra k k'] :
    ∃ φ : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).asOver ≅
      (modelEllipticCurve (W.map (algebraMap k k'))).asOver,
      IsMonHom φ.hom := by
  have b := isPullback_projModelBaseChange (R' := k') W
  -- ascribe the pullback iso to the `asOver.left` types (defeq) so `Over.isoMk` fires cleanly
  let e' : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).asOver.left ≅
      (modelEllipticCurve (W.map (algebraMap k k'))).asOver.left := b.isoPullback.symm
  have heπ' : e'.hom ≫ (modelEllipticCurve (W.map (algebraMap k k'))).asOver.hom
      = ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).asOver.hom := by
    show b.isoPullback.inv ≫ projModelπ (W.map (algebraMap k k')) = _
    rw [Iso.inv_comp_eq]
    exact b.isoPullback_hom_snd.symm
  refine ⟨Over.isoMk e' heπ', isMonHom_of_pointed _ ?_⟩
  -- zero-compat: `baseChange-zero ≫ isoPullback.inv = projModelZero (W.map _)`
  have hz : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).zero ≫ e'.hom
      = (modelEllipticCurve (W.map (algebraMap k k'))).zero := by
    -- the two pullback components of the base-changed zero section (defeq `pullback.lift`)
    have hfst : ((modelEllipticCurve W).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).zero ≫
          pullback.fst (modelEllipticCurve W).π
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))
        = Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ (modelEllipticCurve W).zero :=
      pullback.lift_fst _ _ _
    have hsnd : ((modelEllipticCurve W).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).zero ≫
          pullback.snd (modelEllipticCurve W).π
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))
        = 𝟙 _ :=
      pullback.lift_snd _ _ _
    -- forward form: the model zero maps to the base-changed zero under the pullback iso
    have hz2 : projModelZero (W.map (algebraMap k k')) ≫ b.isoPullback.hom
        = ((modelEllipticCurve W).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).zero := by
      refine pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (CategoryStruct.comp _) b.isoPullback_hom_fst).trans ?_
        exact (projModelZero_baseChange (R' := k') W).trans hfst.symm
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (CategoryStruct.comp _) b.isoPullback_hom_snd).trans ?_
        exact (projModelZero_projModelπ (W.map (algebraMap k k'))).trans hsnd.symm
    show _ ≫ b.isoPullback.inv = projModelZero (W.map (algebraMap k k'))
    rw [Iso.comp_inv_eq]
    exact hz2.symm
  ext1
  rw [Over.comp_left, show (Over.isoMk e' heπ').hom.left = e'.hom from rfl,
    ((modelEllipticCurve W).baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).one_eq_zero,
    (modelEllipticCurve (W.map (algebraMap k k'))).one_eq_zero]
  exact (Category.assoc _ _ _).trans (congrArg _ hz)

/-- **(κ̄-wiring master — BB-QF over an arbitrary field)** The model `[N]` is locally
quasi-finite over ANY field `k`: base-change to the algebraic closure `κ̄` (ALPHA's
`modelMulByHom_locallyQuasiFinite`), transport across the pointed group-object iso
`modelBaseChangeIsoAsOver` (GIT 6.4), and fppf-descend along `Spec κ̄ → Spec k`
(surjective + flat + quasi-compact) using the `DescendsAlong @LocallyQuasiFinite`
instance (`ForMathlib/QuasiFiniteDescent`) on the `[N]` base-change square. -/
theorem modelMulByHom_locallyQuasiFinite_of_field (W : WeierstrassCurve k) [W.IsElliptic]
    (N : ℕ) [NeZero N] :
    LocallyQuasiFinite ((modelEllipticCurve W).mulByHom N) := by
  set κ := AlgebraicClosure k
  set fc : CommRingCat.of k ⟶ CommRingCat.of κ := CommRingCat.ofHom (algebraMap k κ)
    with hfc
  -- (1) ALPHA over the algebraic closure
  haveI h1 : LocallyQuasiFinite
      ((modelEllipticCurve (W.map (algebraMap k κ))).mulByHom N) :=
    modelMulByHom_locallyQuasiFinite (W.map (algebraMap k κ)) N
  -- (2) transport across the pointed group-object iso to the base-changed record
  obtain ⟨φ, hφ⟩ := modelBaseChangeIsoAsOver W κ
  haveI := hφ
  haveI h2 : LocallyQuasiFinite
      (((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom N) :=
    locallyQuasiFinite_mulByHom_of_isMonHom_iso φ N
  -- (3) the `[N]` base-change square, by cancelling the π-square off the big rectangle
  have hcomm : ((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom N ≫
        pullback.fst (modelEllipticCurve W).π (Spec.map fc)
      = pullback.fst (modelEllipticCurve W).π (Spec.map fc) ≫
        (modelEllipticCurve W).mulByHom N :=
    mulByHom_baseChange_fst (modelEllipticCurve W) (Spec.map fc) N
  have hsq : IsPullback
      (((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom N)
      (pullback.fst (modelEllipticCurve W).π (Spec.map fc))
      (pullback.fst (modelEllipticCurve W).π (Spec.map fc))
      ((modelEllipticCurve W).mulByHom N) := by
    refine IsPullback.of_right ?_ hcomm
      ((IsPullback.of_hasPullback (modelEllipticCurve W).π (Spec.map fc)).flip)
    have e1 : ((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom N ≫
          pullback.snd (modelEllipticCurve W).π (Spec.map fc)
        = pullback.snd (modelEllipticCurve W).π (Spec.map fc) :=
      mulByHom_π ((modelEllipticCurve W).baseChange (Spec.map fc)) N
    have e2 : (modelEllipticCurve W).mulByHom N ≫ (modelEllipticCurve W).π
        = (modelEllipticCurve W).π :=
      mulByHom_π (modelEllipticCurve W) N
    rw [e1, e2]
    exact (IsPullback.of_hasPullback (modelEllipticCurve W).π (Spec.map fc)).flip
  -- (4) the descent leg `Spec κ̄ → Spec k` is fppf
  haveI hSurjSpec : Surjective (Spec.map fc) := by
    refine ⟨fun y => ?_⟩
    haveI hsing : Subsingleton (↥(Spec (CommRingCat.of k))) :=
      ⟨fun a b => PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
        (Ideal.eq_bot_of_prime _).symm)⟩
    obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of κ)) := inferInstance
    exact ⟨x, Subsingleton.elim _ _⟩
  haveI hFlatSpec : Flat (Spec.map fc) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap k κ).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  haveI hQCSpec : QuasiCompact (Spec.map fc) := inferInstance
  -- (5) descend
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq
    ⟨⟨MorphismProperty.pullback_fst _ _ hSurjSpec,
      MorphismProperty.pullback_fst _ _ hFlatSpec⟩,
      MorphismProperty.pullback_fst _ _ hQCSpec⟩ h2

/-- **(model fibre-count over an arbitrary field)** Every topological fibre of the model
`[N]` is finite over ANY field `k`: the κ̄-master gives local quasi-finiteness, `[N]` is
proper (an endomorphism of the proper model, cancellation along the separated `π`), hence
quasi-compact, and mathlib's `Scheme.Hom.finite_preimage_singleton` finishes. Removes the
`[IsAlgClosed]` hypothesis from ALPHA's `modelMulByHom_finite_fibres`. -/
theorem modelMulByHom_finite_fibres_of_field (W : WeierstrassCurve k) [W.IsElliptic]
    (N : ℕ) [NeZero N] (y : (modelEllipticCurve W).E) :
    (⇑((modelEllipticCurve W).mulByHom N).base ⁻¹' {y}).Finite := by
  haveI := modelMulByHom_locallyQuasiFinite_of_field W N
  haveI hp : IsProper ((modelEllipticCurve W).mulByHom N) := by
    haveI h : IsProper ((modelEllipticCurve W).mulByHom N ≫ (modelEllipticCurve W).π) := by
      rw [mulByHom_π]
      exact (modelEllipticCurve W).proper
    exact IsProper.of_comp ((modelEllipticCurve W).mulByHom N) (modelEllipticCurve W).π
  exact ((modelEllipticCurve W).mulByHom N).finite_preimage_singleton y

end KappaBarWiring

/-- **(BB-QF global fibre-count — the geometric leaf over an arbitrary base)** Every
topological fibre of `[N] : E ⟶ E` is finite. The fibre over `y` lies inside the `π`-fibre
over `s := π y`, which is the (pointed-model-isomorphic) base-changed record over `κ(s)`;
`finite_fibres_mulByHom_of_isMonHom_iso` transports the any-field model fibre-count
`modelMulByHom_finite_fibres_of_field` onto it, and the fibre embedding `pullback.fst`
(= `fiberι`) carries the finiteness up. This is exactly the `Torsion.lean` BB-QF leaf
`mulByHom_finite_fibres`, proved here over ANY base and in EVERY characteristic. -/
theorem mulByHom_finite_preimage_singleton (E : EllipticCurve S) (N : ℕ) [NeZero N]
    (y : E.E) : (⇑(E.mulByHom N).base ⁻¹' {y}).Finite := by
  set s := E.π.base y with hs
  have hrange : Set.range ⇑(pullback.fst E.π (S.fromSpecResidueField s))
      = ⇑E.π ⁻¹' {s} := E.π.range_fiberι s
  have hinj : Function.Injective ⇑(pullback.fst E.π (S.fromSpecResidueField s)) :=
    (E.π.fiberι s).isEmbedding.injective
  -- pointed model on the π-fibre + any-field model fibre-count, transported
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  have hbc : ∀ z, (⇑((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ))
      ⁻¹' {z}).Finite :=
    fun z => finite_fibres_mulByHom_of_isMonHom_iso φ (N : ℤ)
      (fun w => modelMulByHom_finite_fibres_of_field W N w) z
  -- points of the `[N]`-fibre lie over `s`
  have hπN : ∀ x : E.E, E.π ((E.mulByHom (N : ℤ)) x) = E.π x := by
    intro x
    rw [← Scheme.Hom.comp_apply, E.mulByHom_π]
  -- `y` itself lies over `s`
  have hyr : y ∈ Set.range ⇑(pullback.fst E.π (S.fromSpecResidueField s)) := by
    rw [hrange]
    exact hs.symm
  obtain ⟨ytil, hytil⟩ := hyr
  -- the fibre is contained in the fibre-inclusion image of the base-changed fibre
  refine Set.Finite.subset
    ((hbc ytil).image ⇑(pullback.fst E.π (S.fromSpecResidueField s))) ?_
  intro x hx
  have hxy : (E.mulByHom (N : ℤ)) x = y := hx
  have hxr : x ∈ Set.range ⇑(pullback.fst E.π (S.fromSpecResidueField s)) := by
    rw [hrange]
    show E.π x = s
    have h2 : s = E.π ((E.mulByHom (N : ℤ)) x) := by rw [hxy]
    exact (h2.trans (hπN x)).symm
  obtain ⟨xtil, hxtil⟩ := hxr
  refine ⟨xtil, ?_, hxtil⟩
  have key : ∀ a : ↥(pullback E.π (S.fromSpecResidueField s)),
      (E.mulByHom (N : ℤ)) ((pullback.fst E.π (S.fromSpecResidueField s)) a)
      = (pullback.fst E.π (S.fromSpecResidueField s))
          (((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) a) := by
    intro a
    have h1 := congrFun (congrArg
      (fun f : (E.baseChange (S.fromSpecResidueField s)).E ⟶ E.E => ⇑f)
      (mulByHom_baseChange_fst E (S.fromSpecResidueField s) (N : ℤ))) a
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans
      (h1.symm.trans (Scheme.Hom.comp_apply _ _ _))
  apply hinj
  calc (pullback.fst E.π (S.fromSpecResidueField s))
        (((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) xtil)
      = (E.mulByHom (N : ℤ)) ((pullback.fst E.π (S.fromSpecResidueField s)) xtil) :=
        (key xtil).symm
    _ = (E.mulByHom (N : ℤ)) x := by rw [hxtil]
    _ = y := hxy
    _ = (pullback.fst E.π (S.fromSpecResidueField s)) ytil := hytil.symm

/-- **(BB-QF CLOSED — direct global assembly)** `[N] : E ⟶ E` is locally quasi-finite over
an arbitrary base, via `LocallyQuasiFinite.of_finite_preimage_singleton` on the global
fibre-count (`[N]` is proper, hence locally of finite type). This is the full content of
the `Torsion.lean` BB-QF box, and makes the per-fibre sub-leaf below a corollary
(base-change stability) rather than an input. -/
theorem mulByHom_locallyQuasiFinite_global (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    LocallyQuasiFinite (E.mulByHom N) := by
  haveI hp : IsProper (E.mulByHom N) := by
    haveI h : IsProper (E.mulByHom N ≫ E.π) := by
      rw [E.mulByHom_π]
      exact E.proper
    exact IsProper.of_comp (E.mulByHom N) E.π
  exact LocallyQuasiFinite.of_finite_preimage_singleton _
    fun x => mulByHom_finite_preimage_singleton E N x

/-- **(BB-QF BETA per-fibre sub-leaf — the single remaining BETA obligation)** Each residue-field
fibre of `[N] : E ⟶ E` is locally quasi-finite. NOTE the fibre's LQF **cannot** come from `[N]`'s own
LQF (that is circular via `of_fiberToSpecResidueField`); it must come from the model. Precise discharge
route (degree-free, NOT `abelEnrichment_exists`-gated):
* **(a)** [ALPHA, `ModelFibreCount.lean`, in progress] over the field, `modelEllipticCurve W`'s `[N]`
  is `LocallyQuasiFinite` — image infinite via HasseWeil `card_torsion_ellPow_nat`, so fibres are proper
  closed in the dim-≤1 integral `zChart` (`coordinateRing_krullDimLE_one`), hence finite
  (`IsArtinianScheme.finite`);
* **(b)** [transport — ALL building blocks LANDED] over `κ̄(s)` (`s := π y`), `E_s ≅ modelEllipticCurve W_s`
  is a *pointed* iso, so `locallyQuasiFinite_mulByHom_of_isMonHom_iso` gives
  `LocallyQuasiFinite (E_{κ̄(s)}.mulByHom N)`; the `[IsMonHom]` is discharged by **`isMonHom_of_pointed`**
  (this file, PROVEN) from the pointedness of the iso alone;
* **(c)** [fibre + descent] the fibre `fiberToSpecResidueField y` is a base change of `E_s.mulByHom N`
  (`mulByHom_baseChange`, `GroupLaw.lean:217`); LQF is base-change-stable, and descends `κ̄(s) → κ(y)`.
**ALL transport machinery now PROVEN + axiom-clean:** `fibrewiseElliptic`, **`fibreModelIsoAsOver`** (the
raw-iso→asOver wrapping INCL. its `IsMonHom` η-matching — the deep transparency-cast piece, now closed),
`finite_fibres_mulByHom_of_isMonHom_iso`, `locallyQuasiFinite_mulByHom_of_isMonHom_iso`,
`mulByHom_locallyQuasiFinite_assembled`. So this sub-leaf reduces to: `fibreModelIsoAsOver` (at `s := π y`)
+ `finite_fibres_mulByHom_of_isMonHom_iso` transport ALPHA's model finite fibres
(`modelMulByHom_finite_preimage_singleton`, mod g5) onto `(E.baseChange (fromSpecResidueField s)).mulByHom N`;
then the **fibre-of-endo identification** — `(E.mulByHom N)`'s fibre ↔ the base-changed record's `[N]`-fibre
via the pullback square (`Scheme.Pullback.range_fst` + `mulByHom_baseChange_fst`) + κ̄/κ descent. The ONLY
remaining pieces: the fibre-of-endo id (deep pullback, no mathlib shortcut) + ALPHA's g5. -/
theorem fiber_mulByHom_locallyQuasiFinite (E : EllipticCurve S) (N : ℕ) [NeZero N] (y : E.E) :
    LocallyQuasiFinite ((E.mulByHom N).fiberToSpecResidueField y) := by
  haveI := mulByHom_locallyQuasiFinite_global E N
  exact MorphismProperty.pullback_snd _ _ this

/-- **(BB-QF BETA global assembly — PROVED here)** `[N] : E ⟶ E` is locally quasi-finite, by the
mathlib fibrewise criterion `LocallyQuasiFinite.of_fiberToSpecResidueField` applied to the per-fibre
sub-leaf `fiber_mulByHom_locallyQuasiFinite`. This is the assembled form of `Torsion`'s BB-QF leaf
`mulByHom_locallyQuasiFinite` (identical statement); the boarded relocation wires it in. -/
theorem mulByHom_locallyQuasiFinite_assembled (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    LocallyQuasiFinite (E.mulByHom N) :=
  LocallyQuasiFinite.of_fiberToSpecResidueField _ fun y => E.fiber_mulByHom_locallyQuasiFinite N y



end EllipticCurve

end ModularCurves
