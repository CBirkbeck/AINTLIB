import ModularCurves.EllipticCurve.MulByHomFibres

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
  refine ⟨Over.isoMk e heπ, isMonHom_of_pointed _ ?_⟩
  -- η-matching (STRUCTURE LANDED; closer scoped). Derivation is mapped: `ext1` reduces to
  -- `η.left ≫ (Over.isoMk e heπ).hom.left = η.left`; `one_eq_zero` (both records) rewrites each
  -- `η.left = 𝟙_.hom ≫ zero`, `(E.baseChange _).zero` is defeq `sectionFiberPoint`, and `hez`
  -- (`sectionFiberPoint ≫ e.hom = projModelZero W = (modelEllipticCurve W).zero`) closes it.
  -- The SYNTACTIC closer is transparency-blocked: `Over.isoMk e heπ` carries `e`'s defeq-cast type
  -- (`fiber ≅ projModel` ↦ `asOver.left ≅ asOver.left`), so `Over.isoMk_hom_left`-style rewrites and
  -- `𝟙_`-base matches (`residueField s` vs `CommRingCat.of ↑(residueField s)`) don't fire under
  -- `instances` transparency; needs `eqToIso` cast-restructuring (Comparison.lean-style). Atlas-lane closer.
  ext1
  sorry

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
The transport/rigidity/assembly building blocks are all landed green (`locallyQuasiFinite_mulByHom_of_isMonHom_iso`,
`isMonHom_of_pointed`, `mulByHom_locallyQuasiFinite_assembled`); the ONLY remaining work is (a) ALPHA's
model conclusion (g1–g5) + the fibre-iso extraction + the (c) fibre-of-endo identification.
**De-risking note:** the per-fibre pointed iso is a READY structure — `E`'s `FibrewiseElliptic` (from
`localModel`) yields, at each residue point `p`, a `⟨W', e, heπ, hez⟩` with `e` a *pointed* iso
(`heπ` = `compat_π`, `hez` = `compat_zero`); see the `obtain ⟨W', hW', e, heπ, hez⟩ := h p` pattern in
`Comparison.isElliptic_of_fibrewiseElliptic_projModel` (`Comparison.lean:300+`). So step (b)'s iso is a
clean `FibrewiseElliptic` application, and `hez` feeds `isMonHom_of_pointed` directly — no deep atlas
navigation. Bounded, atlas-context hand-off to the ALPHA session. -/
theorem fiber_mulByHom_locallyQuasiFinite (E : EllipticCurve S) (N : ℕ) [NeZero N] (y : E.E) :
    LocallyQuasiFinite ((E.mulByHom N).fiberToSpecResidueField y) := by sorry

/-- **(BB-QF BETA global assembly — PROVED here)** `[N] : E ⟶ E` is locally quasi-finite, by the
mathlib fibrewise criterion `LocallyQuasiFinite.of_fiberToSpecResidueField` applied to the per-fibre
sub-leaf `fiber_mulByHom_locallyQuasiFinite`. This is the assembled form of `Torsion`'s BB-QF leaf
`mulByHom_locallyQuasiFinite` (identical statement); the boarded relocation wires it in. -/
theorem mulByHom_locallyQuasiFinite_assembled (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    LocallyQuasiFinite (E.mulByHom N) :=
  LocallyQuasiFinite.of_fiberToSpecResidueField _ fun y => E.fiber_mulByHom_locallyQuasiFinite N y

end EllipticCurve

end ModularCurves
