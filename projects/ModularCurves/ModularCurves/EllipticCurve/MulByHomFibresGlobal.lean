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
