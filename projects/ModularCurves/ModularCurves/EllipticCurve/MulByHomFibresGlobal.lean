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

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- **(BB-QF BETA per-fibre sub-leaf)** Each residue-field fibre of `[N] : E ⟶ E` is locally
quasi-finite. Over the residue field `κ(y)`, the fibre transports from the field-level model
fibre-count (`ModelFibreCount.lean`, ALPHA) across the pointed comparison `E_s ≅ modelEllipticCurve W_s`
(`locallyQuasiFinite_mulByHom_of_isMonHom_iso`, with `[IsMonHom]` from GIT 6.4 rigidity + the localModel
pointed iso). Degree-free (HasseWeil torsion witness only); NOT `abelEnrichment_exists`-gated. -/
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
