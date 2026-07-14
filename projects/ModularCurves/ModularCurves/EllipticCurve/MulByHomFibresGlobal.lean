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

/-- **(BB-QF BETA per-fibre sub-leaf — the single remaining BETA obligation)** Each residue-field
fibre of `[N] : E ⟶ E` is locally quasi-finite. NOTE the fibre's LQF **cannot** come from `[N]`'s own
LQF (that is circular via `of_fiberToSpecResidueField`); it must come from the model. Precise discharge
route (degree-free, NOT `abelEnrichment_exists`-gated):
* **(a)** [ALPHA, `ModelFibreCount.lean`, in progress] over the field, `modelEllipticCurve W`'s `[N]`
  is `LocallyQuasiFinite` — image infinite via HasseWeil `card_torsion_ellPow_nat`, so fibres are proper
  closed in the dim-≤1 integral `zChart` (`coordinateRing_krullDimLE_one`), hence finite
  (`IsArtinianScheme.finite`);
* **(b)** [transport] over `κ̄(s)` (`s := π y`), `E_s ≅ modelEllipticCurve W_s` is a *pointed* iso, so
  `locallyQuasiFinite_mulByHom_of_isMonHom_iso` gives `LocallyQuasiFinite (E_{κ̄(s)}.mulByHom N)` — the
  `[IsMonHom]` from GIT 6.4 `isMonHom_of_one_comp_eq'` + the `localModel` pointed iso;
* **(c)** [fibre + descent] the fibre `fiberToSpecResidueField y` is a base change of `E_s.mulByHom N`
  (`mulByHom_baseChange`, `GroupLaw.lean:217`); LQF is base-change-stable, and descends `κ̄(s) → κ(y)`.
Blocked only on (a) (ALPHA's model conclusion) + the (b)/(c) fibre plumbing; a clean, bounded hand-off. -/
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
