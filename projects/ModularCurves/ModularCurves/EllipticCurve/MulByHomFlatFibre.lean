import ModularCurves.ForMathlib.StandardSmoothMaximalDVR
import ModularCurves.EllipticCurve.MulByHomFibresGlobal
import ModularCurves.EllipticCurve.AdditionChartDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas

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

end ModularCurves
