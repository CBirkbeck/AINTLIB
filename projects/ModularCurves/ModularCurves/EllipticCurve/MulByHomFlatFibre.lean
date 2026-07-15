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

end ModularCurves
