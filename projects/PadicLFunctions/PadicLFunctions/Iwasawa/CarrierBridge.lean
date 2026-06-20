import PadicLFunctions.Measure.Functoriality
import PadicLFunctions.Measure.FiniteProduct
import PadicLFunctions.Iwasawa.PlusPart
import PadicLFunctions.Iwasawa.StructureTheory.Isotypic

/-!
# The carrier bridge `PadicMeasure(𝒢⁺) ≅ IwasawaAlgebraGroup ℤ_p Δ`  (S13-G, CARRIER-BRIDGE)

The ring isomorphism connecting §12's measure-algebra carrier `Λ(𝒢⁺) = PadicMeasure p (GPlus p)` to
the structure-theory carrier `IwasawaAlgebraGroup ℤ_p Δ = (ℤ_p⟦T⟧)[Δ]` over which `charIdealGroup`
is defined.  It is assembled (this file) from the measure-algebra tools
* `pushforwardRingEquiv` — functoriality along a continuous group iso,
* `finiteProductRingEquiv` — `PadicMeasure(Δ × Γ) ≅ (PadicMeasure Γ)[Δ]` for finite `Δ`,
* `mahlerPushforwardRingEquiv ∘ mahlerRingEquiv` — `PadicMeasure(Γ) ≅ ℤ_p⟦T⟧` via the log iso `Γ ≅ ℤ_p`,
* `MonoidAlgebra.mapRingEquiv` — coefficient base-change,

given the two **group-theoretic** inputs (discharged in `Iwasawa/GPlusDecomp.lean`):
the decomposition `𝒢⁺ ≅ Δ × Γ` (`Δ` finite Teichmüller part, `Γ` the pro-cyclic 1-units) and the
logarithm isomorphism `Γ ≅ (ℤ_p, +)`.

## Main declarations

* `PadicMeasure.carrierBridge`: `PadicMeasure p (GPlus p) ≃+* IwasawaAlgebraGroup ℤ_[p] Δ`.
-/

noncomputable section

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-- **The carrier bridge** (assembled).  From a continuous group isomorphism `𝒢⁺ ≅ Δ × Γ` (data
`g, g'` and the hom/inverse equations) with `Δ` finite and `Γ` a compact commutative group, together
with a logarithm isomorphism `Γ ≅ (ℤ_p, +)` (data `logCM, expCM` and equations), we obtain the ring
isomorphism `PadicMeasure p (GPlus p) ≃+* IwasawaAlgebraGroup ℤ_[p] Δ`. -/
def carrierBridge
    {Δ : Type*} [CommGroup Δ] [Fintype Δ] [DecidableEq Δ] [TopologicalSpace Δ] [DiscreteTopology Δ]
    {Γ : Type*} [TopologicalSpace Γ] [CommGroup Γ] [ContinuousMul Γ] [CompactSpace Γ]
    (g : C(GPlus p, Δ × Γ)) (g' : C(Δ × Γ, GPlus p))
    (gmul : ∀ x y, g (x * y) = g x * g y) (gone : g 1 = 1)
    (gleft : ∀ x, g' (g x) = x) (gright : ∀ y, g (g' y) = y)
    (logCM : C(Γ, ℤ_[p])) (expCM : C(ℤ_[p], Γ))
    (hlogmul : ∀ x y, logCM (x * y) = logCM x + logCM y) (hlogone : logCM 1 = 0)
    (hexpleft : ∀ x, expCM (logCM x) = x) (hexpright : ∀ a, logCM (expCM a) = a) :
    PadicMeasure p (GPlus p) ≃+* Iwasawa.IwasawaAlgebraGroup ℤ_[p] Δ :=
  (pushforwardRingEquiv p g g' gmul gone gleft gright).trans
    ((finiteProductRingEquiv p).trans
      (MonoidAlgebra.mapRingEquiv Δ
        ((mahlerPushforwardRingEquiv p logCM expCM hlogmul hlogone hexpleft hexpright).trans
          (mahlerRingEquiv p))))

end PadicMeasure
