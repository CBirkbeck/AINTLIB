import PadicLFunctions.Iwasawa.StructureTheory.CharIdealGroupQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Transporting the Main-Conjecture quotient across the carrier bridge  (S13-G, CHARIDEAL-CONJUNCT)

The capstone glue of the characteristic-ideal half of `thm:vandiver`: the Iwasawa Main Conjecture
isomorphism `𝒳⁺ ≅ Λ(𝒢⁺)/I` lives over the measure carrier `R = Λ(𝒢⁺) = PadicMeasure(𝒢⁺)`, while the
equivariant characteristic ideal `charIdealGroup` is defined over `S = IwasawaAlgebraGroup ℤ_p Δ`.
The carrier bridge `Φ : R ≃+* S` (`Iwasawa/CarrierBridge.lean`) transports the quotient presentation:
viewing `𝒳⁺` as an `S`-module along `Φ⁻¹`, `𝒳⁺ ≅ S/(Φ g)`, so by `charIdealGroup_of_quotientEquiv`,
`charIdealGroup 𝒳⁺ = Φ(I)`.

## Main declarations

* `Iwasawa.transportQuotientEquiv`: `Φ : R ≃+* S`, `X ≃ₗ[R] R/(g)` ⟹ `X ≃ₗ[S] S/(Φ g)` (with the
  `S`-module structure on `X` pulled back along `Φ⁻¹`).
-/

noncomputable section

namespace Iwasawa

variable {R S : Type*} [CommRing R] [CommRing S] (Φ : R ≃+* S)

/-- The image of a principal ideal under a ring isomorphism: `(Φ g) = Φ.map (g)`. -/
theorem map_span_singleton_ringEquiv (g : R) :
    Ideal.span {Φ g} = Ideal.map (Φ : R →+* S) (Ideal.span {g}) := by
  rw [Ideal.map_span, Set.image_singleton]; simp

/-- `Φ` carries the `R`-module structure of `R/(g)` to the `S`-module structure of `S/(Φ g)`:
`Φ.quotientEquiv` intertwines scaling by `r` on `R/(g)` with scaling by `Φ r` on `S/(Φ g)`. -/
theorem quotientEquiv_smul {g : R} (r : R) (z : R ⧸ Ideal.span {g}) :
    Ideal.quotientEquiv (Ideal.span {g}) (Ideal.span {Φ g}) Φ (map_span_singleton_ringEquiv Φ g)
        (r • z)
      = Φ r • Ideal.quotientEquiv (Ideal.span {g}) (Ideal.span {Φ g}) Φ
        (map_span_singleton_ringEquiv Φ g) z := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

/-- **Transport of a quotient presentation across a ring isomorphism.**  If `X ≃ₗ[R] R/(g)` and `X`
is given the `S`-module structure pulled back along `Φ⁻¹` (`Module.compHom`), then `X ≃ₗ[S] S/(Φ g)`. -/
def transportQuotientEquiv {X : Type*} [AddCommGroup X] [Module R X] {g : R}
    (e : X ≃ₗ[R] (R ⧸ Ideal.span {g})) :
    letI : Module S X := Module.compHom X (Φ.symm : S →+* R)
    X ≃ₗ[S] (S ⧸ Ideal.span {Φ g}) :=
  letI : Module S X := Module.compHom X (Φ.symm : S →+* R)
  let q : (R ⧸ Ideal.span {g}) ≃+* (S ⧸ Ideal.span {Φ g}) :=
    Ideal.quotientEquiv (Ideal.span {g}) (Ideal.span {Φ g}) Φ (map_span_singleton_ringEquiv Φ g)
  { toFun := fun x => q (e x)
    invFun := fun y => e.symm (q.symm y)
    left_inv := fun x => by simp
    right_inv := fun y => by simp
    map_add' := fun x y => by simp
    map_smul' := fun s x => by
      show q (e (Φ.symm s • x)) = s • q (e x)
      rw [map_smul, quotientEquiv_smul, Φ.apply_symm_apply] }

/-- **The characteristic-ideal half of `thm:vandiver`, via a carrier bridge.**  Given a Main-
Conjecture-style isomorphism `e : X ≃ₗ[R] R/(g₀)` over a source ring `R` and a carrier bridge
`Φ : R ≃+* IwasawaAlgebraGroup 𝒪 H`, viewing `X` as an `IwasawaAlgebraGroup`-module along `Φ⁻¹`
(`Module.compHom`) gives `charIdealGroup(X) = (Φ g₀)` — the bridged image of the principal ideal.
Composes `transportQuotientEquiv` with `charIdealGroup_of_quotientEquiv`.

In the Iwasawa Main Conjecture: `R = Λ(𝒢⁺) = PadicMeasure(𝒢⁺)`, `𝒪 = ℤ_p`, `H = Δ`, `X = 𝒳⁺_∞`,
`e` the MC isomorphism, `Φ` the carrier bridge `PadicMeasure.carrierBridge`, `g₀` the generator of
`zetaIdealPlus`. -/
theorem charIdealGroup_eq_of_carrierBridge {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsNoetherianRing 𝒪]
    {H : Type*} [CommGroup H] [Fintype H] [Invertible (Fintype.card H : 𝒪)]
    [Fintype (H →* 𝒪ˣ)] (hcomplete : ∑ ω : H →* 𝒪ˣ, isotypicIdempotent 𝒪 H ω = 1)
    {X : Type*} [AddCommGroup X] [Module R X]
    (Φ : R ≃+* IwasawaAlgebraGroup 𝒪 H) {g₀ : R}
    (e : X ≃ₗ[R] (R ⧸ Ideal.span {g₀})) :
    letI : Module (IwasawaAlgebraGroup 𝒪 H) X := Module.compHom X (Φ.symm : _ →+* R)
    ∀ [Module.Finite (IwasawaAlgebraGroup 𝒪 H) X]
      [Module.Finite (IwasawaAlgebraGroup 𝒪 H) (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {Φ g₀})]
      (hX : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) X),
      charIdealGroup 𝒪 H X hX = Ideal.span {Φ g₀} := by
  letI : Module (IwasawaAlgebraGroup 𝒪 H) X := Module.compHom X (Φ.symm : _ →+* R)
  intro _ _ hX
  exact charIdealGroup_of_quotientEquiv 𝒪 H hcomplete hX (transportQuotientEquiv Φ e)

end Iwasawa
