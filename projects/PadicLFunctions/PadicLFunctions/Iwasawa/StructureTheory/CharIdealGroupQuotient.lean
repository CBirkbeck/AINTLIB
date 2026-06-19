import PadicLFunctions.Iwasawa.StructureTheory.Isotypic
import PadicLFunctions.Iwasawa.StructureTheory.CharIdealQuotient

/-!
# Invariance and computation of `Ch_{Λ(𝒢)}`  (S13-S5, continued)

This file proves two structural facts about the equivariant characteristic ideal
`Ch_{Λ(𝒢)}` of `Iwasawa.charIdealGroup`:

* `Iwasawa.charIdealGroup_eq_of_linearEquiv`: `Ch_{Λ(𝒢)}` is a `Λ(𝒢)`-linear-isomorphism
  invariant.  This reduces to the per-component invariance of `Ch_Λ`
  (`charIdeal_eq_of_linearEquiv`, S13-S4): a `Λ(𝒢)`-linear iso commutes with the isotypic
  idempotents (they act by an algebra element), so it carries each isotypic component
  isomorphically onto the corresponding component of the target.

The companion reassembly `Ch_{Λ(𝒢)}(Λ(𝒢)/I) = I` (ticket `CHARIDEALGROUP-QUOT`) and the
`PadicMeasure(𝒢⁺) ≅ Λ(𝒢⁺)` carrier bridge (ticket `CARRIER-BRIDGE`) — the two remaining inputs to
the characteristic-ideal half of `thm:vandiver` — are tracked separately.
-/

noncomputable section

open DirectSum

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪] (H : Type*) [CommGroup H] [Fintype H]

local notation "Λ" => IwasawaAlgebra 𝒪

local notation "Λ𝒢" => IwasawaAlgebraGroup 𝒪 H

/-- A `Λ(𝒢)`-linear isomorphism `e : M ≃ M'` carries the `ω`-isotypic component of `M`
onto that of `M'`: `e(M^{(ω)}) = M'^{(ω)}`.  Because the isotypic component is the range of
multiplication by `e_ω ∈ Λ(𝒢)` and `e` (being `Λ(𝒢)`-linear) commutes with that
multiplication, mapping the range under `e` gives the range over `M'`. -/
theorem isotypicComponent_map_of_linearEquiv [Invertible (Fintype.card H : 𝒪)]
    (ω : H →* 𝒪ˣ) {M M' : Type*} [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [AddCommGroup M'] [Module (IwasawaAlgebraGroup 𝒪 H) M']
    (e : M ≃ₗ[IwasawaAlgebraGroup 𝒪 H] M') :
    Submodule.map (e : M →ₗ[IwasawaAlgebraGroup 𝒪 H] M') (isotypicComponent 𝒪 H ω M)
      = isotypicComponent 𝒪 H ω M' := by
  rw [isotypicComponent, isotypicComponent, ← LinearMap.range_comp]
  rw [show (e : M →ₗ[IwasawaAlgebraGroup 𝒪 H] M').comp
        (LinearMap.lsmul (IwasawaAlgebraGroup 𝒪 H) M (isotypicIdempotent 𝒪 H ω))
      = (LinearMap.lsmul (IwasawaAlgebraGroup 𝒪 H) M' (isotypicIdempotent 𝒪 H ω)).comp
        (e : M →ₗ[IwasawaAlgebraGroup 𝒪 H] M') from by
      ext x; simp [LinearMap.lsmul_apply]]
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr e.surjective, Submodule.map_top]

/-- A `Λ(𝒢)`-linear iso `e : M ≃ M'` restricts to a `Λ(𝒢)`-linear iso of `ω`-isotypic components
`M^{(ω)} ≃ M'^{(ω)}` (via `isotypicComponent_map_of_linearEquiv`). -/
def isotypicComponentEquivOfLinearEquiv [Invertible (Fintype.card H : 𝒪)]
    (ω : H →* 𝒪ˣ) {M M' : Type*} [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [AddCommGroup M'] [Module (IwasawaAlgebraGroup 𝒪 H) M']
    (e : M ≃ₗ[IwasawaAlgebraGroup 𝒪 H] M') :
    (isotypicComponent 𝒪 H ω M) ≃ₗ[IwasawaAlgebraGroup 𝒪 H] (isotypicComponent 𝒪 H ω M') :=
  (e.submoduleMap (isotypicComponent 𝒪 H ω M)).trans
    (LinearEquiv.ofEq _ _ (isotypicComponent_map_of_linearEquiv 𝒪 H ω e))

/-- The component iso `isotypicComponentEquivOfLinearEquiv`, with scalars restricted to the base ring
`Λ` on the `RestrictScalars` types — the `Λ`-linear form that `charIdeal` consumes. -/
def isotypicComponentRestrictScalarsEquiv [Invertible (Fintype.card H : 𝒪)]
    (ω : H →* 𝒪ˣ) {M M' : Type*} [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [AddCommGroup M'] [Module (IwasawaAlgebraGroup 𝒪 H) M']
    (e : M ≃ₗ[IwasawaAlgebraGroup 𝒪 H] M') :
    RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω M)
      ≃ₗ[IwasawaAlgebra 𝒪]
        RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω M') :=
  { ((RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω M)).trans
      (isotypicComponentEquivOfLinearEquiv 𝒪 H ω e).toAddEquiv).trans
      (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω M')).symm with
    map_smul' := fun (c : IwasawaAlgebra 𝒪)
        (x : RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
          ↥(isotypicComponent 𝒪 H ω M)) => by
      show (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
            ↥(isotypicComponent 𝒪 H ω M')).symm
          ((isotypicComponentEquivOfLinearEquiv 𝒪 H ω e)
            ((RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
                ↥(isotypicComponent 𝒪 H ω M))
              ((RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
                  ↥(isotypicComponent 𝒪 H ω M)).symm
                (algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) c •
                  (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
                    ↥(isotypicComponent 𝒪 H ω M)) x))))
        = c • (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
            ↥(isotypicComponent 𝒪 H ω M')).symm
            ((isotypicComponentEquivOfLinearEquiv 𝒪 H ω e)
              ((RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
                ↥(isotypicComponent 𝒪 H ω M)) x))
      rw [AddEquiv.apply_symm_apply, map_smul,
        RestrictScalars.addEquiv_symm_map_algebraMap_smul] }

/-- Per-`ω` invariance: `Ch_Λ(M^{(ω)}) = Ch_Λ(M'^{(ω)})` for a `Λ(𝒢)`-linear iso `e`
(`charIdeal_eq_of_linearEquiv` applied to the restricted component iso). -/
theorem charIdealComponent_eq_of_linearEquiv [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    (ω : H →* 𝒪ˣ) {M M' : Type*} [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M]
    [AddCommGroup M'] [Module (IwasawaAlgebraGroup 𝒪 H) M']
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M']
    (hM : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M)
    (hM' : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M')
    (e : M ≃ₗ[IwasawaAlgebraGroup 𝒪 H] M') :
    charIdealComponent 𝒪 H ω M hM = charIdealComponent 𝒪 H ω M' hM' := by
  letI instM : Module (IwasawaAlgebra 𝒪) (RestrictScalars (IwasawaAlgebra 𝒪)
      (IwasawaAlgebraGroup 𝒪 H) ↥(isotypicComponent 𝒪 H ω M)) := inferInstance
  letI instM' : Module (IwasawaAlgebra 𝒪) (RestrictScalars (IwasawaAlgebra 𝒪)
      (IwasawaAlgebraGroup 𝒪 H) ↥(isotypicComponent 𝒪 H ω M')) := inferInstance
  rw [charIdealComponent, charIdealComponent]
  exact @charIdeal_eq_of_linearEquiv 𝒪 _
    (RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) ↥(isotypicComponent 𝒪 H ω M))
    (RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) ↥(isotypicComponent 𝒪 H ω M'))
    _ instM (isotypicComponent_finite_Λ 𝒪 H ω M)
    _ instM' (isotypicComponent_finite_Λ 𝒪 H ω M') _ _
    (isotypicComponent_isTorsion_Λ 𝒪 H ω M hM)
    (isotypicComponent_isTorsion_Λ 𝒪 H ω M' hM')
    (isotypicComponentRestrictScalarsEquiv 𝒪 H ω e)

/-- **`Ch_{Λ(𝒢)}` is a `Λ(𝒢)`-linear-isomorphism invariant** (S13-S5).  A `Λ(𝒢)`-linear iso
carries each isotypic component isomorphically onto the corresponding component of the target
(`isotypicComponent_map_of_linearEquiv`), so the per-component characteristic ideals agree
(`charIdealComponent_eq_of_linearEquiv`, via `charIdeal_eq_of_linearEquiv`); the `⨅_ω comap` defining
`charIdealGroup` therefore agrees term by term. -/
theorem charIdealGroup_eq_of_linearEquiv [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    {M M' : Type*} [AddCommGroup M] [Module (IwasawaAlgebraGroup 𝒪 H) M]
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M]
    [AddCommGroup M'] [Module (IwasawaAlgebraGroup 𝒪 H) M']
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H) M']
    (hM : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M)
    (hM' : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H) M')
    (e : M ≃ₗ[IwasawaAlgebraGroup 𝒪 H] M') :
    charIdealGroup 𝒪 H M hM = charIdealGroup 𝒪 H M' hM' := by
  rw [charIdealGroup, charIdealGroup]
  exact iInf_congr fun ω => by rw [charIdealComponent_eq_of_linearEquiv 𝒪 H ω hM hM' e]

end Iwasawa
