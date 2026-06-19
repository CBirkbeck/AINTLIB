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

/-! ## The reassembly `Ch_{Λ(𝒢)}(Λ(𝒢)/I) = I` for principal `I` (ticket `CHARIDEALGROUP-QUOT`)

The ω-augmentation `φ_ω : Λ(𝒢) → Λ` is a retraction of `algebraMap : Λ → Λ(𝒢)` and sends the
idempotent `e_ω` to `1`.  Combined with `mul_isotypicIdempotent` (`s·e_ω = algebraMap(φ_ω s)·e_ω`)
these give a concrete `Λ`-linear iso of the ω-isotypic component of `Λ(𝒢)/(g)` with `Λ/(φ_ω g)`,
hence `Ch_Λ((Λ(𝒢)/(g))^{(ω)}) = (φ_ω g)` by `charIdeal_quotient`; the `⨅_ω comap φ_ω` then
reassembles to `(g)` via the orthogonal-idempotent decomposition `∑_ω e_ω = 1`. -/

/-- The ω-augmentation `φ_ω : Λ(𝒢) → Λ` is a **retraction** of the structure map `Λ → Λ(𝒢)`:
`φ_ω(algebraMap r) = r`.  (`algebraMap r = single 1 r` and `φ_ω(single 1 r) = r·ω(1) = r`.) -/
@[simp] theorem charAugmentation_algebraMap (ω : H →* 𝒪ˣ) (r : IwasawaAlgebra 𝒪) :
    charAugmentation 𝒪 H ω (algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) r) = r := by
  rw [show (algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) r)
        = MonoidAlgebra.single 1 r from by rw [MonoidAlgebra.coe_algebraMap]; simp,
    charAugmentation_single]
  simp

/-- The ω-augmentation sends its own idempotent to `1`: `φ_ω(e_ω) = 1` (RJW: `e_ω` projects onto
the ω-factor `Λ` of `Λ(𝒢) ≅ ∏_ω Λ`).  Each term `φ_ω(single a (N⁻¹ω(a)⁻¹)) = N⁻¹` and there are
`|H| = N` of them. -/
@[simp] theorem charAugmentation_isotypicIdempotent_self [Invertible (Fintype.card H : 𝒪)]
    (ω : H →* 𝒪ˣ) : charAugmentation 𝒪 H ω (isotypicIdempotent 𝒪 H ω) = 1 := by
  unfold isotypicIdempotent
  rw [map_sum]
  have hterm : ∀ a : H, charAugmentation 𝒪 H ω (MonoidAlgebra.single a
      (algebraMap 𝒪 (IwasawaAlgebra 𝒪) (⅟(Fintype.card H : 𝒪) * ((ω a)⁻¹ : 𝒪ˣ))))
      = algebraMap 𝒪 (IwasawaAlgebra 𝒪) (⅟(Fintype.card H : 𝒪)) := by
    intro a
    rw [charAugmentation_single, ← map_mul]
    congr 1
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← map_natCast (algebraMap 𝒪 (IwasawaAlgebra 𝒪)), ← map_mul,
    mul_invOf_self, map_one]

/-- The class `[e_ω]` of the idempotent lies in the ω-isotypic component of `Λ(𝒢)/(g)`. -/
theorem quotMk_isotypicIdempotent_mem [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (g : IwasawaAlgebraGroup 𝒪 H) :
    (Submodule.Quotient.mk (isotypicIdempotent 𝒪 H ω) :
        IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})
      ∈ isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) := by
  refine ⟨Submodule.Quotient.mk 1, ?_⟩
  rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

/-- The cyclic-generator map `r ↦ algebraMap(r)·[e_ω]` of the ω-isotypic component of `Λ(𝒢)/(g)`,
as a `Λ`-linear map `Λ → RestrictScalars Λ Λ(𝒢) ↥component`. -/
noncomputable def isotypicComponentGen [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (g : IwasawaAlgebraGroup 𝒪 H) :
    IwasawaAlgebra 𝒪 →ₗ[IwasawaAlgebra 𝒪]
      RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})) where
  toFun r := (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
      ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))).symm
    ((algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) r •
      (⟨_, quotMk_isotypicIdempotent_mem 𝒪 H ω g⟩ :
        ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})))))
  map_add' r s := by
    rw [← map_add]; congr 1; rw [map_add, add_smul]
  map_smul' r s := by
    rw [RingHom.id_apply, smul_eq_mul, map_mul, mul_smul,
      RestrictScalars.addEquiv_symm_map_algebraMap_smul]

/-- The underlying value of the cyclic-generator map: `(isotypicComponentGen ω g r : Λ(𝒢)/(g))
= algebraMap(r) • [e_ω] = [algebraMap(r)·e_ω]`. -/
theorem isotypicComponentGen_apply_coe [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (g : IwasawaAlgebraGroup 𝒪 H) (r : IwasawaAlgebra 𝒪) :
    ((RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})))
      (isotypicComponentGen 𝒪 H ω g r) : IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})
      = Submodule.Quotient.mk (algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) r
          * isotypicIdempotent 𝒪 H ω) := by
  rw [isotypicComponentGen]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.apply_symm_apply]
  rw [Submodule.coe_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul]

/-- The cyclic-generator map is **surjective** onto the ω-isotypic component: every element
`e_ω·[s]` of the component equals `algebraMap(φ_ω s)·[e_ω]` (using `[s]·e_ω = algebraMap(φ_ω s)·e_ω`
from `mul_isotypicIdempotent`), so `[s] ↦ φ_ω s` exhibits the preimage. -/
theorem isotypicComponentGen_surjective [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (g : IwasawaAlgebraGroup 𝒪 H) :
    Function.Surjective (isotypicComponentGen 𝒪 H ω g) := by
  intro z
  -- pull `z` back to the underlying submodule element, which is `e_ω • [s]` for some `s`
  set zc := (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
    ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))) z with hzc
  obtain ⟨s, hs⟩ : ∃ s : IwasawaAlgebraGroup 𝒪 H,
      isotypicIdempotent 𝒪 H ω • (Submodule.Quotient.mk s :
        IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) = (zc : IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) := by
    have hmem := zc.2
    simp only [isotypicComponent, LinearMap.mem_range] at hmem
    obtain ⟨m, hmeq⟩ := hmem
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    exact ⟨s, by rw [← LinearMap.lsmul_apply]; exact hmeq⟩
  refine ⟨charAugmentation 𝒪 H ω s, ?_⟩
  -- match via the `addEquiv` then the underlying submodule element
  apply (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
    ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))).injective
  apply Subtype.ext
  rw [isotypicComponentGen_apply_coe, ← hzc, ← hs]
  -- `[algebraMap(φ_ω s)·e_ω] = e_ω•[s]`:  `algebraMap(φ_ω s)·e_ω = s·e_ω = e_ω·s` then quotient
  rw [← mul_isotypicIdempotent, ← smul_eq_mul, Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm, ← smul_eq_mul,
    Submodule.Quotient.mk_smul]

/-- The **kernel** of the cyclic-generator map is `(φ_ω g)`.  `algebraMap(r)·e_ω ∈ (g)` iff
`g ∣ algebraMap(r)·e_ω`; the retraction `φ_ω` turns this into `φ_ω g ∣ r` (forward: apply `φ_ω`,
using `φ_ω(e_ω)=1`; backward: `algebraMap(φ_ω g)·e_ω = g·e_ω` makes `algebraMap(c·φ_ω g)·e_ω`
a multiple of `g`). -/
theorem isotypicComponentGen_ker [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (g : IwasawaAlgebraGroup 𝒪 H) :
    LinearMap.ker (isotypicComponentGen 𝒪 H ω g) = Ideal.span {charAugmentation 𝒪 H ω g} := by
  ext r
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
  -- membership in the kernel ⇔ the underlying class vanishes ⇔ `g ∣ algebraMap(r)·e_ω`
  have hzero : (isotypicComponentGen 𝒪 H ω g r = 0)
      ↔ ((RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
            ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})))
          (isotypicComponentGen 𝒪 H ω g r) : IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h
      refine (RestrictScalars.addEquiv (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) _).injective ?_
      rw [map_zero]
      exact Subtype.ext (by rw [ZeroMemClass.coe_zero]; exact h)
  rw [hzero, isotypicComponentGen_apply_coe, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_span_singleton]
  constructor
  · -- `g ∣ algebraMap(r)·e_ω` ⟹ `φ_ω g ∣ r`: apply `φ_ω`
    rintro ⟨t, ht⟩
    refine ⟨charAugmentation 𝒪 H ω t, ?_⟩
    have := congrArg (charAugmentation 𝒪 H ω) ht
    rw [map_mul, charAugmentation_algebraMap, charAugmentation_isotypicIdempotent_self, mul_one,
      map_mul] at this
    rw [this, mul_comm]
  · -- `φ_ω g ∣ r` ⟹ `g ∣ algebraMap(r)·e_ω`:  `algebraMap(φ_ω g)·e_ω = g·e_ω`
    rintro ⟨c, rfl⟩
    refine ⟨algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) c
      * isotypicIdempotent 𝒪 H ω, ?_⟩
    rw [map_mul]
    rw [show algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (charAugmentation 𝒪 H ω g)
          * algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) c * isotypicIdempotent 𝒪 H ω
        = algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) c
          * (algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (charAugmentation 𝒪 H ω g)
            * isotypicIdempotent 𝒪 H ω) from by ring,
      ← mul_isotypicIdempotent]
    ring

/-- The **ω-isotypic component of `Λ(𝒢)/(g)` is `Λ`-linearly isomorphic to `Λ/(φ_ω g)`**: the
cyclic-generator map `r ↦ algebraMap(r)·[e_ω]` is a `Λ`-linear surjection
(`isotypicComponentGen_surjective`) with kernel `(φ_ω g)` (`isotypicComponentGen_ker`). -/
noncomputable def isotypicComponentQuotientEquiv [Invertible (Fintype.card H : 𝒪)] (ω : H →* 𝒪ˣ)
    (g : IwasawaAlgebraGroup 𝒪 H) :
    (IwasawaAlgebra 𝒪 ⧸ Ideal.span {charAugmentation 𝒪 H ω g}) ≃ₗ[IwasawaAlgebra 𝒪]
      RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})) :=
  letI instC : Module (IwasawaAlgebra 𝒪) (RestrictScalars (IwasawaAlgebra 𝒪)
      (IwasawaAlgebraGroup 𝒪 H)
      ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))) :=
    RestrictScalars.module _ _ _
  (Submodule.quotEquivOfEq _ _ (isotypicComponentGen_ker 𝒪 H ω g).symm).trans
    (@LinearMap.quotKerEquivOfSurjective (IwasawaAlgebra 𝒪) _ _ _ _ _ _ instC
      (isotypicComponentGen 𝒪 H ω g) (isotypicComponentGen_surjective 𝒪 H ω g))

/-- **The ω-component of `Ch_{Λ(𝒢)}` for a principal quotient** (when `φ_ω g ≠ 0`):
`Ch_Λ((Λ(𝒢)/(g))^{(ω)}) = (φ_ω g)`.  Transport `charIdeal_quotient` (`Ch_Λ(Λ/(φ_ω g)) = (φ_ω g)`)
across the component iso `isotypicComponentQuotientEquiv`. -/
theorem charIdealComponent_quotient [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    (ω : H →* 𝒪ˣ) {g : IwasawaAlgebraGroup 𝒪 H} (hg : charAugmentation 𝒪 H ω g ≠ 0)
    (htor : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H)
      (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})) :
    charIdealComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) htor
      = Ideal.span {charAugmentation 𝒪 H ω g} := by
  letI instC : Module (IwasawaAlgebra 𝒪) (RestrictScalars (IwasawaAlgebra 𝒪)
      (IwasawaAlgebraGroup 𝒪 H)
      ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))) :=
    RestrictScalars.module _ _ _
  -- torsion of `Λ/(φ_ω g)` (input to `charIdeal_quotient` and `charIdeal_eq_of_linearEquiv`)
  have htorQ : Module.IsTorsion (IwasawaAlgebra 𝒪)
      (IwasawaAlgebra 𝒪 ⧸ Ideal.span {charAugmentation 𝒪 H ω g}) :=
    isTorsion_quotient_span hg
  haveI instFinC : Module.Finite (IwasawaAlgebra 𝒪)
      (RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))) :=
    isotypicComponent_finite_Λ 𝒪 H ω _
  rw [charIdealComponent, ← charIdeal_quotient hg htorQ]
  exact (@charIdeal_eq_of_linearEquiv 𝒪 _
    (IwasawaAlgebra 𝒪 ⧸ Ideal.span {charAugmentation 𝒪 H ω g})
    (RestrictScalars (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
      ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})))
    _ _ _ _ instC instFinC _ _ htorQ
    (isotypicComponent_isTorsion_Λ 𝒪 H ω _ htor)
    (isotypicComponentQuotientEquiv 𝒪 H ω g)).symm

/-- **Orthogonal decomposition of a ring element** along the complete idempotents:
`x = ∑_ω algebraMap(φ_ω x)·e_ω`.  (`x = x·∑_ω e_ω = ∑_ω x·e_ω` and `x·e_ω = algebraMap(φ_ω x)·e_ω`
by `mul_isotypicIdempotent`.) -/
theorem sum_algebraMap_charAugmentation_mul_isotypicIdempotent [Invertible (Fintype.card H : 𝒪)]
    [Fintype (H →* 𝒪ˣ)] (hcomplete : ∑ ω : H →* 𝒪ˣ, isotypicIdempotent 𝒪 H ω = 1)
    (x : IwasawaAlgebraGroup 𝒪 H) :
    ∑ ω : H →* 𝒪ˣ, algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H)
        (charAugmentation 𝒪 H ω x) * isotypicIdempotent 𝒪 H ω = x := by
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
    (mul_isotypicIdempotent 𝒪 H ω x).symm, ← Finset.mul_sum, hcomplete, mul_one]

/-- **The `⨅_ω comap φ_ω` reassembly** (crux of `CHARIDEALGROUP-QUOT`):
`⨅_ω φ_ω⁻¹(φ_ω g) = (g)` in `Λ(𝒢)`.  Forward (`⊇`): `φ_ω g ∈ (φ_ω g)` for each `ω`.  Backward
(`⊆`): if `φ_ω x = a_ω·φ_ω g` for all `ω`, then `x = ∑_ω algebraMap(φ_ω x)·e_ω
= ∑_ω g·algebraMap(a_ω)·e_ω = g·∑_ω algebraMap(a_ω)·e_ω ∈ (g)`, using `g·e_ω
= algebraMap(φ_ω g)·e_ω` and the complete decomposition `∑_ω e_ω = 1`. -/
theorem iInf_comap_charAugmentation_span_singleton [Invertible (Fintype.card H : 𝒪)]
    [Fintype (H →* 𝒪ˣ)] (hcomplete : ∑ ω : H →* 𝒪ˣ, isotypicIdempotent 𝒪 H ω = 1)
    (g : IwasawaAlgebraGroup 𝒪 H) :
    ⨅ ω : H →* 𝒪ˣ, Ideal.comap (charAugmentation 𝒪 H ω)
        (Ideal.span {charAugmentation 𝒪 H ω g}) = Ideal.span {g} := by
  apply le_antisymm
  · -- `⊆`:  membership in every `comap φ_ω (φ_ω g)` gives `φ_ω g ∣ φ_ω x`, reassembled to `g ∣ x`
    intro x hx
    rw [Submodule.mem_iInf] at hx
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
    -- choose `a_ω` with `φ_ω x = φ_ω g · a_ω`
    choose a ha using hx
    rw [Ideal.mem_span_singleton]
    refine ⟨∑ ω : H →* 𝒪ˣ, algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (a ω)
      * isotypicIdempotent 𝒪 H ω, ?_⟩
    rw [Finset.mul_sum,
      ← sum_algebraMap_charAugmentation_mul_isotypicIdempotent 𝒪 H hcomplete x]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [ha ω, map_mul]
    -- `algebraMap(φ_ω g · a_ω)·e_ω = g·(algebraMap(a_ω)·e_ω)`
    rw [show algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (charAugmentation 𝒪 H ω g)
          * algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (a ω)
          * isotypicIdempotent 𝒪 H ω
        = algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (a ω)
          * (algebraMap (IwasawaAlgebra 𝒪) (IwasawaAlgebraGroup 𝒪 H) (charAugmentation 𝒪 H ω g)
            * isotypicIdempotent 𝒪 H ω) from by ring,
      ← mul_isotypicIdempotent]
    ring
  · -- `⊇`:  `g ∈ comap φ_ω (φ_ω g)` for every `ω`, since `φ_ω g ∈ (φ_ω g)`
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_iInf]
    intro ω
    rw [Ideal.mem_comap]
    exact Ideal.mem_span_singleton_self _

/-- For a **torsion** principal quotient `Λ(𝒢)/(g)`, each augmentation `φ_ω g` is nonzero.
The ω-component is torsion over `Λ` (`isotypicComponent_isTorsion_Λ`), and the component iso
`isotypicComponentQuotientEquiv` makes `Λ/(φ_ω g)` torsion over the domain `Λ`; were `φ_ω g = 0`
this would say the free module `Λ` is torsion, impossible. -/
theorem charAugmentation_ne_zero_of_isTorsion [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    (ω : H →* 𝒪ˣ) {g : IwasawaAlgebraGroup 𝒪 H}
    (htor : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H)
      (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})) :
    charAugmentation 𝒪 H ω g ≠ 0 := by
  intro hzero
  -- the ω-component is torsion over `Λ`; transport along the iso to `Λ/(φ_ω g) = Λ/⊥ ≅ Λ`
  have htorC := isotypicComponent_isTorsion_Λ 𝒪 H ω _ htor
  letI instC : Module (IwasawaAlgebra 𝒪) (RestrictScalars (IwasawaAlgebra 𝒪)
      (IwasawaAlgebraGroup 𝒪 H)
      ↥(isotypicComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}))) :=
    RestrictScalars.module _ _ _
  -- pull the torsion back to `Λ/(φ_ω g)`
  have htorQ : Module.IsTorsion (IwasawaAlgebra 𝒪)
      (IwasawaAlgebra 𝒪 ⧸ Ideal.span {charAugmentation 𝒪 H ω g}) := by
    intro y
    obtain ⟨s, hs⟩ := htorC (x := (isotypicComponentQuotientEquiv 𝒪 H ω g) y)
    refine ⟨s, ?_⟩
    apply (isotypicComponentQuotientEquiv 𝒪 H ω g).injective
    rw [map_zero, ← hs, Submonoid.smul_def, Submonoid.smul_def, map_smul]
  -- but `Λ/(φ_ω g) = Λ/(0) = Λ` is not torsion (the class of `1` survives every nonzerodivisor)
  rw [hzero] at htorQ
  obtain ⟨s, hs⟩ := htorQ (x := Submodule.Quotient.mk 1)
  rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
    Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, zero_dvd_iff] at hs
  exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2) hs

/-- **`Ch_{Λ(𝒢)}(Λ(𝒢)/I) = I` for a principal ideal `I = (g)`** (ticket `CHARIDEALGROUP-QUOT`,
the reassembly half of `thm:vandiver` part (ii)).  Unfolding `Ch_{Λ(𝒢)} = ⨅_ω φ_ω⁻¹(Ch_Λ((·)^{(ω)}))`:
each ω-component contributes `Ch_Λ((Λ(𝒢)/(g))^{(ω)}) = (φ_ω g)` (`charIdealComponent_quotient`,
with `φ_ω g ≠ 0` from `charAugmentation_ne_zero_of_isTorsion`), and the
`⨅_ω φ_ω⁻¹(φ_ω g)` reassembles to `(g)` via the orthogonal-idempotent decomposition
`∑_ω e_ω = 1` (`iInf_comap_charAugmentation_span_singleton`).

The hypotheses `[Fintype (H →* 𝒪ˣ)]` and `hcomplete : ∑_ω e_ω = 1` are RJW's *"after extending `L`
by the values of `ω`"* (TeX 3665), exactly as for `isInternal_isotypicComponent`. -/
theorem charIdealGroup_quotient [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Invertible (Fintype.card H : 𝒪)] [IsNoetherianRing 𝒪]
    [Fintype (H →* 𝒪ˣ)] (hcomplete : ∑ ω : H →* 𝒪ˣ, isotypicIdempotent 𝒪 H ω = 1)
    {g : IwasawaAlgebraGroup 𝒪 H}
    [Module.Finite (IwasawaAlgebraGroup 𝒪 H)
      (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})]
    (htor : Module.IsTorsion (IwasawaAlgebraGroup 𝒪 H)
      (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g})) :
    charIdealGroup 𝒪 H (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) htor = Ideal.span {g} := by
  rw [charIdealGroup]
  have heq : ⨅ ω : H →* 𝒪ˣ, Ideal.comap (charAugmentation 𝒪 H ω)
        (charIdealComponent 𝒪 H ω (IwasawaAlgebraGroup 𝒪 H ⧸ Ideal.span {g}) htor)
      = ⨅ ω : H →* 𝒪ˣ, Ideal.comap (charAugmentation 𝒪 H ω)
          (Ideal.span {charAugmentation 𝒪 H ω g}) :=
    iInf_congr fun ω => by
      rw [charIdealComponent_quotient 𝒪 H ω
        (charAugmentation_ne_zero_of_isTorsion 𝒪 H ω htor) htor]
  rw [heq, iInf_comap_charAugmentation_span_singleton 𝒪 H hcomplete g]

end Iwasawa
