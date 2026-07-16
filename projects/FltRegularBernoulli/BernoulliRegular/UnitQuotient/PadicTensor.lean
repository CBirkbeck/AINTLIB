module

public import BernoulliRegular.UnitQuotient.ModPReduction
public import BernoulliRegular.UnitQuotient.GlobalUnitDimension
public import BernoulliRegular.Idempotents
public import BernoulliRegular.Characters
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# T-Q1-EIGEN: p-adic tensor of the cyclotomic unit free part

For the rank-one Pollaczek specialisation (T-Q1-RANK-ONE), the eigenspace
identification `e_χ(C ⊗ Λ) ≃ Λ` for `Λ = ℤ_[p]` requires the p-adic
tensor of the cyclotomic unit free part. This file ships the basic
infrastructure:

* `CyclotomicUnitFreePartPadic K p := CyclotomicUnitFreePart K ⊗[ℤ] ℤ_[p]`
  — the p-adic completion of the free part.
* The natural ℤ_[p]-module structure (via the right tensor factor).
* Δ-action lifted from `cyclotomicUnitFreePartLinearEquiv` via `LinearMap.rTensor`.

The Δ-character idempotent decomposition and the rank-1 eigenspace identification
at `χ = ω^i` are built on top of this.

## References

* Washington, *Introduction to Cyclotomic Fields* §5.1 (cyclotomic unit
  log embeddings + Dirichlet).
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The **p-adic tensor of the cyclotomic unit free part**:
`ℤ_[p] ⊗_ℤ (𝓞 K)ˣ / torsion`, the natural lift to characteristic-zero
p-adic-coefficient module. The ℤ_[p] is on the **left** so the natural
`Module ℤ_[p]` structure follows from `TensorProduct.leftModule`. -/
abbrev CyclotomicUnitFreePartPadic : Type _ :=
  TensorProduct ℤ ℤ_[p] (CyclotomicUnitFreePart K)

/-- The natural `Module ℤ_[p]` structure on `CyclotomicUnitFreePartPadic`,
via left-tensoring. -/
example : Module ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) := inferInstance

/-- **`CyclotomicUnitFreePartPadic K` is free over `ℤ_[p]`**: tensor of free
ℤ_[p]-module ℤ_[p] with free ℤ-module FreePart K. -/
instance : Module.Free ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) := by
  classical
  exact Module.Free.tensor

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **The Padic free part has finrank `NumberField.Units.rank K` over `ℤ_[p]`**.
Direct from `Module.finrank_baseChange` plus the existing `cyclotomicUnitFreePart_finrank`. -/
@[simp]
theorem cyclotomicUnitFreePartPadic_finrank :
    Module.finrank ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) =
      NumberField.Units.rank K := by
  change Module.finrank ℤ_[p] (ℤ_[p] ⊗[ℤ] CyclotomicUnitFreePart K) =
    NumberField.Units.rank K
  rw [Module.finrank_baseChange]
  exact cyclotomicUnitFreePart_finrank K

/-- **The Padic free part is finitely generated over `ℤ_[p]`**: tensor of
finitely-generated ℤ-module FreePart K with ℤ_[p]. -/
instance : Module.Finite ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) :=
  Module.Finite.of_basis (Module.Free.chooseBasis ℤ_[p]
    (CyclotomicUnitFreePartPadic (p := p) K))

/-- **The Padic free part is Noetherian as a `ℤ_[p]`-module**, since it's
finitely generated over the Noetherian ring `ℤ_[p]`. -/
instance : IsNoetherian ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) :=
  isNoetherian_of_isNoetherianRing_of_finite _ _


/-- The natural ℤ-linear inclusion `CyclotomicUnitFreePart K → CyclotomicUnitFreePartPadic K`
sending `v` to `1 ⊗ₜ v`, packaged via `TensorProduct.mk`. -/
def cyclotomicUnitFreePartToPadic :
    CyclotomicUnitFreePart K →ₗ[ℤ] CyclotomicUnitFreePartPadic (p := p) K :=
  TensorProduct.mk ℤ ℤ_[p] (CyclotomicUnitFreePart K) (1 : ℤ_[p])

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem cyclotomicUnitFreePartToPadic_apply (v : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartToPadic (p := p) K v = (1 : ℤ_[p]) ⊗ₜ[ℤ] v :=
  rfl

/-- The **Δ-action on the p-adic tensor**: lifted from
`cyclotomicUnitFreePartLinearEquiv` via `LinearEquiv.baseChange` to `ℤ_[p]`.
This action is `ℤ_[p]`-linear (not just `ℤ`-linear). -/
noncomputable def cyclotomicUnitFreePartPadicLinearEquiv
    (a : CyclotomicUnitDelta p) :
    CyclotomicUnitFreePartPadic (p := p) K ≃ₗ[ℤ_[p]]
      CyclotomicUnitFreePartPadic (p := p) K :=
  (cyclotomicUnitFreePartLinearEquiv (p := p) K a).baseChange ℤ ℤ_[p]
    (CyclotomicUnitFreePart K) (CyclotomicUnitFreePart K)

@[simp]
theorem cyclotomicUnitFreePartPadicLinearEquiv_apply_tmul
    (a : CyclotomicUnitDelta p) (z : ℤ_[p]) (v : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartPadicLinearEquiv (p := p) K a (z ⊗ₜ[ℤ] v) =
      z ⊗ₜ[ℤ] cyclotomicUnitFreePartLinearEquiv (p := p) K a v := by
  simp only [cyclotomicUnitFreePartPadicLinearEquiv]
  rw [LinearEquiv.baseChange_tmul]

/-- **Teichmüller character on `CyclotomicUnitDelta p`** (= `(ZMod p)ˣ`),
valued in `ℤ_[p]`. Powers `ω^k` give the character spectrum needed for
the eigenspace decomposition. -/
noncomputable def cyclotomicOmegaPadicChar (k : ℕ) :
    MulChar (CyclotomicUnitDelta p) ℤ_[p] where
  toFun a := teichmuller p ((a : (ZMod p)ˣ) : ZMod p) ^ k
  map_one' := by
    change teichmuller p (((1 : (ZMod p)ˣ) : ZMod p)) ^ k = 1
    rw [Units.val_one, map_one, one_pow]
  map_mul' a b := by
    change teichmuller p (((a * b : (ZMod p)ˣ) : ZMod p)) ^ k =
      teichmuller p ((a : (ZMod p)ˣ) : ZMod p) ^ k *
        teichmuller p ((b : (ZMod p)ˣ) : ZMod p) ^ k
    rw [Units.val_mul, map_mul, mul_pow]
  map_nonunit' a ha := absurd (Group.isUnit a) ha

@[simp]
theorem cyclotomicOmegaPadicChar_apply (k : ℕ) (a : CyclotomicUnitDelta p) :
    cyclotomicOmegaPadicChar (p := p) k a =
      teichmuller p ((a : (ZMod p)ˣ) : ZMod p) ^ k :=
  rfl

/-- **Padic Δ-action as MonoidHom**: bundles
`cyclotomicUnitFreePartPadicLinearEquiv` into a MonoidHom from
`CyclotomicUnitDelta p` to ℤ_[p]-linear-equiv automorphisms. -/
noncomputable def cyclotomicUnitFreePartPadicDeltaAction :
    CyclotomicUnitDelta p →*
      (CyclotomicUnitFreePartPadic (p := p) K ≃ₗ[ℤ_[p]]
        CyclotomicUnitFreePartPadic (p := p) K) where
  toFun a := cyclotomicUnitFreePartPadicLinearEquiv (p := p) K a
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    ext x
    change cyclotomicUnitFreePartPadicLinearEquiv (p := p) K 1 ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) =
      (1 : ℤ_[p]) ⊗ₜ[ℤ] x
    rw [cyclotomicUnitFreePartPadicLinearEquiv_apply_tmul]
    rw [show (cyclotomicUnitFreePartLinearEquiv (p := p) K 1) x = x from
      LinearEquiv.ext_iff.mp (cyclotomicUnitFreePartDeltaAction (p := p) K).map_one x]
  map_mul' a b := by
    apply LinearEquiv.toLinearMap_injective
    ext x
    change cyclotomicUnitFreePartPadicLinearEquiv (p := p) K (a * b) ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) =
      cyclotomicUnitFreePartPadicLinearEquiv (p := p) K a
        (cyclotomicUnitFreePartPadicLinearEquiv (p := p) K b ((1 : ℤ_[p]) ⊗ₜ[ℤ] x))
    rw [cyclotomicUnitFreePartPadicLinearEquiv_apply_tmul,
      cyclotomicUnitFreePartPadicLinearEquiv_apply_tmul,
      cyclotomicUnitFreePartPadicLinearEquiv_apply_tmul]
    congr 1
    -- (cyclotomicUnitFreePartLinearEquiv K (a*b)) x =
    -- (cyclotomicUnitFreePartLinearEquiv K a) ((cyclotomicUnitFreePartLinearEquiv K b) x)
    have h := (cyclotomicUnitFreePartDeltaAction (p := p) K).map_mul a b
    exact LinearEquiv.ext_iff.mp h x

/-- The **Padic Δ-representation**: packages the action as a standard
`ℤ_[p]`-linear representation of `CyclotomicUnitDelta p`. -/
noncomputable def cyclotomicUnitFreePartPadicRepresentation :
    Representation ℤ_[p] (CyclotomicUnitDelta p)
      (CyclotomicUnitFreePartPadic (p := p) K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (cyclotomicUnitFreePartPadicDeltaAction (p := p) K)

@[simp]
theorem cyclotomicUnitFreePartPadicRepresentation_apply
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicRepresentation (p := p) K a x =
      cyclotomicUnitFreePartPadicLinearEquiv (p := p) K a x :=
  rfl

/-- **Invertibility of `(p-1)` in ℤ_[p]**: needed for the character idempotent
since `Fintype.card (CyclotomicUnitDelta p) = p - 1`. The unit-status follows
from `Nat.Coprime p (p-1)` ⟹ `‖((p-1 : ℕ) : ℤ_[p])‖ = 1`. -/
noncomputable instance instInvertibleCardCyclotomicUnitDeltaPadic :
    Invertible ((Fintype.card (CyclotomicUnitDelta p) : ℤ_[p])) := by
  have hp_prime := (Fact.out : p.Prime)
  have h_card : (Fintype.card (CyclotomicUnitDelta p) : ℕ) = p - 1 := by
    change Fintype.card (ZMod p)ˣ = p - 1
    rw [ZMod.card_units]
  -- `(p - 1 : ℤ_[p])` is a unit since gcd(p, p-1) = 1 (consecutive integers).
  have h_coprime : p.Coprime (p - 1) := by
    have hp_two_le : 2 ≤ p := hp_prime.two_le
    rw [Nat.coprime_self_sub_right (by omega)]
    -- Goal: Coprime p 1.
    exact Nat.coprime_one_right p
  have h_norm : ‖((p - 1 : ℕ) : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr h_coprime
  have h_unit : IsUnit (((p - 1 : ℕ) : ℤ_[p])) :=
    PadicInt.isUnit_iff.mpr h_norm
  -- Cast and rewrite via h_card.
  have : Invertible (((p - 1 : ℕ) : ℤ_[p])) := h_unit.invertible
  rw [show (Fintype.card (CyclotomicUnitDelta p) : ℤ_[p]) = ((p - 1 : ℕ) : ℤ_[p]) from by
    rw [h_card]]
  infer_instance

/-- The **character idempotent projector** acting on
`CyclotomicUnitFreePartPadic`. For a `MulChar (CyclotomicUnitDelta p) ℤ_[p]`,
projects onto the `χ`-eigenspace via `(1/|Δ|) Σ_a χ(a)⁻¹ • σ_a`. -/
noncomputable def cyclotomicUnitFreePartPadicCharacterProjector
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    Module.End ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) := by
  classical
  exact (cyclotomicUnitFreePartPadicRepresentation (p := p) K).asAlgebraHom
    (charIdempotent (G := CyclotomicUnitDelta p) (R := ℤ_[p]) χ)

/-- The **χ-eigenspace** in `CyclotomicUnitFreePartPadic`: elements `x`
with `σ_a • x = χ(a) • x` for all `a ∈ Δ`. -/
def cyclotomicUnitFreePartPadicCharacterEigenspace
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    Submodule ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) where
  carrier := {x | ∀ a, cyclotomicUnitFreePartPadicLinearEquiv (p := p) K a x = χ a • x}
  zero_mem' := by
    intro a
    rw [map_zero, smul_zero]
  add_mem' hx hy := by
    intro a
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    rw [map_smul, hx a, smul_smul, smul_smul, mul_comm]

/-- **Padic χ-eigenspace is finitely generated over `ℤ_[p]`**: as a
submodule of the Noetherian PadicFreePart. -/
instance instFinitePadicCharacterEigenspace
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    Module.Finite ℤ_[p]
      (cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ) :=
  Module.Finite.of_injective
    (cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ).subtype
    (Submodule.injective_subtype _)

/-- **Padic χ-eigenspace is free over `ℤ_[p]`**: submodule of free PID-module. -/
noncomputable instance instFreePadicCharacterEigenspace
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    Module.Free ℤ_[p]
      (cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ) := by
  classical
  have b := Module.Free.chooseBasis ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K)
  exact Module.Free.of_basis
    (Submodule.basisOfPid b
      (cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ)).2

/-- The **mod-p class map as ℤ-linear**: a manually-constructed
`→ₗ[ℤ]` version of `cyclotomicUnitFreePartModPClass`, avoiding the
`Int.instSemiring` vs `Int.instCommSemiring.toSemiring` typeclass issue
in `AddMonoidHom.toIntLinearMap`. -/
def cyclotomicUnitFreePartModPClassLinear :
    CyclotomicUnitFreePart K →ₗ[ℤ] CyclotomicUnitFreePartModP (p := p) K where
  toFun := cyclotomicUnitFreePartModPClass (p := p) K
  map_add' := (cyclotomicUnitFreePartModPClass (p := p) K).map_add
  map_smul' c v := by
    change cyclotomicUnitFreePartModPClass (p := p) K (c • v) =
      c • cyclotomicUnitFreePartModPClass (p := p) K v
    exact (cyclotomicUnitFreePartModPClass (p := p) K).map_zsmul c v

/-- The **mod-p reduction tensor**
`ℤ_[p] ⊗[ℤ] FreePart K →ₗ[ℤ] ℤ_[p] ⊗[ℤ] FreePartModP K`,
sending `z ⊗ v ↦ z ⊗ [v]` (mod-p class on the right factor only). -/
noncomputable def cyclotomicUnitFreePartPadicReduceRight :
    CyclotomicUnitFreePartPadic (p := p) K →ₗ[ℤ]
      TensorProduct ℤ ℤ_[p] (CyclotomicUnitFreePartModP (p := p) K) :=
  LinearMap.lTensor ℤ_[p] (cyclotomicUnitFreePartModPClassLinear (p := p) K)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem cyclotomicUnitFreePartPadicReduceRight_tmul
    (z : ℤ_[p]) (v : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartPadicReduceRight (p := p) K (z ⊗ₜ[ℤ] v) =
      z ⊗ₜ[ℤ] cyclotomicUnitFreePartModPClass (p := p) K v :=
  rfl

/-- The **`PadicInt.toZMod` as a ℤ-linear map**: ring hom cast to ℤ-linear,
avoiding the `Int.instSemiring` typeclass mismatch. -/
noncomputable def padicToZModLinear :
    ℤ_[p] →ₗ[ℤ] ZMod p where
  toFun := PadicInt.toZMod (p := p)
  map_add' := PadicInt.toZMod.map_add
  map_smul' c z := by
    change PadicInt.toZMod (c • z) = c • PadicInt.toZMod z
    rw [zsmul_eq_mul, map_mul, map_intCast, zsmul_eq_mul]

/-- The **left-factor mod-p reduction** `ℤ_[p] ⊗[ℤ] M →ₗ[ℤ] ZMod p ⊗[ℤ] M`,
sending `z ⊗ m ↦ (z.toZMod) ⊗ m`. -/
noncomputable def cyclotomicUnitFreePartPadicReduceLeft :
    TensorProduct ℤ ℤ_[p] (CyclotomicUnitFreePartModP (p := p) K) →ₗ[ℤ]
      TensorProduct ℤ (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) :=
  LinearMap.rTensor (CyclotomicUnitFreePartModP (p := p) K)
    (padicToZModLinear (p := p))

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem cyclotomicUnitFreePartPadicReduceLeft_tmul
    (z : ℤ_[p]) (m : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartPadicReduceLeft (p := p) K (z ⊗ₜ[ℤ] m) =
      ((PadicInt.toZMod (p := p)) z) ⊗ₜ[ℤ] m :=
  rfl

/-- The **scalar smul on tensor**: `ZMod p ⊗[ℤ] FreePartModP →ₗ[ℤ] FreePartModP`,
sending `c ⊗ x ↦ c • x` (using the `Module (ZMod p) FreePartModP` structure). -/
noncomputable def cyclotomicUnitFreePartModPSmulFromTensor :
    TensorProduct ℤ (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) →ₗ[ℤ]
      CyclotomicUnitFreePartModP (p := p) K :=
  TensorProduct.lift {
    toFun := fun c ↦ {
      toFun := fun x ↦ c • x
      map_add' := fun x y ↦ smul_add c x y
      map_smul' := fun n x ↦ by
        change c • ((n : ℤ) • x) = (n : ℤ) • (c • x)
        rw [smul_comm]
    }
    map_add' := fun c d ↦ by
      apply LinearMap.ext
      intro x
      change (c + d) • x = c • x + d • x
      exact add_smul c d x
    map_smul' := fun n c ↦ by
      apply LinearMap.ext
      intro x
      change ((n : ℤ) • c) • x = (n : ℤ) • (c • x)
      rw [smul_assoc]
  }

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem cyclotomicUnitFreePartModPSmulFromTensor_tmul
    (c : ZMod p) (m : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPSmulFromTensor (p := p) K (c ⊗ₜ[ℤ] m) = c • m :=
  rfl

/-- The **full mod-p reduction map** `ℤ_[p] ⊗ FreePart K →ₗ[ℤ] FreePartModP K`,
composed of the right-factor reduction (`v ↦ [v]`), left-factor reduction
(`z ↦ z.toZMod`), and scalar smul. Sends `z ⊗ v ↦ z.toZMod • [v]`. -/
noncomputable def cyclotomicUnitFreePartPadicReduceModP :
    CyclotomicUnitFreePartPadic (p := p) K →ₗ[ℤ]
      CyclotomicUnitFreePartModP (p := p) K :=
  (cyclotomicUnitFreePartModPSmulFromTensor (p := p) K).comp <|
    (cyclotomicUnitFreePartPadicReduceLeft (p := p) K).comp <|
      cyclotomicUnitFreePartPadicReduceRight (p := p) K

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
@[simp]
theorem cyclotomicUnitFreePartPadicReduceModP_tmul
    (z : ℤ_[p]) (v : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K (z ⊗ₜ[ℤ] v) =
      ((PadicInt.toZMod (p := p)) z) •
        cyclotomicUnitFreePartModPClass (p := p) K v :=
  rfl

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Reduction sends `1 ⊗ v ↦ [v]`** (the natural inclusion-reduction). -/
@[simp]
theorem cyclotomicUnitFreePartPadicReduceModP_one_tmul
    (v : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K
      (cyclotomicUnitFreePartToPadic (p := p) K v) =
      cyclotomicUnitFreePartModPClass (p := p) K v := by
  rw [cyclotomicUnitFreePartToPadic_apply, cyclotomicUnitFreePartPadicReduceModP_tmul]
  rw [show (PadicInt.toZMod (p := p) (1 : ℤ_[p])) = (1 : ZMod p) from map_one _,
    one_smul]

/-- **Padic-to-modP character reduction**: applying `PadicInt.toZMod` to
`cyclotomicOmegaPadicChar k a` gives `((a : ZMod p))^k` (which matches
the project's mod-p `cyclotomicOmegaChar k`). -/
@[simp]
theorem cyclotomicOmegaPadicChar_toZMod (k : ℕ) (a : CyclotomicUnitDelta p) :
    PadicInt.toZMod (cyclotomicOmegaPadicChar (p := p) k a) =
      ((a : (ZMod p)ˣ) : ZMod p) ^ k := by
  rw [cyclotomicOmegaPadicChar_apply, map_pow, toZMod_teichmuller]

/-- **Padic-character to ZMod-character reduction**: composing a
`MulChar Δ ℤ_[p]` with `PadicInt.toZMod` gives a `MulChar Δ (ZMod p)`. -/
noncomputable def MulChar.padicToZMod (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    MulChar (CyclotomicUnitDelta p) (ZMod p) :=
  χ.ringHomComp (PadicInt.toZMod (p := p))

@[simp]
theorem MulChar.padicToZMod_apply
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) (a : CyclotomicUnitDelta p) :
    MulChar.padicToZMod (p := p) χ a = PadicInt.toZMod (χ a) :=
  rfl

/-- **The mod-p eigenspace** at character χ : MulChar Δ (ZMod p), bundled
as a Submodule of `CyclotomicUnitFreePartModP K`. -/
def cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local
    (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    Submodule (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) where
  carrier := {x | ∀ a, cyclotomicUnitFreePartModPLinearEquiv (p := p) K a x = χ a • x}
  zero_mem' := by intro a; rw [map_zero, smul_zero]
  add_mem' hx hy := by intro a; rw [map_add, hx a, hy a, smul_add]
  smul_mem' c x hx := by
    intro a
    change cyclotomicUnitFreePartModPLinearEquiv (p := p) K a (c • x) = χ a • c • x
    rw [show cyclotomicUnitFreePartModPLinearEquiv (p := p) K a (c • x) =
      c • cyclotomicUnitFreePartModPLinearEquiv (p := p) K a x from
      ZMod.map_smul
        (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).toAddEquiv.toAddMonoidHom c x]
    rw [hx, smul_smul, smul_smul, mul_comm]

/-- **The local mod-p eigenspace coincides with the project standard one**.
Both define the same Submodule of W; the actions used in the carrier
condition (`cyclotomicUnitFreePartModPLinearEquiv` versus the ZMod-bundled
`cyclotomicUnitFreePartModPDeltaActionZMod`) refer to the same underlying
map on elements. -/
theorem cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local_eq
    (χ : MulChar (CyclotomicUnitDelta p) (ZMod p)) :
    cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local (p := p) K χ =
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace (p := p) K χ := by
  ext x
  rfl

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **The reduction map sends `c • x` to `c.toZMod • reduce(x)`** for the
`Module ℤ_[p]` smul on the source. This is the key compatibility
showing the reduction map intertwines the ℤ_[p]-action (on Padic) with
the ZMod p-action (on FreePartModP) via `PadicInt.toZMod`. -/
theorem cyclotomicUnitFreePartPadicReduceModP_smul_compat
    (c : ℤ_[p]) (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K (c • x) =
      (PadicInt.toZMod (p := p) c) •
        cyclotomicUnitFreePartPadicReduceModP (p := p) K x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z v =>
    rw [TensorProduct.smul_tmul']
    rw [cyclotomicUnitFreePartPadicReduceModP_tmul]
    rw [cyclotomicUnitFreePartPadicReduceModP_tmul]
    rw [show PadicInt.toZMod (p := p) (c • z) = PadicInt.toZMod (p := p) (c * z) from by
      rw [smul_eq_mul]]
    rw [map_mul, smul_smul]
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, smul_add]

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **The reduction map is surjective**: every element of `FreePartModP`
arises as the image of some Padic element (specifically `1 ⊗ v` for any
representative `v` of the class). -/
theorem cyclotomicUnitFreePartPadicReduceModP_surjective :
    Function.Surjective (cyclotomicUnitFreePartPadicReduceModP (p := p) K) := by
  intro y
  -- Since FreePartModP = FreePart / pFreePart, every y has a representative v ∈ FreePart.
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  -- We can lift to 1 ⊗ v ∈ PadicFreePart.
  refine ⟨cyclotomicUnitFreePartToPadic (p := p) K v, ?_⟩
  -- reduce(1 ⊗ v) = [v] = mkQ v.
  rw [cyclotomicUnitFreePartPadicReduceModP_one_tmul]
  rfl

/-- **Reduction map intertwines Δ-action**: the reduction sends the Padic
Δ-action to the mod-p free part Δ-action. Direct calculation on
generators `z ⊗ v`: both sides reduce to `z.toZMod • [σ_a • v]`. -/
theorem cyclotomicUnitFreePartPadicReduceModP_equivariant
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K
        (cyclotomicUnitFreePartPadicLinearEquiv (p := p) K a x) =
      cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        (cyclotomicUnitFreePartPadicReduceModP (p := p) K x) := by
  -- Induct on `x` (TensorProduct.induction_on).
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
  | tmul z v =>
    rw [cyclotomicUnitFreePartPadicLinearEquiv_apply_tmul]
    rw [cyclotomicUnitFreePartPadicReduceModP_tmul]
    rw [cyclotomicUnitFreePartPadicReduceModP_tmul]
    -- Goal: z.toZMod • [σ_a • v] = modPLinearEquiv K a (z.toZMod • [v]).
    -- Use modP-action ZMod-linearity: modP K a (c • x) = c • modP K a x.
    rw [show cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        ((PadicInt.toZMod (p := p)) z •
          cyclotomicUnitFreePartModPClass (p := p) K v) =
      (PadicInt.toZMod (p := p)) z •
        cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
          (cyclotomicUnitFreePartModPClass (p := p) K v) from
      ZMod.map_smul (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).toAddEquiv.toAddMonoidHom
        ((PadicInt.toZMod (p := p)) z) (cyclotomicUnitFreePartModPClass (p := p) K v)]
    rw [show cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        (cyclotomicUnitFreePartModPClass (p := p) K v) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (cyclotomicUnitFreePartLinearEquiv (p := p) K a v) from
      cyclotomicUnitFreePartModPLinearEquiv_apply_class (p := p) (K := K) a v]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- **Reduction sends Padic eigenspace into ZMod-eigenspace**: if x is in
the Padic ω^χ-eigenspace, then `reduce(x)` is in the mod-p
`MulChar.padicToZMod χ`-eigenspace. -/
theorem cyclotomicUnitFreePartPadicReduceModP_eigenspace_mem
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    {x : CyclotomicUnitFreePartPadic (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K x ∈
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local (p := p) K
        (MulChar.padicToZMod (p := p) χ) := by
  intro a
  rw [← cyclotomicUnitFreePartPadicReduceModP_equivariant (p := p) K a x]
  rw [hx a, cyclotomicUnitFreePartPadicReduceModP_smul_compat]
  rfl

/-- **Padic character projector image lies in the Padic eigenspace**.
For `χ : MulChar Δ ℤ_[p]` and any `x` in the Padic free part, the
projection `e_χ(x) := ρ.asAlgebraHom(charIdempotent χ) x` satisfies the
eigenspace condition `σ_a(e_χ x) = χ(a) • e_χ x` for every `a ∈ Δ`.

The proof composes:

* `Representation.asAlgebraHom_single_one`: the Δ-action `σ_a` is the
  representation evaluated at the single-basis element `single a 1`.
* `single_mul_charIdempotent`: in the group algebra, `single a 1 * ε_χ = χ(a) • ε_χ`.
* `map_mul` and `map_smul`: the representation is an algebra and module
  homomorphism. -/
theorem cyclotomicUnitFreePartPadicCharacterProjector_mem_eigenspace
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicCharacterProjector (p := p) K χ x ∈
      cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ := by
  classical
  have hp_prime := (Fact.out : p.Prime)
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have : HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (CyclotomicUnitDelta p)) :=
    exponent_zmod_units (p := p) ▸ inferInstance
  have : Invertible (2 : ℤ_[p]) := by
    have h_cop : p.Coprime 2 :=
      (Nat.Prime.coprime_iff_not_dvd hp_prime).mpr (fun h ↦ by
        have := Nat.le_of_dvd (by norm_num) h; omega)
    have h_norm : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr h_cop
    have h_unit : IsUnit (((2 : ℕ) : ℤ_[p])) := PadicInt.isUnit_iff.mpr h_norm
    have h_eq : ((2 : ℕ) : ℤ_[p]) = (2 : ℤ_[p]) := by norm_cast
    exact (h_eq ▸ h_unit).invertible
  intro a
  set ρ := cyclotomicUnitFreePartPadicRepresentation (p := p) K with hρ_def
  -- Goal: σ_a (e_χ x) = χ(a) • e_χ x where σ_a = padicLinearEquiv K a and
  -- e_χ x = ρ.asAlgebraHom (charIdempotent χ) x.
  change ρ a (ρ.asAlgebraHom (charIdempotent (G := CyclotomicUnitDelta p) (R := ℤ_[p]) χ) x) =
    χ a • ρ.asAlgebraHom (charIdempotent (G := CyclotomicUnitDelta p) (R := ℤ_[p]) χ) x
  rw [← Representation.asAlgebraHom_single_one ρ a]
  rw [← Module.End.mul_apply, ← map_mul]
  rw [single_mul_charIdempotent (G := CyclotomicUnitDelta p) (R := ℤ_[p]) a χ]
  rw [map_smul]
  rfl

/-- **Reduction commutes with `Representation.asAlgebraHom (single g 1)`**:
on basis monomial elements of the group algebra, the Padic representation
followed by reduction equals reduction followed by the mod-p representation.
This is exactly the Δ-equivariance, repackaged through `asAlgebraHom_single_one`. -/
theorem cyclotomicUnitFreePartPadicReduceModP_asAlgebraHom_single_compat
    (g : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K
        ((cyclotomicUnitFreePartPadicRepresentation (p := p) K).asAlgebraHom
          (MonoidAlgebra.single g (1 : ℤ_[p])) x) =
      (cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K).asAlgebraHom
        (MonoidAlgebra.single g (1 : ZMod p))
        (cyclotomicUnitFreePartPadicReduceModP (p := p) K x) := by
  rw [Representation.asAlgebraHom_single_one]
  rw [Representation.asAlgebraHom_single_one]
  exact cyclotomicUnitFreePartPadicReduceModP_equivariant (p := p) K g x

/-- **Reduction commutes with `χ • asAlgebraHom (single g 1)`**: scalar
extension of the singleton compat. Useful as the per-summand step in the
projector compatibility. -/
theorem cyclotomicUnitFreePartPadicReduceModP_asAlgebraHom_smul_single_compat
    (g : CyclotomicUnitDelta p) (c : ℤ_[p])
    (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K
        (c • (cyclotomicUnitFreePartPadicRepresentation (p := p) K).asAlgebraHom
          (MonoidAlgebra.single g (1 : ℤ_[p])) x) =
      (PadicInt.toZMod (p := p) c) •
        (cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K).asAlgebraHom
          (MonoidAlgebra.single g (1 : ZMod p))
          (cyclotomicUnitFreePartPadicReduceModP (p := p) K x) := by
  rw [cyclotomicUnitFreePartPadicReduceModP_smul_compat]
  rw [cyclotomicUnitFreePartPadicReduceModP_asAlgebraHom_single_compat]

/-- **Reduction commutes with the sum `Σ_g χ(g) • asAlgebraHom (single g⁻¹ 1)`**:
the linear extension of the per-summand compat to the full sum that defines
the character idempotent. -/
theorem cyclotomicUnitFreePartPadicReduceModP_asAlgebraHom_sum_compat
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K
        (∑ g : CyclotomicUnitDelta p, χ g •
          (cyclotomicUnitFreePartPadicRepresentation (p := p) K).asAlgebraHom
            (MonoidAlgebra.single g⁻¹ (1 : ℤ_[p])) x) =
      ∑ g : CyclotomicUnitDelta p, (MulChar.padicToZMod (p := p) χ) g •
        (cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K).asAlgebraHom
          (MonoidAlgebra.single g⁻¹ (1 : ZMod p))
          (cyclotomicUnitFreePartPadicReduceModP (p := p) K x) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  exact cyclotomicUnitFreePartPadicReduceModP_asAlgebraHom_smul_single_compat
    (p := p) K g⁻¹ (χ g) x

/-- **Generic API**: equal elements in a monoid have equal `⅟`-values, regardless
of which `Invertible` instance is used to compute them. Closes the dependent-instance
plumbing that arises whenever `Invertible` instances on equal-but-not-defeq elements
have to be identified. -/
theorem invOf_eq_invOf_of_eq {R : Type*} [Monoid R] {a b : R}
    (h : a = b) (ia : Invertible a) (ib : Invertible b) :
    @Invertible.invOf R _ _ a ia = @Invertible.invOf R _ _ b ib := by
  subst h
  exact congrArg (fun i ↦ @Invertible.invOf R _ _ a i) (Subsingleton.elim ia ib)

/-- **Scalar identity for the cardinality inverse** under `PadicInt.toZMod`:
the image of `⅟(|Δ| : ℤ_[p])` in `ZMod p` equals `⅟(|Δ| : ZMod p)`. The proof
uses `map_invOf` to push the ring hom past the inverse, then closes the
remaining `Invertible`-instance plumbing via the generic `invOf_eq_invOf_of_eq`
helper (`PadicInt.toZMod` of the natural-number cast equals the natural-number
cast on the target). -/
theorem cyclotomicUnitDeltaCard_invOf_toZMod (hp_gt_two : 2 < p) :
    PadicInt.toZMod (p := p) (⅟((Fintype.card (CyclotomicUnitDelta p) : ℤ_[p]))) =
      letI := cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
      ⅟((Fintype.card (CyclotomicUnitDelta p) : ZMod p)) := by
  let iZ : Invertible ((Fintype.card (CyclotomicUnitDelta p) : ZMod p)) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  let iM : Invertible (PadicInt.toZMod (p := p)
      ((Fintype.card (CyclotomicUnitDelta p) : ℤ_[p]))) :=
    Invertible.map (PadicInt.toZMod (p := p))
      ((Fintype.card (CyclotomicUnitDelta p) : ℤ_[p]))
  rw [map_invOf]
  refine invOf_eq_invOf_of_eq ?_ iM iZ
  exact map_natCast (PadicInt.toZMod (p := p)) _

/-- **Full projector compatibility**: the mod-p reduction map intertwines the
Padic character idempotent at `χ` with the mod-p character idempotent at
`χ.padicToZMod`. This is the gating step for surjectivity of the Padic
χ-eigenspace onto the mod-p χ-eigenspace, which feeds the rank-1 result. -/
theorem cyclotomicUnitFreePartPadicReduceModP_projector_compat
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    (x : CyclotomicUnitFreePartPadic (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K
        (cyclotomicUnitFreePartPadicCharacterProjector (p := p) K χ x) =
      cyclotomicUnitFreePartModPDeltaCharacterProjector (p := p) K hp_gt_two
        (MulChar.padicToZMod (p := p) χ)
        (cyclotomicUnitFreePartPadicReduceModP (p := p) K x) := by
  classical
  let : Invertible ((Fintype.card (CyclotomicUnitDelta p) : ZMod p)) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  simp only [cyclotomicUnitFreePartPadicCharacterProjector,
    cyclotomicUnitFreePartModPDeltaCharacterProjector]
  rw [charIdempotent_def, charIdempotent_def, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply,
      cyclotomicUnitFreePartPadicReduceModP_smul_compat]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [cyclotomicUnitDeltaCard_invOf_toZMod (p := p) hp_gt_two]
  congr 1
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [MulChar.padicToZMod_apply]
  exact cyclotomicUnitFreePartPadicReduceModP_asAlgebraHom_smul_single_compat
    (p := p) K g⁻¹ (χ g) x

/-- **Eigenspace surjectivity**: every element of the mod-p `(χ mod p)`-eigenspace
arises as the reduction of some element of the Padic χ-eigenspace. The lift is
constructed by taking any global preimage `z` and projecting it via the Padic
character idempotent: the projector lands in the Padic eigenspace, and the
projector compatibility brings the reduction back to the original `y` (using
identity-on-eigenspace for the mod-p projector). -/
theorem cyclotomicUnitFreePartPadicReduceModP_eigenspace_surjective
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    {y : CyclotomicUnitFreePartModP (p := p) K}
    (hy : y ∈ cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local (p := p) K
              (MulChar.padicToZMod (p := p) χ)) :
    ∃ x : CyclotomicUnitFreePartPadic (p := p) K,
      x ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ ∧
        cyclotomicUnitFreePartPadicReduceModP (p := p) K x = y := by
  classical
  let : Invertible ((Fintype.card (CyclotomicUnitDelta p) : ZMod p)) :=
    cyclotomicUnitDeltaCardInvertibleZMod (p := p) hp_gt_two
  obtain ⟨z, hz⟩ := cyclotomicUnitFreePartPadicReduceModP_surjective (p := p) K y
  refine ⟨cyclotomicUnitFreePartPadicCharacterProjector (p := p) K χ z,
    cyclotomicUnitFreePartPadicCharacterProjector_mem_eigenspace
      (p := p) K hp_gt_two χ z, ?_⟩
  rw [cyclotomicUnitFreePartPadicReduceModP_projector_compat (p := p) K hp_gt_two χ z, hz]
  simp only [cyclotomicUnitFreePartModPDeltaCharacterProjector]
  exact characterProjector_apply_of_mem_eigenspace
    (cyclotomicUnitFreePartModPDeltaRepresentation (p := p) K)
    (MulChar.padicToZMod (p := p) χ) hy

/-- The submodule `p • V_p`: image of multiplication by the prime `p` on the
Padic free part. This is the kernel of the natural mod-`p` reduction map. -/
abbrev cyclotomicUnitFreePartPadic_pSmulSubmodule :
    Submodule ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) :=
  LinearMap.range
    (LinearMap.lsmul ℤ_[p] (CyclotomicUnitFreePartPadic (p := p) K) ((p : ℕ) : ℤ_[p]))

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Reduction kills `p • V_p`**: any element of `p • V_p` reduces to zero. -/
theorem cyclotomicUnitFreePartPadicReduceModP_pSmul_eq_zero
    {x : CyclotomicUnitFreePartPadic (p := p) K}
    (hx : x ∈ cyclotomicUnitFreePartPadic_pSmulSubmodule (p := p) K) :
    cyclotomicUnitFreePartPadicReduceModP (p := p) K x = 0 := by
  obtain ⟨y, hy⟩ := hx
  simp only [LinearMap.lsmul_apply] at hy
  rw [← hy, cyclotomicUnitFreePartPadicReduceModP_smul_compat]
  rw [show PadicInt.toZMod (p := p) ((p : ℕ) : ℤ_[p]) = 0 from by
    rw [map_natCast]; exact ZMod.natCast_self p]
  exact zero_smul _ _

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Kernel of red equals `p • V_p`**: the reverse inclusion via basis transport.
For `x ∈ V_p` with `red x = 0`, expand `x = Σ c_i • (1 ⊗ e_i)` in the Padic
basis (lifted from V_int's Dirichlet basis). The reduction sends the basis
elements term-by-term to W's mod-p basis, so `red x = Σ (c_i mod p) • bW i`.
Vanishing of this in W combined with basis independence gives `c_i.toZMod = 0`,
hence each `c_i ∈ (p)`, so `c_i = p · c_i'` for some `c_i'`. Summing gives
`x = p • Σ c_i' • (1 ⊗ e_i)`. -/
theorem cyclotomicUnitFreePartPadicReduceModP_ker_eq_pSmul
    {x : CyclotomicUnitFreePartPadic (p := p) K}
    (hx : cyclotomicUnitFreePartPadicReduceModP (p := p) K x = 0) :
    ∃ y : CyclotomicUnitFreePartPadic (p := p) K, ((p : ℕ) : ℤ_[p]) • y = x := by
  classical
  set bV : Module.Basis (Fin (NumberField.Units.rank K)) ℤ_[p]
      (CyclotomicUnitFreePartPadic (p := p) K) :=
    Algebra.TensorProduct.basis ℤ_[p] (cyclotomicUnitFreeBasis K) with hbV_def
  set bW : Module.Basis (Fin (NumberField.Units.rank K)) (ZMod p)
      (CyclotomicUnitFreePartModP (p := p) K) :=
    cyclotomicUnitFreePartModPBasis (p := p) K with hbW_def
  -- Step 1: red sends bV i to bW i.
  have h_red_basis : ∀ i, cyclotomicUnitFreePartPadicReduceModP (p := p) K (bV i) = bW i := by
    intro i
    have h_bV : bV i = (1 : ℤ_[p]) ⊗ₜ[ℤ] cyclotomicUnitFreeBasis K i :=
      Algebra.TensorProduct.basis_apply (cyclotomicUnitFreeBasis K) i
    rw [h_bV, cyclotomicUnitFreePartPadicReduceModP_tmul]
    rw [show PadicInt.toZMod (p := p) (1 : ℤ_[p]) = 1 from map_one _, one_smul]
    rw [hbW_def, cyclotomicUnitFreePartModPBasis, ModN.basis_apply_eq_mkQ]
  -- Step 2: red x = Σ (bV.repr x i).toZMod • bW i.
  have h_red_x :
      cyclotomicUnitFreePartPadicReduceModP (p := p) K x =
        ∑ i, ((PadicInt.toZMod (p := p)) (bV.repr x i)) • bW i := by
    conv_lhs => rw [← bV.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cyclotomicUnitFreePartPadicReduceModP_smul_compat, h_red_basis]
  -- Step 3: each coefficient is zero, hence each bV.repr x i ∈ (p).
  rw [h_red_x] at hx
  have h_coord_zero : ∀ i, (PadicInt.toZMod (p := p)) (bV.repr x i) = 0 := by
    intro i
    have h_repr_eq : bW.repr (∑ j, ((PadicInt.toZMod (p := p)) (bV.repr x j)) • bW j) i =
        (PadicInt.toZMod (p := p)) (bV.repr x i) := by
      rw [map_sum, Finset.sum_apply']
      simp [Finsupp.single_apply, Finset.sum_ite_eq']
    have : bW.repr (0 : CyclotomicUnitFreePartModP (p := p) K) i = 0 := by simp
    rw [← hx, h_repr_eq] at this
    exact this
  -- Step 4: lift each coefficient: bV.repr x i = p * c_i for some c_i.
  have h_lift : ∀ i, ∃ c : ℤ_[p], bV.repr x i = ((p : ℕ) : ℤ_[p]) * c := by
    intro i
    have h_mem : bV.repr x i ∈ Ideal.span {((p : ℕ) : ℤ_[p])} := by
      rw [show ((p : ℕ) : ℤ_[p]) = ((p : ℤ_[p])) from by norm_cast]
      rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact h_coord_zero i
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h_mem
    exact ⟨c, hc.symm.trans (mul_comm _ _)⟩
  choose c hc using h_lift
  -- Step 5: y = Σ c_i • bV i; check p • y = x.
  refine ⟨∑ i, c i • bV i, ?_⟩
  rw [Finset.smul_sum]
  conv_rhs => rw [← bV.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul, ← hc i]

/-- **Eigenspace kernel**: for `x` in the Padic χ-eigenspace with `red x = 0`,
the lift `y ∈ V_p` from the global kernel lemma can be projected into the
eigenspace via `e_χ`, giving `y' ∈ V_p^χ` with `p • y' = x`. The proof uses
that the projector is identity on its own eigenspace and ℤ_p-linear. -/
theorem cyclotomicUnitFreePartPadicReduceModP_eigenspace_ker_eq_pSmul
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    {x : CyclotomicUnitFreePartPadic (p := p) K}
    (hx_eigen : x ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ)
    (hx_red : cyclotomicUnitFreePartPadicReduceModP (p := p) K x = 0) :
    ∃ y ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ,
      ((p : ℕ) : ℤ_[p]) • y = x := by
  classical
  have hp_prime := (Fact.out : p.Prime)
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have : HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (CyclotomicUnitDelta p)) :=
    exponent_zmod_units (p := p) ▸ inferInstance
  have : Invertible (2 : ℤ_[p]) := by
    have h_cop : p.Coprime 2 :=
      (Nat.Prime.coprime_iff_not_dvd hp_prime).mpr (fun h ↦ by
        have := Nat.le_of_dvd (by norm_num) h; omega)
    have h_norm : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr h_cop
    have h_unit : IsUnit (((2 : ℕ) : ℤ_[p])) := PadicInt.isUnit_iff.mpr h_norm
    have h_eq : ((2 : ℕ) : ℤ_[p]) = (2 : ℤ_[p]) := by norm_cast
    exact (h_eq ▸ h_unit).invertible
  obtain ⟨y, hy⟩ := cyclotomicUnitFreePartPadicReduceModP_ker_eq_pSmul (p := p) K hx_red
  refine ⟨cyclotomicUnitFreePartPadicCharacterProjector (p := p) K χ y,
    cyclotomicUnitFreePartPadicCharacterProjector_mem_eigenspace
      (p := p) K hp_gt_two χ y, ?_⟩
  have hex : cyclotomicUnitFreePartPadicCharacterProjector (p := p) K χ x = x :=
    characterProjector_apply_of_mem_eigenspace
      (cyclotomicUnitFreePartPadicRepresentation (p := p) K) χ hx_eigen
  rw [← hex, ← hy, map_smul]

/-- **Eigenspace `not p-divisible` ↔ `red ≠ 0`**: a clean bridge form
of the eigenspace kernel equality. For `x` in the Padic χ-eigenspace,
`x` has no Padic preimage `y ∈ V_p^χ` with `p • y = x` (i.e., `x` is
"not p-divisible inside the eigenspace") iff `red x ≠ 0` in
`W^(χ mod p)` (i.e., the mod-p image is non-zero). -/
theorem cyclotomicUnitFreePartPadic_eigenspace_not_pdivisible_iff
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p])
    {x : CyclotomicUnitFreePartPadic (p := p) K}
    (hx_eigen : x ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ) :
    (¬ ∃ y ∈ cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ,
        ((p : ℕ) : ℤ_[p]) • y = x) ↔
    cyclotomicUnitFreePartPadicReduceModP (p := p) K x ≠ 0 := by
  constructor
  · intro h_not_pdiv h_red
    exact h_not_pdiv <| cyclotomicUnitFreePartPadicReduceModP_eigenspace_ker_eq_pSmul
      (p := p) K hp_gt_two χ hx_eigen h_red
  · intro h_red ⟨y, _, hy⟩
    apply h_red
    rw [← hy, cyclotomicUnitFreePartPadicReduceModP_smul_compat]
    rw [show PadicInt.toZMod (p := p) ((p : ℕ) : ℤ_[p]) = 0 from by
      rw [map_natCast]; exact ZMod.natCast_self p]
    exact zero_smul _ _

/-- **Restricted reduction map V_p^χ →+ W^(χ mod p)**: the AddMonoidHom
form of the just-shipped eigenspace surjectivity + Δ-invariance. -/
def cyclotomicUnitFreePartPadicReduceModP_eigenspaceHom
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ →+
      cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local (p := p) K
        (MulChar.padicToZMod (p := p) χ) where
  toFun := fun ⟨x, hx⟩ ↦
    ⟨cyclotomicUnitFreePartPadicReduceModP (p := p) K x,
      cyclotomicUnitFreePartPadicReduceModP_eigenspace_mem (p := p) K χ hx⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' := fun x y ↦ Subtype.ext (map_add _ x.1 y.1)

/-- **Eigenspace reduction is surjective**: the AddMonoidHom form. -/
theorem cyclotomicUnitFreePartPadicReduceModP_eigenspaceHom_surjective
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    Function.Surjective
      (cyclotomicUnitFreePartPadicReduceModP_eigenspaceHom (p := p) K χ) := by
  intro y
  obtain ⟨w, hw_eigen, hw_red⟩ :=
    cyclotomicUnitFreePartPadicReduceModP_eigenspace_surjective
      (p := p) K hp_gt_two χ y.2
  exact ⟨⟨w, hw_eigen⟩, Subtype.ext hw_red⟩

/-- **Helper**: for a basis `bV` and a function `f` on the index set,
the basis representation of `Σ i, f i • bV i` at index `j` is `f j`.
A direct consequence of `Basis.equivFun` being the inverse of basis-sum. -/
private theorem basis_repr_sum_smul {ι R M : Type*} [Fintype ι] [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis ι R M)
    (f : ι → R) (j : ι) :
    (b.repr (∑ i, f i • b i)) j = f j := by
  classical
  rw [show ∑ i, f i • b i = b.equivFun.symm f from
        (Module.Basis.equivFun_symm_apply b f).symm]
  change (b.equivFun (b.equivFun.symm f)) j = f j
  rw [LinearEquiv.apply_symm_apply]

/-- **Rank equality**: `finrank ℤ_[p] V_p^χ = finrank (ZMod p) W^(χ mod p)`.

Proof via basis transport. Pick a Padic basis `bV` of `V_p^χ` indexed by
`ι := ChooseBasisIndex ℤ_[p] V_p^χ`. Define `bW_cand i := red(bV i) ∈ W^(χ mod p)`.

1. `bW_cand` spans `W^(χ mod p)`: any `w ∈ W^(χ mod p)` lifts to `v ∈ V_p^χ`
   with `red v = w`; expand `v = Σ c_i • bV i` to get `w = Σ (c_i mod p) •
   bW_cand i`.

2. `bW_cand` is linearly independent: a relation `Σ c_j • bW_cand j = 0`
   lifts to `ĉ_j ∈ ℤ_[p]` via val cast; the lifted combination
   `Σ ĉ_j • bV j` lives in `V_p^χ ∩ ker red`, which by the eigenspace
   kernel equality equals `p • V_p^χ`. So `Σ ĉ_j • bV j = p • Σ d_j • bV j`,
   and basis injectivity on `bV` forces `ĉ_j = p · d_j`, hence `c_j = ĉ_j mod p = 0`.

Combined: `bW_cand` is a `(ZMod p)`-basis of cardinality
`finrank ℤ_[p] V_p^χ`, so `finrank (ZMod p) W^(χ mod p) = finrank ℤ_[p] V_p^χ`. -/
theorem cyclotomicUnitFreePartPadicCharacterEigenspace_finrank
    (hp_gt_two : 2 < p)
    (χ : MulChar (CyclotomicUnitDelta p) ℤ_[p]) :
    Module.finrank ℤ_[p]
        (cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ) =
      Module.finrank (ZMod p)
        (cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local (p := p) K
          (MulChar.padicToZMod (p := p) χ)) := by
  classical
  set V_p_chi := cyclotomicUnitFreePartPadicCharacterEigenspace (p := p) K χ
  set W_chi_modp := cyclotomicUnitFreePartModPDeltaCharacterEigenspace_local (p := p) K
    (MulChar.padicToZMod (p := p) χ)
  set bV := Module.Free.chooseBasis ℤ_[p] V_p_chi
  set red_eig := cyclotomicUnitFreePartPadicReduceModP_eigenspaceHom (p := p) K χ
  set bW_cand : Module.Free.ChooseBasisIndex ℤ_[p] V_p_chi → W_chi_modp :=
    fun i ↦ red_eig (bV i)
  -- Helper: red_eig of `c • bV i` (in V_p_chi) equals `c.toZMod • bW_cand i` (in W_chi_modp).
  have h_red_smul : ∀ (c : ℤ_[p]) (i : Module.Free.ChooseBasisIndex ℤ_[p] V_p_chi),
      red_eig (c • bV i) = (PadicInt.toZMod (p := p) c) • bW_cand i := by
    intro c i
    apply Subtype.ext
    change cyclotomicUnitFreePartPadicReduceModP (p := p) K (c • (bV i : _)) =
      (PadicInt.toZMod (p := p) c) • (red_eig (bV i) : _)
    exact cyclotomicUnitFreePartPadicReduceModP_smul_compat (p := p) K _ _
  -- Step 1: bW_cand spans W_chi_modp.
  have h_span : Submodule.span (ZMod p) (Set.range bW_cand) = ⊤ := by
    refine eq_top_iff.mpr (fun w _ ↦ ?_)
    obtain ⟨v, hv⟩ := cyclotomicUnitFreePartPadicReduceModP_eigenspaceHom_surjective
      (p := p) K hp_gt_two χ w
    rw [← hv, ← bV.linearCombination_repr v,
      Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [h_red_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- Step 2: bW_cand is linearly independent over ZMod p.
  have h_indep : LinearIndependent (ZMod p) bW_cand := by
    rw [Fintype.linearIndependent_iff]
    intro g h_sum i
    -- Lift g to ĝ via val cast.
    set ĝ : Module.Free.ChooseBasisIndex ℤ_[p] V_p_chi → ℤ_[p] :=
      fun j ↦ ((g j).val : ℤ_[p])
    have h_cast : ∀ j, PadicInt.toZMod (p := p) (ĝ j) = g j := fun j ↦ by
      change PadicInt.toZMod (p := p) (((g j).val : ℕ) : ℤ_[p]) = g j
      rw [map_natCast, ZMod.natCast_zmod_val]
    -- v := Σ ĝ j • bV j ∈ V_p^χ.
    set v : V_p_chi := ∑ j, ĝ j • bV j
    -- red_eig v = Σ g j • bW_cand j = 0.
    have h_red_v : red_eig v = 0 := by
      rw [show v = ∑ j, ĝ j • bV j from rfl, map_sum]
      have h_each : ∀ j ∈ (Finset.univ :
          Finset (Module.Free.ChooseBasisIndex ℤ_[p] V_p_chi)),
          red_eig (ĝ j • bV j) = (g j) • bW_cand j := fun j _ ↦ by
        rw [h_red_smul, h_cast]
      rw [Finset.sum_congr rfl h_each, h_sum]
    -- v lies in the global kernel; lift via eigenspace kernel.
    have h_v_red : cyclotomicUnitFreePartPadicReduceModP (p := p) K
        (v : CyclotomicUnitFreePartPadic (p := p) K) = 0 := by
      have hh := congrArg Subtype.val h_red_v
      change (red_eig v : CyclotomicUnitFreePartModP (p := p) K) = (0 : _)
      exact hh
    obtain ⟨y, y_eig, hy_smul⟩ :=
      cyclotomicUnitFreePartPadicReduceModP_eigenspace_ker_eq_pSmul
        (p := p) K hp_gt_two χ v.2 h_v_red
    set yV : V_p_chi := ⟨y, y_eig⟩
    -- v = p • yV (as elements of V_p_chi).
    have h_v_eq : v = ((p : ℕ) : ℤ_[p]) • yV := by
      apply Subtype.ext
      change (v : CyclotomicUnitFreePartPadic (p := p) K) =
        ((p : ℕ) : ℤ_[p]) • (y : CyclotomicUnitFreePartPadic (p := p) K)
      exact hy_smul.symm
    -- Apply bV.repr: ĝ i = (bV.repr v) i = (bV.repr (p • yV)) i = p · (bV.repr yV) i.
    have h_repr_v : (bV.repr v) i = ĝ i := by
      rw [show v = ∑ j, ĝ j • bV j from rfl]
      exact basis_repr_sum_smul bV ĝ i
    have h_repr_pyV : (bV.repr v) i = ((p : ℕ) : ℤ_[p]) * (bV.repr yV) i := by
      rw [h_v_eq, map_smul]
      rfl
    have h_g_zero : g i = 0 := by
      rw [← h_cast i]
      have h_eq_g : ĝ i = ((p : ℕ) : ℤ_[p]) * (bV.repr yV) i := by
        rw [← h_repr_v, h_repr_pyV]
      rw [h_eq_g, map_mul]
      rw [show PadicInt.toZMod (p := p) ((p : ℕ) : ℤ_[p]) = 0 from by
        rw [map_natCast]; exact ZMod.natCast_self p]
      rw [zero_mul]
    exact h_g_zero
  -- Combined: bW_cand is a ZMod p-basis of W_chi_modp.
  set bW : Module.Basis (Module.Free.ChooseBasisIndex ℤ_[p] V_p_chi) (ZMod p) W_chi_modp :=
    Module.Basis.mk h_indep (le_of_eq h_span.symm)
  rw [Module.finrank_eq_card_basis bV, Module.finrank_eq_card_basis bW]

end BernoulliRegular

end
