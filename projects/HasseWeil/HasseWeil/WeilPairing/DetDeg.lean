/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import HasseWeil.WeilPairing.PairingAdjoint
import HasseWeil.WeilPairing.PairingDet
import HasseWeil.WeilPairing.PairingNondeg
import HasseWeil.WeilPairing.Representation
import HasseWeil.WeilPairing.RootsOfUnity

/-!
# Route 2A — the Weil-pairing determinant identity `det(ρ_ℓ φ) = deg φ` (Silverman III.8.6)

This file builds the **DET-DEG** capstone (tickets `T-R2-DET-DEG` + `T-R2-ASSEMBLE`): from the now
proven Weil pairing (`weilPairing`, bilinear / alternating / nondegenerate, with the per-isogeny
scaling `e_ℓ(φS,φT) = e_ℓ(S,T)^{deg φ}`) and the `ρ_ℓ` matrix representation
(`HasseWeil/WeilPairing/Representation.lean`), it derives

  `det(ρ_ℓ φ) ≡ deg φ (mod ℓ)`,

and then assembles the per-`ℓ` Frobenius-matrix data feeding the shipped Hasse-bound reduction
(`HasseWeil/WeilPairing/{Assembly,Reduction}.lean`).

## The additive symplectic form `omegaForm`

The Weil pairing is multiplicative, valued in the `ℓ`-th roots of unity `μ_ℓ ⊆ F`.  Over `K̄`
(`[IsAlgClosed F]`, `(ℓ:F) ≠ 0`) there is a primitive `ℓ`-th root of unity, hence an additive
isomorphism `μ_ℓ ≅ ℤ/ℓ` (`rootsOfUnity_addEquiv_zmod`).  Taking the discrete logarithm of the
pairing through this isomorphism turns `e_ℓ` into an **alternating, nondegenerate, `ZMod ℓ`-bilinear
form** `omegaForm : E[ℓ] →ₗ[ZMod ℓ] E[ℓ] →ₗ[ZMod ℓ] ZMod ℓ`:

* the bilinearity (`weilPairing_mul_left` / `weilPairing_mul_right`) becomes additivity, upgraded to
  `ZMod ℓ`-linearity automatically (`AddMonoidHom.toZModLinearMap`, since `E[ℓ]` is `ℓ`-torsion);
* `weilPairing_alternating` (`e_ℓ(T,T)=1`) becomes `omegaForm T T = 0`;
* `weilPairing_nondegenerate` becomes nondegeneracy of `omegaForm`;
* the per-isogeny scaling `e_ℓ(φS,φT) = e_ℓ(S,T)^{deg φ}` becomes
  `omegaForm (φS) (φT) = (deg φ) • omegaForm S T`.

## DET-DEG

On the rank-2 space `E[ℓ] ≅ (ZMod ℓ)²`, the abstract `Λ²` lemma
`PairingDet.det_eq_of_alternating_scaling` says any endomorphism scales the (nondegenerate
alternating) form `omegaForm` by its determinant.  The Weil scaling
`omegaForm (φx) (φy) = (deg φ)·omegaForm x y` then forces
`LinearMap.det (φ|E[ℓ]) = (deg φ : ZMod ℓ)`, hence (via `rhoEll_det`)
`det (ρ_ℓ φ) = (deg φ : ZMod ℓ)`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (the pairing), III.8.6 (`det φ_ℓ = deg φ`
  via the symplectic scaling), V.2.3.1 (the Hasse-bound assembly).
-/

open WeierstrassCurve HasseWeil.Curves Matrix

namespace HasseWeil.WeilPairing.TorsionGeometric

open HasseWeil HasseWeil.WeilPairing

-- The shared variable context carries `[IsIntegrallyClosed …CoordinateRing]`, which several
-- statements need only for instance synthesis (not in their type), so the linter over-reports
-- it as unused; it cannot be `omit`ted without breaking resolution.
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [IsAlgClosed F] (hℓF : (ℓ : F) ≠ 0)

section AdditiveForm

/-- A point of `E[ℓ] = W.toAffine[((ℓ:ℕ):ℤ)]` is killed by `(ℓ:ℤ)` (the form the pairing wants). -/
theorem zsmul_eq_zero_of_mem_torsion (S : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    ((ℓ : ℕ) : ℤ) • S.val = 0 := (mem_torsionSubgroup _ _ _).mp S.property

include hℓF

/-- The Weil pairing value as an element of `rootsOfUnity ℓ F` (`μ_ℓ`), built from the nonzero
field value `e_ℓ(S,T)` and the root-of-unity property `e_ℓ(S,T)^ℓ = 1`. -/
noncomputable def pairingRou (S T : W.toAffine[((ℓ : ℕ) : ℤ)]) : rootsOfUnity ℓ F :=
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  rootsOfUnity.mkOfPowEq (weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
      (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T))
    (by simpa using (weilPairing_pow_eq_one W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
      (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T)))

/-- The `F`-value of `pairingRou S T` is the Weil pairing `e_ℓ(S,T)`. -/
theorem pairingRou_coe (S T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    ((pairingRou W ℓ hℓF S T : Fˣ) : F) =
      weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
        (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T) := by
  have : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  rfl

/-- **Bilinearity of `pairingRou` in slot 1** (from `weilPairing_mul_left`). -/
theorem pairingRou_mul_left (S₁ S₂ T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    pairingRou W ℓ hℓF (S₁ + S₂) T = pairingRou W ℓ hℓF S₁ T * pairingRou W ℓ hℓF S₂ T := by
  refine Subtype.ext (Units.ext ?_)
  rw [pairingRou_coe, Subgroup.coe_mul, Units.val_mul, pairingRou_coe, pairingRou_coe]
  exact weilPairing_mul_left W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S₁.val S₂.val T.val _ _ _ _

/-- **Bilinearity of `pairingRou` in slot 2** (from `weilPairing_mul_right`). -/
theorem pairingRou_mul_right (S T₁ T₂ : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    pairingRou W ℓ hℓF S (T₁ + T₂) = pairingRou W ℓ hℓF S T₁ * pairingRou W ℓ hℓF S T₂ := by
  refine Subtype.ext (Units.ext ?_)
  rw [pairingRou_coe, Subgroup.coe_mul, Units.val_mul, pairingRou_coe, pairingRou_coe]
  exact weilPairing_mul_right W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T₁.val T₂.val _ _ _ _

/-- A primitive `ℓ`-th root of unity in `Fˣ`, over `K̄` with `(ℓ:F) ≠ 0`.  Exists by
`HasEnoughRootsOfUnity` (`IsAlgClosed ⟹ IsSepClosed`, `NeZero (ℓ:F)`). -/
noncomputable def primRou : Fˣ :=
  haveI : NeZero ((ℓ : ℕ) : F) := ⟨hℓF⟩
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  ((HasEnoughRootsOfUnity.exists_primitiveRoot F ℓ).choose_spec.isUnit
    (hℓ.out.pos.ne')).unit

omit [DecidableEq F] in
theorem primRou_isPrimitiveRoot : IsPrimitiveRoot (primRou (F := F) ℓ hℓF) ℓ :=
  haveI : NeZero ((ℓ : ℕ) : F) := ⟨hℓF⟩
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  (HasEnoughRootsOfUnity.exists_primitiveRoot F ℓ).choose_spec.isUnit_unit (hℓ.out.pos.ne')

/-- The discrete logarithm `μ_ℓ → ℤ/ℓ` for the chosen primitive root, as an `AddMonoidHom` on
`Additive (rootsOfUnity ℓ F)`. -/
noncomputable def logRou : Additive (rootsOfUnity ℓ F) →+ ZMod ℓ :=
  haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  (rootsOfUnity_addEquiv_zmod (primRou_isPrimitiveRoot ℓ hℓF)).toAddMonoidHom

omit [DecidableEq F] in
/-- `logRou` sends a product of roots of unity to a sum: `log(ζ₁·ζ₂) = log ζ₁ + log ζ₂`. -/
theorem logRou_mul (a b : rootsOfUnity ℓ F) :
    logRou ℓ hℓF (Additive.ofMul (a * b)) =
      logRou ℓ hℓF (Additive.ofMul a) + logRou ℓ hℓF (Additive.ofMul b) := by
  rw [← map_add]
  rfl

/-- The discrete-log Weil pairing `ω(S,T) = log e_ℓ(S,T) ∈ ZMod ℓ`. -/
noncomputable def omegaFun (S T : W.toAffine[((ℓ : ℕ) : ℤ)]) : ZMod ℓ :=
  logRou ℓ hℓF (Additive.ofMul (pairingRou W ℓ hℓF S T))

theorem omegaFun_add_left (S₁ S₂ T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    omegaFun W ℓ hℓF (S₁ + S₂) T = omegaFun W ℓ hℓF S₁ T + omegaFun W ℓ hℓF S₂ T := by
  unfold omegaFun
  rw [pairingRou_mul_left, logRou_mul]

theorem omegaFun_add_right (S T₁ T₂ : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    omegaFun W ℓ hℓF S (T₁ + T₂) = omegaFun W ℓ hℓF S T₁ + omegaFun W ℓ hℓF S T₂ := by
  unfold omegaFun
  rw [pairingRou_mul_right, logRou_mul]

/-- For fixed `S`, the additive map `T ↦ ω(S,T)`. -/
noncomputable def omegaRightHom (S : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    W.toAffine[((ℓ : ℕ) : ℤ)] →+ ZMod ℓ where
  toFun T := omegaFun W ℓ hℓF S T
  map_zero' := by
    have h := omegaFun_add_right W ℓ hℓF S 0 0
    rw [add_zero] at h
    linear_combination -h
  map_add' := omegaFun_add_right W ℓ hℓF S

/-- For fixed `S`, the `ZMod ℓ`-linear map `T ↦ ω(S,T)` (additive ⟹ `ZMod ℓ`-linear on
`ℓ`-torsion). -/
noncomputable def omegaRightLin (S : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] ZMod ℓ :=
  (omegaRightHom W ℓ hℓF S).toZModLinearMap ℓ

@[simp] theorem omegaRightLin_apply (S T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    omegaRightLin W ℓ hℓF S T = omegaFun W ℓ hℓF S T := rfl

/-- The additive map `S ↦ (T ↦ ω(S,T))` into the linear duals. -/
noncomputable def omegaLeftHom :
    W.toAffine[((ℓ : ℕ) : ℤ)] →+ (W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] ZMod ℓ) where
  toFun S := omegaRightLin W ℓ hℓF S
  map_zero' := by
    ext T
    have h := omegaFun_add_left W ℓ hℓF 0 0 T
    rw [add_zero] at h
    simp only [omegaRightLin_apply, LinearMap.zero_apply]
    linear_combination -h
  map_add' S₁ S₂ := by
    ext T
    simp only [omegaRightLin_apply, LinearMap.add_apply]
    exact omegaFun_add_left W ℓ hℓF S₁ S₂ T

/-- **The additive symplectic form `ω` of the Weil pairing** (Silverman III.8.1): the
`ZMod ℓ`-valued alternating bilinear form on `E[ℓ]` obtained by taking the discrete log of the
multiplicative Weil pairing.  Built from `omegaLeftHom` via `AddMonoidHom.toZModLinearMap`
(additive ⟹ `ZMod ℓ`-linear, since `E[ℓ]` is `ℓ`-torsion). -/
noncomputable def omegaForm :
    W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ]
      (W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] ZMod ℓ) :=
  (omegaLeftHom W ℓ hℓF).toZModLinearMap ℓ

@[simp] theorem omegaForm_apply (S T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    omegaForm W ℓ hℓF S T = omegaFun W ℓ hℓF S T := rfl

/-- `pairingRou T T = 1` (the identity root of unity), from `weilPairing_self` (`e_ℓ(T,T) = 1`). -/
theorem pairingRou_self (T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    pairingRou W ℓ hℓF T T = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [pairingRou_coe, show ((((1 : rootsOfUnity ℓ F) : Fˣ)) : F) = (1 : F) from rfl]
  exact weilPairing_self W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) T.val
    (zsmul_eq_zero_of_mem_torsion W ℓ T)

/-- **`ω` is alternating** (`ω(T,T) = 0`), the log of `weilPairing_alternating` (`e_ℓ(T,T)=1`). -/
theorem omegaForm_self (T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    omegaForm W ℓ hℓF T T = 0 := by
  rw [omegaForm_apply]
  unfold omegaFun
  rw [pairingRou_self, show Additive.ofMul (1 : rootsOfUnity ℓ F) = 0 from rfl, map_zero]

/-- **`ω` is nondegenerate** in the second slot: if `ω(S,T) = 0` for all `S ∈ E[ℓ]`, then
`T = 0`. -/
theorem omegaForm_nondegenerate {T : W.toAffine[((ℓ : ℕ) : ℤ)]}
    (h : ∀ S : W.toAffine[((ℓ : ℕ) : ℤ)], omegaForm W ℓ hℓF S T = 0) :
    T = 0 := by
  have : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
  refine Subtype.ext (weilPairing_nondegenerate W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) T.val
    (zsmul_eq_zero_of_mem_torsion W ℓ T) (fun S hS => ?_))
  set S' : W.toAffine[((ℓ : ℕ) : ℤ)] := ⟨S, (mem_torsionSubgroup _ _ _).mpr hS⟩
  have hω : (rootsOfUnity_addEquiv_zmod (primRou_isPrimitiveRoot ℓ hℓF))
      (Additive.ofMul (pairingRou W ℓ hℓF S' T)) = 0 := by
    have := h S'; rwa [omegaForm_apply, omegaFun] at this
  have hone : Additive.ofMul (pairingRou W ℓ hℓF S' T) = 0 := by
    simpa using (rootsOfUnity_addEquiv_zmod (primRou_isPrimitiveRoot ℓ hℓF)).injective
      (hω.trans (map_zero _).symm)
  have hval : ((pairingRou W ℓ hℓF S' T : Fˣ) : F) =
      ((((1 : rootsOfUnity ℓ F) : Fˣ)) : F) := by
    rw [show pairingRou W ℓ hℓF S' T = 1 by simpa using congrArg Additive.toMul hone]
  rwa [pairingRou_coe, show ((((1 : rootsOfUnity ℓ F) : Fˣ)) : F) = (1 : F) from rfl] at hval

/-- The pairing-power: if `e_ℓ(ψS, ψT) = e_ℓ(S,T)^d` for an `AddMonoidHom ψ` (preserving `E[ℓ]`),
then `pairingRou (ψS) (ψT) = (pairingRou S T)^d` as roots of unity. -/
theorem pairingRou_scaling (ψ : W.toAffine.Point →+ W.toAffine.Point) (d : ℕ)
    (S T : W.toAffine[((ℓ : ℕ) : ℤ)])
    (hsc : weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
          (ψ S.val) (ψ T.val) (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ S, map_zero])
          (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ T, map_zero]) =
        weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
          (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T) ^ d) :
    pairingRou W ℓ hℓF (torsionRestrict W ℓ ψ S) (torsionRestrict W ℓ ψ T) =
      pairingRou W ℓ hℓF S T ^ d := by
  refine Subtype.ext (Units.ext ?_)
  rw [pairingRou_coe, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, pairingRou_coe]
  exact hsc

/-- **The additive scaling `ω(ψS, ψT) = (d : ZMod ℓ) · ω(S,T)`**, the discrete log of the
multiplicative scaling `e_ℓ(ψS, ψT) = e_ℓ(S,T)^d`. -/
theorem omegaForm_scaling (ψ : W.toAffine.Point →+ W.toAffine.Point) (d : ℕ)
    (S T : W.toAffine[((ℓ : ℕ) : ℤ)])
    (hsc : weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
          (ψ S.val) (ψ T.val) (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ S, map_zero])
          (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ T, map_zero]) =
        weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
          (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T) ^ d) :
    omegaForm W ℓ hℓF (torsionRestrict W ℓ ψ S) (torsionRestrict W ℓ ψ T) =
      (d : ZMod ℓ) * omegaForm W ℓ hℓF S T := by
  rw [omegaForm_apply, omegaForm_apply]
  unfold omegaFun
  rw [pairingRou_scaling W ℓ hℓF ψ d S T hsc,
    show Additive.ofMul (pairingRou W ℓ hℓF S T ^ d)
      = d • Additive.ofMul (pairingRou W ℓ hℓF S T) from rfl, map_nsmul, nsmul_eq_mul]

/-- **`ω` is antisymmetric** (`ω(S,T) + ω(T,S) = 0`), the log of `weilPairing_antisymm`
(`e_ℓ(S,T)·e_ℓ(T,S)=1`). -/
theorem omegaForm_antisymm (S T : W.toAffine[((ℓ : ℕ) : ℤ)]) :
    omegaForm W ℓ hℓF S T + omegaForm W ℓ hℓF T S = 0 := by
  rw [omegaForm_apply, omegaForm_apply]
  unfold omegaFun
  rw [← logRou_mul]
  have hmul : pairingRou W ℓ hℓF S T * pairingRou W ℓ hℓF T S = 1 := by
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, pairingRou_coe, pairingRou_coe,
      show ((((1 : rootsOfUnity ℓ F) : Fˣ)) : F) = (1 : F) from rfl]
    exact weilPairing_antisymm W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val _ _
  rw [hmul, show Additive.ofMul (1 : rootsOfUnity ℓ F) = 0 from rfl, map_zero]

/-- **The Gram entry `ω(b 0, b 1) ≠ 0`** (nondegeneracy on the symplectic basis).  If it were `0`,
then by alternating (`ω(b i, b i) = 0`) and antisymmetry (`ω(b 1, b 0) = -ω(b 0, b 1) = 0`), the
linear form `ω(·, b 1)` would vanish on the basis, hence everywhere, forcing `b 1 = 0` by
nondegeneracy — contradicting `b 1 ≠ 0`. -/
theorem omegaForm_gram_ne_zero :
    omegaForm W ℓ hℓF (torsion_ell_basis W ℓ hℓF 0) (torsion_ell_basis W ℓ hℓF 1) ≠ 0 := by
  have : Nontrivial (ZMod ℓ) := ⟨0, 1, by
    have : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
    exact zero_ne_one⟩
  intro h01
  refine (torsion_ell_basis W ℓ hℓF).ne_zero 1 (omegaForm_nondegenerate W ℓ hℓF fun S => ?_)
  have hrepr := (torsion_ell_basis W ℓ hℓF).sum_repr S
  rw [Fin.sum_univ_two] at hrepr
  rw [← hrepr, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, omegaForm_self, h01]
  simp

end AdditiveForm

section DetDeg

include hℓF

/-- **DET-DEG (module form)** (Silverman III.8.6): for an `AddMonoidHom ψ` preserving `E[ℓ]` whose
Weil-pairing scaling is `e_ℓ(ψS, ψT) = e_ℓ(S,T)^d`, the determinant of `ψ` on `E[ℓ]` is
`(d:ZMod ℓ)`.
Combines `omegaForm_scaling` (the additive scaling) with `PairingDet.det_eq_of_alternating_scaling`
(the `Λ²` lemma on the nondegenerate alternating form `ω`). -/
theorem linearMap_det_torsionRestrict_eq (ψ : W.toAffine.Point →+ W.toAffine.Point) (d : ℕ)
    (hsc : ∀ S T : W.toAffine[((ℓ : ℕ) : ℤ)],
      weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
          (ψ S.val) (ψ T.val) (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ S, map_zero])
          (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ T, map_zero]) =
        weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
          (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T) ^ d) :
    LinearMap.det (torsionRestrict W ℓ ψ) = (d : ZMod ℓ) := by
  refine HasseWeil.WeilPairing.det_eq_of_alternating_scaling (torsion_ell_basis W ℓ hℓF)
    (omegaForm W ℓ hℓF) (omegaForm_self W ℓ hℓF) (omegaForm_gram_ne_zero W ℓ hℓF)
    (torsionRestrict W ℓ ψ) (fun x y => ?_)
  exact omegaForm_scaling W ℓ hℓF ψ d x y (hsc x y)

/-- **DET-DEG (matrix form)** (Silverman III.8.6): `det(ρ_ℓ ψ) = (d : ZMod ℓ)` from the pairing
scaling, via `rhoEll_det`. -/
theorem det_rhoEll_eq_degree (ψ : W.toAffine.Point →+ W.toAffine.Point) (d : ℕ)
    (hsc : ∀ S T : W.toAffine[((ℓ : ℕ) : ℤ)],
      weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
          (ψ S.val) (ψ T.val) (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ S, map_zero])
          (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ T, map_zero]) =
        weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
          (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T) ^ d) :
    (rhoEll W ℓ hℓF ψ).det = (d : ZMod ℓ) := by
  rw [rhoEll_det]
  exact linearMap_det_torsionRestrict_eq W ℓ hℓF ψ d hsc

end DetDeg

section RingHom

/-- `ρ_ℓ` respects subtraction (`torsionRestrict` is additive, `LinearMap.toMatrix` a
`LinearEquiv`). -/
theorem rhoEll_sub (ψ₁ ψ₂ : W.toAffine.Point →+ W.toAffine.Point) :
    rhoEll W ℓ hℓF (ψ₁ - ψ₂) = rhoEll W ℓ hℓF ψ₁ - rhoEll W ℓ hℓF ψ₂ := by
  rw [rhoEll, rhoEll, rhoEll,
    show torsionRestrict W ℓ (ψ₁ - ψ₂)
      = torsionRestrict W ℓ ψ₁ - torsionRestrict W ℓ ψ₂ by ext P; rfl, map_sub]

/-- `ρ_ℓ(n • ψ) = (n : ZMod ℓ) • ρ_ℓ(ψ)` (the `ℤ`-scalar on `End E` reduces mod `ℓ`). -/
theorem rhoEll_zsmul (n : ℤ) (ψ : W.toAffine.Point →+ W.toAffine.Point) :
    rhoEll W ℓ hℓF (n • ψ) = (n : ZMod ℓ) • rhoEll W ℓ hℓF ψ := by
  rw [rhoEll, rhoEll,
    show torsionRestrict W ℓ (n • ψ) = n • torsionRestrict W ℓ ψ by ext P; rfl,
    map_zsmul, Int.cast_smul_eq_zsmul]

/-- **`1 − ρ_ℓ(π) = ρ_ℓ(id − π)`** — the matrix of the isogeny `1 − π` on `E[ℓ]`. -/
theorem one_sub_rhoEll (πhom : W.toAffine.Point →+ W.toAffine.Point) :
    1 - rhoEll W ℓ hℓF πhom = rhoEll W ℓ hℓF (AddMonoidHom.id W.toAffine.Point - πhom) := by
  rw [rhoEll_sub, rhoEll_id]

/-- **`r • ρ_ℓ(π) − s • 1 = ρ_ℓ(r • π − s • id)`** — the matrix of the isogeny `rπ − s` on
`E[ℓ]`. -/
theorem smul_rhoEll_sub (r s : ℤ) (πhom : W.toAffine.Point →+ W.toAffine.Point) :
    (r : ZMod ℓ) • rhoEll W ℓ hℓF πhom - (s : ZMod ℓ) • 1 =
      rhoEll W ℓ hℓF (r • πhom - s • AddMonoidHom.id W.toAffine.Point) := by
  rw [rhoEll_sub, rhoEll_zsmul, rhoEll_zsmul, rhoEll_id]

end RingHom

section Assembly

include hℓF

/-- A convenient abbreviation for the per-isogeny Weil-pairing scaling hypothesis on `E[ℓ]`:
`e_ℓ(ψ S, ψ T) = e_ℓ(S,T)^d` for all torsion `S, T`, for an `AddMonoidHom ψ` preserving `E[ℓ]`. -/
def WeilScales (ψ : W.toAffine.Point →+ W.toAffine.Point) (d : ℕ) : Prop :=
  ∀ S T : W.toAffine[((ℓ : ℕ) : ℤ)],
    weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
        (ψ S.val) (ψ T.val)
        (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ S, map_zero])
        (by rw [← map_zsmul ψ, zsmul_eq_zero_of_mem_torsion W ℓ T, map_zero]) =
      weilPairing W ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val
        (zsmul_eq_zero_of_mem_torsion W ℓ S) (zsmul_eq_zero_of_mem_torsion W ℓ T) ^ d

/-- **The three Frobenius det facts from the Weil-pairing scalings** (the `Reduction`/`Assembly`
interface).  Given the Frobenius hom `πhom` on `E[ℓ]`, scalars `r s : ℤ`, natural degrees
`dπ, d1, drs`, and the three per-isogeny Weil-pairing scalings (`π` scales by `dπ`, `1−π` by `d1`,
`rπ−s` by `drs`), the matrix `M = ρ_ℓ(πhom)` satisfies `det M = dπ`, `det(1−M) = d1`,
`det(rM − sI) = drs` in `ZMod ℓ`. -/
theorem frob_det_data_of_weil_scaling (πhom : W.toAffine.Point →+ W.toAffine.Point)
    (r s : ℤ) (dπ d1 drs : ℕ)
    (hπ : WeilScales W ℓ hℓF πhom dπ)
    (h1 : WeilScales W ℓ hℓF (AddMonoidHom.id W.toAffine.Point - πhom) d1)
    (hrs : WeilScales W ℓ hℓF (r • πhom - s • AddMonoidHom.id W.toAffine.Point) drs) :
    (rhoEll W ℓ hℓF πhom).det = (dπ : ZMod ℓ) ∧
      (1 - rhoEll W ℓ hℓF πhom).det = (d1 : ZMod ℓ) ∧
      ((r : ZMod ℓ) • rhoEll W ℓ hℓF πhom - (s : ZMod ℓ) • 1).det = (drs : ZMod ℓ) :=
  ⟨det_rhoEll_eq_degree W ℓ hℓF πhom dπ hπ,
   one_sub_rhoEll W ℓ hℓF πhom ▸ det_rhoEll_eq_degree W ℓ hℓF _ d1 h1,
   smul_rhoEll_sub W ℓ hℓF r s πhom ▸ det_rhoEll_eq_degree W ℓ hℓF _ drs hrs⟩

/-- **The per-`ℓ` Frobenius determinant residual from the Weil scalings, integer form** (the exact
shape of the shipped `Reduction.deg_eq_of_frob_det_data` /
`Assembly.qf_nonneg_of_frob_det_residual` hypothesis).  Given the Frobenius hom on `E[ℓ]` over `K̄`,
integers `q, t, Dν` equal (as integers) to the geometric degrees `deg π`, `q+1−deg(1−π)`,
`deg(rπ−s)`, and the three Weil-pairing scalings, there is a matrix `M = ρ_ℓ(π)` with `det M = q`,
`det(1−M) = q+1−t`, `det(rM−sI) = Dν` in `ZMod ℓ`. -/
theorem frob_det_residual_of_weil_scaling (πhom : W.toAffine.Point →+ W.toAffine.Point)
    (q t Dν : ℤ) (r s : ℤ) (dπ d1 drs : ℕ)
    (hqd : (dπ : ℤ) = q) (h1d : (d1 : ℤ) = q + 1 - t) (hDd : (drs : ℤ) = Dν)
    (hπ : WeilScales W ℓ hℓF πhom dπ)
    (h1 : WeilScales W ℓ hℓF (AddMonoidHom.id W.toAffine.Point - πhom) d1)
    (hrs : WeilScales W ℓ hℓF (r • πhom - s • AddMonoidHom.id W.toAffine.Point) drs) :
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      M.det = (q : ZMod ℓ) ∧ (1 - M).det = ((q + 1 - t : ℤ) : ZMod ℓ) ∧
      ((r : ZMod ℓ) • M - (s : ZMod ℓ) • 1).det = (Dν : ZMod ℓ) := by
  obtain ⟨hdet, hdet1, hdetrs⟩ := frob_det_data_of_weil_scaling W ℓ hℓF πhom r s dπ d1 drs hπ h1 hrs
  refine ⟨rhoEll W ℓ hℓF πhom, ?_, ?_, ?_⟩
  · rw [hdet, ← hqd]
    push_cast
    ring
  · rw [hdet1, ← h1d]
    push_cast
    ring
  · rw [hdetrs, ← hDd]
    push_cast
    ring

end Assembly

end HasseWeil.WeilPairing.TorsionGeometric
