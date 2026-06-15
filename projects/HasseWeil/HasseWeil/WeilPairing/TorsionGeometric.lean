/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import HasseWeil.Curves.Differentials
import HasseWeil.EC.SeparableKernelTorsor
import HasseWeil.Hasse.TorsionCard
import HasseWeil.RouteBGeneral

/-!
# `#E[ℓ] = ℓ²` over an algebraically closed field, via the separable-kernel torsor

Instantiating the axiom-clean capstone `card_kernel_eq_degree_of_separable_concrete`
(`SeparableKernelTorsor.lean`) at `φ = [ℓ]` over `F = K̄` (algebraically closed), with `ℓ : ℤ`,
`ℓ ≠ 0` such that `(ℓ : F) ≠ 0` (so `[ℓ]` is separable). This discharges the three geometric
hypotheses (`hcov`, `h_normal`, `hdesc`) for `[ℓ]` and assembles `#E[ℓ] = ℓ²`.

## Separability of `[ℓ]` over `K̄` (Route B, finite-field free)

Separability of `[ℓ]` for `(ℓ : F) ≠ 0` is supplied by the field-general Route-B chain
`HasseWeil.omegaCoeff_mulByInt` / `HasseWeil.mulByInt_isSeparable` (Silverman III.5.3/4,
axiom-clean, no EDS Wronskian), imported here from `HasseWeil/RouteBGeneral.lean`. That chain
was born in this file as a `K → F` re-derivation of the `[Fintype K]`-scoped
`RouteBInduction.lean` induction; it was relocated (2026-06-11) so that it sits below
`Hasse/Separability.lean` in the import graph.

Reference: Silverman III.4.10c (the torsor), III.5.3 (`a_{[m]} = m`), III.6.4(a) (`#E[m] = m²`).
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

/-- **`hcov` reducer (field-general)**: if `τ_k` fixes `φ.pullback (x_gen)` and
`φ.pullback (y_gen)`, then it fixes `φ.pullback z` for all `z` (`algHom_ext_x_y_gen`). -/
theorem hcov_of_xy (φ : Isogeny W.toAffine W.toAffine) (k : W.toAffine.Point)
    (h_x : translateAlgEquivOfPoint W k (φ.pullback (x_gen W)) = φ.pullback (x_gen W))
    (h_y : translateAlgEquivOfPoint W k (φ.pullback (y_gen W)) = φ.pullback (y_gen W)) :
    ∀ z : KE, translateAlgEquivOfPoint W k (φ.pullback z) = φ.pullback z := by
  have h_eq : (translateAlgEquivOfPoint W k).toAlgHom.comp φ.pullback = φ.pullback :=
    algHom_ext_x_y_gen W (ψ₁ := (translateAlgEquivOfPoint W k).toAlgHom.comp φ.pullback)
      (ψ₂ := φ.pullback) h_x h_y
  intro z
  exact congrFun (congrArg DFunLike.coe h_eq) z

/-- **The `hxy` witness for `[ℓ]`** (Silverman III.4.10c / addition formula): for every kernel
point `k ∈ E[ℓ]`, the function-field translation `τ_k = translateAlgEquivOfPoint W k` fixes the
`ℓ`-division coordinate functions `mulByInt_x ℓ` and `mulByInt_y ℓ`. Mathematically these are the
`x`- and `y`-coordinates of `[ℓ]·P` as functions of `P`; precomposing with translation by `k`
gives `P ↦ x([ℓ](P+k)) = x([ℓ]P + [ℓ]k) = x([ℓ]P)` since `[ℓ]k = O`. -/
theorem hxy_mulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    ∀ k : (mulByInt W.toAffine ℓ).kernel,
      translateAlgEquivOfPoint W k.val (mulByInt_x W ℓ) = mulByInt_x W ℓ ∧
      translateAlgEquivOfPoint W k.val (mulByInt_y W ℓ) = mulByInt_y W ℓ := by
  intro k
  set m : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W)
      (translateAlgEquivOfPoint W k.val).toAlgHom with hm_def
  obtain ⟨hns, hsmul0⟩ := HasseWeil.zsmul_genericPoint_eq W ℓ hℓ
  -- `zsmul_genericPoint_eq` carries the `FractionRing.instDecidableEq` instance, a different
  -- term from the ambient `instDecidableEqFunctionField` threaded through `m`/`•`; the
  -- `Subsingleton.elim … ▸` realigns it (the `MulByIntAddRecurrence` fix) so the rewrites fire.
  have hsmul : ℓ • HasseWeil.genericPoint W =
      Affine.Point.some (mulByInt_x W ℓ) (mulByInt_y W ℓ) hns :=
    Subsingleton.elim (instDecidableEqFunctionField W) FractionRing.instDecidableEq ▸ hsmul0
  have hk0 : (ℓ : ℤ) • k.val = (0 : W.toAffine.Point) := by
    have hmem : (mulByInt W.toAffine ℓ).toAddMonoidHom k.val = 0 :=
      (HasseWeil.Isogeny.mem_kernel_iff (mulByInt W.toAffine ℓ) k.val).mp k.property
    rwa [mulByInt_apply] at hmem
  have h_add : m (ℓ • HasseWeil.genericPoint W) = ℓ • HasseWeil.genericPoint W := by
    rw [m.map_zsmul, show m (HasseWeil.genericPoint W) =
        HasseWeil.genericPoint W + HasseWeil.liftPointToKE W k.val from
      HasseWeil.translateAlgEquivOfPoint_map_genericPoint W k.val,
      zsmul_add, ← map_zsmul (HasseWeil.liftPointToKE W) ℓ k.val, hk0, map_zero, add_zero]
  rw [hsmul, hm_def] at h_add
  exact WeierstrassCurve.Affine.Point.some.inj ((WeierstrassCurve.Affine.Point.map_some
    (f := (translateAlgEquivOfPoint W k.val).toAlgHom) (h := hns)).symm.trans h_add)

/-- **`hcov` for `[ℓ]`, reduced to division-function translation-invariance**: the full
`hcov [ℓ]` follows from the two facts `τ_k (mulByInt_x ℓ) = mulByInt_x ℓ` and
`τ_k (mulByInt_y ℓ) = mulByInt_y ℓ` for every kernel point `k ∈ E[ℓ]` (`hxy`). These two facts are
the function-field shadow of `[ℓ] ∘ (·+k) = [ℓ]` on the `x`- and `y`-coordinates, i.e. the
ℓ-division functions `Φ_ℓ/Ψ_ℓ²`, `ω_ℓ/ψ_ℓ³` are invariant under `x ↦ translateX_xy k`. -/
theorem hcov_mulByInt_of_xy (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hxy : ∀ k : (mulByInt W.toAffine ℓ).kernel,
      translateAlgEquivOfPoint W k.val (mulByInt_x W ℓ) = mulByInt_x W ℓ ∧
      translateAlgEquivOfPoint W k.val (mulByInt_y W ℓ) = mulByInt_y W ℓ) :
    ∀ k : (mulByInt W.toAffine ℓ).kernel, ∀ z : KE,
      translateAlgEquivOfPoint W k.val ((mulByInt W.toAffine ℓ).pullback z) =
        (mulByInt W.toAffine ℓ).pullback z := by
  intro k
  refine hcov_of_xy W (mulByInt W.toAffine ℓ) k.val ?_ ?_
  · -- `x_gen W` is definitionally the displayed `algebraMap …` form of `mulByInt_pullback_x`.
    have hpx : (mulByInt W.toAffine ℓ).pullback (x_gen W) = mulByInt_x W ℓ :=
      mulByInt_pullback_x W ℓ hℓ
    rw [hpx]; exact (hxy k).1
  · have hpy : (mulByInt W.toAffine ℓ).pullback (y_gen W) = mulByInt_y W ℓ :=
      mulByInt_pullback_y W ℓ hℓ
    rw [hpy]; exact (hxy k).2

/-- **Assembly**: given the capstone's output `#ker[ℓ] = deg[ℓ]`, conclude `#E[ℓ] = ℓ²`. -/
theorem card_torsion_ell_of_ker_deg (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (h_ker_deg : Nat.card (mulByInt W.toAffine ℓ).kernel = (mulByInt W.toAffine ℓ).degree) :
    (Nat.card W.toAffine[ℓ] : ℤ) = ℓ ^ 2 :=
  HasseWeil.torsionSubgroup_card_of_witness W ℓ hℓ h_ker_deg

end HasseWeil.WeilPairing.TorsionGeometric
