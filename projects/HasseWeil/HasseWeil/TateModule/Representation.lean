/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.TateModule.TateModule
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The ℓ-adic Galois representation `ρ_ℓ` (Silverman III.7)

For an elliptic curve `W₀` over a field `K` with algebraically closed extension `F` (e.g.
`F = AlgebraicClosure K`) such that `ℓ ≠ char K`, the absolute Galois group `Gal(F/K) = F ≃ₐ[K] F`
acts on each `ℓⁿ`-torsion group `E[ℓⁿ]` of `E = W₀.baseChange F`, the action commuting with the
multiplication-by-`ℓ` connecting maps `tateConn`, and hence acts `ℤ_[ℓ]`-linearly on the Tate
module `T_ℓ(E) = lim_n E[ℓⁿ]`. The resulting homomorphism `Gal(F/K) → Aut_{ℤ_[ℓ]}(T_ℓ(E))` is the
**ℓ-adic representation** of `E`.

## Main definitions and results

* `galoisTorsionRestrict W₀ ℓ σ n : E[ℓⁿ] →ₗ[ZMod (ℓⁿ)] E[ℓⁿ]` (**L11**) — the Galois action of
  `σ : F ≃ₐ[K] F` on the `ℓⁿ`-torsion, via mathlib's `WeierstrassCurve.Affine.Point.map σ.toAlgHom`
  (an `AddMonoidHom` that preserves torsion since `[ℓⁿ](σ P) = σ ([ℓⁿ] P) = σ O = O`). The
  `ZMod (ℓⁿ)`-linearity is automatic (`AddMonoidHom.toZModLinearMap`).
* `galois_comm_tateConn W₀ ℓ σ n` (**L12**) — the action commutes with `tateConn`
  (`map_zsmul` of `Affine.Point.map σ`), so it descends to the limit.
* `rhoTate W₀ ℓ σ : T_ℓ(E) ≃ₗ[ℤ_[ℓ]] T_ℓ(E)` (**L12**) — `σ` acting coordinatewise on compatible
  sequences, `ℤ_[ℓ]`-linear and invertible (inverse from `σ⁻¹`).
* `rhoTateHom W₀ ℓ : (F ≃ₐ[K] F) →* (T_ℓ(E) ≃ₗ[ℤ_[ℓ]] T_ℓ(E))` (**L13**) — the ℓ-adic
  representation as a group homomorphism (`map_one`/`map_mul` from functoriality of
  `Affine.Point.map`, i.e. `map_id`/`map_map`).
* `rhoTateGL W₀ ℓ hℓF : (F ≃ₐ[K] F) →* GL (Fin 2) ℤ_[ℓ]` (**L14**) — the `GL₂(ℤ_[ℓ])` form,
  obtained from `rhoTateHom` by conjugating with the basis isomorphism `tateModuleEquiv`
  (Silverman, Remark 7.2).

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), §III.7, pp. 87–88
(the Galois action on `E[ℓⁿ]`, its commutation with `[ℓ]`, and the Definition of `ρ_ℓ`).
-/

open WeierstrassCurve Matrix

namespace HasseWeil.TateModule

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric
open scoped HasseWeil.WeilPairing.TorsionGeometric

variable {K : Type*} [Field K] [DecidableEq K]
  {F : Type*} [Field F] [DecidableEq F] [Algebra K F] [IsAlgClosed F]
  (W₀ : WeierstrassCurve K) [(W₀.baseChange F).toAffine.IsElliptic]

/-! ## The Galois action on points (functoriality) -/

section GaloisPoint

/-- The Galois action of `σ : F ≃ₐ[K] F` on the points of `E = W₀.baseChange F`, as an
`AddMonoidHom` `E.Point →+ E.Point`. It is mathlib's `WeierstrassCurve.Affine.Point.map` along the
algebra homomorphism `σ.toAlgHom : F →ₐ[K] F`; since `σ` fixes `K`, the target curve is the same
`E`, so domain and codomain agree. -/
noncomputable def galoisPointHom (σ : F ≃ₐ[K] F) :
    (W₀.baseChange F).toAffine.Point →+ (W₀.baseChange F).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (σ.toAlgHom)

omit [DecidableEq K] [IsAlgClosed F] [(W₀.baseChange F).toAffine.IsElliptic] in
/-- Functoriality of the point action `galoisPointHom` in `σ` (composition leg):
`galoisPointHom (σ * τ) = galoisPointHom σ ∘ galoisPointHom τ`. This is mathlib's
`Affine.Point.map_map` (`map (g.comp f) = map g ∘ map f`); the multiplication on `F ≃ₐ[K] F`
is composition, so `(σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom`. -/
theorem galoisPointHom_mul (σ τ : F ≃ₐ[K] F) (P : (W₀.baseChange F).toAffine.Point) :
    galoisPointHom W₀ (σ * τ) P = galoisPointHom W₀ σ (galoisPointHom W₀ τ P) := by
  rw [galoisPointHom, galoisPointHom, galoisPointHom, WeierstrassCurve.Affine.Point.map_map]
  rfl

omit [DecidableEq K] [IsAlgClosed F] [(W₀.baseChange F).toAffine.IsElliptic] in
/-- Functoriality of the point action `galoisPointHom` in `σ` (identity leg):
`galoisPointHom 1 P = P`. The identity automorphism `1 : F ≃ₐ[K] F` fixes every coordinate
(`AlgEquiv.one_apply`), so the point map is the identity. -/
theorem galoisPointHom_one (P : (W₀.baseChange F).toAffine.Point) :
    galoisPointHom W₀ (1 : F ≃ₐ[K] F) P = P := by
  cases P with
  | zero => rfl
  | some x y h => rw [galoisPointHom, WeierstrassCurve.Affine.Point.map_some]; congr 1

end GaloisPoint

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-! ## L11 — Galois action on each `E[ℓⁿ]` -/

section GaloisTorsion

omit [DecidableEq K] [IsAlgClosed F] hℓ in
/-- The Galois action `galoisPointHom σ` (any additive endomorphism, in fact) preserves the
`ℓⁿ`-torsion `E[ℓⁿ]`: if `[ℓⁿ] P = O` then `[ℓⁿ](σ P) = σ([ℓⁿ] P) = σ O = O`. (Uses only that
`galoisPointHom σ` is an `AddMonoidHom`, hence commutes with `m • ·`.) -/
theorem galoisPointHom_mem_torsion_ellPow (σ : F ≃ₐ[K] F) (n : ℕ)
    {P : (W₀.baseChange F).toAffine.Point}
    (hP : P ∈ (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
    galoisPointHom W₀ σ P ∈ (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)] := by
  rw [mem_torsionSubgroup] at hP ⊢
  rw [← map_zsmul (galoisPointHom W₀ σ), hP, map_zero]

/-- The Galois action of `σ : F ≃ₐ[K] F` on the `ℓⁿ`-torsion `E[ℓⁿ]`, packaged as an
`AddMonoidHom`. This is `galoisPointHom σ` co-restricted from `E.Point` to `E[ℓⁿ]` using
`galoisPointHom_mem_torsion_ellPow`. -/
noncomputable def galoisTorsionRestrictHom (σ : F ≃ₐ[K] F) (n : ℕ) :
    (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)] →+
      (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)] :=
  ((galoisPointHom W₀ σ).comp ((W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)]).subtype).codRestrict _
    (fun P ↦ galoisPointHom_mem_torsion_ellPow W₀ ℓ σ n P.property)

omit [DecidableEq K] [IsAlgClosed F] hℓ in
@[simp] theorem galoisTorsionRestrictHom_coe (σ : F ≃ₐ[K] F) (n : ℕ)
    (P : (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
    (galoisTorsionRestrictHom W₀ ℓ σ n P : (W₀.baseChange F).toAffine.Point) =
      galoisPointHom W₀ σ P := rfl

/-- **L11.** The Galois action of `σ : F ≃ₐ[K] F` on the `ℓⁿ`-torsion `E[ℓⁿ]`, as a
`ZMod (ℓⁿ)`-linear endomorphism. The point map `galoisPointHom σ` preserves `E[ℓⁿ]` because it is
additive (`[ℓⁿ](σ P) = σ([ℓⁿ] P) = σ O = O`); linearity over `ZMod (ℓⁿ)` is automatic since that
scalar action is the natural-number `•` (`AddMonoidHom.toZModLinearMap`). -/
noncomputable def galoisTorsionRestrict (σ : F ≃ₐ[K] F) (n : ℕ) :
    (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)] →ₗ[ZMod (ℓ ^ n)]
      (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)] :=
  (galoisTorsionRestrictHom W₀ ℓ σ n).toZModLinearMap (ℓ ^ n)

omit [DecidableEq K] [IsAlgClosed F] hℓ in
@[simp] theorem galoisTorsionRestrict_apply (σ : F ≃ₐ[K] F) (n : ℕ)
    (P : (W₀.baseChange F).toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
    (galoisTorsionRestrict W₀ ℓ σ n P : (W₀.baseChange F).toAffine.Point) =
      galoisPointHom W₀ σ P := rfl

end GaloisTorsion

/-! ## L12 — Commutation with `tateConn` and assembly of `ρ_ℓ` on `T_ℓ(E)` -/

section RhoTate

omit [DecidableEq K] [IsAlgClosed F] hℓ in
/-- **L12 (commutation).** The Galois action commutes with the connecting maps `tateConn`:
`tateConn n (galoisTorsionRestrict σ (n+1) P) = galoisTorsionRestrict σ n (tateConn n P)`.
Both sides are, on the underlying points, `galoisPointHom σ` applied to `ℓ • (P : E.Point)`,
which agree because `galoisPointHom σ` is an `AddMonoidHom` and so commutes with `ℓ • ·`
(`map_zsmul`). -/
theorem galois_comm_tateConn (σ : F ≃ₐ[K] F) (n : ℕ)
    (P : (W₀.baseChange F).toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) :
    tateConn (W₀.baseChange F) ℓ n (galoisTorsionRestrict W₀ ℓ σ (n + 1) P) =
      galoisTorsionRestrict W₀ ℓ σ n (tateConn (W₀.baseChange F) ℓ n P) := by
  apply Subtype.ext
  rw [tateConn_coe, galoisTorsionRestrict_apply, galoisTorsionRestrict_apply, tateConn_coe]
  exact (map_zsmul (galoisPointHom W₀ σ) (ℓ : ℤ) (P : (W₀.baseChange F).toAffine.Point)).symm

/-- The Galois action of `σ : F ≃ₐ[K] F` on the Tate module `T_ℓ(E)`, as a `ℤ_[ℓ]`-linear map: it
sends a compatible sequence `f` to the coordinatewise image `n ↦ galoisTorsionRestrict σ n (f n)`.
The result is again compatible by `galois_comm_tateConn`; `ℤ_[ℓ]`-linearity is checked
coordinatewise from the `ZMod (ℓⁿ)`-linearity of each `galoisTorsionRestrict σ n`. -/
noncomputable def rhoTateAux (σ : F ≃ₐ[K] F) :
    tateModule (W₀.baseChange F) ℓ →ₗ[ℤ_[ℓ]] tateModule (W₀.baseChange F) ℓ where
  toFun f := ⟨fun n ↦ galoisTorsionRestrict W₀ ℓ σ n (f.val n), fun n ↦ by
    rw [galois_comm_tateConn W₀ ℓ σ n (f.val (n + 1)), tateCompat_compat]⟩
  map_add' f g := by
    apply Subtype.ext; funext n
    simp only [AddSubgroup.coe_add, Pi.add_apply, map_add]
  map_smul' z f := by
    apply Subtype.ext; funext n
    simp only [smul_tateCompat_val, map_smul, RingHom.id_apply]

omit [DecidableEq K] [IsAlgClosed F] in
@[simp] theorem rhoTateAux_val (σ : F ≃ₐ[K] F) (f : tateModule (W₀.baseChange F) ℓ) (n : ℕ) :
    (rhoTateAux W₀ ℓ σ f).val n = galoisTorsionRestrict W₀ ℓ σ n (f.val n) := rfl

omit [DecidableEq K] [IsAlgClosed F] in
/-- `rhoTateAux` is functorial in `σ`: `rhoTateAux (σ * τ) = rhoTateAux σ ∘ rhoTateAux τ`. On each
coordinate this is `galoisPointHom_mul`. -/
theorem rhoTateAux_mul (σ τ : F ≃ₐ[K] F) :
    rhoTateAux W₀ ℓ (σ * τ) = (rhoTateAux W₀ ℓ σ).comp (rhoTateAux W₀ ℓ τ) :=
  LinearMap.ext fun f ↦ Subtype.ext (funext fun n ↦
    Subtype.ext (galoisPointHom_mul W₀ σ τ (f.val n).val))

omit [DecidableEq K] [IsAlgClosed F] in
/-- `rhoTateAux 1 = id`: the identity automorphism acts trivially. On each coordinate this is
`galoisPointHom_one`. -/
theorem rhoTateAux_one :
    rhoTateAux W₀ ℓ (1 : F ≃ₐ[K] F) = LinearMap.id :=
  LinearMap.ext fun f ↦ Subtype.ext (funext fun n ↦
    Subtype.ext (galoisPointHom_one W₀ (f.val n).val))

/-- **L12.** The Galois action of `σ : F ≃ₐ[K] F` on the Tate module `T_ℓ(E)`, as a `ℤ_[ℓ]`-linear
**equivalence**. It is `rhoTateAux σ`, with inverse `rhoTateAux σ⁻¹`: the two compose to
`rhoTateAux (σ * σ⁻¹) = rhoTateAux 1 = id` (and symmetrically), by `rhoTateAux_mul` and
`rhoTateAux_one`. -/
noncomputable def rhoTate (σ : F ≃ₐ[K] F) :
    tateModule (W₀.baseChange F) ℓ ≃ₗ[ℤ_[ℓ]] tateModule (W₀.baseChange F) ℓ :=
  LinearEquiv.ofLinear (rhoTateAux W₀ ℓ σ) (rhoTateAux W₀ ℓ σ⁻¹)
    (by rw [← rhoTateAux_mul, mul_inv_cancel, rhoTateAux_one])
    (by rw [← rhoTateAux_mul, inv_mul_cancel, rhoTateAux_one])

omit [DecidableEq K] [IsAlgClosed F] in
@[simp] theorem rhoTate_apply (σ : F ≃ₐ[K] F) (f : tateModule (W₀.baseChange F) ℓ) :
    rhoTate W₀ ℓ σ f = rhoTateAux W₀ ℓ σ f := rfl

end RhoTate

/-! ## L13 — `ρ_ℓ` as a group homomorphism -/

section RhoHom

omit [DecidableEq K] [IsAlgClosed F] in
/-- `rhoTate (σ * τ) = rhoTate σ * rhoTate τ` (the group `M ≃ₗ M` has `(f * g) x = f (g x)`).
This is `rhoTateAux_mul` repackaged on the `LinearEquiv` level. -/
theorem rhoTate_mul (σ τ : F ≃ₐ[K] F) :
    rhoTate W₀ ℓ (σ * τ) = rhoTate W₀ ℓ σ * rhoTate W₀ ℓ τ :=
  LinearEquiv.toLinearMap_injective (rhoTateAux_mul W₀ ℓ σ τ)

omit [DecidableEq K] [IsAlgClosed F] in
/-- `rhoTate 1 = 1` (the identity automorphism). This is `rhoTateAux_one` repackaged on the
`LinearEquiv` level. -/
theorem rhoTate_one : rhoTate W₀ ℓ (1 : F ≃ₐ[K] F) = 1 :=
  LinearEquiv.toLinearMap_injective (rhoTateAux_one W₀ ℓ)

/-- **L13.** The **ℓ-adic representation** `ρ_ℓ : Gal(F/K) → Aut_{ℤ_[ℓ]}(T_ℓ(E))` of the elliptic
curve `E = W₀.baseChange F`, as a group homomorphism (Silverman III.7, Definition). The
multiplicativity (`map_one`/`map_mul`) is the functoriality of the Galois action
(`rhoTate_one`/`rhoTate_mul`), itself coming from `Affine.Point.map_id`/`map_map`. -/
noncomputable def rhoTateHom :
    (F ≃ₐ[K] F) →* (tateModule (W₀.baseChange F) ℓ ≃ₗ[ℤ_[ℓ]] tateModule (W₀.baseChange F) ℓ) where
  toFun := rhoTate W₀ ℓ
  map_one' := rhoTate_one W₀ ℓ
  map_mul' := rhoTate_mul W₀ ℓ

omit [DecidableEq K] [IsAlgClosed F] in
@[simp] theorem rhoTateHom_apply (σ : F ≃ₐ[K] F) :
    rhoTateHom W₀ ℓ σ = rhoTate W₀ ℓ σ := rfl

end RhoHom

/-! ## L14 — The `GL₂(ℤ_[ℓ])` form (Silverman, Remark 7.2) -/

section RhoGL

variable (hℓF : (ℓ : F) ≠ 0)

/-- The multiplicative equivalence `Aut_{ℤ_[ℓ]}(T_ℓ(E)) ≃* GL₂(ℤ_[ℓ])` induced by the chosen
`ℤ_[ℓ]`-basis isomorphism `tateModuleEquiv : T_ℓ(E) ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])` (Prop 7.1a). It is
the composite: identify the automorphism group with the unit group `GeneralLinearGroup` of the
module (`generalLinearEquiv`), conjugate it across `tateModuleEquiv` (`congrLinearEquiv`), and
identify the unit group of `Fin 2 → ℤ_[ℓ]` with the matrix group `GL (Fin 2) ℤ_[ℓ]`
(`Matrix.GeneralLinearGroup.toLin`). -/
noncomputable def tateAutEquivGL :
    (tateModule (W₀.baseChange F) ℓ ≃ₗ[ℤ_[ℓ]] tateModule (W₀.baseChange F) ℓ) ≃*
      GL (Fin 2) ℤ_[ℓ] :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ_[ℓ]
        (tateModule (W₀.baseChange F) ℓ)).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv
        (tateModuleEquiv (W₀.baseChange F) ℓ hℓF)).trans
      Matrix.GeneralLinearGroup.toLin.symm)

/-- **L14 (Silverman, Remark 7.2).** The `GL₂` form of the ℓ-adic representation:
`ρ_ℓ : Gal(F/K) → GL₂(ℤ_[ℓ])`. It is `rhoTateHom` post-composed with the basis identification
`tateAutEquivGL`, after choosing the `ℤ_[ℓ]`-basis of `T_ℓ(E)` from `tateModuleEquiv`. -/
noncomputable def rhoTateGL : (F ≃ₐ[K] F) →* GL (Fin 2) ℤ_[ℓ] :=
  (tateAutEquivGL W₀ ℓ hℓF).toMonoidHom.comp (rhoTateHom W₀ ℓ)

end RhoGL

end HasseWeil.TateModule
