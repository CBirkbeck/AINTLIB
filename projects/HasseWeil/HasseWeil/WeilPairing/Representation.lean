/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TorsionModule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace

/-!
# The mod-`ℓ` matrix representation `ρ_ℓ` of endomorphisms

For `ℓ` prime, `F` algebraically closed with `(ℓ : F) ≠ 0` (i.e. `ℓ ≠ char F`), the geometric
`ℓ`-torsion `E[ℓ] = W.toAffine[(ℓ : ℤ)]` is a `2`-dimensional `ZMod ℓ`-vector space
(`HasseWeil.WeilPairing.TorsionGeometric.torsion_ell_linearEquiv`).

This file builds the matrix representation
`ρ_ℓ : End(E) → GL₂(ZMod ℓ)` (Silverman III.7, III.8) on this torsion, the input to the
characteristic-polynomial / Hasse-bound endgame. Concretely, for an additive endomorphism
`ψ : E.Point →+ E.Point` (every isogeny — in particular Frobenius and `[n]` — is such a hom):

* `torsionRestrict ψ` — the restriction of `ψ` to `E[ℓ]`, as a `ZMod ℓ`-**linear** map.
  Linearity is free: `ψ` preserves `E[ℓ]` (it commutes with `[ℓ] = ℓ • ·`), it is additive, and
  the `ZMod ℓ`-scalar action on `E[ℓ]` is the natural-number `•`, which every `AddMonoidHom`
  commutes with (`ZMod.map_smul`).
* `rhoEll ψ` — the `Matrix (Fin 2) (Fin 2) (ZMod ℓ)` of `torsionRestrict ψ` in the chosen basis
  `torsion_ell_basis`, via `LinearMap.toMatrix`.

The structural identities are the substance for the trace/determinant endgame:

* `rhoEll_comp` — `ρ_ℓ(ψ₁ ∘ ψ₂) = ρ_ℓ(ψ₁) · ρ_ℓ(ψ₂)` (multiplicativity, `LinearMap.toMatrix_comp`);
* `rhoEll_id` — `ρ_ℓ(id) = 1`;
* `rhoEll_add` — `ρ_ℓ(ψ₁ + ψ₂) = ρ_ℓ(ψ₁) + ρ_ℓ(ψ₂)` (`LinearMap.toMatrix` is a `LinearEquiv`);
* `rhoEll_mulByInt` — `ρ_ℓ([n]) = (n : ZMod ℓ) • 1` (scalar matrices), since `[n]` acts as `n • ·`;
* `rhoEll_det` — `det (ρ_ℓ(ψ)) = LinearMap.det (torsionRestrict ψ)` (`LinearMap.det_toMatrix`);
* `rhoEll_trace` — `trace (ρ_ℓ(ψ)) = LinearMap.trace … (torsionRestrict ψ)`
  (`LinearMap.trace_eq_matrix_trace`).

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.7–8, V.2.
-/

open WeierstrassCurve Matrix

namespace HasseWeil.WeilPairing.TorsionGeometric

open HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [IsAlgClosed F] (hℓF : (ℓ : F) ≠ 0)

section TorsionRestrict

-- The torsion-restriction machinery is characteristic-agnostic: it never uses `[IsAlgClosed F]`
-- (only the `ZMod ℓ`-module structure on `E[ℓ]`, and that `ψ` is an `AddMonoidHom`).
omit [IsAlgClosed F]

omit hℓ in
/-- An additive endomorphism `ψ` of `E.Point` preserves the `ℓ`-torsion `E[ℓ]`: if `ℓ • P = 0`
then `ℓ • ψ P = ψ (ℓ • P) = ψ 0 = 0`. (Uses only that `ψ` is an `AddMonoidHom`; it commutes with
`ℓ • ·`.) -/
theorem map_mem_torsion_ell (ψ : W.toAffine.Point →+ W.toAffine.Point)
    {P : W.toAffine.Point} (hP : P ∈ W.toAffine[(ℓ : ℤ)]) :
    ψ P ∈ W.toAffine[(ℓ : ℤ)] := by
  rw [mem_torsionSubgroup] at hP ⊢
  rw [← map_zsmul ψ, hP, map_zero]

/-- The restriction of an additive endomorphism `ψ : E.Point →+ E.Point` to the `ℓ`-torsion
`E[ℓ]`, as an `AddMonoidHom E[ℓ] →+ E[ℓ]`.

This is `ψ` composed with the inclusion `E[ℓ] ↪ E.Point`, co-restricted back into `E[ℓ]` using
`map_mem_torsion_ell`. -/
noncomputable def torsionRestrictHom (ψ : W.toAffine.Point →+ W.toAffine.Point) :
    W.toAffine[(ℓ : ℤ)] →+ W.toAffine[(ℓ : ℤ)] :=
  (ψ.comp (W.toAffine[(ℓ : ℤ)]).subtype).codRestrict _
    (fun P => map_mem_torsion_ell W ℓ ψ P.property)

omit hℓ in
@[simp] theorem torsionRestrictHom_coe (ψ : W.toAffine.Point →+ W.toAffine.Point)
    (P : W.toAffine[(ℓ : ℤ)]) :
    (torsionRestrictHom W ℓ ψ P : W.toAffine.Point) = ψ P := rfl

/-- **The `ZMod ℓ`-linear restriction of `ψ` to `E[ℓ]`.** Every additive endomorphism of `E.Point`
preserves `E[ℓ]` and the resulting map is automatically `ZMod ℓ`-linear, because the `ZMod ℓ`-scalar
action on `E[ℓ]` is the natural-number `•` action, with which every `AddMonoidHom` commutes
(`ZMod.map_smul`). -/
noncomputable def torsionRestrict (ψ : W.toAffine.Point →+ W.toAffine.Point) :
    W.toAffine[(ℓ : ℤ)] →ₗ[ZMod ℓ] W.toAffine[(ℓ : ℤ)] :=
  (torsionRestrictHom W ℓ ψ).toZModLinearMap ℓ

@[simp] theorem torsionRestrict_apply (ψ : W.toAffine.Point →+ W.toAffine.Point)
    (P : W.toAffine[(ℓ : ℤ)]) :
    (torsionRestrict W ℓ ψ P : W.toAffine.Point) = ψ P := rfl

/-- `torsionRestrict` respects composition. -/
theorem torsionRestrict_comp (ψ₁ ψ₂ : W.toAffine.Point →+ W.toAffine.Point) :
    torsionRestrict W ℓ (ψ₁.comp ψ₂) =
      (torsionRestrict W ℓ ψ₁).comp (torsionRestrict W ℓ ψ₂) := by
  ext P; rfl

/-- `torsionRestrict` of the identity is the identity. -/
theorem torsionRestrict_id :
    torsionRestrict W ℓ (AddMonoidHom.id W.toAffine.Point) = LinearMap.id := by
  ext P; rfl

/-- `torsionRestrict` is additive in `ψ`. -/
theorem torsionRestrict_add (ψ₁ ψ₂ : W.toAffine.Point →+ W.toAffine.Point) :
    torsionRestrict W ℓ (ψ₁ + ψ₂) = torsionRestrict W ℓ ψ₁ + torsionRestrict W ℓ ψ₂ := by
  ext P; rfl

/-- `torsionRestrict` of `[n] = n • ·` is multiplication by the scalar `(n : ZMod ℓ)`. The
`ZMod ℓ`-scalar `(n : ZMod ℓ)` agrees with the `ℤ`-action `n • ·` on any `ZMod ℓ`-module
(`Int.cast_smul_eq_zsmul`). -/
theorem torsionRestrict_zsmul (n : ℤ) :
    torsionRestrict W ℓ (zsmulAddGroupHom n) = (n : ZMod ℓ) • LinearMap.id := by
  refine LinearMap.ext fun P => ?_
  -- LHS acts as the `ℤ`-action `n • P`; RHS is the `ZMod ℓ`-scalar `(n : ZMod ℓ) • P`.
  change torsionRestrict W ℓ (zsmulAddGroupHom n) P = (n : ZMod ℓ) • P
  rw [Int.cast_smul_eq_zsmul]
  rfl

end TorsionRestrict

section Rho

/-- **The mod-`ℓ` matrix representation** `ρ_ℓ(ψ) ∈ M₂(ZMod ℓ)` of an additive endomorphism
`ψ : E.Point →+ E.Point`: the matrix of the `ZMod ℓ`-linear map `torsionRestrict ψ` on `E[ℓ]` in
the chosen `Fin 2`-basis `torsion_ell_basis`. (Silverman III.7.) -/
noncomputable def rhoEll (ψ : W.toAffine.Point →+ W.toAffine.Point) :
    Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
  LinearMap.toMatrix (torsion_ell_basis W ℓ hℓF) (torsion_ell_basis W ℓ hℓF)
    (torsionRestrict W ℓ ψ)

/-- **Multiplicativity / `map_mul`**: `ρ_ℓ(ψ₁ ∘ ψ₂) = ρ_ℓ(ψ₁) · ρ_ℓ(ψ₂)`. The matrix of a
composite of linear maps is the product of the matrices (`LinearMap.toMatrix_comp`). -/
theorem rhoEll_comp (ψ₁ ψ₂ : W.toAffine.Point →+ W.toAffine.Point) :
    rhoEll W ℓ hℓF (ψ₁.comp ψ₂) = rhoEll W ℓ hℓF ψ₁ * rhoEll W ℓ hℓF ψ₂ := by
  simp only [rhoEll, torsionRestrict_comp,
    LinearMap.toMatrix_comp (torsion_ell_basis W ℓ hℓF) (torsion_ell_basis W ℓ hℓF)
      (torsion_ell_basis W ℓ hℓF)]

/-- **`map_one`**: `ρ_ℓ(id) = 1`. The identity endomorphism has the identity matrix
(`LinearMap.toMatrix_id`). -/
theorem rhoEll_id :
    rhoEll W ℓ hℓF (AddMonoidHom.id W.toAffine.Point) = 1 := by
  rw [rhoEll, torsionRestrict_id, ← LinearMap.toMatrix_id (torsion_ell_basis W ℓ hℓF)]

/-- **`map_add`**: `ρ_ℓ(ψ₁ + ψ₂) = ρ_ℓ(ψ₁) + ρ_ℓ(ψ₂)`. `LinearMap.toMatrix` is a linear
equivalence, hence additive, and `torsionRestrict` is additive in `ψ`. -/
theorem rhoEll_add (ψ₁ ψ₂ : W.toAffine.Point →+ W.toAffine.Point) :
    rhoEll W ℓ hℓF (ψ₁ + ψ₂) = rhoEll W ℓ hℓF ψ₁ + rhoEll W ℓ hℓF ψ₂ := by
  rw [rhoEll, torsionRestrict_add, map_add]
  rfl

/-- **The scalar values** `ρ_ℓ([n]) = (n : ZMod ℓ) • 1`. Multiplication-by-`n` acts as the scalar
`(n : ZMod ℓ)` on the `ZMod ℓ`-module `E[ℓ]`, so its matrix is `n` times the identity. This is the
key input to the trace/determinant computation of the Hasse endgame: `tr ρ_ℓ([n]) = 2n`,
`det ρ_ℓ([n]) = n²`. -/
theorem rhoEll_zsmulAddGroupHom (n : ℤ) :
    rhoEll W ℓ hℓF (zsmulAddGroupHom n) = (n : ZMod ℓ) • 1 := by
  rw [rhoEll, torsionRestrict_zsmul, map_smul, LinearMap.toMatrix_id]

/-- **`ρ_ℓ([n]) = (n : ZMod ℓ) • 1`**, stated for the multiplication-by-`n` isogeny `mulByInt W n`.
Its underlying point map is `zsmulAddGroupHom n`, so this is `rhoEll_zsmulAddGroupHom`. -/
theorem rhoEll_mulByInt (n : ℤ) :
    rhoEll W ℓ hℓF (mulByInt W.toAffine n).toAddMonoidHom = (n : ZMod ℓ) • 1 :=
  rhoEll_zsmulAddGroupHom W ℓ hℓF n

end Rho

section DetTrace

/-- **`det` compatibility**: `det (ρ_ℓ(ψ)) = LinearMap.det (torsionRestrict ψ)`. The matrix
determinant in any basis equals the intrinsic linear-map determinant
(`LinearMap.det_toMatrix`). This bridges the matrix `ρ_ℓ` to the basis-free determinant used in the
degree = `det` step (Silverman III.8.6). -/
theorem rhoEll_det (ψ : W.toAffine.Point →+ W.toAffine.Point) :
    (rhoEll W ℓ hℓF ψ).det = LinearMap.det (torsionRestrict W ℓ ψ) :=
  LinearMap.det_toMatrix (torsion_ell_basis W ℓ hℓF) (torsionRestrict W ℓ ψ)

/-- **`trace` compatibility**: `trace (ρ_ℓ(ψ)) = LinearMap.trace … (torsionRestrict ψ)`. The matrix
trace in any basis equals the intrinsic linear-map trace (`LinearMap.trace_eq_matrix_trace`). This
bridges the matrix `ρ_ℓ` to the basis-free trace used in the `tr π = a` step (Silverman III.8.6). -/
theorem rhoEll_trace (ψ : W.toAffine.Point →+ W.toAffine.Point) :
    (rhoEll W ℓ hℓF ψ).trace =
      LinearMap.trace (ZMod ℓ) W.toAffine[(ℓ : ℤ)] (torsionRestrict W ℓ ψ) :=
  (LinearMap.trace_eq_matrix_trace (ZMod ℓ) (torsion_ell_basis W ℓ hℓF)
    (torsionRestrict W ℓ ψ)).symm

end DetTrace

end HasseWeil.WeilPairing.TorsionGeometric
