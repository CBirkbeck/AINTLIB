import HasseWeil.Curves.BaseChange
import HasseWeil.Curves.Divisors

/-!
# Galois action on points and divisors

For a smooth plane curve `C` over a field `F` and an `F`-algebra `L`, the
Galois group `L ≃ₐ[F] L` acts on:

1. The `L`-rational points `C.pointsOver L = (C.baseChange L).SmoothPoint`
   by acting on coordinates;
2. The divisor group `Divisor (C.baseChange L)` by permuting points
   (via `Finsupp.mapDomain`).

A divisor `D` is **defined over `F`** if it is fixed by every such σ.

This closes Stream-A infrastructure tickets T-II-INFRA-C-003, C-004, C-005,
and unblocks T-II-3-004 (Galois action on divisors).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.3 (Galois action
  on `Div(C)`)
-/

open WeierstrassCurve

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)
variable (L : Type*) [Field L] [Algebra F L]

/-- For an `F`-algebra automorphism `σ : L ≃ₐ[F] L`, the base-changed
curve `C.baseChange L` is fixed by `σ`'s coefficient map. -/
theorem baseChange_map_AlgEquiv (σ : L ≃ₐ[F] L) :
    (C.baseChange L).toAffine.map (σ : L →+* L) = (C.baseChange L).toAffine := by
  ext <;> simp [WeierstrassCurve.map, AlgEquiv.commutes]

/-- The image of a point under an `F`-algebra automorphism: `σ` acts on
coordinates `(x, y) ↦ (σ x, σ y)`. Preservation of nonsingularity follows
from `WeierstrassCurve.Affine.map_nonsingular`. -/
noncomputable def mapPoint (σ : L ≃ₐ[F] L) (P : C.pointsOver L) :
    C.pointsOver L where
  x := σ P.x
  y := σ P.y
  nonsingular :=
    C.baseChange_map_AlgEquiv L σ ▸
      (Affine.map_nonsingular (W := (C.baseChange L).toAffine)
        (f := (σ : L →+* L)) (x := P.x) (y := P.y) σ.injective).mpr P.nonsingular

@[simp] theorem mapPoint_x (σ : L ≃ₐ[F] L) (P : C.pointsOver L) :
    (C.mapPoint L σ P).x = σ P.x := rfl

@[simp] theorem mapPoint_y (σ : L ≃ₐ[F] L) (P : C.pointsOver L) :
    (C.mapPoint L σ P).y = σ P.y := rfl

/-- The Galois group `L ≃ₐ[F] L` acts on `C.pointsOver L` by acting on
coordinates. Reference: Silverman I.2 (Galois action on projective space
specialized to an affine smooth curve). -/
noncomputable instance : MulAction (L ≃ₐ[F] L) (C.pointsOver L) where
  smul σ P := C.mapPoint L σ P
  one_smul P := by
    ext
    · exact AlgEquiv.one_apply _
    · exact AlgEquiv.one_apply _
  mul_smul σ τ P := by
    ext
    · exact AlgEquiv.mul_apply σ τ P.x
    · exact AlgEquiv.mul_apply σ τ P.y

@[simp] theorem smul_x (σ : L ≃ₐ[F] L) (P : C.pointsOver L) :
    (σ • P).x = σ P.x := rfl

@[simp] theorem smul_y (σ : L ≃ₐ[F] L) (P : C.pointsOver L) :
    (σ • P).y = σ P.y := rfl

/-! ### Galois action on divisors -/

/-- Induced Galois action on divisors: `(Σ n_P (P))^σ = Σ n_P (P^σ)`.
Reference: Silverman II.3 (definition). -/
noncomputable instance divisor_mulAction :
    MulAction (L ≃ₐ[F] L) (Divisor (C.baseChange L)) where
  smul σ D := D.mapDomain (σ • ·)
  one_smul D := by
    change Finsupp.mapDomain ((1 : L ≃ₐ[F] L) • ·) D = D
    simp only [one_smul]
    exact Finsupp.mapDomain_id
  mul_smul σ τ D := by
    change Finsupp.mapDomain ((σ * τ) • ·) D =
      Finsupp.mapDomain (σ • ·) (Finsupp.mapDomain (τ • ·) D)
    rw [show (fun P => (σ * τ) • P) = (σ • ·) ∘ (τ • ·) from by
      funext P; exact mul_smul σ τ P, Finsupp.mapDomain_comp]

/-- A divisor `D` on the base change `C_L` is **defined over `F`** if it is
fixed by the Galois action. Reference: Silverman II.3 (p.27, discussion
after `Div⁰(C)` definition). -/
def _root_.HasseWeil.Curves.Divisor.IsDefinedOverF
    {F} [Field F] {C : SmoothPlaneCurve F}
    {L} [Field L] [Algebra F L]
    (D : Divisor (C.baseChange L)) : Prop :=
  ∀ σ : L ≃ₐ[F] L, σ • D = D

/-- The action of `σ` on divisors is an `AddMonoidHom`. -/
noncomputable def smulDivisorHom (σ : L ≃ₐ[F] L) :
    Divisor (C.baseChange L) →+ Divisor (C.baseChange L) :=
  Finsupp.mapDomain.addMonoidHom (σ • ·)

theorem smul_divisor_eq_hom (σ : L ≃ₐ[F] L) (D : Divisor (C.baseChange L)) :
    σ • D = C.smulDivisorHom L σ D := rfl

/-- The `F`-defined divisors form an additive subgroup of
`Divisor (C.baseChange L)`.
Reference: Silverman II.3 (`Div_K(C)`). -/
noncomputable def divisorF : AddSubgroup (Divisor (C.baseChange L)) where
  carrier := {D | D.IsDefinedOverF}
  add_mem' {D₁ D₂} h₁ h₂ σ := by
    rw [smul_divisor_eq_hom, map_add, ← smul_divisor_eq_hom, ← smul_divisor_eq_hom,
      h₁ σ, h₂ σ]
  zero_mem' σ := by rw [smul_divisor_eq_hom, map_zero]
  neg_mem' {D} hD σ := by
    rw [smul_divisor_eq_hom, map_neg, ← smul_divisor_eq_hom, hD σ]

theorem mem_divisorF_iff (D : Divisor (C.baseChange L)) :
    D ∈ C.divisorF L ↔ D.IsDefinedOverF := Iff.rfl

end SmoothPlaneCurve

end HasseWeil.Curves
