/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Coefficient systems for modular symbols

This file constructs the two foundational `SL(2, ℤ)`-representations underlying the integral
modular-symbol substrate.

## Main definitions

* `HeckeRing.GL2.ModularSymbols.symRep R m` : the symmetric-power coefficient system, i.e. the
  representation of `SL(2, ℤ)` on `SymPow R m`, the homogeneous degree-`m` polynomials in two
  variables.  For weight `k`, the relevant value is `m = k - 2`.  A matrix `g` acts by the linear
  substitution `Xᵢ ↦ ∑ⱼ (g⁻¹)ᵢⱼ • Xⱼ` (i.e. `(g · P)(v) = P(g⁻¹ v)`), the covariant left action.

* `HeckeRing.GL2.ModularSymbols.div0Rep R` : the representation of `SL(2, ℤ)` on `Div0 R`, the
  degree-0 divisors on `ℙ¹(ℚ)`.  It is the restriction of the permutation representation on
  `ℙ¹(ℚ) →₀ R` (induced from the `SL(2, ℤ)`-action on the projective line) to the augmentation
  kernel.

## Conventions

For `symRep`, the convention `(g · P)(v) = P(g⁻¹ v)`, i.e. `Xᵢ ↦ ∑ⱼ (g⁻¹)ᵢⱼ • Xⱼ`, is exactly the
one that makes `g ↦ ρ g` a *monoid* homomorphism (a left action): polynomial substitution is
contravariant, and the inverse flips it back to covariant.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups
open MvPolynomial

universe u

/-! ## `symRep` — the `Sym^m` coefficient system -/

/-- `Sym^m(R²)` modelled as homogeneous degree-`m` polynomials in two variables `X₀, X₁`.  Finite
free over `R` of rank `m + 1` (monomial basis `X₀ᵃ X₁ᵇ`, `a + b = m`). -/
abbrev SymPow (R : Type u) [CommRing R] (m : ℕ) : Submodule R (MvPolynomial (Fin 2) R) :=
  homogeneousSubmodule (Fin 2) R m

/-- The `R`-algebra endomorphism of `MvPolynomial (Fin 2) R` given by the linear substitution
`Xᵢ ↦ ∑ⱼ Mᵢⱼ • Xⱼ` attached to a matrix `M`. -/
noncomputable def substAlgHom {R : Type u} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval (fun i => ∑ j, M i j • X j)

@[simp]
theorem substAlgHom_X {R : Type u} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    substAlgHom M (X i) = ∑ j, M i j • X j := by
  simp [substAlgHom]

/-- `substAlgHom` of the identity matrix is the identity algebra hom. -/
theorem substAlgHom_one {R : Type u} [CommRing R] :
    substAlgHom (1 : Matrix (Fin 2) (Fin 2) R) = AlgHom.id R (MvPolynomial (Fin 2) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [substAlgHom_X]
  simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- Substitution is contravariant: `substAlgHom B ∘ substAlgHom A = substAlgHom (A * B)`. -/
theorem substAlgHom_comp {R : Type u} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (substAlgHom B).comp (substAlgHom A) = substAlgHom (A * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substAlgHom_X, map_sum, map_smul]
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

/-- Each variable image `∑ⱼ Mᵢⱼ • Xⱼ` under the substitution is homogeneous of degree `1`. -/
theorem substAlgHom_X_isHomogeneous {R : Type u} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (i : Fin 2) : ((∑ j, M i j • X j : MvPolynomial (Fin 2) R)).IsHomogeneous 1 := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun j _ => ?_)
  exact (MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem (M i j)
    (MvPolynomial.isHomogeneous_X R j)

/-- A linear substitution maps a homogeneous polynomial of degree `m` to a homogeneous polynomial
of degree `m`. -/
theorem substAlgHom_isHomogeneous {R : Type u} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)
    {p : MvPolynomial (Fin 2) R} {m : ℕ} (hp : p.IsHomogeneous m) :
    (substAlgHom M p).IsHomogeneous m := by
  have h2 := hp.aeval (fun i => ∑ j, M i j • X j) (substAlgHom_X_isHomogeneous M)
  rw [one_mul] at h2
  exact h2

/-- The integer matrix `(g⁻¹).1` of `g⁻¹ ∈ SL(2, ℤ)`, cast entrywise into `R`. -/
noncomputable def symMat (R : Type u) [CommRing R] (g : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) R :=
  (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R)

theorem symMat_one (R : Type u) [CommRing R] :
    symMat R (1 : SL(2, ℤ)) = 1 := by
  rw [symMat, inv_one, Matrix.SpecialLinearGroup.coe_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem symMat_mul (R : Type u) [CommRing R] (g h : SL(2, ℤ)) :
    symMat R (g * h) = symMat R h * symMat R g := by
  simp only [symMat, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul]
  exact (Int.castRingHom R).mapMatrix.map_mul _ _

/-- The `Sym^m` coefficient system: the representation of `SL(2, ℤ)` on the homogeneous degree-`m`
polynomials in two variables, where `g` acts by the covariant substitution `Xᵢ ↦ ∑ⱼ (g⁻¹)ᵢⱼ • Xⱼ`,
i.e. `(g · P)(v) = P(g⁻¹ v)`. -/
noncomputable def symRep (R : Type u) [CommRing R] (m : ℕ) :
    Representation R SL(2, ℤ) (SymPow R m) :=
  Representation.subrepresentation
    { toFun := fun g => (substAlgHom (symMat R g)).toLinearMap
      map_one' := by
        simp only [symMat_one, substAlgHom_one]
        rfl
      map_mul' := fun g h => by
        simp only [symMat_mul]
        rw [← substAlgHom_comp]
        rfl }
    (SymPow R m) <| by
  intro g x hx
  rw [Submodule.mem_comap]
  exact substAlgHom_isHomogeneous (symMat R g) hx

/-- The action of `symRep`, as a substitution on the underlying polynomial:
`g · P = P ∘ (g⁻¹ ·)`, i.e. `(symRep R m g P).val = substAlgHom (g⁻¹) P.val`. -/
@[simp]
theorem symRep_apply (R : Type u) [CommRing R] (m : ℕ) (g : SL(2, ℤ)) (P : SymPow R m) :
    ((symRep R m g P : SymPow R m) : MvPolynomial (Fin 2) R)
      = substAlgHom (symMat R g) (P : MvPolynomial (Fin 2) R) :=
  rfl

/-! ## `div0Rep` — divisors on `ℙ¹(ℚ)` -/

/-- Degree-0 divisors on `ℙ¹(ℚ)`: the kernel of the augmentation `R[ℙ¹ℚ] → R`.

The permutation representation `Representation.ofMulAction` lives on the `MonoidAlgebra`
`R[ℙ¹ℚ]`, so the augmentation submodule is expressed on that carrier via
`MonoidAlgebra.coeffLinearEquiv`; it is the same augmentation kernel as
`ker (Finsupp.linearCombination R (fun _ => 1))` on `ℙ¹ℚ →₀ R`, transported through the
coefficient equivalence (cf. `Representation.ker_leftRegular_norm_eq`). -/
noncomputable abbrev Div0 (R : Type u) [CommRing R] :
    Submodule R (MonoidAlgebra R (Projectivization ℚ (Fin 2 → ℚ))) :=
  LinearMap.ker (Finsupp.linearCombination R (fun _ => (1 : R)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)

noncomputable def div0Rep (R : Type u) [CommRing R] :
    Representation R SL(2, ℤ) (Div0 R) :=
  Representation.subrepresentation
    ((Representation.ofMulAction R SL(2, ℚ) (Projectivization ℚ (Fin 2 → ℚ))).comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ))) (Div0 R) <| by
  intro g x hx
  simp only [LinearMap.mem_ker, MonoidHom.comp_apply, Submodule.mem_comap,
    LinearMap.comp_apply, Representation.ofMulAction_def, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.lmapDomain_apply,
    Finsupp.linearCombination_mapDomain] at hx ⊢
  exact hx

/-- The action of `div0Rep`, as the permutation of cusps `(x) ↦ (g · x)` on the underlying
divisor: on coefficients, `(div0Rep R g D).coeff = Finsupp.mapDomain (g · ·) D.coeff`, where `g`
acts on `ℙ¹(ℚ)` through `SL(2, ℤ) → SL(2, ℚ)`.  (The permutation representation now lives on the
`MonoidAlgebra` carrier `R[ℙ¹ℚ]`, so the identity is stated on the `MonoidAlgebra.coeff` field.) -/
@[simp]
theorem div0Rep_apply (R : Type u) [CommRing R] (g : SL(2, ℤ)) (D : Div0 R) :
    ((div0Rep R g D : Div0 R) : MonoidAlgebra R (Projectivization ℚ (Fin 2 → ℚ))).coeff
      = Finsupp.mapDomain ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g) • ·)
          (D : MonoidAlgebra R (Projectivization ℚ (Fin 2 → ℚ))).coeff :=
  rfl

end HeckeRing.GL2.ModularSymbols
