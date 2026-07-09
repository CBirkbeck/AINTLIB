import ModularCurves.ForMathlib.Coaction
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The shear automorphism of a Hopf co-action

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B1]`): the algebra automorphism
of `B ⊗[R] A` dual to the shear `(x, g) ↦ (g·x, g)` of `X ×_S G` — the map trivializing
the translation groupoid over itself (Stacks `groupoids-lemma-diagram-pull`, the
`(α, β) ↦ (α, α⁻¹β)` bijection). Concretely

* `coactionShear ρ : B ⊗[R] A →ₐ[R] B ⊗[R] A`, `b ⊗ a ↦ ρ(b)·(1 ⊗ a)`, with
  `coactionShear_comp_includeLeft : Φ ∘ (b ↦ b⊗1) = ρ` — the *shear trivialization*: the
  `ρ`-twisted inclusion becomes the plain inclusion after composing with `Φ`;
* `coactionUnshear ρ` — the inverse, built from the antipode
  (`HopfAlgebra.antipodeAlgHom`, `A` commutative);
* `coactionShearEquiv ρ : B ⊗[R] A ≃ₐ[R] B ⊗[R] A` — the packaged automorphism, given
  `IsCoaction ρ`.

All proofs are `AlgHom`-composite identities through `Algebra.TensorProduct.{map, assoc}`
— no Sweedler sums: coassociativity enters verbatim in the form stored in `IsCoaction`,
the antipode axioms in the `AlgHom` forms derived from
`HopfAlgebra.mul_antipode_{r,l}Tensor_comul`, and counitality via `IsCoaction.counit`.

Downstream (`[HG-B2]`, `[HG-B5]`) this transports every `ρ`-side structure on `B ⊗[R] A`
(module structure, freeness, faithful flatness) to the plain left-factor structure — the
"only left instances" design pin of the charter.
-/

open scoped TensorProduct

namespace ModularCurves

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- The multiplication-after-antipode map `A ⊗[R] A →ₐ[R] A`, `a ⊗ a' ↦ S(a)·a'`. The
composite `mulAntipode ∘ Δ` is `unit ∘ counit` — the antipode axiom in algebra-map form
(`mulAntipode_comp_comulAlgHom`). -/
noncomputable def mulAntipode : (A ⊗[R] A) →ₐ[R] A :=
  Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R A) (AlgHom.id R A)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem mulAntipode_tmul (a a' : A) :
    mulAntipode R A (a ⊗ₜ[R] a') = HopfAlgebra.antipode R a * a' := rfl

/-- The symmetric variant `a ⊗ a' ↦ a·S(a')`. -/
noncomputable def mulAntipodeRight : (A ⊗[R] A) →ₐ[R] A :=
  Algebra.TensorProduct.lift (AlgHom.id R A) (HopfAlgebra.antipodeAlgHom R A)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem mulAntipodeRight_tmul (a a' : A) :
    mulAntipodeRight R A (a ⊗ₜ[R] a') = a * HopfAlgebra.antipode R a' := rfl

/-- **The antipode axiom, algebra-map form**: `S(a₍₁₎)·a₍₂₎ = ε(a)·1` as an identity of
algebra maps `A → A`, i.e. `mulAntipode ∘ Δ = unit ∘ ε`. -/
theorem mulAntipode_comp_comulAlgHom :
    (mulAntipode R A).comp (Bialgebra.comulAlgHom R A)
      = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  apply AlgHom.toLinearMap_injective
  have hlin : (mulAntipode R A).toLinearMap
      = (LinearMap.mul' R A) ∘ₗ (LinearMap.rTensor A (HopfAlgebra.antipode R)) := by
    ext a a'
    simp
  ext a
  simp [hlin]

/-- **The other antipode axiom, algebra-map form**: `a₍₁₎·S(a₍₂₎) = ε(a)·1`. -/
theorem mulAntipodeRight_comp_comulAlgHom :
    (mulAntipodeRight R A).comp (Bialgebra.comulAlgHom R A)
      = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A) := by
  apply AlgHom.toLinearMap_injective
  have hlin : (mulAntipodeRight R A).toLinearMap
      = (LinearMap.mul' R A) ∘ₗ (LinearMap.lTensor A (HopfAlgebra.antipode R)) := by
    ext a a'
    simp
  ext a
  simp [hlin]

variable {R A}
variable {B : Type*} [CommRing B] [Algebra R B]

/-- **The shear endomorphism** `Φ : B ⊗[R] A → B ⊗[R] A`, `b ⊗ a ↦ ρ(b)·(1 ⊗ a)` — the
structure-sheaf dual of `(x, g) ↦ (g·x, g)`. Its defining property is
`coactionShear_comp_includeLeft : Φ ∘ includeLeft = ρ`. -/
noncomputable def coactionShear (ρ : B →ₐ[R] B ⊗[R] A) : (B ⊗[R] A) →ₐ[R] B ⊗[R] A :=
  Algebra.TensorProduct.lift ρ Algebra.TensorProduct.includeRight
    (fun _ _ => Commute.all _ _)

@[simp]
theorem coactionShear_tmul (ρ : B →ₐ[R] B ⊗[R] A) (b : B) (a : A) :
    coactionShear ρ (b ⊗ₜ[R] a) = ρ b * (1 ⊗ₜ[R] a) := rfl

/-- The shear trivialization: composing the plain inclusion with the shear recovers the
co-action. This is the identity that transports `ρ`-side structure to left-side
structure. -/
theorem coactionShear_comp_includeLeft (ρ : B →ₐ[R] B ⊗[R] A) :
    (coactionShear ρ).comp Algebra.TensorProduct.includeLeft = ρ :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

theorem coactionShear_comp_includeRight (ρ : B →ₐ[R] B ⊗[R] A) :
    (coactionShear ρ).comp Algebra.TensorProduct.includeRight
      = Algebra.TensorProduct.includeRight :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

/-- **The inverse shear** `Ψ : b ⊗ a ↦ ρ(b)·(1 ⊗ S(a))`... realized as the composite
`(id ⊗ (S(·)·(·))) ∘ assoc ∘ (ρ ⊗ id)`, i.e. `b ⊗ a ↦ b₍₀₎ ⊗ S(b₍₁₎)·a` — the dual of
`(x, g) ↦ (g⁻¹·x, g)`. -/
noncomputable def coactionUnshear (ρ : B →ₐ[R] B ⊗[R] A) : (B ⊗[R] A) →ₐ[R] B ⊗[R] A :=
  ((Algebra.TensorProduct.map (AlgHom.id R B) (mulAntipode R A)).comp
    (Algebra.TensorProduct.assoc R R R B A A).toAlgHom).comp
    (Algebra.TensorProduct.map ρ (AlgHom.id R A))

section InverseLaws

variable (ρ : B →ₐ[R] B ⊗[R] A)

/-- The associator sends the left inclusion of `(B ⊗ A) ⊗ A` to `id ⊗ includeLeft`. -/
private theorem assoc_toAlgHom_comp_includeLeft :
    (Algebra.TensorProduct.assoc R R R B A A).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (S := R))
      = Algebra.TensorProduct.map (AlgHom.id R B)
          (Algebra.TensorProduct.includeLeft (S := R)) := by
  ext
  · rfl
  · rfl

/-- The counit key: tensoring with `unit ∘ ε` on the right is the left inclusion after the
counitality contraction. -/
private theorem map_ofId_counit_eq :
    Algebra.TensorProduct.map (AlgHom.id R B)
        ((Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
      = (Algebra.TensorProduct.includeLeft (S := R)).comp
          ((Algebra.TensorProduct.rid R R B).toAlgHom.comp
            (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R A))) := by
  refine Algebra.TensorProduct.ext ?_ ?_
  · ext b
    simp
  · ext a
    show (1 : B) ⊗ₜ[R] algebraMap R A (Bialgebra.counitAlgHom R A a)
        = (Algebra.TensorProduct.rid R R B) ((1 : B) ⊗ₜ[R] (Bialgebra.counitAlgHom R A a))
          ⊗ₜ[R] (1 : A)
    rw [Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- **The inverse shear undoes the co-action**: `Ψ ∘ ρ = includeLeft`, i.e.
`b₍₀₎ ⊗ S(b₍₀₎₍₁₎)·b₍₁₎ = b ⊗ 1`. The chain: coassociativity turns `assoc ∘ (ρ⊗id) ∘ ρ`
into `(id ⊗ Δ) ∘ ρ`, the antipode axiom collapses `mulAntipode ∘ Δ` to `unit ∘ ε`, and
counitality contracts the rest. -/
theorem coactionUnshear_comp_coaction (hρ : IsCoaction ρ) :
    (coactionUnshear ρ).comp ρ = Algebra.TensorProduct.includeLeft := by
  rw [coactionUnshear, AlgHom.comp_assoc, AlgHom.comp_assoc, hρ.coassoc,
    ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id,
    mulAntipode_comp_comulAlgHom, map_ofId_counit_eq, AlgHom.comp_assoc,
    AlgHom.comp_assoc, hρ.counit, AlgHom.comp_id]

/-- The inverse shear fixes the right inclusion. -/
theorem coactionUnshear_comp_includeRight :
    (coactionUnshear ρ).comp Algebra.TensorProduct.includeRight
      = Algebra.TensorProduct.includeRight := by
  ext a
  show coactionUnshear ρ ((1 : B) ⊗ₜ[R] a) = (1 : B) ⊗ₜ[R] a
  simp [coactionUnshear, Algebra.TensorProduct.one_def]

end InverseLaws

end ModularCurves
