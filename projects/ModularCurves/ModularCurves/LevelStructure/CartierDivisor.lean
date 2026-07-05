import ModularCurves.EllipticCurve.GroupLaw
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Relative effective Cartier divisors and full sets of sections (KM Ch. 1)

The substrate for Drinfeld level structures, transcribed from KM Ch. 1 (which the project
has in full, with proofs, via the KM preview: §§1.1–1.9).

* A **relative effective Cartier divisor** `D` in a curve `C/S` (KM 1.1–1.2). Official
  definition: a closed subscheme, flat over `S`, whose ideal sheaf is invertible. Mathlib
  has no invertible-ideal-sheaf API yet, so we take as *working definition* the
  characterisation in the relative-curve case (KM 1.2.3): a closed subscheme which is
  finite locally free over the base. The equivalence with the official definition, in the
  smooth-relative-curve case we use, is ticket `T-D1` (its statement needs the
  invertible-`O_C`-module API — API gap AG-LB in plan.md — and is recorded there, not
  here, to avoid a junk placeholder).

* A **full set of sections** (KM 1.8.2; working form from the proof of KM 1.9.1, verbatim:
  "The points `P₁,…,P_N` form a full set of sections of `Spec(B)/R` if and only if this
  universal `f` satisfies `Norm(f) = ∏ f(Pᵢ)`"). We state the affine case as an honest
  definition quantified over base changes (equivalent to KM's single universal case
  `A = R[T₁,…,T_N]`, by KM 1.8.4).

* The **divisor `Σᵢ [Pᵢ]` attached to a family of sections** (KM 1.2.2 for one section;
  sums of divisors via ideal products). The sum is a registered construction (DS4a,
  ticket `T-D3`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {C S : Scheme.{u}}

/-- A relative effective Cartier divisor in `C/S`, in the working form for relative curves
(KM 1.2.3): a closed subscheme of `C` (given by its ideal sheaf) which is finite, flat and
of finite presentation (= finite locally free) over `S`.

Official definition (KM 1.1.1): a closed subscheme `D ⊆ C`, flat over `S`, whose ideal
sheaf is an invertible `O_C`-module; equivalence in our situation: ticket `T-D1`
(blocked on API gap AG-LB). -/
structure RelEffCartierDiv (π : C ⟶ S) where
  /-- The ideal sheaf of the divisor. -/
  ideal : C.IdealSheafData
  finite : IsFinite (ideal.subschemeι ≫ π)
  flat : Flat (ideal.subschemeι ≫ π)
  lfp : LocallyOfFinitePresentation (ideal.subschemeι ≫ π)

namespace RelEffCartierDiv

variable {π : C ⟶ S}

/-- The degree of a relative effective Cartier divisor at `s : S` — the rank of the finite
locally free morphism `D ⟶ S` (KM 1.2; locally constant in `s`). -/
noncomputable def degree (D : RelEffCartierDiv π) (s : S) : ℕ :=
  haveI := D.finite
  haveI := D.flat
  (D.ideal.subschemeι ≫ π).finrank s

/-- **(DS4a, ticket T-D3)** The divisor `Σᵢ [Pᵢ]` attached to a finite family of sections
of `π` — the closed subscheme whose ideal is the *product* of the ideal sheaves of the
(closed-immersion) sections. DATA-SORRY (register entry DS4a). Specifications: degree `= n`
(`sectionsDivisor_degree`), and formation commutes with arbitrary base change (KM 1.1). -/
noncomputable def sectionsDivisor (π : C ⟶ S) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) : RelEffCartierDiv π := sorry

/-- **(T-D3a, specification of DS4a)** `Σᵢ [Pᵢ]` has degree `n`. Source: KM 1.2.2. -/
theorem sectionsDivisor_degree (π : C ⟶ S) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (s : S) :
    (sectionsDivisor π P).degree s = n := by sorry

end RelEffCartierDiv

section FullSections

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

open TensorProduct in
/-- The base change of a section `P : B →ₐ[R] R` to an `R`-algebra `A`, as a section
`A ⊗[R] B →ₐ[A] A`. -/
noncomputable def AlgHom.sectionBaseChange (A : Type u) [CommRing A] [Algebra R A]
    (P : B →ₐ[R] R) : A ⊗[R] B →ₐ[A] A :=
  ((Algebra.TensorProduct.rid R A A).toAlgHom).comp
    (Algebra.TensorProduct.map (AlgHom.id A A) P)

open TensorProduct in
/-- **Full set of sections, affine case** (KM 1.8.2; universal-norm form of KM 1.9.1).
`B` an `R`-algebra (finite locally free as `R`-module in applications), sections
`P₁, ⋯, Pₙ : B →ₐ[R] R`. They are a *full set of sections* of `Spec B / Spec R` if for
every `R`-algebra `A` and every `f ∈ A ⊗_R B`:
`Norm_{(A ⊗ B)/A}(f) = ∏ᵢ (Pᵢ)_A(f)`.

Verbatim source (proof of KM 1.9.1): "The points `P₁,…,P_N` form a full set of sections of
`Spec(B)/R` if and only if this universal `f` satisfies `Norm(f) = ∏ f(Pᵢ)` in
`R[T₁,…,T_N]`" — quantifying over all `A` is equivalent by base change (KM 1.8.4). -/
def IsFullSetOfSectionsAlg {n : ℕ} (P : Fin n → (B →ₐ[R] R)) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A],
    ∀ f : A ⊗[R] B,
      Algebra.norm A f = ∏ i, AlgHom.sectionBaseChange R B A (P i) f

/-- **(T-D2 = KM 1.9.2, verbatim source in hand with proof)** Over a *reduced* base, "in
order that `P₁,…,P_N` form a full set of sections of `Z/S`, it is necessary and sufficient
that for every geometric point `Spec(k) → S` … `Norm(f) = ∏ f((Pᵢ)_k)`" — i.e. it suffices
to check the norm equation after base change to every residue field. -/
theorem isFullSetOfSectionsAlg_iff_fields [IsReduced R] [Module.Free R B]
    [Module.Finite R B] {n : ℕ} (P : Fin n → (B →ₐ[R] R)) :
    IsFullSetOfSectionsAlg R B P ↔
      ∀ (K : Type u) [Field K] [Algebra R K], ∀ f : TensorProduct R K B,
        Algebra.norm K f = ∏ i, AlgHom.sectionBaseChange R B K (P i) f := by sorry

end FullSections

end ModularCurves
