import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import ModularCurves.ForMathlib.MinimalPrimeBasicOpen

/-!
# Finite affine open covers

This file constructs the finite affine covers used to build Čech complexes over an
affine base. Properness supplies compactness, while separatedness makes every nonempty
finite intersection of the chosen affine opens affine.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A compact scheme admits an affine open cover indexed by a finite type. -/
theorem Scheme.exists_finite_affine_openCover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ ∀ i, IsAffineOpen (U i) := by
  have hU : IsOpenCover (fun U : X.affineOpens ↦ U.1) := by
    rw [IsOpenCover, iSup_affineOpens_eq_top]
  obtain ⟨s, hs⟩ := hU.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ i.1.1, hs, fun i ↦ i.1.2⟩

/-- A compact quasi-separated scheme with finitely many generic points admits a finite affine
open cover each of whose members contains every generic point. -/
theorem Scheme.exists_finite_affine_openCover_containing_genericPoints
    (X : Scheme.{u}) [CompactSpace X] [Finite (genericPoints X)]
    [QuasiSeparatedSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ i (η : genericPoints X), η.1 ∈ U i := by
  choose U hU hxU hηU using fun x : X ↦
    genericPoints.exists_affineOpen_containing_point x
  have hcover : IsOpenCover U := by
    rw [IsOpenCover]
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ U i.1, hs, fun i ↦ hU i.1,
    fun i η ↦ hηU i.1 η⟩

/-- A compact quasi-separated scheme with finitely many generic points admits a finite affine
open cover whose common intersection is dense. -/
theorem Scheme.exists_finite_affine_openCover_dense_iInf
    (X : Scheme.{u}) [CompactSpace X] [Finite (genericPoints X)]
    [QuasiSeparatedSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        Dense ((⨅ i, U i : X.Opens) : Set X) := by
  obtain ⟨ι, hι, U, hcover, hU, hηU⟩ :=
    X.exists_finite_affine_openCover_containing_genericPoints
  letI : Finite ι := hι
  refine ⟨ι, hι, U, hcover, hU, ?_⟩
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hsub : (genericPoints X : Set X) ⊆ ((⨅ i, U i : X.Opens) : Set X) := by
    intro η hη
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun i ↦ hηU i ⟨η, hη⟩
  have hclosure := closure_mono hsub
  rw [genericPoints.closure] at hclosure
  exact hclosure (Set.mem_univ x)

/-- A Noetherian scheme admits a finite affine open cover whose common intersection is dense. -/
theorem Scheme.exists_finite_affine_openCover_dense_iInf_of_isNoetherian
    (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        Dense ((⨅ i, U i : X.Opens) : Set X) := by
  letI : Finite (genericPoints X) :=
    (genericPoints.finite
      (finite_irreducibleComponents_of_isNoetherian (X := X))).to_subtype
  exact X.exists_finite_affine_openCover_dense_iInf

/-- A Noetherian scheme admits a nonempty finite affine open cover whose common intersection
is dense. The singleton empty cover handles the empty scheme. -/
theorem Scheme.exists_nonempty_finite_affine_openCover_dense_iInf_of_isNoetherian
    (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] :
    ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        Dense ((⨅ i, U i : X.Opens) : Set X) := by
  obtain ⟨ι, hι, U, hcover, hU, hDense⟩ :=
    X.exists_finite_affine_openCover_dense_iInf_of_isNoetherian
  letI : Finite ι := hι
  by_cases hnonempty : Nonempty ι
  · exact ⟨ι, hι, hnonempty, U, hcover, hU, hDense⟩
  · letI : IsEmpty ι := not_nonempty_iff.mp hnonempty
    have hbot : (⊥ : X.Opens) = ⊤ := by
      simpa only [IsOpenCover, iSup_of_empty] using hcover
    have hcover' : IsOpenCover (fun _ : ULift.{u} Unit ↦ (⊥ : X.Opens)) := by
      rw [IsOpenCover]
      simpa using hbot
    have hDense' : Dense (((⊥ : X.Opens) : Set X)) := by
      rw [hbot]
      exact dense_univ
    exact ⟨ULift.{u} Unit, inferInstance, inferInstance, fun _ ↦ ⊥, hcover',
      fun _ ↦ isAffineOpen_bot X, by simpa using hDense'⟩

/-- A proper scheme over an affine base has a finite affine open cover whose every
nonempty finite intersection is affine. -/
theorem Scheme.Hom.exists_finite_affine_openCover_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsAffine S] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        ∀ (s : Finset ι), s.Nonempty → IsAffineOpen (⨅ i ∈ (s : Set ι), U i) := by
  letI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  letI : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, U, hU, hUaff⟩ := X.exists_finite_affine_openCover
  letI : Finite ι := hι
  refine ⟨ι, hι, U, hU, hUaff, fun s hs ↦ ?_⟩
  exact IsAffineOpen.biInf (s : Set ι) s.finite_toSet
    (Finset.coe_nonempty.mpr hs) fun i _ ↦ hUaff i

end AlgebraicGeometry
