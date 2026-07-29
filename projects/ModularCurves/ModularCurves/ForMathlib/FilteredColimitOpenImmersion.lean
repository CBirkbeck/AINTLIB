/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import ModularCurves.ForMathlib.FiniteAffineOpenCover
import ModularCurves.ForMathlib.FilteredColimitCompactOpen

/-!
# Closed scalar extensions of compact open immersions

Closedness of a compact open immersion into an affine finitely presented target descends
from a filtered colimit to one later scalar-extension stage.
-/

open CategoryTheory CategoryTheory.Limits TensorProduct TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (S i →ₐ[R] S j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, S i →ₐ[R] A}

private theorem isClosedImmersion_pullback_snd_comp
    {X Y P Q : Scheme.{u}} (f : X ⟶ Y) (p : P ⟶ Y) (q : Q ⟶ P)
    [IsClosedImmersion (pullback.snd f p)] :
    IsClosedImmersion (pullback.snd f (q ≫ p)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f p q]
  infer_instance

private theorem isClosedImmersion_pullback_snd_comp_iff
    {X Y P Q : Scheme.{u}} (f : X ⟶ Y) (p : P ⟶ Y) (q : Q ⟶ P) :
    IsClosedImmersion (pullback.snd f (q ≫ p)) ↔
      IsClosedImmersion (pullback.snd (pullback.snd f p) q) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f p q,
    MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion]

private theorem isClosedImmersion_pullback_snd_change_base
    {X Y P Q V : Scheme.{u}} (f : X ⟶ Y) (p : P ⟶ Y) (q : Q ⟶ P)
    (v : V ⟶ Y) (r : Q ⟶ V) (h : q ≫ p = r ≫ v)
    [IsClosedImmersion (pullback.snd (pullback.snd f p) q)] :
    IsClosedImmersion (pullback.snd (pullback.snd f v) r) := by
  have hdirect : IsClosedImmersion (pullback.snd f (q ≫ p)) :=
    (isClosedImmersion_pullback_snd_comp_iff f p q).mpr inferInstance
  rw [h] at hdirect
  exact (isClosedImmersion_pullback_snd_comp_iff f v r).mp hdirect

/-- Closedness of a scalar extension at one stage persists after scalar extension
to any later stage. -/
theorem Scheme.Hom.isClosedImmersion_scalarExtension_of_isClosedImmersion
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
    {C : Type u} [CommRing C] [Algebra (S i) C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of C))
    (hclosed :
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j))))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) C)))))) :
    letI : Algebra (S i) (S k) :=
      (t (hij.trans hjk)).toRingHom.toAlgebra
    IsClosedImmersion
      (pullback.snd f
        (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S k))))
          (Spec.map (CommRingCat.ofHom (algebraMap (S i) C))))) := by
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (S i) (S k) :=
    (t (hij.trans hjk)).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))
  let gk := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S k)))
  let gC := Spec.map (CommRingCat.ofHom (algebraMap (S i) C))
  let q₀ := Spec.map (CommRingCat.ofHom (t hjk).toRingHom)
  have hq₀ : q₀ ≫ gj = gk := by
    dsimp only [q₀, gj, gk]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact H.t_comp hij hjk
  let q : pullback gk gC ⟶ pullback gj gC :=
    pullback.lift (pullback.fst gk gC ≫ q₀) (pullback.snd gk gC) (by
      rw [Category.assoc, hq₀, pullback.condition])
  letI : IsClosedImmersion (pullback.snd f (pullback.snd gj gC)) := hclosed
  have h := isClosedImmersion_pullback_snd_comp f (pullback.snd gj gC) q
  have hq : q ≫ pullback.snd gj gC = pullback.snd gk gC := by
    exact pullback.lift_snd _ _ _
  rw [hq] at h
  exact h

/-- A compact open immersion into a finitely presented affine stage target whose scalar
extension to the filtered colimit is closed is already closed after scalar extension to
one later stage. -/
theorem Scheme.Hom.exists_isClosedImmersion_scalarExtension_of_isOpenImmersion
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {i : ι} {C : Type u} [CommRing C] [Algebra (S i) C]
    [Algebra.FinitePresentation (S i) C]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of C)) [IsOpenImmersion f]
    (hcompact : IsCompact (f.opensRange : Set (Spec (.of C))))
    (hclosed :
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) A)))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) C)))))) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j))))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) C))))) := by
  letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap (S i) A))
  let gC := Spec.map (CommRingCat.ofHom (algebraMap (S i) C))
  let pA := pullback.snd gA gC
  let fA := pullback.snd f pA
  let eA := pullbackSpecIso (S i) A C
  letI : IsClosedImmersion fA := hclosed
  have hrange : IsClopen
      (fA.opensRange : Set ((pullback gA gC).carrier : Type u)) := by
    refine ⟨?_, fA.opensRange.isOpen⟩
    rw [Scheme.Hom.coe_opensRange]
    exact fA.isClosedEmbedding.isClosed_range
  have hopenA : eA.inv ⁻¹ᵁ fA.opensRange =
      TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight (R := S i) (A := A)).toRingHom,
          PrimeSpectrum.continuous_comap _⟩ f.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackSnd, ← Scheme.Hom.comp_preimage]
    rw [pullbackSpecIso_inv_snd]
    rfl
  have hclopenA : IsClopen
      ((↑(TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight (R := S i) (A := A)).toRingHom,
          PrimeSpectrum.continuous_comap _⟩ f.opensRange) :
            Set (PrimeSpectrum (A ⊗[S i] C)))) := by
    rw [← hopenA]
    exact hrange.preimage eA.inv.continuous
  obtain ⟨j, hij, hj⟩ :=
    H.exists_isClopen_comap_tensorProduct f.opensRange hcompact hclopenA
  refine ⟨j, hij, ?_⟩
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))
  let pj := pullback.snd gj gC
  let fj := pullback.snd f pj
  let ej := pullbackSpecIso (S i) (S j) C
  apply IsClosedImmersion.of_isPreimmersion fj
  have hopenj : ej.hom ⁻¹ᵁ
        TopologicalSpace.Opens.comap
          ⟨PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight
                (R := S i) (A := S j) (B := C)).toRingHom,
            PrimeSpectrum.continuous_comap _⟩ f.opensRange =
      fj.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackSnd]
    change ej.hom ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := S i) (A := S j) (B := C)).toRingHom) ⁻¹ᵁ
          f.opensRange) = pj ⁻¹ᵁ f.opensRange
    rw [← Scheme.Hom.comp_preimage]
    have hprojection : ej.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := S i) (A := S j) (B := C)).toRingHom) = pj := by
      dsimp only [ej, pj, gj, gC]
      rw [show Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := S i) (A := S j) (B := C)).toRingHom) =
          Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight
              (R := S i) (A := S j) (B := C)))) from rfl]
      exact pullbackSpecIso_hom_snd (S i) (S j) C
    rw [hprojection]
  rw [← Scheme.Hom.coe_opensRange, ← hopenj]
  exact (hj.preimage ej.hom.continuous).1

/-- Finitely many compact open immersions into finitely presented affine stage targets
whose scalar extensions to the filtered colimit are closed become closed simultaneously
at one common later stage. -/
theorem Scheme.Hom.exists_common_isClosedImmersion_scalarExtension_of_isOpenImmersion
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {ρ : Type u} [Finite ρ] {i : ι}
    (C : ρ → Type u) [∀ r, CommRing (C r)] [∀ r, Algebra (S i) (C r)]
    [∀ r, Algebra.FinitePresentation (S i) (C r)]
    (X : ρ → Scheme.{u}) (f : ∀ r, X r ⟶ Spec (.of (C r)))
    [∀ r, IsOpenImmersion (f r)]
    (hcompact : ∀ r, IsCompact ((f r).opensRange : Set (Spec (.of (C r)))))
    (hclosed : ∀ r,
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd (f r)
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) A)))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (C r))))))) :
    ∃ (j : ι) (hij : i ≤ j), ∀ r,
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd (f r)
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j))))
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (C r)))))) := by
  classical
  choose j hij hj using fun r ↦
    Scheme.Hom.exists_isClosedImmersion_scalarExtension_of_isOpenImmersion
      H (f r) (hcompact r) (hclosed r)
  letI : Fintype ρ := Fintype.ofFinite ρ
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨k, hk⟩ := (insert i (Finset.univ.image j)).exists_le
  have hik : i ≤ k := hk i (Finset.mem_insert_self i _)
  have hjk : ∀ r, j r ≤ k := fun r ↦ hk (j r)
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem j (Finset.mem_univ r)))
  refine ⟨k, hik, fun r ↦ ?_⟩
  exact Scheme.Hom.isClosedImmersion_scalarExtension_of_isClosedImmersion
    H (hij r) (hjk r) (f r) (hj r)

/-- An open immersion into a proper scheme over a Noetherian filtered-colimit stage whose
scalar extension to the colimit is closed is already closed after scalar extension to one
later stage. -/
theorem Scheme.Hom.exists_isClosedImmersion_scalarExtension_of_isOpenImmersion_of_isProperTarget
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {i : ι} [IsNoetherianRing (S i)] {Z : Scheme.{u}}
    (zπ : Z ⟶ Spec (.of (S i))) [IsProper zπ]
    {X : Scheme.{u}} (f : X ⟶ Z) [IsOpenImmersion f]
    (hclosed :
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) A))) zπ))) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsClosedImmersion
        (pullback.snd f
          (pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))) zπ)) := by
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian zπ
  letI : CompactSpace Z := (quasiCompact_iff_compactSpace zπ).mp inferInstance
  obtain ⟨ρ, hρ, U, hcover, hUaff⟩ := Z.exists_finite_affine_openCover
  letI : Finite ρ := hρ
  let C : ρ → Type u := fun r ↦ Γ(Z, U r)
  let chart : ∀ r, Spec (.of (C r)) ⟶ Z := fun r ↦ (hUaff r).fromSpec
  let zC : ∀ r, Spec (.of (C r)) ⟶ Spec (.of (S i)) := fun r ↦ chart r ≫ zπ
  letI chartAlgebra (r : ρ) : Algebra (S i) (C r) :=
    (Spec.preimage (zC r)).hom.toAlgebra
  have hstruct (r : ρ) :
      Spec.map (CommRingCat.ofHom (algebraMap (S i) (C r))) = zC r := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  letI chartFinitePresentation (r : ρ) :
      Algebra.FinitePresentation (S i) (C r) := by
    change RingHom.FinitePresentation (algebraMap (S i) (C r))
    rw [RingHom.algebraMap_toAlgebra]
    apply (LocallyOfFinitePresentation.SpecMap_iff (Spec.preimage (zC r))).mp
    rw [Spec.map_preimage]
    infer_instance
  have hcompact (r : ρ) (W : (Spec (.of (C r))).Opens) :
      IsCompact (W : Set (Spec (.of (C r)))) := by
    letI : IsNoetherianRing (C r) := Algebra.FiniteType.isNoetherianRing (S i) (C r)
    exact NoetherianSpace.isCompact _
  let Xc : ρ → Scheme.{u} := fun r ↦ pullback f (chart r)
  let fC : ∀ r, Xc r ⟶ Spec (.of (C r)) := fun r ↦ pullback.snd f (chart r)
  letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap (S i) A))
  let pA := pullback.snd gA zπ
  let fA := pullback.snd f pA
  letI : IsClosedImmersion fA := hclosed
  let gC : ∀ r, Spec (.of (C r)) ⟶ Spec (.of (S i)) := fun r ↦
    Spec.map (CommRingCat.ofHom (algebraMap (S i) (C r)))
  let pCA : ∀ r, pullback gA (gC r) ⟶ Spec (.of (C r)) := fun r ↦
    pullback.snd gA (gC r)
  let qA : ∀ r, pullback gA (gC r) ⟶ pullback gA zπ := fun r ↦
    pullback.lift (pullback.fst gA (gC r)) (pCA r ≫ chart r) (by
      change pullback.fst gA (gC r) ≫ gA = pCA r ≫ zC r
      rw [← hstruct r]
      exact pullback.condition)
  have hqA (r : ρ) : qA r ≫ pA = pCA r ≫ chart r := by
    exact pullback.lift_snd _ _ _
  have hclosedC (r : ρ) :
      IsClosedImmersion (pullback.snd (fC r) (pCA r)) := by
    letI : IsClosedImmersion (pullback.snd fA (qA r)) := inferInstance
    exact isClosedImmersion_pullback_snd_change_base f pA (qA r) (chart r) (pCA r) (hqA r)
  obtain ⟨j, hij, hclosedj⟩ :=
    Scheme.Hom.exists_common_isClosedImmersion_scalarExtension_of_isOpenImmersion
      H C Xc fC (fun r ↦ hcompact r (fC r).opensRange) hclosedC
  have hchartCovers : ∀ x, ∃ r y, chart r y = x := by
    intro x
    have hx : x ∈ ((⨆ r, U r) : Z.Opens) := by
      rw [show (⨆ r, U r) = ⊤ from hcover]
      trivial
    obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hr' : x ∈ Set.range (chart r) := by
      rw [show Set.range (chart r) = (U r : Set Z) from (hUaff r).range_fromSpec]
      exact hr
    obtain ⟨y, hy⟩ := hr'
    exact ⟨r, y, hy⟩
  let chartCover : Z.OpenCover := {
    I₀ := ρ
    X r := Spec (.of (C r))
    f := chart
    mem₀ := (Scheme.Cover.mkOfCovers ρ (fun r ↦ Spec (.of (C r)))
      chart hchartCovers).mem₀ }
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))
  let pj := pullback.snd gj zπ
  let fj := pullback.snd f pj
  let pCj : ∀ r, pullback gj (gC r) ⟶ Spec (.of (C r)) := fun r ↦
    pullback.snd gj (gC r)
  let chartCoverj0 : (pullback gj zπ).OpenCover :=
    Scheme.Pullback.openCoverOfRight chartCover gj zπ
  let chartMapj : ∀ r, pullback gj (gC r) ⟶ pullback gj zπ := fun r ↦
    pullback.lift (pullback.fst gj (gC r)) (pCj r ≫ chart r) (by
      calc
        pullback.fst gj (gC r) ≫ gj = pCj r ≫ gC r := pullback.condition
        _ = pCj r ≫ zC r := congrArg (fun q ↦ pCj r ≫ q) (hstruct r)
        _ = pCj r ≫ chart r ≫ zπ := by simp only [zC])
  have hchartMapj (r : ρ) : pCj r ≫ chart r = chartMapj r ≫ pj := by
    exact (pullback.lift_snd _ _ _).symm
  have hchartMapjCopy (r : ρ) :
      chartMapj r = (pullback.congrHom rfl (hstruct r)).hom ≫ chartCoverj0.f r := by
    have hcoverFst : chartCoverj0.f r ≫ pullback.fst gj zπ =
        pullback.fst gj (zC r) := by
      dsimp only [chartCoverj0]
      rw [Scheme.Pullback.openCoverOfRight_f]
      simp only [chartCover, zC, pullback.map, Category.comp_id]
      exact pullback.lift_fst _ _ _
    have hcoverSnd : chartCoverj0.f r ≫ pullback.snd gj zπ =
        pullback.snd gj (zC r) ≫ chart r := by
      dsimp only [chartCoverj0]
      rw [Scheme.Pullback.openCoverOfRight_f]
      simp only [chartCover, zC, pullback.map]
      exact pullback.lift_snd _ _ _
    have hcongrFst : (pullback.congrHom rfl (hstruct r)).hom ≫
        pullback.fst gj (zC r) = pullback.fst gj (gC r) := by
      simp only [pullback.congrHom_hom, pullback.map, Category.comp_id]
      exact pullback.lift_fst _ _ _
    have hcongrSnd : (pullback.congrHom rfl (hstruct r)).hom ≫
        pullback.snd gj (zC r) = pCj r := by
      simp only [pullback.congrHom_hom, pullback.map, Category.comp_id, pCj]
      exact pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · calc
        chartMapj r ≫ pullback.fst gj zπ = pullback.fst gj (gC r) :=
          pullback.lift_fst _ _ _
        _ = (pullback.congrHom rfl (hstruct r)).hom ≫ pullback.fst gj (zC r) :=
          hcongrFst.symm
        _ = (pullback.congrHom rfl (hstruct r)).hom ≫
            (chartCoverj0.f r ≫ pullback.fst gj zπ) :=
          congrArg (fun q ↦ (pullback.congrHom rfl (hstruct r)).hom ≫ q) hcoverFst.symm
        _ = ((pullback.congrHom rfl (hstruct r)).hom ≫ chartCoverj0.f r) ≫
            pullback.fst gj zπ := (Category.assoc _ _ _).symm
    · calc
        chartMapj r ≫ pullback.snd gj zπ = pCj r ≫ chart r :=
          pullback.lift_snd _ _ _
        _ = ((pullback.congrHom rfl (hstruct r)).hom ≫
            pullback.snd gj (zC r)) ≫ chart r := congrArg (fun q ↦ q ≫ chart r) hcongrSnd.symm
        _ = (pullback.congrHom rfl (hstruct r)).hom ≫
            (pullback.snd gj (zC r) ≫ chart r) := Category.assoc _ _ _
        _ = (pullback.congrHom rfl (hstruct r)).hom ≫
            (chartCoverj0.f r ≫ pullback.snd gj zπ) :=
          congrArg (fun q ↦ (pullback.congrHom rfl (hstruct r)).hom ≫ q) hcoverSnd.symm
        _ = ((pullback.congrHom rfl (hstruct r)).hom ≫ chartCoverj0.f r) ≫
            pullback.snd gj zπ := (Category.assoc _ _ _).symm
  let chartCoverj : (pullback gj zπ).OpenCover :=
    chartCoverj0.copy ρ (fun r ↦ pullback gj (gC r)) chartMapj
      (Equiv.refl ρ) (fun r ↦ pullback.congrHom rfl (hstruct r)) hchartMapjCopy
  have hcoverMap (r : ρ) : chartCoverj.f r = chartMapj r := by
    exact Scheme.Cover.copy_f chartCoverj0 ρ (fun r ↦ pullback gj (gC r))
      chartMapj (Equiv.refl ρ) (fun r ↦ pullback.congrHom rfl (hstruct r))
      hchartMapjCopy r
  have hresult : IsClosedImmersion fj := by
    apply IsZariskiLocalAtTarget.of_openCover chartCoverj
    change ∀ r : ρ, IsClosedImmersion (pullback.snd fj (chartCoverj.f r))
    intro r
    have hclosedj' : IsClosedImmersion (pullback.snd (fC r) (pCj r)) := by
      exact hclosedj r
    letI : IsClosedImmersion (pullback.snd (fC r) (pCj r)) := hclosedj'
    have hlocal : IsClosedImmersion (pullback.snd fj (chartMapj r)) :=
      isClosedImmersion_pullback_snd_change_base f (chart r) (pCj r) pj
        (chartMapj r) (hchartMapj r)
    rw [hcoverMap r]
    exact hlocal
  exact ⟨j, hij, hresult⟩

end

end AlgebraicGeometry
