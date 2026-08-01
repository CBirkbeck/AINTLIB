/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.LineVertical

/-!
# Consumer wiring for the line and vertical (GAP-A-4)

Instantiates the rank-two divisor-restriction interface at a pair of sections of a
smooth relative curve: the evaluation equivalences come from the section
retractions (`evaluationQuotEquiv` on the chart-top algebra), the concentration
data from support avoidance, and the chart trivializations from principal
kernels. The heavy cohomological input (`H¹`-vanishing) remains a hypothesis
slot, exactly as in the rank ladder of `PoleSheafRankTwoThree`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {C S : Scheme.{u}} {π : C ⟶ S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The chart-top evaluation equivalence of a section.** A section of `π` landing
in an affine chart, with principal kernel ideal there, evaluates the chart-top
quotient by the transported generator down to the base sections: the lifted
section is an algebra retraction of the chart with that kernel. -/
theorem nonempty_evaluation_quotEquiv_of_ker_span [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hzU : z ⁻¹ᵁ U.1 = ⊤)
    (rP : Γ(C, U.1)) (hP : (Scheme.Hom.ker z).ideal U = Ideal.span {rP})
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r) :
    Nonempty ((Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸
        Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) := by
  classical
  haveI : IsClosedImmersion z :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion hz
  -- lift the section into the chart
  have hrange : Set.range z.base ⊆ Set.range U.1.ι.base := by
    intro c hc
    obtain ⟨s, rfl⟩ := hc
    have hs : s ∈ z ⁻¹ᵁ U.1 := by rw [hzU]; trivial
    exact ⟨⟨z.base s, hs⟩, rfl⟩
  let zU : S ⟶ U.1.toScheme := IsOpenImmersion.lift U.1.ι z hrange
  have hcomp : zU ≫ U.1.ι = z := IsOpenImmersion.lift_fac U.1.ι z hrange
  rw [← hcomp] at hP hzU hz
  have hret : zU ≫ (U.1.ι ≫ π) = 𝟙 S := by
    rw [← Category.assoc]
    exact hz
  haveI : IsClosedImmersion (zU ≫ U.1.ι) := by
    rw [hcomp]
    infer_instance
  -- the appTop retraction
  have hAppTopEq : Scheme.Hom.appTop (U.1.ι ≫ π) ≫ Scheme.Hom.appTop zU =
      𝟙 Γ(S, (⊤ : S.Opens)) := by
    rw [← Scheme.Hom.comp_appTop, hret, Scheme.Hom.id_appTop]
  -- the evaluation as an algebra retraction of the chart top sections
  set σ : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) →ₐ[Γ(S, (⊤ : S.Opens))]
      Γ(S, (⊤ : S.Opens)) :=
    { toRingHom := (Scheme.Hom.appTop zU).hom
      commutes' := fun r => by
        have h2 := congrArg
          (fun (w : Γ(S, (⊤ : S.Opens)) ⟶ Γ(S, (⊤ : S.Opens))) => w.hom r)
          hAppTopEq
        simpa [halg] using h2 } with hσdef
  -- the composite evaluation is the section's appLE
  have hkey : U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge ≫
      Scheme.Hom.appTop zU = (zU ≫ U.1.ι).appLE U.1 ⊤ hzU.ge := by
    rw [show Scheme.Hom.appTop zU =
      zU.appLE ⊤ ⊤ le_rfl from Scheme.Hom.app_eq_appLE zU]
    rw [Scheme.Hom.appLE_comp_appLE]
  -- the kernel of the section's appLE is the principal span
  have hkerLE : RingHom.ker ((zU ≫ U.1.ι).appLE U.1 ⊤ hzU.ge).hom =
      Ideal.span {rP} := by
    rw [← ModularCurves.RelEffCartierDiv.KerPrincipal.ker_app π (zU ≫ U.1.ι) hz
      (le_top.trans (le_of_eq (Scheme.Hom.preimage_top π).symm)) hzU.ge]
    rw [← Scheme.Hom.ker_apply]
    exact hP
  -- transport the kernel through the chart-top isomorphism
  have hbij := (ConcreteCategory.isIso_iff_bijective
    (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge)).mp inferInstance
  have hkerσ : RingHom.ker σ = Ideal.span
      {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP} := by
    ext x
    obtain ⟨y, rfl⟩ := hbij.surjective x
    have hxval : σ ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom y) =
        ((zU ≫ U.1.ι).appLE U.1 ⊤ hzU.ge).hom y := by
      have h3 := congrArg
        (fun (w : Γ(C, U.1) ⟶ Γ(S, (⊤ : S.Opens))) => w.hom y) hkey
      exact h3
    constructor
    · intro hx
      have hy : y ∈ RingHom.ker ((zU ≫ U.1.ι).appLE U.1 ⊤ hzU.ge).hom := by
        rw [RingHom.mem_ker, ← hxval]
        exact hx
      rw [hkerLE] at hy
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hy
      refine Ideal.mem_span_singleton'.mpr
        ⟨(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom a, ?_⟩
      rw [← map_mul, ha]
    · intro hx
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
      obtain ⟨a', rfl⟩ := hbij.surjective a
      rw [← map_mul] at ha
      have hy2 : a' * rP = y := hbij.injective ha
      rw [RingHom.mem_ker, hxval, ← hy2]
      have hmem : a' * rP ∈ Ideal.span {rP} :=
        Ideal.mem_span_singleton'.mpr ⟨a', rfl⟩
      rw [← hkerLE] at hmem
      exact RingHom.mem_ker.mp hmem
  exact ⟨ModularCurves.evaluationQuotEquiv σ _ hkerσ⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[GAP-A-4, rank-two coordinates at a section pair]** For sections `P, Q` of a
separated smooth relative curve landing in an affine chart where both kernel
ideals are principal on nonzerodivisors, the base sections of the pair-divisor
twist cokernel are free of rank two over the base. The ambient invertible `L`,
its chart trivialization, and the base-algebra structure remain slots. -/
theorem nonempty_baseSections_cokernel_divisorTwistHom_equiv_pair_of_sections
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (P Q : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens)
    (hPU : P.1 ⁻¹ᵁ U.1 = ⊤) (hQU : Q.1 ⁻¹ᵁ U.1 = ⊤)
    (rP rQ : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ})
    (hnzdP : rP ∈ nonZeroDivisors Γ(C, U.1))
    (hnzdQ : rQ ∈ nonZeroDivisors Γ(C, U.1))
    (L : C.Modules) (hL : IsInvertible L)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r) :
    Nonempty ((Scheme.Modules.baseSections π
        (Limits.cokernel (divisorTwistHom
          (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal L)))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 2 → Γ(S, (⊤ : S.Opens)))) := by
  classical
  haveI hclP : IsClosedImmersion P.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion P.2
  haveI hclQ : IsClosedImmersion Q.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion Q.2
  -- the chart trivialization of the pair ideal
  have hspanU : (ModularCurves.RelEffCartierDiv.sectionsDivisor
      π ![P, Q]).ideal.ideal U = Ideal.span {rP * rQ} :=
    sectionsDivisor_pair_ideal_span hsm P Q U rP rQ hP hQ
  have hnzdPQ : rP * rQ ∈ nonZeroDivisors Γ(C, U.1) := mul_mem hnzdP hnzdQ
  let eI : (restrictFunctor U.1.ι).obj (idealModule
      (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal) ≅
      unitObj U.1.toScheme :=
    idealModuleRestrictTrivOfSpan U (rP * rQ) hspanU hnzdPQ
  -- the principal-nonzerodivisor cover for the mono chain
  have hcover : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal.ideal V =
        Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1) := by
    intro c
    obtain ⟨V, hcV, hV⟩ :=
      ModularCurves.RelEffCartierDiv.SectionsIdeal.exists_multiChart
        π hsm ![P, Q] c
    obtain ⟨f₀, hf₀, hf₀nzd⟩ := hV 0
    obtain ⟨f₁, hf₁, hf₁nzd⟩ := hV 1
    exact ⟨V, hcV, f₀ * f₁,
      sectionsDivisor_pair_ideal_span hsm P Q V f₀ f₁ hf₀ hf₁,
      mul_mem hf₀nzd hf₁nzd⟩
  haveI hMono : Mono ((restrictFunctor U.1.ι).map (divisorTwistHom
      (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal L)) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ L hcover hL) U.1
  -- the concentration open: complement of the section images
  have hranges : ∀ s, P.1.base s ∈ U.1 := fun s => by
    have : s ∈ P.1 ⁻¹ᵁ U.1 := by rw [hPU]; trivial
    exact this
  have hrangesQ : ∀ s, Q.1.base s ∈ U.1 := fun s => by
    have : s ∈ Q.1 ⁻¹ᵁ U.1 := by rw [hQU]; trivial
    exact this
  let V : C.Opens := ⟨(Set.range P.1.base ∪ Set.range Q.1.base)ᶜ,
    (IsClosed.union P.1.isClosedEmbedding.isClosed_range
      Q.1.isClosedEmbedding.isClosed_range).isOpen_compl⟩
  have hUV : U.1 ⊔ V = ⊤ := by
    refine le_antisymm le_top ?_
    intro c _
    by_cases hc : c ∈ Set.range P.1.base ∪ Set.range Q.1.base
    · rcases hc with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact Or.inl (hranges s)
      · exact Or.inl (hrangesQ s)
    · exact Or.inr hc
  -- the support of the pair ideal is the union of the images
  have hsupp : ((ModularCurves.RelEffCartierDiv.sectionsDivisor
      π ![P, Q]).ideal.support : Set ↥C) =
      Set.range P.1.base ∪ Set.range Q.1.base := by
    rw [ModularCurves.RelEffCartierDiv.sectionsDivisor_ideal π hsm ![P, Q]]
    rw [ModularCurves.RelEffCartierDiv.SectionsIdeal.support_prod π ![P, Q]]
    ext c
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hc | hc)
      · exact ⟨0, hc⟩
      · exact ⟨1, hc⟩
  have htriv : ∀ (W : C.Opens), W ≤ V →
      (1 : Γ(C, W)) ∈ idealSections (ModularCurves.RelEffCartierDiv.sectionsDivisor
        π ![P, Q]).ideal (Opposite.op W) := by
    intro W hWV
    refine one_mem_idealSections_of_disjoint_support _ W ?_
    rw [hsupp]
    refine Set.disjoint_left.mpr fun c hc hcW => ?_
    exact (hWV hcW) hc
  -- the transported generators and their spans
  have hg'nzdP : (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP ∈
      nonZeroDivisors Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := by
    rw [← MulEquivClass.map_nonZeroDivisors
      (asIso (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge)).commRingCatIsoToRingEquiv]
    exact ⟨rP, hnzdP, rfl⟩
  have hv : Ideal.span {twistChartMultiplier
      (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal
        L U.1 eI eL} =
      Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP *
        (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rQ} := by
    rw [← map_mul]
    exact span_twistChartMultiplier_eq _ L U (rP * rQ) hspanU hnzdPQ eI eL
  -- the evaluation equivalences
  obtain ⟨eP⟩ := nonempty_evaluation_quotEquiv_of_ker_span
    P.1 P.2 U hPU rP hP halg
  obtain ⟨eQ⟩ := nonempty_evaluation_quotEquiv_of_ker_span
    Q.1 Q.2 U hQU rQ hQ halg
  -- assemble through the rank-two interface
  exact nonempty_baseSections_cokernel_divisorTwistHom_equiv_pair
    (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal L U
    eI eL V hUV htriv hMono
    ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP)
    ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rQ)
    hv hg'nzdP halg eP eQ

end AlgebraicGeometry.Scheme.Modules
