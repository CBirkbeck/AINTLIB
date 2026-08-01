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

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace Matrix

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The line kernel from surjectivity alone.** When global sections surject onto
the twist cokernel's sections (the `H¹` consequence), the evaluation rows are
unimodular by Binet–Cauchy, and the kernel of the restriction on base sections is
the free rank-one span of the cross product of the rows — no evaluation values are
ever computed. -/
theorem ker_baseSectionsMap_cokernel_eq_span_crossProduct_of_surjective
    {M N : C.Modules} (f : M ⟶ N)
    (b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π N))
    (e2 : Scheme.Modules.baseSections π (Limits.cokernel f)
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 2 → Γ(S, (⊤ : S.Opens))))
    (hsurj : Function.Surjective
      (Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)).hom) :
    LinearMap.ker
        ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens))
        {b3.equivFun.symm
          ((fun j => e2 ((Scheme.Modules.baseSectionsMap π
            (Limits.cokernel.π f)) (b3 j)) 0) ⨯₃
           (fun j => e2 ((Scheme.Modules.baseSectionsMap π
            (Limits.cokernel.π f)) (b3 j)) 1))} := by
  classical
  -- the composite in coordinates
  have hcoord : ∀ (s : Scheme.Modules.baseSections π N) (i : Fin 2),
      (fun j => e2 ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) (b3 j)) i) ⬝ᵥ b3.equivFun s =
      e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) s) i := by
    intro s i
    calc (fun j => e2 ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) (b3 j)) i) ⬝ᵥ b3.equivFun s
        = ∑ j, b3.equivFun s j •
            e2 ((Scheme.Modules.baseSectionsMap π
              (Limits.cokernel.π f)) (b3 j)) i := by
          simp only [dotProduct, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = (∑ j, b3.equivFun s j •
            e2 ((Scheme.Modules.baseSectionsMap π
              (Limits.cokernel.π f)) (b3 j))) i := by
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun j _ => rfl
      _ = e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) s) i := by
          have hsum : (∑ j, b3.equivFun s j •
              e2 ((Scheme.Modules.baseSectionsMap π
                (Limits.cokernel.π f)) (b3 j))) =
              e2 ((Scheme.Modules.baseSectionsMap π
                (Limits.cokernel.π f)) s) := by
            calc ∑ j, b3.equivFun s j •
                e2 ((Scheme.Modules.baseSectionsMap π
                  (Limits.cokernel.π f)) (b3 j))
                = ∑ j, e2 ((Scheme.Modules.baseSectionsMap π
                    (Limits.cokernel.π f)) (b3.equivFun s j • b3 j)) := by
                  exact Finset.sum_congr rfl fun j _ => by
                    rw [_root_.map_smul, _root_.map_smul]
              _ = e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f))
                    (∑ j, b3.equivFun s j • b3 j)) := by
                  rw [map_sum, map_sum]
              _ = _ := by rw [b3.sum_equivFun]
          rw [hsum]
  refine ker_baseSectionsMap_cokernel_eq_span_crossProduct f b3 e2
    (fun i j => e2 ((Scheme.Modules.baseSectionsMap π
      (Limits.cokernel.π f)) (b3 j)) i)
    (fun i j => rfl) ?_
  refine ModularCurves.span_range_crossProduct_eq_top_of_surjective _ _ ?_
  intro y
  obtain ⟨s, hs⟩ := hsurj (e2.symm ![y 0, y 1])
  refine ⟨b3.equivFun s, ?_, ?_⟩
  · rw [hcoord s 0]
    have : e2 ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) s) = ![y 0, y 1] := by
      rw [show ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) s : Scheme.Modules.baseSections π
          (Limits.cokernel f)) = e2.symm ![y 0, y 1] from hs]
      exact e2.apply_symm_apply _
    rw [this]
    rfl
  · rw [hcoord s 1]
    have : e2 ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) s) = ![y 0, y 1] := by
      rw [show ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) s : Scheme.Modules.baseSections π
          (Limits.cokernel f)) = e2.symm ![y 0, y 1] from hs]
      exact e2.apply_symm_apply _
    rw [this]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[GAP-A-4, the line]** For a section pair on a chart with principal
nonzerodivisor kernels, an invertible ambient module with a rank-three basis of
base sections, and vanishing `H¹` of the twisted tensor, the kernel of restriction
to the pair divisor is free of rank one: it is spanned by the cross product of the
two evaluation rows, assembled through the basis. The generator is the module of
the chord line; its unimodularity is Binet–Cauchy from cohomological surjectivity,
never from evaluation minors. -/
theorem exists_ker_baseSectionsMap_cokernel_eq_span_of_sections
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
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r)
    [Subsingleton (CategoryTheory.Sheaf.H (tensorObj (idealModule
      (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal) L).sheaf 1)]
    (b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π L)) :
    ∃ ℓ : Scheme.Modules.baseSections π L,
      LinearMap.ker ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
          π ![P, Q]).ideal L))).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens)) {ℓ} := by
  classical
  -- the principal cover and the global mono
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
  haveI hMonoT : Mono (divisorTwistHom
      (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal L) :=
    mono_divisorTwistHom _ L hcover hL
  -- surjectivity of the restriction on base sections from the H¹ slot
  have hsurj := Scheme.Modules.baseSectionsMap_cokernel_surjective_of_subsingleton_H_one
    π (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
      π ![P, Q]).ideal L)
  -- the rank-two coordinates
  obtain ⟨e2⟩ := nonempty_baseSections_cokernel_divisorTwistHom_equiv_pair_of_sections
    hsm P Q U hPU hQU rP rQ hP hQ hnzdP hnzdQ L hL eL halg
  exact ⟨b3.equivFun.symm
      ((fun j => e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
          π ![P, Q]).ideal L))) (b3 j)) 0) ⨯₃
       (fun j => e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
          π ![P, Q]).ideal L))) (b3 j)) 1)),
    ker_baseSectionsMap_cokernel_eq_span_crossProduct_of_surjective _ b3 e2 hsurj⟩

end AlgebraicGeometry.Scheme.Modules
