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

end AlgebraicGeometry.Scheme.Modules
