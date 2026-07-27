import ModularCurves.ForMathlib.SheafCohomologyExact

/-!
# Degree-one sheaf cohomology as a cokernel

This file extracts the first nontrivial consequence of the long exact sequence in
sheaf cohomology. When the middle sheaf has vanishing first cohomology, the connecting
homomorphism presents the first cohomology of the kernel as a cokernel in abelian groups.
-/

open CategoryTheory CategoryTheory.Limits

universe w' w v u

namespace CategoryTheory.Sheaf.H

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

private noncomputable def zeroOneShortComplex : ShortComplex AddCommGrpCat.{w'} :=
  ShortComplex.mk ((functorH J 0).map S.g)
    (AddCommGrpCat.ofHom (δ hS 0 1 rfl)) (by
      ext x
      exact longSequence_comp_zero₃ hS 0 1 rfl x)

private theorem zeroOneShortComplex_exact : (zeroOneShortComplex hS).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact longSequence_exact₃ hS 0 1 rfl x hx

private theorem zeroOneShortComplex_epi
    [Subsingleton (H S.X₂ 1)] : Epi (zeroOneShortComplex hS).g := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro x
  exact longSequence_exact₁ hS 0 1 rfl x (Subsingleton.elim _ _)

/-- If the middle sheaf in a short exact sequence has vanishing `H¹`, then the
connecting homomorphism identifies `H¹` of the kernel with the cokernel of the
degree-zero map. -/
noncomputable def cokernelMapZeroIsoOne [Subsingleton (H S.X₂ 1)] :
    cokernel ((functorH J 0).map S.g) ≅ (functorH J 1).obj S.X₁ := by
  let T := zeroOneShortComplex hS
  letI : Epi T.g := zeroOneShortComplex_epi hS
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel T.f) (zeroOneShortComplex_exact hS).gIsCokernel

/-- The cokernel comparison carries the cokernel projection to the connecting
homomorphism. -/
@[reassoc]
theorem cokernelMapZeroIsoOne_hom_fac [Subsingleton (H S.X₂ 1)] :
    cokernel.π ((functorH J 0).map S.g) ≫ (cokernelMapZeroIsoOne hS).hom =
      AddCommGrpCat.ofHom (δ hS 0 1 rfl) := by
  let T := zeroOneShortComplex hS
  letI : Epi T.g := zeroOneShortComplex_epi hS
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel T.f) (zeroOneShortComplex_exact hS).gIsCokernel
      WalkingParallelPair.one

end

end CategoryTheory.Sheaf.H
