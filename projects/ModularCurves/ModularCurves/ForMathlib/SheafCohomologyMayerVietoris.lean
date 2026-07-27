import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import ModularCurves.ForMathlib.SheafCohomologyTerminal

/-!
# Vanishing from the Mayer--Vietoris sequence

This file extracts an elementwise vanishing criterion from the Mayer--Vietoris
long exact sequence for two open subsets of a topological space.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- If two opens cover a space, cohomology in degree `n + 1` vanishes provided
degree `n` vanishes on their intersection and degree `n + 1` vanishes on both
opens. The local hypotheses use the cohomology presheaf values appearing
directly in the Mayer--Vietoris sequence. -/
theorem subsingleton_H_succ_of_mayerVietoris
    (F : Sheaf AddCommGrpCat.{u} X) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (n : ℕ)
    (hIntersection : Subsingleton
      ((toSiteSheaf F).H' n (U ⊓ V)))
    (hU : Subsingleton ((toSiteSheaf F).H' (n + 1) U))
    (hV : Subsingleton ((toSiteSheaf F).H' (n + 1) V)) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  let S := Opens.mayerVietorisSquare U V
  let F' := toSiteSheaf F
  have hT : IsTerminal S.X₄ := by
    change IsTerminal (U ⊔ V)
    rw [hUV]
    exact isTerminalTop
  let e := HPrimeAddEquivHOfIsTerminal F S.X₄ hT (n + 1)
  letI : AddCommGroup (CategoryTheory.Sheaf.H F (n + 1)) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  have hXOne : Subsingleton (F'.H' n S.X₁) := by
    change Subsingleton (F'.H' n (U ⊓ V))
    exact hIntersection
  have hXTwo : Subsingleton (F'.H' (n + 1) S.X₂) := by
    change Subsingleton (F'.H' (n + 1) U)
    exact hU
  have hXThree : Subsingleton (F'.H' (n + 1) S.X₃) := by
    change Subsingleton (F'.H' (n + 1) V)
    exact hV
  letI : Subsingleton (F'.H' n S.X₁) := hXOne
  letI : Subsingleton (F'.H' (n + 1) S.X₂) := hXTwo
  letI : Subsingleton (F'.H' (n + 1) S.X₃) := hXThree
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  let x' : F'.H' (n + 1) S.X₄ := e.symm x
  have hxTo : S.toBiprod F' (n + 1) x' = 0 := by
    rw [S.toBiprod_apply]
    have hpair :
        (⟨(F'.cohomologyPresheaf (n + 1)).map S.f₂₄.op x',
            (F'.cohomologyPresheaf (n + 1)).map S.f₃₄.op x'⟩ :
          (F'.H' (n + 1) S.X₂) × (F'.H' (n + 1) S.X₃)) = 0 := by
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact Subsingleton.elim _ _
    rw [hpair, map_zero]
  have hExact : Function.Exact
      (S.δ F' n (n + 1) rfl) (S.toBiprod F' (n + 1)) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      ((S.sequence_exact F' n (n + 1) rfl).exact 2)
  obtain ⟨y, hy⟩ := (hExact x').mp hxTo
  have hx' : x' = 0 := by
    rw [← hy, Subsingleton.elim y 0, map_zero]
  calc
    x = e x' := (e.apply_symm_apply x).symm
    _ = e 0 := congrArg e hx'
    _ = 0 := by exact e.map_zero

end TopCat.Sheaf
