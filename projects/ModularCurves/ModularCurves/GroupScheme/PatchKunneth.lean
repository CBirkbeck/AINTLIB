import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The affine Künneth identification over a base patch

Construction support for `[CHARTER-HOPF]` Wave C (`.mathlib-quality/decomposition-hopf-crux.md`,
leaf `[HG-C1c-1]`, prerequisite): given an affine open `V` of a base scheme `S` and two
affine opens `W₁ ⊆ X`, `W₂ ⊆ Y` lying over `V` along structure maps `f : X ⟶ S`,
`g : Y ⟶ S`, the fibre product of the restricted structure maps is the `Spec` of the
tensor product of the section rings:

  `pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂) ≅ Spec (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂))`

whenever the `Γ(S,V)`-algebra structures on the section rings are the restriction
(`appLE`) maps. That hypothesis is what makes the legs match `pullbackSpecIso` on the
nose.

Instantiations: with `(f, g) = (G.π, E.π)` and `(W₁, W₂) = (G|_V, U)` this is the chart
Künneth of the translation co-action; with `(f, g) = (G.π, G.π)` and
`(W₁, W₂) = (G|_V, G|_V)` it is the target of the comultiplication of the Hopf algebra of
`G` over the patch.
-/

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}} {V : S.Opens} {W₁ : X.Opens} {W₂ : Y.Opens}

/-- An affine open is isomorphic to the `Spec` of its sections, via `toSpecΓ`. -/
theorem IsAffineOpen.isIso_toSpecΓ {W : X.Opens} (hW : IsAffineOpen W) :
    IsIso W.toSpecΓ :=
  hW.isoSpec_hom ▸ inferInstanceAs (IsIso hW.isoSpec.hom)

section

variable (f : X ⟶ S) (g : Y ⟶ S) {e₁ : W₁ ≤ f ⁻¹ᵁ V} {e₂ : W₂ ≤ g ⁻¹ᵁ V}
variable [Algebra Γ(S, V) Γ(X, W₁)] [Algebra Γ(S, V) Γ(Y, W₂)]

/-- **The affine Künneth identification over a base patch.** -/
noncomputable def patchKunneth
    (hV : IsAffineOpen V) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (h₁ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁)) = f.appLE V W₁ e₁)
    (h₂ : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂)) = g.appLE V W₂ e₂) :
    pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
      ≅ Spec (.of (Γ(X, W₁) ⊗[Γ(S, V)] Γ(Y, W₂))) := by
  haveI := hV.isIso_toSpecΓ
  haveI := hW₁.isIso_toSpecΓ
  haveI := hW₂.isIso_toSpecΓ
  refine (asIso (pullback.map (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W₁))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Y, W₂))))
    W₁.toSpecΓ W₂.toSpecΓ V.toSpecΓ ?_ ?_))
    ≪≫ pullbackSpecIso Γ(S, V) Γ(X, W₁) Γ(Y, W₂)
  · rw [h₁]
    exact (Scheme.Opens.toSpecΓ_SpecMap_appLE f V W₁ e₁).symm
  · rw [h₂]
    exact (Scheme.Opens.toSpecΓ_SpecMap_appLE g V W₂ e₂).symm

end

end AlgebraicGeometry
