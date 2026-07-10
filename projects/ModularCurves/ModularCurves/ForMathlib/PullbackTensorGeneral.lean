/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import ModularCurves.Picard.Pic
import ModularCurves.ForMathlib.PullbackTensorMonoidal

/-!
# General pullback–tensor compatibility — decomposition skeleton (Route G)

`/develop --decompose` skeleton for **D-PresPB′-general** (board v10.98/v10.99): the general-`f`
pullback–tensor gate of the GME (2.16) Picard-functoriality chain. Route G (construction-grain):
give the presheaf pushforward its lax monoidal structure, get the oplax comparison `δ` on the
pullback by doctrinal adjunction, show `δ` is an iso on free-yoneda generators (on an Opens-site
the tensor of free-yonedas is the free-yoneda of the meet — the lattice miracle — and
`freeFunctorCompPullbackIso` matches the pullback side), and extend along free presentations by
two single-variable five-lemma passes in the abelian target. Payoff:
`functorMonoidalOfComp` ⟹ `(Modules.pullback f).Monoidal` ⟹ `Skeleton.monoidHom` ⟹
`Pic(f) : Pic X →* Pic Y`.

All leaves are stated `Nonempty`-wrapped (`Prop`s — no `sorryAx` in monoidal DATA, the v10.8
discipline; the data is built at execution time, each structure landing only when its leaf is
sorry-free). Full route adjudication, verbatim anchors and attack logs:
`.mathlib-quality/decomposition-pullback-monoidal-general.md`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Functor

namespace PresheafOfModules

section LaxPushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))

/-- **[D-PresPB′-general], leaf B1.** The presheaf-of-modules pushforward along an *arbitrary*
ring comparison `φ` is lax monoidal: `ε`, `μ` sectionwise from
`ModuleCat.restrictScalars.LaxMonoidal` through the `pushforward₀ ⋙ restrictScalars`
factorization (model: `pushforward₀OfCommRingCat.Monoidal`). No iso hypothesis — lax needs
none. Its left adjoint (the pullback) then carries the oplax comparison
`δ_{P,Q} : f^*ᵖ(P⊗Q) ⟶ f^*ᵖP ⊗ f^*ᵖQ` by `Adjunction.leftAdjointOplaxMonoidal` (leaf B2,
a one-liner once this is data). -/
theorem nonempty_pushforward_laxMonoidal :
    Nonempty ((pushforward.{u} φ).LaxMonoidal) := by
  sorry

end LaxPushforward

section FreeYonedaTensor

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **[D-PresPB′-general], leaf G1 (the lattice miracle).** On the Opens-site of a scheme, the
presheaf tensor of two free-yoneda presheaves of modules is the free-yoneda of the meet:
pointwise, `Hom(V,U₁) × Hom(V,U₂) = [V ≤ U₁ ⊓ U₂]` (a meet-semilattice has representable
products of representables), and the free-module functor sends products of types to tensor
products of free modules (`finsuppTensorFinsupp`-style). Together with mathlib's
`freeFunctorCompPullbackIso` this makes the oplax comparison `δ` an isomorphism on free-yoneda
pairs — before sheafifying. -/
theorem nonempty_freeYoneda_tensor_iso (U₁ U₂ : X.Opens) :
    Nonempty (((free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
        (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂) :
          PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (U₁ ⊓ U₂))) := by
  sorry

end FreeYonedaTensor

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **[D-PresPB′-general], payoff packaging (leaves G3 + A).** The pullback of sheaves of
modules along an arbitrary morphism of schemes is a monoidal functor for the (v10.97)
localized-monoidal structures: the objectwise content is the general-`f` sheafified
pullback–tensor comparison (`nonempty_sheafify_presheafPullback_tensor`, extended from the
free-yoneda generators by two single-variable presentation passes in the abelian
`SheafOfModules`), packaged through `functorMonoidalOfComp` with the `Lifting` instance
`sheafificationCompPullback`. Consumer: `Skeleton.monoidHom` then gives
`Pic(f) : Pic X →* Pic Y` — the GME (2.16) Picard functor. -/
theorem nonempty_pullback_monoidal (f : Y ⟶ X) :
    letI := Modules.monoidalCategory X
    letI := Modules.monoidalCategory Y
    Nonempty ((Modules.pullback f).Monoidal) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
