/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.SubgroupQuotientConstruction

/-!
# The subgroup-scheme quotient glue: the equalizer-subring model (`[HG-C4c-2]`)

Design v10.190-G0. For **any** stable open `W ⊆ E` the quotient functions are the equalizer
subring of the two restricted-leg section maps — no affineness, no Künneth:
`quotientRing W := eqLocus Γ(act|_W) Γ(pr|_W)`, glued via restriction-descended transitions
on the `ForMathlib/SchemeQuotient` pattern. The Hopf layer (C4a/C4b, proven) enters only
through the per-affine-patch comparison `quotientRing P.U = coinvariants P.chartCoaction`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)

/-- The action-side section map of a stable open: sections of `W` pulled back along the
restricted translation action. -/
noncomputable def actRing {W : E.E.Opens} (hW : G.IsStableOpen W) :
    Γ(E.E, W) ⟶ Γ((Over.mk G.π ⊗ E.asOver).left, G.actionProj.left ⁻¹ᵁ W) :=
  W.topIso.inv ≫ (G.restrictedAction hW).appTop ≫ (G.actionProj.left ⁻¹ᵁ W).topIso.hom

/-- The projection-side section map of a stable open. -/
noncomputable def prRing (W : E.E.Opens) :
    Γ(E.E, W) ⟶ Γ((Over.mk G.π ⊗ E.asOver).left, G.actionProj.left ⁻¹ᵁ W) :=
  W.topIso.inv ≫ (G.restrictedProj W).appTop ≫ (G.actionProj.left ⁻¹ᵁ W).topIso.hom

/-- **The quotient ring of a stable open**: the subring of sections on which the translated
and projected pullbacks agree — the invariant functions. -/
noncomputable def quotientRing {W : E.E.Opens} (hW : G.IsStableOpen W) : Subring Γ(E.E, W) :=
  RingHom.eqLocus (G.actRing hW).hom (G.prRing W).hom

/-- **The local quotient of a stable open**: the spectrum of its invariant functions. -/
noncomputable def localQuotientOpen {W : E.E.Opens} (hW : G.IsStableOpen W) : Scheme.{u} :=
  Spec (CommRingCat.of (G.quotientRing hW))

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
