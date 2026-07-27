/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# The agreement locus of two maps into an étale morphism is clopen (YFULL route γ)

For `f : X ⟶ S` formally unramified, locally of finite type, and separated (in
particular for `f` étale), and two `S`-maps `a b : Z ⟶ X` with `a ≫ f = b ≫ f`, the
scheme-theoretic **agreement locus** — the pullback of the relative diagonal
`pullback.diagonal f` along `pullback.lift a b` — includes into `Z` by a morphism that is
simultaneously an open immersion (the diagonal of an unramified morphism is an open
immersion) and a closed immersion (the diagonal of a separated morphism is a closed
immersion). Hence its range in `Z` is **clopen**.

This is the topological engine of the `Y(N)` clopen full-level locus (route γ): the locus
where two of the `N²` torsion sections `[a]P + [b]Q` coincide is the agreement locus of
two sections of the finite-étale `E[N] ×_S E[N] → S`, hence clopen; the full-level locus
is the complement of the union of these finitely many closed agreement loci, hence open.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S)

/-- The inclusion of the agreement locus of `a, b : Z ⟶ X` (over `f`) into `Z`: the
pullback of the relative diagonal `pullback.diagonal f` along `pullback.lift a b`. -/
noncomputable def agreementι (a b : Z ⟶ X) (hab : a ≫ f = b ≫ f) :
    pullback (pullback.lift a b hab) (pullback.diagonal f) ⟶ Z :=
  pullback.fst (pullback.lift a b hab) (pullback.diagonal f)

/-- For `f` formally unramified and locally of finite type, the agreement-locus inclusion
is an open immersion (pullback of the open-immersion relative diagonal). -/
instance isOpenImmersion_agreementι [FormallyUnramified f] [LocallyOfFiniteType f]
    (a b : Z ⟶ X) (hab : a ≫ f = b ≫ f) :
    IsOpenImmersion (agreementι f a b hab) := by
  haveI : IsOpenImmersion (pullback.diagonal f) :=
    FormallyUnramified.isOpenImmersion_diagonal f
  exact inferInstanceAs (IsOpenImmersion (pullback.fst _ _))

/-- For `f` separated, the agreement-locus inclusion is a closed immersion (pullback of
the closed-immersion relative diagonal). -/
instance isClosedImmersion_agreementι [IsSeparated f]
    (a b : Z ⟶ X) (hab : a ≫ f = b ≫ f) :
    IsClosedImmersion (agreementι f a b hab) := by
  haveI : IsClosedImmersion (pullback.diagonal f) :=
    ‹IsSeparated f›.isClosedImmersion_diagonal
  exact inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

/-- **The agreement locus of two maps into an étale morphism is clopen.** For `f`
formally unramified, locally of finite type, and separated, the range in `Z` of the
agreement-locus inclusion of `a b : Z ⟶ X` (with `a ≫ f = b ≫ f`) is clopen. -/
theorem isClopen_range_agreementι [FormallyUnramified f] [LocallyOfFiniteType f]
    [IsSeparated f] (a b : Z ⟶ X) (hab : a ≫ f = b ≫ f) :
    IsClopen (Set.range (agreementι f a b hab).base) :=
  ⟨(IsClosedImmersion.isClosedEmbedding
      (agreementι f a b hab)).isClosed_range,
    (agreementι f a b hab).isOpenEmbedding.isOpen_range⟩

end AlgebraicGeometry
