/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import ModularCurves.ForMathlib.EtaleIsoLocus

/-!
# The iso-locus of a finite locally free morphism (YFULL route γ, [YF-ISOLOC])

For a finite, flat, locally-finitely-presented morphism `ψ : X ⟶ S` (a *finite locally
free* morphism), the rank function `finrank ψ : S → ℕ` is locally constant
(mathlib `Scheme.Hom.isLocallyConstant_finrank`), so each rank level set is clopen. In
particular the **rank-`1` locus** `{s | finrank ψ s = 1}` is clopen, and over it `ψ`
restricts (by base change) to an isomorphism (`Scheme.Hom.isIso_iff_finrank_eq`).

This is the trivialization-free, `finrank`-only core of the `Y(N)` clopen leaf
`isOpenImmersion_levelSpaceΓι` (route γ of the CHARTER-YFULL audit): for `N` invertible
`E[N] ×_S E[N]` is finite étale, and the full-level locus is exactly the locus where the
tautological classifier of the `N²` sections `[a]P + [b]Q` becomes an isomorphism of
finite locally free `E[N]`-schemes — no étale-local trivialization `E[N] ≅ (ℤ/N)²` and
no rank count is needed, only the locally-constant rank.

Since `Etale ⟹ Flat` and `Etale ⟹ LocallyOfFinitePresentation` are instances, the
results apply verbatim to any finite étale `ψ` with only `[IsFinite ψ] [Etale ψ]` in
scope.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (ψ : X ⟶ S)
  [IsFinite ψ] [Flat ψ] [LocallyOfFinitePresentation ψ]

/- `isClopen_finrank_eq` is NOT restated here: the identical theorem (same namespace, same
statement) already lives in `ForMathlib/EtaleIsoLocus.lean`. The duplication was invisible
while both files were unreachable from the root import. -/

/-- The rank-`n` locus of a finite locally free morphism, as an open subscheme of the
base (it is in fact clopen — `isClopen_finrank_eq`). -/
noncomputable def finrankLocus (n : ℕ) : S.Opens :=
  ⟨{s : S | ψ.finrank s = n}, (isClopen_finrank_eq ψ n).2⟩

@[simp] theorem mem_finrankLocus {n : ℕ} {s : S} :
    s ∈ finrankLocus ψ n ↔ ψ.finrank s = n := Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **[YF-ISOLOC], iso half.** Over the rank-`1` locus, a finite locally free morphism
restricts (by base change along the open immersion of the locus) to an isomorphism. -/
theorem isIso_pullbackSnd_finrankLocus_one :
    IsIso (pullback.snd ψ (finrankLocus ψ 1).ι) := by
  haveI : IsFinite (pullback.snd ψ (finrankLocus ψ 1).ι) :=
    MorphismProperty.pullback_snd _ _ ‹IsFinite ψ›
  haveI : LocallyOfFinitePresentation (pullback.snd ψ (finrankLocus ψ 1).ι) :=
    MorphismProperty.pullback_snd _ _ ‹LocallyOfFinitePresentation ψ›
  rw [(pullback.snd ψ (finrankLocus ψ 1).ι).isIso_iff_finrank_eq]
  funext u
  rw [Scheme.Hom.finrank_pullback_snd, Pi.one_apply]
  exact u.2

end AlgebraicGeometry
