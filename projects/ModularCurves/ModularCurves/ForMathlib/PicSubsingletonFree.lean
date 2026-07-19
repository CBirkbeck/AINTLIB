/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib

/-!
# Invertible modules over a ring with trivial Picard group are free

Over a commutative ring `R` whose Picard group `CommRing.Pic R` is trivial
(`Subsingleton (Pic R)`), every invertible `R`-module is free of rank one. Here "invertible"
is mathlib's `Module.Invertible R M`: the canonical contraction `Mᵛ ⊗[R] M → R` is an
isomorphism (equivalently, `M ⊗[R] N ≃ₗ[R] R` for some `N`). An element of `Pic R` *is* an
iso-class of invertible module, so `Subsingleton (Pic R)` says all such classes coincide with
the class of `R`.

## Note: this is essentially already in mathlib

`Mathlib/RingTheory/PicardGroup.lean` already contains the ring-level heart:

* `CommRing.Pic.subsingleton_iff` :
  `Subsingleton (Pic R) ↔ ∀ M, Module.Invertible R M → Module.Free R M`;
* the (universe-polymorphic in `M`) `instance [Subsingleton (Pic R)] : Module.Free R M` for
  invertible `M`;
* `Module.Invertible.free_iff_linearEquiv : Module.Free R M ↔ Nonempty (M ≃ₗ[R] R)`.

and the intended *supply* of `Subsingleton (Pic R)` for a **semilocal** ring is also there:

* `[Finite (MaximalSpectrum R)] : Subsingleton (Pic R)` (semilocal Picard triviality), and
  `[IsLocalRing R] : Subsingleton (Pic R)`, `[IsDomain R] [Nonempty (NormalizedGCDMonoid R)]`, …

This file therefore adds **no new mathematics**. It only repackages those facts as
explicit-hypothesis named lemmas whose signatures match what the semilocal ω-triviality
mouth-core (`exists_localModel_core_at`, `Moduli/EngineDescent.lean`) consumes: an invertible
module over a ring with trivial Picard group is free, is isomorphic to the ring, and — the form
mathlib does not state verbatim — carries a concrete rank-one basis `Basis (Fin 1) R M`.
All proofs are one-liners over the mathlib API.
-/

open CommRing (Pic)

namespace Module

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- **Trivial Picard group ⟹ invertible modules are free.** Over a commutative ring `R` with
`Subsingleton (Pic R)`, every invertible `R`-module `M` is free.

This is a thin, explicit-hypothesis wrapper over mathlib's
`instance [Subsingleton (Pic R)] : Module.Free R M`
(see `CommRing.Pic.subsingleton_iff`). -/
theorem free_of_subsingleton_pic (hPic : Subsingleton (Pic R)) [Module.Invertible R M] :
    Module.Free R M :=
  haveI := hPic
  inferInstance

/-- **Trivial Picard group ⟹ every invertible module is isomorphic to the base ring.** Combines
`free_of_subsingleton_pic` with `Module.Invertible.free_iff_linearEquiv`. -/
theorem nonempty_linearEquiv_self_of_subsingleton_pic (hPic : Subsingleton (Pic R))
    [Module.Invertible R M] : Nonempty (M ≃ₗ[R] R) :=
  Module.Invertible.free_iff_linearEquiv.mp (free_of_subsingleton_pic R M hPic)

/-- **Trivial Picard group ⟹ every invertible module has a rank-one basis.** The concrete
`Basis (Fin 1) R M` form — a single global basis element — obtained by transporting the standard
basis of `R` along the isomorphism `R ≃ₗ[R] M`. This is the shape the semilocal ω-triviality
mouth-core needs (an `OmegaBasis`/global trivialisation of the `ω` line bundle). -/
theorem nonempty_basis_fin_one_of_subsingleton_pic (hPic : Subsingleton (Pic R))
    [Module.Invertible R M] : Nonempty (Basis (Fin 1) R M) :=
  (nonempty_linearEquiv_self_of_subsingleton_pic R M hPic).map fun e =>
    (Basis.singleton (Fin 1) R).map e.symm

end Module
