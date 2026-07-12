/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves stream D
-/
import ModularCurves.GroupScheme.NIsogeny
import ModularCurves.ForMathlib.GrassmannianGlueData

/-!
# The moduli space of `N`-isogeny data ([L15] = KM 6.5.1) — STREAM-NISOG wave M2

KM Proposition 6.5.1 (print p. 165, verbatim): *"Given `E/S`, view `E[N]/S` as the `Spec`
of a coherent sheaf `𝓕` of bi-algebras on `S` which is locally free of rank `N²`. A
subgroup `G ⊆ E[N]` of the type being sought is nothing other than a locally free rank-`N`
quotient `𝔥` of `𝓕`, such that the locally free rank `N²−N` kernel `𝒦 ⊆ 𝓕` is a bi-ideal
in `𝓕`. Therefore `[N-Isog]` is relatively represented by a closed subscheme of the
Grassmannian of all rank `N` quotients of `𝓕`."*

This file executes the decomposition `.mathlib-quality/decomposition-nisog-L15.md`:

* [L15-b] the dictionary: `N`-isogeny data ↔ Grassmannian members (`Module.Grassmannian`,
  whose members are exactly KM's kernels `𝒦` with locally free rank-`N` quotient) that are
  bi-ideals. The bialgebra structure on the torsion sections is **hypothesis-wired**: c5β's
  E[N]-package (CHARTER-C5B-2) supplies the finite-locally-free facts, and NEW-HOPF's pins
  supply the comultiplication; until they land, both enter as explicit hypotheses/data.
* [L15-c] the relative Grassmannian over `S` (charts = fable-FP's `grassmannianScheme`
  over trivializing affines; delivered gate, zero sorries).
* [L15-d] the bi-ideal locus is closed (T-D15/LFP-arc toolbox).
* [L15-e] classification via `pointOfMember` (gate-proven forward map).
* [L15-f] finiteness (KM's fibre count; c5β substrate hypothesis-wired).
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

universe u

namespace ModularCurves

/-! ## The bi-ideal condition (KM 6.5.1's "is a bi-ideal in 𝓕")

Stated abstractly for a commutative ring `A`, an `A`-algebra `F` carrying comultiplication
and counit data (the bialgebra structure of the torsion sections — supplied by the
NEW-HOPF pins at consumption time), and a submodule `K ⊆ F`. -/

/-- **(KM 6.5.1, the cut condition)** A submodule `K` of an `A`-bialgebra `F` (presented
by explicit comultiplication `Δ` and counit `ε` data) is a *bi-ideal* when it is an ideal,
is killed by the counit, and is a coideal for the comultiplication:
`Δ K ⊆ K ⊗ F + F ⊗ K`. These are the equations KM cuts the Grassmannian by. -/
def IsBiIdeal {A : Type u} [CommRing A] {F : Type u} [CommRing F] [Algebra A F]
    (Δ : F →ₐ[A] F ⊗[A] F) (ε : F →ₐ[A] A) (K : Submodule A F) : Prop :=
  (∀ (f : F) (k : F), k ∈ K → f * k ∈ K) ∧
    (∀ k ∈ K, ε k = 0) ∧
      ∀ k ∈ K, Δ k ∈
        LinearMap.range (TensorProduct.map K.subtype (LinearMap.id (R := A) (M := F))) ⊔
          LinearMap.range (TensorProduct.map (LinearMap.id (R := A) (M := F)) K.subtype)

end ModularCurves
