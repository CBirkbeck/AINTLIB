/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.EtaleDescent
import ModularCurves.ForMathlib.AdjoinRootBaseChange

/-!
# The `μ_N` finite étale algebra, in coordinates (WP-D3c-2b)

`muNAlgebra k N hk` (`WeilPairing/EtaleDescent.lean`) is defined as the global sections of the
scheme `μ_{N, Spec k}`, which is convenient for the Galois-descent machinery but opaque for
base change along a map of fields. Over a **field** the tree already has the explicit model
`muNSpecFieldIso : μ_{N,Spec k} ≅ Spec (k[X] ⧸ (X^N − 1))` (`GroupScheme/MuN.lean`), and this
file turns it into a `k`-algebra identification of the carriers.

With that plus `quotSpanBaseChange` (`ForMathlib/AdjoinRootBaseChange.lean`) the `μ_N` side of
the field-change transport of the Weil pairing becomes pure algebra.
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace ModularCurves

variable (k : Type u) [Field k] (N : ℕ) [NeZero N] (hk : (N : k) ≠ 0)

/- Note. The carrier of `muNAlgebra k N hk` is `Γ(muN (Spec k) N, ⊤)`, but its `Algebra k`
structure is installed by a `letI` **inside** `finiteEtaleOfπ`, so it is not available to
instance search here. Everything below is therefore stated at the level of rings; the algebra
structure is reattached at the use site, where `finiteEtaleOfπ`'s `letI` is in scope. -/

/-- **(WP-D3c-2b)** The `μ_N`-scheme over a field is affine, so its global sections are the
model ring: the underlying ring of `muNAlgebra k N hk` is isomorphic to `k[X] ⧸ (X^N − 1)`.

This is `Scheme.Γ` applied to `muNSpecFieldIso`, read through `Scheme.ΓSpecIso`. The
`k`-algebra compatibility — which is what the transport needs — is `muNSpecFieldIso_struct`. -/
noncomputable def muNCarrierRingEquiv :
    Γ(muN (Spec (CommRingCat.of k)) N, ⊤) ≃+* AdjoinRoot ((X : Polynomial k) ^ N - 1) :=
  ((Scheme.Γ.mapIso (muNSpecFieldIso k N).symm.op).trans
      (Scheme.ΓSpecIso
        (CommRingCat.of (AdjoinRoot ((X : Polynomial k) ^ N - 1))))).commRingCatIsoToRingEquiv

/-- **(WP-D3c-2b)** The inverse of `muNCarrierRingEquiv` is `Γ` of the model's structure map:
it sends the model ring into the carrier exactly as `muNSpecFieldIso` prescribes. Recorded as
the computation rule the algebra compatibility is proved from. -/
theorem muNCarrierRingEquiv_symm_apply
    (x : AdjoinRoot ((X : Polynomial k) ^ N - 1)) :
    (muNCarrierRingEquiv k N).symm x =
      (muNSpecFieldIso k N).hom.appTop.hom
        ((Scheme.ΓSpecIso
          (CommRingCat.of (AdjoinRoot ((X : Polynomial k) ^ N - 1)))).inv.hom x) :=
  rfl

end ModularCurves
