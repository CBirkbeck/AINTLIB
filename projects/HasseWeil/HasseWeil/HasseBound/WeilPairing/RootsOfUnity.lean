/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Route 2A — the Weil-pairing codomain `μ_ℓ ≅ ℤ/ℓ` (pairing step 4)

The Weil pairing `e_ℓ : E[ℓ] × E[ℓ] → μ_ℓ` is multiplicative, valued in the `ℓ`-th roots of unity.
The finite-level residual `hscale` works with the **additive** symplectic form on `E[ℓ] ≅ (ℤ/ℓ)²`
valued in `ℤ/ℓ`. The bridge is the additive isomorphism `μ_ℓ ≅ ℤ/ℓ`, available whenever the base
field contains a primitive `ℓ`-th root of unity (true over `K̄` for `ℓ ≠ char K`).

This ships `rootsOfUnity_addEquiv_zmod`: `Additive (rootsOfUnity ℓ F) ≃+ ℤ/ℓ` from a primitive
`ℓ`-th root, by composing mathlib's `IsPrimitiveRoot.zmodEquivZPowers` with
`IsPrimitiveRoot.zpowers_eq` (`⟨ζ⟩ = μ_ℓ`).
-/

namespace HasseWeil.WeilPairing

/-- **`μ_ℓ ≅ ℤ/ℓ` additively** (the Weil-pairing codomain additivisation). For a field `F` with a
primitive `ℓ`-th root of unity `ζ`, the `ℓ`-th roots of unity (written additively) are isomorphic to
`ℤ/ℓ`. The Weil pairing's `μ_ℓ`-values are pushed through this to land in the symplectic form's
`ℤ/ℓ`. -/
noncomputable def rootsOfUnity_addEquiv_zmod {F : Type*} [Field F] {ℓ : ℕ} [NeZero ℓ] {ζ : Fˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) :
    Additive (rootsOfUnity ℓ F) ≃+ ZMod ℓ :=
  (hζ.zpowers_eq ▸ hζ.zmodEquivZPowers).symm

end HasseWeil.WeilPairing
