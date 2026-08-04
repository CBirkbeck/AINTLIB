/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.RootSplitting

/-!
# Root-powers on points, and the exponent step of `hdet` (route β, item (B))

`hdet` (`WeilPairing/DetCocycle.lean`) compares two composites
`γ ≫ rootPower N ζ k ≫ muNMapAlong p N`. Both are `W`-points of `μ_{N,S}` — *not* of `μ_{N,S'}` — and
their structure maps to `S` agree, because the two projections of the kernel pair agree after `→ S`.
So the comparison can be made by **values**, and the two lemmas that compute those values already
exist in `GroupScheme/MuN.lean`:

* `muNPointsEquiv_mapAlong` — the base-change comparison `muNMapAlong` does not change the value;
* `muNPointsEquiv_natural` — restriction along `k` acts on values by `Γ.map k.op`.

Together with `rootPower`'s definition (the point with value `ζ ^ k.val`) this reduces `hdet`'s
exponent step to a single equation in `Γ(W, ⊤)`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S' S : Scheme.{u}} (N : ℕ) [NeZero N]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The value of `rootPower N ζ k` is `ζ ^ k.val` — `rootPower` is by definition the point
`muNPointsEquiv` sends to that root of unity. -/
theorem muNPointsEquiv_rootPower (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (k : ZMod N) :
    (muNPointsEquiv S' N (𝟙 S') ⟨rootPower N ζ k, rootPower_π N ζ k⟩ :
        Γ(S', (⊤ : S'.Opens))) =
      (ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val := by
  have h : (⟨rootPower N ζ k, rootPower_π N ζ k⟩ :
      { h : S' ⟶ muN S' N // h ≫ muNπ S' N = 𝟙 S' }) =
      (muNPointsEquiv S' N (𝟙 S')).symm
        ⟨(ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val, by
          rw [← pow_mul, mul_comm, pow_mul, ζ.2, one_pow]⟩ := Subtype.ext rfl
  rw [h, Equiv.apply_symm_apply]

/- **(route β, item (B)) — NOT YET LANDED.** The exponent step

`comp_rootPower_muNMapAlong_eq`:  for `α β : W ⟶ S'` with `α ≫ p = β ≫ p`, and exponents `m m'` with
  `Γ(α)(ζ) ^ m.val = Γ(β)(ζ) ^ m'.val`  in `Γ(W, ⊤)`,
  `α ≫ rootPower N ζ m ≫ muNMapAlong p N = β ≫ rootPower N ζ m' ≫ muNMapAlong p N`.

The mathematical content is settled — inject by `muNPointsEquiv S N (α ≫ p)` (both sides *do* lie over
that map, by `hover` below plus `hp`), then compute each value by `muNPointsEquiv_mapAlong` followed by
`muNPointsEquiv_natural` and `muNPointsEquiv_rootPower` above. The obstruction is purely elaborative:
`muNPointsEquiv_mapAlong`'s statement bakes in a *specific* proof term for the section condition, so
the value computation must be threaded by `Eq.trans`/`exact` rather than `rw` (proof terms are defeq
but not syntactically equal), and the naive `rw`-based script hits `isDefEq` timeouts on
`muNPointsEquiv`. The `hover` half is trivial and is recorded here for reuse:

  `(γ ≫ rootPower N ζ k ≫ muNMapAlong p N) ≫ muNπ S N = γ ≫ p`
  by `muNMapAlong_π` then `rootPower_π`.

Next attempt should state the value lemma in exactly the shape `muNPointsEquiv_mapAlong` produces
(`⟨v.1 ≫ muNMapAlong g N, _⟩` for `v := ⟨γ ≫ rootPower N ζ k, _⟩`) so that no reassociation `rw` is
needed at all. -/

end ModularCurves
