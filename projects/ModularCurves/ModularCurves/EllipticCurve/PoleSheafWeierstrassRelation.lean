/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafMonomialBasis

/-!
# The Weierstrass relation from the pole filtration

The rank-six pole basis makes the square of a normalized pole-order-three
section monic over the cube of a normalized pole-order-two section.
-/

namespace Module.Basis

/-- An element with final coordinate one in a six-element basis satisfies a
linear relation in generalized Weierstrass form. -/
theorem exists_fin_six_weierstrass_relation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis (Fin 6) R M) (q : M)
    (hq : b.repr q (Fin.last 5) = 1) :
    ∃ a₁ a₂ a₃ a₄ a₆ : R,
      q + a₁ • b 4 + a₃ • b 2 =
        b 5 + a₂ • b 3 + a₄ • b 1 + a₆ • b 0 := by
  let c := b.repr q
  refine ⟨-c 4, c 3, -c 2, c 1, c 0, ?_⟩
  have hq5 : b.repr q (5 : Fin 6) = 1 := hq
  apply b.ext_elem
  intro i
  fin_cases i <;> simp [c, hq5]

end Module.Basis
