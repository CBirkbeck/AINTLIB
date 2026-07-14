/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.Representability
import ModularCurves.EllipticCurve.Rigidity

/-!
# Additivity of section-pullback over locally noetherian bases (T-E4a-noeth)

`EllHom.pullSection_add_of_isLocallyNoetherian`: SUPERSEDED alias of the now-unrestricted
`EllHom.pullSection_add` (de-sorried 2026-07-14 via the K4 records-level canonicity
supply; machinery moved to `Moduli/Representability.lean`).

This is GME Cor 2.2.5 made effective through the canonicity chain: the cartesian square of
`f` gives a pointed isomorphism from `X.curve.E` onto the chosen pullback — the total
space of `(Y.curve).baseChange f.baseHom` — and `isMonHom_of_one_comp_eq'` (GIT Cor 6.4
over a locally noetherian base, T-W7.7) makes that isomorphism a homomorphism of the two
independent group structures. The base-changed side is additive by the T-H2b dictionary
(`Point.baseChangeEquiv`) and `Point.pull_add`, and injectivity of the transport closes.

The unrestricted statement (`EllHom.pullSection_add`, Representability.lean) stays parked
behind the arbitrary-base canonicity upgrade T-W7.8 per the owner decision (2026-07-08):
`EllObj R` keeps arbitrary bases.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

universe u

namespace ModularCurves

namespace EllHom

variable (R : CommRingCat.{u}) {X Y : EllObj R} (f : X ⟶ Y)

/-- **(T-E4a-noeth, SUPERSEDED)** The noetherian-restricted additivity, kept as an
alias: the unrestricted `EllHom.pullSection_add` was de-sorried (STREAM-OMEGA
2026-07-14) via the records-level canonicity primitive
`isMonHom_of_pointedIso_records` (K4 supply), which dissolved the T-W7.8 park-reason.
The comparison machinery (`curveIsoPullback`, `transportSection`, …) now lives in
`Moduli/Representability.lean` next to the theorem. -/
theorem pullSection_add_of_isLocallyNoetherian [IsLocallyNoetherian X.base]
    (P Q : Y.curve.Section) :
    EllHom.pullSection R f (P + Q)
      = EllHom.pullSection R f P + EllHom.pullSection R f Q :=
  EllHom.pullSection_add R f P Q

end EllHom

end ModularCurves
