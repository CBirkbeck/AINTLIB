/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import ModularCurves.Moduli.MellWeierstrass

/-!
# T-E8: the stack statements for `M_ell^W` (statement-level bridge)

The [U/G] moduli pseudofunctor of Weierstrass data, `MellWScheme : Schemeᵒᵖ ⥤ Cat`
(`Moduli/MellWeierstrass.lean`, T-W6), packaged for mathlib's descent machinery
(`CategoryTheory.Pseudofunctor.IsStack`, Stacks 026F), with the two stack CLAIMS of
the v8/T-E8 layer stated over it: `M_ell^W` is a stack for the Zariski and for the
étale topology on `Scheme`.

**Statement-level only** (board v10.55 tail dispatch, non-load-bearing bridge): the
two `IsStack` theorems are registered WIP; their proofs are T-E8 proper — Zariski
descent = gluing Weierstrass data along opens (consumes the T-W4 dictionary and the
T-W6 groupoid presentation); étale descent additionally consumes torsor descent
(T-Q5/A711 layer). Nothing here is consumed by the active representability streams —
Y(N)/Y₁(N) ride the (Ell)-relative engine, not stack descent.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Bicategory

namespace ModularCurves

/-- The `[U/G]` moduli functor `MellWScheme` promoted to a pseudofunctor out of the
locally discrete bicategory, in the input shape of mathlib's descent machinery
(`Pseudofunctor.IsStack`). Non-load-bearing packaging: `Functor.toPseudofunctor'`
with identity/composition 2-cells by `eqToIso`. -/
noncomputable def mellWPseudofunctor :
    LocallyDiscrete (Scheme.{u})ᵒᵖ ⥤ᵖ Cat.{u, u} :=
  MellWScheme.toPseudofunctor'

/-- **(T-E8, Zariski clause — STATEMENT)** `M_ell^W` is a stack for the Zariski
topology: Weierstrass data and their coordinate-change isomorphisms glue along open
covers. Registered WIP (proof = T-E8 proper; Zariski descent through the T-W4
dictionary and the T-W6 groupoid presentation). -/
theorem mellWPseudofunctor_isStack_zariski :
    mellWPseudofunctor.{u}.IsStack Scheme.zariskiTopology := by
  sorry

/-- **(T-E8, étale clause — STATEMENT)** `M_ell^W` is a stack for the étale topology
(the moduli stack of Weierstrass data is an étale stack; the classical `M_ell` layer
sits over it via the T-W7 comparison). Registered WIP (proof = T-E8 proper; consumes
étale torsor descent, T-Q5/A711 layer). -/
theorem mellWPseudofunctor_isStack_etale :
    mellWPseudofunctor.{u}.IsStack Scheme.etaleTopology := by
  sorry

end ModularCurves
