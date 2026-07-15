/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The algebra-hom lift of an `Away` localization (ForMathlib)

`IsLocalization.Away.liftAlgHom` — an `R`-algebra map `g : A →ₐ[R] P` sending `a` to a unit lifts to
an `R`-algebra map `Localization.Away a →ₐ[R] P` — is now in mathlib
(`Mathlib/RingTheory/Localization/Away/Basic.lean`), together with `liftAlgHom_apply`,
`coe_liftAlgHom` and `lift_eq`. This module previously carried a local duplicate; it has been removed
and all uses rewired to mathlib's version. The module is kept as a thin re-export so downstream
imports keep resolving.
-/
