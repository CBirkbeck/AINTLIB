/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalProperties.Projective

/-!
# Constant fibre rank over a reduced ring (Stacks 0FWG)

A finite module over a **reduced** ring whose fibre dimension `p ↦ dim_{κ(p)} (M ⊗ κ(p))` is
locally constant is finite locally free.

## Why this file exists

This is the *only* new commutative algebra the rank-one seesaw (`ForMathlib/Seesaw.lean`) needs,
and it is **not in mathlib** (searched 2026-08-08: `leansearch` on the statement,
`local_search "rankAtStalk"`, and `grep IsReduced` in `RingTheory/Spectrum/Prime/FreeLocus.lean`,
`RingTheory/Flat/Rank.lean`, `RingTheory/LocalProperties/Projective.lean` — all empty). It
replaces cohomology-and-base-change / Grauert, which mathlib also lacks: the seesaw applies it to
the **cokernel** of the tree's finite-projective replacement differential, whose fibre dimension
*is* locally constant by right-exactness of `⊗`, and reads off local freeness of the kernel from
the two resulting splittings.

## Source

Stacks Project, tag [0FWG]:

> "Let `R` be a reduced ring and let `M` be a finite `R`-module such that
> `p ↦ dim_{κ(p)} M ⊗_R κ(p)` is locally constant on `Spec(R)`. Then `M` is finite locally free."

## The proof, and where reducedness enters

Everything happens over the local ring `R_p`; note that every prime `q ⊆ p` lies in *every*
Zariski neighbourhood of `p` (if `g ∉ p` and `q ⊆ p` then `g ∉ q`), so local constancy at `p`
becomes **constancy on all of `Spec R_p`**. Then:

1. Nakayama (`IsLocalRing.map_tensorProduct_mk_eq_top`) lifts a `κ(𝔪)`-basis of the fibre to a
   surjection `g : R^n ↠ M`.
2. For every prime `q`, the induced `κ(q)^n → M ⊗ κ(q)` is surjective between spaces of the same
   dimension `n`, hence **bijective**.
3. So for `x ∈ ker g`, the image of `x` in `κ(q)^n` is zero, i.e. every coordinate `x i` lies
   in `q`.
4. Intersecting over all primes puts each `x i` in the nilradical — which is `0` because `R` is
   **reduced**. Hence `ker g = ⊥` and `g` is an isomorphism.

Note (external review, 2026-08-08): step 3 asserts that the *composite* `K → R^n → κ(q)^n`
vanishes, i.e. `K_q ⊆ q R_q^n`. It does **not** assert `K ⊗ κ(q) = 0`, which does not follow.
The Noetherian hypothesis is not needed anywhere; `Module.Finite R M` suffices.
-/

universe u

open Module
open scoped TensorProduct

namespace ModularCurves

/-- **(Stacks 0FWG, local form)** A finite module over a reduced local ring whose fibre dimension
is at least `n` at every prime, and exactly `n` at the closed point, is free.

The `n`-at-the-closed-point hypothesis is what Nakayama consumes; the `≥ n` at the other primes is
what upgrades "surjective" to "bijective" on each fibre. Both are supplied by local constancy of
the fibre dimension, since every prime of a local ring is a generization of the closed point. -/
theorem free_of_isReduced_of_forall_le_finrank_fiber
    {R : Type u} [CommRing R] [IsLocalRing R] [IsReduced R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ)
    (hclosed : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = n)
    (hmin : ∀ p : PrimeSpectrum R,
      n ≤ Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Free R M := by
  sorry

end ModularCurves
