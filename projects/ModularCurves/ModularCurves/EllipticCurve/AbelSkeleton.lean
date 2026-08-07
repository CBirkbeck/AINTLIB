/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.BaseChangeKerCoker
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech
import ModularCurves.Picard.InvertibleSheafBaseCechFlat
import ModularCurves.Picard.RigidDescent

/-!
# The degree-one cohomology package for the Abel route (`AP2-A0`)

Interface for the consolidated plan `[A′]` (`plan-ds4-abel-pairing.md`, STABLE round 19): the two
fibre facts that Katz–Mazur p. 66 and Hida pp. 107–108 both derive from "fibre-by-fibre of degree
one" and then consume — and which are the ONLY inputs the rest of their proofs use.

* KM p. 66: *"over an algebraically closed field, `H¹(E, ℒ) = 0` for `degree(ℒ) > 2g−2 = 0`"*, then
  rank one by relative Riemann–Roch.
* Hida p. 107: *"`H¹(E_s, ℒ(s))` is dual to `H⁰(E_s, ℒ(s)⁻¹ ⊗ Ω_{E_s/s})` by the Serre duality.
  Since `g = 1` … `deg < 0` and hence … `= 0`"*, then `rank_{𝒪_S}(f_*ℒ) = 1` by (2.1.6).

Named for what it asserts (cohomology), **not** `FibrewiseDegreeOne` — the tree has no degree notion
for an invertible sheaf, and "degree one ⟹ this package" is exactly `AP2-A1`, the one place such a
notion is needed. Phrased against the ordered base-Čech complex (the tree's derived-functor-free
surrogate; mathlib has no `R¹f_*`), for an **arbitrary** invertible `M`, never `𝒪(n[0])` —
specialising and identifying via relative Abel is circular (`b2_log.jsonl`, `KM-SEESAW-1`/`-2prime`).

The exactness clause runs over **every** `n < card ι` (positive-degree vanishing; the terminal case
is tautological since `C^q = 0` for `q ≥ card ι`) — the range the finite-homology base-change route
consumes (round 14; `Function.Exact (d n) (d (n+1))` is exactness at `C^{n+1}`, so `H⁰ = ker d⁰` is
untouched and the rank-one clause is consistent). The `∧` is a def-bundle over the shared quantifier
`K` with per-property projections below, per `references/statement-splitting.md`.

An earlier skeleton here carried two theorems with a vacuous `hdeg` placeholder — **false as
stated** (round 14 counterexamples: `𝒪_E`, genus two `𝒪(P)`, `𝒪_E(2[0])`, `ℙ¹` with `𝒪(1)`).
Deleted by `AP2-A0`; the content returns as `AP2-A1` (degree ⟹ package, RR at field level) and
`AP2-A2` (package ⟹ `f_*M` invertible + base-change compatible, finite-homology route only).
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace ModularCurves

/-- **(AP2-A0, the `[A′]` interface)** `M` has the degree-one fibre cohomology package: after base
change to every field over the base ring, the ordered base-Čech complex is exact in every positive
degree and its degree-zero kernel — `Γ` of the fibre — is one-dimensional.

Sources: Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 66; Hida, *GME*, pp. 107–108. -/
def HasDegreeOneFibreCohomology {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K],
    (∀ n, n < Fintype.card ι →
      Function.Exact
        (((orderedBaseCechComplex π M U).d n (n + 1)).hom.baseChange K)
        (((orderedBaseCechComplex π M U).d (n + 1) (n + 2)).hom.baseChange K)) ∧
    Module.finrank K
      (LinearMap.ker (((orderedBaseCechComplex π M U).d 0 1).hom.baseChange K)) = 1

/-- Positive-degree exactness projection of `HasDegreeOneFibreCohomology`. -/
theorem HasDegreeOneFibreCohomology.exact {X S : Scheme.{u}} {π : X ⟶ S} {M : X.Modules}
    {ι : Type u} [Fintype ι] [LinearOrder ι] {U : ι → X.Opens}
    (h : HasDegreeOneFibreCohomology π M U)
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K]
    (n : ℕ) (hn : n < Fintype.card ι) :
    Function.Exact
      (((orderedBaseCechComplex π M U).d n (n + 1)).hom.baseChange K)
      (((orderedBaseCechComplex π M U).d (n + 1) (n + 2)).hom.baseChange K) :=
  (h K).1 n hn

/-- Kernel-rank projection of `HasDegreeOneFibreCohomology`: the degree-zero Čech kernel is
one-dimensional over every field over the base ring. -/
theorem HasDegreeOneFibreCohomology.kernel_finrank {X S : Scheme.{u}} {π : X ⟶ S} {M : X.Modules}
    {ι : Type u} [Fintype ι] [LinearOrder ι] {U : ι → X.Opens}
    (h : HasDegreeOneFibreCohomology π M U)
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    Module.finrank K
      (LinearMap.ker (((orderedBaseCechComplex π M U).d 0 1).hom.baseChange K)) = 1 :=
  (h K).2

end ModularCurves
