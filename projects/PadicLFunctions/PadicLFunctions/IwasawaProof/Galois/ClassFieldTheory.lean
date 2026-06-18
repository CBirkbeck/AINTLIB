import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# An interface to global class field theory (ray-class form)  (S13-G, G2-CFT)

The **single axiomatised input** of the Galois side of the Iwasawa Main Conjecture
(`.mathlib-quality/plan-G.md`, expert review 2026-06-18).  Rather than a bespoke
cyclotomic-tower sequence, we assume the *general classical theorem of global class field
theory* in ray-class / ideal-theoretic form, for arbitrary number fields, and **derive** the
specialised CFTunits1 sequence from it (tickets G2-RAYSEQ / G2-DEDUCE / G2-LIMIT).  Chosen so a
future mathlib global-CFT library discharges the whole thing by *instantiation* (`G2-DISCHARGE`).

This file builds the interface in layers:

* `RayClassData K` — the ray class groups `Cl_K(𝔪)` of `K` as a family of finite abelian groups
  (the bare data + algebraic structure).
* `ClassFieldTheory K` (later) — Artin reciprocity (`Cl_K(𝔪) ≃ Gal(H_𝔪/K)`), existence, and the
  conductor–ramification correspondence, layered over `RayClassData`.

(Will move to `Common/` so every monorepo project can use it.)
-/

noncomputable section

namespace Iwasawa.Galois

open NumberField

/-- **Ray class groups as data.**  For a number field `K`, a family of finite abelian groups
`Cl_K(𝔪)` indexed by moduli `𝔪 : Ideal (𝓞 K)` (the archimedean part of the modulus is implicit;
for totally real fields it is folded into the ray class field on the CFT layer).  This is the
ideal-theoretic ray class group — exactly the object a future global-CFT library will provide. -/
class RayClassData (K : Type) [Field K] [NumberField K] where
  /-- the ray class group `Cl_K(𝔪)`. -/
  rayClassGroup : Ideal (𝓞 K) → Type
  /-- `Cl_K(𝔪)` is an abelian group. -/
  commGroup : ∀ 𝔪, CommGroup (rayClassGroup 𝔪)
  /-- `Cl_K(𝔪)` is finite. -/
  finite : ∀ 𝔪, Finite (rayClassGroup 𝔪)

/-- `Cl_K(𝔪)` is a commutative group (instance form of `RayClassData.commGroup`). -/
instance instCommGroupRayClassGroup {K : Type} [Field K] [NumberField K] [RayClassData K]
    (𝔪 : Ideal (𝓞 K)) : CommGroup (RayClassData.rayClassGroup 𝔪) :=
  RayClassData.commGroup 𝔪

/-- `Cl_K(𝔪)` is finite (instance form of `RayClassData.finite`). -/
instance instFiniteRayClassGroup {K : Type} [Field K] [NumberField K] [RayClassData K]
    (𝔪 : Ideal (𝓞 K)) : Finite (RayClassData.rayClassGroup 𝔪) :=
  RayClassData.finite 𝔪

end Iwasawa.Galois
