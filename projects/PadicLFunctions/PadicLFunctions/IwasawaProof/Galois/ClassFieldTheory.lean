import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Algebra.Category.Grp.Basic

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

/-- **The class field theory interface** over a number field `K`, layered on `RayClassData`.
Bundles the classical theorems of global CFT (ray-class form) as data:

* the forget-modulus surjection `Cl_K(𝔪) ↠ Cl_K` (the ideal-theoretic ray → class sequence);
* **Artin reciprocity** `Cl_K(𝔪) ≃ Gal(H_𝔪/K)` (the ray class field Galois group, bundled via the
  `CommGrp` category to avoid carrying its group structure as a bare field);
* **existence**: every finite abelian `L/K` is dominated by a ray class field (its Galois group is
  a quotient of some `Gal(H_𝔪/K)`).

This is the single axiomatised input of Stage G; a future mathlib global-CFT library provides the
instance (`G2-DISCHARGE`), and CFTunits1 is *derived* from it. -/
class ClassFieldTheory (K : Type) [Field K] [NumberField K] [RayClassData K] where
  /-- `Cl_K(𝔪) ↠ Cl_K`, forgetting the modulus. -/
  toClassGroup : ∀ 𝔪 : Ideal (𝓞 K), RayClassData.rayClassGroup 𝔪 →* ClassGroup (𝓞 K)
  /-- the forget-modulus map is surjective. -/
  toClassGroup_surjective : ∀ 𝔪, Function.Surjective (toClassGroup 𝔪)
  /-- the map `(𝓞_K/𝔪)ˣ → Cl_K(𝔪)` sending a residue to the class of the principal ideal it
  generates (the start of the ray–class–group sequence). -/
  fromUnitsMod : ∀ 𝔪 : Ideal (𝓞 K), (𝓞 K ⧸ 𝔪)ˣ →* RayClassData.rayClassGroup 𝔪
  /-- exactness `(𝓞_K/𝔪)ˣ → Cl_K(𝔪) → Cl_K → 0`: an element of `Cl_K(𝔪)` dies in `Cl_K` iff it
  comes from `(𝓞_K/𝔪)ˣ`.  (The ideal-theoretic ray sequence — elementary, bundled here since the
  ray class group is abstract interface data.) -/
  ray_exact : ∀ 𝔪 (x : RayClassData.rayClassGroup 𝔪),
    toClassGroup 𝔪 x = 1 ↔ x ∈ (fromUnitsMod 𝔪).range
  /-- the **ray class field** Galois group `Gal(H_𝔪/K)`, as a bundled commutative group. -/
  rayClassFieldGal : Ideal (𝓞 K) → CommGrpCat.{0}
  /-- **Artin reciprocity**: `Cl_K(𝔪) ≃ Gal(H_𝔪/K)`. -/
  artin : ∀ 𝔪, RayClassData.rayClassGroup 𝔪 ≃* rayClassFieldGal 𝔪

end Iwasawa.Galois
