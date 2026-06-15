# Complete Topological Ring Category & 𝒱 — Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Define `CompleteTopCommRingCat`, the categories 𝒱^pre and 𝒱, and update
`IsSheafy`/`AdicSpace` to follow Wedhorn §8.1–§8.2 exactly.

**Architecture:** New file `CompleteTopCommRingCat.lean` for the bundled category,
then extend `StructureSheaf.lean` with 𝒱^pre/𝒱 definitions using
`PresheafedSpace CompleteTopCommRingCat`.

---

## Task 1: Define `CompleteTopCommRingCat`

**File:** Create `Adic spaces/CompleteTopCommRingCat.lean`

- Structure: `α`, `CommRing`, `TopologicalSpace`, `IsTopologicalRing`,
  `UniformSpace`, `IsUniformAddGroup`, `CompleteSpace`, `T0Space`
- Morphisms: `{ f : R →+* S // Continuous f }` (same as TopCommRingCat)
- Category, FunLike, ConcreteCategory instances
- HasForget₂ to TopCommRingCat, CommRingCat, TopCat

## Task 2: Define presheafValue as CompleteTopCommRingCat object

**File:** Modify `Adic spaces/Presheaf.lean`

- `presheafValueObj D : CompleteTopCommRingCat` — bundles `presheafValue D`
- `restrictionMapMor D D' h : presheafValueObj D ⟶ presheafValueObj D'` — bundles restriction map

## Task 3: Define 𝒱^pre and 𝒱

**File:** Modify `Adic spaces/StructureSheaf.lean`

- `VPreObj` — extends `PresheafedSpace CompleteTopCommRingCat` with valuations
- `VPreHom` — morphisms with valuation compatibility
- `Category VPreObj` instance
- `IsSheafTopRing` — Remark 8.20 condition
- `VObj` — full subcategory (sheaf version)
- Update `AffinoidAdicSpace` and `AdicSpace` definitions

## Task 4: Update imports

**File:** Modify `Adic spaces.lean`

- Add `import «Adic spaces».CompleteTopCommRingCat`
