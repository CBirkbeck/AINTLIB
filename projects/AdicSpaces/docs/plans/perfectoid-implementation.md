# Perfectoid Theory Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the 5 sub-projects from the perfectoid theory spec, creating 6 new library files and updating 15 Scottish Book problem files.

**Architecture:** Build definitions bottom-up: almost mathematics and pseudo-uniformizers first (independent), then perfectoid rings, then tilting + perfectoid spaces in parallel, finally the FF curve. Each file compiles independently. Deep theorems are sorry'd.

**Tech Stack:** Lean 4 v4.29.0-rc3, Mathlib v4.29.0-rc3. Key Mathlib deps: `PerfectRing`, `frobenius`, `WittVector`, `PreTilt`, `fontaineTheta`, `Module.annihilator`, `KaehlerDifferential`.

**Spec:** `docs/plans/perfectoid-theory.md`

---

## File Map

| File | Action | Responsibility |
|------|--------|---------------|
| `Adic spaces/AlmostMathematics.lean` | Create | AlmostSetup, IsAlmostZero, almost morphism properties |
| `Adic spaces/PseudoUniformizer.lean` | Create | IsPseudoUniformizer, PseudoUniformizer type |
| `Adic spaces/PerfectoidRing.lean` | Create | IsPerfectoidRing, IsPerfectoidField |
| `Adic spaces/Tilting.lean` | Create | PerfectoidRing.tilt, Ainf, theta map |
| `Adic spaces/PerfectoidSpace.lean` | Create | AffinoidPerfectoidSpace, IsPerfectoidSpace |
| `Adic spaces/FarguesFontaine.lean` | Create | Y_FF, X_FF, Frobenius action |
| `Adic spaces.lean` | Modify | Add imports for all new files |
| `Adic spaces/ScottishBook/Problem*.lean` | Modify | 15 problem files get formalized statements |

---

## Chunk 1: Foundation (Sub-projects 1 & 2a — parallel)

### Task 1: Almost Mathematics

**Files:**
- Create: `Adic spaces/AlmostMathematics.lean`

- [ ] **Step 1: Create AlmostMathematics.lean with core definitions**

Write the file with: `AlmostSetup V` class, `IsAlmostZero` predicate (element and module level), `LinearMap.IsAlmostInjective/IsAlmostSurjective/IsAlmostBijective`, basic lemmas.

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.KaehlerDifferential.Basic

/-!
# Almost Mathematics

The theory of "almost modules" over a ring `V` with an idempotent ideal `m`
(Gabber–Ramero, *Almost Ring Theory*, LNM 1800).

An element `x` of a `V`-module `M` is **almost zero** if `a • x = 0` for all `a ∈ m`.
A `V`-linear map is **almost injective/surjective** if its kernel/cokernel is almost zero.

## Main definitions

* `AlmostSetup V` : A ring `V` with a distinguished idempotent ideal `m` (`m² = m`).
* `IsAlmostZero V x` : Element `x` is annihilated by every element of `m`.
* `Module.IsAlmostZero V M` : Module `M` is annihilated by `m`.
* `LinearMap.IsAlmostInjective f` : Kernel of `f` is almost zero.
* `LinearMap.IsAlmostSurjective f` : Cokernel of `f` is almost zero.
* `Algebra.IsAlmostEtale V A B` : `B` is almost étale over `A`.

## References

* Gabber–Ramero, *Almost Ring Theory*, Springer LNM 1800
* Scholze, *Perfectoid Spaces*, §4 (almost mathematics in perfectoid context)
-/

universe u v

/-- A **basic almost setup** is a commutative ring `V` equipped with an idempotent
ideal `m` (satisfying `m * m = m`). In the perfectoid context, `V = O_K` and
`m` is the maximal ideal of a perfectoid field `K`. -/
class AlmostSetup (V : Type u) [CommRing V] where
  /-- The distinguished idempotent ideal. -/
  m : Ideal V
  /-- The ideal is idempotent: `m * m = m`. -/
  idempotent : m * m = m

namespace AlmostMath

variable {V : Type u} [CommRing V] [AlmostSetup V]
variable {M : Type v} [AddCommGroup M] [Module V M]

/-- An element `x` of a `V`-module is **almost zero** if `a • x = 0` for all `a ∈ m`. -/
def IsAlmostZero (x : M) : Prop :=
  ∀ a : V, a ∈ AlmostSetup.m (V := V) → a • x = 0

theorem IsAlmostZero.zero : IsAlmostZero (V := V) (0 : M) :=
  fun _ _ => smul_zero _

theorem IsAlmostZero.add {x y : M} (hx : IsAlmostZero (V := V) x)
    (hy : IsAlmostZero (V := V) y) : IsAlmostZero (V := V) (x + y) :=
  fun a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]

theorem IsAlmostZero.neg {x : M} (hx : IsAlmostZero (V := V) x) :
    IsAlmostZero (V := V) (-x) :=
  fun a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem IsAlmostZero.smul {x : M} (hx : IsAlmostZero (V := V) x) (r : V) :
    IsAlmostZero (V := V) (r • x) :=
  fun a ha => by rw [smul_comm, hx a ha, smul_zero]

end AlmostMath

/-- A `V`-module `M` is **almost zero** if `m ≤ annihilator(M)`, i.e., every element
of `m` annihilates every element of `M`. -/
class Module.IsAlmostZero (V : Type u) (M : Type v) [CommRing V] [AlmostSetup V]
    [AddCommGroup M] [Module V M] : Prop where
  /-- The ideal `m` annihilates the module. -/
  almost_zero : AlmostSetup.m (V := V) ≤ Module.annihilator V M

namespace AlmostMath

variable {V : Type u} [CommRing V] [AlmostSetup V]
variable {M N : Type v} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- A `V`-linear map is **almost injective** if its kernel is almost zero. -/
def LinearMap.IsAlmostInjective (f : M →ₗ[V] N) : Prop :=
  Module.IsAlmostZero V (LinearMap.ker f)

/-- A `V`-linear map is **almost surjective** if its cokernel is almost zero. -/
def LinearMap.IsAlmostSurjective (f : M →ₗ[V] N) : Prop :=
  Module.IsAlmostZero V (N ⧸ LinearMap.range f)

/-- A `V`-linear map is **almost bijective** if it is both almost injective and
almost surjective. -/
def LinearMap.IsAlmostBijective (f : M →ₗ[V] N) : Prop :=
  f.IsAlmostInjective ∧ f.IsAlmostSurjective

/-- A `V`-module is **almost finitely generated** if for every `a ∈ m`, the element
`a` acts through a finitely generated submodule. -/
def Module.IsAlmostFinitelyGenerated (V : Type u) (M : Type v)
    [CommRing V] [AlmostSetup V] [AddCommGroup M] [Module V M] : Prop :=
  ∀ a : V, a ∈ AlmostSetup.m (V := V) →
    ∃ (S : Finset M), ∀ x : M, a • x ∈ Submodule.span V (S : Set M)

end AlmostMath
```

- [ ] **Step 2: Verify compilation**

Run: `lake env lean "Adic spaces/AlmostMathematics.lean"`
Expected: Zero errors, zero warnings (all lemmas are proved, not sorry'd).

- [ ] **Step 3: Add to root imports**

Add `import «Adic spaces».AlmostMathematics` to `Adic spaces.lean`.

- [ ] **Step 4: Commit**

```bash
git add "Adic spaces/AlmostMathematics.lean" "Adic spaces.lean"
git commit -m "Add almost mathematics library (Gabber–Ramero framework)"
```

---

### Task 2: Pseudo-uniformizers

**Files:**
- Create: `Adic spaces/PseudoUniformizer.lean`

- [ ] **Step 1: Create PseudoUniformizer.lean**

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».HuberRings

/-!
# Pseudo-uniformizers

A **pseudo-uniformizer** of a topological ring `A` is a topologically nilpotent unit
(Definition 6.10 of Wedhorn). Every Tate ring has a pseudo-uniformizer.

## Main definitions

* `IsPseudoUniformizer w` : A unit `w : Aˣ` is topologically nilpotent.
* `PseudoUniformizer A` : The type of pseudo-uniformizers of `A`.
* `IsTateRing.pseudoUniformizer` : Extract a pseudo-uniformizer from a Tate ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 6.10
-/

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A unit `w : Aˣ` is a **pseudo-uniformizer** if it is topologically nilpotent
(Definition 6.10 of Wedhorn). -/
def IsPseudoUniformizer (w : Aˣ) : Prop :=
  IsTopologicallyNilpotent (w : A)

/-- The type of pseudo-uniformizers of a topological ring `A`. -/
def PseudoUniformizer (A : Type*) [CommRing A] [TopologicalSpace A] :=
  {w : Aˣ // IsPseudoUniformizer w}

instance : CoeOut (PseudoUniformizer A) Aˣ := ⟨Subtype.val⟩

/-- Every Tate ring has a pseudo-uniformizer. -/
noncomputable def IsTateRing.pseudoUniformizer [IsTateRing A] :
    PseudoUniformizer A :=
  ⟨IsTateRing.exists_topologicallyNilpotent_unit.choose,
   IsTateRing.exists_topologicallyNilpotent_unit.choose_spec⟩

/-- A pseudo-uniformizer is topologically nilpotent. -/
theorem PseudoUniformizer.isTopologicallyNilpotent (w : PseudoUniformizer A) :
    IsTopologicallyNilpotent (w.val : A) :=
  w.property
```

- [ ] **Step 2: Verify compilation**

Run: `lake env lean "Adic spaces/PseudoUniformizer.lean"`
Expected: Zero errors.

- [ ] **Step 3: Add to root imports and commit**

```bash
# Add import to Adic spaces.lean
git add "Adic spaces/PseudoUniformizer.lean" "Adic spaces.lean"
git commit -m "Add pseudo-uniformizer type (Wedhorn Definition 6.10)"
```

---

## Chunk 2: Perfectoid Rings (Sub-project 2b)

### Task 3: IsPerfectoidRing and IsPerfectoidField

**Files:**
- Create: `Adic spaces/PerfectoidRing.lean`
- Depends on: Task 2 (PseudoUniformizer.lean)

- [ ] **Step 1: Create PerfectoidRing.lean**

Write the file with `IsPerfectoidRing p A` class extending `IsTateRing`, and `IsPerfectoidField`.

Key design decisions:
- `p : ℕ` as explicit argument (Mathlib convention)
- `[Fact (Nat.Prime p)]` for the primality
- extends `IsTateRing A`
- Needs `[UniformSpace A]` for `CompleteSpace`
- The `ramified` condition: ∃ w pseudo-uniformizer with w^p | p in A° and Frob surjective on A°/w
- Import `Mathlib.FieldTheory.Perfect` for `frobenius`
- Import our `Uniform.lean` for `IsUniform`
- Import our `Bounded.lean` for `powerBoundedSubring`

The Frobenius surjectivity condition requires forming the quotient ring
`powerBoundedSubring.toSubring A ⧸ Ideal.span {⟨w, hw⟩}` and applying
`frobenius _ p`. This may need careful typeclass management. If Lean can't
synthesize `CharP` on the quotient, use a `sorry`'d instance or restate
the condition more directly as:
```
∀ x ∈ powerBoundedSubring A, ∃ y ∈ powerBoundedSubring A,
  (y ^ p - x) ∈ Ideal.span {(w : A)} -- Frobenius surjective mod w
```

- [ ] **Step 2: Verify compilation**

Run: `lake env lean "Adic spaces/PerfectoidRing.lean"`
Expected: Zero errors. Only sorry warnings on theorem stubs.

- [ ] **Step 3: Add sorry'd key theorems**

Add the sorry'd statements:
- `IsPerfectoidRing.toIsStablyUniform`
- `IsPerfectoidRing.toIsSheafy`

These import `Uniform.lean` and `StructureSheaf.lean`.

- [ ] **Step 4: Verify and commit**

```bash
git add "Adic spaces/PerfectoidRing.lean" "Adic spaces.lean"
git commit -m "Add IsPerfectoidRing and IsPerfectoidField (Scholze Definition 3.5)"
```

---

## Chunk 3: Tilting (Sub-project 3)

### Task 4: Tilting and A_inf

**Files:**
- Create: `Adic spaces/Tilting.lean`
- Depends on: Task 3 (PerfectoidRing.lean)

- [ ] **Step 1: Create Tilting.lean with tilt, A_inf, and theta**

```lean
import «Adic spaces».PerfectoidRing
import Mathlib.RingTheory.Perfection
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.Perfectoid.FontaineTheta
```

Define:
- `PerfectoidRing.tilt p A` as `PreTilt (powerBoundedSubring.toSubring A) p`
- `Ainf p A` as `WittVector p (PerfectoidRing.tilt p A)`
- `PerfectoidRing.theta` using `WittVector.fontaineTheta`
- Sorry'd: `tilt_isPerfectoidRing`, `theta_surjective`, `ker_theta_principal`,
  `tilt_isPerfect`, `tiltingEquiv`

Note: The `PreTilt` and `fontaineTheta` types take specific arguments. Read
Mathlib's `Mathlib.RingTheory.Perfection` and `Mathlib.RingTheory.Perfectoid.FontaineTheta`
to get the exact signatures. Use `lean_hover_info` to check types if needed.

- [ ] **Step 2: Verify compilation**

Run: `lake env lean "Adic spaces/Tilting.lean"`
Expected: Zero errors.

- [ ] **Step 3: Commit**

```bash
git add "Adic spaces/Tilting.lean" "Adic spaces.lean"
git commit -m "Add tilting functor, A_inf, and Fontaine theta (Scholze §3)"
```

---

## Chunk 4: Perfectoid Spaces (Sub-project 4)

### Task 5: Perfectoid Spaces

**Files:**
- Create: `Adic spaces/PerfectoidSpace.lean`
- Depends on: Task 3 (PerfectoidRing.lean)

- [ ] **Step 1: Create PerfectoidSpace.lean**

Define `AffinoidPerfectoidSpace p` as a structure bundling a perfectoid ring,
and `IsPerfectoidSpace p X` as a class on `AdicSpace` requiring locally perfectoid
covers.

Import `StructureSheaf.lean` for `AdicSpace`, `AffinoidAdicSpace`.

The key challenge: `AdicSpace` is defined at `StructureSheaf.lean:209` as a structure
with `carrier`, `instTopologicalSpace`, `isLocallyAffinoid`. The `IsPerfectoidSpace`
class should state that the affinoid covers can be chosen to be perfectoid.

- [ ] **Step 2: Add sorry'd theorems**

- `AffinoidPerfectoidSpace.isSheafy`
- `AffinoidPerfectoidSpace.isStablyUniform`
- `AffinoidPerfectoidSpace.toAdicSpace`
- `PerfectoidSpace.tilt` (tilt of a perfectoid space is perfectoid in char p)

- [ ] **Step 3: Verify and commit**

```bash
git add "Adic spaces/PerfectoidSpace.lean" "Adic spaces.lean"
git commit -m "Add perfectoid spaces (Scholze Definition 3.19)"
```

---

## Chunk 5: Fargues–Fontaine Curve (Sub-project 5)

### Task 6: The adic Fargues–Fontaine curve

**Files:**
- Create: `Adic spaces/FarguesFontaine.lean`
- Depends on: Tasks 3, 4, 5

- [ ] **Step 1: Create FarguesFontaine.lean**

Define:
- `WittVector` Huber pair instances (sorry'd)
- `Y_FF p E π` — the pre-curve as a subset of `Spa(W(O_E))`
- `Y_FF.frobeniusAction` — Frobenius acts on Y_FF via `Spv.comap` (sorry'd)
- `frobeniusOrbitRel` — the equivalence relation from the Frobenius orbit
- `X_FF p E π` — the quotient `Y_FF / φ^ℤ`
- Sorry'd key theorems: noetherian, regular, dim 1, classical points

The `O_E` (ring of integers of E) can be expressed as
`powerBoundedSubring.toSubring E` since for a perfectoid field, `E° = O_E`.

- [ ] **Step 2: Verify compilation**

Run: `lake env lean "Adic spaces/FarguesFontaine.lean"`
Expected: Zero errors.

- [ ] **Step 3: Commit**

```bash
git add "Adic spaces/FarguesFontaine.lean" "Adic spaces.lean"
git commit -m "Add adic Fargues–Fontaine curve X_FF = Y_FF / φ^ℤ"
```

---

## Chunk 6: Scottish Book Problems (remaining 15)

### Task 7: State remaining Scottish Book problems

**Files:**
- Modify: 15 files in `Adic spaces/ScottishBook/` (Problems 2,3,4,5,6,13,14,20,21,22,25,26,32,33,34)
- Depends on: Tasks 3, 5

- [ ] **Step 1: Problems needing only IsPerfectoidRing (7 problems)**

Update Problems 2, 3, 6, 13, 20, 33, 34 to import `PerfectoidRing.lean` and
state their theorems using `IsPerfectoidRing`.

For each: read the existing docstring, write the theorem statement with proper
hypotheses, verify compilation.

Key patterns:
- Problem 2: `IsPerfectoidSpace → IsPerfectoidRing` for Tate pairs
- Problem 3: `IsPerfectoidRing + MulAction G → IsPerfectoidRing (FixedPoints)`
- Problem 6: `∃ A stably uniform, ¬ IsSousperfectoid A` (needs `IsSousperfectoid` def)
- Problem 13: `IsPerfectoidRing over ℚ_p → ∃ perfectoid subfield` (negated)
- Problem 20: seminormalization of finite perfectoid algebra
- Problem 33: `WittVector p R` with specific topology, sheafy?
- Problem 34: fibers perfectoid + uniform → perfectoid?

- [ ] **Step 2: Problems needing tilting (4 problems)**

Update Problems 5, 14, 22, 38 to import `Tilting.lean`.

- Problem 5: `W(R⁺) ⊗̂ A°)[1/p]` stably uniform?
- Problem 14: arithmetically profinite → perfectoid field?
- Problem 22: finite morphism ↔ finite tilt morphism?
- Problem 38: perfectoid subfield of tilt = tilt of perfectoid subfield? (negated)

- [ ] **Step 3: Problems needing IsPerfectoidSpace (4 problems)**

Update Problems 4, 21, 25, 26, 32 to import `PerfectoidSpace.lean`.

- Problem 4: Zariski-dense perfectoid subset → perfectoid?
- Problem 21: perfectoid residue fields → perfectoid?
- Problem 25: inverse limit along finite flat → perfectoid?
- Problem 26: Serre criterion for perfectoid?
- Problem 32: completed tensor product sheafy?

- [ ] **Step 4: Verify all 15 compile**

```bash
for n in 002 003 004 005 006 013 014 020 021 022 025 026 032 033 034; do
  lake env lean "Adic spaces/ScottishBook/Problem0${n}.lean" 2>&1 | grep error
done
```
Expected: No error output.

- [ ] **Step 5: Commit**

```bash
git add "Adic spaces/ScottishBook/"
git commit -m "State remaining 15 Scottish Book problems using perfectoid theory"
```

---

## Chunk 7: Final integration

### Task 8: Root imports, memory, and cleanup

- [ ] **Step 1: Update root import file**

Ensure `Adic spaces.lean` imports all new files:
```
import «Adic spaces».AlmostMathematics
import «Adic spaces».PseudoUniformizer
import «Adic spaces».PerfectoidRing
import «Adic spaces».Tilting
import «Adic spaces».PerfectoidSpace
import «Adic spaces».FarguesFontaine
```

- [ ] **Step 2: Update TICKETS.md**

Add Phase 6 tickets for perfectoid theory and mark completed ones.

- [ ] **Step 3: Update docs/STATUS.md**

Add entries for new files with their status.

- [ ] **Step 4: Full build check**

```bash
lake build
```
Expected: Builds successfully (may take a while with Mathlib).

- [ ] **Step 5: Final commit and push**

```bash
git add -A
git commit -m "Add perfectoid theory: almost math, perfectoid rings, tilting, FF curve

Sub-project 1: AlmostMathematics.lean (Gabber-Ramero framework)
Sub-project 2: PseudoUniformizer.lean + PerfectoidRing.lean (Scholze Def 3.5)
Sub-project 3: Tilting.lean (tilt functor, A_inf, Fontaine theta)
Sub-project 4: PerfectoidSpace.lean (Scholze Def 3.19)
Sub-project 5: FarguesFontaine.lean (adic FF curve X_FF = Y_FF/φ^Z)
+ 15 Scottish Book problems now formalized (35 of 40 total)

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>"
```
