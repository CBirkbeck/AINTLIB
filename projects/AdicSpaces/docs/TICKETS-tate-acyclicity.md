# Tate Acyclicity — Parallelizable Tickets

**Master goal:** Prove Wedhorn Theorem 8.28(b): strongly noetherian Tate rings are sheafy
(as a sheaf of complete topological rings).
**Reference:** Wedhorn, *Adic Spaces*, §6.18, §8.1–8.2, Appendix A (pp.73-85, 104-106).
**Constraint:** No `sorry` or `axiom`.
**Full plan:** `docs/plans/2026-03-21-tate-acyclicity.md`

---

## Agent Coordination Protocol

**EVERY agent MUST follow these rules:**

1. **Before starting a ticket:** Update the tracker table below — set Status
   to `IN PROGRESS`, fill in your Agent ID and start date. **Commit this change**
   before writing any code. This prevents two agents picking up the same ticket.

2. **Check for conflicts:** Before picking a ticket, read this file and check
   the tracker. If a ticket is `IN PROGRESS`, do NOT work on it. Pick a
   different ticket from the same wave, or wait.

3. **Check dependencies:** Only pick up tickets whose dependencies are `DONE`.
   See the dependency graph below.

4. **When finished:** Update the tracker — set Status to `DONE`, fill in the
   completion date and the commit hash. **Commit this change** immediately.

5. **If blocked:** Set Status to `BLOCKED`, add a note explaining why, and commit.

6. **Do not modify files owned by another in-progress ticket.** Each ticket
   lists its file(s). If another ticket is IN PROGRESS on that file, wait.

7. **Commit frequently** with messages referencing the ticket number
   (e.g., `TICKET-1A: define CechCochain and cechDiff`).

## Tracker

| Ticket | Status | Agent | Started | Completed | Commit | Notes |
|--------|--------|-------|---------|-----------|--------|-------|
| 0 | DONE | claude-main | 2026-03-21 | 2026-03-21 | — | Report: docs/plans/mathlib-audit-tate.md |
| 1A | DONE | claude-main | 2026-03-21 | 2026-03-21 | — | CechCohomology.lean |
| 1B | DONE | claude-main | 2026-03-21 | 2026-03-22 | — | A.3 infra + basis-sheaf types |
| 2A | DONE | claude-opus | 2026-03-21 | 2026-03-21 | 7843694 | Algebraic defs + embeddings; topology TBD |
| 2B | DONE | claude-opus | 2026-03-21 | 2026-03-22 | be52a6c | 0 sorry (discrete case) |
| 3 | DONE | claude-opus | 2026-03-22 | 2026-03-23 | a68b496 | 0 sorry; discrete case |
| 4 | DONE | claude-opus | 2026-03-23 | 2026-03-23 | 6312c2c | 0 sorry; discrete case |
| 5 | DONE | claude-opus | 2026-03-23 | 2026-03-23 | 0d42a8a | 0 sorry; discrete case |
| 6 | DONE | claude-opus | 2026-03-21 | 2026-03-21 | 0c4be61 | Depends: 0 |

## Dependency Graph

```
TICKET-0   mathlib/project audit
    |
    +---> TICKET-1A  finite-cover Cech API
    |         |
    |         +---> TICKET-1B  refinement lemmas + minimal basis-sheaf criterion
    |
    +---> TICKET-2A  Tate/Laurent algebra models + universal properties
    |
    +---> TICKET-6   noetherian Tate module topology API (Prop 6.18)
                |
                +---> TICKET-2B  Remark 8.29 + Lemma 8.31
                          |
                          +---> TICKET-3  Prop 8.30 + Cor 8.32

TICKET-2A + TICKET-2B + TICKET-3 ---> TICKET-4  Lemma 8.33

TICKET-1B + TICKET-3 + TICKET-4 ---> TICKET-5  Lemma 8.34 + Theorem 8.28(b)
```

**Can run in parallel:** {1A, 2A, 6} then {1B, 2B} then {3} then {4} then {5}

---

## Worker Instructions

1. **Do NOT implement Cartan/Godement** unless on an optional follow-up ticket.
2. **Do NOT implement completion-preserves-exactness for TICKET-4.** Wedhorn 8.33
   works directly in completed Tate algebras — there is no separate uncompleted
   row whose completion gives the target.
3. **Track topological strictness early.** The final theorem is a sheaf of
   **complete topological rings**, not just a sheaf of rings. Expose `IsStrict`
   for continuous linear maps and strict-exact sequences.
4. **Model the Laurent algebra cleanly.** It is the central reusable object.
   Use two models (quotient + bilateral series) with a comparison isomorphism.
5. **Fix the class design before downstream tickets.** Use Wedhorn Def 6.36 for
   `IsStronglyNoetherianTate`, NOT just "noetherian ring of definition".

---

## TICKET-0: Prerequisite Mathlib/Project Audit

**Status:** NOT STARTED
**Estimated:** 1 session
**Blocks:** All other tickets
**File:** `docs/plans/mathlib-audit-tate.md` (report)

### Task

Audit mathlib v4.29.0-rc3 and the existing project for APIs needed by the
proof. For each item, report: exists? (name + file), or how hard to build.

### Audit checklist

- [ ] Existing project API for rational subsets / presheaf values / completed
  rational localizations / restricted power series / Laurent series
- [ ] `RingHom.Flat` / `RingHom.FaithfullyFlat` and useful lemmas (contraction
  of primes, faithful flatness criteria, finite products)
- [ ] Snake lemma / 3x3 lemma support for module diagrams
- [ ] Adic/module-topology APIs in mathlib
- [ ] Artin-Rees and cofinality lemmas for filtrations
- [ ] Whether the project has Wedhorn Remark 7.55 (decomposing rational subsets
  into basic R(f/1) and R(1/f) steps)
- [ ] `IsNoetherianRing` preservation for polynomial/power series rings
- [ ] `TensorProduct` right exactness API
- [ ] `UniformSpace.Completion.map` properties

### Deliverable

Report ending with a **critical path** section: which lemmas are needed for
Wedhorn 8.33 vs which are future/generalization only.

---

## TICKET-1A: Finite-Cover Cech Complex — Definitions

**Status:** NOT STARTED
**Estimated:** ~150 lines
**Blocks:** TICKET-1B
**Depends on:** TICKET-0
**File:** `Adic spaces/CechCohomology.lean`

### Task

Build a finite-cover Cech complex API from scratch (none exists in mathlib).

### Design decisions

- Index by `Fin (q+1) -> ι` (all functions), NOT order-homs `→o`. This is
  better for refinement maps, product covers, and restriction of covers.
- Do NOT expose alternating cochains in the public API. If needed later, add
  as internal comparison. The current theorem only needs the full complex.

### Definitions to create

```
-- Finite cover indexed by type ι
structure FiniteCover (X : Type*) [TopologicalSpace X] (ι : Type*) [Fintype ι]

-- Multi-intersection
def FiniteCover.inter (U : FiniteCover X ι) (σ : Fin (q+1) → ι) : Set X

-- q-cochains
def Cech (F : Set X → Type*) (U : FiniteCover X ι) (q : ℕ) : Type*
  -- := ∏ σ : Fin (q+1) → ι, F (U.inter σ)

-- Differential
def cechDiff ... : Cech F U q → Cech F U (q+1)

-- Augmentation
def cechAug ... : F Set.univ → Cech F U 0

-- Cover restriction and product-cover constructions
def FiniteCover.restrictTo ...
def FiniteCover.prod ...
```

### Properties to prove

- [ ] `cechDiff_comp_cechDiff : cechDiff (q+1) ∘ cechDiff q = 0`
- [ ] `cechAug_comp_cechDiff : cechDiff 0 ∘ cechAug = 0`
- [ ] Extensionality lemmas for cochains
- [ ] Chain maps induced by cover maps / refinements

### Acceptance criteria

- File compiles, zero warnings, no sorry
- Docstring on every public definition

---

## TICKET-1B: Cech Refinement Theorems + Basis-Sheaf Criterion

**Status:** NOT STARTED
**Estimated:** ~250 lines
**Blocks:** TICKET-5
**Depends on:** TICKET-1A
**File:** `Adic spaces/CechCohomology.lean` (append)

### Task

Formalize exactly the Cech infrastructure used in Lemma 8.34 (Wedhorn App A).

### What to prove (and what NOT to prove)

**DO prove:**

- **Prop A.3(1)** (master lemma): If restrictions of V to intersections of U are
  acyclic, and vice versa, then U acyclic iff V acyclic.
- **Prop A.3(2)**: Refinement preserves acyclicity. (Follows from A.3(1)
  because trivial cover is always acyclic.)
- **Prop A.3(3)**: If V|_{U_{i₀...i_q}} is acyclic for all intersections, then
  U × V acyclic iff U acyclic. This is the exact form used in Lemma 8.34(i).
- **Minimal basis-sheaf criterion**: If B is a basis stable under finite
  intersections, and every finite B-cover of every U ∈ B is acyclic, then the
  presheaf is a sheaf on B, hence extends to a sheaf on all opens.

**Do NOT prove:**

- Full Cech-to-derived-functor comparison (Cartan/Godement). Optional later.
- Higher cohomology H^q = Ȟ^q on all opens. Not needed for Thm 8.28(b).

If you do formalize the full A.4, keep it in a separate namespace so the
main theorem does not depend on it.

### Acceptance criteria

- A.3(1)/(2)/(3) and basis-sheaf criterion proved, no sorry
- Connected to `RationalCovering` from Presheaf.lean

---

## TICKET-2A: Tate and Laurent Algebra Models

**Status:** NOT STARTED
**Estimated:** ~200 lines
**Blocks:** TICKET-2B, TICKET-4
**Depends on:** TICKET-0
**File:** `Adic spaces/TateAlgebra.lean`

### Task

Provide clean models for the completed algebras in Wedhorn 8.29-8.33.

### Objects to define

1. `TateAlgebra A` := A⟨X⟩ (univariate restricted power series)
2. `LaurentTateAlgebra A` := A⟨ζ, ζ⁻¹⟩ (bilateral restricted Laurent series)

### Design: two models for Laurent algebra

- **Quotient model:** `TateAlgebra2 A / (XY - 1)` for universal properties and
  comparison with presheaf values.
- **Bilateral series model:** Direct definition via coefficients for explicit
  computations (decomposition into positive/negative parts).
- Prove a comparison isomorphism between them.

### Required API

- [ ] Constants/variables and evaluation maps
- [ ] Quotient: `A⟨X⟩/(X) ≃ A`
- [ ] Quotient: `A⟨X,Y⟩/(XY-1) ≃ LaurentTateAlgebra A`
- [ ] Extensionality by coefficients on each model
- [ ] Embeddings: `A⟨ζ⟩ → LaurentTateAlgebra A`, `A⟨ζ⁻¹⟩ → LaurentTateAlgebra A`
- [ ] Topology making A⟨X⟩ a Tate ring (inherited from a topologically
  nilpotent unit of A, **NOT from X** — X is not a unit)

### Acceptance criteria

- All objects defined with proper topology
- Comparison isomorphism proved
- No sorry, zero warnings

---

## TICKET-6: Noetherian Tate Module Topology (Prop 6.18)

**Status:** NOT STARTED
**Estimated:** ~200 lines
**Blocks:** TICKET-2B
**Depends on:** TICKET-0
**File:** `Adic spaces/NoetherianTateModules.lean`

### Task

Formalize the API around Wedhorn Prop 6.18 and Remark 6.19. This is the
module topology / open mapping infrastructure needed by Remark 8.29.

### What to prove

1. **Canonical topology** on f.g. modules over a complete noetherian Tate ring
   (Prop 6.18(1)): the unique topology making M a topological A-module with
   I^n M → 0.
2. **Independence** of the chosen ring of definition / lattice.
3. **Continuity**: every A-linear map between f.g. modules is continuous
   (Prop 6.18(2), easy direction).
4. **Open mapping**: every surjective A-linear map between f.g. modules is open
   (Prop 6.18(2), hard direction — needs Artin-Rees).
5. **Strict map API**: reusable `IsStrict` predicate for continuous maps that
   are open onto their image.

### Artin-Rees

If not in mathlib (check TICKET-0), prove it here:
`∃ c, ∀ n ≥ c, I^n M ∩ N = I^{n-c}(I^c M ∩ N)` for f.g. N ⊆ M over
noetherian rings. (~50 lines)

### What does NOT belong here

- Completion-preserves-exactness (future Zavyalov phase)
- Projective scheme arguments

### Acceptance criteria

- Prop 6.18 (both parts) proved, no sorry
- `IsStrict` predicate defined and usable
- Zero warnings

---

## TICKET-2B: Remark 8.29 + Lemma 8.31

**Status:** NOT STARTED
**Estimated:** ~250 lines
**Blocks:** TICKET-3
**Depends on:** TICKET-2A, TICKET-6
**File:** `Adic spaces/TateAlgebra.lean` (append)

### Task

Follow Wedhorn 8.29 / 8.31 exactly. This is the algebraic engine.

### Sub-parts

**2B.1 — M⟨X⟩ as a functor:**
Define M⟨X⟩ for f.g. A-modules. Prove that a strict short exact sequence of
f.g. modules remains exact after applying ⟨X⟩. (Uses Prop 6.18 from TICKET-6.)

**2B.2 — Remark 8.29 (μ_M isomorphism):**
For f.g. M, prove `μ_M : M ⊗[A] A⟨X⟩ →≃ M⟨X⟩`.
Proof: presentation A^n → A^m → M → 0, free case, exactness of ⟨X⟩ on strict maps.

**2B.3 — Lemma 8.31(1) (faithful flatness):**
- Flat: tensor with A⟨X⟩ preserves injections of f.g. modules (via μ_M).
- Faithful: via prime-lifting on the constant term, or quotient criterion
  using `A⟨X⟩/(X) ≅ A`.

**2B.4 — Lemma 8.31(2) (quotient flatness):**
Reusable lemma: if multiplication by g is injective on M⟨X⟩ for every f.g. M,
then A⟨X⟩/(g) is flat over A.

Specialize to `g = f - X` and `g = 1 - fX`. For `g = f - X`, formalize the
noetherian argument: the recurrence `fm₀ = 0, fmₙ = mₙ₋₁` implies the
submodule generated by {m₀, m₁, ...} is finitely generated, leading to u = 0.

### Acceptance criteria

- Remark 8.29 and Lemma 8.31(1)+(2) fully proved, no sorry
- Reusable quotient-flatness-from-injectivity lemma

---

## TICKET-3: Flatness of Restriction Maps (Prop 8.30 + Cor 8.32)

**Status:** NOT STARTED
**Estimated:** ~200 lines
**Blocks:** TICKET-4, TICKET-5
**Depends on:** TICKET-2B
**File:** `Adic spaces/FlatnessResults.lean`

### Task

Connect Tate algebra flatness to the presheaf structure.

### Prerequisites from existing project

- Rational localizations of strongly noetherian Tate rings remain strongly
  noetherian Tate (Example 6.38 — prove if not already in project)
- Wedhorn Remark 7.55: every rational subset decomposes into basic R(f/1)
  and R(1/f) steps (check if already in project from TICKET-0)

### Prop 8.30 (restriction maps flat)

- Reduce to V = X and A complete
- Use Remark 7.55 to reduce to two basic cases
- Identify O_X(R(f/1)) = A⟨X⟩/(f-X) and O_X(R(1/f)) = A⟨X⟩/(1-fX)
- Apply TICKET-2B flatness

### Cor 8.32 (product restriction faithfully flat)

Prove `A → ∏ O_X(U_i)` is faithfully flat for a finite rational cover:
- Flatness: finite products of flat algebras are flat
- Faithfulness: induced map on spectra is surjective because U_i cover Spa A

**Do NOT describe this as factoring through A⟨X⟩** — that is not the right proof.

### Reusable API to leave behind

A general lemma: for a finite family of flat A-algebras whose affinoid spectra
cover Spa A, the map to the finite product is faithfully flat.

### Acceptance criteria

- Prop 8.30 and Cor 8.32 proved, no sorry
- Connected to existing `presheafValue` and `restrictionMap`

---

## TICKET-4: Laurent Cover Exactness (Lemma 8.33)

**Status:** NOT STARTED
**Assignee:** (experienced agent — hardest ticket)
**Estimated:** ~350 lines
**Blocks:** TICKET-5
**Depends on:** TICKET-2A, TICKET-2B, TICKET-3
**File:** `Adic spaces/LaurentCoverExact.lean`

### Task

Formalize exactly Wedhorn Lemma 8.33 on pp.83-84. The proof works **directly
in completed Tate algebras** — there is NO separate uncompleted row whose
completion gives the target row.

### Setup

For f ∈ A, the 2-element cover U₁ = R(f/1), U₂ = R(1/f). Identify:
- B₁ := O_X(U₁) = A⟨ζ⟩/(f-ζ)
- B₂ := O_X(U₂) = A⟨η⟩/(1-fη)
- B₁₂ := O_X(U₁∩U₂) = A⟨ζ,ζ⁻¹⟩/(f-ζ)

### The 3×3 diagram (Wedhorn p.83)

```
                    0                     0
                    ↓                     ↓
(f-ζ)A⟨ζ⟩ × (1-fη)A⟨η⟩  →λ'→  (f-ζ)A⟨ζ,ζ⁻¹⟩  → 0    [Row 1]
                    ↓                     ↓
0 → A  →ι→  A⟨ζ⟩ × A⟨η⟩      →λ→   A⟨ζ,ζ⁻¹⟩          [Row 2]
                    ↓                     ↓
0 → A  →ε→  B₁ × B₂           →δ→   B₁₂         → 0   [Row 3]
                    ↓                     ↓
                    0                     0
```

### Sub-parts

**4.1 — Decomposition lemmas:**
- `A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩` (gives surjectivity of λ)
- `(f-ζ)A⟨ζ,ζ⁻¹⟩ = (f-ζ)A⟨ζ⟩ + (1-fζ⁻¹)A⟨ζ⁻¹⟩` (gives surjectivity of λ')

**4.2 — Kernel lemma:**
For `λ(g(ζ), h(η)) = g(ζ) - h(ζ⁻¹)`, prove `ker λ = im ι` by explicit
coefficient comparison. This is the key computational lemma.

**4.3 — Diagram chase:**
Columns exact (by definition as quotients). Row 1 exact (λ' surjective).
Row 2 exact (λ surjective, ker = im ι). By 3×3 lemma / snake lemma,
row 3 is exact.

**4.4 — Topological upgrade:**
Strengthen to strict-exactness: the map ε is a topological embedding into
B₁ × B₂ (for `IsSheafyTopRing`).

### What does NOT belong here

- "Decompleted exactness" — not part of Wedhorn 8.33
- "Completion preserves exactness" — not part of Wedhorn 8.33
- TICKET-6 is NOT a dependency of this ticket

### Acceptance criteria

- Lemma 8.33 fully proved (including topological embedding), no sorry
- Uses Laurent algebra API from TICKET-2A
- Connected to `IsAcyclic` from TICKET-1A

---

## TICKET-5: General Acyclicity + Assembly (Lemma 8.34 + Thm 8.28(b))

**Status:** NOT STARTED
**Estimated:** ~250 lines
**Blocks:** None (final ticket)
**Depends on:** TICKET-1B, TICKET-3, TICKET-4
**Files:** `Adic spaces/TateAcyclicity.lean` (new),
  `Adic spaces/StructureSheaf.lean` (modify), `Adic spaces.lean` (modify)

### Class design

Use Wedhorn Definition 6.36:

```
class IsStronglyNoetherianTate (A : Type*) [CommRing A] [TopologicalSpace A]
    extends IsTateRing A where
  noetherian_tate_algebra : ∀ n : ℕ, IsNoetherianRing (completion_of (A⟨X₁,...,Xₙ⟩))
```

Equivalently: every Tate ring topologically of finite type over A is noetherian.

### Lemma 8.34 (standard covers acyclic)

Follow Wedhorn pp.84-85 literally:
1. 2-element covers U_f = {R(f/1), R(1/f)} are acyclic (TICKET-4)
2. Restriction to any rational subset remains acyclic (rational localizations
   stay strongly noetherian Tate)
3. By A.3(3) (TICKET-1B), products of 2-element covers (Laurent covers)
   are acyclic
4. For standard cover by T = (f₀,...,fₙ), use Cor 7.32 to choose unit s so
   that Laurent cover by s⁻¹f₁,...,s⁻¹fₙ has U|_{V_j} generated by units
5. Rational covers by units are refined by Laurent covers by f_if_j⁻¹
6. By A.3(2)/(3), standard cover is acyclic

### Theorem 8.28(b) — two outputs

**5.1 Ring-sheaf:** Use basis-sheaf criterion (TICKET-1B) on rational subsets.

**5.2 Topological sheaf:** Either inherit from strict-exactness (TICKET-4
topological upgrade), or separately prove the equalizer map is a topological
embedding. Target: `IsSheafyTopRing A`.

### Steps

- [ ] Define `IsStronglyNoetherianTate` (Wedhorn 6.36)
- [ ] Prove rational localizations preserve strongly noetherian
- [ ] Define Laurent covers, prove acyclic (wrap TICKET-4)
- [ ] Prove Laurent cover refinement (8.34(ii)-(iii))
- [ ] Prove Lemma 8.34 by induction
- [ ] Prove `IsStronglyNoetherianTate.isSheafyTopRing`
- [ ] Add `IsSheafy` instance to StructureSheaf.lean
- [ ] Update imports in `Adic spaces.lean`
- [ ] Full `lake build` verification

### Acceptance criteria

- Theorem 8.28(b) proved as `IsSheafyTopRing`, no sorry
- Full project builds with zero errors

---

## Summary Table

| Ticket | File | Lines | Depends on | Parallel with | Difficulty |
|--------|------|-------|------------|---------------|------------|
| **0** | (report) | — | — | — | Easy |
| **1A** | CechCohomology.lean | ~150 | 0 | 2A, 6 | Medium |
| **1B** | CechCohomology.lean | ~250 | 1A | 2B | Medium |
| **2A** | TateAlgebra.lean | ~200 | 0 | 1A, 6 | Medium |
| **2B** | TateAlgebra.lean | ~250 | 2A, 6 | 1B | Hard |
| **3** | FlatnessResults.lean | ~200 | 2B | — | Hard |
| **4** | LaurentCoverExact.lean | ~350 | 2A, 2B, 3 | — | **Very Hard** |
| **5** | TateAcyclicity.lean | ~250 | 1B, 3, 4 | — | Medium |
| **6** | NoetherianTateModules.lean | ~200 | 0 | 1A, 2A | Hard |

**Parallel execution:**
- **Wave 1** (3 agents): {TICKET-1A, TICKET-2A, TICKET-6}
- **Wave 2** (2 agents): {TICKET-1B, TICKET-2B}
- **Wave 3** (1 agent): TICKET-3
- **Wave 4** (1 agent): TICKET-4
- **Wave 5** (1 agent): TICKET-5

---

## Phase II: Zavyalov's Generalization (FUTURE — separate from Wedhorn 8.28)

Do NOT mix these into the current tickets. Start after Thm 8.28(b) lands.

| Ticket | What |
|--------|------|
| Z-1 | Rational localization API for general Huber pairs (Zavyalov 2.1/2.5) |
| Z-2 | Strong rigid-noetherianity (Def 2.8, Lemma 2.11/2.13, Thm 2.16) |
| Z-3 | Projective/decompleted Cech proof (Zavyalov Thm 3.5 Steps 2-4) |
| Z-4 | FP-approximated sheaves appendix (Lemma A.3, Thm A.5, A.13) |
