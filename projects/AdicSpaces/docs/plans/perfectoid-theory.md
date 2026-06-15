# Perfectoid Theory and Fargues–Fontaine Curve — Design Spec

**Date:** 2026-03-17
**Goal:** Build a complete perfectoid theory library in Lean 4, from almost mathematics
through the adic Fargues–Fontaine curve, with sorry'd deep theorems to be filled
incrementally. This unlocks the 17 remaining Scottish Book problems (rating 8–10)
and establishes infrastructure for p-adic Hodge theory.

**References:**
- Scholze, *Perfectoid Spaces* (2012)
- Wedhorn, *Adic Spaces* (2019), §5–§8
- Gabber–Ramero, *Almost Ring Theory* (LNM 1800)
- Fargues–Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique* (2018)
- Lean 3 project: `leanprover-community/lean-perfectoid-spaces`

---

## Architecture Overview

Five sub-projects in dependency order:

```
Sub-project 1: Almost Mathematics  (independent, mathlib candidate)
                    ↓
Sub-project 2: Perfectoid Rings ← uses Uniform.lean, Bounded.lean, HuberRings.lean
              ↙            ↘
Sub-project 3: Tilting    Sub-project 4: Perfectoid Spaces ← uses Spa/VObj/AdicSpace
              ↘            ↙
        Sub-project 5: Fargues–Fontaine Curve
```

**Period rings (B_dR, B_crys, A_crys) are deferred.** The adic FF curve only needs
`A_inf = W(O_E)` (Witt vectors, already in Mathlib) and the Frobenius action on
`Spa(W(O_E))`. Period rings are not needed for any Scottish Book problem statement
and can be built independently when p-adic Hodge theory work begins.

---

## Sub-project 1: Almost Mathematics

**File:** `Adic spaces/AlmostMathematics.lean`

**Mathlib status:** Nothing exists. All new. Strong mathlib PR candidate.

### Definitions

**1.1 AlmostSetup** — The basic pair `(V, m)`:
```
class AlmostSetup (V : Type*) [CommRing V] where
  m : Ideal V
  idempotent : m * m = m
```
In perfectoid context: `V = O_K`, `m = maximal ideal`. Idempotency `m² = m` follows
from the perfectoid property (every `a ∈ m` has a p-th root in m, up to higher terms).

**1.2 IsAlmostZero** — Element and module level:
```
def IsAlmostZero [AlmostSetup V] [Module V M] (x : M) : Prop :=
  ∀ a ∈ AlmostSetup.m, a • x = 0

class Module.IsAlmostZero (V M) [CommRing V] [AlmostSetup V]
    [AddCommGroup M] [Module V M] : Prop where
  almost_zero : AlmostSetup.m ≤ Module.annihilator V M
```

**1.3 Almost morphism properties:**
```
def LinearMap.IsAlmostInjective (f : M →ₗ[V] N) : Prop :=
  Module.IsAlmostZero V (LinearMap.ker f)

def LinearMap.IsAlmostSurjective (f : M →ₗ[V] N) : Prop :=
  Module.IsAlmostZero V (N ⧸ LinearMap.range f)

def LinearMap.IsAlmostBijective (f : M →ₗ[V] N) : Prop :=
  f.IsAlmostInjective ∧ f.IsAlmostSurjective
```

**1.4 Almost algebra properties:**
```
def Module.IsAlmostFinitelyGenerated (V M) : Prop :=
  ∀ a ∈ AlmostSetup.m, ∃ (n : ℕ) (f : (Fin n → V) →ₗ[V] M),
    ∀ x : M, a • x ∈ LinearMap.range f

def Algebra.IsAlmostEtale (V A B) : Prop :=
  Module.IsAlmostZero V (Ω[B⁄A]) ∧  -- almost unramified
  Module.IsAlmostFlat V B ∧           -- almost flat
  Module.IsAlmostFinitelyPresented V B -- almost f.p.
```

**Key Mathlib imports:** `Module.annihilator`, `LinearMap.ker`/`range`,
`TensorProduct`, `KaehlerDifferential`, `Module.Flat`.

### Basic lemmas to prove (not sorry)
- `IsAlmostZero.zero` — zero element is almost zero
- `IsAlmostZero.add` — almost zero is closed under addition
- `IsAlmostZero.smul` — almost zero is closed under scalar multiplication
- `Module.IsAlmostZero.subsingleton_of_m_eq_top` — if `m = ⊤`, almost zero = zero

---

## Sub-project 2: Perfectoid Rings

**Files:** `Adic spaces/PerfectoidRing.lean`, `Adic spaces/PseudoUniformizer.lean`

**Mathlib status:** `PerfectRing`, `frobenius`, `frobeniusEquiv` all exist.
`IsPerfectoidRing` does NOT exist.

### Definitions

**2.1 PseudoUniformizer** (new file `PseudoUniformizer.lean`):
```
def IsPseudoUniformizer (w : Aˣ) : Prop :=
  IsTopologicallyNilpotent (w : A)

def PseudoUniformizer (A) := {w : Aˣ // IsTopologicallyNilpotent (w : A)}
```
Note: `IsTateRing A` already asserts `∃ u : Aˣ, IsTopologicallyNilpotent (u : A)`.

**2.2 IsPerfectoidRing** (new file `PerfectoidRing.lean`):
```
class IsPerfectoidRing (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    extends IsTateRing A : Prop where
  complete : CompleteSpace A            -- needs [UniformSpace A]
  t0 : T0Space A
  uniform : TopologicalRing.IsUniform A
  ramified : ∃ (w : PseudoUniformizer A),
    IsPowerBounded (w.val : A) ∧
    (∃ c, IsPowerBounded c ∧ (p : A) = c * ((w.val : A) ^ p))
  frobenius_surj : ∃ (w : PseudoUniformizer A),
    Function.Surjective (frobenius (powerBoundedSubring.toSubring A ⧸
      Ideal.span {⟨(w.val : A), ‹_›⟩}) p)
```

Design decision: Parametrize by `p : ℕ` (residue characteristic) as an
explicit argument, following Mathlib's convention for `PerfectRing R p`.

**2.3 IsPerfectoidField:**
```
class IsPerfectoidField (p : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    extends IsPerfectoidRing p K : Prop
```

### Key sorry'd theorems
- `IsPerfectoidRing.powerBounded_isIntegrallyClosed` — A° integrally closed
- `IsPerfectoidRing.toIsStablyUniform` — perfectoid ⇒ stably uniform
- `IsPerfectoidRing.toIsSheafy` — perfectoid ⇒ sheafy
- `discreteTopology_not_perfectoid` — discrete rings are not perfectoid

---

## Sub-project 3: Tilting

**File:** `Adic spaces/Tilting.lean`

**Mathlib status:** `PreTilt O p`, `Tilt K v O hv p` exist as types.
`PreTilt.untilt`, `WittVector.fontaineTheta`, `surjective_fontaineTheta` exist.
No tilting equivalence. No valuation on Tilt.

### Definitions

**3.1 The tilt of a perfectoid ring:**
```
abbrev PerfectoidRing.tilt (p : ℕ) [Fact (Nat.Prime p)] (A : Type*)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsPerfectoidRing p A] : Type* :=
  PreTilt (powerBoundedSubring.toSubring A) p
```

Uses Mathlib's `PreTilt O p = Perfection (O ⧸ Ideal.span {p}) p`.

**3.2 The tilt is perfectoid (char p):**
```
instance PerfectoidRing.tilt.isPerfectoidRing [IsPerfectoidRing p A] :
    IsPerfectoidRing p (PerfectoidRing.tilt p A) := sorry
```

**3.3 A_inf — the Witt vectors of the tilt:**
```
abbrev Ainf (p : ℕ) [Fact (Nat.Prime p)] (A : Type*)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsPerfectoidRing p A] : Type* :=
  WittVector p (PerfectoidRing.tilt p A)
```

**3.4 Fontaine's theta for perfectoid rings:**
```
def PerfectoidRing.theta [IsPerfectoidRing p A] :
    Ainf p A →+* powerBoundedSubring.toSubring A :=
  WittVector.fontaineTheta _ p
```

### Key sorry'd theorems
- `PerfectoidRing.theta_surjective` — theta is surjective
- `PerfectoidRing.ker_theta_principal` — ker(theta) is principal
- `PerfectoidRing.tilt_isPerfect` — A♭ is perfect (Frobenius bijective)
- `PerfectoidField.tiltingEquiv` — tilting equivalence for fields (the big one)

---

## Sub-project 4: Perfectoid Spaces

**File:** `Adic spaces/PerfectoidSpace.lean`

**Mathlib status:** Nothing. Uses our `Spa`, `VObj`, `AdicSpace`.

### Definitions

**4.1 Affinoid perfectoid space:**
```
/-- An affinoid perfectoid space is Spa(A, A⁺) for a perfectoid ring A. -/
structure AffinoidPerfectoidSpace (p : ℕ) [Fact (Nat.Prime p)] where
  Ring : Type*
  [instCommRing : CommRing Ring]
  [instTopologicalSpace : TopologicalSpace Ring]
  [instIsTopologicalRing : IsTopologicalRing Ring]
  [instPlusSubring : PlusSubring Ring]
  [instPerfectoidRing : IsPerfectoidRing p Ring]
```

**4.2 Perfectoid space** (locally affinoid perfectoid):
```
/-- A perfectoid space is an adic space that is locally isomorphic to
Spa(A, A⁺) for perfectoid rings A (Scholze, Definition 3.19). -/
class IsPerfectoidSpace (p : ℕ) [Fact (Nat.Prime p)]
    (X : AdicSpace) : Prop where
  locally_perfectoid : ∀ x : X.carrier, ∃ (U : Opens X.carrier),
    x.val ∈ U ∧ ∃ (A : Type*) [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [PlusSubring A] [IsPerfectoidRing p A],
      Nonempty (U ≃ₜ Spa A A⁺)
```

### Key sorry'd theorems
- `AffinoidPerfectoidSpace.isSheafy` — perfectoid affinoid is sheafy
- `AffinoidPerfectoidSpace.isStablyUniform` — perfectoid affinoid is stably uniform
- `AffinoidPerfectoidSpace.isPerfectoidSpace` — affinoid perfectoid is a perfectoid space
- `PerfectoidSpace.tilt` — the tilt of a perfectoid space is perfectoid (char p)

---

## Sub-project 5: Fargues–Fontaine Curve

**File:** `Adic spaces/FarguesFontaine.lean`

**Depends on:** Sub-projects 2, 3 + our `Spa`, `VObj` + Mathlib `WittVector`.

**Key insight:** The adic FF curve only needs `A_inf = W(O_E)` and the Frobenius
action on `Spa`. No period rings (B_dR, B_crys) are required.

### Definitions

**5.1 Setup** — Fix a perfectoid field E of char p:
```
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (E : Type*) [Field E] [IsPerfectoidField p E] [CharP E p]
```

**5.2 The Huber pair (W(O_E), W(O_E)):**
```
/-- W(O_E) as a Huber ring. Since O_E is a perfect valuation ring of char p,
W(O_E) is a complete DVR (Mathlib), hence a Huber ring. -/
instance : IsHuberRing (WittVector p O_E) := sorry

/-- W(O_E) is its own plus subring (integrally closed DVR). -/
instance : PlusSubring (WittVector p O_E) := sorry
```

**5.3 Y_FF — the pre-curve:**
```
/-- The pre-curve Y_FF = Spa(W(O_E), W(O_E)) \ V(p, [π]).
This is the complement of the simultaneous vanishing locus of p and [π]
in the adic spectrum, where π is a pseudo-uniformizer of E. -/
def Y_FF (π : PseudoUniformizer E) : Set (Spa (WittVector p O_E) _) :=
  {v | ¬ (v.val.vle (p : WittVector p O_E) 0 ∧
          v.val.vle (WittVector.teichmuller _ π.val) 0)}
```

**5.4 Frobenius action on Y_FF:**
```
/-- The Frobenius φ acts on Y_FF via Spv.comap of WittVector.frobenius.
This is well-defined because φ preserves V(p, [π]). -/
def Y_FF.frobeniusAction (π : PseudoUniformizer E) :
    Y_FF p E π → Y_FF p E π := sorry
```

**5.5 X_FF — the Fargues–Fontaine curve:**
```
/-- The adic Fargues–Fontaine curve X_FF = Y_FF / φ^ℤ.
This is the quotient of the pre-curve by the discrete Frobenius action. -/
def X_FF (π : PseudoUniformizer E) : Type* :=
  Quotient (Y_FF.frobeniusOrbitRel p E π)
```

### Key sorry'd theorems
- `X_FF_isNoetherian` — X_FF is noetherian
- `X_FF_isRegular` — X_FF is regular (all stalks are regular local rings)
- `X_FF_dim_one` — Krull dimension is 1
- `X_FF_classicalPoints` — classical points ↔ untilts of E up to Frobenius

---

## Deferred: Period Rings

**Not on critical path.** Can be built independently for p-adic Hodge theory.

When ready, create `Adic spaces/PeriodRings.lean` with:
- `BdRPlus p R` — re-export Mathlib's `BDeRhamPlus` with our notation
- `BdR p R` — re-export Mathlib's `BDeRham`
- `Acrys p R` — PD-envelope of A_inf w.r.t. ker(θ) (needs PD envelope construction)
- `Bcrys p R` — `Acrys[1/p]`
- Frobenius on each, embeddings `B_crys ↪ B_dR`
- Schematic FF curve via `Proj(⊕_d B_crys^{φ=p^d})`

**Blocked on:** Divided power envelope construction (not in Mathlib).

---

## Scottish Book Problems Unlocked

With Sub-projects 1–4, these 15 problems become statable:

| Problems | What they need | Sub-project |
|----------|---------------|-------------|
| 2, 4, 21, 34 | `IsPerfectoidRing`, `IsPerfectoidSpace` | 2, 4 |
| 3, 13 | `IsPerfectoidRing` + group action | 2 |
| 5, 32, 33 | `IsPerfectoidRing` + Witt vectors | 2, 3 |
| 6, 20 | `IsPerfectoidRing` + seminormalization | 2 |
| 14, 38 | `IsPerfectoidField` + tilting | 2, 3 |
| 22 | tilting correspondence + finite morphisms | 3 |
| 25, 26 | `IsPerfectoidSpace` + rigid analytic | 4 |
| 16 | diamonds (beyond scope, needs pro-étale) | — |
| 40 | tilde-inverse limits | — |

Problems 16 and 40 remain out of scope (rating 10).

---

## File Organization (mathlib-ready)

```
Adic spaces/
  AlmostMathematics.lean      — Sub-project 1 (mathlib candidate)
  PseudoUniformizer.lean       — Sub-project 2
  PerfectoidRing.lean          — Sub-project 2 (mathlib candidate)
  Tilting.lean                 — Sub-project 3
  PerfectoidSpace.lean         — Sub-project 4
  FarguesFontaine.lean         — Sub-project 5
```

Each file is self-contained with proper imports, docstrings, and Wedhorn/Scholze
references. Definitions are complete (no `True` placeholders); proofs of deep
theorems use `sorry` with docstrings explaining what needs to be proved.

---

## Parallelization Plan

```
Start ─┬── Sub-project 1 (Almost Mathematics) ─────────────────────────┐
       │                                                                │
       └── Sub-project 2 (Perfectoid Rings) ──┬── Sub-project 4 ──── Sub-project 5
                       │                       │  (Perf. Spaces)     (FF Curve)
                       └── Sub-project 3 ──────┘
                           (Tilting)
```

- **Sub-projects 1 and 2** start immediately in parallel
- **Sub-project 3** needs 2 (for `IsPerfectoidRing`)
- **Sub-project 4** needs 2
- **Sub-project 5** needs 2, 3, 4

**Estimated tickets per sub-project:**
1. Almost Mathematics: 6 tickets
2. Perfectoid Rings: 8 tickets
3. Tilting: 6 tickets
4. Perfectoid Spaces: 5 tickets
5. Fargues–Fontaine: 6 tickets

**Total: ~31 tickets**

---

## Success Criteria

1. All definitions compile (zero errors, sorry only in theorem proofs)
2. The 15 remaining Scottish Book problems (excluding 16, 40) are statable
3. `IsPerfectoidRing` + `IsPerfectoidField` have correct mathematical content
4. `X_FF` is defined as a quotient of an open subset of `Spa(W(O_E))`
5. `A_inf = W(O_E♭)` connects to Mathlib's Witt vectors and theta map
6. The tilting functor `A ↦ A♭` maps perfectoid to perfectoid (sorry'd proof)
7. Almost mathematics has a clean API (`AlmostSetup`, `IsAlmostZero`, etc.)
