# Plan: Completion-Localization Route for T003

## Goal
Prove `restrictionMap_isLocalization` (Wedhorn Prop 8.15) by establishing
the `IsLocalization.Away` conditions algebraically, bypassing the blocked
`locLift_preimage_locNhd` / `IsUniformInducing` topological route.

## Key Insight
The Eq condition `σ(c) = 0 → ∃ n, s'^n * c = 0` is strictly WEAKER than
injectivity when `s' = D₀.canonicalMap D.s` is not a unit. It only requires
the kernel to be s'-torsion, not {0}.

## Three conditions for `IsLocalization.Away`

### 1. Unit: `σ(s')` is a unit in `presheafValue D`
**Status**: PROVED (`isUnit_s_in_presheafValue`)

### 2. Surj: `∀ z, ∃ n a, z * σ(s')^n = σ(a)`
**Status**: Separate sorry (`restrictionMapHom_surj`, Baire category argument)

### 3. Eq: `σ(c) = 0 → ∃ n, s'^n * c = 0`
**Status**: THIS IS THE T003 TARGET. Proof plan below.

## Proof of Eq condition

### Step A — Noetherian torsion stabilization
In `Loc.Away D₀.s` (Noetherian as localization of Noetherian A):
```
ann(algebraMap(D.s)) ⊆ ann(algebraMap(D.s)²) ⊆ ... stabilizes at N₀
```
So `algebraMap(D.s)^{N₀}` kills ALL `algebraMap(D.s)`-torsion elements.
In particular: `algebraMap(D.s)^{N₀} * ker(locLift) = {0}`.

**Lean signature**:
```lean
private theorem locLift_torsion_bounded
    [IsNoetherianRing A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∃ N₀ : ℕ, ∀ x : Localization.Away D₀.s,
      locLift D₀ D h x = 0 →
        algebraMap A (Localization.Away D₀.s) (D.s ^ N₀) * x = 0
```

**Proof**: Ascending chain `ann(s^n)` in the Noetherian ring `Loc.Away D₀.s`
stabilizes. Use `IsNoetherianRing` + `Ideal.isAscending`.

### Step B — Topological kernel = closure of algebraic kernel
```
ker(restrictionMapHom) = closure(D₀.coeRingHom '' ker(locLift))
```

**Lean signature**:
```lean
private theorem restrictionMapHom_ker_eq_closure
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    (RingHom.ker (restrictionMapHom D₀ D h) : Set (presheafValue D₀)) =
    closure (D₀.coeRingHom '' {x | locLift D₀ D h x = 0})
```

**Proof**:
- (⊇) `D₀.coeRingHom(ker(locLift))` maps to 0 under `restrictionMapHom`
  (by `restrictionMapHom_coe'`). Kernel is closed → closure ⊆ kernel.
- (⊆) Uses: localization is flat → adic completion preserves kernel →
  every element of the topological kernel is a limit of algebraic kernel elements.
  **This is the deepest step.** May use `AdicCompletion.map_exact` from Mathlib
  or a direct density argument with the torsion-free quotient.

### Step C — Extension to completion
For `c ∈ ker(restrictionMapHom)`: by Step B, `c = lim D₀.coeRingHom(t_n)`
where `t_n ∈ ker(locLift)`. By Step A: `algebraMap(D.s)^{N₀} * t_n = 0`
hence `D₀.coeRingHom(algebraMap(D.s)^{N₀} * t_n) = 0` hence
`s'^{N₀} * D₀.coeRingHom(t_n) = 0`. Taking limits: `s'^{N₀} * c = 0`.

**Lean signature** (the final Eq condition):
```lean
private theorem restrictionMapHom_eq_condition
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A] [FirstCountableTopology A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (c : presheafValue D₀) (hc : restrictionMapHom D₀ D h c = 0) :
    ∃ n : ℕ, (D₀.canonicalMap D.s) ^ n * c = 0
```

## Dependency on existing API
- `isUnit_s_in_presheafValue` (CompletionLocalization.lean) ✓
- `restrictionMapHom_coe'` (PresheafTateStructure.lean) ✓
- `D₀.coeRingHom` is `IsUniformInducing` (completion embedding) ✓
- `IsNoetherianRing` for `Loc.Away D₀.s` — follows from `[IsNoetherianRing A]`
- `AdicCompletion.map_exact` or equivalent — needs check in Mathlib

## Impact
Once Eq is proved:
- `restrictionMap_isLocalization` follows from Unit + Surj + Eq
- `restrictionMapHom_injective` becomes a COROLLARY: if `s'` happens to be
  a non-zero-divisor, n=0 gives injectivity; otherwise the localization
  structure still holds with nontrivial s'-torsion kernel
- `locLift_preimage_locNhd` becomes dead code (can be deleted or proved
  as a corollary from `IsLocalization.Away` + completion structure)

## Open question for Step B
Does Mathlib's `AdicCompletion.map_exact` apply to the sequence
`0 → ker(locLift) → Loc.Away D₀.s → Loc.Away D.s`?
This sequence is of `Loc.Away D₀.s`-modules, but completion is for
`locSubring D₀`-modules with `locIdeal`-adic topology. Need to check:
- Is `ker(locLift)` finitely generated as a `locSubring D₀`-module?
- Does the adic completion of `Loc.Away D₀.s` match `presheafValue D₀`?
