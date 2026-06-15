# Inventory: ./HasseWeil/FormalGroupBridge.lean

**File**: `HasseWeil/FormalGroupBridge.lean`
**Lines**: 1–124
**Purpose**: Bridge between the formal group world (linear coefficient of the formal power series expansion of α*(t)) and the function-field omega-pullback coefficient world (`omegaPullbackCoeff`). Provides the abstract additivity theorem and concrete instances for `[n]`.

**Imports**: `HasseWeil.OmegaPullbackCoeff`, `HasseWeil.LocalExpansion`, `HasseWeil.FormalGroupAssoc`

---

## Declarations

### `theorem isogPullbackCoeff_add_of_formal`

- **Type**:
  ```
  (α β αβ : Isogeny W.toAffine W.toAffine)
  (a_α a_β a_αβ : KE)
  (hα : omegaPullbackCoeff W α = a_α)
  (hβ : omegaPullbackCoeff W β = a_β)
  (hαβ : omegaPullbackCoeff W αβ = a_αβ)
  (h_add : a_αβ = a_α + a_β) :
  omegaPullbackCoeff W αβ = omegaPullbackCoeff W α + omegaPullbackCoeff W β
  ```
- **What**: Given that three isogenies α, β, αβ have omega-pullback coefficients equal to explicit elements a_α, a_β, a_αβ in K(E), and that a_αβ = a_α + a_β, concludes that the omega-pullback coefficient of αβ is the sum of those of α and β.
- **How**: Pure `rw` chain: substitutes `hαβ`, `hα`, `hβ`, then `h_add`. One-line proof. The mathematical content (formal group law preserving the linear term) is entirely in the *hypotheses*; the theorem is a pure transitivity wrapper.
- **Hypotheses**: Three explicit bridge hypotheses (each isogeny's omega-pullback coefficient equals a named element), plus the formal-group addition identity at the linear coefficient level. Requires W to be an elliptic curve over a field with `DecidableEq`.
- **Uses from project**: `omegaPullbackCoeff` (from `OmegaPullbackCoeff.lean`)
- **Used by**: `bridge_mulByInt`, `omegaPullbackCoeff_mulByInt_add` (indirectly, via being the abstract template), `omegaPullbackCoeff_isConstant_of_witness` (none — none call it directly within this file). Referenced in comments in `FormalIsogenySeries.lean` and `PullbackCoeff.lean` as intended downstream consumer.
- **Visibility**: public
- **Lines**: 66–75, proof length 1 line
- **Notes**: None. No sorry. Deliberately thin — the design principle is that hypothesis satisfaction is discharged in caller files (`BridgeMulByInt`, `BridgeFrobenius`, etc.).

---

### `theorem bridge_mulByInt`

- **Type**:
  ```
  (n : ℤ) (hn : n ≠ 0) :
  omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n
  ```
- **What**: The omega-pullback coefficient of the multiplication-by-n isogeny [n] equals the image of n in K(E) via the structure map from the base field F. This is the "bridge" for the [n] family.
- **How**: One-line `exact`, forwarding directly to `omegaPullbackCoeff_mulByInt` from `OmegaPullbackCoeff.lean`. No new argument.
- **Hypotheses**: n ≠ 0 (the [n] isogeny must be nonzero).
- **Uses from project**: `omegaPullbackCoeff_mulByInt` (from `OmegaPullbackCoeff.lean`), `mulByInt`, `omegaPullbackCoeff`
- **Used by**: `omegaPullbackCoeff_mulByInt_add`, `omegaPullbackCoeff_mulByInt_isConstant` (within this file). Also called directly in `BridgeMulByInt.lean:1041`.
- **Visibility**: public
- **Lines**: 84–86, proof length 1 line
- **Notes**: None. No sorry. Acts as a thin named alias for `omegaPullbackCoeff_mulByInt`; the name `bridge_mulByInt` aligns with the file's bridge theme.

---

### `theorem omegaPullbackCoeff_mulByInt_add`

- **Type**:
  ```
  (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m + n ≠ 0) :
  omegaPullbackCoeff W (mulByInt W.toAffine (m + n)) =
    omegaPullbackCoeff W (mulByInt W.toAffine m) +
      omegaPullbackCoeff W (mulByInt W.toAffine n)
  ```
- **What**: The omega-pullback coefficient of [m+n] equals the sum of those of [m] and [n], for nonzero m, n, m+n. This is the additivity of the bridge for the [n] family as a sanity check.
- **How**: Rewrites all three sides via `bridge_mulByInt`, then uses `map_add` (ring hom sends sums to sums) and `Int.cast_add` (cast of a sum is sum of casts). Pure algebraic calculation in K(E).
- **Hypotheses**: m ≠ 0, n ≠ 0, m+n ≠ 0 (all three isogenies must be nonzero).
- **Uses from project**: `bridge_mulByInt`, `omegaPullbackCoeff`, `mulByInt`
- **Used by**: unused in file (no other declaration in this file calls it)
- **Visibility**: public
- **Lines**: 93–99, proof length 2 lines
- **Notes**: Described in the docstring as a "sanity check". No sorry. Not referenced by any other project file (dead-code candidate for this file; may be intended as an example/test).

---

### `theorem omegaPullbackCoeff_isConstant_of_witness`

- **Type**:
  ```
  (α : Isogeny W.toAffine W.toAffine) (c : F)
  (h : omegaPullbackCoeff W α = algebraMap F KE c) :
  omegaPullbackCoeff W α ∈ (algebraMap F KE).range
  ```
- **What**: If the omega-pullback coefficient of α is witnessed to equal the image of some c : F under the structure map, then it lies in the range of that map (i.e., it is a "constant" element of K(E)).
- **How**: Rewrites using h, then provides the explicit witness ⟨c, rfl⟩ for range membership. A one-line proof.
- **Hypotheses**: An explicit base-field witness c and the bridge identity.
- **Uses from project**: `omegaPullbackCoeff`
- **Used by**: `omegaPullbackCoeff_mulByInt_isConstant` (within this file). Referenced by name in a comment in `GapQfKernel.lean:1092`.
- **Visibility**: public
- **Lines**: 111–115, proof length 1 line
- **Notes**: No sorry. Companion to the main bridge — extracts range-membership from a concrete witness. Intended as T-IV-BRIDGE-002 in the project's ticket system.

---

### `theorem omegaPullbackCoeff_mulByInt_isConstant`

- **Type**:
  ```
  (n : ℤ) (hn : n ≠ 0) :
  omegaPullbackCoeff W (mulByInt W.toAffine n) ∈ (algebraMap F KE).range
  ```
- **What**: The omega-pullback coefficient of [n] lies in the base field F (viewed as a subfield of K(E) via the structure map). Axiom-clean.
- **How**: Term-mode proof: applies `omegaPullbackCoeff_isConstant_of_witness` with explicit witness `(n : F)` and forwards to `omegaPullbackCoeff_mulByInt` for the bridge identity.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: `omegaPullbackCoeff_isConstant_of_witness`, `omegaPullbackCoeff_mulByInt` (from `OmegaPullbackCoeff.lean`), `mulByInt`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 118–121, proof length 1 line (term-mode)
- **Notes**: No sorry. Described as "axiom-clean" in the docstring (T-IV-BRIDGE-002 for the [n] family). Dead-code candidate within this file.

---

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total declarations | 5 |
| Theorems/Lemmas | 5 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| Long proofs (>30 lines) | 0 |
| set_option maxHeartbeats | 0 |

## Key API within the file

- `bridge_mulByInt`: used by `omegaPullbackCoeff_mulByInt_add` and `omegaPullbackCoeff_mulByInt_isConstant` (via `omegaPullbackCoeff_isConstant_of_witness` chain) — most widely used within this file.
- `omegaPullbackCoeff_isConstant_of_witness`: used by `omegaPullbackCoeff_mulByInt_isConstant`.

## Dead-code candidates (within this file)

- `omegaPullbackCoeff_mulByInt_add`: not called by any other declaration in this file; described as a "sanity check".
- `omegaPullbackCoeff_mulByInt_isConstant`: not called by any other declaration in this file.
- `isogPullbackCoeff_add_of_formal`: not called within this file (the abstract template is meant for external callers like `BridgeMulByInt`, `BridgeFrobenius`).

## Notes

This is a thin scaffold/interface file: all proofs are 1–2 lines and contain no sorry. The mathematical weight lives entirely in `OmegaPullbackCoeff.lean` (which proves `omegaPullbackCoeff_mulByInt`) and the caller files (`BridgeMulByInt.lean`, `BridgeFrobenius.lean`) which verify the bridge hypotheses for concrete isogenies. The file's main declaration `isogPullbackCoeff_add_of_formal` is a pure-transitivity wrapper by design.
