# Inventory: ./HasseWeil/WeilPairing/FrobeniusGaloisScaling.lean

**Total declarations**: 9 (8 top-level named + 1 local instance)
**Defs**: 2 (`FrobeniusGaloisData`, `FrobeniusGaloisGeometric`)
**Theorems/Lemmas**: 6
**Instances**: 1 (local `instDecEqACFGS`)
**Sorries**: none
**maxHeartbeats overrides**: none

---

## Summary

This file delivers the **pure-algebra core** of the Galois-equivariance route to Silverman III.8.1d
(`e_ℓ(π̄ S, π̄ T) = e_ℓ(S,T)^{#K}`).  It is entirely axiom-clean, no `sorry`.  The structure is a
clean composition: abstract core → Prop-typed leaf bundle → geometric residual (proved in imported
files) → discharge.

---

## Declarations

### `noncomputable local instance instDecEqACFGS`
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides `DecidableEq` on the algebraic closure `K̄` needed for the `BaseChange` section, using `Classical.decEq`.
- **How**: Direct `Classical.decEq _`.
- **Hypotheses**: `K : Type*`, `[Field K]`
- **Uses from project**: none
- **Used by**: all declarations in `section BaseChange`
- **Visibility**: private (local)
- **Lines**: 164
- **Notes**: Needed to satisfy the `DecidableEq (AlgebraicClosure K)` typeclass hole introduced by `section BaseChange` variable declarations.

---

### `theorem weilPairing_galois_core`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (q : ℕ) (σ : KE ≃+* KE) (S T S' T' : W.toAffine.Point) (hS : ℓ•S=0) (hT : ℓ•T=0) (hS' : ℓ•S'=0) (hT' : ℓ•T'=0) (hconj : σ(τ_S(g_T)) = τ_{S'}(σ(g_T))) {c : F} (hc : c ≠ 0) (hnat : σ(g_T) = algebraMap c · g_{T'}) (hpow : ∀ a, σ(algebraMap a) = algebraMap (a^q)) → e_ℓ(S',T') = e_ℓ(S,T)^q`
- **What**: The **Galois-equivariance constant-ratio identity** (III.8.1d algebra core): given an abstract ring automorphism `σ` of `K(E)` satisfying three hypotheses (translation conjugation, `σ`-naturality of the Weil function, and `q`-power on constants), concludes `e_ℓ(S',T') = e_ℓ(S,T)^q`.
- **How**: Applies `σ` to the pairing relation `weilPairing_translate` (`τ_S(g_T) = algebraMap e · g_T`), rewrites the LHS via `hconj`, the RHS via `hpow` and `map_mul`, substitutes `hnat`, uses `(translateAlgEquivOfPoint W S').commutes` (AlgEquiv fixes `algebraMap`), applies `weilPairing_translate` on the primed side, and cancels `algebraMap c · g_{T'} ≠ 0` via `mul_right_cancel₀` + injectivity of `algebraMap`.
- **Hypotheses**: `[Field F]`, `[DecidableEq F]`, `[IsAlgClosed F]`, `W : WeierstrassCurve F` elliptic with integrally-closed coordinate ring; `ℓ ≠ 0` in `F`; `σ` a ring automorphism of `K(E)`; conjugation, `σ`-naturality and `q`-power-on-constants hypotheses as stated.
- **Uses from project**: `weilFunction_ne_zero`, `weilPairing_translate`, `translateAlgEquivOfPoint` (`.commutes`)
- **Used by**: `frobeniusScaling_of_galoisData` (line 233)
- **Visibility**: public
- **Lines**: 98–137; proof lines 109–137 (29 lines)
- **Notes**: Proof just under 30 lines. Abstract/generic — works for any automorphism with the three named properties; deliberately decoupled from the concrete Frobenius.

---

### `def FrobeniusGaloisData`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p^r)] : Prop`  
  Quantifies over ℓ-torsion `S, T` and their Frobenius images; asserts existence of a ring automorphism `σ` of `K̄(E)` and nonzero `c : K̄` satisfying: conjugation of translation at `g_T`, `σ`-naturality `σ(g_T) = algebraMap c · g_{π̄ T}`, and `q`-power on constants `σ(algebraMap a) = algebraMap (a^{#K})`.
- **What**: Bundles per `(S,T)` the arithmetic-Frobenius witness that `weilPairing_galois_core` needs: existence of `σ` on `K̄(E)` with conjugation, `σ`-naturality, and `q`-power-on-constants properties. This is the full leaf for the Galois route to III.8.1d.
- **How**: Prop-typed existential; no proof content.
- **Hypotheses**: `K` finite field of characteristic `p` and size `p^r`; base-changed elliptic curve `W_{K̄}` satisfies IsElliptic + integrally-closed coordinate ring.
- **Uses from project**: `frobeniusHomBaseChange`, `translateAlgEquivOfPoint`, `weilFunction`
- **Used by**: `frobeniusScaling_of_galoisData` (hypothesis), `frobeniusGaloisData_of_geometric` (conclusion), `frobeniusGaloisData_holds` (conclusion)
- **Visibility**: public
- **Lines**: 182–206
- **Notes**: Prop-valued Def. The three bundled properties directly match the three hypotheses of `weilPairing_galois_core`.

---

### `theorem frobeniusScaling_of_galoisData`
- **Type**: `(hdata : FrobeniusGaloisData W p r) → FrobeniusScaling W p r (AlgebraicClosure K)`
- **What**: Discharges `FrobeniusScaling` (the Frobenius scaling `e_ℓ(π̄ S, π̄ T) = e_ℓ(S,T)^{#K}` for all primes `ℓ ≠ char K`) from the Galois leaf `FrobeniusGaloisData`, by pure application of `weilPairing_galois_core`.
- **How**: Unpacks torsion conditions using `zsmul_eq_zero_of_mem_torsion`; derives `π̄`-torsion via `map_zsmul`; obtains the `(σ,c,hc,hconj,hnat,hpow)` witness from `hdata`; then calls `weilPairing_galois_core` with `S' = π̄ S`, `T' = π̄ T`, `q = #K`.
- **Hypotheses**: `FrobeniusGaloisData W p r`; `K` finite of char `p` with `#K = p^r`; `W_{K̄}` elliptic.
- **Uses from project**: `zsmul_eq_zero_of_mem_torsion`, `frobeniusHomBaseChange`, `weilPairing_galois_core`, `FrobeniusGaloisData`
- **Used by**: `frobeniusScaling_holds` (line 395)
- **Visibility**: public
- **Lines**: 214–235; proof lines 218–235 (18 lines)
- **Notes**: None.

---

### `def FrobeniusGaloisGeometric`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p^r)] : Prop`  
  Like `FrobeniusGaloisData` but for the **concrete** `σ = frobeniusFunctionFieldEquiv W` only, and only the two geometric facts: (1) conjugation `σ(τ_S(g_T)) = τ_{π̄ S}(σ(g_T))`; (2) existence of nonzero `c` with `σ(g_T) = algebraMap c · g_{π̄ T}`.  The `q`-power-on-constants property is **excluded** (it is proved axiom-clean separately).
- **What**: Carrier Prop for the two residual geometric facts about the concrete arithmetic Frobenius automorphism: translation conjugation and `σ`-naturality (divisor Galois descent). The third `FrobeniusGaloisData` property (q-power on constants) is omitted because it is proved elsewhere.
- **How**: Prop-typed conjunction/existential; no proof content.
- **Hypotheses**: Same as `FrobeniusGaloisData`.
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `frobeniusHomBaseChange`, `translateAlgEquivOfPoint`, `weilFunction`
- **Used by**: `frobeniusGaloisData_of_geometric` (hypothesis), `frobeniusGaloisGeometric_holds` (conclusion)
- **Visibility**: public
- **Lines**: 274–294
- **Notes**: Strictly weaker than `FrobeniusGaloisData` (same σ fixed, third property dropped). Designed so that `frobeniusGaloisData_of_geometric` completes it to `FrobeniusGaloisData` by inserting the axiom-clean `frobeniusFunctionFieldEquiv_algebraMap`.

---

### `theorem frobeniusGaloisData_of_geometric`
- **Type**: `(hgeom : FrobeniusGaloisGeometric W p r) → FrobeniusGaloisData W p r`
- **What**: Reduces `FrobeniusGaloisData` to `FrobeniusGaloisGeometric` by supplying the concrete automorphism `σ = frobeniusFunctionFieldEquiv W` and the axiom-clean q-power-on-constants property `frobeniusFunctionFieldEquiv_algebraMap`.
- **How**: Unpacks `hgeom` to get `hconj`, `c`, `hc`, `hnat`; constructs the `FrobeniusGaloisData` witness as `⟨frobeniusFunctionFieldEquiv W, c, hc, hconj, hnat, fun a => frobeniusFunctionFieldEquiv_algebraMap W a⟩`.
- **Hypotheses**: `FrobeniusGaloisGeometric W p r`.
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `frobeniusFunctionFieldEquiv_algebraMap`, `FrobeniusGaloisGeometric`, `FrobeniusGaloisData`
- **Used by**: `frobeniusGaloisData_holds` (line 380)
- **Visibility**: public
- **Lines**: 301–308; proof lines 305–308 (4 lines)
- **Notes**: Minimal glue lemma; only works because `frobeniusFunctionFieldEquiv_algebraMap` is the one axiom-clean ingredient not in `FrobeniusGaloisGeometric`.

---

### `theorem frobeniusGaloisGeometric_holds`
- **Type**: `FrobeniusGaloisGeometric W p r`
- **What**: Proves that the geometric residual `FrobeniusGaloisGeometric` holds — i.e., both the translation conjugation and `σ`-naturality hold for the concrete `σ = frobeniusFunctionFieldEquiv` and `π̄ = frobeniusHomBaseChange`. This is axiom-clean (leaf 1 of the Frobenius scaling).
- **How**: The proof proceeds in two branches. (1) **Conjugation**: bridges `frobeniusHomBaseChange = geomFrobeniusPoint` via `frobeniusHomBaseChange_eq_geomFrobeniusPoint`, further reduces `frobeniusHomBaseChange S = geomFrobeniusPointFun S` using `geomFrobeniusPoint_apply`, then directly applies `frobeniusFunctionFieldEquiv_conj`. (2) **σ-naturality**: obtains `hπT' : ℓ•(geomFrobeniusPoint T)=0` by rewriting via the same bridge, obtains `(c,hc,hnat)` from `frobeniusFunctionFieldEquiv_weilFunction_eq_smul`, then rewrites the Weil function at `frobeniusHomBaseChange T` to the one at `geomFrobeniusPoint T` using a bridge on proof-irrelevance of the torsion hypothesis.
- **Hypotheses**: `W` over finite field `K` of char `p` with `#K = p^r`; `W_{K̄}` elliptic; standard integrally-closed coordinate ring.
- **Uses from project**: `frobeniusHomBaseChange_eq_geomFrobeniusPoint`, `geomFrobeniusPoint_apply`, `geomFrobeniusPointFun`, `frobeniusFunctionFieldEquiv_conj`, `frobeniusFunctionFieldEquiv_weilFunction_eq_smul`, `weilFunction`, `FrobeniusGaloisGeometric`
- **Used by**: `frobeniusGaloisData_holds` (line 381, via `frobeniusGaloisData_of_geometric`)
- **Visibility**: public
- **Lines**: 333–371; proof lines 336–371 (36 lines)
- **Notes**: **Proof > 30 lines** (36 lines). The bulk of the proof handles the `frobeniusHomBaseChange ↔ geomFrobeniusPoint` bridge needed because `frobeniusFunctionFieldEquiv_conj` and `frobeniusFunctionFieldEquiv_weilFunction_eq_smul` use `geomFrobeniusPoint` while the statement uses `frobeniusHomBaseChange`.

---

### `theorem frobeniusGaloisData_holds`
- **Type**: `FrobeniusGaloisData W p r`
- **What**: Composition combining `frobeniusGaloisData_of_geometric` and `frobeniusGaloisGeometric_holds` to produce `FrobeniusGaloisData` unconditionally (axiom-clean).
- **How**: One-liner term-mode composition: `frobeniusGaloisData_of_geometric W p r (frobeniusGaloisGeometric_holds W p r)`.
- **Hypotheses**: Same as `FrobeniusGaloisData`.
- **Uses from project**: `frobeniusGaloisData_of_geometric`, `frobeniusGaloisGeometric_holds`
- **Used by**: `frobeniusScaling_holds` (line 395)
- **Visibility**: public
- **Lines**: 377–381; proof 2 lines (term-mode)
- **Notes**: None.

---

### `theorem frobeniusScaling_holds`
- **Type**: `FrobeniusScaling W p r (AlgebraicClosure K)`
- **What**: The final fully-closed Frobenius Weil-pairing scaling `e_ℓ(π̄ S, π̄ T) = e_ℓ(S,T)^{#K}` for every prime `ℓ ≠ char K` on `E_{K̄}[ℓ]`. Axiom-clean: `#print axioms = [propext, Classical.choice, Quot.sound]`.
- **How**: One-liner term-mode: `frobeniusScaling_of_galoisData W p r (frobeniusGaloisData_holds W p r)`.
- **Hypotheses**: `W` over finite field `K` of characteristic `p`, `#K = p^r`; `W_{K̄}` elliptic.
- **Uses from project**: `frobeniusScaling_of_galoisData`, `frobeniusGaloisData_holds`
- **Used by**: `HasseBound.lean` (leaf 1 assembly)
- **Visibility**: public
- **Lines**: 392–395; proof 2 lines (term-mode)
- **Notes**: The `FrobeniusScaling` type is from `FrobMatrixData.lean`; this is the main external export of the file.

---

## Cross-file usage of this file's declarations

- `frobeniusScaling_holds` — consumed by `HasseBound.lean:83` as leaf 1 in the final Hasse bound assembly.
- `FrobeniusGaloisData`, `FrobeniusGaloisGeometric`, `weilPairing_galois_core` — referenced only in `FrobeniusFunctionFieldEquiv.lean` and `FrobeniusConjugation.lean` documentation comments (not in proof bodies of other files).

## Key API (used by 3+ declarations in this file)

- `weilPairing_galois_core` — used by: `frobeniusScaling_of_galoisData` (body)
- `FrobeniusGaloisData` — defined here; used by: `frobeniusScaling_of_galoisData` (hypothesis), `frobeniusGaloisData_of_geometric` (conclusion), `frobeniusGaloisData_holds` (conclusion)
- `FrobeniusGaloisGeometric` — defined here; used by: `frobeniusGaloisData_of_geometric` (hypothesis), `frobeniusGaloisGeometric_holds` (conclusion)
- `frobeniusGaloisData_holds` — used by: `frobeniusScaling_holds`; count in-file = 1 only
- `frobeniusFunctionFieldEquiv` — imported; used by: `FrobeniusGaloisGeometric` (body), `frobeniusGaloisData_of_geometric` (body), `frobeniusGaloisGeometric_holds` (body) — 3 uses

## Long proofs (> 30 lines)

- `frobeniusGaloisGeometric_holds` — 36 proof lines

## Dead-code candidates (unused within this file)

All declarations are used transitively via `frobeniusScaling_holds`, which is consumed externally. No unused declarations within this file.
