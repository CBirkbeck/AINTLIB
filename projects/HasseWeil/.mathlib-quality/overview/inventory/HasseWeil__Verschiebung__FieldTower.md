# Inventory: ./HasseWeil/Verschiebung/FieldTower.lean

**File**: `HasseWeil/Verschiebung/FieldTower.lean`
**Module**: `HasseWeil` (namespace)
**Import**: `HasseWeil.Frobenius`
**Total declarations**: 4 (all theorems, no defs/instances)

---

## Context

This file establishes the field-tower facts needed for the Verschiebung construction
over a finite field `K = F_q` and an elliptic curve `W : WeierstrassCurve K`:

```
K  ⊆  Im([q]*)  ⊆?  K(E)^q = Im(π*)  ⊆  K(E)
```

---

## Declarations

---

### `theorem frobeniusIsog_pullback_finrank`

- **Type**:
  ```
  frobeniusIsog_pullback_finrank :
    @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (frobeniusIsog W).toAlgebra.toModule = Fintype.card K
  ```
- **What**: States that the degree `[K(E) : Im(π*)]` equals `q = #K`. That is, the Frobenius isogeny's pullback has codimension `q` in `K(E)`.
- **How**: One-liner proof — directly specialises `frobeniusIsog_degree W` from `HasseWeil/Frobenius.lean`, which establishes that the degree of `frobeniusIsog W` is `#K`.
- **Hypotheses**: `K` a finite field, `W : WeierstrassCurve K`, `W.toAffine.IsElliptic`.
- **Uses from project**: `frobeniusIsog W` (Frobenius.lean), `frobeniusIsog_degree W` (Frobenius.lean).
- **Used by**: Referenced in comments of `HasseWeil/Verschiebung/PurelyInsep.lean` (lines 197–198).
- **Visibility**: public
- **Lines**: 69–72, proof length: 1 line (single term-mode proof)
- **Notes**: No `set_option maxHeartbeats`. Trivial wrapper; potential mathlib-style note: could be a `@[simp]` alias. The type annotation uses `@Module.finrank` with explicit universe arguments to unambiguously specify the algebra structure.

---

### `theorem mulByInt_q_pullback_finrank`

- **Type**:
  ```
  mulByInt_q_pullback_finrank :
    @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAlgebra.toModule =
      Fintype.card K ^ 2
  ```
- **What**: States that `[K(E) : Im([q]*)] = q²`, i.e., the multiplication-by-`q` isogeny's pullback has codimension `q²` in `K(E)`.
- **How**: Reduces via `mulByInt_degree` (from `Basic.lean`) to `(q² : ℤ).toNat = q^2 : ℕ`, which is discharged by `push_cast` + `ring` + `Int.toNat_natCast`. The key step is a `change` to expose `.degree`, then `rw [h]` with the degree identity, then a `show` with an explicit cast identity.
- **Hypotheses**: `K` a finite field, `W : WeierstrassCurve K`, `W.toAffine.IsElliptic`. Also uses `hq : (q : ℤ) ≠ 0` (derived from `Fintype.card_pos`).
- **Uses from project**: `mulByInt W.toAffine` (project isogeny), `mulByInt_degree` (Basic.lean).
- **Used by**: Referenced in comments/proof of `HasseWeil/Verschiebung/PurelyInsep.lean` (lines 197–198).
- **Visibility**: public
- **Lines**: 78–90, proof length: ~10 lines
- **Notes**: No `set_option maxHeartbeats`. The cast manipulation `(((q : ℕ) : ℤ) ^ 2).toNat = q ^ 2` is slightly involved but correct. Inline comment `-- Show ((((Fintype.card K : ℕ) : ℤ)) ^ 2).toNat = Fintype.card K ^ 2` clarifies intent.

---

### `theorem mulByInt_q_pullback_image_subset_frobenius_witness`

- **Type**:
  ```
  mulByInt_q_pullback_image_subset_frobenius_witness
      (h_qth_root : ∀ z : W.toAffine.FunctionField,
        ∃ g : W.toAffine.FunctionField,
          g ^ Fintype.card K = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z)
      : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.fieldRange ≤
          (frobeniusIsog W).pullback.fieldRange
  ```
- **What**: Given that every element of `Im([q]*)` has a `q`-th root in `K(E)`, proves the inclusion `Im([q]*) ⊆ Im(π*)` (Silverman III.6.2, witness form). This is the load-bearing Verschiebung inclusion.
- **How**: Given `f = [q]*.pullback z`, uses `h_qth_root z` to extract `g` with `g^q = [q]*.pullback z`, then uses `frobeniusIsog_pullback_apply` (which says `π*.pullback g = g^q`) to show `π*.pullback g = f`, yielding `f ∈ Im(π*)`.
- **Hypotheses**: In addition to the curve hypotheses, requires the witness hypothesis `h_qth_root` (existence of `q`-th roots for all pullback elements).
- **Uses from project**: `frobeniusIsog W` (Frobenius.lean), `mulByInt W.toAffine` (project isogeny), `frobeniusIsog_pullback_apply` (Frobenius.lean).
- **Used by**: `HasseWeil/Verschiebung/PurelyInsep.lean` line 241 calls this theorem directly.
- **Visibility**: public
- **Lines**: 117–131, proof length: ~9 lines
- **Notes**: No `set_option maxHeartbeats`. The theorem is in "witness form" — the unconditional version (discharging `h_qth_root`) is deferred to Session 3. No `sorry` in this file's proof; the hypothesis carries the content.

---

### `theorem mulByInt_q_factor_witness`

- **Type**:
  ```
  mulByInt_q_factor_witness
      (V : W.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
      (h_factor : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback =
        (frobeniusIsog W).pullback.comp V)
      : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.fieldRange ≤
          (frobeniusIsog W).pullback.fieldRange
  ```
- **What**: Given an algebra hom `V` (the Verschiebung pullback candidate) satisfying the factoring identity `[q]* = π* ∘ V*`, produces the inclusion `Im([q]*) ⊆ Im(π*)`. Alternative parametrization of the same inclusion via an explicit algebra hom rather than a root-existence witness.
- **How**: For `f = [q]*.pullback z`, sets the witness `V z` and computes `π*.pullback (V z) = (π* ∘ V*) z = [q]*.pullback z = f` via `h_factor`. The key step is an explicit `rw [show ... from rfl]` to unfold `comp` before applying `h_factor`.
- **Hypotheses**: `V` an `K`-algebra endomorphism of `K(E)` and the factoring identity `h_factor`.
- **Uses from project**: `frobeniusIsog W` (Frobenius.lean), `mulByInt W.toAffine` (project isogeny).
- **Used by**: Not referenced anywhere else in this file. Not found in other project files (dead-code candidate within the project).
- **Visibility**: public
- **Lines**: 152–163, proof length: ~8 lines
- **Notes**: No `set_option maxHeartbeats`. This is a second/alternative witness parametrization; may be redundant given `mulByInt_q_pullback_image_subset_frobenius_witness`. The doc-comment notes it is the canonical choice once the unconditional Verschiebung is built.

---

## Summary statistics

| Metric | Count |
|--------|-------|
| Total declarations | 4 |
| Theorems/Lemmas | 4 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Proofs > 30 lines | 0 |

## Key API (used by 3+ declarations in this file)

None — each declaration is independent; `frobeniusIsog W` and `mulByInt W.toAffine` appear across multiple declarations but these are project-level constructs imported from Frobenius.lean/Basic.lean, not declared in this file.

## Unused (dead-code candidates within file)

- `mulByInt_q_factor_witness` — not referenced by any other declaration in this file.
- `frobeniusIsog_pullback_finrank` — not referenced by any other declaration in this file.
- (Both are used by external files: `PurelyInsep.lean` uses the first three; `mulByInt_q_factor_witness` appears unused in any project file.)

## Notes

This is a thin "field tower" scaffolding file (4 theorems, ~165 lines including module doc). All theorems carry their substantive mathematical content as explicit hypotheses — the file ships the reductions/frameworks but defers the hard inclusions to Session 3. No sorries, no heartbeat overrides, no long proofs.
