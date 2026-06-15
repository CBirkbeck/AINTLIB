# Inventory: ./HasseWeil/RouteBInduction.lean

**File**: `HasseWeil/RouteBInduction.lean`
**Module header**: Silverman III.5.3: `a_{[m]} = m` via curve-side additivity (Route B assembly)
**Imports**: `HasseWeil.AdditionPullback.SilvermanIV14`, `HasseWeil.Hasse.OpenLemmaPrimitives`, `HasseWeil.EC.MulByIntAddRecurrence`
**Total declarations**: 8 theorems, 0 defs, 0 instances

---

## Declarations

### `theorem omegaPullbackCoeff_addIsog_id`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) (hxy : AddNonInversePair (Isogeny.id W.toAffine) α) (hinj : Function.Injective (addCoordAlgHomPair hxy)) (h_ne : x_gen W ≠ α.pullback (x_gen W)) : omegaPullbackCoeff W (addIsog hxy hinj) = 1 + omegaPullbackCoeff W α`
- **What**: The omega-pullback coefficient (differential scaling factor) of the sum isogeny `id ⊞ α` equals `1 + a_α`. This is Silverman III.5.2 specialised to `φ = id`.
- **How**: Uniqueness in the 1-dimensional Kähler module via `omegaPullbackCoeff_unique`. Computes pullbacks of generators via `addIsog_pullback` + `OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq` + `addPullback_x_pair_id`, identifies `α*u of σ = u₃`, then applies the RB-ω4 lemma `kaehler_D_addPullback_x_eq_one_add_smul_omega` and cancels `u₃⁻¹ · u₃`.
- **Hypotheses**: A Weierstrass curve `W` over a finite field `K`; `α` is an endomorphism; `hxy` asserts `id` and `α` form a non-inverse addition pair; `hinj` says the coordinate algebra homomorphism for the pair is injective; `h_ne` says `x_gen ≠ α*(x_gen)` (non-degenerate sum).
- **Uses from project**: `addIsog_pullback`, `OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq`, `addPullback_x_pair_id`, `OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq`, `addPullback_y_pair_id`, `alpha_star_u`, `alpha_star_u_eq`, `u_gen_ne_zero`, `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`, `kaehler_D_addPullback_x_eq_one_add_smul_omega`
- **Used by**: `omegaPullbackCoeff_mulByInt_succ` (indirectly, same strategy); used externally in `GapQfKernel.lean`
- **Visibility**: public
- **Lines**: 35–69, proof length ~35 lines
- **Notes**: Proof > 30 lines.

---

### `theorem omegaPullbackCoeff_addIsog_pair`

- **Type**: `{α₁ α₂ : Isogeny W.toAffine W.toAffine} (hxy : AddNonInversePair α₁ α₂) (hinj : Function.Injective (addCoordAlgHomPair hxy)) (h_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W)) : omegaPullbackCoeff W (addIsog hxy hinj) = omegaPullbackCoeff W α₁ + omegaPullbackCoeff W α₂`
- **What**: The full general-pair Silverman III.5.2 additivity: for any genuine sum isogeny `α₁ ⊞ α₂` (with distinct x-pullbacks), the omega-pullback coefficient is the sum of those of the factors.
- **How**: Same strategy as `omegaPullbackCoeff_addIsog_id` but using the general-pair lemma `kaehler_D_addPullback_x_pair_eq_smul_omega` (which yields `u₃ • ((a_{α₁}+a_{α₂}) • ω)`) in place of the id-specific version; uniqueness via `omegaPullbackCoeff_unique`.
- **Hypotheses**: Same setup as above but for arbitrary `α₁, α₂` (no restriction to `id`); `h_ne` requires the two x-pullbacks differ.
- **Uses from project**: `addIsog_pullback`, `OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq`, `OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq`, `alpha_star_u`, `alpha_star_u_eq`, `u_gen_ne_zero`, `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`, `kaehler_D_addPullback_x_pair_eq_smul_omega`
- **Used by**: `omegaPullbackCoeff_mulByInt_succ` (same idea); used externally in `GapSpines.lean`, `WeilPairing/PencilSeparable.lean`
- **Visibility**: public
- **Lines**: 82–116, proof length ~35 lines
- **Notes**: Proof > 30 lines. This is the key API lemma for the Route B Weil pairing work (used by `genuineIsogSmulSub_isSeparable` in GapSpines).

---

### `theorem omegaPullbackCoeff_mulByInt_succ`

- **Type**: `(k : ℤ) (hk2 : 2 ≤ k) : omegaPullbackCoeff W (mulByInt W.toAffine (k + 1)) = 1 + omegaPullbackCoeff W (mulByInt W.toAffine k)`
- **What**: The chord step in the induction: `a_{[k+1]} = 1 + a_{[k]}` for all integers `k ≥ 2`.
- **How**: Uses `addPullback_xy_mulByInt_eq_succ` (the RB-ID recurrence from `MulByIntAddRecurrence`) to reduce `[k+1]*x` to `addPullback_x [k]`, `mulByInt_x_ne_mulByInt_x` to verify the non-degeneracy `x_gen ≠ [k]*x`, then applies `kaehler_D_addPullback_x_eq_one_add_smul_omega` and `omegaPullbackCoeff_unique`.
- **Hypotheses**: `k ≥ 2` (ensures `k ≠ 0`, `k+1 ≠ 0`, and `[k]*x ≠ x_gen`).
- **Uses from project**: `mulByInt_x_ne_mulByInt_x`, `mulByInt_x_one`, `mulByInt_pullback_x`, `addPullback_xy_mulByInt_eq_succ`, `alpha_star_u_mulByInt`, `alpha_star_u_eq`, `u_gen_ne_zero`, `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`, `kaehler_D_addPullback_x_eq_one_add_smul_omega`
- **Used by**: `omegaPullbackCoeff_mulByInt_ge_two`
- **Visibility**: public
- **Lines**: 135–172, proof length ~38 lines
- **Notes**: Proof > 30 lines.

---

### `theorem omegaPullbackCoeff_mulByInt_ge_two`

- **Type**: `(n : ℤ) (hn : 2 ≤ n) : omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap K KE n`
- **What**: `a_{[n]} = n` (as an element of `K(E)` via `algebraMap`) for all `n ≥ 2`, proved by `Int.le_induction`.
- **How**: Induction base `n = 2` via the separate axiom-clean lemma `omegaPullbackCoeff_mulByInt_two`; induction step uses `omegaPullbackCoeff_mulByInt_succ` and ring arithmetic on `algebraMap`.
- **Hypotheses**: `n ≥ 2`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_two`, `omegaPullbackCoeff_mulByInt_succ`
- **Used by**: `omegaPullbackCoeff_mulByInt_pos`
- **Visibility**: public
- **Lines**: 177–183, proof length 7 lines

---

### `theorem omegaPullbackCoeff_mulByInt_pos`

- **Type**: `(n : ℤ) (hn : 1 ≤ n) : omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap K KE n`
- **What**: `a_{[n]} = n` for all `n ≥ 1`, covering the `n = 1` base case (`[1] = id`, `a_id = 1`) and delegating `n ≥ 2` to `omegaPullbackCoeff_mulByInt_ge_two`.
- **How**: Case split on `n = 1` vs `n > 1`; the `n = 1` case uses `mulByInt_one_eq_id` and `omegaPullbackCoeff_id`.
- **Hypotheses**: `n ≥ 1`.
- **Uses from project**: `mulByInt_one_eq_id`, `omegaPullbackCoeff_id`, `omegaPullbackCoeff_mulByInt_ge_two`
- **Used by**: `omegaPullbackCoeff_mulByInt_routeB`
- **Visibility**: public
- **Lines**: 187–191, proof length 5 lines

---

### `theorem omegaPullbackCoeff_mulByInt_neg`

- **Type**: `(n : ℤ) (hn : n ≠ 0) : omegaPullbackCoeff W (mulByInt W.toAffine (-n)) = -omegaPullbackCoeff W (mulByInt W.toAffine n)`
- **What**: Negation symmetry: the omega-pullback coefficient of `[-n]` is the negative of that of `[n]`.
- **How**: Uses `mulByInt_x_neg` (the x-coordinate of `[-n]P` equals that of `[n]P`) and `mulByInt_y_neg` with `WeierstrassCurve.Affine.negY` to show `α*u of [-n] = -(α*u of [n])`; the spec equation then flips sign and uniqueness gives the result.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `mulByInt_pullback_x`, `mulByInt_x_neg`, `alpha_star_u_mulByInt`, `mulByInt_y_neg`, `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`
- **Used by**: `omegaPullbackCoeff_mulByInt_routeB`
- **Visibility**: public
- **Lines**: 197–221, proof length ~25 lines

---

### `theorem omegaPullbackCoeff_mulByInt_routeB`

- **Type**: `(n : ℤ) (hn : n ≠ 0) : omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap K KE n`
- **What**: The central Route B result (Silverman III.5.3, integer form): `a_{[n]} = n` for all nonzero integers `n`, without EDS Wronskian or formal group.
- **How**: Splits into `n < 0` (use `omegaPullbackCoeff_mulByInt_neg` to reduce to positive, then `omegaPullbackCoeff_mulByInt_pos`) and `n > 0` (direct from `omegaPullbackCoeff_mulByInt_pos`).
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_neg`, `omegaPullbackCoeff_mulByInt_pos`
- **Used by**: `omegaPullbackCoeff_mulByInt_p_eq_zero_routeB`, `omegaPullbackCoeff_mulByInt_card_eq_zero`; extensively used externally (GapSpines, GapQfKernel, OmegaPullbackCoeff comments, WeilPairing/TorsionSeparable, TorsionGeometric)
- **Visibility**: public
- **Lines**: 226–235, proof length 10 lines

---

### `theorem omegaPullbackCoeff_mulByInt_p_eq_zero_routeB`

- **Type**: `(p : ℕ) [CharP K p] (hp : p ≠ 0) : omegaPullbackCoeff W (mulByInt W.toAffine (p : ℤ)) = 0`
- **What**: In characteristic `p`, the omega-pullback coefficient of `[p]` vanishes (`a_{[p]} = (p : K) = 0`). Wronskian-free and formal-group-free pillar B endpoint.
- **How**: Applies `omegaPullbackCoeff_mulByInt_routeB` and then `CharP.cast_eq_zero` to reduce `(p : K) = 0`.
- **Hypotheses**: `CharP K p` and `p ≠ 0`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_routeB`
- **Used by**: unused in file; used externally in `GapQfKernel.lean`
- **Visibility**: public
- **Lines**: 241–244, proof length 4 lines

---

### `theorem omegaPullbackCoeff_mulByInt_card_eq_zero`

- **Type**: `omegaPullbackCoeff W (mulByInt W.toAffine (Fintype.card K : ℤ)) = 0`
- **What**: Over the finite field `K` with `q = #K` elements, the omega-pullback coefficient of `[q]` vanishes (`a_{[q]} = 0`), since `q ≡ 0` in `K`. This is the q-th-root input to the Verschiebung factorisation `[q] = V ∘ Frob`.
- **How**: Applies `omegaPullbackCoeff_mulByInt_routeB` and then `FiniteField.cast_card_eq_zero` (via `Fintype.card_ne_zero`).
- **Hypotheses**: `K` a finite field, `W` an elliptic curve over `K`.
- **Uses from project**: `omegaPullbackCoeff_mulByInt_routeB`
- **Used by**: unused in file; potentially used externally
- **Visibility**: public
- **Lines**: 250–255, proof length 5 lines

---

## Cross-reference summary

| Callers | Called |
|---------|--------|
| `omegaPullbackCoeff_mulByInt_ge_two` | `omegaPullbackCoeff_mulByInt_succ`, `omegaPullbackCoeff_mulByInt_two` |
| `omegaPullbackCoeff_mulByInt_pos` | `omegaPullbackCoeff_mulByInt_ge_two`, `mulByInt_one_eq_id`, `omegaPullbackCoeff_id` |
| `omegaPullbackCoeff_mulByInt_neg` | `mulByInt_pullback_x`, `mulByInt_x_neg`, `alpha_star_u_mulByInt`, `mulByInt_y_neg`, `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec` |
| `omegaPullbackCoeff_mulByInt_routeB` | `omegaPullbackCoeff_mulByInt_neg`, `omegaPullbackCoeff_mulByInt_pos` |
| `omegaPullbackCoeff_mulByInt_p_eq_zero_routeB` | `omegaPullbackCoeff_mulByInt_routeB` |
| `omegaPullbackCoeff_mulByInt_card_eq_zero` | `omegaPullbackCoeff_mulByInt_routeB` |

**Key API** (used by 3+ declarations in this file): `omegaPullbackCoeff_mulByInt_routeB` (used by `_mulByInt_pos` → `_mulByInt_routeB` → 2 endpoints, i.e., 3 internal dependents transitively; directly by `_p_eq_zero_routeB` and `_card_eq_zero`); `omegaPullbackCoeff_mulByInt_pos` and `omegaPullbackCoeff_mulByInt_neg` (used by `_routeB`).

**Declarations unused within this file** (dead-code candidates for this file; all used externally):
- `omegaPullbackCoeff_addIsog_id` — used by `GapQfKernel.lean`
- `omegaPullbackCoeff_addIsog_pair` — used by `GapSpines.lean`, `WeilPairing/PencilSeparable.lean`
- `omegaPullbackCoeff_mulByInt_succ` — private helper, all use is via `_ge_two`
- `omegaPullbackCoeff_mulByInt_ge_two` — all use via `_pos`
- `omegaPullbackCoeff_mulByInt_p_eq_zero_routeB` — used by `GapQfKernel.lean`
- `omegaPullbackCoeff_mulByInt_card_eq_zero` — potentially used externally

## Notes

No `set_option maxHeartbeats` in the file. No `sorry`. No instances or defs — pure theorems only. The file is the clean Route B assembly tying `SilvermanIV14` (RB-ω4) + `MulByIntAddRecurrence` (RB-ID) into the full `a_{[n]} = n` induction, bypassing the EDS Wronskian and formal group.
