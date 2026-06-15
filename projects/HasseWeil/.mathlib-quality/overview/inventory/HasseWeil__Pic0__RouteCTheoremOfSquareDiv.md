# Inventory: ./HasseWeil/Pic0/RouteCTheoremOfSquareDiv.lean

**Total declarations:** 8 (8 theorems, 0 defs, 0 instances)
**Sorries:** none
**`set_option maxHeartbeats`:** none
**Long proofs (>30 lines):** none

---

## Module structure

The file is split into two namespaces:
- `HasseWeil.Pic0.RouteCTheoremOfSquareDiv` (Parts A–C, lines 87–225 and 251–341)
- A large module-doc block (lines 227–249) for Part D

**Parts A–C** work over a generic `[Field F] [DecidableEq F]` elliptic `WeierstrassCurve.Affine F`.
**Part D** (lines 265–341) uses `{E : WeierstrassCurve.Affine F} [E.IsElliptic]` (with implicit `W`
replaced by `E`) and adds the `open HasseWeil`.

---

## Declaration Inventory

---

### `theorem kappaDivisor_add_linEquiv`

- **Type**: `(A B : W.Point) → SmoothPlaneCurve.ProjLinearlyEquiv ⟨W⟩ (Curves.kappaDivisor W (A + B)) (Curves.kappaDivisor W A + Curves.kappaDivisor W B)`
- **What**: Asserts that `κ(A+B) ∼ κ(A) + κ(B)` as projective divisors (linear equivalence); this is the divisor incarnation of Abel's theorem (Silverman III.3.5) specialised to the unconditional Miller hypothesis.
- **How**: One-liner plugging `Curves.miller_hypothesis_holds_allChar W` into `Curves.kappaDivisor_add_linEquiv_of_miller`.
- **Hypotheses**: `W` is an elliptic Weierstrass curve over a field `F` with `DecidableEq`.
- **Uses from project**: `Curves.kappaDivisor_add_linEquiv_of_miller`, `Curves.miller_hypothesis_holds_allChar`, `Curves.kappaDivisor`
- **Used by**: `tos_divisor` (within this file)
- **Visibility**: public
- **Lines**: 103–107, proof length ~1 line
- **Notes**: Clean wrapper; re-exports `Curves.kappaDivisor_add_linEquiv_of_miller` with the unconditional Miller instance plugged in.

---

### `theorem tos_divisor`

- **Type**: `{f g h : W.Point →+ W.Point} → (∀ Q, f Q = g Q + h Q) → (Q : W.Point) → SmoothPlaneCurve.ProjIsPrincipal ⟨W⟩ (Curves.kappaDivisor W (f Q) - Curves.kappaDivisor W (g Q) - Curves.kappaDivisor W (h Q))`
- **What**: The theorem of the square in divisor form (Silverman III.6.2(c)): whenever three point homomorphisms satisfy `f Q = g Q + h Q` for all `Q`, the difference divisor `κ(fQ) − κ(gQ) − κ(hQ)` is principal, char-free and unconditional.
- **How**: Rewrites with `hsum Q` to reduce to `kappaDivisor_add_linEquiv`, then uses `abel` to regroup the subtraction into the form `κ(fQ) − (κ(gQ) + κ(hQ))` that `ProjLinearlyEquiv` expects.
- **Hypotheses**: `W` elliptic, point homs `f, g, h` satisfying `f = g + h` pointwise.
- **Uses from project**: `kappaDivisor_add_linEquiv` (this file), `Curves.kappaDivisor`
- **Used by**: (unused within this file; exported to `RouteCAddFormula.lean`)
- **Visibility**: public
- **Lines**: 124–142, proof length ~18 lines
- **Notes**: No sorry, no maxHeartbeats. Proof is short but non-trivial: needs `abel` to align subtraction associativity.

---

### `theorem sigma_delta`

- **Type**: `{f g h : W.Point →+ W.Point} → (Q : W.Point) → Curves.projectiveDivisorSum W (Curves.kappaDivisor W (f Q) - Curves.kappaDivisor W (g Q) - Curves.kappaDivisor W (h Q)) = f Q - g Q - h Q`
- **What**: Computes `σ` (the `projectiveDivisorSum` section) of the theorem-of-the-square difference divisor: `σ(κ(fQ) − κ(gQ) − κ(hQ)) = fQ − gQ − hQ`, using the fact that `σ ∘ κ = id`.
- **How**: Three applications of `Curves.projectiveDivisorSum_sub` (additivity of σ) followed by three applications of `Curves.projectiveDivisorSum_kappaDivisor` (`σ(κ P) = P`).
- **Hypotheses**: None beyond `W` elliptic.
- **Uses from project**: `Curves.projectiveDivisorSum`, `Curves.kappaDivisor`, `Curves.projectiveDivisorSum_sub`, `Curves.projectiveDivisorSum_kappaDivisor`
- **Used by**: `sigma_delta_eq_zero_iff` (this file); also called directly in `RouteCAddFormula.lean`
- **Visibility**: public
- **Lines**: 155–163, proof length ~4 lines
- **Notes**: Clean; no sorry, no maxHeartbeats. Pure `rw`-chain.

---

### `theorem sigma_delta_eq_zero_iff`

- **Type**: `{f g h : W.Point →+ W.Point} → (Q : W.Point) → (Curves.projectiveDivisorSum W (...) = 0 ↔ f Q = g Q + h Q)`
- **What**: The reviewer's Q2 equivalence: the `σ` of the difference divisor vanishes if and only if the three point maps add at `Q`, i.e. `fQ = gQ + hQ`. This makes precise that "sums-to-O" is exactly the theorem-of-the-square content.
- **How**: Rewrites using `sigma_delta` then splits the iff: the forward direction solves `fQ − gQ − hQ = 0 ⟹ fQ = gQ + hQ` by `simpa`; the backward direction uses `abel` after `rw [hadd]`.
- **Hypotheses**: None beyond `W` elliptic.
- **Uses from project**: `sigma_delta` (this file)
- **Used by**: `picDual_add_iff_sigma_vanishes` (this file)
- **Visibility**: public
- **Lines**: 170–183, proof length ~13 lines
- **Notes**: No sorry, no maxHeartbeats.

---

### `theorem tos_toClass`

- **Type**: `{f g h : W.Point →+ W.Point} → (∀ Q, f Q = g Q + h Q) → (Q : W.Point) → WeierstrassCurve.Affine.Point.toClass (f Q) = WeierstrassCurve.Affine.Point.toClass (g Q) + WeierstrassCurve.Affine.Point.toClass (h Q)`
- **What**: The theorem of the square at the `ClassGroup` level: `toClass (fQ) = toClass(gQ) + toClass(hQ)` whenever `fQ = gQ + hQ`, by the `map_add` property of mathlib's `Point.toClass` `AddMonoidHom`.
- **How**: Rewrites with `hsum Q` then applies mathlib's `map_add` for the `AddMonoidHom` `Point.toClass`.
- **Hypotheses**: `f, g, h` point homs with `f = g + h` pointwise. The `omit [W.IsElliptic]` annotation means `W.IsElliptic` is not needed.
- **Uses from project**: `WeierstrassCurve.Affine.Point.toClass`
- **Used by**: (unused within this file)
- **Visibility**: public
- **Lines**: 202–208, proof length ~2 lines
- **Notes**: Uses `omit [W.IsElliptic]` — the statement does not need the elliptic hypothesis. No sorry, no maxHeartbeats.

---

### `theorem toClassEquiv'_add_iff`

- **Type**: `{f g h : W.Point →+ W.Point} → (Q : W.Point) → (toClassEquiv' (fQ) = toClassEquiv' (gQ) + toClassEquiv' (hQ) ↔ fQ = gQ + hQ)`
- **What**: The `κ = toClassEquiv'` additive isomorphism form of the theorem of the square: the `ClassGroup`-images add if and only if the points add, using injectivity of the `AddEquiv` `toClassEquiv'` to reduce back to the point level.
- **How**: Rewrites with `← map_add` (so the LHS becomes `toClassEquiv'(gQ + hQ) = toClassEquiv'(fQ)`) then applies `toClassEquiv'.injective.eq_iff` to conclude.
- **Hypotheses**: `W` Weierstrass curve (no `IsElliptic` needed on the left of the iff direction from `map_add`; injectivity of `toClassEquiv'` handles the right).
- **Uses from project**: `WeierstrassCurve.Affine.Point.toClassEquiv'`
- **Used by**: (unused within this file; bridges to `RouteCTheoremOfSquare.picDual_add_iff_classMap_mul` per doc)
- **Visibility**: public
- **Lines**: 216–223, proof length ~4 lines
- **Notes**: Uses `omit [W.IsElliptic]` (inherited from containing `variable` block without `omit`). No sorry, no maxHeartbeats.

---

### `theorem picDual_add_iff_pointwise`

- **Type**: Long signature with 9 hypotheses (`ch, hinj, hfin` triples for `α, α₁, α₂`): `(picDual α ... = picDual α₁ ... + picDual α₂ ...) ↔ (∀ Q, picDual α ... Q = picDual α₁ ... Q + picDual α₂ ... Q)`
- **What**: The `picDual` additivity `hadd` is equivalent to its pointwise form: equality of `AddMonoidHom`s iff they agree on every input. This pins the consumer's residual to the fibre-level statement.
- **How**: The iff holds by `ext` for `AddMonoidHom`s; both directions use `rfl` after the respective introduction.
- **Hypotheses**: Isogenies `α, α₁, α₂ : Isogeny E E`, each with a `CoordHom` (with injectivity and finiteness witnesses).
- **Uses from project**: `Isogeny.picDual`
- **Used by**: `picDual_add_iff_sigma_vanishes` (this file)
- **Visibility**: public
- **Lines**: 265–278, proof length ~3 lines
- **Notes**: No sorry, no maxHeartbeats. Pure propositional unfolding; both directions are `rfl`-trivial.

---

### `theorem htrace_dual_of_picDual_add`

- **Type**: Long signature; given `α, α₁, α₂ : Isogeny E E` with `CoordHom`s, `r s t : ℤ`, `hbeta`, `hsum`, `hdual₁`, `hdual₂`, `hadd` → `α.toAddMonoidHom + α.picDual ... = (mulByInt E (r * t - 2 * s)).toAddMonoidHom`
- **What**: Given the single additivity residual `hadd` (`picDual α = picDual α₁ + picDual α₂`) together with the two non-circular seeds `picDual α₁ = r·V` and `picDual α₂ = −s·id` and the Frobenius trace shape, produces the III.8 relation `α + α̂ = [r·t − 2s]` that the geometric degree consumer needs.
- **How**: Direct delegation to `RouteCAdditivity.htrace_dual_of_picDual_additive` — pure forwarding with all arguments threaded through.
- **Hypotheses**: Three isogenies with CoordHom data, integers `r s t`, shape hypotheses `hbeta` and `hsum`, dual-seed hypotheses `hdual₁, hdual₂`, and the single residual `hadd`.
- **Uses from project**: `RouteCAdditivity.htrace_dual_of_picDual_additive`, `Isogeny.picDual`, `mulByInt`
- **Used by**: (unused within this file; called in `RouteCAddFormula.lean`)
- **Visibility**: public
- **Lines**: 321–339, proof length ~1 line (single delegation call on line 338–339)
- **Notes**: No sorry, no maxHeartbeats. This is a pure forwarding wrapper that makes the interface available in the `RouteCTheoremOfSquareDiv` namespace.

---

### `theorem picDual_add_iff_sigma_vanishes`

- **Type**: Long signature with 9 CoordHom-triple hypotheses: `(picDual α ... = picDual α₁ ... + picDual α₂ ...) ↔ (∀ Q, projectiveDivisorSum E (κ(picDual α ... Q) − κ(picDual α₁ ... Q) − κ(picDual α₂ ... Q)) = 0)`
- **What**: The consumer's additivity residual `hadd` is equivalent to the statement that for every `Q` the difference divisor of dual images has vanishing `σ` — precisely the "pulled-back theorem-of-the-square divisor sums to O" content the reviewer described (Q2 equivalence).
- **How**: Rewrites via `picDual_add_iff_pointwise` to reduce to a pointwise statement, then applies `sigma_delta_eq_zero_iff` (using `forall_congr'`) to replace point-equality by σ-vanishing.
- **Hypotheses**: Three isogenies with CoordHom triples.
- **Uses from project**: `picDual_add_iff_pointwise` (this file), `sigma_delta_eq_zero_iff` (this file), `Curves.projectiveDivisorSum`, `Curves.kappaDivisor`, `Isogeny.picDual`
- **Used by**: (unused within this file; exported as a characterisation)
- **Visibility**: public
- **Lines**: 287–305, proof length ~5 lines
- **Notes**: No sorry, no maxHeartbeats.

---

## Cross-reference summary (internal)

| Caller | Calls |
|--------|-------|
| `tos_divisor` | `kappaDivisor_add_linEquiv` |
| `sigma_delta_eq_zero_iff` | `sigma_delta` |
| `picDual_add_iff_sigma_vanishes` | `picDual_add_iff_pointwise`, `sigma_delta_eq_zero_iff` |
| `htrace_dual_of_picDual_add` | (none in this file; delegates to `RouteCAdditivity`) |

**Key API** (used by 3+ other declarations in file): none — no declaration is referenced by 3 or more other declarations within this file. (`sigma_delta` and `kappaDivisor_add_linEquiv` are each used by exactly 1 other internal declaration; `sigma_delta_eq_zero_iff` and `picDual_add_iff_pointwise` each by 1.)

---

## Unused declarations (within this file)

The following declarations are not referenced by any other declaration *in this file* (they may be used by other project files):

- `tos_divisor` — used in `RouteCAddFormula.lean`
- `sigma_delta` — used in `RouteCAddFormula.lean`
- `tos_toClass` — not referenced in any located file (dead code candidate, or bridging future use)
- `toClassEquiv'_add_iff` — not referenced in any located file (dead code candidate)
- `picDual_add_iff_sigma_vanishes` — not referenced by other declarations in this file; may be used externally
- `htrace_dual_of_picDual_add` — used in `RouteCAddFormula.lean`
- `picDual_add_iff_pointwise` — used only by `picDual_add_iff_sigma_vanishes` within this file

---

## Notes

This file is an entirely clean, sorry-free, axiom-clean bridge file (8 theorems, no defs or instances, no `maxHeartbeats` overrides). It provides the divisor-level theorem of the square for the Route C pipeline, moving off the ideal-extension wall from `RouteCTheoremOfSquare.lean`. The `tos_toClass` and `toClassEquiv'_add_iff` declarations (Part C) appear to be unused outside the file and are possible dead-code candidates, though they serve as documented mathematical statements.
