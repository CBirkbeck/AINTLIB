# Inventory: ./HasseWeil/FormalGroup/Height.lean

**File summary**: 151 lines. Defines the height of a formal group homomorphism and of a formal group (Silverman IV.7), and proves that height is additive under composition. No sorries.

---

### `noncomputable def FormalGroupHom.height`
- **Type**: `{F G : FormalGroup R} → (p : ℕ) → FormalGroupHom F G → ℕ∞`
- **What**: The height of a formal group homomorphism `f : F → G` over a ring of prime characteristic `p`. Defined as `f.toSeries.order.map (padicValNat p)`, which is `⊤` when `f.toSeries = 0` and equals the p-adic valuation of the order otherwise.
- **How**: Direct definition using `PartialOrder.ENat.map` and `padicValNat`. No proof content.
- **Hypotheses**: `R` is a commutative ring; `p : ℕ`.
- **Uses from project**: `FormalGroupHom.toSeries` (via `FormalGroup.Hom`).
- **Used by**: `FormalGroupHom.height_zero_toSeries`, `FormalGroupHom.height_of_ne_zero`, `FormalGroup.height`, `FormalGroupHom.height_comp`.
- **Visibility**: public
- **Lines**: 55–57 (noncomputable def, 3 lines)
- **Notes**: None.

---

### `@[simp] theorem FormalGroupHom.height_zero_toSeries`
- **Type**: `{F G : FormalGroup R} → (p : ℕ) → (f : FormalGroupHom F G) → f.toSeries = 0 → f.height p = ⊤`
- **What**: The height of a formal group homomorphism whose underlying power series is zero equals `⊤`.
- **How**: Rewrites with `PowerSeries.order_zero` (mathlib) and the definition of height; the `map` on `⊤` reduces to `⊤` by `rfl`.
- **Hypotheses**: `f.toSeries = 0`.
- **Uses from project**: `FormalGroupHom.height`.
- **Used by**: Unused in file (dead-code candidate; may be used by other files).
- **Visibility**: public
- **Lines**: 61–64 (proof 2 lines)
- **Notes**: `@[simp]` tagged. Not referenced elsewhere in this file.

---

### `theorem FormalGroupHom.height_of_ne_zero`
- **Type**: `{F G : FormalGroup R} → (p : ℕ) → (f : FormalGroupHom F G) → f.toSeries ≠ 0 → f.height p = padicValNat p f.toSeries.order.toNat`
- **What**: When the underlying series is nonzero, the height equals the p-adic valuation of the order (as a natural number), unwrapping the `WithTop.map` form of the definition.
- **How**: Rewrites with `PowerSeries.coe_toNat_order` (mathlib) to convert `order.map` to `padicValNat` of `order.toNat`, then closes by `rfl`.
- **Hypotheses**: `f.toSeries ≠ 0`.
- **Uses from project**: `FormalGroupHom.height`.
- **Used by**: Unused in file (dead-code candidate; may be used by other files).
- **Visibility**: public
- **Lines**: 68–73 (proof 3 lines)
- **Notes**: Not referenced elsewhere in this file.

---

### `noncomputable def FormalGroup.height`
- **Type**: `(F : FormalGroup R) → (p : ℕ) → ℕ∞`
- **What**: The height of a formal group `F` over a ring of prime characteristic `p`, defined as the height of the multiplication-by-`p` endomorphism `[p] : F → F`.
- **How**: Direct definition via `FormalGroupHom.height` applied to `F.mulByNatHom p`.
- **Hypotheses**: `R` is a commutative ring; `p : ℕ`.
- **Uses from project**: `FormalGroup.mulByNatHom` (from `FormalGroup.MulByNat`), `FormalGroupHom.height`.
- **Used by**: `FormalGroup.height_eq`.
- **Visibility**: public
- **Lines**: 79–80 (noncomputable def, 2 lines)
- **Notes**: None.

---

### `theorem FormalGroup.height_eq`
- **Type**: `(F : FormalGroup R) → (p : ℕ) → F.height p = (F.mulByNatHom p).height p`
- **What**: States that `FormalGroup.height` unfolds to `FormalGroupHom.height` applied to `mulByNatHom`; purely a definitional unfolding lemma.
- **How**: `rfl` — the two sides are definitionally equal.
- **Hypotheses**: None beyond the variable declarations.
- **Uses from project**: `FormalGroup.height`, `FormalGroup.mulByNatHom`, `FormalGroupHom.height`.
- **Used by**: Unused in file (dead-code candidate).
- **Visibility**: public
- **Lines**: 83–85 (proof 1 line)
- **Notes**: Purely a `rfl` unfolding; not referenced elsewhere in this file.

---

### `private theorem ENat.map_padicValNat_mul`
- **Type**: `(p : ℕ) → [Fact p.Prime] → {a b : ℕ∞} → a ≠ 0 → b ≠ 0 → (a * b).map (padicValNat p) = a.map (padicValNat p) + b.map (padicValNat p)`
- **What**: The function `ENat.map (padicValNat p)` converts multiplication in `ℕ∞` to addition, when both factors are nonzero and `p` is prime. This is the `ℕ∞` analogue of `padicValNat p (m * n) = padicValNat p m + padicValNat p n`.
- **How**: Case-splits on whether `a` and `b` are `⊤` or finite. In the `⊤` cases uses `ENat.top_mul` / `ENat.mul_top` (mathlib). In the finite case, applies `padicValNat.mul` (mathlib) after extracting the nonzero witnesses, then uses `push_cast` to match the cast arithmetic.
- **Hypotheses**: `p` prime (via `Fact p.Prime`); `a ≠ 0` and `b ≠ 0` in `ℕ∞`.
- **Uses from project**: None (purely mathlib + stdlib).
- **Used by**: `FormalGroupHom.height_comp`.
- **Visibility**: private
- **Lines**: 97–121 (proof 22 lines)
- **Notes**: Private helper. Proof is 22 lines — the case split on `ℕ∞` shapes is standard but requires careful use of `ENat.top_mul`/`mul_top` and `padicValNat.mul`.

---

### `theorem FormalGroupHom.height_comp`
- **Type**: `{F G H : FormalGroup R} → [NoZeroDivisors R] → (p : ℕ) → [Fact p.Prime] → (g : FormalGroupHom G H) → (f : FormalGroupHom F G) → (g.comp f).height p = f.height p + g.height p`
- **What**: Silverman IV.7 (selected part): the height of a composition of formal group homomorphisms is the sum of the heights, i.e., height is additive under composition.
- **How**: Unfolds height to `order.map (padicValNat p)`, rewrites with `FormalGroupHom.comp_toSeries` (project, Hom.lean) and `PowerSeries.order_subst` (project, OrderSubst.lean) to get `(g.toSeries.order * f.toSeries.order).map (padicValNat p)`, then applies `ENat.map_padicValNat_mul` (using `PowerSeries.order_ne_zero_iff_constCoeff_eq_zero` and `FormalGroupHom.zero_const` to discharge nonzero conditions), and closes with `add_comm`.
- **Hypotheses**: `R` has no zero divisors (needed for `PowerSeries.order_subst`); `p` is prime.
- **Uses from project**: `FormalGroupHom.height`, `FormalGroupHom.comp_toSeries` (Hom.lean), `FormalGroupHom.zero_const` (Hom.lean), `PowerSeries.order_subst` (OrderSubst.lean), `ENat.map_padicValNat_mul` (this file).
- **Used by**: Unused in file (may be used by importers).
- **Visibility**: public
- **Lines**: 131–148 (proof 15 lines)
- **Notes**: The main mathematical result of the file. Proof is 15 lines.

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `FormalGroupHom.height` | `height_zero_toSeries`, `height_of_ne_zero`, `FormalGroup.height`, `height_comp` |
| `FormalGroupHom.height_zero_toSeries` | unused in file |
| `FormalGroupHom.height_of_ne_zero` | unused in file |
| `FormalGroup.height` | `height_eq` |
| `FormalGroup.height_eq` | unused in file |
| `ENat.map_padicValNat_mul` | `height_comp` |
| `FormalGroupHom.height_comp` | unused in file |

**Key API** (used by 3+ others in file): `FormalGroupHom.height` (used by 4 declarations).

**Unused in file** (dead-code candidates — may be used by importers): `height_zero_toSeries`, `height_of_ne_zero`, `FormalGroup.height_eq`, `FormalGroupHom.height_comp`.

**No sorries. No `set_option maxHeartbeats`. No long proofs (>30 lines).** The file is only imported by `HasseWeil.lean` (the top-level barrel) and no individual module imports it, so all public declarations are potentially dead code from within the subproject's internal graph; they are API leaves.
