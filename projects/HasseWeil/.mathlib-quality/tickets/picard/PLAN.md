# Pic⁰ Route to Universal Silverman III.4.8

## Goal

Discharge the universal `AddHomProperty` for the new `Isogeny.AG` structure
(in `HasseWeil/EC/IsogenyAG.lean`):

```lean
theorem AddHomProperty_universal :
    ∀ {F : Type*} [Field F] [DecidableEq F]
      {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
      (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom),
      φ.AddHomProperty cd
```

via Silverman's actual proof (textbook page 71, **3-line argument**):

> An isogeny `φ : E₁ → E₂` is finite, so by II.3.7 it induces a homomorphism
> `φ_∗ : Pic⁰(E₁) → Pic⁰(E₂)`. The canonical map `κ_i : E_i → Pic⁰(E_i)`
> (Silverman III.3.4) is a group iso, and the diagram commutes since
> `φ(O) = O`. Hence `φ` is a hom on points.

## References

- **Silverman III.4.8** (page 71): the theorem.
- **Silverman III.3.4**: `σ : Pic⁰(E) ≅ E` group iso (with inverse `κ`).
- **Silverman II.3.7** (referenced from III.4.8 proof): pushforward of
  divisors under finite morphisms is well-defined as a group hom on Div⁰.
- **Silverman II.5.5(c)** (Riemann-Roch corollary): for genus 1,
  `dim L(D + (O)) = 1` when `deg D = 0`. **AVOIDED** in this project — we
  use the geometric group law directly.
- **Project ticket T-III-3-003** (P) ~ (Q) ⇒ P = Q — checked-out by
  worker-K, gives σ injectivity.
- **Project ticket T-III-3-004** Pic⁰(E) ≅ E — depends on T-III-3-003.

## Existing Infrastructure (~65% there)

**DONE in `HasseWeil/Curves/`:**
- `Divisors.lean`: `Divisor C`, `degree`, `Div⁰`, `divisorOf`,
  `IsPrincipal`, `~`, `Pic`, `Pic⁰` (T-II-3-001..007 all DONE).
- `ProjectiveDivisor.lean`: `ProjectiveDivisor C` (handles point at
  infinity), `projectiveDivisorOf`, projective versions of degree, Div⁰,
  principal, `~`, `PicProj`, `PicProj₀` (T-II-3-001b DONE).
- `NormValuation.lean`: smooth point ↔ maximal ideal bridge, including
  `smoothPointEquivMaxIdeal` (~20 axiom-clean lemmas).
- `EC/IsogenyAG.lean`: the new `Isogeny.AG` structure, `AddHomProperty`
  predicate, `WithHom` bundle, all closure operations (id, compose,
  frobenius).

**OPEN / IN-FLIGHT:**
- `T-II-3-008` (PARTIAL): `div(f) = 0 ⟺ f ∈ K̄*`.
- `T-II-3-009` (CHECKED-OUT, worker-K): `deg(projectiveDivisorOf f) = 0`.
- `T-III-3-003` (CHECKED-OUT, worker-K): (P) ~ (Q) ⇒ P = Q.
- `T-III-3-004` (OPEN): the Pic⁰ ≅ E iso itself.

## Mathlib Inventory

| Concept | Mathlib | Our action |
|---|---|---|
| Picard group of modules | `Mathlib.RingTheory.PicardGroup` (CommRing.Pic) | NOT applicable — that's for modules over rings |
| Class group | `Mathlib.RingTheory.ClassGroup` (Dedekind domains) | Different perspective; cite when explaining |
| Curves divisors / Pic⁰ | **NOT in mathlib** | Use this project's `Curves/Divisors.lean` |
| Riemann-Roch | **NOT in mathlib** for curves | AVOID — use group-law route |
| Curve morphism pushforward | **NOT in mathlib** | DEFINE here as `pushforwardDivisor` |

## File Structure

Three new files (won't disturb other workers):

```
HasseWeil/Curves/PicZero.lean              (Phases A, B — σ, κ definitions + group structure)
HasseWeil/Curves/PicZeroPushforward.lean   (Phase C — isogeny pushforward on Pic⁰)
HasseWeil/EC/IsogenyAG/HomProperty.lean    (Phases D, E, F — diagram commute + III.4.8 closure)
```

## Dependency Graph

```
T-PIC-A-001 (σ on Div⁰)  ─┬→ T-PIC-A-002 (σ vanishes on principal) → T-PIC-A-003 (σ̄ on Pic⁰)
                          │                                            │
                          │                                            ↓
                          │                                       T-PIC-A-004 (σ̄ is group hom)
                          │                                            │
                          ↓                                            ↓
T-PIC-B-001 (κ : E → Pic⁰) ────→ T-PIC-B-002 (κ_zero) ────→ T-PIC-B-003 (σ̄ ∘ κ = id)

T-PIC-C-001 (pushforwardDiv) → T-PIC-C-002 (preserves deg)
                            ↓
                    T-PIC-C-003 (preserves principal: φ_*(div g) = div N(g))
                            ↓
                    T-PIC-C-004 (φ_∗ on Pic⁰ as group hom)

(A-003 + A-004 + B-003 + C-004) → T-PIC-D-001 (diagram commute) → T-PIC-E-001 (witness-parametric ∀)

worker-K's T-III-3-003 ─────→ T-PIC-F-001 (κ ∘ σ̄ = id)
                                        │
T-PIC-A-004 + T-PIC-B-003 + F-001 ──→ T-PIC-F-002 (σ̄ ≅ E packaged as MulEquiv)
                                        │
T-PIC-E-001 + F-002 ───────────→ T-PIC-F-003 (B-4-003 closure: ∀ φ cd, AddHomProperty)
```

## Generality Decisions

- **Affine vs projective.** Use `ProjectiveDivisor` throughout — Silverman
  III.3.4 fundamentally needs the point at infinity in `Div⁰`. Our
  `Curves/ProjectiveDivisor.lean` already handles this.
- **Algebraic-closure hypothesis.** Silverman states III.3.4 over `K̄`. We
  parametrize by an arbitrary `[Field F]`; the IsAlgClosed hypothesis only
  becomes required when bridging to T-III-3-003 (which has it). Phases A
  through E carry their own hypotheses minimally.
- **Coord-ring witness.** All `Isogeny.AG` machinery is parametrized by an
  external `coordHom : φ.toCurveMap.CoordHom`. The Pic⁰ pushforward
  requires this witness too (to define the point map).

## Phases

### Phase A — σ : ProjectiveDiv⁰(E) → E

Define the sum-of-points map and its basic API.

### Phase B — κ : E → Pic⁰(E)

The inverse direction in Silverman III.3.4(d).

### Phase C — Pushforward on Pic⁰

Define `Isogeny.AG → (Pic⁰(E₁) → Pic⁰(E₂))`. Three sub-tickets:
divisor-level pushforward, degree preservation, principal preservation
(the `div(N(g))` = `φ_*(div g)` identity for the algebra norm).

### Phase D — Diagram Commute

`κ_E₂ ∘ φ_pt = φ_∗ ∘ κ_E₁`. Trivial once we have the structural pieces
(uses only the basepoint preservation `φ(O) = O`).

### Phase E — Witness-parametric Universal Theorem

`AddHomProperty_of_picZero_iso`: takes the σ̄ iso for both curves as
explicit arguments, derives the universal AddHomProperty.

### Phase F — Discharge via worker-K

When T-III-3-003 lands, construct the σ̄ iso and apply E to get the
unconditional B-4-003.

## Estimated Scope

| Phase | Tickets | Lines | Independent of worker-K? |
|---|---|---|---|
| A | 4 | ~250 | yes |
| B | 3 | ~120 | yes |
| C | 4 | ~340 | yes |
| D | 1 | ~30 | yes |
| E | 1 | ~40 | yes |
| F | 3 | ~70 | NO — needs worker-K |
| **Total** | **16** | **~850** | **600 lines parallelizable** |

## Risks

- **T-III-3-003 stalls.** Worker-K's hardest ticket. Mitigated by
  E-001 (witness-parametric path) — 600 lines deliver concrete value
  even if F never lands.
- **Pushforward preserves principal (T-PIC-C-003).** The `φ_*(div g) =
  div(N(g))` identity is "standard" but mathlib infra is thin. May
  need ~150 lines on its own.
- **Projective divisor bookkeeping.** `ProjectiveDivisor` includes the
  point at infinity explicitly; we have to be careful about which parts
  of computations live in the affine vs projective view.
