# T-III-6-001: Dual isogeny exists and is unique

**Status**: OPEN (existing axiomatic — refactor)
**Silverman**: III.6.1(a)
**Module**: `HasseWeil/DualIsogeny.lean` → `HasseWeil/EC/DualIsogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 100
**Difficulty**: hard (CRITICAL)
**Stream**: C

## Depends on
- T-III-4-016 (factorization)
- T-III-4-017 (quotient curve)

## Blocks
- T-III-6-002..010

## Statement (Silverman III.6.1(a))
For every nonzero isogeny `φ : E₁ → E₂` of degree `m`, there exists a unique
isogeny `φ̂ : E₂ → E₁`, called the **dual isogeny** of `φ`, such that
`φ̂ ∘ φ = [m]`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The dual isogeny of φ.
    Reference: Silverman III.6.1(a). -/
def Isogeny.dual (φ : Isogeny E₁ E₂) : Isogeny E₂ E₁

/-- Uniqueness of the dual. -/
theorem Isogeny.dual_unique (φ : Isogeny E₁ E₂) (hφ : φ ≠ 0)
    (ψ : Isogeny E₂ E₁) (h : ψ.comp φ = E₁.mulByInt φ.degree) :
    ψ = φ.dual

end HasseWeil.EC
```

## Notes
- Construction (Silverman III.6.1(b)):
  1. `[m] : E₁ → E₁` factors through `E₁/ker [m]`.
  2. Since `ker φ ⊂ E₁[m] = ker [m]`, by T-III-4-016, `[m]` factors as
     `[m] = (something) ∘ φ` provided `φ` is separable.
  3. For inseparable case: write `φ = φ_sep ∘ Frob^e` (T-II-2-016) and dualize
     each piece separately.
  4. Or use the `Pic⁰` construction: `φ̂ = κ_{E₁} ∘ φ_* ∘ κ_{E₂}^{-1}` where
     `κ` is the isomorphism `Pic⁰ ≅ E` (T-III-3-004).
- The current `HasseWeil/DualIsogeny.lean` has a SORRY for the construction;
  this ticket is the proper construction.

## Detailed Silverman proof (III.6.1)

Silverman III.6.1(a) proves existence of the dual via the factorization
theorem III.4.16 + quotient curve III.4.17:

**Case 1: φ separable.** Then ker φ is a finite subgroup G ⊂ E₁[m]. By III.4.17
the quotient E₁/G exists as an elliptic curve isogenous to E₁ via `[m]_G : E₁/G ≅ E₂`
(since G = ker φ and both φ and [m] map onto `E₁` at the appropriate index).
The dual is defined by:
```
φ̂ := [m]_G ∘ π : E₂ → E₂ → E₁
```
where π : E₂ → E₁/G ≅ E₂ is the projection.

More concretely: since `ker φ ⊂ ker [m]` (as [m] kills all m-torsion), III.4.16
gives a unique isogeny ψ : E₂ → E₁ such that ψ ∘ φ = [m]. Set φ̂ := ψ.

**Case 2: φ purely inseparable.** Write φ = Frob^e (by III.4.13 + III.4.14).
Then deg φ = p^e and φ̂ := p_Frob^e (the "Verschiebung") — or equivalently,
φ̂ is the Frobenius on the dual side.

**Case 3: general φ.** Decompose φ = φ_sep ∘ Frob^e (T-II-2-016) and dualize:
```
φ̂ = Frob^e^ ∘ φ_sep^ : E₂ → E₁^(p^e) → E₁
```
with appropriate Verschiebung handling.

**Uniqueness**: if ψ₁ ∘ φ = [m] = ψ₂ ∘ φ and φ is surjective (nonzero isogeny),
then ψ₁ and ψ₂ agree on image of φ = E₂, hence equal.

## Proof dependencies (Silverman chain)

- **III.4.16** (factorization through quotient): if ker φ ⊂ ker ψ, then ψ factors.
- **III.4.17** (quotient curve): E/G exists as EC for any finite subgroup G ⊂ E.
- **III.4.15** (separable ⇒ #ker = deg): tight degree count.
- **T-III-4-015** (sep ⇒ #ker = deg) — **not yet done**.
- **T-III-4-016** (factorization) — **not yet done**.
- **T-III-4-017** (quotient curve) — **not yet done**.

## Alternative route: Pic⁰ correspondence (Silverman III.3.4)

Much shorter: given κ : Pic⁰(E) ≅ E (T-III-3-004), an isogeny φ : E₁ → E₂
induces φ_* : Pic⁰(E₁) → Pic⁰(E₂) (push-forward of divisors). Then:
```
φ̂ := κ_{E₁} ∘ φ_* ∘ κ_{E₂}^{-1} : E₂ → Pic⁰(E₂) → Pic⁰(E₁) → E₁.
```
Uniqueness and the functional equation `φ̂ ∘ φ = [deg φ]` follow from
functoriality of Pic⁰ and III.3.4. This uses T-III-3-004 which is also not done.

## Recommendation for future worker

**Do not attempt the direct construction** (III.4.15-17) for this ticket until
either (a) those tickets are done or (b) the Pic⁰ route is built. Both are
substantial (weeks of work each).

## Structural obstruction analysis (2026-04-20)

After close inspection, the `exists_dual` sorry cannot be reduced to a
smaller sorry without one of the two heavy dependency routes. Specifically:

**Attempt**: split `exists_dual` into `exists_dual_raw` (existence) +
`unique_dual` (uniqueness-from-composition-identity).

**Uniqueness half** (`β ∘ α = γ ∘ α ∧ α ∘ β = α ∘ γ → β = γ`):
- **Pullback equality** (`β.pullback = γ.pullback`): ✅ provable via
  `Isogeny.pullback_injective` + left cancellation on `α.pullback`. ~5 lines.
- **toAddMonoidHom equality** (`β.toAddMonoidHom = γ.toAddMonoidHom`):
  BLOCKED. Requires either
  (a) `α.toAddMonoidHom` surjective on F-points — **fails** (F may not be
      algebraically closed; isogenies are only surjective on K̄-points), or
  (b) `Isogeny.pullback` determines `Isogeny.toAddMonoidHom` — the **Pic⁰
      correspondence** (T-III-3-004), the key missing lemma.

So both halves of `exists_dual` are genuinely hard. The Isogeny structure
in `Basic.lean:63` carries both pullback AND toAddMonoidHom as INDEPENDENT
data — this is a deliberate design choice because the project hasn't
built the algebraic geometry needed to derive one from the other.

## Single-session tractability: ❌

This ticket is NOT achievable in a single session. The minimum path is:

**Route A (direct, via quotient curves)**: T-III-4-012 → T-III-4-013 →
T-III-4-014 → T-III-4-015 → T-III-4-016 → T-III-4-017 → T-III-6-001.
Estimated 1500-2500 lines across ~2-3 months.

**Route B (via Pic⁰)**: T-II-3-007 (Pic⁰ functoriality) → T-III-3-003
(P ~ Q ⇒ P = Q) → T-III-3-004 (Pic⁰ ≅ E) → T-III-6-001. Estimated
600-1000 lines across ~4-6 weeks.

Route B is faster but still multi-week.

## Recommendation (updated 2026-04-20)

Do not attempt T-III-6-001 closure in single sessions. Instead:
- Audit downstream tickets that cascade sorry from here — confirm
  they're content-complete (so they "auto-close" when T-III-6-001 closes).
- Focus on tickets OUTSIDE the dual-isogeny subtree (e.g., Hasse bound
  via T-V-1 chain, or formal group / Weil pairing directions).
- When starting T-III-6-001: pick Route B, budget 4-6 weeks minimum.

## Progress log

- 2026-04-20 [worker-A] Detailed obstruction analysis: tried to split
  `exists_dual` into `exists_dual_raw` + `unique_dual`. Found that even
  uniqueness CANNOT be cleanly split off without Pic⁰ (T-III-3-004) or
  equivalent machinery, because `Isogeny`'s structure carries pullback
  and toAddMonoidHom as independent data (by design choice in
  `Basic.lean:63` — the AG to derive one from the other hasn't been
  built). Updated ticket with concrete dependency routes + realistic
  session budgets. Status remains OPEN.
