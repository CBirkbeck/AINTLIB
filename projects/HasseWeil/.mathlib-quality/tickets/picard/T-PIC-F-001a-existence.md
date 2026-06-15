# T-PIC-F-001a: Existence — every D ∈ Div⁰(E) is equivalent to (P) − (O)

**Status**: DONE (`exists_kappa_form` in `HasseWeil/Curves/Miller.lean`,
axiom-clean — uses `picZeroIsoE` to express every Pic⁰ element as
`kappaDivisor`-class of a point)
**Silverman**: III.3.4(a) (existence direction)
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~120
**Difficulty**: medium
**Phase**: F (existence direction — INDEPENDENT of worker-K)

## Depends on

- T-PIC-A-002a (general line case) — provides the chord-tangent identity
  at divisor level
- T-PIC-A-002b (vertical line case, DONE) — provides the inverse-pair
  identity at divisor level
- T-PIC-A-001 (DONE) — `projectiveDivisorSum`

## Blocks

- T-PIC-F-001c (assembly)

## Statement

```lean
theorem exists_kappa_form
    [W.IsElliptic]
    (D : ProjectiveDivisor.degZero (⟨W⟩ : SmoothPlaneCurve F)) :
    ∃ P : W.Point,
      D.val ~_div (kappaDivisor W P)
```

(Equivalent: every degree-zero divisor is **linearly equivalent** to
`(P) - (O)` for some `P ∈ E`, and that `P` is exactly `σ(D)`.)

## Mathematical content (no Riemann-Roch!)

Standard inductive proof (Silverman III.3.4(a) without R-R):

Induction on `|D.val.support|` (number of distinct points in support).

**Base**: `D = 0`. Take `P = O`; then `(O) - (O) = 0 ~ 0`.

**Single-point**: `D = (Q) - (O)`. Take `P = Q`; trivial.

**Step (general)**: D has at least two distinct support points. Pick
two: P₁ with multiplicity n₁ ≠ 0, P₂ with multiplicity n₂ ≠ 0.

Use the **chord-line identity** (T-PIC-A-002a): line `L` through P₁ and
P₂ meets E at a third point `R`, and:

```
(P₁) + (P₂) + (R) - 3·(O) = div(L) ~ 0
⟹ (P₁) + (P₂) ~ (-(R)) + (O)    -- since R = -(P₁ + P₂) by group law
                              -- and (R) - (O) ~ -((-R) - (O)) trivially
                              -- hmm, need to think more carefully
```

Cleaner statement: `(P₁) + (P₂) - (P₁ + P₂) - (O) = div(L · L'⁻¹) ~ 0`
where L is the line through P₁, P₂ and L' is the vertical line at
x-coordinate of `P₁ + P₂` — this combination is the standard
"chord then negate" sequence used to define `Point.add`.

So `(P₁) + (P₂) ~ (P₁ + P₂) + (O)`, which **reduces the support size by 1**
(P₁ and P₂ collapse into P₁ + P₂).

Iterate until D has ≤ 1 support point, then apply base/single-point case.

The final `P` extracted is `Σ nᵢ Pᵢ` in the group — exactly `σ(D)`.

## Naming

`exists_kappa_form` or `exists_kappaDivisor_equivDiv`.

## Generality

`[W.IsElliptic]`. **No `[IsAlgClosed F]` required for this piece** — the
existence is purely formal once we have the chord identity. (The
algebraic-closure hypothesis enters via A-002a's full coverage of
arbitrary lines, but the inductive step only uses lines through F-rational
points.)

## Proof approach

```lean
theorem exists_kappa_form D := by
  induction h : D.val.support.card with
  | zero =>
      -- D = 0
      use 0
      simp [...]
  | succ n ih =>
      by_cases h_single : D.val.support.card = 1
      · -- D = c·(P) - c·(O) for some single P, c
        obtain ⟨P, hP⟩ := ...
        use n_factor • P
        ...
      · -- D has ≥ 2 distinct support points
        obtain ⟨P₁, P₂, hne, h₁, h₂⟩ := ...
        -- Chord-line identity reduces D to D' with smaller support
        have h_chord : (single P₁ 1 + single P₂ 1 : Divisor) ~_div
                       (single (P₁ + P₂) 1 + single 0 1) := by
          exact divisorIdentity_chord P₁ P₂  -- from A-002a
        have h_smaller : D.val ~_div (D.val - chord_correction) := ...
        have h_smaller_support : ... .support.card = n := ...
        exact ih (D.val - chord_correction) h_smaller_support
```

Estimated:
- Base + single-point: ~30 LOC.
- Inductive step: ~60 LOC (chord-line bookkeeping is fiddly).
- Helper lemmas (divisor arithmetic with `kappaDivisor`): ~30 LOC.

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.exists_kappa_form
```
reports only standard axioms.

## Risks

- The "chord correction" subtraction at divisor level needs careful
  bookkeeping with `Finsupp.single` arithmetic. May need 30-50 LOC of
  helper lemmas.

- The single-point case `D = c·(P) - c·(O)` for `c : ℤ` needs to invoke
  the **integer scalar multiplication** in E (`MulByInt`), which exists
  in `EC/MulByIntBaseCase.lean` etc. but the bridge to divisor level may
  need ~20 LOC.

- **No worker-K dependency.** This piece is fully shippable in
  parallel with anything worker-K is doing.

## Progress log
