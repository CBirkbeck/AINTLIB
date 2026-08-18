# /mathlibable report — `LutzNagell.LutzNagellTheorem.curveQ_a₁`

**Verdict: NO-mathlib-has-it**

---

## 0. Declaration resolution

- Parsed/claimed name: `LutzNagell.LutzNagellTheorem.curveQ_a₁` — ✓ **VERIFIED** against source.
- Location: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralCurve.lean:27`
- Namespace: `LutzNagell.LutzNagellTheorem`, inside `open WeierstrassCurve`, with `variable (W : WeierstrassCurve ℤ)`.

Source statement (`GeneralCurve.lean:23-27`):

```lean
/-- The base change of `W` to `ℚ`. -/
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)

@[simp] lemma curveQ_a₁ : (curveQ W).a₁ = (W.a₁ : ℚ) := by simp [curveQ]
```

`curveQ` is a plain `abbrev` (definitionally `W.map (algebraMap ℤ ℚ)`); it is **not** a new structure or
opaque def. So `curveQ_a₁` says: the `a₁` coefficient of the base change of an integral Weierstrass
curve `W` to `ℚ` equals the integer `W.a₁` viewed in `ℚ`. It is one of five companion `@[simp]`
read-off lemmas `curveQ_a₁ … curveQ_a₆` (lines 27–31), each with the identical proof `by simp [curveQ]`.

---

## 1. Mathematical content

This is a coefficient-functoriality fact: base change of a Weierstrass curve along a ring homomorphism
acts coefficient-wise, and along `ℤ → ℚ` the map on each integer coefficient is the canonical integer
cast. It is a definitional unfolding, not a theorem with mathematical depth.

---

## 2. Literature search

Not a named theorem; no literature sweep warranted (small, mechanical decl). The "standard form" is
simply functoriality of the Weierstrass-coefficient assignment under base change — covered exhaustively
by Silverman, *The Arithmetic of Elliptic Curves*, §III.1 (the Weierstrass equation transforms by
applying the field/ring map to each coefficient). No external source is needed to fix the maximally
general statement; mathlib already encodes it (see §3).

ChatGPT MCP: not consulted (server flagged down in environment; decl is trivial and the mathlib match
is exact, so a second opinion adds nothing).

---

## 3. Mathlib search (five methods)

`lean_loogle` / `lean_leansearch` were unavailable in this environment, so the search was done by
reading the pinned mathlib source directly
(`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`). This is stronger
than an index hit: it shows the lemma exists **and** is used by name inside mathlib.

**The match — `WeierstrassCurve.map_a₁`.** `Weierstrass.lean:229-232`:

```lean
/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩
```

The `@[simps]` attribute auto-generates, as `@[simp]` lemmas, exactly:

```
WeierstrassCurve.map_a₁ : (W.map f).a₁ = f W.a₁
WeierstrassCurve.map_a₂ : (W.map f).a₂ = f W.a₂
WeierstrassCurve.map_a₃ : (W.map f).a₃ = f W.a₃
WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄
WeierstrassCurve.map_a₆ : (W.map f).a₆ = f W.a₆
```

for an arbitrary ring hom `f : R →+* A`. These names are not hypothetical — mathlib itself invokes them
by name in the very next proofs: `map_b₂` uses `simp only [b₂, map_a₁, map_a₂]` (line 244), `map_b₄` uses
`map_a₁, map_a₃, map_a₄` (line 249), `map_b₈` uses `map_a₁, map_a₂, map_a₃, map_a₄, map_a₆` (line 259).
So `WeierstrassCurve.map_a₁` is a confirmed, exported, `@[simp]` lemma in the same mathlib file the
project already imports (`import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`, `GeneralCurve.lean:2`).

**The cast step.** `curveQ_a₁` displays the RHS as `(W.a₁ : ℚ)` rather than `(algebraMap ℤ ℚ) W.a₁`.
These are equal by `eq_intCast` (`Mathlib/Data/Int/Cast/Lemmas.lean:336`):
`f n = n` for any `f : ℤ → α` in a `RingHomClass`. This is a `@[simp]`-discharged standard fact.

Hence `simp [curveQ]` proves `curveQ_a₁` by: unfold the `curveQ` abbrev → fire `map_a₁` → fire
`eq_intCast`. All three steps are mathlib simp lemmas; nothing project-local is used. The fact that the
project's own proof is the one-liner `by simp [curveQ]` is itself the demonstration that mathlib alone
closes the goal.

This is the *consolidation-fork* case flagged in the task: NagellLutz forks parts of the
elliptic-curve hierarchy, and this coefficient lemma is a re-statement of a result that already lives in
upstream mathlib in strictly greater generality.

---

## 4. Generality analysis

| | statement | generality |
|---|---|---|
| project `curveQ_a₁` | `(curveQ W).a₁ = (W.a₁ : ℚ)`, `W : WeierstrassCurve ℤ` | fixed `ℤ → ℚ` |
| mathlib `map_a₁` | `(W.map f).a₁ = f W.a₁`, any `f : R →+* A`, any `CommRing R A` | maximally general |

The project lemma is the single instance `R := ℤ`, `A := ℚ`, `f := algebraMap ℤ ℚ` of the mathlib
lemma (modulo the `eq_intCast` cosmetic rewrite). Mathlib is strictly more general on every axis: the
source ring, the target ring, and the ring hom. There is no axis on which `curveQ_a₁` is more general.
So this is not even a "generalise-first" candidate — the general form is already in mathlib.

---

## 5. Composition check (≤3 mathlib calls?)

Yes — and it is essentially **one** call.

```lean
example (W : WeierstrassCurve ℤ) : (W.map (algebraMap ℤ ℚ)).a₁ = (W.a₁ : ℚ) := by
  rw [WeierstrassCurve.map_a₁]; exact eq_intCast _ _   -- 2 lemmas; or simply: by simp
```

- `WeierstrassCurve.map_a₁` (mathlib `@[simp]`) — does the coefficient read-off.
- `eq_intCast` (mathlib `@[simp]`) — turns `(algebraMap ℤ ℚ) W.a₁` into `(W.a₁ : ℚ)`.

Two mathlib lemmas, both `@[simp]`, both already imported. `simp` chains them automatically. Well within
the ≤3 budget; the result is a direct corollary, not an independent contribution.

---

## 6. Downstream usage (for the cleanup recommendation, not the verdict)

`curveQ_a₁` *is* used internally (unlike `curveQ_a₂/a₄/a₆`), always inside a `simp only` coefficient
rewrite:

| call site | usage |
|---|---|
| `…/LutzNagellTheorem/GeneralMain.lean:167` | `simp only [curveQ_a₁, curveQ_a₃, shortCurveZ_a₁, shortCurveZ_a₃, …]` |
| `…/LutzNagellTheorem/GeneralDiscriminant.lean:72` | `simp only [curveQ_a₁, curveQ_a₃] at hψ₂` |
| `…/LutzNagellTheorem/GeneralPrimeOrder.lean:176` | `simp only [curveQ_a₁, curveQ_a₃] at h; linarith` |

Because `curveQ` is a bare `abbrev`, each of these would work identically with the mathlib lemma:
`simp only [curveQ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, eq_intCast, …]`. So the local
lemma can be retired in favour of upstream without statement changes downstream.

---

## 7. Verdict

**NO-mathlib-has-it.**

`curveQ_a₁` is the `f = algebraMap ℤ ℚ` instance of mathlib's
`WeierstrassCurve.map_a₁ : (W.map f).a₁ = f W.a₁`, which the `@[simps]` attribute on `WeierstrassCurve.map`
(`Mathlib/.../EllipticCurve/Weierstrass.lean:230`) already emits as a `@[simp]` lemma — and which mathlib
itself uses by name at `Weierstrass.lean:244`. The only extra step, rewriting `(algebraMap ℤ ℚ) W.a₁`
to `(W.a₁ : ℚ)`, is the standard `eq_intCast` (`Mathlib/Data/Int/Cast/Lemmas.lean:336`). The project's
proof is literally `by simp [curveQ]`: mathlib's simp set closes it with nothing project-specific. The
result already exists upstream in strictly greater generality; there is no contribution to add.

**Cleanup recommendation (process, not mathlibability):** delete the `curveQ_aᵢ` block
(`GeneralCurve.lean:27-31`) and migrate the three `curveQ_a₁`/`curveQ_a₃` call sites
(`GeneralMain.lean:167`, `GeneralDiscriminant.lean:72`, `GeneralPrimeOrder.lean:176`) to
`WeierstrassCurve.map_a₁`/`map_a₃` + `eq_intCast` (or just unfold `curveQ` and let `simp` fire the
upstream `@[simp]` lemmas). Statement-preserving; owning project's call.

---

### One-line ledger rationale
`curveQ_a₁` is `WeierstrassCurve.map_a₁` (a `@[simps]`-generated mathlib `@[simp]` lemma) specialised to
`f = algebraMap ℤ ℚ`; the cast is `eq_intCast`. Mathlib has it, strictly more general.
