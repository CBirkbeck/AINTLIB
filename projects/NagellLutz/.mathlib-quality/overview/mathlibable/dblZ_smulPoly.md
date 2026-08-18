# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.dblZ_smulPoly`

- Step-9 mathlibable assessment, AINTLIB `/overview`, NagellLutz project (Nagell–Lutz theorem;
  elliptic curves; division polynomials; elliptic divisibility sequences).
- decl `WeierstrassCurve.Universal.Jacobian.dblZ_smulPoly`:
  ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:437`.

## 0. Qualified name — VERIFIED

Namespace nesting in `ZSMul.lean` (from `grep "^namespace"`):
`namespace WeierstrassCurve` (L76) → `namespace Universal` (L86) → `namespace Jacobian` (L395),
and L437 sits inside all three (`end Jacobian` is L544). So the full name is

    WeierstrassCurve.Universal.Jacobian.dblZ_smulPoly

— exactly the parsed guess. ✔

## 1. The statement and proof (from source)

```lean
-- ZSMul.lean:437–443
lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  unfold dblZ smulPoly WeierstrassCurve.Jacobian.negY curvePoly
    WeierstrassCurve.Affine.baseChange WeierstrassCurve.baseChange
  simp_rw [fin3_def_ext, WeierstrassCurve.map]
  rw [← ψc_spec _ n]; congr; convert curve.ω_spec n using 1
  simp_rw [show ∀ x, CC x = (algebraMap _ Poly) x from fun _ ↦ rfl]
  norm_num; ring
```

with `n : ℤ` implicit (from `variable {m n : ℤ}` at L97).

Surrounding objects:
- `smulPoly (n) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]` (ZSMul.lean:414) — the
  universal division-polynomial triple `(φₙ, ωₙ, ψₙ)` in Jacobian coordinates.
- `curvePoly : WeierstrassCurve Poly := curve.baseChange Poly` (Universal.lean:167), where
  `curve : Affine (MvPolynomial Coeff ℤ)` (Universal.lean:84) is **the universal Weierstrass
  curve** over `ℤ[A₁,A₂,A₃,A₄,A₆]`.
- `dblZ` is **mathlib's** Jacobian doubling Z-coordinate:
  `def dblZ (P : Fin 3 → R) : R := P z * (P y - W'.negY P)`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:199`).

**What it says (mathematical content).** Apply mathlib's Jacobian point-doubling Z-coordinate
`dblZ` to the division-polynomial triple `(φₙ, ωₙ, ψₙ)` of the universal curve; the result is the
`(2n)`-th division polynomial `ψ₂ₙ`. Concretely, with `negY` for this triple,
`dblZ(φₙ,ωₙ,ψₙ) = ψₙ·((ωₙ) − negY) = ψₙ·(2ωₙ + a₁φₙψₙ + a₃ψₙ³) = ψₙ·ψcₙ = ψ₂ₙ`, the classical
"`ψₙ` divides `ψ₂ₙ`, with complementary factor `ψcₙ`" identity. It is computed **in the polynomial
ring `Poly` itself, with no passage to a quotient** — this is the easy "Z-coordinates already agree
on the nose" half of the universal doubling identity `dblXYZ_smulField`.

**Load-bearing proof steps:**
- `rw [← ψc_spec _ n]` — turns the goal's RHS `ψ(2n)` into `ψ n * ψc n`, using
  `ψc_spec : W.ψ n * W.ψc n = W.ψ (2*n)` (DivisionPolynomialOmega.lean:93,
  `:= normEDS_mul_compl₂EDS _ _ _ _`).
- `convert curve.ω_spec n using 1` — the heart of the proof. `ω_spec`
  (DivisionPolynomialOmega.lean:82) is `2·ω n + a₁·φ n·ψ n + a₃·ψ n³ = ψc n`.

**Both `ψc` and `ω_spec` are project-only objects** (DivisionPolynomialOmega.lean), built on the
project's `ω` — which mathlib **does not have** (see §5). `ω_spec` is precisely the rearranged form
of mathlib's *intended-but-absent* `ωₙ` definition (see §5 quote). So this lemma is, in substance,
mathlib's `dblZ` evaluated on a triple whose middle entry is the missing `ω`, proven equal to `ψ₂ₙ`
via the `ω`/`ψc` machinery.

## 2. Role / consumers (Phase 6.0)

Internal callers (NagellLutz), all in `ZSMul.lean`:
- L467 `dblXYZ_smulField` — `simp only [… ← dblZ_smulPoly, ← map_dblZ]` (the Z-coordinate input to
  the universal doubling identity).
- L512 `addXYZ_smulField` — `… ← dblZ_smulPoly, ← map_dblZ, smulField_zero` (the `n = −m` branch).

So **K = 2 internal uses**, both feeding the two universal `*_smulField` identities, which in turn
drive the headline `zsmul_eq_smulEval`. Genuine load-bearing infrastructure, not a one-off.

**Duplicated verbatim in a second project:**
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:516` contains an identical
`private lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by …`. This is the
"duplicated General*/PID* tracks" the brief flagged: Junyan Xu's universal-curve division-polynomial
file is **copied** into NagellLutz and HasseWeil, not shared. (In HasseWeil it is `private`; in
NagellLutz it is public.)

## 3. Literature search (Phase 3)

The identity is bog-standard, textbook elliptic-curve theory. The factorisation
`ψ₂ₙ = ψₙ·(2ωₙ + a₁φₙψₙ + a₃ψₙ³)` (equivalently `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2`) is the
defining relation for the `ω`-family in the multiplication-by-`n` formula
`[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`.

Standard references for `(φₙ, ωₙ, ψₙ)` and the `ψₙ | ψ₂ₙ` doubling relation:
- Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), Exercise 3.7 (division polynomials).
- A. Sutherland, MIT 18.783 Lecture 6 (division polynomials; Jacobian coordinates as the convenient
  model for `[n]`): https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf
- mathlib's own `DivisionPolynomial/Basic.lean` module docstring (it states exactly this `ωₙ`
  formula and the `ψₙ | ψ₂ₙ` divisibility — see §5).

The **triple/Z-coordinate identity itself is not a separately-named theorem** in the literature; it
is an intermediate computation toward the multiplication-by-`n` map. (Web search returned the
expected sources — Sutherland 18.783, Silverman-style treatments — but no separately-named "doubling
Z-coordinate equals ψ₂ₙ" result; it is plumbing inside the standard derivation.)

## 4. Generality analysis (Phase 4) — STRICTLY NARROWER than its natural form

| # | knob | here | natural mathlib form | weaker? | cost |
|---|------|------|----------------------|---------|------|
| 1 | the curve | hard-wired to `curvePoly = curve.baseChange Poly` (the **universal** curve over `ℤ[A₁..A₆]`) | any `W : WeierstrassCurve R`, `[CommRing R]` | **yes** | the **general statement is cheap** — `dblZ`, `negY`, `φ`, `ψ`, `ω`, `ψc`, `ω_spec`, `ψc_spec` are *already* stated for a general `W` (DivisionPolynomial.lean:29 `variable … (W : WeierstrassCurve R)`; `ω`/`ω_spec`/`ψc`/`ψc_spec` all general). The natural form `W.dblZ ![W.φ n, W.ω n, W.ψ n] = W.ψ (2*n)` would have essentially **this same 4-line proof**. |

The natural mathlib statement is

    lemma dblZ_smulPoly {R} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
      W.dblZ ![W.φ n, W.ω n, W.ψ n] = W.ψ (2 * n)

The universal restriction is a **proof-technique specialisation** (Xu proves the universal case so
that he can later specialise to *any* field, including char 2), not a content restriction — the
identity holds over every `W`. **VERDICT: strictly narrower; the general form is cheap** *modulo the
missing `ω`* (the proof is the same `ω_spec`/`ψc_spec` rewrite). This is the standard `YES-but-
generalise-first` shape — **except** the generalisation can't actually land in mathlib until `ω`
does (§5).

## 5. Mathlib search (Phase 5) — NOT in mathlib; blocked by the `ω` TODO

Five-method search (lean_loogle / lean_leansearch were unavailable in this environment — the
mathlib-index MCP tools are not exposed here — so this is a **source-level** search of the pinned
mathlib in `.lake/packages/mathlib`, which is definitive for presence/absence):

- **[A] exact name** `dblZ_smulPoly`: only in the two AINTLIB copies; **not in mathlib**.
- **[B] exact statement** `dblZ … = ψ (2*n)` / `dblZ` on a division-poly triple:
  `grep -rn "dblZ" Mathlib/.../DivisionPolynomial/` → **empty**. mathlib's `DivisionPolynomial`
  files never mention `dblZ`/`dblXYZ`/`zsmul`. ⇒ no such identity in mathlib.
- **[C] the bridge direction** — does mathlib's `Jacobian/` ever reference division polynomials?
  `grep -rln "DivisionPolynomial|normEDS|preΨ|\.ψ " Mathlib/.../Jacobian/` → **empty**. **The two
  subsystems (`Jacobian` doubling and `DivisionPolynomial`) are currently disconnected in mathlib.**
  This lemma is exactly a bridge between them.
- **[D] the ingredient** `dblZ`: present
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean:199`,
  `dblZ P = P z * (P y − W'.negY P)`), with API `dblZ_smul`, `dblZ_of_Z_eq_zero`, `dblZ_of_Y_eq`,
  `dblZ_ne_zero_of_Y_ne`, … — but **never applied to division polynomials**.
- **[E] the blocker — `ω`**: `grep -rn "def ω" Mathlib/.../DivisionPolynomial/` → **empty**. mathlib
  has `preΨ, ΨSq, Ψ, Φ, ψ, φ` but **not `ω`**, and the module docstring marks it an explicit TODO:

  > `DivisionPolynomial/Basic.lean:30` — `ωₙ := (ψ₂ₙ / ψₙ − ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2`.
  > `DivisionPolynomial/Basic.lean:71` — `* TODO: the bivariate polynomials ωₙ.`
  > `DivisionPolynomial/Basic.lean:83` — `TODO: implementation notes for the definition of ωₙ.`

  The project's `ω_spec` (`2·ω n + a₁·φ·ψ + a₃·ψ³ = ψc n`, with `ψc n · ψ n = ψ(2n)`) is **precisely
  the rearrangement of this intended-but-absent `ωₙ` definition** — i.e. NagellLutz has implemented
  the exact thing mathlib's TODO calls for.

**Conclusion:** `dblZ_smulPoly` is **NOT in mathlib**, and it cannot be — it *names a value mathlib
cannot yet express* (`curve.ω n`) and *connects two subsystems mathlib keeps separate* (`dblZ` ↔
`ψ`). It sits squarely downstream of the open `ωₙ` TODO.

## 6. Composition check (Phase 6a) — NOT composable from current mathlib

Can ≤3 chained mathlib calls reproduce `dblZ(φₙ,ωₙ,ψₙ) = ψ₂ₙ`? **No.** The very *statement* mentions
`curve.ω n`, which has no mathlib referent (`ω` is a TODO). You cannot even write the goal in terms
of mathlib alone — the term `![W.φ n, W.ω n, W.ψ n]` inlines to `![φₙ, ⟨MISSING⟩, ψₙ]`. The proof
then needs `ω_spec` + `ψc_spec`, both project-only. **NOT-COMPOSABLE — blocked by the missing `ω`,
not by proof depth.** (Once `ω` + `ω_spec` + `ψc`/`ψc_spec` land in mathlib, this becomes a clean
4-line lemma — see §4.)

## 7. Five-bucket verdict

**Category:** `BORDERLINE-needs-human`

**Why not the neighbours:**
- **not `NO-mathlib-has-it`** — §5: absent, and structurally absent (relies on the `ω` TODO; bridges
  two disconnected subsystems).
- **not `NO-composable-from-mathlib`** — §6: not expressible, let alone derivable, from current
  mathlib; the missing `ω` is infrastructure, not a 3-call gap.
- **not `YES-add-as-is`** — §4: it is strictly narrower (hard-wired to the universal curve) than the
  obvious general form, so it should not go in verbatim.
- **not cleanly `YES-but-generalise-first`** — although the *shape* is exactly that (cheap
  generalisation to general `W`), the generalised lemma **still cannot land in mathlib until `ωₙ`
  does**, and *whether/how* to upstream the `ω`-family + multiplication-by-`n` machinery (and how to
  package this Z-coordinate identity within it — named bridge lemma vs. inlined step) is a
  human-scope/packaging decision. Per the skill's rule, "the general form needs new mathlib
  infrastructure (`ω`)" is a BORDERLINE question to the maintainer, not a self-resolving downgrade.

This is the **same situation as its already-assessed sibling `smulPoly`** (verdict
`BORDERLINE-needs-human`): standard mathematics, genuine reusable API (duplicated verbatim across
NagellLutz + HasseWeil), but downstream of the `ω` mathlib gap, with a packaging/scope call only a
human should make. `dblZ_smulPoly` is one of the *satellite lemmas stated about* that triple.

**Evidence summary:**
- Literature (Phase 3): the `ψₙ | ψ₂ₙ` doubling/`ω`-defining identity is textbook (Silverman GTM 106
  Ex. 3.7; Sutherland 18.783 L6; mathlib's own docstring), but **not a separately-named theorem** —
  it is an intermediate step in the multiplication-by-`n` derivation.
- Generality (Phase 4): **strictly narrower** — universal curve only; natural form is general `W`,
  proof unchanged, but depends on `ω`.
- Mathlib search (Phase 5): **not present**; ingredient `dblZ` present but **never** linked to
  division polynomials; the middle coordinate `ω` is an **explicit mathlib TODO** (Basic.lean:71,83)
  whose intended definition (Basic.lean:30) is exactly the project's `ω_spec`.
- Composition (Phase 6a): **NOT-COMPOSABLE** — the statement isn't expressible in current mathlib
  (`ω` absent); two-call/three-call reproduction impossible.

**Rationale (≤20 words):**
Standard but downstream of mathlib's open `ωₙ` TODO; narrower than the general form — upstream
packaging is a maintainer call.

**Numbered questions for the human (≤4):**

1. **Packaging / scope.** Do you intend to upstream `WeierstrassCurve.ω` + the multiplication-by-`n`
   formula (`zsmul_eq_smulEval`, Xu's universal-ring proof) to mathlib (mathlib's `DivisionPolynomial`
   lists `ωₙ` as an open TODO, and NagellLutz already implements it)? If **yes**, `dblZ_smulPoly`
   should be re-assessed **as part of that PR** — likely as the **general** `W.dblZ ![W.φ n, W.ω n,
   W.ψ n] = W.ψ (2*n)`. If **no**, it stays project-local.
2. **Named bridge vs. inlined step.** In the mathlib form, keep this as a *named* lemma
   `dblZ_smulPoly` (a stated bridge between Jacobian `dblZ` and the `ψ`-sequence, mirroring
   `addZ_smulPoly`/`map_dblZ`), or inline it inside the universal doubling proof? (It is a 4-line
   computation whose only consumers are the two `*_smulField` identities.)
3. **Generalise before any upstreaming.** Should the local copy first be rewritten to the general
   `W` form (cheap; `ω`/`ω_spec`/`ψc_spec` are already general) so the proof is curve-agnostic,
   independent of the mathlib timeline?
4. **De-duplicate now.** `dblZ_smulPoly` (+ the whole `(φₙ,ωₙ,ψₙ)` satellite suite) is duplicated
   verbatim in NagellLutz and HasseWeil. Hoist into a shared AINTLIB `Common/` module immediately
   (pure dedup, no maths), regardless of the mathlib question?

---
*Sources:* Sutherland, MIT 18.783 (2015) Lecture 6 —
https://math.mit.edu/classes/18.783/2015/LectureNotes6.pdf ; Silverman, *The Arithmetic of Elliptic
Curves* (GTM 106), Ex. 3.7 ; mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
(module docstring, lines 30/71/83) and `.../Jacobian/Formula.lean:199` (`dblZ`).
