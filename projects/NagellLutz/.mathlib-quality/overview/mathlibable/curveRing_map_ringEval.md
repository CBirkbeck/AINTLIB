# /mathlibable report — `WeierstrassCurve.Universal.curveRing_map_ringEval`

> The **pointed naturality / universal-property lemma** of the `ringEval` specialization
> homomorphism: every Weierstrass curve `W` over `R` with a point `(x,y)` is recovered from the
> universal pointed curve (over its coordinate ring `Universal.Ring`) by mapping along the
> point-induced evaluation hom `ringEval`. It is the *pointed refinement* of `map_specialize`
> (`curve.map W.specialize = W`), the unpointed twin assessed in `map_specialize.md`
> (→ `BORDERLINE-needs-human`). This lemma is named in `ringEval.md`'s `YES`-bundle (line 317) as one
> of the inseparable companions of `ringEval`, and named in `curve.md`'s rationale (line 300) as one
> of the theorems the universal curve is *named after*.

### Baseline (Phase 0)
- lake build:               (not re-run — local build is stale per task note; reasoned from source +
  mathlib `.lake/packages/mathlib` source tree, which is the authoritative index here)
- decl `WeierstrassCurve.Universal.curveRing_map_ringEval`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:237`
- kind:                      `lemma`  (a `Prop` — Phase 4.5 diamond/defeq pass is **skipped**)
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" — defines
  the universal Weierstrass curve over `ℤ[A₁..A₆]`, the universal ring/field, the specialization
  hom `W.specialize`, and the point-induced homs `polyEval`/`ringEval`.

**Qualified-name verification.** File has `namespace WeierstrassCurve` (line 69); `namespace
Universal` is opened (line 75/196) and the lemma sits inside it at line 237 (the `end Universal`
closes at line 241). The intervening `open Universal` (line 185) + `namespace Universal` (line 196)
nest it correctly. Parsed qualified name `WeierstrassCurve.Universal.curveRing_map_ringEval` is
**CONFIRMED**.

Exact source (lines 237–239):
```lean
lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W :=
  (map_map curve (algebraMap _ _) (ringEval eqn)).symm ▸
    (ringEval_comp_eq_specialize eqn) ▸ map_specialize W
```
with the ambient binders (lines 186, 198, 210):
`{R} [CommRing R] (W : WeierstrassCurve R) (x y : R) {W x y} (eqn : Affine.Equation W x y)`.

---

### Statement (Phase 1)

`curveRing_map_ringEval` states: **for any Weierstrass curve `W` over a commutative ring `R`,
together with an affine point `(x, y)` satisfying `W`'s Weierstrass equation, the base change of the
universal Weierstrass curve to its own coordinate ring `O = ℤ[A₁..A₆][X,Y]/⟨P⟩`, mapped along the
point-induced specialization ring homomorphism `ringEval : O →+* R`, equals `W`.**

In board notation: let `𝓔` be the universal curve over `A = ℤ[A₁..A₆]`, with coordinate ring
`O = A[X,Y]/(P)` carrying the tautological/generic point `(X mod P, Y mod P)`. A pointed curve
`(W, (x,y))` over `R` induces an evaluation hom `ev = ringEval : O →+* R` (`Aᵢ ↦ aᵢ(W)`, `X ↦ x`,
`Y ↦ y`). Then `(𝓔 ×_A O).map(ev) = W`. Equivalently: pulling the universal curve back to `O` and
then specializing along the point's evaluation map recovers `W` — the **functoriality (naturality) of
the universal pointed curve under specialization**.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — the base ring of the target curve (no further hypotheses; full
  `CommRing` generality).
- `(W : WeierstrassCurve R)` — the target Weierstrass curve.
- `{x y : R}` — the coordinates of the point.

Hypotheses (Lean side):
- `(eqn : W.Affine.Equation x y)` — `(x, y)` lies on (the affine model of) `W`; this is exactly what
  makes `ringEval` well-defined (it factors `polyEval` through the relation `P = 0`).

Conclusion (math): the universal curve over its coordinate ring, specialized along the point's
evaluation map, equals `W`.
Conclusion (Lean): `Universal.curveRing.map (Universal.ringEval eqn) = W`, an equality in
`WeierstrassCurve R`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (in the structural sense), but a **structurally load-bearing API lemma**.
Reason: it is not a `## Main results` headline (the project's main result is Nagell–Lutz), not a
person-named theorem, and it introduces no new structure. It is the *universal-property /
functoriality lemma* of the project's `ringEval` specialization hom — a corollary-shaped statement
that is nonetheless the linchpin transporting universal-ring `smulRing` arithmetic down to a concrete
curve (4 call sites in `ZSMul.lean`). Per the skill, literature width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: this is a **`lemma`**, not a `def`/`abbrev`/`structure` — the one-liner check is
**n/a** (it gates definitions, not propositions). Recorded for completeness: the proof is a 3-rewrite
term-mode chain (`map_map` ▸ `ringEval_comp_eq_specialize` ▸ `map_specialize`); it is a genuine
naturality lemma, not a `:= rfl` glue alias, so the Mode-B verdict-inheritance rule does **not** fire
(it is not `rfl`/`Iff.rfl`/`unfold` — it composes three distinct facts, one of them mathlib's
`map_map`, two of them project-local universal-property lemmas).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | universal Weierstrass curve specialization homomorphism functoriality; every elliptic curve a specialization of universal curve | yes  | universal Weierstrass curve + universal point "corresponding to the identity map"; specialization hom `σ : E(ℚ(t)) → E(t₀)` | Reed ecintro; **Stange-style homogeneous-division-poly paper (arXiv 1303.4327)** explicitly: "there exists a universal Weierstrass curve and a universal point corresponding to the identity map"; mathlib4 Weierstrass docs (map over a ring hom) |
|  2 | WebSearch (general / coord-ring)  | universal elliptic curve coordinate ring base change recovers curve; specialization map; Katz–Mazur     | yes  | `A = ℤ[a₁..a₆]` parametrizes; Katz–Mazur *Arithmetic Moduli*; Conrad KM paper; Parson moduli | base change to the coordinate ring + recover-the-curve is treated as a routine moduli/functoriality fact, **not a separately-named proposition** |
|  3 | WebSearch (named-after / aliases) | elliptic curve point induces ring homomorphism on coordinate ring; generic point; naturality of base change; pointed curve | yes  | Sage `ell_generic` (curves over a general ring; evaluation of polynomials at points); "a map between curves induces a ring hom between coordinate rings via polynomial evaluation"; coordinate-ring chapter notes | the evaluation-hom-from-a-point and its naturality are standard scheme-theory (`Spec` of the eval map = the point), but no source names *this* compatibility as a theorem — it is "the universal curve represents the pointed-curve functor" |
|  4 | ChatGPT MCP                      | Is the "base-change-universal-curve-to-its-coord-ring-then-specialize = W" naturality a NAMED result; is the coefficient-ring universal property the primary statement with this a corollary; is it fundamentally functoriality-of-base-change + the defining equations? | **n/a — server DOWN** | — | Codex exec **failed** (task note warned MCP may be down; confirmed). Compensated with extra WebSearch breadth (#1–#3 + #9–#10) and direct mathlib-source reading (`map_map`, `map_baseChange`). |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "universal" / "specialization"                                  | **n/a** | (no `references/` dir for NagellLutz; no `refs/` store on this checkout) | both directories absent — recorded n/a (verified by `ls`) |
|  6 | nLab                             | universal elliptic curve / moduli stack of elliptic curves; pullback of universal family                | yes  | universal curve `𝓔 → 𝓜₁,₁`; pulling back `𝓔` along a map to the moduli stack yields the classified curve | the naturality *is* the defining property of the universal family (pullback along the classifying map = the curve); no separate name |
|  7 | nCatLab (categorical)            | representable moduli functor of (pointed) Weierstrass curves; representing object                        | yes  | `ℤ[a₁..a₆]` (resp. its coord ring) represents the functor `R ↦ {Weierstrass curves}` (resp. pointed); Yoneda → universal element | this lemma is exactly "the universal element pulls back to an arbitrary element" — the Yoneda/representability triviality, unnamed |
|  8 | Stacks Project (if alg geom)     | moduli stack of elliptic curves (tag 072K); universal object pulls back to the classified object        | yes  | tag 072K + the general "universal family pulls back along the classifying morphism" pattern | base change of the universal family to recover a given one is the *definition* of "universal/representing", not a stated proposition |
|  9 | MathOverflow / Math.StackExchange| universal Weierstrass curve generic point; point ↦ evaluation hom on coordinate ring; functoriality      | yes  | point on `X` ↔ `R`-algebra map `O(X) → R` (Spec); base change naturality | confirms the point↔eval-hom dictionary as standard scheme theory; the curve-level naturality is its immediate consequence |
| 10 | recent arXiv (last 5 years)      | division polynomials over the universal ring; specialize-to-a-concrete-curve; EDS recurrences            | yes  | ψₙ/φₙ/ωₙ live over `ℤ[a₁..a₆][x,y]`; "evaluate-and-specialize" to a concrete `W` is the standard technique | arXiv 1303.4327 (homogeneous division polys, universal curve + universal point), eprint 2025/521 — the universal ψₙ is the standard home; specializing down is *the* method, used but not named as a proposition |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (specific
functoriality form, coordinate-ring/general form, named-after/aliases) + arXiv #10; nLab / nCatLab /
Stacks / MathOverflow each checked; local refs recorded n/a (both `references/` and `refs/` absent).
ChatGPT MCP is **down** (Codex command failure, not a skip) and is compensated by extra WebSearch
breadth + direct mathlib-source reading.

### Literature summary (Phase 3)

Concept identified as: **the naturality / universal property of the universal (pointed) Weierstrass
curve under specialization** — every pointed Weierstrass curve `(W, (x,y))` over any `R` is the
pullback of the universal pointed curve along the evaluation map its point induces.
Sources agree on the standard form: **yes** — the universal Weierstrass curve and its universal point
are classical and named (Stange/homogeneous-division-poly arXiv 1303.4327 states "a universal
Weierstrass curve and a universal point corresponding to the identity map"; Katz–Mazur; the nLab
moduli stack; Sage `ell_generic`). **But the specific compatibility "base-change the universal curve
to its coordinate ring, then specialize along the point's evaluation map = `W`" is universally treated
as the *defining property of universality* (Yoneda: the universal element pulls back to an arbitrary
element), not as a separately-named proposition.** It is functoriality-of-base-change (`(E.map f).map
g = E.map (g ∘ f)`) composed with the defining equations of the specialization hom (`Aᵢ ↦ aᵢ(W)`,
`X ↦ x`, `Y ↦ y`) — exactly the shape of the Lean proof.
Most general standard form: stated over an arbitrary commutative ring `R` (the project's form);
mathlib's `WeierstrassCurve` API and the moduli-theoretic statement both live at this generality.
Generality dimensions where the literature varies: base ring `R` — from a function field `ℚ(t)`
(Silverman specialization) up to an arbitrary `CommRing`; the project sits at the **maximal** end
(`CommRing R`, no further hypothesis), matching mathlib's `map`/`baseChange`.
Disagreement with the literature: **none** — but the literature does not motivate a *separate named
proposition*; it is the universal property realized as a lemma. (This mirrors the
`map_specialize.md` finding exactly: standard, maximally general, but inseparable from the
`Universal.curve` construction.)

---

### Generality analysis — `WeierstrassCurve.Universal.curveRing_map_ringEval`

Literature-standard form (from Phase 3): the naturality of the universal pointed curve, stated over an
arbitrary commutative ring `R` for an arbitrary pointed Weierstrass curve.

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | base ring `R`                     | `[CommRing R]`                      | arbitrary commutative ring        | **NO**              | Already the weakest sensible class; `WeierstrassCurve` and its `map`/`baseChange` require `CommRing`. Cannot drop to a non-commutative or semiring setting — the Weierstrass equation and `MvPolynomial`/`AdjoinRoot` machinery need `CommRing`. |
| 2 | the curve `W`                     | arbitrary `WeierstrassCurve R`      | arbitrary Weierstrass curve       | **NO**              | Fully general — no `IsElliptic`/`Δ`-unit hypothesis is imposed (correctly, since recovering `W` needs none). |
| 3 | the point hypothesis `eqn`        | `W.Affine.Equation x y`            | `(x,y)` on `W`                     | **NO**              | This is precisely the hypothesis that makes `ringEval` exist (it factors `polyEval` through `P = 0`); it cannot be dropped without the LHS being ill-typed. It is the *minimal* hypothesis (affine `Equation`, not the stronger `Nonsingular`). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: **0**. (Every parameter is already at the weakest class the
statement can carry; the hypothesis `eqn` is the minimal one — affine `Equation`, not `Nonsingular`.)
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                    | no       | — | The only hypothesis `eqn` is a genuine `Prop` argument (a *point*), not a "let X be a foo" preamble; it cannot become an instance (there is no canonical point). |
|  2 | sequences/metric → filters/topology?                                                               | no       | — | No analytic content. |
|  3 | construct an object where a universal-property class would characterise it?                        | **partial / no** | If `Universal.curve` were re-expressed via an `IsUniversalWeierstrass`/initiality **class**, this lemma would become (a pointed instance of) that class's *defining axiom* rather than a derived lemma. | This is the SAME Phase-4c lever flagged in `curve.md` (row 3) and `map_specialize.md` (Q2): it is a redesign of the **`Universal.curve` def**, not a restatement of *this* lemma. `curve.md` concluded the concrete model is correct and the universal property is rightly witnessed by `specialize`/`map_specialize` (+ this pointed refinement), not bolted on as a class. So: no standalone modernisation of this lemma. |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | — | Not a substructure statement. |
|  5 | vector-space/field-specific → modules/(semi)ring?                                                  | no       | — | Already at `CommRing`; nothing field-specific. |
|  6 | 1-categorical → higher/∞-categorical?                                                              | no       | — | The moduli-stack `𝓔` (nLab/Stacks) is the ∞-flavour, but that is a different formalisation target, not a restatement of this functoriality lemma. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group?                                                   | no       | — | No index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma as stated).
One-line reason: the lemma is already the maximally-general functoriality statement; the only
"modernisation" lever (a universal-property/initiality class) is a redesign of the **`Universal.curve`
def**, identical to the one `curve.md` evaluated and *declined* (the concrete model is the canonical
representing object) — it changes the def, not this lemma, and would merely turn this lemma into the
pointed case of that class's defining axiom.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.curveRing_map_ringEval`

**n/a — declaration kind is `lemma`** (a `Prop`). It introduces no definitional equality and no
typeclass-search path, so Phase 4.5 is skipped.

---

### Mathlib search-status: `WeierstrassCurve.Universal.curveRing_map_ringEval`

[A] Lean-Finder       (no dedicated Lean-Finder tool exposed in this env) — n/a; substituted by exhaustive grep over the pinned mathlib source tree `.lake/packages/mathlib` (methods D/E below), which is authoritative.
[B] Loogle            (no `lean_loogle` tool exposed in this env) — n/a; the type-pattern target (a `WeierstrassCurve.map`/`baseChange` naturality recovering a curve) is covered by the grep in [D]: the only such lemmas in mathlib are `map_id`, `map_map`, `map_baseChange` (none of which mentions a *universal* curve or a specialization hom).
[C] LeanSearch        (no `lean_leansearch` tool exposed in this env) — n/a; the natural-language target ("universal curve specialized along a point's evaluation hom recovers the curve") is resolved negatively by the WebSearch+grep combination: the object `Universal.curve`/`ringEval` does not exist in mathlib (see [D]).
[D] Grep mathlib src  `grep -rn 'map_map|map_baseChange|ringEval|specialize|Universal' .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/` — **functoriality present** (`map_map` = `Weierstrass.lean:281` `(W.map f).map g = W.map (g.comp f)`; `map_baseChange` = `:285`; coefficient lemmas `map_aᵢ`/`map_Δ`/`map_j`); **but NO `ringEval`, NO `specialize`, NO `Universal.curve`, NO lemma of this shape.** Also `grep -rln 'def ringEval|def specialize|abbrev curveRing|Universal.curve' .lake/packages/mathlib/Mathlib/` → **empty** (the whole `Universal.lean` is unupstreamed). |
[E] Name pattern      `curveRing_map_ringEval`, `*_map_ringEval`, `map_specialize` (as a WeierstrassCurve lemma), `Universal.curve` in mathlib — **no hit** (these are project-local, authored by Junyan Xu; `map_specialize` collides only with `stalkSpecializes`/`map_specializes` in `Scheme.lean`, an unrelated specialization-of-points notion).

Searched for both:
  - the user's current form (`curveRing.map (ringEval eqn) = W`) — **not in mathlib** (`curveRing`,
    `ringEval` are project-local);
  - the literature-standard form (naturality of the universal pointed curve / the universal element
    pulls back to an arbitrary element) — **not in mathlib as a lemma**: mathlib has no universal-curve
    *object* at all, only the prose mention in `DivisionPolynomial/Basic.lean:36–38` and the
    object-free `MvPolynomial`-recurrence + `map_baseChange` route.

Concluded: **not in mathlib** (all available methods exhausted, including the literature-standard
form). Mathlib has the *functoriality building block* `WeierstrassCurve.map_map` (`Weierstrass.lean:281`)
and `map_baseChange` (`:285`), **but the two project-local ingredients the proof needs**
(`ringEval_comp_eq_specialize` and `map_specialize`, which are about the project-only `ringEval` /
`specialize` / `Universal.curve`) **do not exist in mathlib.** So the building blocks are NOT all
present in mathlib — only one of the three proof steps is mathlib's.

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.Universal.curveRing_map_ringEval`

Internal use count (NagellLutz, excluding the declaring line): **4** — all in `ZSMul.lean`.
External-to-file callers (NagellLutz): **1 distinct file** (`ZSMul.lean`); plus a verbatim duplicate
in HasseWeil (see below).

| Caller file:line                              | Usage pattern (one-line excerpt)                                                                  |
|-----------------------------------------------|---------------------------------------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:569                     | `simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]`  |
| LutzNagell/ZSMul.lean:577                     | `simp_rw [curveRing_map_ringEval]`                                                                 |
| LutzNagell/ZSMul.lean:582                     | `simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]` |
| LutzNagell/ZSMul.lean:622                     | `… curveRing_map_ringEval, map_neg, map_one]`                                                      |

These are the proofs that transport the universal-ring `smulRing` (n-division-point) identities down
to a concrete curve `W` — the engine of the project's `n • P` computation. `curveRing_map_ringEval` is
the rewrite that turns `(curveRing.map (ringEval eqn))`-statements back into `W`-statements.

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - **(none)** in NagellLutz — every site uses the lemma by name.
  - **Verbatim cross-project duplicate**: `HasseWeil/Auxiliary/Universal.lean:240` re-declares the
    identical lemma (same proof), with its own call sites in `HasseWeil/Auxiliary/DivisionPolynomial.lean`
    (lines 647, 655, 661, 704). This is a `Common/`-dedup *cleanup* concern, and is *also* evidence the
    lemma is real shared API (two independent NT developments depend on it).

**Call-sites reading.** K = 4 internal uses (NagellLutz) + 4 more in the HasseWeil duplicate, **no
inline re-derivation** anywhere. By the Phase-6.0.1 table this is the **"K ≥ 3, no inline
re-derivation → real API; consumers depend on it → YES-\* bucket"** pattern. It is decidedly *not* the
"K = 0, re-derived inline → NO-composable wrapper" pattern.

#### Composition check

Can `curveRing_map_ringEval` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `(map_map curve (algebraMap _ _) (ringEval eqn)).symm ▸ (ringEval_comp_eq_specialize eqn) ▸ map_specialize W`
  - Mathlib decls used: **`WeierstrassCurve.map_map`** (`Weierstrass.lean:281`) — exactly **one**
    mathlib call.
  - Project-local decls used: **`ringEval_comp_eq_specialize`** (`Universal.lean:229`) and
    **`map_specialize`** (`Universal.lean:194`) — two of the three steps are about `ringEval` /
    `specialize` / `Universal.curve`, none of which exist in mathlib.
  - Result: **NOT a mathlib-only composition.** The chain is mathlib-`map_map` ∘ (two project-local
    universal-property lemmas). Inlining at the 4 call sites would require those two project lemmas (and
    transitively the whole `Universal.curve`/`ringEval` package) to be present — which is precisely the
    object mathlib lacks.
  - Notes: the *shape* (`map_map` ▸ ring-hom-compatibility ▸ universal-property) is generic, but the
    content is the universal property of a non-mathlib object.

Attempt 2 (could mathlib's `map_id`/`map_map`/`map_baseChange` + `MvPolynomial.aeval_X` give it
without `Universal.curve`?):
  - **No.** This is the identical dead-end recorded in `map_specialize.md` (lines 222–225): "No chain
    of `map_id`/`map_map`/`map_baseChange` produces the universal-property map out of `ℤ[A₁..A₆]`",
    because the LHS object (`Universal.curve` and its coordinate-ring base change `curveRing`) **does
    not exist in mathlib**. You cannot compose a statement *about* an object mathlib does not have.

Conclusion: **NOT-COMPOSABLE from mathlib's current contents.** Mathlib supplies only one of the three
proof ingredients (`map_map`); the other two — and the very objects the lemma is stated about
(`curveRing`, `ringEval`) — are project-local and absent from mathlib. This rules out
`NO-composable-from-mathlib` (that bucket *requires* mathlib to hold all the building blocks).

---

## Verdict: `WeierstrassCurve.Universal.curveRing_map_ringEval`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the universal Weierstrass curve **and its universal point** are
  standard and classical (Stange/arXiv 1303.4327 — "a universal Weierstrass curve and a universal
  point corresponding to the identity map"; Katz–Mazur; nLab/Stacks moduli stack; Sage `ell_generic`).
  The Lean statement is the **pointed naturality / universal property** at full `CommRing` generality.
  But the literature treats this compatibility as the *defining property of universality* (Yoneda: the
  universal element pulls back to an arbitrary element), **not as a separately-named proposition** — it
  is functoriality-of-base-change + the defining equations of the specialization hom.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — 0 weakenings (base `CommRing`, arbitrary `W`,
  minimal `Equation` hypothesis). Modern-idiom: the only lever (a universal-property class) is a
  redesign of the **`Universal.curve` def** — the same lever `curve.md` evaluated and declined — not a
  restatement of this lemma.
- Diamond/defeq risk (Phase 4.5): **n/a** — it is a `lemma`.
- Mathlib search (Phase 5): **not in mathlib**; mathlib has the functoriality block `map_map`
  (`Weierstrass.lean:281`) and `map_baseChange` (`:285`), but **no `ringEval` / `specialize` /
  `Universal.curve`** — confirmed by empty grep over `.lake/packages/mathlib/Mathlib/`.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — only one of the three proof
  ingredients (`map_map`) is mathlib's; the other two (`ringEval_comp_eq_specialize`,
  `map_specialize`) and the objects the lemma is about (`curveRing`, `ringEval`) are project-local and
  absent from mathlib. **4 NagellLutz call sites** (+ 4 in a verbatim HasseWeil duplicate), no inline
  re-derivation → real shared API.

**Rationale (1–2 paragraphs):**

On its own mathematical merits this lemma is a clean **YES**: it is the pointed universal property /
naturality of the universal Weierstrass curve — a standard, classical fact (the universal element
pulls back to an arbitrary element) — stated at the maximal `CommRing` generality with the minimal
point hypothesis, sorry-free, genuinely load-bearing (4 call sites driving the project's `n • P`
arithmetic, plus a verbatim HasseWeil dependency), and **not** composable from mathlib (mathlib lacks
two of the three proof ingredients and both objects the statement mentions). It is *not*
`NO-composable-from-mathlib` (mathlib does not hold the building blocks), *not* `NO-mathlib-has-it`
(mathlib has nothing of the kind), and *not* `YES-but-generalise-first` (it is already maximal; the
sole "modernisation" lever changes the underlying `def`, not this lemma).

The reason it is **BORDERLINE rather than a self-resolved YES-add-as-is** is identical to the one that
made its **unpointed twin `map_specialize` BORDERLINE** (`map_specialize.md` → `BORDERLINE-needs-human`,
Q1–Q3): **this lemma is not a standalone unit.** It is the universal property of the project-local
`Universal.curve` + `ringEval` construction (with its bespoke 5-element `Coeff` inductive,
`specialize` hom, coordinate ring `Universal.Ring`, and `ringEval`), **none of which exist in
mathlib** — and mathlib made a *deliberate* design choice in its DivisionPolynomial development to work
with `MvPolynomial Coeff ℤ`-valued recurrences and a `map_baseChange` morphism, naming "the universal
morphism `𝓡[X,Y] → R[X,Y]`" only in a docstring and **never constructing the universal curve as an
object** (`DivisionPolynomial/Basic.lean:36–38`). So whether `curveRing_map_ringEval` belongs in
mathlib is **inseparable from** whether mathlib should reify the universal curve at all — a
mathlib-design / project-policy judgment the skill cannot make alone. (This is a genuine design
judgment, **not** a cost-driven downgrade: the proof is cheap; the open question is architectural.)
Concretely, the sibling reports already disagree on exactly this seam: `ringEval.md`
(→ `YES-add-as-is`) lists `curveRing_map_ringEval` *inside* its single-PR bundle (line 317), treating
the bundle decision as already made "yes"; `map_specialize.md` (→ `BORDERLINE`) defers that very
bundle decision to a human. The honest, non-silent verdict — per the skill's "never silently pick when
two buckets fit" rule — is to surface the seam: **the lemma rides along with the `Universal.curve`
bundle, and the bundle-vs-mathlib's-existing-presentation call is the human decision.**

**Numbered questions (≤5):**
  1. Should mathlib gain a reified **universal Weierstrass curve** object (`Universal.curve` over
     `ℤ[A₁..A₆]`, with the `Coeff` inductive, the coordinate ring `Universal.Ring`, the field
     `Universal.Field`, and the homs `specialize` / `polyEval` / `ringEval`), rather than only its
     current object-free `MvPolynomial`-recurrence + `map_baseChange` presentation? `curveRing_map_ringEval`
     ships **only** as part of that construction — yes/no? *(Identical to `map_specialize.md` Q1; a "yes"
     here resolves both lemmas to YES-add-as-is inside the bundle. This is the gating question — answer
     it once for the whole `Universal.lean` package, since `curve.md`/`ringeval.md`/`map_specialize.md`/
     this report all hinge on it.)*
  2. If yes: is the project's concrete packaging (the 5-element `Coeff` inductive + `MvPolynomial.aeval`-
     and `AdjoinRoot.lift`-based `specialize`/`ringEval`) the form mathlib wants, or should the universal
     curve be characterised by an **initiality / universal-property typeclass** (Phase 4c row 3), in
     which case `map_specialize` becomes the unpointed defining axiom and `curveRing_map_ringEval` its
     pointed instance — a `def` redesign, not a change to this lemma? *(Same lever `curve.md` declined.)*
  3. Within AINTLIB specifically: the whole `Universal.lean` (incl. this lemma) is **forked near-verbatim
     across NagellLutz and HasseWeil**; should the `Common/`-dedup cleanup land first (one shared copy)
     before any mathlib upstreaming, so the bundle is consolidated when it moves? (yes/no — a sequencing
     decision, owned by the cleanup fleet, not a mathematical one.)

**Next action:** user (or a mathlib EC maintainer) answers Q1–Q3 — and crucially, **answer Q1 once for
the entire `Universal.lean` package**, since `curve.md` (`YES`), `ringEval.md` (`YES`),
`map_specialize.md` (`BORDERLINE`) and this report all hinge on the same bundle decision and should be
resolved together rather than per-lemma.
  - **If Q1 = "yes":** `curveRing_map_ringEval` is a clean **`YES-add-as-is`** that rides along as the
    *pointed* universal-property lemma in the bundle. Proposed mathlib location:
    `Mathlib/AlgebraicGeometry/EllipticCurve/Universal.lean` (new file), shipped as **one PR** with
    `Coeff`, `Universal.curve`, `Δ_curve_ne_zero`, `Poly`/`Ring`/`Field`, `pointedCurve`, `specialize`,
    `map_specialize`, `polyEval` (+ `polyEval_apply`, `polyEval_comp_eq_specialize`), `ringEval`
    (+ `ringEval_mk`, `ringEval_comp_mk`, `ringEval_comp_eq_specialize`), **and this lemma** — exactly
    the bundle named in `ringEval.md:308–319` and `curve.md:325–328`. Proposed PR title:
    `feat(AlgebraicGeometry/EllipticCurve): the universal Weierstrass curve and its specialization maps`.
    Pre-PR: land the `Common/` dedup (Q3), then run `/generalise` (expected: none — already maximal) and
    `/cleanup` on the whole package; reviewer = recent EC committers (David Kurniadi Angdinata; Junyan
    Xu, the file's author).
  - **If Q1 = "no":** `curveRing_map_ringEval` stays a correct, well-scoped **project-local** lemma with
    no mathlib action (and the NagellLutz ↔ HasseWeil duplication is handled purely as an internal
    `Common/`-dedup cleanup ticket).

---

## Next step

`BORDERLINE-needs-human`. The lemma is a YES on its own merits — the standard, maximally-general,
load-bearing *pointed* universal-property of the universal Weierstrass curve, not composable from
mathlib (mathlib lacks two of its three proof ingredients and both objects it mentions). But it is
inseparable from the project-local `Universal.curve` + `ringEval` package, and whether mathlib should
reify that package (vs. its existing object-free `MvPolynomial`-recurrence presentation) is the same
human/design decision that made the unpointed twin `map_specialize` BORDERLINE. **Answer the gating
question Q1 once for the whole `Universal.lean` bundle** (`curve`/`ringEval`/`map_specialize`/this
lemma): a "yes" makes this a clean `YES-add-as-is` riding in the single-PR bundle named in
`ringEval.md`; a "no" leaves it a correct project-local lemma (with the NagellLutz ↔ HasseWeil
duplication handled as a `Common/` cleanup ticket).
