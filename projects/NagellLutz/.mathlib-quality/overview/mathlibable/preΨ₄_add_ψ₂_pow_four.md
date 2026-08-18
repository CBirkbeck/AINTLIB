# /mathlibable report — `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four`

## Baseline (Phase 0)

- lake build:               ⚠ not run (local build stale per task brief; reasoned from source +
                            grep over the vendored `.lake/packages/mathlib` tree, which is the
                            exact mathlib this project pins)
- decl `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:64`
- qualified name:           ✓ `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four` (file opens
                            `namespace WeierstrassCurve` at line 35; matches the parsed name)
- kind:                     lemma (theorem-kind) → Phase 2b one-liner check and Phase 4.5
                            diamond/defeq check are **n/a**
- has sorry:                no
- module docstring summary: "The omega division polynomials and related definitions" — extends
                            mathlib's division-polynomial development with the `ω` family, the
                            complement `ψc`, and the invariant `invar`, needed for the `ZSMul`
                            (scalar-multiplication) proof.

## Statement (Phase 1)

`preΨ₄_add_ψ₂_pow_four` is a **polynomial identity** in the bivariate ring `R[X][Y]` over a
commutative ring `R`, for a Weierstrass curve `W / R`:

> `C W.preΨ₄ + W.ψ₂ ^ 4  =  C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq)`

Here, all objects are mathlib (or mathlib-cloned) division-polynomial data of `W`:
- `preΨ₄ : R[X]` — the univariate polynomial auxiliary to the 4-division polynomial
  (`ψ₄ = preΨ₄ · ψ₂`); a fixed degree-6 polynomial in the `bᵢ`.
- `ψ₂ : R[X][Y]` — the 2-division polynomial (`= polynomialY`).
- `Ψ₂Sq : R[X]` — the univariate polynomial congruent to `ψ₂²` (`= 4X³ + b₂X² + 2b₄X + b₆`).
- `Ψ₃ : R[X]` — the 3-division polynomial.
- `invar : R[X]` — **project-local** "invariant" `6X² + b₂X + b₄` (defined in this same file,
  `DivisionPolynomialOmega.lean:48`; **not** a mathlib object).
- `polynomial : R[X][Y]` — the Weierstrass polynomial of `W` (`Affine.polynomial`).
- `C` — the inclusion `R[X] → R[X][Y]`.

Mathematically, working modulo the Weierstrass relation `ψ₂² ≡ Ψ₂Sq` and using
`preΨ₄ + Ψ₂Sq² = invar · Ψ₃` (the sibling lemma `preΨ₄_add_Ψ₂Sq_sq`), this rewrites `preΨ₄ + ψ₂⁴`
into a form whose "error term" against `invar · Ψ₃` is an explicit multiple of the Weierstrass
polynomial. It is **pure intermediate scaffolding**: its sole purpose is to be rewritten inside the
proof of `ω_spec` (line 84 of the same file), the specification lemma for the `ω` division
polynomial.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — ambient commutative ring (maximally general for this content).
- `(W : WeierstrassCurve R)` — the curve.

Hypotheses: none (it is an unconditional polynomial identity).

Conclusion (math): the displayed identity in `R[X][Y]`.
Conclusion (Lean): `C W.preΨ₄ + W.ψ₂ ^ 4 = C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq)`.

Proof body (3 lines): `simp_rw [show 4 = 2 * 2 …, pow_mul, ψ₂_sq, add_sq, ← add_assoc, ← C_pow,
← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring` — i.e. unfold `ψ₂⁴ = (ψ₂²)²`, substitute
`ψ₂² = C Ψ₂Sq + 4·polynomial` (mathlib's `ψ₂_sq`), expand the square, fold in the sibling identity
`preΨ₄ + Ψ₂Sq² = invar·Ψ₃`, and close with `ring`. A genuine algebraic derivation, not a one-step
rewrite.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an unnamed intermediate polynomial identity; not a `def`/structure, not a named theorem,
not listed under `## Main definitions`. It is a helper consumed once, inside `ω_spec`.

(Per the skill, literature width is EXHAUSTIVE regardless. Recorded SMALL for framing.)

## One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (Note: the proof body is 3 substantive
lines of real algebra, so even by analogy this is not a "one-liner".)

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
| 1  | WebSearch (specific form)        | "elliptic curve omega division polynomial ωₙ … second coordinate scalar multiplication formula"| yes  | `[n]P = (φ/ψ², ω/ψ³)`; `4y·ωₙ = ψ²₍ₙ₋₁₎ψ₍ₙ₊₂₎ − ψ₍ₙ₋₂₎ψ²₍ₙ₊₁₎` | Standard `ω` definition; **the literature names `ω` and the `4y·ω = …` relation, not a `preΨ₄ + ψ₂⁴` step** |
| 2  | WebSearch (general / context)    | division-polynomial scalar mult `φₙ = x·ψₙ² − ψ₍ₙ₋₁₎ψ₍ₙ₊₁₎`                                     | yes  | same family; `φ`,`ψ`,`ω` triple                       | Silverman AEC Ch.III / Ex.3.7; Stange, Ayad — the `bᵢ`-level identities are textbook scaffolding, not separately named |
| 3  | WebSearch (named-after / mathlib)| "mathlib WeierstrassCurve omega division polynomial ωₙ pull request Junyan Xu"                  | yes  | mathlib docs: **"TODO: the bivariate polynomials ωₙ"** | The exact development this file implements is an open mathlib TODO; no standalone name for this helper |
| 4  | ChatGPT MCP                      | (MCP down per task brief — fallback to WebSearch ×3 + live mathlib docs)                        | n/a  | n/a — substituted by channels 1–3 + 6                 | Brief notes ChatGPT MCP may be down; compensated with extra WebSearch + WebFetch on the live mathlib docs |
| 5  | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`                                              | n/a  | directory absent                                      | No project references dir (`ls` → No such file); recorded n/a |
| 6  | Live mathlib docs (WebFetch)     | `DivisionPolynomial/Basic.html` — does it define ω / `preΨ₄ + ψ₂⁴`?                             | no   | ω **not** defined; **no** `preΨ₄_add_ψ₂_pow_four`; ω is a documented TODO with sketch `ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` | Authoritative: confirms absence in current mathlib HEAD, not just the pinned copy |
| 7  | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                        | n/a  | nLab has no division-polynomial `ω` page              | Not a categorical concept; recorded n/a |
| 8  | Stacks Project                   | division polynomial / `ωₙ`                                                                      | n/a  | not covered                                           | Stacks does not treat explicit division polynomials; n/a |
| 9  | MathOverflow / Math.SE           | covered transitively by WebSearch #1–2                                                          | n/a  | only the standard `4y·ω` relation surfaces            | No discussion of a `preΨ₄ + ψ₂⁴`-shaped identity; it is internal bookkeeping |
| 10 | recent arXiv (≤5 yr)             | Stange 2025 "Division polynomials for arbitrary isogenies"; 1909.12654 "Sequences assoc. to EC"| yes  | confirm `ψ/φ/ω` framework; `bᵢ`-level identities are derivation steps, never separately named | Reinforces: this is scaffolding, not a citable result |

### Literature summary (Phase 3)

Concept identified as: an **intermediate algebraic identity inside the construction of the `ω`
(omega) division polynomial** for a Weierstrass curve. The surrounding *named* objects are standard
(the `ω` polynomials and the relation `4y·ωₙ = ψ²₍ₙ₋₁₎ψ₍ₙ₊₂₎ − ψ₍ₙ₋₂₎ψ²₍ₙ₊₁₎`, giving the second
coordinate of `[n]P`). The specific identity `preΨ₄ + ψ₂⁴ = invar·Ψ₃ + 8·f·(2f + Ψ₂Sq)` is **not**
a named result anywhere; it is a `bᵢ`-level bookkeeping step that a paper would absorb into "a
direct computation". 
Sources agree on the standard `ω` form: yes.
Most general standard form (of the *surrounding* object): `ωₙ` over any base, second coordinate of
scalar multiplication; mathlib's own TODO sketch matches.
Generality dimensions where the literature varies: base ring (the project already uses the most
general `CommRing R`); index conventions (`n ≥ 2` vs all `ℤ` — the project does all `ℤ`).
Disagreement with the literature: none — but note the literature has **no name** for this exact
helper, which is itself a signal it is internal scaffolding rather than a mathlib-target result in
its own right.

## Generality analysis (Phase 4)

Literature-standard form (Phase 3): the `ω` family over an arbitrary base; this helper is a
fixed polynomial identity with no hypotheses to weaken.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (universal coeff via `Universal.curve` then specialise) | NO | Identity is over the universal Weierstrass ring; `CommRing` is already the floor. `preΨ₄`, `Ψ₂Sq`, `invar` are defined over any `CommRing`. |
| 2 | (no hypotheses)        | unconditional     | unconditional        | n/a                 | Nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (over `CommRing R`, no removable hypotheses).
Number of weakening opportunities: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | bundled hyps → typeclasses? | no | already a typeclass-only signature (`[CommRing R]`). |
| 2 | sequences → filters? | no | finite polynomial identity; no limiting notions. |
| 3 | construction → universal property? | no | it is an equation, not a construction. |
| 4 | subset-predicate → bundled substructure? | no | n/a. |
| 5 | field/metric → module/(semi)ring weakening? | no | already `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | n/a. |
| 7 | concrete index → general monoid? | no | no free index in the statement (the `n`-dependence lives in the *consumer* `ω_spec`, not here). |

Modern idiom available: **no**. One-line reason: this is a fixed finite algebraic identity over the
most general sensible coefficient ring; there is no contemporary reformulation that reorganises it.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

## Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a — index tool not reachable in this environment (offline build).
[B] Loogle            type-pattern `?a + _ ^ 4 = _` around `preΨ₄`/`ψ₂` → no `preΨ₄ + ψ₂⁴` lemma
                      (confirmed via web loogle + the grep below, which is definitive on the pinned tree).
[C] LeanSearch        "preΨ₄ plus ψ₂ to the fourth identity" / "omega division polynomial spec" →
                      only the `ψ₄ = preΨ₄·ψ₂` family surfaces; no hit.
[D] Grep mathlib src  `grep -rn "preΨ₄" .lake/packages/mathlib/Mathlib/` → **17 hits, all in
                      `DivisionPolynomial/Basic.lean` + `Degree.lean`**: the *definition* and the
                      `Ψ_four`/`ψ_four`/`Φ_three`/`Φ_four`/degree lemmas. **No lemma relating
                      `preΨ₄ + ψ₂⁴`.** `grep -rn "preΨ₄_add\|_add_ψ₂_pow\|add_Ψ₂Sq"` → **0 hits**.
                      `grep "compl₂EDS\|redInvarDenom\|invarDenom\|redInvar\b\|redInvar_normEDS\|
                      compl₂EDS_eq_redInvarNum_sub"` over mathlib → **0 hits** (the whole `redInvar`
                      machinery this lemma feeds is absent; mathlib has `complEDS₂`/`complEDS`, a
                      *different, partial* track without the invariant-numerator/denominator API).
[E] Name pattern      `def invar`/`.invar` in mathlib → only unrelated `invariants`/`invariantExtension`
                      in RepresentationTheory/Analysis; **no Weierstrass `invar`**. ω: `grep`/WebFetch
                      → mathlib has **no `ω`/omega division polynomial** (documented TODO).

Searched for both:
  - the user's current form (`preΨ₄ + ψ₂⁴ = invar·Ψ₃ + …`) — absent;
  - the literature-standard surrounding object (`ω`, `4y·ω = …`) — absent (mathlib TODO).

Concluded: **not in mathlib** (all available methods exhausted; the live mathlib docs confirm `ω`
and its supporting `invar`/`redInvar` machinery are an open TODO, and grep over the pinned source is
definitive that `preΨ₄_add_ψ₂_pow_four` does not exist).

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four`

Internal use count (this project, excluding the declaring file): **0**.
External callers (other AINTLIB projects): **1 file** — HasseWeil has a **byte-identical copy** of
the lemma + an identical use.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:84` | `rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, …]` — sole consumer, inside `ω_spec` (same file). |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:82` | **duplicate declaration** of the same lemma (same statement, same proof). |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:104` | identical use inside that project's `ω_spec`. |

Inline-derivation grep: the lemma is **not** re-derived inline anywhere else; the two occurrences
are the two parallel forks of Junyan Xu's omega-polynomial development (one renames mathlib's
`complEDS₂`→`compl₂EDS`, the other keeps `complEDS₂`). So across AINTLIB this identity is genuinely
duplicated, signalling shared upstream provenance rather than two independent needs.

Composability signal: it is consumed **exactly once** within its own file (a `rw` step in
`ω_spec`), and the parallel project simply re-states it. Per the call-sites table that is a
"K = 1 internal use" pattern → leans toward "could be inlined into `ω_spec`" rather than "needs to
exist as public API" — **but** see the heuristic table below: it is a non-trivial `ring`
sub-derivation that genuinely earns extraction from the long `ω_spec` proof.

### Composition check

Can `preΨ₄_add_ψ₂_pow_four` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1: `by rw [ψ₂_sq, ...]; ring` using only mathlib.
  - Mathlib decls available: `ψ₂_sq`, `Ψ₂Sq`, `C_pow`, `C_add`, `b_relation`, `add_sq` — all exist.
  - Missing: the sibling identity `preΨ₄_add_Ψ₂Sq_sq` (`preΨ₄ + Ψ₂Sq² = invar·Ψ₃`) is **itself
    project-local** (it references the **project-local** `invar`, which mathlib does not have), and
    the RHS of the target literally contains `W.invar` — a non-mathlib symbol. You cannot even
    *state* the lemma in current mathlib, let alone prove it in ≤3 calls.
  - Result: **fails** — not a mathlib composition; it is a real `ring`/`linear_combination`
    derivation through two project-local lemmas and a project-local definition.

Conclusion: **NOT-COMPOSABLE** from mathlib (≤3 calls). The proof is a genuine algebraic
computation, and its statement depends on the project-local `invar`.

## Verdict: `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *surrounding* `ω` machinery is standard and is an **explicit
  mathlib TODO**, but this specific `preΨ₄ + ψ₂⁴` identity has **no name in the literature** — it is
  internal `bᵢ`-level scaffolding.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (over `CommRing R`); no modernisation move.
- Mathlib search (Phase 5): **not in mathlib**; moreover the whole `invar`/`redInvar`/`ω` track it
  serves is absent (documented TODO).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib in ≤3 calls — and not even
  *statable* in mathlib, since its RHS uses the project-local `invar`.

**Rationale:**

This lemma sits in an awkward spot that the five buckets don't cleanly resolve, so the honest
verdict is BORDERLINE. On one hand it is clearly **not** a NO bucket: mathlib does not have it
(Phase 5, definitive grep), and it is not a ≤3-call mathlib composition (Phase 6) — it is a real
`ring` derivation whose statement even *mentions* a symbol (`invar`) mathlib lacks. On the other
hand it is **not** a clean `YES-add-as-is` either: it is an **unnamed intermediate identity** whose
only role is one `rw` step inside `ω_spec`, it is not a literature-named result, and — decisively —
it **cannot be PR'd on its own**, because both its right-hand side (`invar`) and its downstream
consumer (`ω`, `ψc`, `redInvarDenom`, `compl₂EDS_eq_redInvarNum_sub`, `redInvar_normEDS`) are part
of the larger omega-polynomial development that mathlib explicitly lists as `TODO: the bivariate
polynomials ωₙ`.

So the real question is not "is this lemma true and useful" (it is) but **"at what grain, and by
whom, should the omega-polynomial development enter mathlib?"** — a PR-grouping and ownership
judgment the skill should not make unilaterally. The strong recommendation is: this lemma belongs in
mathlib **only as part of the `ω` PR** that closes the existing `DivisionPolynomial/Basic.lean`
TODO (most naturally as a `private`/`local` helper, or inlined into `ω_spec`, since it is consumed
once). The fact that it is **byte-identically duplicated** in two AINTLIB projects (NagellLutz and
HasseWeil) confirms shared upstream provenance — this is Junyan Xu / David Angdinata's omega-
polynomial work (the file header credits exactly them, and they are mathlib's
division-polynomial authors). Upstreaming should be coordinated with that effort, not done
piecemeal from a fork.

**Numbered questions (≤5):**

1. Should the omega-polynomial development (`ω`, `ψc`, `invar`, and the `redInvar`/`compl₂EDS`
   machinery in the forked `EllipticDivisibilitySequence.lean`) be upstreamed to mathlib **as one
   coordinated PR** closing the `DivisionPolynomial/Basic.lean` "TODO: the bivariate polynomials
   ωₙ"? (If yes, this lemma rides along with it and is **not** assessed standalone.)
2. Is AINTLIB the right vehicle to upstream this, or should it be left to the original authors
   (Junyan Xu / David Angdinata, who wrote both this file and mathlib's division-polynomial files)?
   The file header credits them; coordinating avoids a duplicate-effort collision.
3. Within such a PR, should `preΨ₄_add_ψ₂_pow_four` be a **named public lemma**, a **`private`
   helper**, or **inlined into `ω_spec`**? It has a single consumer and no literature name, so
   `private`/inlined is the likely mathlib-style choice — confirm the preference.
4. The two AINTLIB copies have **diverged in naming** (`compl₂EDS` vs mathlib-style `complEDS₂`).
   Before any upstreaming, should these forks be reconciled to mathlib's existing `complEDS₂`
   spelling so the omega track sits cleanly on top of what mathlib already has?

**Next action:** user answers Q1–Q4. Most likely resolution: **bundle into the `ω`/omega-polynomial
mathlib PR** (closing the existing TODO), as a `private`/inlined helper, coordinated with the
upstream authors — at which point this decl's standalone verdict is moot. If instead the user wants
it assessed as a standalone public contribution, re-run with that framing; absent the surrounding ω
machinery it is not independently mathlib-shippable (its statement references the non-mathlib
`invar`).

---

## Next step

Answer the four numbered questions above. The default recommendation is to upstream the **whole
omega-polynomial development as one coordinated PR** that closes mathlib's
`DivisionPolynomial/Basic.lean` `ωₙ` TODO — with this lemma as a `private`/inlined helper inside it,
in coordination with the original authors — rather than treating `preΨ₄_add_ψ₂_pow_four` as a
standalone mathlib target.
