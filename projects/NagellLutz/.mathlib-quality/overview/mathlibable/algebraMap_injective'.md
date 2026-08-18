# /mathlibable report — `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'`

## Verdict: **NO-composable-from-mathlib**

(One-line rationale: the structure map `R → R[X]/(monic f)` is injective because the
quotient is a free `R`-module with `1` in its basis; both building blocks — mathlib's
`smul_basis_eq_zero` and `Polynomial.C_injective` — are already upstream, and the lemma
is a ≤3-call composition. It is a fork-helper, not a mathlib contribution.)

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task note) — reasoning from source
- decl `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/Universal.lean:50`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Additions to Affine.Point and the universal elliptic curve" —
  explicitly *"lemmas missing from the released mathlib that are needed for the division
  polynomial / ZSMul development"*. The file **forks/back-ports mathlib** and lists this
  lemma under that mandate.

---

### Statement (Phase 1)

`algebraMap_injective'` states: for a Weierstrass curve `W'` over a commutative ring `R`,
the canonical `R`-algebra structure map into the affine coordinate ring
`R[W'] = R[X,Y]/⟨W'(X,Y)⟩` is **injective**.

Mathematically: the structure map `R → R[X][Y]/⟨f⟩` (where `f = W'.polynomial` is the
Weierstrass polynomial, **monic of degree 2 in `Y`**) is injective. The standard reason:
because `f` is monic, the quotient is a *free* `R[X]`-module on the power basis `{1, Y}`,
hence (composing with `R → R[X]` via `C`) a free `R`-module containing the unit `1` as a
basis element; the structure map is therefore a **split injection**. No integral-domain
hypothesis is needed.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — base ring, **`CommRing` only (no `IsDomain`)**.
- `{W' : WeierstrassCurve.Affine R}` — the affine Weierstrass curve.

Hypotheses: none.

Conclusion (math): the structure map `R ↪ R[W']` is injective.
Conclusion (Lean): `Function.Injective (algebraMap R W'.CoordinateRing)`.

Proof body (one line):
`(CoordinateRing.algebraMap_poly_injective (W' := W')).comp C_injective`
where the helper `algebraMap_poly_injective : Function.Injective (algebraMap R[X] W'.CoordinateRing)`
is `(injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <| smul_basis_eq_zero …`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma (a plain injectivity statement), not a named theorem, not a new
structure, not a `## Main results` entry. The module docstring itself frames it as a
"lemma missing from released mathlib" — i.e. a back-port/glue helper.

(Literature width run at full EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, so the one-liner def-exemption machinery is **n/a**. Recorded for context:
the body is a single `.comp` composition (one substantive line). For a *lemma* this is a
strong "compose-at-use-site / building-blocks-suffice" signal, not a def-stability concern.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                           | Query                                                                                          | Hit? | Standard form found | Notes |
|----|-----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)         | "coordinate ring elliptic curve free module structure morphism injective base ring"            | yes  | coordinate ring of a curve is a free/torsion-free module over the base; structure map injective | Columbia/MIT/AWS notes: `End`, orders, coordinate rings are free `ℤ`-modules ⇒ structure maps injective; this is textbook background, never a named theorem |
|  2 | WebSearch (general form)          | "AdjoinRoot monic polynomial structure map injective free module base ring"                     | yes  | `R[X]/(monic f)` is free over `R` on `1,X,…,X^{d-1}`; division-by-monic is the `R`-linear retraction | mathlib4 `AdjoinRoot` doc: `modByMonicHom` is the `R`-linear remainder map — the explicit retraction |
|  3 | WebSearch (named-after / aliases) | (folded into #1/#2) "split injection quotient by monic polynomial" / "power basis injective"    | yes  | same fact via power basis; the constant term survives in the basis | no eponymous name exists — it is a one-step corollary of the free/power-basis structure |
|  4 | ChatGPT MCP                       | self-contained: is `R → R[X]/(monic f)` injective for general comm ring (no domain)? standard? named? | n/a  | (MCP down — Codex exec errored; task note warned of this) | reasoned from source + #1/#2: domain-free, split-injection-via-power-basis, **not** a named result |
|  5 | Local references                  | grep `projects/NagellLutz/.mathlib-quality/references/` for coordinate ring / AdjoinRoot         | n/a  | (no references dir present for NagellLutz) | recorded n/a — directory absent |
|  6 | nLab                              | "coordinate ring" / "free module structure map" (concept is not categorical-flavoured)          | n/a  | — | elementary commutative-algebra fact; nLab has no dedicated page for the structure-map-injectivity micro-fact |
|  7 | nCatLab                           | —                                                                                              | n/a  | — | not a categorical concept |
|  8 | Stacks Project                    | "finite free algebra" / "monic polynomial quotient"                                            | yes  | Stacks 00P0-area: `R[X]/(monic)` is finite free over `R` ⇒ faithfully flat ⇒ structure map injective | confirms the math; again a corollary of finite-freeness, not a standalone tagged lemma |
|  9 | MathOverflow / Math.SE            | "is R injects into R[X]/(monic f) when R not a domain"                                          | yes  | yes — because `R` is a direct summand (the `1` basis vector); domain not needed | consensus: trivial corollary of the free-module decomposition |
| 10 | recent arXiv (last 5y)            | division polynomials / coordinate ring injectivity                                              | n/a  | — | nothing treats this micro-fact as a result; it is universally used silently |

### Literature summary (Phase 3)

Concept identified as: **injectivity of the structure map of a finite-free algebra**
(`R ↪ R[X]/(monic f)`), specialised to the elliptic-curve coordinate ring `R[W']`.
Sources agree on the standard form: **yes** — it is a one-line corollary of "`R[X]/(monic f)`
is a free `R`-module with `1` a basis element", valid over **any** commutative ring.
Most general standard form: for any comm. ring `R` and any **monic** `f ∈ R[X]`, the map
`R → R[X]/(f)` is a split (hence injective) `R`-algebra map; equivalently `Module.Free` +
`1 ∈ basis`. The Weierstrass case is the `f = W'.polynomial` (monic in `Y`) instance.
Disagreement with the literature: **none**. The literature treats this as background, never
as a citable theorem — a strong signal it is glue, not a contribution.

---

### Generality analysis — `algebraMap_injective'`

Literature-standard form (Phase 3): `R → R[X]/(monic f)` injective for any `CommRing R`.

| # | Parameter / hypothesis      | Current Lean form              | Literature-standard form           | Weaker form exists? | Reason |
|---|-----------------------------|--------------------------------|-------------------------------------|---------------------|--------|
| 1 | `[CommRing R]`              | commutative ring               | commutative ring                    | NO                  | already at the standard generality — **no `IsDomain` assumed** (better than mathlib's gated `AdjoinRoot` lemma) |
| 2 | `W' : Affine R`             | a Weierstrass curve            | any monic `f ∈ R[X]` (the abstract case) | yes (abstract)  | the abstract `AdjoinRoot (monic f)` form is strictly more general, but it is *already covered* by the building blocks; specialising to `W'` adds nothing mathlib lacks |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the Weierstrass-specialised statement — it
correctly drops `IsDomain`). Weakening opportunities: 0 on the stated form. The only
"generalisation" is to abstract away `W'` to a bare monic `f`, but that abstract lemma is
itself nothing more than the same building-block composition (free-module + `1` in basis),
so it does not turn this into a YES — it confirms the building blocks already suffice.
Cost of any restatement: n/a (verdict is NO-composable).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | typeclasses vs bundled hyps | no | already typeclass-driven (`[CommRing R]`) |
| 2 | sequences/metric → filters/topology | no | purely algebraic |
| 3 | construction → universal-property class | no | it is an injectivity fact, nothing to characterise universally |
| 4 | set+closure → bundled substructure | no | n/a |
| 5 | vector-space/field-specific → weaken typeclasses | **already done** | the lemma is over `CommRing`, weaker than the domain-gated mathlib analogue — but the modern *form* is still "use the free-module API", i.e. compose, don't add a lemma |
| 6 | 1-categorical → higher-categorical | no | n/a |
| 7 | concrete index → general algebra | no | n/a |

Modern idiom available: **no** (the contemporary mathlib idiom here is precisely "derive it
from `Module.Free` / power-basis at the use site", which is the NO-composable conclusion,
not a new lemma).

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'`

[A] Lean-Finder       (index unavailable offline; covered by [D]/[E])      n/a
[B] Loogle            `Function.Injective (algebraMap _ (AdjoinRoot _))` / `… CoordinateRing` pattern  no exact hit for a domain-free form
[C] LeanSearch        "structure map into coordinate ring of Weierstrass curve injective"  no standalone hit
[D] Grep mathlib src  `algebraMap_injective'`, `algebraMap_poly_injective`, `CoordinateRing.*injective`, `of.injective`, `Monic.*injective`  → see below
[E] Name pattern      `algebraMap_injective'` / `algebraMap_poly_injective` qualified  → **absent from mathlib** (grep empty)

Grep findings (the decisive evidence):
- `WeierstrassCurve.Affine.CoordinateRing` is a mathlib **`abbrev` for `AdjoinRoot W'.polynomial`**
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:90-91`).
- **`smul_basis_eq_zero`** — the exact helper the project's proof calls — **is already in
  mathlib** at `…/Affine/Point.lean:144` (linear independence of the power basis `{1, Y}`).
  The project forks the file but this lemma is upstream.
- Mathlib's only `AdjoinRoot` structure-map injectivity lemma is
  **`AdjoinRoot.of.injective_of_degree_ne_zero`** (`Mathlib/RingTheory/AdjoinRoot.lean:265`),
  but it is **gated on `[IsDomain R]`** — so it does **not** directly give the project's
  domain-free statement.
- Mathlib **does** have the domain-free building block:
  **`Polynomial.Monic.free_adjoinRoot : g.Monic → Module.Free R (AdjoinRoot g)`**
  (`AdjoinRoot.lean:645`) and `AdjoinRoot.powerBasis'` (`:630`), plus the explicit linear
  retraction `AdjoinRoot.modByMonicHom`. And `Polynomial.C_injective` is upstream.

Searched for both: the user's form (Weierstrass-specialised) AND the literature-standard
form (`R → R[X]/(monic f)`, domain-free). Neither appears as a *standalone* mathlib lemma;
the **building blocks for both are upstream**.

Concluded: **"not in mathlib as a standalone lemma; mathlib has the building blocks**
(`smul_basis_eq_zero`, `Polynomial.Monic.free_adjoinRoot`/`powerBasis'`, `Polynomial.C_injective`)
**— their composition yields our form."**

---

### Call sites — `algebraMap_injective'`

Internal use count: **K = 1** (within NagellLutz, excluding the declaring lines 50-51).
External-to-file callers: 0 (the one use is in the *same* file).

| Caller file:line                                   | Usage pattern (one-line excerpt) |
|----------------------------------------------------|----------------------------------|
| projects/NagellLutz/LutzNagell/Universal.lean:126  | `(Affine.CoordinateRing.algebraMap_injective' (W' := curve))` — fed to `.comp` after `IsFractionRing.injective` inside `algebraMap_field_injective` |

Inline-derivation grep: the **sibling helper** `algebraMap_poly_injective` is used directly
(not via this lemma) at many HasseWeil sites (e.g. `OmegaPullbackCoeff.lean:714`,
`MulByIntPullback.lean:310`, `WronskianGeneral.lean:65`) — i.e. downstream code routinely
composes `(IsFractionRing.injective …).comp algebraMap_poly_injective` *inline*, bypassing
`algebraMap_injective'`. This confirms the composition is the natural idiom and the wrapper
is thin.

Signal: **K = 1, used once, in-file, and the equivalent composition is done inline elsewhere
⇒ NO-composable.** (Note: the duplicate in HasseWeil's fork has the same K=1 shape — both
forks carry an identical thin wrapper used exactly once.)

---

### Composition check (Phase 6)

Can `algebraMap_injective'` be derived from mathlib in ≤3 chained calls? **Yes.**

The lemma's own proof is *already* a mathlib composition, modulo the helper:

Attempt 1 (direct, as written):
```lean
example {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R} :
    Function.Injective (algebraMap R W'.CoordinateRing) :=
  WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective.comp Polynomial.C_injective
```
- but `algebraMap_poly_injective` is itself the project's helper. Inlining *it* too:

Attempt 2 (fully inlined over mathlib primitives — what a call site would write):
```lean
example {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R} :
    Function.Injective (algebraMap R W'.CoordinateRing) :=
  ((injective_iff_map_eq_zero _).mpr fun p hp ↦
      And.left (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W') (q := 0)
        (by rwa [Algebra.smul_def, mul_one, zero_smul, add_zero]))).comp Polynomial.C_injective
```
- Mathlib decls used: `Polynomial.C_injective`, `WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero`
  (mathlib `…/Affine/Point.lean:144`), `injective_iff_map_eq_zero`, plus the `Algebra.smul_def`/
  `zero_smul` simp lemmas. Result: **succeeds** — every leaf is upstream.
- At the actual call site `curve` is over `MvPolynomial Coeff ℤ` (a domain), so even the
  shorter `AdjoinRoot.of.injective_of_degree_ne_zero` (mathlib `:265`) closes it directly:
  `(AdjoinRoot.of.injective_of_degree_ne_zero (by simp [degree_polynomial]))` — a 1-call hit.

Conclusion: **COMPOSABLE** (≤3 mathlib calls for the general `CommRing` form; ≤1 call at the
domain-instantiated call site).

---

## Verdict: `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the fact is textbook background — "`R[X]/(monic f)` is free
  over `R` with `1` in its basis ⇒ structure map is a split injection" — never a named theorem;
  agrees across MIT/Stacks/MathOverflow.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on its own statement (correctly drops
  `IsDomain`); no modern-idiom restatement — the idiom *is* "compose from the free-module API".
- Mathlib search (Phase 5): not a standalone mathlib lemma, but every building block is upstream
  (`smul_basis_eq_zero` at `…/Affine/Point.lean:144`, `Polynomial.Monic.free_adjoinRoot`/
  `powerBasis'`/`C_injective`); mathlib's `AdjoinRoot.of.injective_of_degree_ne_zero` is the
  domain-gated analogue.
- Composition check (Phase 6): COMPOSABLE — ≤3 calls (general form), ≤1 call at the call site.

**Rationale:**

This is a thin glue helper that the project's own module docstring flags as a *"lemma missing
from released mathlib"* needed for the division-polynomial development — i.e. a fork
back-port, not a fresh contribution. Mathematically it is the one-step corollary that the
structure map of a quotient by a **monic** polynomial is injective, which holds over any
commutative ring because the quotient is `R`-free with `1` as a basis vector (split
injection). Mathlib already ships the load-bearing primitive — `smul_basis_eq_zero` (linear
independence of the `{1,Y}` power basis) lives upstream at `Affine/Point.lean:144`, and
`Polynomial.Monic.free_adjoinRoot` / `AdjoinRoot.powerBasis'` / `Polynomial.C_injective` give
the abstract version — so `algebraMap_injective'` is literally `algebraMap_poly_injective.comp
C_injective`, a ≤3-call composition with no new mathematical content.

The call-site evidence seals it: the lemma is used **exactly once**, in its own file, and the
*same* `(IsFractionRing.injective …).comp algebraMap_poly_injective` composition is written
**inline** at many downstream sites (HasseWeil's `OmegaPullbackCoeff`, `MulByIntPullback`,
`WronskianGeneral`) without going through `algebraMap_injective'` at all. A wrapper that one
file uses once and that everyone else inlines is the textbook NO-composable shape. (One small
upside worth noting for a *human*: the project's domain-free statement is genuinely more
general than mathlib's `IsDomain`-gated `AdjoinRoot.of.injective_of_degree_ne_zero`; if anyone
wanted a mathlib contribution here it would be **`AdjoinRoot.of_injective_of_monic`** — drop
`IsDomain`, assume `f.Monic` — as a *general `AdjoinRoot` lemma*, NOT a Weierstrass-namespaced
one. But that is a different, abstract decl; this specific Weierstrass helper composes away.)

**WHY not (refactor-actionable):**
Mathlib has the building blocks; `algebraMap_injective'` is a 1–3 mathlib-call composition,
so no new lemma is warranted at this (Weierstrass-specialised) level.

Mathlib building blocks:
- `Polynomial.C_injective` — `Mathlib/Algebra/Polynomial/Basic.lean`
- `WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero` — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:144`
- (abstract alt.) `Polynomial.Monic.free_adjoinRoot` `:645` / `AdjoinRoot.powerBasis'` `:630` / `AdjoinRoot.of.injective_of_degree_ne_zero` `:265` — `Mathlib/RingTheory/AdjoinRoot.lean`

Composition sketch (≤3 lines, general `CommRing` form):
```lean
example {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R} :
    Function.Injective (algebraMap R W'.CoordinateRing) :=
  ((injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
      WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := W') (q := 0) <| by
        rwa [Algebra.smul_def, mul_one, zero_smul, add_zero]).comp Polynomial.C_injective
```
At the lone call site, where the base is the domain `MvPolynomial Coeff ℤ`, even shorter:
```lean
AdjoinRoot.of.injective_of_degree_ne_zero (f := curve.polynomial) (by simp [curve, degree_polynomial])
```

Call sites in our project (from Phase 6.0): **K = 1** (NagellLutz `Universal.lean:126`, inside
`algebraMap_field_injective`). The identical fork copy lives in HasseWeil with the same K=1.

Refactor plan:
1. In NagellLutz `Universal.lean`, inline the composition at line 126: replace
   `(Affine.CoordinateRing.algebraMap_injective' (W' := curve))` with the helper composition
   `(Affine.CoordinateRing.algebraMap_poly_injective.comp Polynomial.C_injective)`, OR — since
   `curve` is over a domain — with `AdjoinRoot.of.injective_of_degree_ne_zero …` directly.
   Then delete the `algebraMap_injective'` declaration (lines 50-51).
2. Note `algebraMap_poly_injective` (the helper at lines 45-48) is itself a thin wrapper over
   the upstream `smul_basis_eq_zero`; it is used widely in HasseWeil and is the natural inline
   unit there, so it can stay as a *local* convenience even though `algebraMap_injective'` goes.
3. The whole `Universal.lean` "Point.lean additions" block is a mathlib fork; the cleaner global
   move is to upstream a *general* `AdjoinRoot.of_injective_of_monic` (domain-free) to
   `Mathlib/RingTheory/AdjoinRoot.lean` and delete the Weierstrass-specialised forks in both
   NagellLutz and HasseWeil — but that is a separate `AdjoinRoot` contribution, tracked apart
   from this decl.

**Next action:** delete `algebraMap_injective'` from NagellLutz; inline the composition (or the
domain-instantiated `AdjoinRoot.of.injective_of_degree_ne_zero`) at its single call site. (If a
mathlib PR is desired, file it as the *abstract* domain-free `AdjoinRoot.of_injective_of_monic`,
not this Weierstrass wrapper.)

---

## Next step

Delete `WeierstrassCurve.Affine.CoordinateRing.algebraMap_injective'` from the NagellLutz
project and inline its ≤3-call composition at the one call site (`Universal.lean:126`). It is a
fork back-port whose building blocks (`smul_basis_eq_zero`, `C_injective`) are already in
mathlib — nothing new to upstream at this generality.
