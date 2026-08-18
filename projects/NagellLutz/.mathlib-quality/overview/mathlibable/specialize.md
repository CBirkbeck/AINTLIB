# /mathlibable report — `WeierstrassCurve.specialize`

## Verdict: BORDERLINE-needs-human

One-line, but it is the named anchor of a universal-curve API mathlib flags as missing (the `ωₙ` TODO). Upstreaming it is a packaging call on the whole `Coeff`/`Universal.curve`/`polyEval`/`ringEval` scaffold.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task); decl read from source.
- decl `WeierstrassCurve.specialize`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:190`
- kind:                      `def` (noncomputable section)
- has sorry:                 no
- qualified name:            **`WeierstrassCurve.specialize`** (file is inside `namespace WeierstrassCurve`, lines 69–243; `variable {R} [CommRing R] (W : WeierstrassCurve R)` at line 186; used as `W.specialize`). Task's parsed name confirmed.
- module docstring summary:  Additions to `Affine.Point` and the universal elliptic curve (forked from Junyan Xu) for the division-polynomial / ZSMul development; defines `Universal.curve` over `ℤ[A₁..A₆]` and the specialization machinery `specialize` / `polyEval` / `ringEval`.

---

### Statement (Phase 1)

`WeierstrassCurve.specialize` is a **definition**: given a Weierstrass curve `W` over a commutative ring `R`, it is the ring homomorphism

  `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R`

obtained from the universal property of the polynomial ring `MvPolynomial Coeff ℤ` (where `Coeff` is the 5-element index type `{A₁,A₂,A₃,A₄,A₆}`) by sending each indeterminate `Aᵢ` to the corresponding coefficient `W.aᵢ` of `W`. Mathematically: the unique ℤ-algebra map evaluating the five Weierstrass indeterminates at `W`'s coefficients. Pushing the universal curve `Universal.curve` forward along it recovers `W` (lemma `map_specialize`).

Body (one substantive line):
```lean
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom
```

Variables / typeclasses:
- `{R : Type*}` `[CommRing R]` — the base ring (arbitrary commutative ring).
- `(W : WeierstrassCurve R)` — the curve whose coefficients are the evaluation targets.

Hypotheses: none.

Conclusion (math): the coefficient-evaluation ℤ-algebra homomorphism `ℤ[A₁..A₆] → R`.
Conclusion (Lean): `MvPolynomial Coeff ℤ →+* R` — n/a, it is a definition.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper `def` wrapping `MvPolynomial.aeval`; not a new mathematical structure, not a named theorem, not a project main result (the main result is the Nagell–Lutz theorem; this is plumbing for the universal-curve track). It *is* part of a BIG-ish ensemble — the universal curve `Universal.curve` and its evaluation maps — but the decl itself is small.

(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line**.
One-liner verdict: **ONE-LINER**.

Exemption check:
| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | **no**   | `specialize` is NOT `@[reducible]`, but downstream proofs deliberately *unfold* it: `map_specialize := by simp [specialize, …]` and `polyEval_comp_eq_specialize := by ext <;> simp [polyEval]` rely on it reducing to `aeval`. It is used as a transparent alias, not as a sealed barrier — so the "defeq barrier" rationale does not apply. |
| Avoid typeclass diamonds         | **no**   | No instance/typeclass is keyed on it; it is an ordinary `→+*` term, no `Mul`/`Zero`/`AddCommMonoid` collision. |
| Mark semantic intent / API name  | **yes (weak)** | The name + docstring *is* the API surface for the universal-curve track: `polyEval`, `ringEval`, `map_specialize`, `polyEval_comp_eq_specialize`, `ringEval_comp_eq_specialize` all reference `W.specialize`. Renaming/inlining would touch ≥5 sites. But every consumer is itself inside the same not-yet-upstreamed scaffold. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name only, and that exemption is weak because all consumers live in the same un-upstreamed package).

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | universal Weierstrass curve ring ℤ[a1..a6] specialization homomorphism EDS | yes | ring `A = ℤ[a₁..a₆]` parametrising Weierstrass curves; universal curve `𝓔 → Spec(A)⁰`; a Weierstrass curve is the pushforward of the universal one along a ring hom `A → R` | Katz "Weierstrass families" notes; confirms the *concept* but the ring hom is described as "the mechanism for specialization", not a named object. |
| 2 | WebSearch (general form) | "universal elliptic curve" coeff ring ℤ[a1..a6] every elliptic curve is a specialization division polynomial | yes | division polynomials `Ψₙ ∈ ℤ[a₁..a₆,x,y]`; "any particular curve obtained as a specialization of the universal family" by specializing the parameters in any ring | The universal property is the content; valid over an arbitrary ring. |
| 3 | WebSearch (named-after / aliases) | Silverman "specialization map"/"specialization homomorphism" definition coefficient ring evaluation | yes | In Silverman the **"specialization homomorphism" is `σ_{t₀}: E(ℚ(t)) → E_{t₀}(ℚ)`** — the map *on points/sections* of an elliptic surface, and the named theorem is its **injectivity** for all but finitely many `t₀`. | **Key:** the standard named "specialization homomorphism" is NOT this coefficient-evaluation ring hom. The project reuses the word for a different (trivial) map. |
| 4 | ChatGPT MCP | (self-contained question on whether the coeff-evaluation ring hom is a named standard object and whether its definition exceeds the polynomial-ring universal property) | **n/a** | — | MCP server down in this environment (Codex exec failed), as the task warned. Compensated with extra WebSearch + direct mathlib-source reading. |
| 5 | Local references | `.mathlib-quality/references/` for NagellLutz | n/a | (directory absent) | No `references/` dir under `projects/NagellLutz/.mathlib-quality/`. |
| 6 | nLab | moduli stack of elliptic curves / Weierstrass | yes | "moduli stack of elliptic curves"; universal curves over moduli/parameter spaces "by definition" | nLab treats the universal curve over the moduli stack; the affine coefficient-ring evaluation map is not singled out as a named morphism. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept beyond #6; the map is the universal property of a free ℤ-algebra. |
| 8 | Stacks Project (alg geom) | universal Weierstrass curve over ℤ[a1..a6] / stack of curves (tag 0DMJ) | partial | the stack of curves / Weierstrass data = line bundle + sections of `L⁴,L⁶` | Stacks discusses Weierstrass data abstractly; the bare affine evaluation hom `ℤ[a₁..a₆] → R` is not a named tag — it is `Spec R → 𝔸⁵` / the universal property of a polynomial ring. |
| 9 | MathOverflow / MSE | universal elliptic curve coefficient ring specialization generality | yes (via #1,#2) | consistent: specialization = specializing parameters; valid over any commutative ring | No disagreement on generality. |
| 10 | recent arXiv (≤5 yr) | injectivity of the specialization homomorphism of elliptic curves; recurrence for EDS; division polynomials | yes | arXiv:1409.7189, arXiv:2102.07573, etc. — all use "specialization homomorphism" for the **points** map and study its injectivity; division-polynomial papers use `ℤ[a₁..a₆,x,y]` as the universal coefficient ring. | Reconfirms #3: the named object in the literature is the points-map, not this ring hom. |

### Literature summary (Phase 3)

Concept identified as: the **coefficient-evaluation / universal-property ring homomorphism** `ℤ[A₁..A₆] →+* R` of the polynomial ring, sending the five Weierstrass indeterminates to a curve's coefficients (equivalently the classifying map `Spec R → 𝔸⁵_ℤ` of the Weierstrass data; the comorphism of "every Weierstrass curve is the pushforward of the universal one").
Sources agree on the standard form: **yes** on the *concept* (universal curve over `ℤ[a₁..a₆]`, valid over an arbitrary commutative ring). **But** the *name* "specialization homomorphism" in the standard literature (Silverman) denotes a **different** map — `E(ℚ(t)) → E_{t₀}(ℚ)` on points — whose named theorem is injectivity. The project's `specialize` is the (un-named-in-the-literature) coefficient-evaluation ring hom.
Most general standard form: for any `CommRing R` and any Weierstrass curve `W/R`, the unique ℤ-algebra map `ℤ[A₁..A₆] → R` with `Aᵢ ↦ W.aᵢ`. Nothing about the *definition* needs a field or domain.
Generality dimensions where the literature varies:
  - base `R`: ranges from `field` (in arithmetic applications) to `arbitrary commutative ring` (for the universal property); the most general is **arbitrary commutative ring** — and the project already uses that.
Disagreement with the literature: the *definition* carries no mathematical content beyond the polynomial-ring universal property; the literature's *named* "specialization homomorphism" is a heavier object (the points map) that this decl is not.

---

### Generality analysis — `WeierstrassCurve.specialize` (Phase 4)

Literature-standard form (from Phase 3): the unique ℤ-algebra hom `ℤ[A₁..A₆] → R`, `Aᵢ ↦ W.aᵢ`, for an arbitrary commutative ring `R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | arbitrary comm. ring | arbitrary comm. ring | **NO** | already maximally general; the universal property needs only `CommRing` (and ℤ is initial, so no further weakening). |
| 2 | `(W : WeierstrassCurve R)` | bundled curve | tuple of 5 coefficients | borderline | could be phrased on a raw 5-tuple `Coeff → R`, but bundling on `WeierstrassCurve` is the right mathlib idiom and is what `map_specialize` needs. Not a weakening. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (arbitrary `CommRing R`; the definition has no superfluous hypotheses).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclass/instance? | no | — | already an unbundled `def` of a `→+*`; nothing to classify. |
| 2 | sequences/metric → filters/topology? | no | — | no limiting/topological content. |
| 3 | construct an object → universal-property class? | **partially** | This map *is* the universal property of `MvPolynomial Coeff ℤ`. The "modern idiom" is exactly: don't give it a curve-specific name — call `MvPolynomial.aeval (Coeff.rec W.a₁ … W.a₆)` (`AlgHom`) and `.toRingHom` where a bare `→+*` is needed. | Inheriting the full `MvPolynomial.aeval` API (`aeval_X`, `aeval_C`, `comp_aeval`, …) for free rather than re-deriving via the named alias. |
| 4 | set+closure-predicate → bundled substructure? | no | — | — |
| 5 | field/metric-specific → weaken typeclass? | no | — | already on `CommRing`. |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index → general algebraic structure? | no | — | the index `Coeff` is intrinsically the 5 Weierstrass coefficients. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild)** — the contemporary mathlib move is to *use `MvPolynomial.aeval` directly* (it is already an `AlgHom`, the strictly richer object) rather than ship a one-line `→+*` alias. The only thing the named `def` adds over `MvPolynomial.aeval (Coeff.rec …)` is a curve-specific name and docstring. Real improvement: composing with the full `aeval` API. This is an *organisational* observation, not a strong "must generalise" — it pushes toward NO-composable, not toward YES-but-generalise-first (there is no strictly-more-general true statement to prove; the general statement already *is* `aeval`'s universal property).

---

### Diamond / defeq risk — `WeierstrassCurve.specialize` (Phase 4.5; kind = def)

| # | Risk | Verdict | Evidence |
|---|------|---------|----------|
| 1 | Typeclass diamond | **none** | not an instance; produces a plain `→+*` term, no instance-search path introduced. |
| 2 | Reducibility leak | **low** | not `@[reducible]`; semireducible. `simp [specialize]` unfolds it on demand (in `map_specialize`), which is the intended use, not a leak. |
| 3 | Non-canonical unfolding | **low** | unfolds to `(MvPolynomial.aeval …).toRingHom`; predictable. No surprising `rfl`/`simp` behaviour observed in the file. |
| 4 | Instance priority collision | **none** | not an instance. |
| 5 | Universe issues | **none** | `R : Type*`, no forced universe annotation. |
| 6 | Coercion ambiguity | **none** | no `CoeFun`/`CoeSort`; the `.toRingHom` is an explicit forgetful map from `AlgHom`, the standard mathlib coercion already exists. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**. No HIGH rows. (If upstreamed, prefer `aeval`-direct to avoid even the mild reducibility surface — see Phase 4c.)

---

### Mathlib search-status: `WeierstrassCurve.specialize` (Phase 5)

[A] Lean-Finder — n/a (mathlib index tools `lean_loogle`/`lean_leansearch` not exposed in this env; substituted exhaustive source grep over the pinned mathlib `09b373db6e24`).
[B] Loogle — pattern `WeierstrassCurve _ → (MvPolynomial _ _ →+* _)` — **no hits** (grep proxy: no `specialize`/`Specialize`/`universalRing`/`UniversalRing`/`Coeff` anywhere under `Mathlib/AlgebraicGeometry/EllipticCurve/` or `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`).
[C] LeanSearch — NL "specialization homomorphism of a Weierstrass curve from the universal coefficient ring" — n/a (index tool absent); literature-channel covered the NL angle.
[D] Grep mathlib src — terms `specialize`, `universal`, `MvPolynomial.*Weierstrass`, `Coeff`, `baseChange`, `def map` — **partial**: mathlib HAS `WeierstrassCurve.map (f : R →+* A)` (`Weierstrass.lean:231`) and `baseChange [Algebra R A]` (`:236`); `DivisionPolynomial/Basic.lean:36–38` *describes in prose* "the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`" but defines **no** Lean decl for it, and the consumer `ωₙ` is an explicit **TODO**. No named coefficient ring, no `specialize`.
[E] Name pattern — `specialize` on a curve — **no hits** in mathlib (the only `specialize` occurrences are the Lean tactic, unrelated).

Searched for both: the user's form (`ℤ[A₁..A₆] →+* R`) AND the building block (`MvPolynomial.aeval : MvPolynomial σ R →ₐ[R] S₁`, `Eval.lean:585`).

Concluded: **not in mathlib** as a named decl (all channels exhausted, plus the literature-standard general form). The *building block* `MvPolynomial.aeval` IS in mathlib; `WeierstrassCurve.map`/`baseChange` are in mathlib; the curve-specific *named* specialization hom and its universal coefficient ring (`Coeff`, `Universal.curve`) are **not** — and mathlib's own `DivisionPolynomial/Basic.lean` marks the associated universal-morphism machinery as future work.

---

### Call sites — `WeierstrassCurve.specialize` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring lines 190–191 and the docstring line 24): **K = 6**.
External-to-file callers within NagellLutz: **2 files** (`Universal.lean`, `ZSMul.lean`).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/Universal.lean:194` | `Universal.curve.map W.specialize = W` (lemma `map_specialize`) |
| `LutzNagell/Universal.lean:203` | `eval₂RingHom (eval₂RingHom W.specialize x) y` (def `polyEval`) |
| `LutzNagell/Universal.lean:207` | `p.map <| mapRingHom W.specialize` (lemma `polyEval_apply`) |
| `LutzNagell/Universal.lean:216` | `AdjoinRoot.lift (eval₂RingHom W.specialize x) y` (def `ringEval`) |
| `LutzNagell/Universal.lean:226` | `(polyEval W x y).comp (algebraMap _ _) = W.specialize` (lemma `polyEval_comp_eq_specialize`) |
| `LutzNagell/Universal.lean:229` | `(ringEval eqn).comp (algebraMap _ _) = W.specialize` (lemma `ringEval_comp_eq_specialize`) |
| `LutzNagell/ZSMul.lean:129` | `simpa [cusp, polyEval, specialize, curve] using this` (unfolds it in a proof) |

Inline-derivation grep (re-derived without `specialize`?):
  - `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:193–194` — the **identical** `def specialize := (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom`. This is the **same forked file** (both from Junyan Xu's universal-curve development), used the same way in HasseWeil's `DivisionPolynomial.lean`. So the decl is *duplicated across two projects*, reinforcing that it is real shared API — and a cross-project dedup target (Common/) independent of the mathlib question.

Composability signal: **K = 6 internal uses, no inline re-derivation that bypasses it** → real API; consumers depend on it → leans YES-*. Tempered by: every consumer lives inside the same un-upstreamed universal-curve scaffold (`Coeff`, `Universal.curve`, `polyEval`, `ringEval`), none of which is in mathlib.

### Composition check (Phase 6)

Can `WeierstrassCurve.specialize` be reproduced from mathlib in ≤3 calls?

Attempt 1: `(MvPolynomial.aeval (Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆)).toRingHom`
  - Mathlib decls used: `MvPolynomial.aeval` (+ `AlgHom.toRingHom` coercion). The project's own `Coeff` inductive and `Coeff.rec` are **not** mathlib.
  - Result: **succeeds** as a term — this is literally the definition body (1 mathlib call + a recursor on a project-local type).
  - Notes: the composition is trivial *given* the project's `Coeff` type. The non-trivial, non-composable part is the surrounding ensemble — `Coeff`, `Universal.curve : Affine (MvPolynomial Coeff ℤ)`, and `map_specialize` (the theorem that pushforward recovers `W`). Those are not 3-call mathlib compositions.

Conclusion: **COMPOSABLE in isolation** (the bare ring hom = one `aeval` call), but **the meaningful unit is NOT composable** — `specialize` only earns its keep alongside `Universal.curve` + `map_specialize` + `polyEval`/`ringEval`, an ensemble mathlib lacks and explicitly TODOs.

---

## Verdict: `WeierstrassCurve.specialize`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *concept* (universal curve over `ℤ[a₁..a₆]`, every curve a specialization) is standard and valid over any `CommRing`; but the *named* "specialization homomorphism" in Silverman is a different map (on points), so the name doesn't anchor a literature object. The definition carries no content beyond the polynomial-ring universal property.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (arbitrary `CommRing R`); Phase 4c notes a mild modern-idiom pull toward using `MvPolynomial.aeval` directly (no stronger statement to prove).
- Mathlib search (Phase 5): NOT in mathlib as a named decl; mathlib has the building block (`MvPolynomial.aeval`) and `WeierstrassCurve.map`/`baseChange`, and `DivisionPolynomial/Basic.lean` describes this exact universal morphism in prose with the consumer `ωₙ` marked TODO.
- Composition check (Phase 6): COMPOSABLE in isolation (one `aeval` call) but the useful unit — `specialize` + `Coeff` + `Universal.curve` + `map_specialize` — is NOT composable from mathlib.

**Rationale:**

Two honest readings pull opposite ways, and choosing between them is a scope/packaging judgment, not a mathematical fact the skill can settle.

*Reading toward NO-composable:* `specialize` is a one-line `def` whose body is a single `MvPolynomial.aeval` call wrapped in `.toRingHom`. The literature does not name this ring hom (Silverman's "specialization homomorphism" is the points map), and its definition has zero content beyond the universal property of a polynomial ring. Mathlib's own idiom would be to use `MvPolynomial.aeval (Coeff.rec …)` at the call site and inherit the full `aeval` API. On its own, it does not clear the bar for a standalone mathlib lemma.

*Reading toward YES (as part of a package):* `specialize` is not really standalone. It is the named anchor of a coherent, genuinely-missing piece of mathlib's elliptic-curve API — the universal coefficient ring `ℤ[A₁..A₆]`, the universal curve `Universal.curve`, the fact that every Weierstrass curve is its pushforward (`map_specialize`), and the evaluation maps `polyEval`/`ringEval` used to specialize division polynomials. Mathlib *explicitly* gestures at exactly this machinery in `DivisionPolynomial/Basic.lean` ("the associated universal morphism `𝓡[X,Y] → R[X,Y]` mapping `Aᵢ` to `aᵢ`") and leaves `ωₙ` — which needs it — as a TODO. It has 6 internal consumers and is duplicated verbatim across NagellLutz and HasseWeil. As the entry point of a PR that adds the universal-curve scaffold (closing that TODO), a named `specialize` is reasonable; as a lone decl it is not.

The skill cannot decide whether mathlib wants the *whole universal-curve package* upstreamed (in which case `specialize` rides along as the named anchor — a YES-add-as-is for the package, with the Phase-2b semantic-name exemption satisfied by `polyEval`/`ringEval`/`map_specialize`) or prefers the inline `aeval` idiom and to build `ωₙ`'s universal morphism differently (in which case `specialize` is NO-composable and should be inlined / dropped). That is a David-Angdinata-track maintainer call about the shape of the missing `ωₙ` infrastructure.

**Numbered questions (≤5):**
1. Is the plan to upstream the **whole** universal-curve scaffold — `Coeff`, `Universal.curve`, `specialize`/`map_specialize`, `polyEval`/`ringEval` — as one PR (closing the `ωₙ`/universal-morphism TODO in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`)? If **yes** → `specialize` rides along as the named anchor (YES-add-as-is for the package). If **no** → it is NO-composable (inline `MvPolynomial.aeval (Coeff.rec …)`).
2. Does mathlib's elliptic-curve maintainer (David Kurniadi Angdinata, author of the DivisionPolynomial files) want the universal coefficient ring modelled as `MvPolynomial Coeff ℤ` with a 5-constructor `Coeff` inductive (the project's choice), or as `MvPolynomial (Fin 5) ℤ` / an existing index — i.e. is the `Coeff` type itself acceptable upstream?
3. If upstreamed, should the map be a `def` named `specialize` returning `→+*`, or just the `AlgHom` `MvPolynomial.aeval (Coeff.rec …)` used directly (richer API, no reducibility surface)? (Phase 4c favours the latter.)
4. Since this `def` is **duplicated verbatim** in `projects/HasseWeil/.../Auxiliary/Universal.lean`, should it first be de-duplicated into `Common/` within AINTLIB regardless of the mathlib decision? (Independent cleanup-ticket question.)

**Next action:** user (or the elliptic-curve track maintainer) answers Q1–Q3; re-run `/mathlibable WeierstrassCurve.specialize` once the packaging decision is made. Separately, file an AINTLIB dedup ticket for Q4 (NagellLutz ↔ HasseWeil `Universal.lean` share this verbatim).

---

## Next step

User answers the numbered questions (chiefly Q1: upstream the whole universal-curve package, or inline `aeval`?). The verdict resolves to YES-add-as-is (as a package anchor) or NO-composable-from-mathlib accordingly. Independently, dedup the verbatim copy shared by NagellLutz and HasseWeil into `Common/`.
