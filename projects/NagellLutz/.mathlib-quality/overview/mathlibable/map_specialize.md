# /mathlibable report — `WeierstrassCurve.map_specialize`

### Baseline (Phase 0)
- lake build:               (not run — local build is stale per task; reasoned from source)
- decl `WeierstrassCurve.map_specialize`: ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:194`
- qualified name:           `WeierstrassCurve.map_specialize` — VERIFIED. Lemma sits inside
                            `namespace WeierstrassCurve` (opened L69, closed L243) but **outside**
                            `namespace Universal` (Universal closes L177, reopens L196). The parsed
                            guess in the prompt was correct.
- kind:                     lemma (theorem)
- has sorry:                no
- module docstring summary: "Additions to Affine.Point and the universal elliptic curve" — provides
                            lemmas missing from released mathlib for the division-polynomial / ZSMul
                            development, and **defines the universal Weierstrass curve** `Universal.curve`
                            over `ℤ[A₁,A₂,A₃,A₄,A₆]` plus the universal pointed curve over its
                            fraction field.

---

### Statement (Phase 1)

`WeierstrassCurve.map_specialize` states the **universal property** of the universal Weierstrass curve:
for any commutative ring `R` and any Weierstrass curve `W` over `R`, applying the specialization ring
homomorphism `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R` (which sends each coefficient variable `Aᵢ` to the
corresponding coefficient `aᵢ` of `W`) to the universal curve `Universal.curve` recovers `W` exactly.

In words: every Weierstrass curve is the specialization of the one universal Weierstrass curve along the
ring map that plugs its own coefficients in for the coefficient variables.

Variables / typeclasses involved (Lean side):
- `{R : Type*}` `[CommRing R]` — the base ring.
- `(W : WeierstrassCurve R)` — an arbitrary Weierstrass curve over `R`.

Project-local objects it depends on (NONE of which are in mathlib):
- `WeierstrassCurve.Universal.curve : Affine (MvPolynomial Coeff ℤ)` — the universal curve, with
  `aᵢ := MvPolynomial.X Aᵢ` (L84–85). `Coeff` is a project-local 5-element inductive (L73).
- `WeierstrassCurve.specialize : MvPolynomial Coeff ℤ →+* R := (MvPolynomial.aeval (Coeff.rec W.a₁ … W.a₆)).toRingHom`
  (L190–191) — the specialization hom.

Hypotheses (Lean side): none beyond the typeclass `[CommRing R]`.

Conclusion (math): `Φ_W(E_univ) = W`, where `E_univ` is the universal Weierstrass curve and `Φ_W` is
the coefficient-specialization map.

Conclusion (Lean): `Universal.curve.map W.specialize = W` (an equality of `WeierstrassCurve R`).

Proof body: `by simp [specialize, curve, map]` — unfolds the three definitions; each of the five
coefficient components reduces by `MvPolynomial.aeval_X : aeval f (X s) = f s`.

---

### Size classification (Phase 2a)

Verdict: BIG
Reason: it is the defining/characterising property of a **new named mathematical structure**
(`Universal.curve`, the universal Weierstrass curve) that the project introduces. Although the lemma
*line* is a one-liner, its content is the universal property of a construction — a BIG concept.
(Literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line — but kind is **lemma**, so the one-liner-def heuristic does not
apply. A `lemma`/`theorem` with a one-line proof is normal and carries no negative signal; the Phase-2b
def-inlining bias is n/a here. (The associated *def* `Universal.curve` is a separate decl, not under
assessment in this invocation.)

Conclusion: n/a — declaration kind is lemma, not def.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "universal Weierstrass curve over Z[a1..a6] specialization every elliptic curve"                        | yes  | `A = ℤ[a₁,…,a₆]`; universal generalized elliptic curve `𝓔 → Spec(A)°`; **every Weierstrass curve is a specialization of the universal one** | Katz–Mazur ("Moduli of Elliptic Curves" notes, Princeton); Cremona Ch.3; TMF lit (arXiv:1312.7394) |
|  2 | WebSearch (general form)         | ""universal elliptic curve" universal Weierstrass equation polynomial ring coefficients division polynomials" | yes  | `Ψₙ ∈ ℤ[a₁,…,a₆,x,y]`; the universal morphism `𝓡[X,Y] → R[X,Y]` maps `Aᵢ ↦ aᵢ` | Matches mathlib's own DivisionPolynomial docstring verbatim ("associated universal morphism … mapping `Aᵢ` to `aᵢ`") |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2: "universal elliptic curve", "universal Weierstrass family", Katz "generic Weierstrass curve") | yes  | same object under several names    | Katz's MMP notes ch.10 call it the "universal Weierstrass family" |
|  4 | ChatGPT MCP                      | n/a — MCP reported down for this environment (task note); compensated with extra WebSearch passes (#1–#3 at three generality levels) and Stacks/nLab below | n/a  | —                                  | Fallback per task instructions |
|  5 | Local references                 | `.mathlib-quality/references/` for "universal" / "Weierstrass"                                          | n/a  | directory absent in NagellLutz     | recorded n/a (refs are gitignored / not present in worktree) |
|  6 | nLab                             | "universal elliptic curve" / "Weierstrass curve"                                                       | yes  | universal elliptic curve over the moduli stack `M_{1,1}` / `M_ell`; Weierstrass presentation | nLab frames it via the moduli stack; the affine `ℤ[a₁..a₆]` presentation is the standard chart |
|  7 | nCatLab (categorical)            | (same as nLab #6 — moduli-stack framing)                                                               | yes  | universal family over the stack    | categorical phrasing; not needed for this affine-level lemma |
|  8 | Stacks Project (alg geom)        | "Weierstrass equation" / "universal Weierstrass"                                                       | yes  | Stacks tag on Weierstrass equations & the algebra `ℤ[a₁,…,a₆]` (`0CJF`-area); generalized elliptic curves | confirms the ring and its modular elements `c₄,c₆,Δ`; the universal property is implicit |
|  9 | MathOverflow / Math.SE           | "universal elliptic curve Weierstrass coefficients specialization"                                     | yes  | repeated as folklore: any Weierstrass curve = pullback of the universal one along `aᵢ ↦ aᵢ` | standard background, no single canonical citation |
| 10 | recent arXiv (last 5 years)      | "homogeneous division polynomials Weierstrass" (arXiv:1303.4327), TMF level-structure (arXiv:1312.7394) | yes  | division polys built over the universal coefficient ring; specialization to `R` | matches the project's downstream use of `map_specialize` |

### Literature summary (Phase 3)

Concept identified as: the **universal Weierstrass curve** (a.k.a. universal/generic elliptic curve in
Weierstrass form, universal Weierstrass family); `map_specialize` is its **universal property** (the
specialization / pullback identity).
Sources agree on the standard form: yes. Universally: `A = ℤ[a₁,a₂,a₃,a₄,a₆]`, the universal curve has
`aᵢ = Aᵢ`, and every Weierstrass curve `W/R` is its image under the unique ring map `Aᵢ ↦ aᵢ(W)`. This
is exactly the Lean statement.
Most general standard form: stated for **any commutative ring `R`** (no field / no discriminant-invertible
hypothesis needed at the level of *Weierstrass curves*; invertibility of `Δ` is only needed to get an
*elliptic* curve, not for this identity). The project's form is already at this generality.
Generality dimensions where the literature varies:
  - base object: ring-level affine presentation (`ℤ[a₁..a₆]`) vs. moduli-stack `M_{1,1}` framing. The
    ring-level form is the right one for a `WeierstrassCurve R`-valued statement; the stack is overkill.
Disagreement with the literature: none. The Lean statement is the standard affine-chart universal property.

---

### Generality analysis — `WeierstrassCurve.map_specialize`

Literature-standard form (from Phase 3): for any commutative ring `R` and Weierstrass curve `W/R`,
`(universal curve).map (Aᵢ ↦ aᵢ(W)) = W`.

| # | Parameter / hypothesis | Current Lean form          | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|----------------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring           | commutative ring          | NO                  | `WeierstrassCurve` and `MvPolynomial.aeval` both require `CommRing`; this is already the minimal/standard base. |
| 2 | `(W : WeierstrassCurve R)` | arbitrary Weierstrass curve | arbitrary                 | NO                  | the statement quantifies over *all* `W`; nothing to weaken. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0. It is already stated for an arbitrary `WeierstrassCurve` over
an arbitrary `CommRing`, which is the most general form in the literature.
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | the hypotheses are already typeclasses (`CommRing`) | — |
|  2 | sequences/metric → filters/topology? | no | no analytic content | — |
|  3 | construct an object → universal-property **class**? | partially | mathlib *could* package "the universal curve + its universal property" as an `Algebra`/initial-object characterisation, but that is a design decision about the **`Universal.curve` def**, not about this lemma's phrasing. The lemma already *is* the universal-property statement. | a universal-property class would let other curves be defined by their specialization map — but this is a redesign of the construction, surfaced as the human question below. |
|  4 | set-with-closure → bundled substructure? | no | not a substructure | — |
|  5 | vector-space/field-specific → weaken typeclasses? | no | already at `CommRing` | — |
|  6 | 1-categorical → higher/∞-categorical? | no (overkill) | the moduli-stack `M_{1,1}` framing exists but is far heavier than a `WeierstrassCurve R` identity | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → general monoid/group? | no | the `ℤ` in `MvPolynomial Coeff ℤ` is the **initial** ring; this is correct — the universal curve must be defined over `ℤ`. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no (for the lemma as phrased).
One-line reason: `map_specialize` is *already* the clean modern statement of the universal property
(`map` along a ring hom equals the target). The only "modernisation" lever (row 3 — package the universal
curve via a universal-property/initiality class) is a decision about the **`Universal.curve` definition**,
not this lemma, and is exactly the kind of design call the BORDERLINE question hands to a human.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is **lemma** (proves an equality; introduces no definitional equality, no
typeclass-search path, no instance). Skipped.

(Note: the *associated def* `Universal.curve` would need its own Phase-4.5 pass if it were upstreamed;
that def is a separate decl and out of scope for this single-decl invocation.)

---

### Mathlib search-status: `WeierstrassCurve.map_specialize`

[A] Lean-Finder       "universal Weierstrass curve specialization", "curve map specialize equals self"   no hits (mathlib index has no universal-curve object)
[B] Loogle            `WeierstrassCurve.map _ _ = _`, `?W.map ?f = ?W` patterns                            partial — only `WeierstrassCurve.map_id` (`W.map (RingHom.id R) = W`) and `map_baseChange`; nothing about a universal curve
[C] LeanSearch        "every Weierstrass curve is a specialization of the universal Weierstrass curve"    no hits
[D] Grep mathlib src  `grep -rn "map_specialize\|universal\|inductive Coeff\|Universal.curve"` over `Mathlib/AlgebraicGeometry/EllipticCurve/` | only **prose** docstring mentions in `DivisionPolynomial/Basic.lean` L36–38 ("universal ring `ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]`", "universal morphism `𝓡[X,Y] → R[X,Y]` mapping `Aᵢ` to `aᵢ`"). **No formalized `Universal.curve`, no `Coeff` inductive, no `specialize`, no `map_specialize`.** |
[E] Name pattern      grep `map_specialize` over whole repo                                                hits ONLY in AINTLIB projects (NagellLutz, HasseWeil — same Junyan-Xu source); zero in `Mathlib/`

Searched for both:
  - the user's current form (`Universal.curve.map W.specialize = W`) — not in mathlib;
  - the literature-standard form (the universal-property identity) — not in mathlib at the object level.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). Critically,
the *reason* is structural: mathlib has **no universal-Weierstrass-curve object** at all. Mathlib's
DivisionPolynomial development deliberately works with `MvPolynomial`-valued recurrences and a base-change
morphism (`map_baseChange`) **without ever constructing `Universal.curve`** — the "universal morphism" is
only named in a docstring, never reified as a curve. So `map_specialize` cannot be a duplicate; there is
nothing in mathlib for it to duplicate.

Nearest mathlib analogue: `WeierstrassCurve.map_id` (`Weierstrass.lean:278`, `W.map (RingHom.id R) = W`)
— same *shape* (a `map` collapsing to `W`), but a completely different statement (identity hom vs. the
coefficient-specialization hom out of the universal ring).

---

### Call sites — `WeierstrassCurve.map_specialize`

Internal use count: **10** (within NagellLutz, excluding the declaring file `Universal.lean:194`).
External-to-file callers: **2 distinct files** in NagellLutz (and the *same* lemma is used identically
in the HasseWeil project — a parallel fork of the same source, ~6 more uses).

| Caller file:line                                   | Usage pattern (one-line excerpt) |
|----------------------------------------------------|-----------------------------------|
| LutzNagell/Universal.lean:218                       | `rwa [← Affine.map_polynomial, map_specialize]` (used internally to build `ringEval`) |
| LutzNagell/Universal.lean:239                       | `(ringEval_comp_eq_specialize eqn) ▸ map_specialize W` (proves `curveRing.map (ringEval eqn) = W`) |
| LutzNagell/DivisionPolynomialOmega.lean:123         | `rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]; simp` |
| LutzNagell/ZSMul.lean:89                            | `simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]` |
| LutzNagell/ZSMul.lean:92                            | `simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]` |
| LutzNagell/ZSMul.lean:95                            | `simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]` |
| LutzNagell/ZSMul.lean:100                           | `simp_rw [polyEval_apply, ← map_ψ, map_specialize]` |
| LutzNagell/ZSMul.lean:103                           | `simp_rw [polyEval_apply, ← map_φ, map_specialize]` |
| LutzNagell/ZSMul.lean:106                           | `simp_rw [polyEval_apply, ← map_ω, map_specialize]` |
| LutzNagell/ZSMul.lean:558                           | `conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, ← coe_mapRingHom, …]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `map_specialize`?): (none)
— every site that needs "transport a universal division-polynomial identity down to `W`" routes through
this single lemma. It is the load-bearing bridge from the universal computation to the concrete curve.

Call-sites signal: **K = 10 ≥ 3, no inline re-derivation → real, heavily-used API.** Under the Phase-6.0.1
table this leans toward a YES-* bucket *on the merits of the lemma*. The obstruction to YES is not the
lemma's usefulness — it is that the lemma is inseparable from the `Universal.curve` construction mathlib
lacks (see verdict).

---

### Composition check (Phase 6)

Can `WeierstrassCurve.map_specialize` be derived from mathlib in ≤3 chained calls?

Attempt 1: unfold + `MvPolynomial.aeval_X` componentwise (what the project's `by simp [specialize, curve, map]`
does). Mathlib decls used: `MvPolynomial.aeval_X`, `WeierstrassCurve.map` (`@[simps]` projections).
  - Result: **succeeds *as a proof*** — but ONLY once `Universal.curve` and `specialize` already exist.
    It does not compose to the statement from mathlib primitives, because mathlib has no `Universal.curve`
    to even form the LHS. The "composition" presupposes the project's definitions.
  - Notes: this is a proof of the lemma given the defs, not a derivation of the lemma from mathlib.

Attempt 2: derive from `WeierstrassCurve.map_id` / `map_baseChange`.
  - Result: fails. `map_id` is about `RingHom.id`; `specialize` is the (non-identity) coefficient-evaluation
    map out of `ℤ[A₁..A₆]`. No chain of `map_id`/`map_map`/`map_baseChange` produces the universal-property
    identity, because none of them reference a universal curve.

Conclusion: **NOT-COMPOSABLE from mathlib's current contents.** The building block `MvPolynomial.aeval_X`
exists, but the *object* the lemma is about (`Universal.curve`) does not exist in mathlib, so there is no
≤3-call mathlib expression whose statement this is. Composability would only hold *after* `Universal.curve`
and `specialize` were themselves added to mathlib.

---

## Verdict: `WeierstrassCurve.map_specialize`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the universal Weierstrass curve and its specialization/universal property
  are **standard and classical** (Katz–Mazur, Cremona Ch.3, Stacks, nLab); the Lean statement matches the
  standard affine-chart form exactly, at full `CommRing` generality.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; 0 weakenings; no modern-idiom improvement to the
  *lemma* (the only lever is a redesign of the `Universal.curve` *def*).
- Mathlib search (Phase 5): **not in mathlib**, and not as a duplicate — mathlib has **no universal-curve
  object at all**; it reifies only the `MvPolynomial`-recurrence + `map_baseChange` approach and mentions
  the universal morphism only in a docstring.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib as-is (the LHS object doesn't exist in mathlib).

**Rationale (1–2 paragraphs):**

The lemma is mathematically standard, maximally general, sorry-free, and genuinely load-bearing (10 internal
call sites; it is the sole bridge transporting universal division-polynomial identities `ψₙ, φₙ, ωₙ` down to
a concrete curve `W`, and the same lemma is reused verbatim in HasseWeil). On the lemma's own merits this is
a YES. **But the lemma is not a standalone unit:** it is the universal property of the project-local
`Universal.curve` definition (with its bespoke 5-element `Coeff` inductive and `specialize` hom), none of
which exist in mathlib. Mathlib made a deliberate design choice in its DivisionPolynomial development to
work with `MvPolynomial Coeff ℤ`-valued recurrences and a base-change morphism, naming "the universal
morphism `𝓡[X,Y] → R[X,Y]`" only in prose and **never constructing the universal curve as an object**. So
upstreaming `map_specialize` is not a one-lemma PR — it is a decision to upstream the entire
`Universal.curve` construction (def + `Coeff` + `specialize` + `polyEval`/`ringEval` + the universal field),
which would partly *re-architect* how mathlib presents division polynomials and the universal ring.

That decision is exactly a mathlib-design / project-policy judgment the skill cannot make alone: it weighs a
cleaner, reusable universal-curve object (which downstream EDS / Nagell–Lutz / Hasse–Weil work clearly wants)
against mathlib's existing, intentionally object-free `map_baseChange` route, and against the diamond/defeq
review the new `Universal.curve` *def* would itself require (out of scope for this lemma-only invocation).
Hence BORDERLINE rather than a self-resolved YES.

**Numbered questions (≤5):**
  1. Should mathlib gain a reified **universal Weierstrass curve** object (`Universal.curve` over
     `ℤ[A₁,A₂,A₃,A₄,A₆]`, with the `Coeff` inductive and `specialize` hom), rather than only the current
     `MvPolynomial`-recurrence + `map_baseChange` presentation? `map_specialize` ships only as part of that
     construction — yes/no?
  2. If yes: is the project's concrete packaging (a 5-element inductive `Coeff` + `MvPolynomial.aeval`-based
     `specialize`) the form mathlib wants, or should the universal curve instead be characterised by an
     **initiality / universal-property typeclass** (Phase 4c row 3) from which `map_specialize` becomes the
     defining axiom? (This is the only "modernisation" lever and it changes the `def`, not the lemma.)
  3. If yes: who owns the upstreaming, and should it be coordinated with the existing
     `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/` maintainers, since adding `Universal.curve`
     would let several `map_baseChange`-style lemmas there be restated through it?

**Next action:** user (or a mathlib EC maintainer) answers Q1–Q3. If Q1 is "yes", run a full `/mathlibable`
(and `/generalise` + Phase-4.5 diamond pass) on the **`Universal.curve` def itself** — that def, not this
lemma, is the real upstreaming unit; `map_specialize` then rides along as its universal-property lemma
(a clean YES-add-as-is in that bundle). If Q1 is "no", `map_specialize` stays a correct, well-scoped
project-local lemma with no mathlib action.

---

## Next step

User answers the three numbered questions above (centrally: does mathlib want a reified universal Weierstrass
curve object?). The lemma cannot be assessed to a YES/NO in isolation because it is the universal property of
the project-local `Universal.curve`, which mathlib does not have; the real upstreaming unit is that `def`,
with `map_specialize` bundled as its characterising lemma.
