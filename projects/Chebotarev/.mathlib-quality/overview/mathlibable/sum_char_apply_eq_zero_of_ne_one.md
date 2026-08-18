# /mathlibable report — `sum_char_apply_eq_zero_of_ne_one`

Mode A (single declaration). Full 10-phase workflow. Generated 2026-06-18.

---

### Baseline (Phase 0)
- lake build:               ✗ stale (project oleans not built on the pinned `d90090f647ca` /
  Lean `v4.31.0-rc2`; `lake build <module>` reports "unknown target" because the build is cold).
  Per the task brief, reasoned from source + mathlib source tree at
  `.lake/packages/mathlib/Mathlib` (present and authoritative) instead of blocking on the build.
- decl `sum_char_apply_eq_zero_of_ne_one`:  ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/CharacterOrthogonality.lean:46`
- true qualified name:       **`sum_char_apply_eq_zero_of_ne_one`** — **root namespace** (no
  enclosing `namespace`; the module docstring states the lemmas "are kept in the root namespace as
  candidates for upstreaming to mathlib"). The task's guessed `as.…` prefix is **not** present.
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  Two complex-valued character-orthogonality relations for a finite
  commutative group (`G →* ℂˣ`), plus their finite-abelian Fourier-inversion consequences;
  earmarked `ForMathlib/`.

---

### Statement (Phase 1)

`sum_char_apply_eq_zero_of_ne_one` is a theorem stating **column orthogonality** (the "second
orthogonality relation") for the complex characters of a finite commutative group: for a finite
commutative group `G` and an element `g ≠ 1`, the sum of the character values `χ(g)` over **all**
characters `χ : G →* ℂˣ` vanishes:
  ∑_{χ : G →* ℂˣ} (χ g : ℂ) = 0.

Proof: pick a character `χ₀` with `χ₀ g ≠ 1` (exists because `ℂ` is algebraically closed, hence
`HasEnoughRootsOfUnity ℂ`, so characters separate points — `CommGroup.exists_apply_ne_one_of_
hasEnoughRootsOfUnity`); left-translating the character index by `χ₀` rescales the sum by the
root of unity `χ₀ g ≠ 1`, and `eq_zero_of_mul_eq_self_left` forces the sum to `0`. The translation
bookkeeping is factored into the private aux lemma `sum_eq_zero_of_mulLeft_mul_const_aux`.

Variables / typeclasses (Lean side):
- `{G : Type*}` — the group.
- `[CommGroup G]` — `G` is a (multiplicative) commutative group.
- `[Finite G]` — finiteness (gives finitely many characters).
- `[Fintype (G →* ℂˣ)]` — so the sum over the character group is well-defined.
- `{g : G}` — the evaluation point.

Hypotheses (Lean side):
- `(hg : g ≠ 1)` — `g` is a non-identity element.

Conclusion (math): the character sum at a non-identity element is `0`.
Conclusion (Lean): `∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a standard helper/orthogonality lemma — not a named-after-a-person theorem, not a new
structure, not a `## Main results` headline. (It IS textbook-canonical, which matters in Phase 3,
but structurally it is a small lemma.) Literature width run EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line check **n/a** (one-liner penalty
applies only to definitions). Recorded and skipped.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                          | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "character orthogonality finite abelian group sum of chi(g) over characters equals zero column orthogonality" | yes  | for `g ≠ 1`, ∑_{χ∈Ĝ} χ(g) = 0; = \|G\| when `g = 1`           | Groupprops "Character orthogonality theorem"; "column orthogonality" is the standard name |
|  2 | WebSearch (general / 2nd-orth)   | "second orthogonality relation characters finite group sum over irreducible characters columns vanishes proof" | yes  | ∑_{χ∈Irr(G)} χ(g) = 0 for `g≠1`; general form ∑χ(g)χ̄(h)=\|C_G(g)\| or 0 | PlanetMath, Univ. Alberta MAPH464, Bielefeld notes; abelian case is the 1-dim'l specialisation |
|  3 | WebSearch (named-after / dual)   | "Pontryagin dual finite abelian group characters sum vanishes nontrivial element Fourier inversion generality arbitrary coefficient field roots of unity" | yes  | same; framed as instance of Pontryagin duality; proof = "multiply by χ(g₀)" | Wikipedia Pontryagin duality; **Keith Conrad** "Characters of finite abelian groups" (the canonical generality reference); nLab Pontrjagin dual; Tao 245C/254A |
|  4 | ChatGPT MCP                      | (3 attempts — standard form, minimal roots-of-unity hypothesis, units-vs-AddChar)              | n/a  | —                                                            | **MCP unavailable**: Codex bridge fails on every call with a stdin-read error (`Reading additional input from stdin…`). Environmental, not query-side. Generality instead pinned from mathlib's own `DirichletCharacter.sum_characters_eq_zero` hypothesis set (see below) + WebSearch #1–3. |
|  5 | Local references                 | (no `.mathlib-quality/references/` PDFs for Chebotarev)                                         | n/a  | —                                                            | dir absent — recorded n/a |
|  6 | nLab                             | "Pontrjagin dual" (surfaced via WebSearch #3)                                                   | yes  | finite-abelian self-duality; orthogonality is a corollary    | ncatlab.org/nlab/show/Pontrjagin+dual |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                                                            | not a higher-categorical concept; the 1-categorical Pontryagin statement (row 6) is the relevant one |
|  8 | Stacks Project                   | —                                                                                              | n/a  | —                                                            | not an algebraic-geometry / scheme-theoretic concept |
|  9 | MathOverflow / Math.SE           | (covered by WebSearch #1–2 hitting Groupprops/PlanetMath/lecture notes)                         | yes  | uniform agreement on the statement + the "multiply by χ(g₀)" proof | no dissent found |
| 10 | recent arXiv (last 5y)           | character orthogonality appears as a tool in many 2019–2024 arXiv papers (EDFs, harmonic analysis on finite groups) | yes  | always the same classical statement; never claimed novel    | e.g. arXiv:1612.08385, 1304.1731 — used, not stated as new |

### Literature summary (Phase 3)

Concept identified as: **column orthogonality / the second orthogonality relation** for characters
of a finite abelian group (a.k.a. orthogonality of the columns of the character table; for abelian
`G` the irreducible characters are exactly the 1-dimensional `G → ℂˣ`).
Sources agree on the standard form: **yes** — ∑_{χ} χ(g) = \|G\|·[g = 1].
Most general standard form: holds for characters `G → kˣ` valued in **any** field/integral domain
`k` that contains enough roots of unity (a primitive `(exp G)`-th root); `ℂ` is the convenient
special case (algebraically closed ⇒ enough roots). Stated for an **arbitrary** finite abelian
group, not just cyclic / `ZMod n`. **Mathlib's own** `DirichletCharacter.sum_characters_eq_zero`
confirms the modern generality target: it is stated over any `[CommRing R] [IsDomain R]` with
`[HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]` — i.e. "enough roots of unity for the
exponent", exactly the literature's minimal hypothesis.
Generality dimensions where the literature varies:
  - coefficient ring: from `ℂ` (most common in expositions) → **any domain with enough roots of
    unity for `exp G`** (the maximally general standard form; this is mathlib's own convention).
  - group: cyclic / `ZMod n` (intro expositions) → **arbitrary finite abelian `G`** (general form).
  - formulation: multiplicative `χ : G →* kˣ` vs additive `AddChar G k` (the
    `Multiplicative`/`Additive` transport) — regarded as the same theorem.
Disagreement with the literature: **none**. The user's form is the standard statement, specialised
to `k = ℂ` and to the multiplicative `G →* ℂˣ` formulation.

---

### Generality analysis — `sum_char_apply_eq_zero_of_ne_one` (Phase 4)

Literature-standard form (from Phase 3): for any finite abelian `G` and any integral domain `k`
with enough roots of unity for `exp G`, ∑_{χ : G →* kˣ} χ(g) = 0 for `g ≠ 1`.

| # | Parameter / hypothesis      | Current Lean form                  | Literature-standard form                   | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|------------------------------------|--------------------------------------------|---------------------|----------------------------------|
| 1 | coefficient ring            | `ℂ` (hard-wired; target `ℂˣ`/`ℂ`)  | any `[CommRing R] [IsDomain R]` with `HasEnoughRootsOfUnity R (Monoid.exponent G)` | **yes** | The proof uses `ℂ` only to get `HasEnoughRootsOfUnity` (via alg-closedness) and `IsRightCancelMulZero` (domain). Replace `ℂ` with `R` + those two typeclasses → the aux lemma and `exists_apply_ne_one_of_hasEnoughRootsOfUnity` already work at that generality. **This is exactly mathlib's `DirichletCharacter` convention.** |
| 2 | `[CommGroup G] [Finite G]`  | finite commutative group           | finite abelian group                       | NO                  | already the standard hypothesis; finiteness + commutativity are essential (need finitely many separating characters). Maximally general on this axis. |
| 3 | element `g`                 | `g : G`, `hg : g ≠ 1`              | non-identity element                       | NO                  | already minimal. |
| 4 | character formulation       | `G →* ℂˣ` (multiplicative, units target) | `MulChar`/`G →* kˣ` or `AddChar` (`Multiplicative`/`Additive` transport) | (lateral, not a weakening) | mathlib carries both; see Phase 4c row 5. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (one real axis: the coefficient ring is
pinned to `ℂ`, whereas the literature-standard — and mathlib's own `DirichletCharacter` — form is
"any integral domain with enough roots of unity for the exponent").
Number of weakening opportunities found: **K = 1** (axis #1, the coefficient ring).
Proposed restatement (general-ring column orthogonality):
```lean
theorem sum_char_apply_eq_zero_of_ne_one
    {G : Type*} [CommGroup G] [Finite G]
    {R : Type*} [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]
    [Fintype (G →* Rˣ)] {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Rˣ, ((χ g : Rˣ) : R) = 0 := by
  sorry -- current ℂ proof generalises essentially verbatim
```
Cost of restatement: **CHEAP** — the proof body is ring-agnostic; `eq_zero_of_mul_eq_self_left`
needs `IsRightCancelMulZero R` (a domain has it) and the separating character needs
`HasEnoughRootsOfUnity R (Monoid.exponent G)` (the explicit hypothesis). No new ideas.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclass? | partly | already typeclass-driven; the ℂ → `R` + `HasEnoughRootsOfUnity R (exp G)` move (Phase 4b) IS the typeclass-idiomatic version | aligns with `MulChar.Duality` / `DirichletCharacter.Orthogonality` conventions |
| 2 | sequences/metric → filters? | no | finite sum; no topology to filter-ise | — |
| 3 | construct → universal property? | no | it's an identity, not a construction | — |
| 4 | subset-closure → bundled substructure? | no | — | — |
| 5 | field/ℂ-specific → typeclass weakening? | **yes** | same as Phase 4b: `ℂ` → `[CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent G)]`. Optionally restate against `MulChar G R` or `AddChar (Additive G) R` to reuse mathlib's duality API. | `DirichletCharacter.sum_characters_eq_zero` and the `AddChar`/Pontryagin ℂ-versions both become **specialisations** of one general-ring statement, instead of three parallel copies |
| 6 | 1-categorical → higher? | no | — | — |
| 7 | concrete index → general algebra? | covered by row 5 (the "index" here is the coefficient ring) | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (same target as Phase 4b: general integral domain with enough
roots of unity for the exponent — this is the contemporary mathlib convention, demonstrated by the
existing `DirichletCharacter` and `MulChar.Duality` files).
  - Proposed mathlib-idiomatic restatement: the general-`R` signature in Phase 4b (optionally
    phrased via `MulChar G R` to plug into `MulChar.Duality`, or `AddChar (Additive G) R` to plug
    into the `AddChar` orthogonality already in `Mathlib/Algebra/Group/AddChar.lean`).
  - Cost: **CHEAP–MODERATE** (CHEAP for the `G →* Rˣ` restatement; MODERATE if also re-expressed
    through `AddChar`/`MulChar` wrappers to maximise API reuse).
  - Mathlib downstream this enables: a single general-ring, general-finite-abelian-group **column**
    orthogonality from which `DirichletCharacter.sum_characters_eq_zero`,
    `DirichletCharacter.sum_characters_eq`, and `AddChar.sum_apply_eq_ite` /
    `AddChar.sum_apply_eq_zero_iff_ne_zero` (currently ℂ-only) all specialise.
  - Real mathematical improvement: eliminates the redundancy that mathlib currently proves the
    **row** version generically (`AddChar.sum_eq_ite`, any domain) but the **column** version only
    twice and narrowly (`DirichletCharacter` for `ZMod n`; `AddChar` for ℂ). A general-ring column
    statement closes that asymmetry.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** (No definitional equalities or typeclass-search paths
introduced.) Skipped.

---

### Mathlib search-status: `sum_char_apply_eq_zero_of_ne_one` (Phase 5)

Five-method search. Method D (grep of the **local mathlib source tree** at
`.lake/packages/mathlib/Mathlib`) is authoritative here and returns exact statements; the
loogle/leansearch web indices query the same published mathlib and are subsumed by it (recorded
n/a-redundant where the source grep already answers).

```
[A] Lean-Finder       "sum over characters of finite abelian group vanishes at nontrivial element"
                                                  → n/a: web UI not callable from this env; covered by [D] source grep
[B] Loogle            ∑ _ : (_ →* ℂˣ), _ = 0 ;  ∑ _ : AddChar _ _, _ = 0
                                                  → n/a: lean_loogle MCP not exposed this session; the type
                                                    patterns were grep'd directly against mathlib source ([D])
[C] LeanSearch        "character orthogonality finite abelian group sum over characters is zero"
                                                  → n/a: lean_leansearch MCP not exposed; subsumed by [D]
[D] Grep mathlib src  "orthogonal", "sum_characters", "sum_apply_eq", "sum_eq_ite", "AddChar",
                      "MulChar … sum", "exists_apply_ne_one_of_hasEnoughRootsOfUnity"
                                                  → **HITS** (exact statements read; see below)
[E] Name pattern      sum_char / sum_characters / sum_apply_eq / orthogonality
                                                  → HITS: DirichletCharacter.sum_characters_eq_zero,
                                                    AddChar.sum_apply_eq_zero_iff_ne_zero, MulChar.sum_eq_zero_of_ne_one
```

Searched for **both** forms (user's `G →* ℂˣ` and the literature-general / `AddChar` / `MulChar`
forms). Findings:

- **Column orthogonality, general finite abelian group, over ℂ — PRESENT (additive formulation):**
  - `AddChar.sum_apply_eq_ite` — `Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean:188`
    — `∑ ψ : AddChar α ℂ, ψ a = if a = 0 then (Fintype.card α : ℂ) else 0` for `[Fintype α]
    [DecidableEq α]`. **This is our theorem (and its `g=1` companion) for `AddChar α ℂ`.**
  - `AddChar.sum_apply_eq_zero_iff_ne_zero` — same file, line 196 — `∑ ψ : AddChar α ℂ, ψ a = 0 ↔
    a ≠ 0` for `[Finite α]`. The `a ≠ 0 → sum = 0` direction is exactly our conclusion.
- **Column orthogonality, specialised to `(ZMod n)ˣ`, over any domain with enough roots — PRESENT:**
  - `DirichletCharacter.sum_characters_eq_zero` —
    `Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean:59` — `∑ χ : DirichletCharacter R n,
    χ a = 0` for `a ≠ 1`, over `[CommRing R] [IsDomain R] [HasEnoughRootsOfUnity R (Monoid.exponent
    (ZMod n)ˣ)]`. **Same theorem, same proof** (`eq_zero_of_mul_eq_self_left` + `Fintype.sum_
    bijective` + `Group.mulLeft_bijective` + `exists_apply_ne_one_of_hasEnoughRootsOfUnity`),
    specialised to the group `(ZMod n)ˣ`. Companions `sum_characters_eq` (line 69) and
    `sum_char_inv_mul_char_eq` (line 80) mirror our `card_mul_eq_sum_…` Fourier consequences.
- **General-monoid character DUALITY — PRESENT, but NO column-orthogonality sum:**
  - `Mathlib/NumberTheory/MulChar/Duality.lean` has `exists_apply_ne_one_of_hasEnoughRootsOfUnity`,
    `card_eq_card_units_of_hasEnoughRootsOfUnity`, double-dual, subgroup correspondence — for
    `MulChar M R` of a finite commutative monoid `M` over any domain with enough roots — **but no
    `∑ χ, χ a = 0`.** The orthogonality sum is NOT lifted to this general-group level.
- **Row orthogonality (the companion `sum_char_self_eq_zero_of_ne_one`) — PRESENT generically:**
  - `AddChar.sum_eq_ite` — `Mathlib/Algebra/Group/AddChar.lean:329` — `∑ a, ψ a = if ψ = 0 then
    card A else 0` over **any** `[CommSemiring R] [IsDomain R]` (`sum_eq_zero_iff_ne_zero` line 340
    adds `[CharZero R]`). Also `MulChar.sum_eq_zero_of_ne_one` — `Mathlib/NumberTheory/MulChar/
    Basic.lean:567` — `∑ a, χ a = 0` for a nontrivial `χ : MulChar R R'`, `[IsDomain R']`.
- **Direct `G →* ℂˣ` / `G →* kˣ` (MonoidHom-to-units) column orthogonality — ABSENT.** No decl
  states the sum over `G →* Mˣ`; mathlib's general-group orthogonality is phrased through `AddChar`
  (target the monoid, via `AddChar.toMonoidHomEquiv : AddChar A M ≃ (Multiplicative A →* M)`).
- Supporting primitives confirmed: `eq_zero_of_mul_eq_self_left`
  (`Mathlib/Algebra/GroupWithZero/Basic.lean:324`),
  `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
  (`Mathlib/GroupTheory/FiniteAbelian/Duality.lean:64`) — both used by our proof, both present.

Concluded: **found a partial / formulation-shifted match.** Mathlib HAS column orthogonality for a
general finite abelian group over ℂ (`AddChar.sum_apply_eq_zero_iff_ne_zero`) and over an arbitrary
domain-with-enough-roots but only for the group `(ZMod n)ˣ` (`DirichletCharacter.sum_characters_eq_
zero`). Mathlib does **NOT** have it in the user's exact `G →* ℂˣ` (MonoidHom-to-units) formulation,
nor in the maximally general "arbitrary finite abelian `G` × arbitrary domain with enough roots"
column form. The user's statement sits between two existing mathlib results, matching neither
verbatim.

---

### Call sites — `sum_char_apply_eq_zero_of_ne_one` (Phase 6.0)

Internal use count (whole Chebotarev project, excluding the declaring file): **K = 1**.
External-to-file callers: **1 distinct file**.

| Caller file:line                                                  | Usage pattern (one-line excerpt)                          |
|-------------------------------------------------------------------|-----------------------------------------------------------|
| `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean:177`        | `· exact sum_char_apply_eq_zero_of_ne_one hg`             |
| `…/ForMathlib/CharacterOrthogonality.lean:77` (same file, internal)| `exact sum_char_apply_eq_zero_of_ne_one fun h ↦ hs …`     |

Inline-derivation grep (was the same statement re-derived elsewhere without this lemma?):
  - `Cyclotomic.lean:166` `sum_galoisCharacter_eq_card_or_zero` — a **private** wrapper that proves
    the full `if g = 1 then card else 0` form and **delegates the `g ≠ 1` branch to this lemma**
    (line 177). So the project's own combined-form lemma is built ON this one, not bypassing it.
  - The two downstream Fourier lemmas in the same file (`card_mul_eq_sum_…`,
    `eq_of_sum_char_mul_eq_zero`) also consume it (lines 64, 77). Real internal API.

Call-site signal: **K = 1 external + load-bearing internal use** (the file's own Fourier-inversion
results and Cyclotomic's `sum_galoisCharacter_eq_card_or_zero` depend on it). Not dead code; not a
bypassed wrapper. Mild K=1 "could-be-inlined" pull, but it genuinely anchors a small API cluster.

### Composition check (Phase 6)

Can `sum_char_apply_eq_zero_of_ne_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 — specialise `AddChar.sum_apply_eq_zero_iff_ne_zero` (ℂ, general group):
  - Idea: transport `∑ χ : G →* ℂˣ, (χ g : ℂ)` to `∑ ψ : AddChar (Additive G) ℂ, ψ (.ofMul g)` and
    apply `(AddChar.sum_apply_eq_zero_iff_ne_zero).mpr`.
  - Mathlib decls used: `AddChar.sum_apply_eq_zero_iff_ne_zero`, `AddChar.toMonoidHomMulEquiv`
    (`AddChar A M ≃* (Multiplicative A →* M)`), `Units.coeHom ℂ` (`ℂˣ →* ℂ`),
    `Fintype.sum_equiv` / `Fintype.sum_bijective`.
  - Result: **partial / fails as a ≤3-call composition.** Obstruction: the **target mismatch**.
    Ours indexes over `G →* ℂˣ` (homs into the *units*); mathlib's `AddChar (Additive G) ℂ`
    corresponds via `toMonoidHomMulEquiv` to `Multiplicative (Additive G) →* ℂ` (homs into the
    *monoid* `ℂ`, not `ℂˣ`). Bridging requires (i) the `Multiplicative/Additive` transport, (ii)
    composing each `χ : G →* ℂˣ` with `Units.coeHom ℂ` and re-indexing the sum across the resulting
    equiv, and (iii) pushing the `(· : ℂˣ → ℂ)` coercion through. There is **no ready-made
    `(G →* ℂˣ) ≃ AddChar (Additive G) ℂ`** in mathlib. That is 4–6 genuine steps with reasoning
    between them — a small bridging proof, not a 1–3-call composition.
  - Notes: the bridge IS routine (CHEAP–MODERATE to write) and shorter than re-proving from scratch,
    but it exceeds the composition heuristics (multiple `have`s + a re-indexing equiv = "proof, not
    composition").

Attempt 2 — specialise `DirichletCharacter.sum_characters_eq_zero`:
  - Result: **fails.** That lemma is hard-wired to the group `(ZMod n)ˣ`; our `G` is arbitrary.
    No specialisation route to general `G`.

Conclusion: **NOT-COMPOSABLE** (in the strict ≤3-call sense). The result follows from mathlib only
via a multi-step formulation bridge (Attempt 1), which is itself a small proof.

---

## Verdict: `sum_char_apply_eq_zero_of_ne_one`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): textbook-canonical **column orthogonality / 2nd orthogonality
  relation**; standard generality is "arbitrary finite abelian `G`, any domain with enough roots of
  unity for `exp G`" — confirmed by sources AND by mathlib's own `DirichletCharacter` hypothesis set.
- Generality analysis (Phase 4): **STRICTLY NARROWER** on one axis (coefficient ring pinned to `ℂ`;
  K=1 cheap weakening to general `R`); Phase 4c flags the same general-ring form as the
  mathlib-idiomatic target.
- Mathlib search (Phase 5): **partial / formulation-shifted match** — mathlib HAS the general-group
  column form over ℂ (`AddChar.sum_apply_eq_zero_iff_ne_zero`, PontryaginDuality.lean:196) and the
  general-domain column form for `(ZMod n)ˣ` (`DirichletCharacter.sum_characters_eq_zero`,
  Orthogonality.lean:59), but NOT the user's `G →* ℂˣ` form and NOT the maximally-general
  (arbitrary `G` × arbitrary domain) column form.
- Composition check (Phase 6): **NOT-COMPOSABLE** in ≤3 calls — only via a multi-step
  `AddChar`/units/`Multiplicative` bridge that is itself a small proof.

**Rationale (why BORDERLINE):**

This is the rare genuinely-ambiguous case the bucket exists for, and the ambiguity is a scope/taste
call, not a gap in the evidence. The mathematics is 100% standard and mathlib already contains the
result in *two adjacent shapes* — but neither is the user's shape, and neither is the maximally
general shape. (a) If one weights "mathlib already proves column orthogonality for a general finite
abelian group over ℂ" (`AddChar.sum_apply_eq_zero_iff_ne_zero`), the user's `G →* ℂˣ` lemma is
**morally redundant** and the right move is to delete it and bridge the single external call site
(`Cyclotomic.lean:177`) through the `AddChar` API — leaning `NO-mathlib-has-it`. But it does **not**
follow in ≤1 line (the units-vs-monoid target mismatch forces a multi-step transport — Phase 6
Attempt 1), so the strict `NO-mathlib-has-it` evidence bar (a ≤1-line `example`) is **not met**, and
it isn't a clean ≤3-call composition either. (b) If one weights the Bourbaki-2.0 generality
asymmetry — mathlib proves the **row** version over an arbitrary domain (`AddChar.sum_eq_ite`) but
the **column** version only narrowly (ℂ-only via `AddChar`; `ZMod n`-only via `DirichletCharacter`)
— then the right move is **not** to add the user's ℂ-specific form but to contribute the
**general-ring column orthogonality** (`∑ χ : G →* Rˣ / MulChar G R, χ g = 0` over any domain with
enough roots for `exp G`) that mathlib genuinely lacks and from which all three existing
specialisations would follow — leaning `YES-but-generalise-first`. Both readings are defensible; the
choice between "it's effectively already there, just bridge it" and "lift it to the general-ring
form mathlib is missing" is a maintainer judgment about how much generalisation is worth shipping.
The skill must not silently pick.

A secondary judgment compounds it: even the `YES-but-generalise-first` path has a sub-choice of
**formulation** — keep the `G →* Rˣ` (MonoidHom-to-units) phrasing, or restate through mathlib's
`MulChar G R` / `AddChar (Additive G) R` wrappers to maximise API reuse. That, too, is a taste call.

**Numbered questions (≤5):**

1. Mathlib already has this exact result for a **general finite abelian group over ℂ** as
   `AddChar.sum_apply_eq_zero_iff_ne_zero` (additive formulation). Do you consider your
   `G →* ℂˣ` (multiplicative) version **redundant** with it — i.e. acceptable to **delete** and
   bridge the one external call site (`Cyclotomic.lean:177`) through the `AddChar` API (a ~5-line
   `Multiplicative`/units transport)? (yes → NO-mathlib-has-it via bridge; no → go to Q2.)

2. If you'd rather **contribute** to mathlib: mathlib is missing the **general-ring** column
   orthogonality (arbitrary finite abelian `G` × arbitrary integral domain with enough roots of
   unity for `exp G`) — it only has the ℂ-special case (`AddChar`) and the `(ZMod n)ˣ` case
   (`DirichletCharacter.sum_characters_eq_zero`). Is generalising your lemma to that form
   (CHEAP — Phase 4b signature) the intended contribution? (yes → YES-but-generalise-first.)

3. If generalising (Q2 = yes): should the contributed statement be phrased as `G →* Rˣ`
   (your current MonoidHom-to-units style), or restated through `MulChar G R` / `AddChar (Additive
   G) R` to slot directly beside `Mathlib/NumberTheory/MulChar/Duality.lean` and have
   `DirichletCharacter.sum_characters_eq_zero` + the `AddChar` ℂ-versions specialise from it?

4. Companion scope: this file's `sum_char_self_eq_zero_of_ne_one` (row version) is **already** in
   mathlib generically (`AddChar.sum_eq_ite` / `MulChar.sum_eq_zero_of_ne_one`), and the
   `card_mul_eq_sum_…` / `eq_of_sum_char_mul_eq_zero` Fourier lemmas mirror
   `DirichletCharacter.sum_characters_eq` / `sum_char_inv_mul_char_eq`. Should the upstreaming
   decision be made for the **whole CharacterOrthogonality.lean cluster at once** (likely
   "general-ring column orthogonality + Fourier inversion over arbitrary `G`") rather than this one
   lemma in isolation?

**Next action:** user answers Q1–Q4; re-run `/mathlibable sum_char_apply_eq_zero_of_ne_one` (or
proceed directly) to resolve to either `NO-mathlib-has-it` (delete + `AddChar` bridge at
`Cyclotomic.lean:177`) or `YES-but-generalise-first` (lift to the general-ring column form via
`/generalise`, ideally for the whole file cluster). Likely outcomes:
  - Q1 = yes → **NO-mathlib-has-it**: delete; bridge the 1 external call site through
    `AddChar.sum_apply_eq_zero_iff_ne_zero`.
  - Q1 = no, Q2 = yes → **YES-but-generalise-first**: restate over `[CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]` (Phase 4b signature), formulation per Q3, scope
    per Q4; then `/generalise` + `/cleanup` before a mathlib PR targeting
    `Mathlib/NumberTheory/MulChar/` (next to `Duality.lean`).

---

### Notes on environment / method
- `ChatGPT math MCP` was unavailable all session (Codex bridge stdin-read error on every call);
  recorded n/a. Generality was instead pinned from mathlib's own `DirichletCharacter.sum_characters_
  eq_zero` hypothesis set + 3 WebSearches at different generality levels + nLab — a stronger basis
  than an index snippet here.
- `lean_loogle` / `lean_leansearch` MCP tools were not exposed this session; Phase-5 Method D
  (direct grep of the local mathlib **source** at `.lake/packages/mathlib/Mathlib`) supersedes them
  with exact statements, and was the primary mathlib-search instrument.
- Local project build is stale (cold `.lake`); reasoned from source per the task brief. The
  composition-bridge sketches (Phase 6) were not `lake build`-checked (the skill does not run them).
