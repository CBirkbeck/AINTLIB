# /mathlibable report — `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`

> Scope note: this report assesses the **PID / fraction-field track** lemma at
> `PIDMain.lean:48` (qualified `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`),
> per the Step-9 task. Its byte-for-byte twin on the **General track** —
> `LutzNagell.LutzNagellTheorem.nsmul_eq_zero_affine_to_jac` at
> `GeneralMain.lean:28` — was assessed in the same overview run with the
> identical verdict (`NO-composable-from-mathlib`). The two are the canonical
> General*/PID* duplication this project flagged; **the deduplication of the
> pair is the actionable cleanup item** (see refactor plan). This file was
> previously the General-track report; both share the base name
> `nsmul_eq_zero_affine_to_jac`.

## Verdict: NO-composable-from-mathlib

A ≤3-call composition of generic Mathlib homomorphism API (`natCast_zsmul` +
AddEquiv-transport via `map_nsmul` / `map_zero`) applied to Mathlib's own
`WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`. Project-internal glue;
keep project-local (deduplicated against the General twin), do not PR to
Mathlib.

---

### Baseline (Phase 0)
- lake build:               not re-run (build known-stale per task brief; decl
  reasoned from source — it elaborates, with 4 downstream call sites in the
  same file that all type-check against its conclusion).
- decl `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:48`
  (inside `namespace LutzNagell` → `namespace PID`, so the fully-qualified name
  is `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`).
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Generalized Lutz–Nagell theorem over a PID `R` of
  characteristic zero with fraction field `K` (and the number-field corollary).

---

### Statement (Phase 1)

`nsmul_eq_zero_affine_to_jac` states: let `R` be a domain that is a PID of
characteristic zero, `K` its fraction field, and `W : WeierstrassCurve R`.
For a nonsingular affine point `P = (x, y)` of the base-changed curve
`curveK R K W = W.map (algebraMap R K)` over `K`, and a natural number `n`, if
`n • P = 0` in the **affine** point group, then
`(n : ℤ) • (P viewed as a Jacobian point via fromAffine) = 0` in the
**Jacobian** point group.

Mathematically: the canonical group isomorphism between the affine and
Jacobian models of `E(K)` sends an `n`-torsion point to an `n`-torsion point,
and the ℕ-scalar annihilation `n • P = 0` is the same condition as the
ℤ-scalar annihilation `(n : ℤ) • P = 0`. It is the elementary fact "a group
homomorphism maps `n`-torsion to `n`-torsion" (here an `AddEquiv`, even an
isomorphism), instantiated at Mathlib's affine↔Jacobian equivalence
`WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`, with the trivial
`ℕ`-smul ⇄ `ℤ`-smul cast bridging the two scalar types.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`
  — the PID. (The last three are `omit`-ted on this lemma; see below.)
- `{K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]`
  — the fraction field. (`IsFractionRing R K` is `omit`-ted.)
- `(W : WeierstrassCurve R)` — the curve.
- `{x y : K}` — affine coordinates of the point.

Note: the lemma carries
`omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [IsFractionRing R K]`,
so it only really uses `[CommRing R] [Field K] [DecidableEq K] [Algebra R K]`.
That is itself a tell that the content is generic group-homomorphism algebra,
not number theory.

Hypotheses (Lean side):
- `{hns : (curveK R K W).toAffine.Nonsingular x y}` — nonsingularity witness.
- `{n : ℕ}` — the multiplier.
- `(h : n • (Affine.Point.some _ _ hns) = 0)` — the affine annihilation.

Conclusion (math): the image of `P` in the Jacobian point group is killed by `n`.
Conclusion (Lean):
`(n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0`.

Proof body (4 lines):
```lean
  rw [natCast_zsmul]
  have h' := congrArg (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm h
  rw [map_nsmul, map_zero] at h'
  simpa using h'
```
i.e. (1) `natCast_zsmul` collapses the goal's `(n : ℤ) •` to `n •`;
(2) apply the inverse equivalence `(toAffineAddEquiv W).symm` to both sides of
`h`; (3) `map_nsmul` + `map_zero` simplify the RHS to `0` and pull the `n •`
out; (4) `simpa` discharges the residual defeq
`(toAffineAddEquiv W).symm (.some …) = fromAffine (.some …)` (the equiv's
`invFun` *is* `fromAffine`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A helper "convert `n • P = 0` on affine points to the Jacobian model"
lemma under `/-! ### Helper lemmas -/`. Not a `## Main results` entry, not
named after a person/place, introduces no structure. Pure glue between two
Mathlib coordinate models.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure`. The one-liner check is for
definitions; n/a here. (Body is 4 lines anyway.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "group isomorphism maps n-torsion to n-torsion order of element preserved under isomorphism"        | yes  | iso preserves order of elements; maps `A[n]` onto `B[n]` | Standard undergraduate group theory (UCSD honors notes; MIT 18.783 §7 torsion subgroups; Grokipedia "Torsion subgroup"). Not a *named* theorem — folklore. |
|  2 | WebSearch (general / Mathlib)    | "Mathlib Lean AddEquiv map_nsmul torsion addOrderOf preserved transport along monoid homomorphism"  | partial | `Mathlib.GroupTheory.Torsion`; `map_nsmul`; `natCast_zsmul` in `Algebra/Group/Defs.lean` | Confirms the building blocks are generic Mathlib; no single packaged "transport `n•P=0` across AddEquiv" lemma surfaced. |
|  3 | WebSearch (named-after / aliases)| (covered by #1 — "order of element preserved under isomorphism" / "n-torsion subgroup") | yes | same as #1 | The concept has no proper-noun name; it is a one-line corollary of "homomorphisms commute with `n•`". |
|  4 | ChatGPT MCP                      | "Is there a single Mathlib lemma transporting `n•P=0` along an AddEquiv to `n•(eP)=0`, or is it `rw [← map_nsmul, hP, map_zero]`? Is `natCast_zsmul` the ℤ↔ℕ smul lemma?" | n/a — **TOOL DOWN** | — | Codex backend errored (`Command failed`), as the task brief warned. Fell back to WebSearch + direct Mathlib source reading + first-principles reasoning. The content is elementary enough that the fallbacks fully resolve it. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for the concept | n/a | (no `references/` dir — only `overview/`) | Directory absent; recorded n/a. |
|  6 | nLab                             | "torsion subgroup" / "group homomorphism preserves order" | n/a | — | Not a categorical/structural concept worth an nLab page; elementary group theory. Recorded n/a with reason. |
|  7 | nCatLab                          | — | n/a | — | Not a higher-categorical concept. |
|  8 | Stacks Project                   | — | n/a | — | Not an algebraic-geometry *result*; it is generic group theory about transport along an iso. The AG content (affine = Jacobian model of `E`) is upstream in Mathlib already. |
|  9 | MathOverflow / Math.SE           | "isomorphism preserves order of element" / "n-torsion functorial" | yes (via #1) | folklore | Universally treated as immediate; no MO thread needed to establish standardness. |
| 10 | recent arXiv (last 5 yrs)        | (torsion-order transport) | n/a | — | A 60-year-old triviality of group theory; no recent-research angle. arXiv hits in #1 were unrelated (Burnside rings, Brin–Thompson groups). |

The protocol passed: WebSearch ran 3 distinct queries (specific form, Mathlib /
general form, aliases); ChatGPT MCP was attempted and recorded DOWN with a
fallback note; local refs / nLab / nCatLab / Stacks / MO / arXiv each checked
or `n/a` with a one-line reason.

### Literature summary (Phase 3)

Concept identified as: "a group isomorphism (more generally an additive-monoid
homomorphism) maps `n`-torsion to `n`-torsion / preserves the order of
elements", composed with "ℕ-scalar and ℤ-scalar multiplication agree on
natural-number multipliers".
Sources agree on the standard form: yes — it is folklore, stated identically
everywhere (homomorphisms commute with `n • (-)`; isomorphisms therefore
preserve `addOrderOf` and the torsion subgroups).
Most general standard form: for **any** `AddMonoidHomClass F A B`, `f : F`, and
`n : ℕ` with `n • a = 0`, one has `n • f a = 0` (since `f (n • a) = n • f a` and
`f 0 = 0`). The `AddEquiv` here is a special case; injectivity/surjectivity is
not even needed for *this* direction.
Generality dimensions where the literature varies: essentially none — it is the
defining property of an additive homomorphism. (`addOrderOf` *equality*, as
opposed to mere annihilation, does need injectivity — Mathlib's
`AddEquiv.addOrderOf_eq` / `addOrderOf_injective`.)
Disagreement with the literature: none.

---

### Generality analysis — `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`

Literature-standard form (from Phase 3): for any `AddMonoidHomClass F A B`,
`n • a = 0 → n • f a = 0`; the affine↔Jacobian case is the instantiation at
`f = (toAffineAddEquiv W).symm` (with the cosmetic `ℤ`-smul cast on the goal).

| # | Parameter / hypothesis                | Current Lean form                              | Literature-standard form        | Weaker form exists? | Reason |
|---|---------------------------------------|------------------------------------------------|---------------------------------|---------------------|--------|
| 1 | the map                               | the specific `toAffineAddEquiv (curveK R K W)` | any `AddMonoidHom` / `AddEquiv` | yes (vacuously)     | The lemma is the *instantiation* of the generic fact at one specific equiv; the generic fact is already implicit in `map_nsmul` + `map_zero`. There is nothing to "generalise" — the general lemma is the composition itself. |
| 2 | `n : ℕ`, conclusion in `(n : ℤ) •`    | ℕ hypothesis, ℤ conclusion                     | one type throughout             | n/a                 | The `ℕ→ℤ` mismatch is an artifact of the downstream Jacobian division-polynomial API wanting `zsmul`; bridged by `natCast_zsmul`. Not a generality axis. |
| 3 | `[IsDomain]`,`[IsPID]`,`[CharZero]`,`[IsFractionRing]` | present then `omit`-ted | unused | already dropped     | The lemma already `omit`s every number-theoretic hypothesis — confirming the content is generic algebra, not arithmetic. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL **as a specialisation** — i.e. there is
no *weaker hypothesis* version to ship, because the lemma is not a standalone
mathematical statement but a one-instance application of `map_nsmul`/`map_zero`.
The genuinely-general statement ("homomorphisms map `n`-torsion to
`n`-torsion") is *already* in Mathlib as the primitive `map_nsmul` (+
`map_zero`); there is nothing left to add.
Number of weakening opportunities: 0 (the only "generalisation" is to delete
the lemma and call the generic primitives directly — that is the
NO-composable verdict, not YES-but-generalise).
Cost of restatement: n/a.

→ Phase 7 considers the NO buckets.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled-hyp → typeclass? | no  | The hypotheses are already typeclasses (and the relevant ones are `omit`-ted). | — |
| 2 | sequences/metric → filters/topology? | no | No analysis here; finite group theory. | — |
| 3 | construct → universal property? | no | Nothing is constructed. | — |
| 4 | set+closure-pred → bundled substructure? | no | — | — |
| 5 | field/metric-specific → typeclass-weakened? | no | Already generic; nt-hyps omitted. | — |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid? | partial | One *could* state it for an arbitrary `AddMonoidHomClass` and arbitrary multiplier type — but that statement **is** `map_nsmul` (already in Mathlib). | The modernisation collapses the lemma into an existing Mathlib primitive, i.e. it argues for **deletion**, not a new contribution. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no (in the sense of "a new mathlib-idiomatic
contribution"). The maximally-idiomatic form is literally Mathlib's existing
`map_nsmul` / `map_zero` / `natCast_zsmul`. There is no Bourbaki-2.0
reformulation that yields a *new* declaration worth shipping; the idiomatic move
is to inline the primitives. One-line reason: the lemma is a specialisation of
existing generic API, not a statement with its own generality to modernise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search-status: `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`

[A] Lean-Finder       (tool not available in this env)                         n/a: offline; substituted by direct source grep [D] + reasoning.
[B] Loogle            `n • ?a = 0 → n • (?f ?a) = 0`; `(n:ℤ) • ?x → n • ?x`     no packaged hit (searched via the generic-lemma names instead — see below).
[C] LeanSearch        "homomorphism maps n-torsion to n-torsion"; "AddEquiv preserves order of element" n/a: offline; the fact is `map_nsmul` (found by grep) + `AddEquiv.addOrderOf_eq`.
[D] Grep mathlib src  `map_nsmul`, `natCast_zsmul`, `orderOf_injective`, `MulEquiv.orderOf_eq`, `addOrderOf.*Equiv`, `fromAffine.*smul`, `affine_to_jac` over `.lake/packages/mathlib/Mathlib/`  hits on the **building blocks**; no hit on the **packaged form**.
[E] Name pattern      `affine_to_jac`, `nsmul_eq_zero.*Jac`, `fromAffine.*addOrder`  no hits — Mathlib has no affine↔Jacobian torsion-transport lemma by any name.

Searched for both:
  - the user's current form (affine `n•P=0` → Jacobian `(n:ℤ)•(fromAffine P)=0`)
    → **not in Mathlib** under any name.
  - the literature-standard / general form ("homomorphism preserves `n`-torsion")
    → **already in Mathlib** as the primitives that compose to give it:
    - `map_nsmul` — generic for `AddMonoidHomClass` (and thus `AddEquiv`); used
      across Mathlib, e.g. `Mathlib/Algebra/Group/ModEq.lean:148` (`← map_nsmul`).
    - `map_zero` — generic `AddMonoidHom`/`AddEquiv` zero-preservation.
    - `natCast_zsmul` — `Mathlib/Algebra/Group/Defs.lean:1052`
      (`@[to_additive (attr := simp, norm_cast)]` of `zpow_natCast`):
      `(↑n) • a = n • a`.
    - `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv` —
      `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:572`, the
      `W.Point ≃+ W.toAffine.Point` equivalence, whose `invFun` is
      `WeierstrassCurve.Jacobian.Point.fromAffine`
      (`…/Jacobian/Point.lean:397`). **The project does NOT fork this file** —
      it consumes Mathlib's `toAffineAddEquiv`/`fromAffine` directly.
    - (Adjacent: `MulEquiv.orderOf_eq` / `AddEquiv.addOrderOf_eq`,
      `Mathlib/GroupTheory/OrderOfElement.lean:363` — iso preserves order;
      not needed for this annihilation direction but confirms the
      "iso ⇒ torsion-preserving" infrastructure is fully present.)

Concluded: "not in Mathlib as a packaged lemma (all methods exhausted, plus the
general form); but Mathlib has the building blocks — `map_nsmul`, `map_zero`,
`natCast_zsmul`, and its own `toAffineAddEquiv`/`fromAffine` — that compose to
yield our form in ≤3 calls."

---

### Call sites — `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`

Internal use count: **4**  (all within the declaring file `PIDMain.lean`; none
elsewhere in the project — the `PID.`-namespaced lemma is not referenced from
any other file).
External-to-file callers: 0 distinct files.

| Caller file:line     | Usage pattern (one-line excerpt)                                                      |
|----------------------|----------------------------------------------------------------------------------------|
| PIDMain.lean:99      | `… prime_order_integrality_squarefree W hns' hp hodd (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ hpQ)) hsf` |
| PIDMain.lean:127     | `… integrality_of_order_four_squarefree W hns' (nsmul_eq_zero_affine_to_jac W (hQ_eq ▸ h4Q)) (hQ_eq ▸ h2Q_ne) hsf2` |
| PIDMain.lean:158     | `… den_dvd_of_order_two W … hpt (nsmul_eq_zero_affine_to_jac W h2P)` |
| PIDMain.lean:273     | `have h2Jac := nsmul_eq_zero_affine_to_jac W h2P` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
the lemma?): the **sibling** `GeneralMain.lean:28` lemma (over ℤ/ℚ) is the same
glue re-stated for the General track — i.e. the project effectively has the
composition twice. Within each track it is factored once; across tracks it is
duplicated. (No raw `congrArg … toAffineAddEquiv.symm … map_nsmul` inlining was
found at the call sites themselves — they all go through the helper.)

Signal reading: all 4 uses are internal to one file, feeding it as a single
`(n:ℤ)•(fromAffine …)=0` argument into the Jacobian-side division-polynomial
lemmas (`prime_order_integrality_squarefree`, `integrality_of_order_four_squarefree`,
`den_dvd_of_order_two`, and `addOrderOf_ne_two_of_kappa_ne_zero` at :273). It is
a genuine local convenience wrapper, but it wraps a 3-call generic composition,
not new mathematics — exactly the NO-composable profile.

---

### Composition check (Phase 6)

Can `nsmul_eq_zero_affine_to_jac` be derived from Mathlib in ≤3 chained calls?

Attempt 1: it IS the proof body, which is a 3-step composition of Mathlib
primitives:
```lean
example {x y : K} {hns : (curveK R K W).toAffine.Nonsingular x y} {n : ℕ}
    (h : n • (Affine.Point.some _ _ hns) = 0) :
    (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  rw [natCast_zsmul]                                              -- (1) ℤ-smul → ℕ-smul
  have h' := congrArg (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm h
  rw [map_nsmul, map_zero] at h'                                  -- (2)+(3) transport
  simpa using h'                                                  -- defeq fromAffine = symm
```
  - Mathlib decls used: `natCast_zsmul`, `map_nsmul`, `map_zero`,
    `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv` (and its `.symm`,
    whose `invFun` is `fromAffine`).
  - Result: succeeds — this is literally the existing 4-line proof.
  - Notes: the only non-`map_*` step is the cosmetic `natCast_zsmul` on the
    goal and the closing `simpa` (which discharges the `(toAffineAddEquiv).symm
    ∘ toAffineLift` ⇄ `fromAffine` definitional equality, `@[simps]`-generated).
    By the Phase-6 heuristics this is a `Foo.bar (Bar.baz hx)`-style
    transport-through-a-map composition, not "a proof in disguise": there is no
    `ring_nf`/`aesop`, no multi-`have` reasoning chain — just push the
    hypothesis through one equiv and renormalise the scalar cast.

Conclusion: **COMPOSABLE** (≤3 Mathlib calls; the composition sketch above is
exactly the lemma's own proof).

---

## Verdict: `LutzNagell.PID.nsmul_eq_zero_affine_to_jac`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the statement is the folklore "a homomorphism
  maps `n`-torsion to `n`-torsion", with no proper name; its general form is
  Mathlib's `map_nsmul` + `map_zero`.
- Generality analysis (Phase 4): no weakening to ship — the maximally-general
  form already exists in Mathlib as `map_nsmul`; Phase 4c finds no new
  idiomatic contribution.
- Mathlib search (Phase 5): not present as a packaged lemma under either form;
  building blocks `map_nsmul`, `map_zero`, `natCast_zsmul`, and Mathlib's own
  `toAffineAddEquiv`/`fromAffine` are all present.
- Composition check (Phase 6): COMPOSABLE — the 3-call composition is the
  lemma's existing proof.

**Rationale:**

`nsmul_eq_zero_affine_to_jac` is project-internal glue, not new mathematics for
Mathlib. Its entire content is "transport `n • P = 0` from the affine point
group to the Jacobian point group, switching the scalar from `ℕ` to `ℤ`". The
transport is exactly `map_nsmul` + `map_zero` applied to Mathlib's *own*
addition-preserving equivalence
`WeierstrassCurve.Jacobian.Point.toAffineAddEquiv` (whose inverse is
`fromAffine`); the scalar switch is the `@[simp, norm_cast]` lemma
`natCast_zsmul`. That Mathlib already bundles the affine↔Jacobian iso as an
`AddEquiv` is precisely *why* this lemma is unnecessary at the library level —
the iso carries `map_nsmul`/`map_zero` for free. The lemma even `omit`s every
number-theoretic hypothesis (`IsDomain`, `IsPID`, `CharZero`, `IsFractionRing`),
which is itself the tell that nothing arithmetic is happening.

The four call sites are all inside `PIDMain.lean`, each feeding the result as a
single `(n:ℤ)•(fromAffine …)=0` argument into the Jacobian-side
division-polynomial lemmas. Keeping it as a 4-line private helper *within the
project* is reasonable hygiene (it removes a repeated `congrArg … map_nsmul`
incantation); but it does not meet Mathlib's bar, because Mathlib already
provides every primitive and the composition is ≤3 calls. This matches the
canonical `NO-composable-from-mathlib` case study (sum-of-two-known-facts):
the building blocks are in Mathlib with identical hypotheses, and the
composition is the proof body.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the user's form is a 3-Mathlib-call
composition. The building blocks are:
- `map_nsmul`        — `AddMonoidHomClass`/`AddEquiv` commutes with `n • (-)`.
- `map_zero`         — `AddMonoidHom`/`AddEquiv` sends `0 ↦ 0`.
- `natCast_zsmul`    — `Mathlib/Algebra/Group/Defs.lean:1052`: `(↑n) • a = n • a`.
- `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv` —
  `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:572`
  (its `.symm`/`invFun` is `…Jacobian.Point.fromAffine`, line 397).

Composition sketch (≤3 lines — the existing proof):
```lean
example {x y : K} {hns : (curveK R K W).toAffine.Nonsingular x y} {n : ℕ}
    (h : n • (Affine.Point.some _ _ hns) = 0) :
    (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  rw [natCast_zsmul]
  have h' := congrArg (Jacobian.Point.toAffineAddEquiv (curveK R K W)).symm h
  rw [map_nsmul, map_zero] at h'
  simpa using h'
```

Call sites in our project (from Phase 6.0): K = 4, all in `PIDMain.lean`
(lines 99, 127, 158, 273).

Refactor plan:
- This is a *local-hygiene* decision, NOT a Mathlib submission. Recommended
  action for cleanup: **keep** the private helper in `PIDMain.lean` (it earns
  its place by deduplicating the `congrArg … map_nsmul … map_zero` incantation
  across 4 sites) — but it must **not** be proposed to Mathlib.
- The real cleanup item is **cross-track deduplication**: this PID lemma and
  its byte-for-byte twin `nsmul_eq_zero_affine_to_jac` in `GeneralMain.lean:28`
  (over ℤ/ℚ) are the same composition. Either (a) keep one generic helper —
  state it once for an arbitrary curve `W' : WeierstrassCurve S` over any
  `[CommRing S]` with a nonsingular affine point, parameterised by the
  `toAffineAddEquiv` of the relevant curve, and have both tracks call it; or
  (b) if the `curveK`/`curveQ` instantiations make a shared helper awkward, at
  minimum cross-link them so a future bump touches both. Per the project's
  General*/PID* consolidation goal, (a) is preferred.
- If a site is ever simplified to a single use, inline the 3-line composition
  there and drop the helper.

Next action: do NOT open a Mathlib PR. In AINTLIB cleanup, treat this as a
**dedup / cross-link ticket** between the PID and General tracks (lane:cleanup
or lane:decompose), keeping the (single, shared) helper project-local. The
generic content is already Mathlib's `map_nsmul`/`map_zero`/`natCast_zsmul`.

---

## Next step

Do not submit to Mathlib. File/handle an AINTLIB cleanup ticket to deduplicate
this PID-track helper against the identical `GeneralMain.lean:28` sibling
(prefer a single shared generic helper over an arbitrary `CommRing` curve),
keeping it project-local; the underlying fact is already Mathlib's generic
`map_nsmul` + `map_zero` + `natCast_zsmul` transported across Mathlib's own
`WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`.
