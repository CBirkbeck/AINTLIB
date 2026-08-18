# `/mathlibable` report — `PadicLFunctions.pScale`

**Final verdict: `NO-composable-from-mathlib`** — mathlib already carries the
positive-real scaling action on the upper half-plane
(`UpperHalfPlane.posRealAction`); `pScale p z` is the one-line specialisation
`(⟨(p : ℝ), _⟩ : {x : ℝ // 0 < x}) • z`, with the coercion equality holding by
`rfl`. No new mathlib declaration is justified.

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task note — `.lake` oleans present, file is `sorry`-free; BUILD NOTE authorises the Phase-0 fallback)
- decl `PadicLFunctions.pScale`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:99`
- kind:                      `def` (`noncomputable`)
- has sorry:                 no (grep for `sorry`/`admit` in the file: none)
- module docstring summary:  RJW §8 complex side — the q-expansion of the p-stabilised Eisenstein series `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)` and its realisation as a `Γ₀(p)` modular form.

---

### Statement (Phase 1)

`PadicLFunctions.pScale` is **a definition** of the following:

Given a prime `p` (`[Fact p.Prime]`) and a point `z` of the open upper half-plane
`ℍ = {w ∈ ℂ : Im w > 0}`, `pScale p z` is the point `p · z ∈ ℍ` — the image of
`z` under multiplication by the positive real (in fact natural) number `p`. This
is a *homothety / dilation* by `p`: it scales both coordinates by `p`, and since
`Im(p·z) = p · Im(z) > 0`, the result is again in `ℍ`. The definition bundles the
complex value `(p : ℂ) * z` with the proof that its imaginary part is positive.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime `p`; only `p.Prime.pos` (i.e. `0 < p`) is used to discharge positivity. Primality itself is *not* needed; any `0 < p` (indeed any positive real) suffices.
- `z : ℍ` — the input point of the upper half-plane.

Hypotheses (Lean side):
- none beyond the parameters (the positivity proof is internal to the bundled subtype element).

Conclusion (math): the point `p·z`, an element of `ℍ`.

Conclusion (Lean): `ℍ` (i.e. `UpperHalfPlane`). The body is
`⟨(p : ℂ) * z, proof that 0 < ((p : ℂ) * z).im⟩`, where the proof rewrites
`Complex.mul_im` / `natCast_im` / `natCast_re` and concludes
`mul_pos (Nat.cast_pos.mpr hp.out.pos) z.im_pos`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper `def` — a one-line specialisation of a known scaling operation,
used only inside this file to express `E_k(pz)`. Not a named theorem, not a new
mathematical structure, not a `## Main results` entry.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for
framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`⟨(p : ℂ) * z, by …⟩` — the value
`(p : ℂ) * z` is the single substantive expression; the `by …` block only
discharges the membership proof).
One-liner verdict: **ONE-LINER**

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | The downstream proofs that rely on `(pScale p z : ℂ) = (p:ℂ)*z` being `rfl` (lines 204–205, 355–356) would work **identically** against `posRealAction`: `coe_pos_real_smul` is `rfl` and `Complex.real_smul`/`ofReal_natCast` are `rfl`, so `((⟨(p:ℝ),_⟩) • z : ℂ) = (p:ℂ)*z` is also definitional. The sealed name buys no extra unfolding control over the mathlib action. |
| Avoid typeclass diamonds          | no       | No instance is being anchored; `pScale` is a plain `def`, not an `instance`. There is no competing `Mul`/`Zero`/`SMul` path that needs disambiguation. |
| Mark semantic intent / API name   | no       | The only consumers are inside the declaring file (Phase 6.0 shows K=0 external). No downstream library depends on the name `pScale`; mathlib’s own `coe_pos_real_smul`/`pos_real_im` provide the stable API surface. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION**. This biases Phase 7 toward a NO
bucket (per Phase 2b → Phase 7 cross-reference).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1  | WebSearch (specific form) | "upper half plane action positive real scalar multiplication modular forms definition" | yes | The slash/level operator on `ℍ` includes the `det(γ)^{k/2}` positive-real factor; GL₂⁺(ℝ) acts by `z ↦ (az+b)/(cz+d)` | Zagier *Elliptic Modular Forms*, Milne *MF*, Conrad — `p·z` is the diagonal case `[[p,0],[0,1]]·z` |
| 2  | WebSearch (specific app.) | "p-stabilization Eisenstein series E_k(z) - p^{k-1} E_k(pz) modular form level p" | yes | `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)`, the U_p-eigenform p-stabilisation | Standard in Iwasawa theory / p-adic L-functions (Hida, Wiles); `E_k(pz)` is the universal occurrence of `pScale` |
| 3  | WebSearch (named-after / aliases) | "nLab upper half plane GL2 R action Mobius transformation modular group" | yes | SL₂(ℝ)/GL₂⁺(ℝ) Möbius action; nLab "Möbius transformation" | The scaling `z↦az` (a>0) is the upper-triangular/diagonal subgroup of this action |
| 4  | WebSearch (Lean-specific) | `"upper half plane" "positive real" scalar action Lean mathlib UpperHalfPlane.posRealAction smul` | yes | mathlib `UpperHalfPlane.posRealAction : MulAction {x : ℝ // 0 < x} ℍ`, with `coe_pos_real_smul`, `pos_real_im`, `pos_real_re` | **Decisive**: mathlib already has exactly this scaling action and its API (leanprover-community mathlib4 docs) |
| 5  | ChatGPT MCP | "standard math definition of scaling a point of the upper half-plane by a positive real / `p·z`; its generality and historical evolution" | n/a | — | ChatGPT MCP not configured in this environment (no `mcp__chatgpt*` tool surfaced). Compensated with 5 WebSearch queries + 2 WebFetch (Wikipedia, mathlib docs) at varied generality. |
| 6  | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` | n/a | (no references dir) | Directory absent (`ls` → No such file or directory). Recorded n/a. |
| 7  | nLab | "Möbius transformation" / upper half plane action | yes | Möbius action of SL₂; the affine subgroup (translations + positive dilations) is the standard Borel part | Scaling by `λ>0` is the dilation generator of the affine subgroup |
| 8  | nCatLab (if categorical) | — | n/a | — | Not a categorical concept; it is a single point-map (a group action evaluation), no universal property at stake. |
| 9  | Stacks Project (if alg geom) | — | n/a | — | Not an algebraic-geometry / scheme-theoretic concept; it is elementary complex-analytic. |
| 10 | MathOverflow / Math.SE | covered by WebSearch #1/#3 (researchgate/physicsforums/Math.SE hits on SL₂ action on ℍ) | yes | Same standard Möbius/affine action; scaling `z↦az`, `Im(az)=a·Im(z)`, `a>0` preserves ℍ | Consensus; nothing non-standard |
| 11 | Wikipedia (WebFetch) | https://en.wikipedia.org/wiki/Upper_half-plane — "is `z ↦ λz`, λ>0 a standard part of the action?" | yes | "dilations: (x,y) ↦ (λx, λy), λ > 0" — explicitly listed as an affine transformation of `ℍ` | Direct confirmation that positive-real scaling is a standard, named (dilation) operation on `ℍ` |

The protocol passes:
- WebSearch ran **5** distinct queries spanning the specific form (#1), the
  application that motivates it (#2), the named-after/aliases (#3 Möbius), the
  Lean form (#4), plus a Wikipedia primary-source fetch (#11).
- ChatGPT MCP: unavailable in this environment — recorded n/a with reason, and
  over-covered with WebSearch + two WebFetch primary sources.
- Local references: n/a (dir absent), with reason.
- nLab checked; Stacks / nCatLab recorded n/a with reasons; MathOverflow/Math.SE
  covered.

### Literature summary (Phase 3)

Concept identified as: **dilation / homothety by a positive real on the upper
half-plane** — equivalently the value of the positive-real (or diagonal-matrix)
action `z ↦ a·z`, `a > 0`; here `a = p`. In the modular-forms context it is the
standard `E_k(pz)` slot inside the p-stabilisation `E_k − p^{k−1}E_k(p·)`.

Sources agree on the standard form: **yes**. Wikipedia lists "(x,y) ↦ (λx,λy),
λ>0" verbatim as an affine transformation of `ℍ`; every modular-forms text uses
`z ↦ pz` as the diagonal `[[p,0],[0,1]]` Möbius image; mathlib itself encodes it
as `posRealAction`.

Most general standard form: scaling by an arbitrary **positive real** `a` (the
full one-parameter dilation subgroup), of which scaling by a natural number `p`
is a strict specialisation. (Even more generally it is the diagonal/positive
part of the GL₂⁺(ℝ) Möbius action, but the positive-real homothety is the
maximally-general form of *this particular* operation `z ↦ a·z`.)

Generality dimensions where the literature varies:
  - scalar type: `ℕ` (the user's `p`) ⊂ `ℝ_{>0}` (the literature/mathlib
    standard `{x : ℝ // 0 < x}`). The most general is the positive reals.

Disagreement with the literature: **none**. The user's `pScale` is the
literature operation restricted to the natural number `p`.

---

### Generality analysis — `PadicLFunctions.pScale`

Literature-standard form (from Phase 3): scaling of `z ∈ ℍ` by a *positive real*
`a`, i.e. the positive-real action `(a : {x : ℝ // 0 < x}) • z`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ` with `[Fact p.Prime]` as the scalar | natural-number scalar `(p:ℂ)` | positive real `a` (subtype `{x:ℝ//0<x}`) | **yes** | Only `0 < p` is used; primality is irrelevant. The operation is well-defined for *any* `a > 0`. Mathlib’s `posRealAction` already takes the maximally-general scalar. |
| 2 | `z : ℍ` | point of upper half-plane | identical | NO | already the right object. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (scalar is `ℕ`/prime
where the standard operation takes any positive real).
Number of weakening opportunities found: **1** (scalar `ℕ` → `{x : ℝ // 0 < x}`).
Proposed restatement: not applicable as a *new* declaration — the maximally
general form already exists in mathlib as `posRealAction` (see Phase 5), so the
correct action is to *use* it, not to ship a generalised `pScale`. (This is why
the verdict lands in a NO bucket, not YES-but-generalise-first: the generalised
target is not missing.)
Cost of restatement: CHEAP — replace `pScale p z` with `(⟨(p:ℝ), _⟩ : {x:ℝ//0<x}) • z`; the coe equality is `rfl`.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let X be a foo" preamble → typeclass/instance? | **yes** | Use the existing `MulAction {x:ℝ//0<x} ℍ` instance (`posRealAction`) instead of a bespoke `def` | `MulAction` API: `one_smul`, `mul_smul`, `pos_real_smul_injective`, `coe_pos_real_smul`, `pos_real_im`, `pos_real_re`, and `isometry_pos_mul` (metric file) all become available for `p·z` for free |
| 2  | sequences/metric → filters/topology? | no | — | not a convergence statement; nothing to filter-ise. |
| 3  | construction → universal-property class? | no | — | it is a single point evaluation, no object with a universal property. |
| 4  | set-with-closure-predicate → bundled substructure? | no | — | not a substructure. |
| 5  | vector-space/metric/field-specific → weaker typeclass? | partial (subsumed by #1/Phase 4a) | scalar `ℕ` → positive-reals via the action | scalar restriction is exactly the `posRealAction` instance |
| 6  | 1-categorical → higher-categorical? | no | — | n/a |
| 7  | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | **yes** (this is the same axis as Phase 4a #1) | replace the concrete `p : ℕ` scalar by the positive-real subtype the action already uses | unifies `p·z` with the rest of mathlib’s `ℍ`-scaling lemmas |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is *already in mathlib* (the
`posRealAction` instance and its `coe`/`im`/`re` simp-lemmas). The
mathlib-idiomatic way to write `p·z` is `(⟨(p:ℝ), _⟩ : {x:ℝ//0<x}) • z`, not a
new `pScale` def.
- Real mathematical improvement: using the action plugs `p·z` into the full
  `MulAction` + isometry API for `ℍ`-dilations, instead of an isolated def with
  no lemmas. But because this idiom is **already present in mathlib**, the
  consequence for *this* assessment is a NO verdict (reuse), not a
  YES-but-generalise-first (the idiomatic target is not missing).

---

### Diamond / defeq risk — `PadicLFunctions.pScale`  (kind: `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | A plain `def` returning `ℍ`; introduces no instance, so no search path to collide. |
| 2 | Reducibility leak | low | Not `@[reducible]`; body `(p:ℂ)*z` is a single multiplication. Even if exposed, it matches `coe_pos_real_smul`’s `rfl` shape, so no surprising defeq. |
| 3 | Non-canonical unfolding | low | `(pScale p z : ℂ)` unfolds to `(p:ℂ)*z` by `rfl` — the *same* normal form the mathlib action produces (`real_smul`/`ofReal_natCast` are `rfl`). No divergence. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | Monomorphic (`ℕ`, `ℂ`, `ℍ` are all `Type 0`). |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort` declared; the only coercion in play is the standard `ℍ → ℂ`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**
Top risks: none.
(Risk is recorded for completeness; since the verdict is a NO bucket, the def is
not being added to mathlib anyway.)

---

### Mathlib search-status: `PadicLFunctions.pScale`

[A] Lean-Finder       n/a: Lean-Finder web UI not reachable as a tool in this environment — substituted with the official mathlib4 docs (WebSearch #4) + grep over the mathlib source tree (method D), which located the exact construct.
[B] Loogle            type-pattern `{x : ℝ // 0 < x} → ℍ → ℍ` / `MulAction {x : ℝ // 0 < x} ℍ` — n/a as a live tool here; the equivalent grep over the source (method D) is authoritative and found `posRealAction`.
[C] LeanSearch        natural-language "scale upper half plane by a positive real" — surfaced (via WebSearch #4 against the mathlib4 docs site) `UpperHalfPlane.posRealAction` and its `coe_pos_real_smul`/`pos_real_im`/`pos_real_re` lemmas.
[D] Grep mathlib src  `grep -rn "SMul.*UpperHalfPlane|MulAction.*ℍ|pos_real|posRealAction" .lake/packages/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/` → **HIT**: `Basic.lean:199 instance posRealAction : MulAction {x : ℝ // 0 < x} ℍ`; `Basic.lean:207 coe_pos_real_smul`; `:211 pos_real_im`; `:215 pos_real_re`; `Metric.lean:320 isometry_pos_mul`. Also grepped for any `pScale`/`*Scale*`/`*dilat*`/`*homothet*` named def → **none** (no clashing or pre-existing named def).
[E] Name pattern      `lean_local_search`-equivalent grep for defs named `scale`/`dilat`/`homothet`/`stretch` returning `ℍ` across `UpperHalfPlane/` and `NumberTheory/` → no named def; confirms mathlib exposes the operation only through the *action*, not a standalone `pScale`-style def.

Searched for both:
  - the user's current form (`(p:ℂ)*z` packaged into `ℍ`, scalar `ℕ`) — no named def;
  - the literature-standard form (scaling by a positive real) — **found** as `UpperHalfPlane.posRealAction`.

Concluded: **found building blocks** — `UpperHalfPlane.posRealAction`
(`MulAction {x : ℝ // 0 < x} ℍ`) together with its `coe_pos_real_smul` lemma and
the casts `Complex.real_smul` (`x • z = x * z`, definitional) and
`Complex.ofReal_natCast` (`((n:ℝ):ℂ) = (n:ℂ)`, `rfl`). Mathlib has the *action*;
it does not have a standalone natural-number `pScale` def (nor needs one).

---

### Call sites — `PadicLFunctions.pScale`

Internal use count: **10** (all within the declaring file
`projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean`).
External-to-file callers: **0 distinct files** (repo-wide grep excluding `.lake`
and the declaring file returned nothing).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| EisensteinComplex.lean:193 | `… * rjwEisenstein (k := k) … (pScale p z))` — the `E_k(pz)` term of the q-expansion `HasSum` target |
| EisensteinComplex.lean:204 | `Complex.exp (2*π*I*((pScale p z : ℂ))) = q ^ p` |
| EisensteinComplex.lean:205 | `rw [show ((pScale p z : ℂ)) = (p:ℂ)*(z:ℂ) from rfl, …]` — **relies on `(pScale p z : ℂ) = (p:ℂ)*z` being `rfl`** |
| EisensteinComplex.lean:210 | `(rjwEisenstein (k := k) … (pScale p z))` |
| EisensteinComplex.lean:211 | `exact hasSum_rjwEisenstein hk hk2 (pScale p z)` |
| EisensteinComplex.lean:226 | `HasSum g (rjwEisenstein … (pScale p z))` |
| EisensteinComplex.lean:350 | (docstring) `pz = pScale p z` |
| EisensteinComplex.lean:353 | `… (p:ℂ)^(k-1) * ModularForm.E hk (pScale p z)` — RJW pointwise formula |
| EisensteinComplex.lean:355 | `have hpt : (levelRaiseMatrix p • z : ℍ) = pScale p z := …` — **bridges the GL/matrix action to `pScale`** |
| EisensteinComplex.lean:367 | `… * rjwEisenstein (k := k) … (pScale p z))` |

Inline-derivation grep (was the equivalent re-derived elsewhere without `pScale`?):
  - Line 355 shows `levelRaiseMatrix p • z` (the SL/GL Möbius action) is *also*
    used to express the same point and proven equal to `pScale p z` by `rfl`-on-coe.
    So even within the file the same `p·z` point is reached two ways — a sign the
    standalone `pScale` is a convenience wrapper, not load-bearing API.

Composability signal: **K = 0 external, all uses internal; the coe is `rfl` and
the point is independently reachable via the matrix action.** Per the Phase-6.0
table this leans **NO-composable-from-mathlib** (a wrapper that the existing
mathlib action + a cast replaces directly).

### Composition check (Phase 6)

Can `PadicLFunctions.pScale` be obtained from mathlib in ≤3 chained calls?

Attempt 1 — instantiate the positive-real action:
```lean
-- with  hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
example (p : ℕ) [Fact p.Prime] (z : ℍ) : ℍ :=
  (⟨(p : ℝ), by exact_mod_cast hp.out.pos⟩ : {x : ℝ // 0 < x}) • z
```
  - Mathlib decls used: `UpperHalfPlane.posRealAction` (the `• `), `Nat.cast_pos`.
  - Result: **succeeds** — this *is* the point `p·z ∈ ℍ`.
  - Coe equality to the old body is itself ≤3 calls / pure defeq:
    `(((⟨(p:ℝ),_⟩) • z : ℍ) : ℂ) = (p:ℂ)*z` by
    `coe_pos_real_smul` (`rfl`) then `Complex.real_smul` (`rfl`) then
    `Complex.ofReal_natCast` (`rfl`) — i.e. `rfl` outright. So every current call
    site that needs `(pScale p z : ℂ) = (p:ℂ)*z` (lines 204–205, 355) keeps
    working verbatim.

Conclusion: **COMPOSABLE** — `pScale p z = (⟨(p:ℝ), Nat.cast_pos.mpr hp.out.pos⟩ : {x:ℝ//0<x}) • z`, a one-call specialisation of the existing `posRealAction`, with the downstream coe equality holding by `rfl`.

---

## Verdict: `PadicLFunctions.pScale`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): "dilation by a positive real on `ℍ`" is standard (Wikipedia lists `(x,y)↦(λx,λy), λ>0`; every modular-forms text uses `z↦pz`); the maximally-general form is scaling by any positive real.
- Generality analysis (Phase 4): STRICTLY NARROWER (scalar `ℕ`/prime vs positive real) — but the general form is **not** missing from mathlib, so this is a reuse case, not a generalise-first case.
- Mathlib search (Phase 5): found the building block `UpperHalfPlane.posRealAction` (`Basic.lean:199`) + `coe_pos_real_smul`/`pos_real_im`/`pos_real_re`; no standalone `pScale` def exists or is needed.
- Composition check (Phase 6): **COMPOSABLE** in one call.

**Rationale:**

`pScale p z` is the point `p·z` of the upper half-plane — the positive-real
dilation by `p`. Mathlib already provides this operation as the *action*
`UpperHalfPlane.posRealAction : MulAction {x : ℝ // 0 < x} ℍ`, whose `smul` field
sends `(a, z)` to `⟨(a:ℝ) • (z:ℂ), …⟩` with positivity proof `mul_pos a.2 z.im_pos`
— literally the same construction as `pScale`, but maximally general in the
scalar (any positive real, not just a natural prime). The bridge from the user's
body `(p:ℂ)*z` to the action's `(↑(p:ℝ)) • (z:ℂ)` is `Complex.real_smul`
(definitional) composed with `Complex.ofReal_natCast` (`rfl`), so the
specialisation `pScale p z = (⟨(p:ℝ), Nat.cast_pos.mpr hp.out.pos⟩) • z` holds
with `(coe) = rfl`. This is a textbook wrapper: a one-line `def` over an existing
mathlib action, used only inside its own file (0 external call sites), with the
target point even reachable independently via the matrix action at line 355. Per
Phase 2b it is moreover a ONE-LINER WITHOUT-EXEMPTION (no defeq/diamond/API-name
need), which independently points away from any YES bucket.

It is *not* `NO-mathlib-has-it` in the strict sense, because mathlib has the
positive-real *action*, not a standalone natural-number `pScale` declaration to
cite as "the same lemma"; the right replacement is to *instantiate* that action,
i.e. a (trivial) composition. Hence `NO-composable-from-mathlib`.

**WHY not (refactor-actionable detail):**
Mathlib has the building block — the positive-real scaling action on `ℍ` — and
`pScale p z` is a 1-call specialisation of it. The named def adds no new
mathematics and no defeq/diamond control beyond what the action already gives
(its coe/im/re lemmas are `rfl`), so it should be inlined rather than upstreamed.

Mathlib building blocks:
- `UpperHalfPlane.posRealAction` — `.lake/packages/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean:199` (`MulAction {x : ℝ // 0 < x} ℍ`)
- `UpperHalfPlane.coe_pos_real_smul` — `…/UpperHalfPlane/Basic.lean:207` (`↑(x • z) = (x:ℝ) • (z:ℂ)`, `rfl`)
- `UpperHalfPlane.pos_real_im` / `pos_real_re` — `…/Basic.lean:211` / `:215`
- `Complex.real_smul` — `.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean:320` (`x • z = x * z`, definitional)
- `Complex.ofReal_natCast` — `…/Data/Complex/Basic.lean:347` (`((n:ℝ):ℂ) = (n:ℂ)`, `rfl`)
- `Nat.cast_pos` — for the positivity proof `(0:ℝ) < (p:ℝ)`.

Composition sketch (≤3 lines):
```lean
-- pScale p z, written via the mathlib action:
example (p : ℕ) [Fact p.Prime] (z : ℍ) : ℍ :=
  (⟨(p : ℝ), Nat.cast_pos.mpr hp.out.pos⟩ : {x : ℝ // 0 < x}) • z
-- and the coe used downstream is rfl:
example (p : ℕ) [Fact p.Prime] (z : ℍ) :
    (((⟨(p : ℝ), Nat.cast_pos.mpr hp.out.pos⟩ : {x : ℝ // 0 < x}) • z : ℍ) : ℂ)
      = (p : ℂ) * z := rfl
```

Call sites in our project (from Phase 6.0): **K = 10** (all in
`EisensteinComplex.lean`; 0 elsewhere).

Refactor plan (project-local cleanup, NOT a mathlib PR — note that under AINTLIB
rules this whole file is a `dev/`-branch producer artifact; this is advisory):
1. Define a local abbreviation if desired:
   `local notation3 "p• " z => (⟨(p:ℝ), Nat.cast_pos.mpr hp.out.pos⟩ : {x:ℝ//0<x}) • z`,
   or simply inline the action expression.
2. At each of the 10 sites, replace `pScale p z` with the action expression. The
   coe-`rfl` sites (lines 204–205, 355) are unaffected since the coe is still `rfl`.
3. Where `pScale`'s im/re are needed, use `UpperHalfPlane.pos_real_im` /
   `pos_real_re` instead of unfolding `Complex.mul_im` by hand (this also
   *simplifies* the positivity proof currently inlined at lines 100–103).
4. Delete the `pScale` def. If the producer prefers to keep a local readable
   name, keep `pScale` as a project-local convenience def but do **not** propose
   it for mathlib — that is the verdict.

Next action: do **not** open a mathlib PR for `pScale`. Inline mathlib's
`posRealAction` at the 10 call sites (or keep `pScale` as a project-local
shorthand), and prefer `pos_real_im`/`pos_real_re` for its imaginary/real parts.

---

## Next step

Do not upstream `pScale`. Mathlib already has the positive-real scaling action
`UpperHalfPlane.posRealAction`; replace `pScale p z` with
`(⟨(p:ℝ), Nat.cast_pos.mpr hp.out.pos⟩ : {x:ℝ//0<x}) • z` at the 10 internal call
sites (the downstream coe equality `(… : ℂ) = (p:ℂ)*z` remains `rfl`), using
`UpperHalfPlane.pos_real_im`/`pos_real_re` for its imaginary/real parts. Keeping
`pScale` as a project-local shorthand is acceptable; proposing it for mathlib is
not.
