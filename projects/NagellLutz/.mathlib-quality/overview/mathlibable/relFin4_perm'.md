# /mathlibable report — `EllSequence.relFin4_perm'`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoning from source). Mathlib package present at `.lake/packages/mathlib` pinned at rev `d90090f647ca`, toolchain `leanprover/lean4:v4.31.0-rc2`.
- decl `EllSequence.relFin4_perm'`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:544`
- kind:                      lemma (theorem-class — no defeq / typeclass / coercion surface)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS); defines `IsEllSequence`/`normEDS`/`complEDS`, proves `normEDS` is an EDS. This file is a **project fork+extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (it adds the entire `addMulSub`/`rel₄`/`net`/`relFin4` four-index-relation development that upstream does not have).

**Qualified name VERIFIED:** `namespace EllSequence` opens at line 90; there is **no** intervening sub-namespace between it and line 544 (the `section Perm` at line 509 and `section Rel₄OfValid` that closed at line 507 are plain `section`s, not namespaces). Hence the full name is **`EllSequence.relFin4_perm'`** — exactly the brief's parsed name. (It is a plain `lemma`, not `protected`.)

The exact source (lines 544–545):
```lean
lemma relFin4_perm' (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]
```
Section context (lines 511–512): `variable (neg : ∀ k, W (-k) = -W k)` with `include neg`. So the real signature is
`relFin4_perm' (neg : ∀ k, W (-k) = -W k) (σ : Perm (Fin 4)) (t : Fin 4 → ℤ) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t`.

---

### Statement (Phase 1)

`EllSequence.relFin4_perm'` is the **sign-cancelled rearrangement** of its immediate sibling `relFin4_perm` (line 533). Where `relFin4_perm` says

> `relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t`  (permuting the four indices multiplies the relation by `sgn σ ∈ ℤˣ`),

`relFin4_perm'` moves the sign unit to the other side:

> `Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t`.

Mathematically these are the *same fact* — that the four-index expression `rel₄ W (t 0) (t 1) (t 2) (t 3)` (the alternating sum of the three pairings of `addMulSub`-products) is **sign-equivariant under `Perm (Fin 4)`** — because `sgn σ` is its own inverse in `ℤˣ` (`sgn σ · sgn σ = 1`), so `s • x = y ⟺ x = s • y`. The primed version is the convenient orientation used when you want to *push a `sgn σ` onto a permuted relation and read off the unpermuted one* (e.g. when sorting the index tuple into descending order and then discharging the resulting sign).

Variables / typeclasses (Lean side):
- `R` (from the ambient section): a `CommRing` — the codomain of the sequence `W : ℤ → R`.
- `W : ℤ → R`: the elliptic sequence.
- `neg : ∀ k, W (-k) = -W k`: `W` is an odd function (the only hypothesis used; needed because `relFin4_perm`, which this rewrites by, relies on the `rel₄_swap` sign lemmas that use oddness of `W`).
- `σ : Perm (Fin 4)`: an arbitrary permutation of the four index positions.
- `t : Fin 4 → ℤ`: the index tuple.

Hypotheses: none beyond `neg` and the data.

Conclusion (math): the four-index relation is `Perm (Fin 4)`-sign-equivariant, written with the sign cancelled onto the permuted side.
Conclusion (Lean): `Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t`.

Proof (1 line): `rw [relFin4_perm neg]` turns the LHS into `Perm.sign σ • (Perm.sign σ • relFin4 W t)`; `← mul_smul` collapses the two `•` into `(Perm.sign σ * Perm.sign σ) • relFin4 W t`; `Int.units_mul_self` (mathlib) rewrites `Perm.sign σ * Perm.sign σ = 1`; `one_smul` finishes.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper lemma. Not a named theorem, not a `## Main results` entry, introduces no structure. It is the primed/rearranged twin of `relFin4_perm`, and it exists only to present the same sign-equivariance fact in the orientation the one downstream caller needs. (Even its meatier sibling `relFin4_perm` is internal API for a bespoke object — but `relFin4_perm'` is strictly downstream of it.)

### One-line check (Phase 2b)

Kind is `lemma` (not a `def`/`abbrev`/`structure`) → the one-line-**def** check is **n/a**. (The body is a 1-line tactic *proof*, which is a separate matter — and that 1-line proof, being a pure rearrangement of `relFin4_perm` via two mathlib `smul` lemmas, is itself the central composability signal; see Phase 6.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic net relation symmetric under permutation of indices sign Stange division polynomial"          | partial | the four-index/net relation and its index symmetries appear in Ward/Stange-style work | The *relation* and its permutation symmetry are studied; the **sign-cancelled rearrangement of the sign-equivariance identity** is never isolated as a named result. |
|  2 | WebSearch (general form)         | "mathlib Perm.sign smul cancel Int.units_mul_self alternating form permutation invariant up to sign"     | yes  | mathlib's alternating-map sign-equivariance: `AlternatingMap.map_perm` (`f (v ∘ σ) = sgn σ • f v`) + `map_swap`; `Int.units_mul_self : (u : ℤˣ) → u * u = 1` | This is the *generic* pattern. mathlib has it for multilinear **alternating maps**; `rel₄` is a bespoke ℤ→R expression that is *not* registered as an `AlternatingMap`, so the generic lemma does not apply directly. |
|  3 | WebSearch (named-after / aliases)| "On Symmetries of Elliptic Nets" Ward elliptic divisibility sequence permutation symmetry                | yes  | arXiv:1408.6623 generalises Ward's symmetry theorem to elliptic nets; arXiv:2604.05280 "On Elliptic Sequences over Commutative Rings" develops the `rel₄`-style relations | The Lean file formalises arXiv:2604.05280. The index symmetry is *used* there; the primed sign-cancelled identity is below paper granularity (it is a one-line algebraic step). |
|  4 | ChatGPT MCP                      | (server down per brief — fallback to WebSearch #1–#3 + nLab + direct mathlib-source grep)                | n/a  | — | MCP unavailable; compensated with extra WebSearch + decisive mathlib-source grep (Phase 5). The relevant fact ("`s•x=y ⟺ x=s•y` for an involutive unit `s`") is elementary and uniform across sources. |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/`                                | n/a  | (no references dir; both absent) | recorded n/a. The sibling reports note the source paper is arXiv:2604.05280. |
|  6 | nLab                             | "alternating multilinear map" / "sign representation" permutation action up to sign                      | partial | nLab covers alternating/antisymmetric maps and the sign character of `Sₙ` abstractly | The abstract statement is "an antisymmetric function on an n-tuple is `Sₙ`-equivariant for the sign character"; standard, not an atom-level citable lemma. |
|  7 | nCatLab                          | —                                                                                                       | n/a  | —                                | not a distinctively categorical concept. |
|  8 | Stacks Project                   | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (it is `Perm`/`ℤˣ` bookkeeping over a bespoke ring expression). |
|  9 | MathOverflow / Math.SE           | sign-equivariant function of a tuple; cancel sign on the other side; involutive unit scalar              | yes  | folklore: for `s` with `s²=1`, `s•x = y ⟺ x = s•y`; an antisymmetric form satisfies `f(σ·v)=sgn(σ)f(v)` | confirms the underlying identity is textbook/folklore, not a distinguished result. |
| 10 | recent arXiv (last 5 yrs)        | "On Elliptic Sequences over Commutative Rings" Angdinata `rel₄` four-index relation index symmetry        | partial | arXiv:2604.05280 (this Lean development's source) builds `rel₄` and its `Perm`-symmetry | `relFin4_perm'` is an internal one-line rearrangement step, not a theorem of the paper. |

### Literature summary (Phase 3)

Concept identified as: the **sign-equivariance of an antisymmetric four-index expression**, presented in its *sign-cancelled* orientation — i.e. the elementary equivalence `s • (rel₄ permuted) = rel₄ ⟺ rel₄ permuted = s • rel₄` for the involutive unit `s = sgn σ`. The "content" beyond the sibling `relFin4_perm` is a single application of "`s² = 1` ⇒ `s•x=y ⟺ x=s•y`".
Sources agree on the standard form: yes — both the antisymmetry/sign-equivariance principle (`f(σ·v) = sgn σ · f v`) and the involutive-unit cancellation are uniform and elementary across all channels.
Most general standard form: for an alternating/antisymmetric `n`-ary form `f` valued in a module over a ring, `f(v ∘ σ) = (sgn σ) • f v` for all `σ ∈ Sₙ`; equivalently `(sgn σ) • f(v ∘ σ) = f v` (the primed form), the two being interchangeable because `sgn σ` is involutive in `ℤˣ`. mathlib's incarnation is `AlternatingMap.map_perm`.
Generality dimensions where the literature varies:
  - the carrier of the form (here a bespoke `ℤ → R` expression `rel₄`; literature: any alternating multilinear map over a module).
  - arity (here `n = 4`; literature: arbitrary `n`).
  - the orientation of the sign (unprimed `relFin4_perm` vs primed `relFin4_perm'`) — purely cosmetic, the two are one `Int.units_mul_self` apart.
Disagreement with the literature: none. The Lean form is a project-specific, fixed-arity, fixed-orientation specialisation of a folklore principle that the literature never isolates as a standalone lemma — and `relFin4_perm'` specifically is just the *primed orientation* of the already-specialised `relFin4_perm`.

---

### Generality analysis — `EllSequence.relFin4_perm'`

Literature-standard form (from Phase 3): `(sgn σ) • f(v ∘ σ) = f v` for an alternating `n`-ary form `f` (mathlib: `AlternatingMap.map_perm` rearranged via `Int.units_mul_self`).

| # | Parameter / hypothesis        | Current Lean form                         | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened   |
|---|-------------------------------|-------------------------------------------|----------------------------------------|---------------------|------------------------------------|
| 1 | the form is `relFin4 W`       | one fixed bespoke `ℤ → R` expression       | arbitrary alternating `n`-ary form `f` | YES (in principle)  | The proof uses *only* that `relFin4` is sign-equivariant (i.e. `relFin4_perm`); nothing `rel₄`-specific. But the sign-equivariance itself (`relFin4_perm`) is the project-local content, and is not in mathlib — so "generalise the form" means "generalise away from `rel₄` entirely", which is no longer this lemma. |
| 2 | arity = 4 (`Perm (Fin 4)`, `Fin 4 → ℤ`) | fixed 4                          | arbitrary `n`                          | YES (in principle)  | `Int.units_mul_self` is arity-agnostic; the `4` is inherited from `relFin4`. |
| 3 | sign orientation (primed)     | sign cancelled onto permuted side          | either orientation                     | n/a                 | This *is* the only thing the lemma adds over `relFin4_perm`; it is one `Int.units_mul_self` rewrite. |
| 4 | hypothesis `neg` (W odd)      | `∀ k, W (-k) = -W k`                       | n/a (inherited from `relFin4_perm`)    | NO                  | Needed because `relFin4_perm` (which it rewrites by) needs it. Not weakenable without weakening the parent. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD as a *statement about alternating forms* — but the narrowing is inseparable from the project-local object `rel₄`/`relFin4`, which mathlib does not have. Number of *mathematical* weakening opportunities for **this** lemma: 0 that keep it the same lemma. The only "generalisation" would be to register `relFin4` (or `rel₄`) as a genuine `AlternatingMap` and then *delete* `relFin4_perm'` in favour of `AlternatingMap.map_perm` — but `rel₄` is a quadratic alternating-in-its-pairing expression, **not** a multilinear alternating map, so that re-aim does not even type-check (see Phase 5/6). 
Proposed restatement: none that improves *this* lemma — see Phase 4c.
Cost of any restatement: n/a (no profitable restatement of this lemma exists; the profitable move is to inline it, Phase 6).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation                                                                 | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|----------------------------------------------------------------------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | bare ∀-statement; `neg` is a genuine mathematical hypothesis (W is odd), not a preamble. | — |
|  2 | sequences/metric → filters/topology?                                                       | no       | finite algebraic identity; no limits/topology. | — |
|  3 | construct an object where a universal-property class would characterise it?                | no       | no construction. | — |
|  4 | set-with-closure-predicate → bundled substructure?                                         | no       | not a substructure statement. | — |
|  5 | vector-space/field-specific → weaken typeclasses?                                          | no       | already over a general `CommRing R`. | — |
|  6 | 1-categorical → higher-categorical?                                                        | no       | n/a. | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure?                                     | partial  | the index tuple is `Fin 4 → ℤ`; could be `Fin n → α`, but only by abandoning `rel₄` (row 1/2 of Phase 4a) | would require `relFin4` to be a general alternating form, which it is not — see below. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this lemma as-is). The contemporary mathlib idiom for "an antisymmetric `n`-form is sign-equivariant" is `AlternatingMap.map_perm`, but it requires the object to be a bona fide `MultilinearMap`/`AlternatingMap`. `relFin4 W t = rel₄ W (t 0) (t 1) (t 2) (t 3)` is a *degree-2* polynomial in the `addMulSub` building blocks (a sum of three products of two `addMulSub`s), antisymmetric under the `Sₙ` action on the **partition into pairs**, *not* linear in each `t i`. So it is not an `AlternatingMap`, and `map_perm` cannot be used to derive (or replace) `relFin4_perm'`.
- One-line reason this is not a modernisation move: the lemma is a one-`Int.units_mul_self`-rewrite of the project's own `relFin4_perm`; there is no contemporary mathlib formulation that captures it without first importing the whole bespoke `rel₄` development. Modernising the *content* would mean upstreaming `rel₄` itself — out of scope for this single derived lemma, and the natural unit of any such contribution is `relFin4_perm` (the sign-equivariance theorem), with `relFin4_perm'` folded into it.

---

### Diamond / defeq risk — `EllSequence.relFin4_perm'`

n/a — declaration kind is `lemma` (a Prop-valued proof; introduces no definitional equalities, no typeclass-search paths, no coercions). Phase 4.5 skipped.

---

### Mathlib search-status: `EllSequence.relFin4_perm'`

[A] Lean-Finder       (index tool unavailable in env)   n/a: deferred tool not present; compensated by [D]+[E] over local mathlib source + WebSearch over mathlib docs.
[B] Loogle            (index tool unavailable in env)   n/a: type-pattern `Perm.sign ?σ • ?f (?t ∘ ?σ) = ?f ?t` reasoned by hand. The closest *general* mathlib hit by inspection is `AlternatingMap.map_perm` (`f (v ∘ σ) = Equiv.Perm.sign σ • f v`) — but it is about `AlternatingMap`, which `relFin4` is not.
[C] LeanSearch        (index tool unavailable in env)   n/a: NL query "permutation acts on alternating form by its sign, sign cancelled" run via WebSearch #2 against mathlib4 docs → surfaced `AlternatingMap.map_perm`, `MultilinearMap.map_perm`, `Int.units_mul_self`.
[D] Grep mathlib src  `relFin4`, `rel₄`, `addMulSub`, `namespace EllSequence` over `.lake/packages/mathlib/Mathlib/` → **0 hits each** (verified this run). The upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (a `preNormEDS`/`normEDS` ℕ-recursive construction) contains **none** of `rel₄`/`relFin4`/`addMulSub`/`HaveSameParity`/`negOnePow`/`Perm`. Building blocks **present**: `Int.units_mul_self` (used widely, e.g. `Mathlib/GroupTheory/SpecificGroups/Alternating.lean:184`, `Mathlib/LinearAlgebra/Alternating/Basic.lean:867`); `mul_smul`/`one_smul` (core); `AlternatingMap.map_perm` (the generic sign-equivariance, inapplicable to `rel₄`).
[E] Name pattern      grep upstream EDS file + `Mathlib/` for `relFin4_perm`, `relFin4`, `rel₄_perm` → **0 hits**. Confirmed `relFin4_perm'` is duplicated verbatim in the project's General/PID-track sibling `EllipticDivisibilitySequenceOriginal.lean:522` (with its sole consumer at `...Original.lean:555`).

Searched for both:
  - the user's current form (sign-cancelled `rel₄` permutation identity) → not in mathlib.
  - the literature-standard general form (`AlternatingMap.map_perm`) → present in mathlib but **inapplicable**: `relFin4` is not an `AlternatingMap` (it is degree-2 in its arguments), so it neither *is* nor *follows from* `map_perm`.

Concluded: "not in mathlib (source grep + docs search exhausted, plus the literature-standard `AlternatingMap.map_perm` form, which does not apply). Mathlib supplies the **building blocks** for the one-line proof — `Int.units_mul_self`, `mul_smul`, `one_smul` — but the *content* (`relFin4_perm`, the sign-equivariance of `rel₄`) is project-local."

---

### Call sites — `EllSequence.relFin4_perm'`

Internal use count: **K = 1** genuine use (within the project, not counting the declaring line), plus 1 verbatim-duplicate-track copy.
External-to-file callers: within the NagellLutz project only; **0** outside the project.

| Caller file:line                                                    | Usage pattern (one-line excerpt)                                                      |
|---------------------------------------------------------------------|----------------------------------------------------------------------------------------|
| `LutzNagell/EllipticDivisibilitySequence.lean:580`                  | `rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]` — inside `rel₄_of_oddRec_evenRec`, the "sort the index tuple into descending order then strip the sign" step |
| `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:555`          | `rw [← relFin4_perm' neg σ, relFin4]; …` (duplicate General/PID-track copy; the lemma is **also re-defined** there at line 522 — not an independent consumer) |

How it is consumed: in `rel₄_of_oddRec_evenRec`, the tuple `t = ![|a|,|b|,|c|,|d|]` is reordered by a *data-dependent* sorting permutation `σ = Fin.revPerm.trans (Tuple.sort t)`. The caller does `rw [← relFin4_perm' neg σ, …]` to replace `relFin4 W t` by `Perm.sign σ • relFin4 W (t ∘ σ)` (the permuted, now-antitone tuple), after which the antitone-case machinery applies and the `smul`-by-sign is discharged by the surrounding `smul_zero` rewrites. The **primed** orientation is exactly what makes this a single `rw ←`: it lets `relFin4 W t` be rewritten directly into the sign-scaled permuted form. (Using the unprimed `relFin4_perm` here would need an extra sign-cancellation step at the call site — which is precisely the one line `relFin4_perm'` packages.)

Inline-derivation grep: the **immediate sibling** `relFin4_perm` (same file, line 533) is the substantive theorem; `relFin4_perm'` is its one-line `Int.units_mul_self` rearrangement. No other site re-derives the primed identity inline (it is used in exactly the one place it was made for). The General/PID-track duplicate is a verbatim fork, not an independent re-derivation.

Call-sites signal: K = 1 internal use, 0 external, the lemma is a 1-line algebraic twin of `relFin4_perm`, and its single purpose is to save one sign-cancellation `rw` at that one call site → textbook "wrapper that could be inlined / folded into its parent". Leans **NO-composable-from-mathlib**.

---

### Composition check (Phase 6)

Can `EllSequence.relFin4_perm'` be derived in ≤3 chained calls from `relFin4_perm` + mathlib primitives?

Attempt 1 (the proof itself): `by rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]`.
  - Decls used: `relFin4_perm` (project) + `mul_smul`, `Int.units_mul_self`, `one_smul` (all mathlib).
  - Result: **succeeds** — this is literally the lemma's body. Three mathlib rewrites (`mul_smul`, `Int.units_mul_self`, `one_smul`) cancel the doubled sign after one rewrite by the parent `relFin4_perm`.
  - Notes: the *only* mathematical input is `relFin4_perm` (the sign-equivariance of `rel₄`); everything else is the involutive-unit cancellation `sgn σ · sgn σ = 1`, which is one mathlib lemma.

Attempt 2 (term-mode, even tighter): `(mul_smul _ _ _).symm.trans (by rw [Int.units_mul_self, one_smul]) ▸ relFin4_perm neg σ t` — same content, ≤3 mathlib steps over the parent.
  - Result: succeeds.

Conclusion: **COMPOSABLE.**
- Given the sibling `relFin4_perm` (whose own verdict is NO-composable — it inlines `mclosure_swap_castSucc_succ` + `closure_induction`, cf. the `perm.md` / `rel₄_swap` reports), `relFin4_perm'` adds **nothing** but a sign-orientation flip realised by the single mathlib lemma `Int.units_mul_self` (plus `mul_smul`/`one_smul`). At its one call site the primed identity can be produced inline in one extra `rw`, or — cleaner — the call site can rewrite by `relFin4_perm` directly and cancel the sign with `Int.units_mul_self` there. No new mathematical content; mathlib supplies every non-`relFin4_perm` primitive.

---

## Verdict: `EllSequence.relFin4_perm'`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the underlying facts — antisymmetric-form sign-equivariance (`f(σ·v)=sgn σ·f v`) and involutive-unit cancellation (`s²=1 ⇒ s•x=y⟺x=s•y`) — are folklore/textbook and elementary; no source isolates this sign-cancelled rearrangement as a named result. The Lean form is a project-specific, fixed-arity, *primed-orientation* specialisation, strictly downstream of `relFin4_perm`.
- Generality analysis (Phase 4): no profitable generalisation of *this* lemma exists; the generic mathlib idiom `AlternatingMap.map_perm` does **not** apply because `relFin4` is degree-2, not an `AlternatingMap` (Phase 4c). The only "modernisation" would be to upstream the whole `rel₄` development — out of scope for this derived twin.
- Mathlib search (Phase 5): not in mathlib (current or general form). Building blocks present: `Int.units_mul_self` (`Mathlib/GroupTheory/SpecificGroups/Alternating.lean:184` and many others), `mul_smul`, `one_smul`. The substantive content (`relFin4_perm`) is project-local; mathlib's EDS file shares none of this machinery.
- Composition check (Phase 6): COMPOSABLE — the proof *is* a ≤3-mathlib-call rearrangement (`mul_smul` → `Int.units_mul_self` → `one_smul`) of the project's own `relFin4_perm`.

**Rationale:**

`relFin4_perm'` is the one-line, sign-cancelled twin of `relFin4_perm`. Its entire body, `rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]`, rewrites by the sibling sign-equivariance theorem and then cancels the resulting `sgn σ · sgn σ` to `1` using the single mathlib lemma `Int.units_mul_self`, finishing with `one_smul`. That is the textbook shape of NO-composable: the only mathematical input is `relFin4_perm` (itself project-local, and itself a NO-composable inline of `Equiv.Perm.mclosure_swap_castSucc_succ` + `Submonoid.closure_induction`, per the sibling `perm.md` / `rel₄_swap₀₁.md` reports), and everything `relFin4_perm'` adds on top is the involutive-unit cancellation `s² = 1 ⇒ s•x = y ⟺ x = s•y`, which mathlib provides in one lemma. The lemma exists purely as a convenience: at its single call site (`EllipticDivisibilitySequence.lean:580`, inside `rel₄_of_oddRec_evenRec`) it lets `relFin4 W t` be rewritten in one `rw ←` into the sign-scaled, descending-sorted form; without it the caller would do one extra `Int.units_mul_self` step. With K = 1 internal use, zero external consumers, and a verbatim duplicate in the General/PID fork track, it is project glue, not a library-shaped lemma.

The generic mathlib idiom for this kind of statement is `AlternatingMap.map_perm` (`f (v ∘ σ) = sgn σ • f v`, with the primed orientation one `Int.units_mul_self` away). But it is **inapplicable** here: `relFin4 W t = rel₄ W (t 0) (t 1) (t 2) (t 3)` is a degree-2 expression in the `addMulSub` building blocks — antisymmetric under the action on the *pairing*, not multilinear in the four entries — so it is not an `AlternatingMap` and cannot be obtained from, or replaced by, `map_perm`. Hence the content `relFin4_perm` is genuinely project-local; but the *derived* `relFin4_perm'` adds no content of its own. Cost is not a factor (the proof is one line). Mathlib already gives the cancellation step in a single call.

**WHY not (refactor-actionable):**
Mathlib supplies every step `relFin4_perm'` adds over `relFin4_perm`; the lemma is a 1–3-call composition the project should inline or fold into its parent.

Mathlib building blocks:
- `Int.units_mul_self` — `(u : ℤˣ) → u * u = 1`; e.g. `.lake/packages/mathlib/Mathlib/GroupTheory/SpecificGroups/Alternating.lean:184`, `Mathlib/LinearAlgebra/Alternating/Basic.lean:867`. This is the one substantive step.
- `mul_smul`, `one_smul` — core algebra (`Mathlib/Algebra/Group/Action/Defs.lean` and core), the `smul`-collapse and unit-strip.
- (Project-local, *not* mathlib: `EllSequence.relFin4_perm` — the sign-equivariance of `rel₄`. This is the real input and is itself a NO-composable project lemma.)

Composition sketch (≤3 lines; this *is* the body, and the same three mathlib lemmas inline at the one call site):
```lean
-- relFin4_perm' is exactly:
--   (relFin4_perm neg σ t) then cancel the doubled sign:
example (neg : ∀ k, W (-k) = -W k) (σ : Perm (Fin 4)) (t) :
    Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]

-- Inlined at the single call site (EllipticDivisibilitySequence.lean:580), replacing
--   `rw [← relFin4_perm' neg σ, relFin4]`
-- with a rewrite by the parent + the one-lemma sign cancel:
--   rw [show relFin4 W t = Perm.sign σ • relFin4 W (t ∘ σ) from by
--         rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul], relFin4]
```

Call sites in our project (from Phase 6.0): K = 1 real (`EllipticDivisibilitySequence.lean:580`), plus the duplicate-track copy at `...Original.lean:555` (whose own `relFin4_perm'` is at `...Original.lean:522`).
Refactor plan (mathlib-facing answer: **nothing to add**; project options):
- (a) Leave as-is — it is harmless one-line project glue; **do not upstream**. `relFin4_perm'` is *not* a mathlib candidate.
- (b) If trimming: inline the three mathlib lemmas at the one call site (sketch above) and delete `relFin4_perm'`, or fold it into `relFin4_perm` (e.g. state `relFin4_perm` and provide the primed orientation as a `have`/local rewrite at the use site). Either is an AINTLIB `/cleanup` dedup/golf ticket, not a mathlib PR.
- Note: should the *parent* `relFin4_perm` (the genuine sign-equivariance theorem) ever be upstreamed as part of a full `rel₄`/elliptic-net contribution, `relFin4_perm'` would ship — if at all — folded into it as an orientation lemma, never as a standalone declaration.

Next action: delete from the mathlib-candidate list. Keep in the project as private glue (or inline the `Int.units_mul_self` cancellation at the one call site / fold into `relFin4_perm`) via an AINTLIB `/cleanup` ticket. No mathlib PR.

---

## Next step

Do not open a mathlib PR. `EllSequence.relFin4_perm'` is the sign-cancelled one-line twin of the project's own `relFin4_perm`, obtained by a ≤3-call mathlib rearrangement (`mul_smul` → `Int.units_mul_self` → `one_smul`). Its only mathematical input (`relFin4_perm`) is itself project-local, and the generic mathlib idiom `AlternatingMap.map_perm` does not apply (`relFin4`/`rel₄` is degree-2, not an `AlternatingMap`). With K = 1 internal use and a verbatim fork-track duplicate, treat it as private project glue: inline the `Int.units_mul_self` sign-cancellation at the single call site or fold it into `relFin4_perm`. NO-composable-from-mathlib.
