# Handover — AINTLIB adic-spaces, Campaign 8 (adic Fargues–Fontaine curve)

**Date**: 2026-07-26 · **Branch**: `dev/adic-spaces` (clean, pushed, `3d4c31343`)
**Build**: `lake build '«Adic spaces»'` — green, 3319 jobs · **`sorry` in `FarguesFontaine/`: 0**
**Campaign commits so far**: 171

---

## 1. What the campaign is doing

Formalising Kedlaya, *Noetherian properties of Fargues–Fontaine curves* (arXiv:1410.5160),
in the specialisation `E = ℚ_p`, `ϖ_E = p`, `q = p`, `L = F` a perfectoid field of
characteristic `p`, in order to show the **chart rings of the adic FF curve are strongly
noetherian**, and hence sheafy via the repo's sorry-free
`isSheafy_of_stronglyNoetherian_828b`.

The full source of Kedlaya's paper is in `refs/paper.tex` (fetched from the arXiv e-print;
`refs/` is gitignored — **never commit it**). Section 4 is "Some additional rings"; the two
results the campaign is aiming at are labelled `L:Robba localizations` (the board calls it
"Lemma 4.9") and `T:strongly noetherian Robba2` ("Theorem 4.10").

---

## 2. State of the mathematics

| Kedlaya | Content | Status |
|---|---|---|
| §2 | Witt Euclidean division, `deg` multiplicativity, exact division, `A^r` is a PID | **done** (`Euclidean.lean`) |
| Thm 3.2 | `A^r⟨T₁,…,T_k⟩` noetherian ⇒ `A^r` strongly noetherian | **done** (`Groebner.lean`) |
| Def 4.2 | `B^I` as a closed subring of `hatK ρ₁ × hatK ρ₂`, `λ_I = wI`, `B^{I,+}` | **done** (`IntervalRing.lean`) |
| Lem 4.4 / Cor 4.5 | three circles, `λ_I = sup λ_t` | **done** |
| Cor 4.6 | restriction map `resIHom : B^I → B^{I'}` | map **done**; injectivity **open** (needs continuity of `t ↦ λ_t(x)`) |
| — | `B^I` is a **Tate ring** (pair of definition `(B^{I,+}, (p))`) | **done** |
| Lem 4.9 case 3 | the presentation map `A^r⟨T,T₁,…,T_k⟩ → B^I⟨T₁,…,T_k⟩` | **done** |
| Lem 4.9 case 3 | surjectivity: **density half done**, **strictness half open** | ← **next task** |
| Thm 4.10 | `B^I` strongly noetherian | open (follows from strictness + Thm 3.2) |

---

## 3. The immediate next task — T911 strictness

**Goal**: the presentation map is *strict surjective*, hence its image is closed; with the
density already proven (`BISub_le_topologicalClosure_evalRange`) this gives surjectivity, and
then T912 (`IsStronglyNoetherian ↥(BISub …)`) is a quotient of the noetherian
`A^r⟨T,T₁,…,T_k⟩`.

**The lift is term-by-term, and in our case it loses nothing.** Choose the Tate variable at a
power of the pseudo-uniformizer, `z̄ = ϖʲ` (decision AD-9), so the left endpoint is on the
nose: `ρ₁ = |ϖ|^{jn}`. Then for a Witt term `pᵐ[x̄]`:

* `m ≥ 0` — lift it to itself (`T`-degree 0); its Gauss norm on `A^r` is `w_{ρ₂}(pᵐ[x̄]) ≤ λ_I(x)`;
* `m < 0` — lift it to `[x̄]·[ϖ]^{-jn|m|}·T^{|m|}`; its Gauss norm is
  `|x̄|·ρ₁^{-|m|} = w_{ρ₁}(pᵐ[x̄]) ≤ λ_I(x)`.

The `m < 0` half is already formalised: `exists_evalAr_eq_pInv_pow` shows the monomial
`[ϖ]^{-jni}·Tⁱ` evaluates to the image of `p^{-i}` and has Gauss norm exactly `|ϖ|^{-jni}`.

**A crude lift does not work**: writing `x = a·(p[ϖ])^{-k}` and using a single `T^k` gives a
norm bigger than `λ_I(x)` by `(ρ₂/ρ₁)^k`. Kedlaya's per-term choice of `T`-power is the point.

**Only `Bloc`-elements need lifting** (they are dense), so this needs *no* coordinates on
`B^I` — i.e. **T908(c) is not on the critical path**. For `x ∈ Bloc` write `x = a·(p[ϖ])^{-k}`
with `a ∈ A_inf` and split `a = prefix_k(a) + tail` (the tail is divisible by `pᵏ`); the lift is
then a **polynomial** in `T`, since only the finitely many `n < k` produce negative `p`-powers.
The prefix/tail machinery exists (`prefixAloc`, `wAloc_prefixAloc`, `gaussValueF_sub_prefix`).

**Then closedness** by successive approximation: each round gains a factor `ε`; use
`wI_evalAr_le` for continuity of evaluation and coefficientwise completeness of `A^r` for the
limit.

---

## 4. Binding working rules

1. **No `set_option maxHeartbeats` / `synthInstance.maxHeartbeats`, ever** (owner instruction,
   2026-07-26). Fix the proof instead. See **PERF-1** on the board for the five recurring
   causes in this codebase and their fixes — read it before you write anything:
   * generic `map_add`/`map_sum`/`map_mul` on a hom into a nested subring → state the identity
     explicitly and prove it from the `RingHom` fields, or at the ambient product level and
     transport with `Subtype.ext`;
   * `f ^ n` whose result type is a metavariable → ascribe it;
   * `Subring.comap` in a definition → give the carrier explicitly;
   * anonymous `⟨…, proof⟩` inside goals → name the bundled element;
   * a goal whose *context* is expensive (≈1 s per tactic step) → make the proof a one-step
     term over named lemmas.
   `Groebner.lean` still carries 6 raises on the campaign's biggest proofs; removing them is
   its own decomposition task (tracked in PERF-1), not a blocker for the mathematics.
2. **Producer discipline** (`CLAUDE.md`): prove theorems, reuse rather than re-prove, leave
   `sorry` where unfinished, do not golf/restyle/bump mathlib — that is the `main`-branch fleet's job.
3. **Verify bar for every commit**: `lake build '«Adic spaces»'` green · zero new `sorry` ·
   `#print axioms` of each new declaration ∈ `{propext, Classical.choice, Quot.sound}`.
4. **Push after every green commit** to `origin/dev/adic-spaces` (owner standing authorisation).
5. **Source-faithfulness**: work from `refs/paper.tex`, not from memory or summaries. Every
   ticket on the board carries its source locator.

---

## 5. Workflow that works well here

* Worktree: `/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces` on `dev/adic-spaces`.
* Iterate in a scratch file that imports the built module, e.g.
  `lake env lean /tmp/…/scratch.lean` — 5–30 s per cycle versus ~1–2 min for a file build.
  Port the working block into the project file only once it compiles.
* Then: `lake build '«Adic spaces»'` → `#print axioms` probe → commit → push.
* The board (`.mathlib-quality/tickets.md`) is the source of truth; the `beastmode_active`
  sentinel holds the current FOCUS line.

---

## 6. File map (the part that matters now)

| File | Lines | Contents |
|---|---|---|
| `WittF.lean` | 2058 | `W(F)` Gauss values, decay/closure machinery, two-radius carrier |
| `GaussNorm.lean` | 923 | `gaussTerm`, `gaussValue`, Teichmüller values |
| `ArCompletion.lean` | 1787 | `hatK`, `toHatK`, `Aloc`, `AlocToHatK`, `ArSub` (= `A^r`), coordinates on `A^r` |
| `RobbaLoc.lean` | — | `Bloc`, `wLoc`, the `p`/`[ϖ]` unit lemmas |
| `Euclidean.lean` | 2224 | Kedlaya §2 through `isPrincipalIdealRing_ArSub` |
| `Groebner.lean` | 2230 | Kedlaya §3 through `isStronglyNoetherian_ArSub`; `gaussNormRPS` |
| `IntervalRing.lean` | 1844 | `B^I`, `wI`, `B^{I,+}`, `resIHom`, pair of definition, **Tate ring** |
| `Presentation.lean` | 1739 | `ArToBI`, evaluation `A^r⟨T⟩ →+* B^I`, the `k`-variable map, density half of T911 |

Key API you will reach for immediately (all in `Presentation.lean` unless noted):

```
ArToBI, ArToBI_injective, wI_ArToBI          A^r inside B^I; its interval norm is the ρ₂-value
teichPowOverP, wI_teichPowOverP_le_one       Kedlaya's Tate variable and its power-boundedness
evalArHom, evalArMvHom                       evaluation, 1-variable and k-variable
wI_evalAr_le                                 evaluation is norm-decreasing  ← continuity input
evalAr_monomial, exists_evalAr_eq_pInv_pow   monomial evaluation; the norm-exact lift of p^{-i}
evalRange, BIProd_mem_evalRange              the image contains all of Bloc
BISub_le_topologicalClosure_evalRange        the image is dense in B^I
exists_BI_series_limit          (IntervalRing) ultrametric series converge in B^I
isTateRing_BISub                (IntervalRing) B^I is a Tate ring
isStronglyNoetherian_ArSub      (Groebner)     Kedlaya Theorem 3.2
```

---

## 7. Design decisions in force (full text on the board)

* **AD-3** `A^r` realised as a closure inside the completed field `hatK ρ`.
* **AD-7** `B^I` realised as the closure of the diagonal `Bloc`-image in `hatK ρ₁ × hatK ρ₂` —
  deliberately avoiding a hand-built `SeminormedRing`. This is why the norm is the *function*
  `wI`, not a `Norm` instance, and why mathlib's summability API is not directly available.
* **AD-8** (open) coordinates on all of `B^I` — *not* needed for T911/T912.
* **AD-9** special intervals suffice: the case-3 presentation uses a **radius-1** Tate algebra,
  the reachable left endpoints `τ/(n·m)` are dense, and the Frobenius fundamental domain may be
  split anywhere — so no general-radius Gröbner theory is required.
* **AD-10** the `k`-variable map is assembled from the 1-variable one by **slicing**
  (`sliceElt`, `sliceElt_mul`, `antidiagonal_cons`), not by redoing the analysis.
* **PERF-1** no heartbeat raises (§4 above).

---

## 8. After T911/T912

* **Cor 4.6 injectivity** (T909): the source argument is three circles *with the weight on the
  vanishing point* (`λ_t ≤ λ_{t₀}^c λ_{t''}^{1-c}`), which kills every `t` strictly between
  `t₀` and any other point of `I`; the endpoints then need **continuity of `t ↦ λ_t(x)`** —
  that continuity is the only missing ingredient, and it is a sub-development of its own
  (uniform approximation by `Bloc`-elements).
* **Lane C**: identify the curve's structure presheaf on the two charts with these `B^I`s
  (the consult in `chatgpt-reply-campaign8-adic-space-2026-07-26.md` gives the explicit
  rational subsets `R(T_U/s_U)`, `R(T_V/s_V)` and warns that the plus ring is the *integral
  closure of `A^+[t/s]`*, not the image of `A^+`), then sheafiness via
  `isSheafy_of_stronglyNoetherian_828b`.
* **Lane D**: `𝒳`-descent.
