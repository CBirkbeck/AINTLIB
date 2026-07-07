# Reply integration — 2026-07-07 (T-W7 group-law brief) — ADVERSARIAL AUDIT

Reply received 2026-07-07. Brief: `./brief.md`. Reply: `./reply.md`.
Owner directive for this integration: *"look at it adversarially and see what we actually want. we
need to make sure we will be able to prove what we need. lets not cut corners."* So every reviewer
recommendation was re-derived/attacked before acceptance; verdicts below.

## Interpretation table

| # | Reviewer point | Maps to | Type | Audit verdict |
|---|----------------|---------|------|---------------|
| 1 | Reduce-to-universal strategy sound; density only over the universal integral atlas; existence/canonicity split must stay | Q5 | direct answer | **ACCEPT** (verified: base change of morphism identities needs no flatness/reducedness) |
| 2 | `m_U` by explicit open-cover-and-glue; NOT a single total formula; graph-closure only as fallback | Q1 | direct answer | **ACCEPT + SHARPEN** — the concrete best instantiation is the **Bosma–Lenstra complete system of 2 addition laws** (see A2 below); single-total-formula is not merely "risky" but **impossible** (B–L: every single addition law has nonempty exceptional divisor) |
| 3 | `π_*O_E = O_S`: prove `Γ(ProjModel(W),O) ≅ R` **uniformly for every ring**, universality by instantiation (`W.map`), NOT by proving over `E_U` + base change | Q2 | direct answer, corrects our option (c) | **ACCEPT — VERIFIED** (A3): our "prove over `E_U`, base-change" idea was wrong (equalizers/kernels don't commute with base change without flatness of the cokernel). Uniform 2-chart computation checked feasible; **BB-COHBC fully retired** |
| 4 | Rigidity proof sketch: affine core (`Γ(X×_SY) = Γ(Y)` via universal O-connectedness) + proper closed-image shrinking; corollary via `h = f(x+y)−f(x)−f(y)` | Q3 | direct answer | **PARTIAL REJECT** — sketch is **incomplete over non-reduced bases** (A4): it yields the factorization only on an open `Y' ⊇` the section, and the globalization to all of `A ×_S A` is exactly what fails by the reviewer's own Q6 argument. R3 leaf = SOURCE-REQUIRED; follow-up F1 filed |
| 5 | Do NOT weaken canonicity to reduced/normal bases; dense-open & graph-closure uniqueness fail over nilpotents | Q3(b)/Q6 | direct answer, rejects our escape hatch | **ACCEPT** (the failure mode is real: agree on `X_red`, differ by nilpotents) — but note tension with #4: the reviewer's own sketch has not closed the non-reduced case either |
| 6 | Generic-fibre bridge: state at morphism level on the secant open; warns we may need "field addition as a morphism" | Q4(a) | direct answer + concern | **ACCEPT DIRECTION, SIMPLIFY FURTHER** (A5): evaluate at the **generic point** `η` of `E_U^n` — a single `L`-point that lies in **every** nonempty open (secant loci included), so the comparison is **pointwise over the field `L = κ(η)`**, mathlib's home turf. No field-level addition *morphism* needed (mathlib doesn't have one — verified) |
| 7 | Integrality: "smooth over integral base + geometrically integral fibres ⇒ integral"; specialized fallback fine | Q4(b) | direct answer | **ACCEPT** (leaf kept with both routes; mathlib availability of the general lemma still to check at implementation) |
| 8 | VC-invariance must be upgraded to **global morphism-level equivariance** (incl. infinity/diagonal/anti-diagonal) | Q5 caveat | concern raised | **ACCEPT — new leaf T-W7.0h**; provable by the same generic-point method over the universal VC-base `R_univ ⊗ ℤ[u^±,r,s,t]` (still a domain) |
| 9 | Use a **bundled `WeierstrassAtlas`** structure for construction, not the pointwise `∀s∃U` predicate | Q5 caveat | design advice | **ACCEPT — new leaf T-W7.1a′** (extract bundled atlas from `LocallyWeierstrass` by choice) |
| 10 | Classifying-map non-flatness harmless | Q5 | direct answer | **ACCEPT** (verified: nothing in Part I infers density/reducedness across the base change) |
| 11 | Milestone split T-W7a (existence) / T-W7b (canonicity); canonicity off the critical path to `E[N]`/Drinfeld/`Y(N)` | unprompted | strategy | **ACCEPT** (matches plan; adopt naming) |
| 12 | Ordering: `m_U` → axioms → descend → `Γ=R` → rigidity → canonicity | unprompted | strategy | **ACCEPT WITH ONE CHANGE** (A6): part of the `Γ`-machinery (pole filtration) moves EARLIER — it is needed on the **existence** path via the comparison theorem the reviewer (and our plan) missed |
| — | **(nothing)** on how two Weierstrass presentations of the same `(E,e)` over the same base are related | — | **GAP IN REPLY** | **NEW DEPENDENCY CAUGHT (A1)**: chart-gluing needs the **comparison theorem** (pointed iso of projective Weierstrass models = unique variable change `(u,r,s,t) ∈ R^× × R³`). Without it, "overlaps related by a variableChange" is unproven and overlap agreement would circularly need canonicity |

## Audit details (what was independently re-derived)

### A1 — the comparison theorem is a real, missing existence-path dependency
The general-`S` gluing sets `m_i = φ_i^{-1}∘(m_U)_{bc}∘(φ_i×φ_i)` per chart. Overlap agreement
`m_i = m_j` on `U_i ∩ U_j` ⟺ the transition `ψ_{ij} = φ_j∘φ_i^{-1}` (a **pointed iso of projective
Weierstrass models** over `Γ(U_ij)`) intertwines the transported group laws. If `ψ_{ij}` is induced
by a variable change → T-W7.0h equivariance closes it. That every pointed iso IS a variable change is
the classical comparison theorem (KM 2.2 / Deligne formulaire style) — **not in our repo, not in the
reviewer's reply, and its classical proof uses exactly the `Γ(O(nO))`-freeness machinery**. Elementary
uniform proof route (re-derived, self-contained): a pointed iso preserves `E∖O` (complement of the
section), giving a ring iso `Φ` of the affine coordinate rings; the **pole filtration** `F_n`
(functions extending with pole order ≤ n along the section, defined via the ideal sheaf of `O`, which
is `(s)` on the explicit open `D(u)` of the infinity chart where `t = s³·u`, `u ≡ 1` at `O`) is
intrinsic, so `Φ(F'_n) = F_n`; freeness computations give `F₂ = R ⊕ Rx`, `F₃ = R ⊕ Rx ⊕ Ry` ⟹
`Φ(x') = αx + β`, `Φ(y') = γy + δx + ε` with `α, γ` units; matching the two Weierstrass relations
forces `α³ = γ²`, so `u := γ/α` has `u² = α`, `u³ = γ` — the variable-change data, over **any** ring
(all divisions by units). Determination of the scheme iso by `Φ`: `E∖O` is scheme-dense in the model
(**verified**: on the infinity chart, `s` is a nonzerodivisor — multiplication-by-`s` matrix on the
free `R[t]`-basis `{1,s,s²}` is injective since `t(1+a₃t−a₆t²)` and constant-term-1 polynomials are
nonzerodivisors by McCoy) + separated target.

### A2 — Bosma–Lenstra instantiation of "cover-and-glue" (Q1)
Sources to acquire **before implementing T-W7.0c**: W. Bosma, H. W. Lenstra Jr., *Complete systems of
two addition laws for elliptic curves*, J. Number Theory 53 (1995) 229–240; H. Lange, W. Ruppert,
*Complete systems of addition laws on abelian varieties*, Invent. Math. 79 (1985). B–L give **two
explicit bidegree-(2,2) polynomial addition-law triples** for the **general long Weierstrass cubic**
whose exceptional divisors are disjoint over every field (all characteristics) — so their opens cover
`E ×_S E` over any base (fibrewise-covering = topological covering), each law is division-free in
projective coordinates, overlap agreement is a polynomial identity over `ℤ[a₁..a₆]` modulo the two
curve relations, and the anti-diagonal/diagonal/infinity worries dissolve uniformly. They also prove
no single law is ever total. **Formalization risk flagged**: the identities are large; NO
maxHeartbeats allowed ⇒ discharge by `linear_combination` with **precomputed cofactor multipliers**
(computed outside Lean, verified inside), split into per-coordinate lemmas.

### A3 — uniform `Γ(ProjModel(W), O) ≅ R` feasibility check (Q2)
Two charts suffice (`D₊(Z) ∪ D₊(Y)`; the reviewer said three — the missing locus of `D₊(Z)` is only
`[0:1:0] ∈ D₊(Y)`), so a single-overlap equalizer. All rings involved are **free** `R`-modules with
universal bases: `A = R[x,y]/(W)` free with `{x^i, x^i y}` (mathlib: `Affine.CoordinateRing` freeness
over `R[X]` with basis `{1,y}`); `B = R[t][s]/(monic-in-s cubic)` free with `{s^ε t^k}, ε ≤ 2`;
`A_y` free with the **normal form** `{x^i, x^i y (i≥0)} ∪ {x^ε y^{-m} (ε≤2)} ∪ {x²y^{-1}}` — one
basis element per "pole order", with `x²y^{-1}` (order 1) in **neither** image (that's `H¹`, rank 1 —
consistency check passed). The equalizer-is-`R` computation is finite linear algebra over universal
integer structure constants ⟹ valid over every ring incl. nilpotents. This also **contains** the
`F_n`-filtration computation of A1 — one shared foundation ticket (T-W7.0i) serves both.

### A4 — the rigidity globalization gap (Q3) — REJECTED as-planned-to-leaf
Re-derivation of the reviewer's sketch: affine core ✓ clean and formal-friendly
(`Hom_S(X ×_S Y, Z_aff) ≅ Hom_S(Y, Z_aff)` from `(pr₂)_*O_{X×_SY} = O_Y`, which is
universality-by-instantiation of A3 — this is where "uniform over every ring" earns its keep); local
step ✓ (`F = h^{-1}(Z∖V)` closed, `pr₂` proper ⟹ `pr₂(F)` closed missing the section ⟹ on the open
complement `Y'`, `h` lands in affine `V`, factors). **But**: this yields `h ≡ e` only on
`A ×_S Y'` with `Y' ⊇ e(S)` **open**. Passing to all of `A ×_S A` over a **non-reduced** `S` is
precisely what the reviewer's own Q6 answer says open/dense agreement cannot do. The reply's corollary
derivation silently uses a *global* factorization. Attempted independent closures (translation by
`T`-points; scheme-density of the neighbourhood; Ass-theoretic support arguments) did not close it —
and per source-faithfulness we will NOT invent the step. GIT §6.1's actual statement/mechanism
(connectedness along which factor? noetherian reduction EGA IV §8? an Artinian/infinitesimal
argument?) is **required verbatim**. → Leaf R3 = SOURCE-REQUIRED; follow-up question F1; acquiring
Mumford GIT remains the unblocking item. Existence path unaffected.

### A5 — generic-point simplification of the bridge (Q4a)
`E_U^n` integral ⟹ its generic point `η` gives a **dominant** `Spec κ(η) → E_U^n`
(mathlib: `Scheme.fromSpecResidueField` exists; dominance-of-generic-point to check/prove — tiny).
Two morphisms `E_U^n ⟶ E_U` are equal iff they agree at `η` (`ext_of_isDominant`, target separated,
source reduced). At `η`: values are `L`-points, `L = κ(η)`; `η` lies in **every** nonempty open, so
all secant/regularity conditions hold automatically and each side evaluates by the affine formulas to
mathlib's `Affine.Point.add` over `L`; the group axioms then ARE mathlib's `Point.instAddCommGroup`
axioms over `L`. Needed dictionary leaf: `L`-points of `projModel` over a field = `Affine.Point`
(chart casework; new, tractable). **No morphism-level field addition needed** — removes the
reviewer's flagged intermediate theorem entirely.

### A6 — ordering change
Reviewer's order kept EXCEPT: T-W7.0i (pole filtration + `Γ = R`) is **pulled onto the existence
path** (feeds the comparison theorem T-W7.1b), schedulable in parallel with T-W7.0c from day one.

## Changes applied
- `tw7-plan.md` rewritten (routes, new leaves 0f′/0h/0i/1b, R1–R3 split, milestones T-W7a/T-W7b,
  **parallelization map** added per owner request).
- `tickets.md` T-W7 block updated to match (new sub-tickets, parallel markers, progress note).
- Follow-up for the reviewer: `REVIEW_FOLLOWUP-tw7.md` (3 questions: rigidity globalization verbatim;
  B–L confirmation; comparison-theorem route check).
- `state.md`: Reply received/integrated: true.

## Open items after integration
- **Acquire**: Mumford GIT (rigidity R3 — the only remaining SOURCE-REQUIRED leaf); Bosma–Lenstra
  1995 + Lange–Ruppert 1985 (T-W7.0c implementation gate); optionally Deligne, *Formulaire* (LNM 476)
  as a cross-check for T-W7.1b.
- **Unanswered by reviewer**: nothing explicitly unanswered from Q1–Q6, but F1–F3 (follow-up) arise
  from the audit.

## ROUND-2 REPLY INTAKE (2026-07-07 pm, `reply2.md`) — assessed as a ROUND-1 DIGEST

| # | Point | Verdict |
|---|-------|---------|
| 1 | T-W7a/T-W7b split; 7-step order; only T-W7a on the critical path | already integrated in round 1 — no change |
| 2 | m_U by 5-piece open-cover/glue; global morphism before generic fibre; global VC-equivariance | already integrated; the 5-piece cover is **superseded** by the B–L two-law cover (this reply predates/never saw round 2 — it does not mention B–L) |
| 3 | Γ = R uniformly per ring, not by base change; three-chart Čech | already integrated (we use the 2-chart cover — single overlap); **ADOPT the decl names**: `projModel_globalSections_eq_baseRing` (0i·i3), `locallyWeierstrass_pushforward_O_eq_O` (0i·i5) |
| 4 | Rigidity sketch (closed images + affine factorisation, shrinking) | superseded by the GIT §6.1 verbatim transcription — the reply's sketch still carries the incomplete globalization step audit A4 flagged |
| 5 | **"Urgent Γ₁(N) drift"** — brief allegedly defines Γ₁ via `Σ_a[aP] = E[N]` | **VERIFIED FALSE (stale)**. Code: `Section.orderDivisor` = `[P]+[2P]+⋯+[NP]` (LevelStructure/ExactOrder.lean:97–99, degree N); `HasExactOrder` = `(orderDivisor).IsSubgroup` = KM 1.4.1 (ExactOrder.lean:104–105); `IsGammaOne := HasExactOrder` (LevelStructure/Basic.lean:70). Brief §2.1 + appendix state the degree-N-subgroup-divisor form and explicitly warn "**not** an equality with the degree-N² divisor E[N]" (REVIEW_BRIEF.md:24, :72). `IsFullLevel` (Γ(N)) is the one that equals `E[N]`, correctly. No fix needed; do NOT spawn a worker on this. |
| 6 | Worker allocation order; skip coarse j-line / coherent cohomology | matches our lanes P0–P5 (their #1 removed per row 5); the skip-list was already our stance |
| — | **F1′ / F2 / F3 NOT ADDRESSED** | the round-2 follow-up (`REVIEW_FOLLOWUP-tw7.md`) remains outstanding — re-send it |

## UPDATE (2026-07-07 pm) — acquisitions closed the audit's open items
Owner supplied Mumford GIT (djvu) + Mumford *Abelian Varieties*; agent fetched Bosma–Lenstra (author
copy, Lenstra's Leiden publication archive `1995c`) and Lange–Ruppert (GDZ scan of Invent. 79,
`LOG_0040`). GIT §6.1 + Cor 6.2–6.6 quote-mined verbatim (→ `../../tw7-source-quotes.md`): **A4's
missing globalization mechanism is Artinian-thickenings + Krull intersection + clopen/connected —
confirming the audit's finding that it is NOT a density argument, and resolving R3 by
transcription.** Honest new scoping surfaced by the source: GIT ch. 6 is locally-noetherian
(Krull/coherence genuinely used) ⟹ canonicity lands loc.-noetherian now; arbitrary-`S` = new infra
leaf T-W7.8 (EGA IV §8 spreading-out). Follow-up revised: F1 retired, F1′ (noetherian sufficiency
downstream), F2 (B–L `{Z=0,Y=0}` instantiation), F3 (comparison theorem). All six worker lanes
P0–P5 unblocked.
