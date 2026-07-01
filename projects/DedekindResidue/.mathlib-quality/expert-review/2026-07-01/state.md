# Expert-review state — 2026-07-01

**Status**: reply received + integrated (`reply.md`). Conditional green light — Hecke theta
route confirmed (not Tate, not abelian). Adjustments folded into `plan.md` + `tickets.md`
(+SP1-AC analytic control, +SP1-N normalisation, +T-ADM, +T-BV; AGP Gaussian-first; AGE
sealed unit-domain API; GRH dual-form). **Deep build now GREEN-LIT and started.**

## Scope of this review
- **Audience**: an external number theorist (no repo access).
- **Goal**: strategic guidance + soundness check on the *whole plan* before the deep build.
- **Scope**: the entire project (Belabas–Friedman formalisation), with the general-K ζ_K
  functional-equation substrate as the focus.
- **Brief**: `REVIEW_BRIEF.md` (project root); dated copy `brief.md` beside this file.

## Questions posed (Phase 11 will map the reply onto these)
- **Q1 — decomposition**: does the four-tier plan (substrate → explicit formula → Stark +
  estimates → Thm 1) faithfully mirror BF15's logical structure, or is a dependency mis-placed?
- **Q2 — substrate route (PRIORITY)**: is the Hecke theta stack (P)→(Θ)→(H)→(FE) the
  right/most-efficient route to the general Dedekind FE for a formalisation, and — Hecke's
  classical theta-and-fundamental-domain lines vs. Tate's adelic lines — which is less painful?
- **Q3 — abelian stepping stone**: worth first doing the abelian case (Dirichlet-L reuse +
  ∏W_χ=1 + conductor–discriminant), or a detour that shares little with the general build?
- **Q4 — GRH + gap inventory**: is the GRH formulation (all zeros of Λ_K on Re s = ½) the
  cleanest, and is the substrate-gap inventory (dual lattice; multivariate Gaussian theta;
  Hecke construction; [abelian only] ∏W_χ=1 + conductor–discriminant; explicit formula;
  Stark) correct and complete — or is a prerequisite missing (Hadamard growth estimate,
  convergence of Σ_ρ)?
- **Q5 — hidden pitfalls**: subtleties in BF15's own estimates (Lemmas 2–5, Thm 1) or in the
  substrate (archimedean residue constant; conditional convergence of Σ_ρ F̂(γ_ρ); the
  explicit-formula test-function admissibility class)?

## On reply
Run `/expert-review --reply <path>` (Mode 2, Phases 10–13): map the reply onto Q1–Q5,
surface advice / concerns / new directions, propose ticket changes (esp. to the [SP1] epic
and its AG-P/AG-Θ/AG-E/FE sub-epics in `tickets.md`), get approval, then apply + archive the
reply here.

## Related artifacts
- `.mathlib-quality/plan.md` — architecture, inventory, generality decisions, SP1/SP2/SP3.
- `.mathlib-quality/decomposition.md` — Thm 1 spine (source-faithful) + SP1 route study +
  AG-P grounded decomposition.
- `.mathlib-quality/tickets.md` — ticket board (SP1 epic restructured into the theta stack).
