# HANDOVER — padic-L-functions formalisation

*Written 2026-06-10, at the close of the §4 work cycle. Read this top to bottom
before touching anything.*

## 1. The mission

Formalise **all** of Rodrigues Jacinto & Williams, *An introduction to p-adic
L-functions* (arXiv:2309.15692) in Lean 4 / Mathlib, **working through the notes
sequentially** (user directive, 2026-06-10). Sections §3 and §4 are done; §5
("Interpolation at Dirichlet characters") is next, then §6, §7, … through §15.

- **Repo**: `github.com/CBirkbeck/padic-L-functions` (**private**), local clone
  `~/Documents/GitHub/padic-L-functions`.
- **Toolchain**: Lean `v4.31.0-rc1`; mathlib pinned in `lake-manifest.json`.
- **Source of truth for the paper**:
  `.mathlib-quality/references/2309.15692-padic-L-functions.tex`. Always cite TeX
  line numbers. §4 was lines 1440–1609; **§5 starts at line 1610**
  (`\section{Interpolation at Dirichlet characters}`).

## 2. Current state (verified 2026-06-10)

- `lake build PadicLFunctions` — **green, ZERO sorries project-wide**.
- `#print axioms` on all headline theorems = `[propext, Classical.choice, Quot.sound]`.
- **§3 complete** (`PadicLFunctions/Measure/`): `PadicMeasure`,
  `mahlerRingEquiv : Λ(ℤ_p) ≃+* ℤ_p⟦T⟧` (RJW Thm 3.20), φ/ψ/σ/Res toolbox, Fubini
  (`integral_swap`), Λ(ℤ_p^×) convolution ring, zero-divisor lemma,
  `augmentationIdeal_eq_span`, pseudo-measures, `exists_topological_generator`.
- **§4 complete** (`PadicLFunctions/KubotaLeopoldt/`): headline
  `PadicMeasure.kubotaLeopoldt` (RJW Thm 4.1 — ∃! pseudo-measure ζ_p with
  ∫x^k·ζ_p = (1−p^{k−1})ζ(1−k)). Supporting cast: `zetaNeg` (rational ζ-values),
  `Fa`/`muA`, `muA_apply_powCM` (Bernoulli moments), `psi_muA` (ψ-invariance,
  ξ-free route), `res_units_muA_apply_powCM`, `zetaNum`,
  `exists_nat_topological_generator`, `padicZeta`, `padicZeta_moments`.
- **Blueprint** (Verso): 14 chapters in `PadicLFunctionsBlueprint/Chapters/`.
  Measures chapter ~20 nodes wired; KubotaLeopoldt **10/11 wired**
  (`kl-values-of-zeta` deliberately unwired — its Mellin half is §2 material; a
  rationale comment sits on the node). Rendered site: `_out/site/html-multi/`
  (open `index.html` locally). Render with `./scripts/ci-pages.sh`.
- **Ticket board**: `.mathlib-quality/tickets.md`. T001–T039 + cleanups all
  **done** except `CLEANUP-FINAL` (open, blocked — needs a lean-lsp-tooled
  session; see §6).
- Last commit at handover: `8a768e4` (T039 milestone) + bookkeeping. Everything
  pushed to `origin main`.

## 3. STANDING RULES (user-mandated, binding — also in `CLAUDE.md`)

These are not suggestions. The user set them explicitly ("make these standing
rules for this project").

1. **Workflow**: plan each paper section with `/develop` (produces decomposition
   + ticket board), execute with `/beastmode`. Planning artifacts live in
   `.mathlib-quality/{plan,decomposition,tickets}.md` and are the source of truth.
2. **Blueprint stays in sync as we go.** When a declaration reaches sorry-free,
   wire the matching chapter node's `(lean := "...")` **in the same session**.
   If a plan restates/renames a declaration, fix the node's prose to stay
   faithful to both source and Lean. Never wire a node to a declaration that
   only partially realises it (leave it unwired with a rationale comment
   instead — see `kl-values-of-zeta` for the pattern). After wiring:
   `lake build PadicLFunctionsBlueprint` must pass; re-render with
   `./scripts/ci-pages.sh` when convenient.
3. **Cleanup immediately after proving.** When a proof ticket reaches
   sorry-free + axiom-clean, run `/cleanup` on the new declarations
   (single-declaration mode) **before marking the ticket done** — never batch
   cleanups. If the session has no lean-lsp MCP tools (true of all sessions so
   far), run the degraded pass (build with linters green + hand-golf obvious
   slack) and record "degraded mode" in the ticket so a tooled session can
   revisit.
4. **Verification bar per ticket**: `lake build` green, zero `sorry` in the new
   declarations, `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
   Record the check in the ticket's Progress notes.
5. **Source-faithfulness**: every planned leaf carries a **verbatim TeX quote**
   in `decomposition.md` (quote-or-delete). Lean-friendlier proof routes are
   allowed only with a recorded replan note in the ticket (see T018, T026, T034
   for the pattern). **p = 2 is excluded wherever the source assumes p odd —
   never silently drop that hypothesis** ((ZMod 8)ˣ is not cyclic; this was
   caught adversarially once already).
6. **Coefficients**: ℤ_p for now. The O_L generalisation is a dedicated pass
   when §5 needs it (see plan.md "Generality Decisions"). Don't widen ad hoc.
7. **Commits**: checkpoint commit after each completed ticket (or tight group);
   pushes to `origin main` are **pre-approved** for this repo. The Lean
   guardrail hook blocks bare `git push` — use
   `LEAN4_GUARDRAILS_BYPASS=1 git push origin main` (user-approved).

## 4. Next work: §5, then sequentially onward

Run `/develop` for §5 (TeX 1610 onward). Read the section in full first
(binding Step 1). Known facts going in:

- §5 is where the **deferred ξ/roots-of-unity machinery comes due**: the
  `Eqphipsi` formula (`(φ∘ψ)F = p⁻¹ Σ_{ξ∈μ_p} F((1+T)ξ−1)`), measures valued in
  extensions (O_L coefficients), and twists by Dirichlet characters. The §3/§4
  deferral notes are in `plan.md` ("Deferred") and `decomposition.md` (§3 tree,
  §4 R3 replan block). T034's ξ-free projection formula (`psi_phi_mul`) may
  cover some of what §5 needs — check before building the full ξ apparatus.
- Rule 6 (ℤ_p coefficients) is expected to break here: §5 likely forces the
  O_L-coefficient generalisation pass. That pass should be **planned as its own
  ticket cluster** (widening `PadicMeasure`, the Mahler transform, etc.), not
  done ad hoc — re-read plan.md "Generality Decisions" first.
- After §5: continue with §6, §7 (locally analytic / §3.7 material was deferred
  to this region), … §15, sequentially per the user's directive.

## 5. Map of the repo

```
PadicLFunctions/                  the Lean library
  Measure/                        §3 (COMPLETE): Basic, MahlerTransform,
                                  Convolution, Toolbox, UnitsZp, Fubini,
                                  PseudoMeasure
  KubotaLeopoldt/                 §4 (COMPLETE): ZetaValues, ZetaValuesComplex,
                                  MuA, ZetaP
PadicLFunctions.lean              library root — ADD NEW MODULE IMPORTS HERE
PadicLFunctionsBlueprint/         Verso blueprint (Chapters/*.lean, one per §)
PadicLFunctionsBlueprintMain.lean site generator entry point
scripts/ci-pages.sh               blueprint build + render (note: applies a
                                  checked-in patch to verso-blueprint v4.30 for
                                  the v4.31 toolchain — idempotent, leave it)
.mathlib-quality/
  plan.md                         mathlib inventory, generality decisions,
                                  deferred table (+ §4 addendum)
  decomposition.md                proof trees w/ verbatim quotes + attack logs
                                  (§3 tree, then §4 tree)
  tickets.md                      the ticket board (T001–T039 + cleanups)
  references/2309.15692-...tex    the paper source
  HANDOVER.md                     this file
.github/workflows/                pages.yml + blueprint-pages.yml exist
                                  (see §6 — Pages not yet live)
CLAUDE.md                         the standing rules (binding)
```

## 6. Open items (do not lose these)

1. **Blueprint remote hosting — RESOLVED 2026-06-10.** User chose to make the
   whole repo **public** (option presented and confirmed via AskUserQuestion;
   trade-offs — public site, public source — were surfaced first). Repo
   visibility flipped to public, Pages enabled with `build_type=workflow`,
   `pages.yml` trigger fixed `development` → `main`. Site:
   **https://cbirkbeck.github.io/padic-L-functions/** — deploys on every push
   to main via `.github/workflows/pages.yml` (cancel-in-progress concurrency,
   so frequent per-ticket pushes just supersede each other). Note: the repo
   redistributes the RJW paper TeX in `.mathlib-quality/references/` — flagged
   to the user at publication time; remove/gitignore if the authors object.
2. **CLEANUP-FINAL** (ticket, open/blocked): full `/cleanup-all` needs a
   lean-lsp-connected session. Queued debt (all cosmetic, build is green):
   `show`-linter warnings (project-wide pattern), flexible-simp at
   `MuA.lean:260`, bundle `psi` as a LinearMap (psi_zero/add/smul/sum are all
   rfl-grade), merge `delQ` into a `CommRing`-general `del`, move
   `mahlerTransform_sub/smul` to Convolution.lean, review placement of
   `instIsDomain` + the `SMulCommClass` instance.
3. **Task #7**: blueprint LaTeX rendering glitch — user reported strings like
   "Dcrys" rendering raw. Client-side KaTeX; never reproduced textually;
   suspect `-verso-data` macro plumbing. Investigate in the rendered site.
4. **Task #8**: mathlib survey areas B (special values / L-functions) and
   C (Iwasawa / cyclotomic) never completed; `.mathlib-quality/mathlib-survey/`
   exists, empty. §5 planning will want survey B.

## 7. Environment gotchas (hard-won — read before debugging)

- **No lean-lsp MCP tools** in any session so far: "verification" of a mathlib
  lemma = grep/Read of `.lake/packages/mathlib/Mathlib/...` at file:line.
  /cleanup runs in degraded mode (rule 3).
- **Guardrail**: bare `git push` is blocked by a hook;
  `LEAN4_GUARDRAILS_BYPASS=1 git push origin main` is the approved form.
- **Axiom checks**: write a temp `AxCheck.lean` importing the module +
  `#print axioms <decl>`, run `lake env lean ./AxCheck.lean`, delete it.
- Frequently-hit Lean/mathlib friction (§3+§4 sessions):
  - `PowerSeries.derivative_subst` takes the ring **A explicitly**:
    `derivative_subst ℚ_[p] hg`.
  - Dot-notation `.derivativeFun` can resolve to `Function.…` under
    `open PowerSeries` — write `PowerSeries.derivativeFun G` explicitly.
  - `(a : PowerSeries R)` natCast vs `C a`: bridge with
    `← map_natCast (PowerSeries.C (R := …)) a`; beware simp re-reversing
    `map_natCast` — rw before simp.
  - MonoidAlgebra/Finsupp and `mahlerTransformₗ`-coe friction: use
    `show … from rfl` bridges and calc blocks; `rw` across type synonyms fails.
  - `rw` with an equation whose pattern occurs on both sides rewrites **all**
    matching occurrences — a trailing re-rewrite then fails with "did not find".
  - ℕ-subtraction: destructure `obtain ⟨k', rfl⟩ : ∃ k', k = k'+1` early
    instead of fighting `k−1` (used in T036/T037/T038).
  - `linear_combination` beats `rw [← hsign]` when associativity blocks the
    pattern; parity `rcases Nat.even_or_odd k` beats fighting `(−1)^k` algebra.
  - Old lemma names that moved: `ZMod.natCast_eq_zero_iff` (not
    `natCast_zmod_eq_zero_iff_dvd`), `Nat.lt_two_pow_self`,
    `ZMod.orderOf_one_add_mul_prime` (namespace `ZMod`),
    `bernoulliPowerSeries_mul_exp_sub_one`, `binomialSeries_nat` (mathlib
    already has 𝓐(δ_n) = (1+T)^n — don't restate).
- The user occasionally kills background agents — **don't launch background
  survey agents unprompted**; do searches inline.
- Date convention in tickets/notes: absolute dates (YYYY-MM-DD).

## 8. How to start

```bash
cd ~/Documents/GitHub/padic-L-functions
lake build PadicLFunctions          # confirm green baseline (B4 check)
```

Then invoke `/develop` for §5 (it will auto-detect resume mode, run its R1
deep-scan against the board, and then plan the new section — give it the §5
TeX line range and the standing-rules note exactly as the §4 cycle did; the §4
ticket texts in tickets.md are the template). After board approval, `/beastmode`
until the section is sorry-free, wiring blueprint nodes and cleaning up
per-ticket as you go. Repeat for §6, §7, …

---

## Addendum 2026-06-11 — §5 complete

The §5 cycle closed in the 2026-06-11 takeover session (this file's §1–§8
describe the §4-era state; tickets.md is the source of truth). Headlines:
**RJW Thm 5.1** (`tame_conductor`), **Thm 5.7** (`zetaEta_twisted_moments` +
`eq_of_twisted_moments_eq`), **Thm 5.17** (`zetaPBranch_interpolation`),
**Thm 5.19** (`Lp_interpolation`, new file `Interpolation/LpFunction.lean`),
**Lem 5.14 as stated** (`PadicExp.lean`, sorry-free incl. exp/log inversion
and the `onePAdicPow`-equivalence — replan L5.3.3 discharged). Project is
sorry-free; axioms standard everywhere; blueprint §5 chapter wired
(Mellin-dependent prose nodes excepted). Open: CLEANUP-FINAL only (blocked
on lean-lsp tooling; scope note in tickets.md). Next per the user's
sequential directive: `/develop` for §6 (board approval is the user's).

## Addendum 2026-06-12 — §6 complete

The §6 cycle (T601–T618 + cleanups) closed 2026-06-12: **RJW Theorem 6.1**
both halves — (i) `ValuesAtOneComplex.LFunction_one_eq` against mathlib's
`DirichletCharacter.LFunction`, (ii) **Leopoldt's theorem**
`MeasureR.LpFunction_one` (D > 1; split-root form). New infrastructure:
extended Iwasawa-branch logarithm (`ExtLog.lean`), formal ψ/digit layer +
integral Eqphipsi (`MeasureR/FormalPsi.lean`), boundary p-adic log
(T618). FOUR B2 statement-defects caught and logged in `b2_log.jsonl`
(general-ring digit decomposition false over fields; seriesEval_phi
hypothesis too weak; HasSum-form of the boundary log false; hnorm
coprime-guard) — the adversarial-briefing pattern works. Project remains
sorry-free, axioms standard, blueprint §6 chapter wired. Open:
CLEANUP-FINAL only (tooling-blocked). Next: `/develop` for §7 (the residue
of ζ_p at s = 1, TeX 2181–2360).
