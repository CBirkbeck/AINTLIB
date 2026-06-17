# AINTLIB — an AI-reviewed number-theory library

**AINTLIB is a "mathlib for number theory," maintained by AI agents.** It is **one Lake workspace**
with every number-theory project side by side under `projects/<P>/`, all on a **single mathlib that is
bumped to latest daily**. Because it is one build unit, any result can `import` any other — that is the
point. Standards are deliberately relaxed (AI reviewers; `sorry` is allowed as a work-in-progress
marker), and a continuous fleet of Claude agents cleans, generalises, and decomposes results as the
projects grow.

## 🔗 Live blueprints

Each project has a [Verso](https://github.com/leanprover/verso-blueprint) blueprint, published as
subdirectories of one site:

**https://cbirkbeck.github.io/AINTLIB-blueprints/**

- [p-adic L-functions](https://cbirkbeck.github.io/AINTLIB-blueprints/padic/)
- [Modular forms — the valence formula](https://cbirkbeck.github.io/AINTLIB-blueprints/leanmodularforms/)
- [Chebotarev density theorem](https://cbirkbeck.github.io/AINTLIB-blueprints/chebotarev/)
- [Kummer's criterion & regular primes](https://cbirkbeck.github.io/AINTLIB-blueprints/flt-bernoulli/)

(Public site; this source repo is private.)

## Structure

- **`main`** — the integrated library. Always builds. Bumped to latest mathlib daily and centrally.
  `sorry` is allowed here as an explicit work-in-progress marker.
- **`dev/<project>` branches** — each project's frontier, where new theorems are proved.

It is maintained by a **4-account Claude fleet**: a coordinator (writes tickets, bumps mathlib, reviews
generalisations) + universal workers that pull GitHub-issue tickets and run `/cleanup`, `/generalise`,
or `/decompose-proof` per the ticket's lane. The binding rules are in `CLAUDE.md`; the full design is
`docs/superpowers/specs/2026-06-16-aintlib-worker-system-design.md`.

## Projects (`projects/<P>/`)

PadicLFunctions · AdicSpaces · Chebotarev · FltRegularBernoulli · HasseWeil · LeanModularForms ·
NagellLutz · FltRegular · Common.

## Build

```bash
lake exe cache get            # mathlib oleans
lake build PadicLFunctions    # any project's lib; builds are incremental
```

Pinned: Lean **v4.31.0-rc2**, mathlib **@d90090f** (moves with the daily bump).

## Layout

- `projects/<P>/<Lib>/…` — each project's Lean source.
- `projects/<P>/_blueprint/` + `projects/<P>/<Lib>Blueprint/` — that project's Verso blueprint side-build.
- `scripts/render-blueprint-local.sh` — render one project's blueprint locally (disk-safe recipe);
  `scripts/build-blueprints.sh` — assemble the multi-blueprint site for Pages.
- `docs/worker-prompts/` — the worker fleet prompts; `docs/superpowers/specs/` — designs.

Built with [Claude Code](https://claude.com/claude-code).
