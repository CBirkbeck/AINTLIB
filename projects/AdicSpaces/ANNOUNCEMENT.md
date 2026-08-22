# Sheafy but not stably uniform — two formalised examples

**Branch:** `announce/sheafy-not-stably-uniform` · **Toolchain:** Lean `v4.33.0` (stable) ·
**mathlib:** release tag `v4.33.0` (`db584cd6d46c`)

This branch is a self-contained, inspectable snapshot of the Lean formalisation of the two
headline theorems of *Uniform sheafy Tate rings that are not stably uniform*
(Birkbeck–Torzewski, <https://cbirkbeck.github.io/uniform-sheafy-tate-domains/>):

1. **Theorem 1.1 — the finite-jet pinching algebra** (cited `[FJP]` in the Lean
   docstrings, as Thm 1.3 of the revision they were written against). `𝓐 = JetA K` is a
   complete uniform Tate domain, nonnoetherian, with `𝓐° = 𝓐₀`, **strongly sheafy**, and
   **not stably uniform** — the bad rational localization `𝓐⟨W/ϖ⟩` acquires a nilpotent.
   * Statements: `Adic spaces/FJP/Over/SheafyEndpoints.lean` and `Over/StrongSheafy.lean`
     (seven endpoints), over an abstract complete ultrametric nonarchimedean field whose
     valuation ring is a DVR — the declarations the paper's own `<lean>` references cite.
   * A parallel development over the concrete witness base `LaurentSeries F` lives in
     `Adic spaces/FJP/` (`FiniteJet.JetA F`, endpoints in `FJP/FiniteJetMain.lean`).
2. **Theorem 8.1 — the weighted-parity algebra** (cited `[WP] thm 6.2` in the Lean
   docstrings). `𝒜 = WPA K id` is a complete uniform Tate domain, nonnoetherian, with
   `𝒜° = 𝒜₀`, **strongly sheafy**, and **not stably uniform** — and here the bad chart is
   an integral domain, so the failure of stable uniformity is *not* caused by a nilpotent.
   * Statements: `Adic spaces/WP/Main.lean` (headline endpoints, two base layers).

All eighteen certified statements (nine per theorem) are kernel-certified; see below.

Two of the nine on each side rule out vacuity rather than adding mathematics.
`IsSheafyComplete` quantifies over `RingOfIntegralElements`, a *subtype*: over an empty
subtype it holds vacuously and says nothing about `(𝓐, 𝓐°)`. So the maximal plus ring is
certified to be a ring of integral elements, for `𝓐` and `𝒜` and separately for the Tate
extensions and shifted-weight algebras the strong-sheafiness statements range over. The
extension case needed `ValuationSpectrum.isRingOfIntegralElements_powerBoundedSubring`, which
proves this for any Huber ring — the older argument took openness from a metric ball, and the
extensions carry a basis-defined topology rather than a norm.

`IsStablyUniform` also changed on 2026-08-22: it now quantifies only over data satisfying
`D.IsRational`. `RationalLocData` is raw data and carries no guarantee that `T ∪ {s}` generates
the unit ideal. Quantifying over all of it made the class stronger than stable uniformity in
the standard sense, and so its negation weaker than the standard failure — the only way this
development uses it. The proofs were unaffected: they always instantiated at the chart datum,
whose rationality `chartDatum_isRational` proves.


## Why this toolchain

Lean `v4.33.0` is the newest **stable** release, and the `v4.33` line carries the fix for
kernel soundness bug [leanprover/lean4#14576](https://github.com/leanprover/lean4/issues/14576)
(axiom-free proof of `False` via unchecked projections on phantom-parameter nested
inductives; reported 2026-07-28, fixed the same day in
[#14577](https://github.com/leanprover/lean4/pull/14577), postmortem 2026-08-01). mathlib is
pinned to its matching release tag `v4.33.0`.

## Kernel-level certification (comparator)

Both headline theorems are certified with
[`leanprover/comparator`](https://github.com/leanprover/comparator): the statements are
pinned in challenge files whose import closure provably contains none of the proving
modules, the axiom budget is `[propext, Quot.sound, Classical.choice]`, and the proofs are
replayed through the Lean kernel. Both runs end `Your solution is okay!`. See
`Adic spaces/Comparator/README.md` for the trust boundary and the full status, and run:

```sh
bash projects/AdicSpaces/scripts/certify.sh                    # Theorem 1.1 (nine statements)
CONFIG="projects/AdicSpaces/Adic spaces/Comparator/wp-config.json" \
  bash projects/AdicSpaces/scripts/certify.sh                  # Theorem 8.1 (nine statements)
```

## Manifests

* `formalisation.yaml` — **generated** inventory (schema 1): every module and declaration,
  plus the informal→formal correspondence for every docstring that cites a source
  (Wedhorn / [FJP] / [WP] / Huber / Stacks), with statement digests.
  Regenerate: `python3 scripts/gen_formalisation.py`; verify:
  `python3 scripts/check_formalisation.py` (currently: no drift).
* `formalization.yaml` — hand-written self-report in the
  [mathlib-initiative v0.3 schema](https://github.com/mathlib-initiative/formalization.yaml):
  sources, scope, per-result axiom status, automation provenance and cost caveats,
  fidelity divergences.

## Provenance

Per the paper's abstract: the two main results (the mathematics) are due to **ChatGPT 5.6
Sol**; the Lean formalisation was carried out by **Claude Code**. This library is part of
AINTLIB, an AI-built and AI-maintained number-theory library; the human owner reviews and
signs off on releases.

## How to build

```sh
lake exe cache get          # mathlib oleans for v4.33.0
lake build "«Adic spaces»"  # the library (root module imports both examples)
```

Build the quoted `«Adic spaces»` target as shown — it is fully green, as are `Common` and
`BernoulliRegular`. A bare `lake build` also builds the sibling projects sharing this
workspace, where a handful of v4.33.0 bump repairs are still pending (off this
announcement's path, owned by the central bump process):
`HasseWeil/Foundation/Curves/Valuation/NormValuation.lean`,
`HasseWeil/Pic0/ToClassSurjective.lean`, and
`LeanModularForms/.../Residue/MultipointPV.lean`.

## Sorry policy on this branch

**Every certified statement — all eighteen — has a `sorry`-free proof closure**; the axiom
set of each is exactly `[propext, Quot.sound, Classical.choice]`, verified by
`#print axioms` and re-checked by comparator. The wider repository tree contains `sorry`s
outside this announcement's scope: the Nonarchimedean Scottish Book *statements* (open
problems), a quarantined conditional reducedness route in `WP/HeadReduced.lean` (part of a
development beyond the paper's current claims), and WIP frontiers of the general Wedhorn
8.28(b) campaign. `formalisation.yaml`'s per-group counts break this down.
