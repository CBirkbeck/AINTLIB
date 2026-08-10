# Sheafy but not stably uniform — two formalised examples

**Branch:** `announce/sheafy-not-stably-uniform` · **Toolchain:** Lean `v4.33.0` (stable) ·
**mathlib:** release tag `v4.33.0` (`db584cd6d46c`)

This branch is a self-contained, inspectable snapshot of the Lean formalisation of the two
headline theorems of *Uniform sheafy Tate domains that are not stably uniform*
(Birkbeck–Torzewski):

1. **The finite-jet pinching algebra** (`[FJP]`, the paper's `thm:main`; Theorem 1.3 in the
   revision the Lean docstrings cite). `𝓐 = JetA F` is a complete uniform Tate domain,
   nonnoetherian, **sheafy**, and **not stably uniform** — the bad rational localization
   `𝓐⟨W/ϖ⟩` acquires a nilpotent.
   * Statements: `Adic spaces/FJP/FiniteJetMain.lean` (five endpoints).
   * A generic-base layer (`Adic spaces/FJP/Over/SheafyEndpoints.lean`) states the
     ring-level endpoints over an abstract complete discretely valued nonarchimedean field.

2. **The weighted-parity algebra** (`[WP]`, §6, `thm:rationally-reduced-example` = Theorem
   6.2). `𝒜 = WPA K id` is a complete uniform Tate domain, nonnoetherian, with `𝒜° = 𝒜₀`,
   **strongly sheafy**, **rationally stably reduced**, and **not stably uniform** — so the
   failure of stable uniformity is *not* caused by a nilpotent: every finite iterated
   rational localization of `𝒜` is reduced, and the bad chart is in fact a domain.
   * Statements: `Adic spaces/WP/Main.lean` (headline endpoints, two base layers).
   * Status: seven of the eight endpoints are kernel-certified. The eighth — (3),
     rationally stably reduced — is proved modulo **one** core input: Wedhorn Prop 8.30
     (rational-restriction flatness), an open frontier of the general 8.28(b) campaign;
     every example-specific input, including all head-reducedness leaves at maximal
     ideals, is discharged. Its statement is already pinned in the challenge file.

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
replayed through the Lean kernel. See `Adic spaces/Comparator/README.md` for the trust
boundary and current status, and run:

```sh
bash projects/AdicSpaces/scripts/certify.sh                    # [FJP] Theorem 1.3
CONFIG="projects/AdicSpaces/Adic spaces/Comparator/wp-config.json" \
  bash projects/AdicSpaces/scripts/certify.sh                  # [WP] Theorem 6.2
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

## Sorry policy on this branch

**Every certified statement — all five [FJP] conclusions and seven of the eight [WP]
endpoints — has a `sorry`-free proof closure**; the axiom set of each is exactly
`[propext, Quot.sound, Classical.choice]`, verified by `#print axioms` and re-checked by
comparator. The single exception is [WP] (3) (rationally stably reduced), whose proof is
complete in every example-specific input but still consumes the core campaign's open
Wedhorn Prop 8.30 flatness (`prop_8_30_flat_clean`) — so it is pinned but not yet listed in
the certificate. The wider repository tree contains `sorry`s outside this announcement's
scope: the Nonarchimedean Scottish Book *statements* (open problems), the superseded
conditional legs in `WP/HeadReduced.lean`, and WIP frontiers of the general Wedhorn 8.28(b)
campaign. `formalisation.yaml`'s per-group counts break this down.
