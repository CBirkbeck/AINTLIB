# Comparator certification: the two sheafy-but-not-stably-uniform examples

Kernel-level certification, via
[`leanprover/comparator`](https://github.com/leanprover/comparator), of the two headline
theorems of *Uniform sheafy Tate rings that are not stably uniform* (Birkbeck–Torzewski,
<https://cbirkbeck.github.io/uniform-sheafy-tate-domains/>):

* **[FJP] Theorem 1.1** (`thm:main`; the finite-jet pinching algebra): `𝓐 = JetA F` is a
  complete uniform Tate domain, nonnoetherian, sheafy, and **not stably uniform** — the
  bad chart acquires a nilpotent.
* **[WP] Theorem 8.1** (the weighted-parity algebra): `𝒜 = WPA K id` is a complete uniform
  Tate domain, nonnoetherian, `𝒜° = 𝒜₀`, **strongly sheafy**, and **not stably uniform** —
  with the bad chart an integral domain, so the failure of stable uniformity is *not*
  caused by a nilpotent.

**Numbering crosswalk.** The library's docstrings were written against an earlier revision
of the paper and cite these as `[FJP] Thm 1.3` and `[WP] thm 6.2`; in the current revision
they are Theorem 1.1 and Theorem 8.1. The certificate names below follow the current
numbering (`fjp_1_1_*`, `wp_8_1_*`).

| file | role |
|---|---|
| `Challenge.lean` | [FJP] Thm 1.1: the nine statements, each `:= sorry` |
| `Solution.lean` | the same nine, forwarded to the library's proofs |
| `comparator-config.json` | `theorem_names` + `permitted_axioms` for the above |
| `WPChallenge.lean` | [WP] Thm 8.1: the nine statements, each `:= sorry` |
| `WPSolution.lean` | the same nine, forwarded to the library's proofs |
| `wp-config.json` | `theorem_names` + `permitted_axioms` for the above |
| `../../scripts/certify.sh` | one-time setup instructions + the run |

`certify.sh` reads the challenge and solution module names out of the config, so:

```sh
bash projects/AdicSpaces/scripts/certify.sh                    # [FJP] Theorem 1.1
CONFIG="projects/AdicSpaces/Adic spaces/Comparator/wp-config.json" \
  bash projects/AdicSpaces/scripts/certify.sh                  # [WP] Theorem 8.1
```

## What comparator checks, and what it buys over `#print axioms`

For each name in `theorem_names`, comparator (1) rebuilds the solution module in a sandbox,
(2) checks the solution's statement is **structurally identical** to the challenge's — the
statement is pinned in a file the solution does not get to edit, (3) checks the axiom set is
within `propext / Quot.sound / Classical.choice`, and (4) replays the proof through the Lean
kernel. `#print axioms` alone answers only (3), and only relative to whatever statement the
library happens to declare; it cannot tell you that `X` says what you think it says.

## Toolchain

This branch pins **Lean `v4.33.0` (stable) + mathlib `v4.33.0`** — the first stable release
line carrying the fix for kernel soundness bug
[leanprover/lean4#14576](https://github.com/leanprover/lean4/issues/14576) (unchecked
projections via phantom-parameter nested inductives; fixed in
[#14577](https://github.com/leanprover/lean4/pull/14577), 2026-07-28). The comparator binary
itself builds on the same `v4.33.0` toolchain, so the judging kernel and the judged
development agree.

## The trust boundary

Each challenge imports only the **definition layer**, and its import closure provably
contains none of the modules that prove the statements being judged:

* `Challenge.lean` imports `FJP.Over.TateInstances` + `MvTateAlgebraTopology` +
  `SheafyRing` + `Uniform`. Closure: 117 project modules, containing exactly five `FJP.*`
  modules — `CDVFBase`, `FiniteJetRings`, `RestrictedLaurent`, `Over.JetRings`,
  `Over.TateInstances`, all definition layer. In particular none of `Over.Chart`,
  `Over.UniformDomain`, `Over.StrictLocalization`, `Over.SheafTransfer`,
  `Over.SheafyEndpoints`, `Over.StrongSheafy`, `Over.ExtendedMilnorInstance`,
  `Over.Functoriality`, or any of the Laurent proving chain.
* `WPChallenge.lean` imports `WP.Algebra` + `SheafyRing` + `Uniform`. Closure: 118 project
  modules, containing no `WP.*` beyond `Algebra`, `Weight`, `RestrictedComplete` — in
  particular none of `WP.Main`, `WP.Sheafy`, `WP.UniformDomain`, `WP.Nonnoetherian`,
  `WP.Chart`, or the reducedness chain.

Do not "fix" a mismatch by importing more here. That trades away the only property these
files exist to provide.

Three statement-spelling conventions keep proving-layer names out of the trusted side:

* the paper's weight `w = id` is spelled `fun k => k` in both WP files — the library
  abbreviation `idWeight` lives in the proving module `WP/Main.lean`;
* both certificates' statements sit on the layer-2 base (`[IsDiscreteValuationRing 𝒪[K]]`),
  where the uniformizer is chosen by the solution (`Uniformizer.ofDVR`) rather than carried
  as data;
* `fjp_1_1_stronglySheafy`'s instance telescope is spelled from the base-agnostic
  `MvTateAlgebraTopology` stack — its completeness slot is
  `mvTate_completeSpace … inferInstance`, not the library's one-line wrapper
  `FiniteJetOver.finiteJet_tateExt_completeSpace`, which lives in the proving module
  `Over/StrongSheafy.lean`. The two are definitionally equal, so the solution still closes
  by forwarding.

## Why `Solution.lean` is a separate file and not the library module

Comparator runs `safeLakeBuild solutionModule` — it rebuilds the solution **inside
landrun**. Pointing `solution_module` at a library module would rebuild the entire project
inside the sandbox and conflate "the untrusted submission" with "the project". The
challenge declares neutral names (`fjp_1_1_*`, `wp_8_1_*`); the solution declares the same
names and forwards each to the library's proof.

## Status (2026-08-10, Lean v4.33.0 + mathlib v4.33.0)

```
$ ./projects/AdicSpaces/scripts/certify.sh
...
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!        # exit 0
```

**[FJP] Theorem 1.1 — all nine statements certified** (statement pinned against
`Challenge.lean`, kernel-accepted, axioms within `propext / Quot.sound /
Classical.choice`): `fjp_1_1_isSheafy`, `fjp_1_1_isUniform`, `fjp_1_1_isDomain`,
`fjp_1_1_not_isNoetherianRing`, `fjp_1_1_powerBounded_eq_unitBall`,
`fjp_1_1_stronglySheafy`, `fjp_1_1_not_isStablyUniform` — all over a *general* base (an
arbitrary complete ultrametric nontrivially-normed field whose valuation ring is a DVR),
not over the concrete witness `LaurentSeries F`.

This includes the two statements (`isSheafy`, `not_isStablyUniform`) that were **not**
certifiable in the 2026-08-01 run on `dev/adic-spaces`: there, an anonymous
`NonarchimedeanRing` witness resolved differently between the challenge and solution
environments (the generic instance lived in `FiniteJetFunctoriality.lean`, outside the
challenge's closure). The instance now lives in the definition layer
(`FiniteJetRings.lean`), so every environment containing `JetA` elaborates the headline
statements to structurally identical types.

**[WP] Theorem 8.1 — all nine statements certified** (`wp-config.json`):
`wp_8_1_isUniform`, `wp_8_1_isDomain`, `wp_8_1_not_isNoetherianRing`,
`wp_8_1_powerBounded_eq_unitBall`, `wp_8_1_isSheafyComplete`, `wp_8_1_stronglySheafy`,
`wp_8_1_not_isStablyUniform`.

## Running it

```sh
./projects/AdicSpaces/scripts/certify.sh     # from the repo root
```

The script documents the one-time setup (clone + build comparator and lean4export; the
`lean4export` artifact lake fetches is a Linux ELF, so build it natively). On Linux install
the real `landrun` for sandboxing; on macOS comparator's own `scripts/fake-landrun.sh` shim
is used — no sandbox, which is acceptable here because the "solution" is this repository's
own code rather than an adversarial submission.
