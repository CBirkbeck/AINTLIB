# Comparator certification: the two sheafy-but-not-stably-uniform examples

Kernel-level certification, via
[`leanprover/comparator`](https://github.com/leanprover/comparator), of the two headline
theorems of *Uniform sheafy Tate domains that are not stably uniform* (Birkbeck–Torzewski):

* **[FJP] Theorem 1.3** (= `thm:main` of the current revision): the finite-jet pinching
  algebra `𝓐 = JetA F` is a complete uniform Tate domain, nonnoetherian, sheafy, and **not
  stably uniform** — the bad chart acquires a nilpotent.
* **[WP] Theorem 6.2** (= `thm:rationally-reduced-example`, §6): the weighted-parity
  algebra `𝒜 = WPA K w` at `w = id` is a complete uniform Tate domain, nonnoetherian,
  `𝒜° = 𝒜₀`, **strongly sheafy**, **rationally stably reduced**, and **not stably
  uniform** — so the failure of stable uniformity is *not* caused by a nilpotent: the bad
  chart is reduced (a domain).

| file | role |
|---|---|
| `Challenge.lean` | [FJP] Thm 1.3: the five statements, each `:= sorry` |
| `Solution.lean` | the same five, forwarded to the library's proofs |
| `comparator-config.json` | `theorem_names` + `permitted_axioms` for the above |
| `WPChallenge.lean` | [WP] Thm 6.2: the eight statements, each `:= sorry` |
| `WPSolution.lean` | the same eight, forwarded to the library's proofs |
| `wp-config.json` | `theorem_names` + `permitted_axioms` for the above |
| `../../scripts/certify.sh` | one-time setup instructions + the run |

`certify.sh` reads the challenge and solution module names out of the config, so:

```sh
bash projects/AdicSpaces/scripts/certify.sh                    # [FJP] Theorem 1.3
CONFIG="projects/AdicSpaces/Adic spaces/Comparator/wp-config.json" \
  bash projects/AdicSpaces/scripts/certify.sh                  # [WP] Theorem 6.2
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

* `Challenge.lean` imports `FJP.FiniteJetRings` + `Uniform`. Closure: 107 project modules,
  containing no `FJP.*` beyond `FiniteJetRings` and `RestrictedLaurent` — in particular
  none of `FiniteJetMain`, `FiniteJetSheafyEndpoints`, `FiniteJetSheafTransfer`,
  `FiniteJetChart`, `FiniteJetUniformDomain`, `FiniteJetNoetherianVertices`.
* `WPChallenge.lean` imports `WP.Algebra` + `WP.ChainReducedDef` + `SheafyRing` + `Uniform`.
  Closure: 118 project modules, containing no `WP.*` beyond `Algebra`, `Weight`,
  `RestrictedComplete`, `ChainReducedDef` — in particular none of `WP.Main`, `WP.Sheafy`,
  `WP.UniformDomain`, `WP.Nonnoetherian`, `WP.Chart`, `WP.Reduced`, or the
  `HeadReduced*`/`Graph*` reducedness chain. (`ChainReduced` was split into
  `WP/ChainReducedDef.lean` precisely so the challenge can *state* conclusion (3) without
  importing its proof.)

Do not "fix" a mismatch by importing more here. That trades away the only property these
files exist to provide.

Two statement-spelling conventions keep proving-layer names out of the trusted side:

* the paper's weight `w = id` is spelled `fun k => k` in both WP files — the library
  abbreviation `idWeight` lives in the proving module `WP/Main.lean`;
* the WP statements sit on the layer-2 base (`[IsDiscreteValuationRing 𝒪[K]]`), where the
  uniformizer is chosen by the solution (`Uniformizer.ofDVR`) rather than carried as data.

## Why `Solution.lean` is a separate file and not the library module

Comparator runs `safeLakeBuild solutionModule` — it rebuilds the solution **inside
landrun**. Pointing `solution_module` at a library module would rebuild the entire project
inside the sandbox and conflate "the untrusted submission" with "the project". The
challenge declares neutral names (`fjp_1_3_*`, `wp_6_2_*`); the solution declares the same
names and forwards each to the library's proof.

## Status (2026-08-10, Lean v4.33.0 + mathlib v4.33.0)

```
$ ./projects/AdicSpaces/scripts/certify.sh
...
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!        # exit 0
```

**[FJP] Theorem 1.3 — all five statements certified** (statement pinned against
`Challenge.lean`, kernel-accepted, axioms within `propext / Quot.sound /
Classical.choice`):

| | |
|---|---|
| `fjp_1_3_isSheafy` | [FJP] Thm 1.3 (sheafy) |
| `fjp_1_3_isUniform` | [FJP] Thm 1.3 (uniform) |
| `fjp_1_3_isDomain` | [FJP] Thm 1.3 (domain) |
| `fjp_1_3_not_isNoetherianRing` | [FJP] Thm 1.3 (nonnoetherian) |
| `fjp_1_3_not_isStablyUniform` | [FJP] Thm 1.3 (not stably uniform) |

This includes the two statements (`isSheafy`, `not_isStablyUniform`) that were **not**
certifiable in the 2026-08-01 run on `dev/adic-spaces`: there, an anonymous
`NonarchimedeanRing` witness resolved differently between the challenge and solution
environments (the generic instance lived in `FiniteJetFunctoriality.lean`, outside the
challenge's closure). The instance now lives in the definition layer
(`FiniteJetRings.lean`), so every environment containing `JetA` elaborates the headline
statements to structurally identical types.

**[WP] Theorem 6.2 — seven of eight endpoints certified** (`wp-config.json`):
`isUniform`, `isDomain`, `not_isNoetherianRing`, `powerBounded_eq_unitBall`,
`isSheafyComplete`, `stronglySheafy`, `not_isStablyUniform`.

**Pinned but not yet certifiable** — `wp_6_2_chainReduced` ([WP] 6.2 (3), rationally
stably reduced). Its proof is complete in every example-specific input (all
head-reducedness leaves discharged at maximal ideals) but still consumes the core
development's Wedhorn Prop 8.30 restriction flatness (`prop_8_30_flat_clean`), an open
frontier of the general 8.28(b) campaign, so its axiom set currently includes `sorryAx`.
The statement stays pinned in `WPChallenge.lean`; when 8.30 lands, adding the name back
to `theorem_names` completes the certificate.

## Running it

```sh
./projects/AdicSpaces/scripts/certify.sh     # from the repo root
```

The script documents the one-time setup (clone + build comparator and lean4export; the
`lean4export` artifact lake fetches is a Linux ELF, so build it natively). On Linux install
the real `landrun` for sandboxing; on macOS comparator's own `scripts/fake-landrun.sh` shim
is used — no sandbox, which is acceptable here because the "solution" is this repository's
own code rather than an adversarial submission.
