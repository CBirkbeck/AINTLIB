# Comparator certification: [FJP] Theorem 1.3

Kernel-level certification of the paper's headline theorem via
[`leanprover/comparator`](https://github.com/leanprover/comparator).

| file | role |
|---|---|
| `Challenge.lean` | the five statements, each `:= sorry` |
| `Solution.lean` | the same five, forwarded to the library's proofs |
| `comparator-config.json` | `theorem_names` + `permitted_axioms` |
| `../../scripts/certify.sh` | one-time setup instructions + the run |

### Why `Solution.lean` is a separate file and not the library module

Comparator runs `safeLakeBuild solutionModule` — it rebuilds the solution **inside landrun**.
That step is the whole point of the sandbox: it is where an adversarial solution would try to
escape. Pointing `solution_module` at a library module therefore rebuilds the entire project
inside the sandbox (3128 jobs here) and conflates "the untrusted submission" with "the project".
All thirteen upstream tests use two dedicated files.

The two shapes are forced by naming, and it is worth knowing which you are in:

* **two files, neutral names** (this setup, and upstream's): the challenge declares
  `fjp_1_3_*`, the solution declares the same names and forwards to `FiniteJet.finiteJet_*`.
  The sandboxed build is one small file.
* **one file, library names** (`chebotarev-density`'s): the challenge declares the library's own
  names, so a solution file *cannot* redeclare them without clashing with the import that
  provides them — hence `solution_module` must be the library module itself.

## What it buys over `#print axioms`

`#print axioms` tells you which axioms the declaration *named* `X` rests on. It cannot tell you
that `X` says what you think it says. Comparator pins the statement — the type lives in a file
the solution does not get to edit — then re-checks the proof with the Lean kernel and confirms
the axiom set is within `propext`, `Quot.sound`, `Classical.choice`.

## The trust boundary

`Challenge.lean` imports only the **definition layer**: `FJP.FiniteJetRings` (defines `JetA`
and carries its instances, including four global `IsRingOfIntegralElements` instances) and
`Uniform` (defines `IsUniform` / `IsStablyUniform`). Their combined import closure — 101
modules — provably contains **none** of the four modules that prove these statements
(`FiniteJetMain`, `FiniteJetSheafTransfer`, `FiniteJetChart`, `FiniteJetUniformDomain`), so the
statements here are independent restatements rather than echoes of the proofs being judged.

Do not "fix" a mismatch by importing more here. That trades away the only property this file
exists to provide.

## Running it

```sh
./projects/AdicSpaces/scripts/certify.sh     # from the repo root
```

The script documents the one-time setup (clone + build comparator and lean4export; the
`lean4export` artifact lake fetches is a Linux ELF, so build it natively). On Linux install the
real `landrun` for sandboxing; on macOS comparator's own `scripts/fake-landrun.sh` shim is used
— no sandbox, which is acceptable here because the "solution" is this repository's own code
rather than an adversarial submission.

## Status: 3 of 5 certified; 2 blocked by an instability in the library

```
$ ./projects/AdicSpaces/scripts/certify.sh
...
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!        # exit 0
```

**Certified** — statement pinned against `Challenge.lean`, kernel-accepted, axioms within
`propext / Quot.sound / Classical.choice`:

| | |
|---|---|
| `FiniteJet.finiteJet_isUniform` | [FJP] Thm 1.3 (uniform) |
| `FiniteJet.finiteJet_isDomain` | [FJP] Thm 1.3 (domain) |
| `FiniteJet.finiteJet_not_noetherian` | [FJP] Thm 1.3 (nonnoetherian) |

**Not certifiable yet** — `finiteJet_isSheafy` and `finiteJet_not_stablyUniform`. Both route
through the `IsSheafy` / `IsStablyUniform` instance stack, which contains an anonymous
auxiliary. Comparator reports:

```
Challenge and solution theorem statement do not match: 'FiniteJet.finiteJet_isSheafy'
```

That is correct behaviour, and the defect is in the library. Under `pp.explicit` the two types
are byte-identical (6529 chars), same `levelParams`, both `thmInfo`; the difference only shows
under **`pp.proofs true`** (44233 vs 42127 chars):

```
stored   : @NormedDivisionRing.to_normOneClass (LaurentSeries F) (NormedField.to… …)
elaborated: @FiniteJet.JetC._proof_1 F inst
```

`NormOneClass` is a `Prop`-valued class, so these are proof-irrelevant equal but syntactically
distinct, and comparator compares `ConstantVal` structurally — which is exactly what pinning a
statement means.

**The mismatch is not import-driven.** Measured: re-elaborating the identical source text with
the solution module's *own* imports still yields 42188 chars against the stored 44233. Importing
the definition layer, `ExampleLaurentSeries`, `RestrictedLaurent`, `FiniteJetChart` or
`FiniteJetSheafTransfer` all give ~42127–42188 — none reproduces the stored term. So **the
stored type of `finiteJet_isSheafy` cannot be reproduced by re-elaborating its own source.**
No arrangement of the challenge can fix that; adding imports only trades away the trust boundary
without helping.

**Fix (owner call):** give the `NormOneClass (L F)` instance a canonical named form in
`FiniteJetRings`, so `JetC`'s elaboration stops emitting an anonymous `_proof_1` into the type of
everything mentioning `JetA F`. That is a change to a definition, so it belongs in its own
verified batch rather than a cleanup commit.

This fragility is invisible to `#print axioms`, to `lake build`, and to the
`formalisation.yaml` digests, because each of those sees a single environment at a time. It took
comparator to surface it.
