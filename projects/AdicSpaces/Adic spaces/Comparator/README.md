# Comparator certification: [FJP] Theorem 1.3

Kernel-level certification of the paper's headline theorem via
[`leanprover/comparator`](https://github.com/leanprover/comparator).

| file | role |
|---|---|
| `Challenge.lean` | the five statements, each `:= sorry` |
| `comparator-config.json` | `theorem_names` + `permitted_axioms` |
| `../../scripts/certify.sh` | one-time setup instructions + the run |

There is **no `Solution.lean`**: as in this repo's other two comparator setups
(`flt-regular-bernoulli`, `chebotarev-density`), the solution module is an ordinary library
module — here `«Adic spaces».FJP.FiniteJetMain` — and `theorem_names` are the library's own
names. Nothing is restated on the solution side.

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

## Current status: statements do not match (a real defect, not a tooling problem)

The run completes and reports:

```
Challenge and solution theorem statement do not match: 'FiniteJet.finiteJet_isSheafy'
```

Under `pp.explicit` the two types are byte-identical (6529 chars), with the same `levelParams`,
both `thmInfo`. The difference only appears under **`pp.proofs true`** (44233 vs 42127 chars):

```
solution : @NormedDivisionRing.to_normOneClass (LaurentSeries F) (NormedField.to… …)
challenge: @FiniteJet.JetC._proof_1 F inst
```

Definitionally equal, syntactically different. Comparator compares `ConstantVal` structurally,
which is exactly what pinning a statement means, so it is right to reject this.

The cause is in the library: `JetC` is an `abbrev` whose elaboration generates an **anonymous
auxiliary** `FiniteJet.JetC._proof_1`, and that constant is embedded in the *type* of anything
mentioning `JetA F`. Whether the elaborator emits the auxiliary or its expansion depends on the
ambient environment, so the type is not stable across import sets.

That fragility is invisible to `#print axioms`, to `lake build`, and to the
`formalisation.yaml` digests, because each of those sees one environment at a time.

**Preferred fix:** give that proof a real name in `FiniteJetRings` so the term is a stable named
constant. That changes a definition, so it is an owner call and needs its own verified batch —
deliberately not folded into a cleanup commit.
