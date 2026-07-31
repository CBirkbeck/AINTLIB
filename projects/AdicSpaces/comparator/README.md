# Comparator challenge/solution for the FJP headline theorems

A challenge/solution pair for [`leanprover/comparator`](https://github.com/leanprover/comparator),
the trustworthy judge for Lean proofs.

| file | role |
|---|---|
| `Challenge.lean` | the statements to be proved, each `:= sorry` |
| `Solution.lean` | the same statements, discharged by the library's own theorems |
| `config.json` | `theorem_names` + `permitted_axioms` |

The challenge set is **[FJP] Theorem 1.3** — the paper's headline result, all five conclusions:
`𝓐` is sheafy, uniform, an integral domain, not noetherian, and not stably uniform.

## What this buys over `#print axioms`

`#print axioms` tells you which axioms a declaration *named `X`* rests on. It cannot tell you
that `X` says what you think it says. Comparator pins the statement: it checks that the
theorem in `Solution.lean` proves **the type written in `Challenge.lean`**, that the Lean
kernel accepts the proof, and that it uses no axiom outside
`propext`, `Quot.sound`, `Classical.choice`.

That closes the gap this project's own tooling cannot: a proof could be axiom-clean and still
prove a weaker statement than intended. Here the intended statement lives in a separate file
that the solution does not get to edit.

## Running it

Comparator needs, on `PATH` (or via `COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT`):

* [`landrun`](https://github.com/Zouuup/landrun) built from `main`
* [`lean4export`](https://github.com/leanprover/lean4export/) at a version matching this
  project's toolchain (`leanprover/lean4:v4.33.0-rc1`)
* optionally [`nanoda`](https://github.com/ammkrn/nanoda_lib/) for a second kernel
  (`"enable_nanoda": true`)

```sh
lake exe cache get          # acceptable if you trust the mathlib cache
lake build Challenge        # build the challenge FIRST, before ever compiling Solution
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- bash -c \
  'lake env path/to/comparator config.json'
```

> **Platform:** `landrun` is Linux-only (it uses Landlock), and the sandboxed invocation above
> is `systemd-run`. On macOS the judged run is not available; the repo's
> `scripts/fake-landrun.sh` allows a development run, but it drops the sandbox and therefore
> the guarantee about an adversarial `Solution.lean`.
>
> That caveat does not apply to *this* pair — the solution is our own library, not an
> untrusted submission — but it does mean the certificate must be produced on Linux.

Comparator's guarantee also assumes you have **not** previously compiled `Solution.lean`, so
that a hostile solution cannot have tampered with the challenge's oleans. Build `Challenge`
first, in a clean checkout.

## Why these files are not in the build

`Challenge.lean` is deliberately full of `sorry`, and this project's rule is that no `sorry`
is ever added to the library. The `«Adic spaces»` `lean_lib` declares no `globs`, so only its
root module is a build target and files under `srcDir` are compiled solely when imported —
nothing imports these, so `lake build` never sees them.

If they are given their own `lean_lib` entries (which comparator needs in order to build the
modules by name), those entries **must stay out of `defaultTargets`**, or the gate would start
reporting five new sorries.
