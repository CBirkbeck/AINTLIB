import VersoBlueprint

/-!  Shared KaTeX macro prelude for every blueprint chapter.

All chapters import this module and must NOT declare their own `tex_prelude`:
per-module preludes are snapshotted into a single shared key of
`window.bpTexPreludeTable` at render time, so divergent per-chapter macro sets
silently overwrite each other (raw macros in the rendered site). One identical
shared chunk makes the overwrite harmless.

The LeanModularForms blueprint prose uses only standard KaTeX commands
(`\operatorname`, `\mathbb`, `\mathcal`, `\rho`, `\partial`, `\frac`, `\sqrt`,
`\arcsin`, …), so the only shorthands defined here are a couple of operator
names used in the residue-theorem statements. -/

open Informal

tex_prelude r#"\def\gWN{\operatorname{gWN}}\def\Res{\operatorname{Res}}\def\ord{\operatorname{ord}}\def\PV{\operatorname{PV}}"#
