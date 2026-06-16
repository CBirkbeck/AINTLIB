import VersoBlueprint

/-!  Shared KaTeX macro prelude for every BernoulliRegular blueprint chapter.

All chapters import this module and must NOT declare their own `tex_prelude`:
per-module preludes are snapshotted into a single shared key of
`window.bpTexPreludeTable` at render time, so divergent per-chapter macro sets
silently overwrite each other (raw macros in the rendered site). One identical
shared chunk makes the overwrite harmless.

Extend the macro list HERE (never per chapter) if a chapter needs a new shorthand. -/

open Informal

tex_prelude r#"\def\hminus{h^{-}}\def\hplus{h^{+}}\def\Gal{\operatorname{Gal}}\def\Norm{\operatorname{N}}\def\ord{\operatorname{ord}}\def\Frob{\operatorname{Frob}}\def\Cl{\operatorname{Cl}}\def\Stick{\theta}\def\zetaN{\zeta_N}"#
