# Blueprint chapter authoring guide (read in full)

You are authoring **one chapter** of a Verso blueprint — a Lean 4 *mathematical
roadmap* — for the lecture notes **"An introduction to p-adic L-functions"**
(Rodrigues Jacinto & Williams, arXiv:2309.15692). The source TeX is at
`.mathlib-quality/references/2309.15692-padic-L-functions.tex`.

**Roadmap mode.** No Lean declarations exist yet. You author the *mathematics* of
your section as Verso directive nodes (statements + proof sketches + dependency
edges). **Do NOT emit `(lean := …)` references** — they would point at
declarations that do not exist and we add them later. A node with no `lean :=`
ref simply renders "not started"; the build stays green.

---

## 1. Exact chapter skeleton

Every chapter file is a Lean module of *exactly* this shape:

```lean
import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"<PASTE THE CANONICAL PRELUDE FROM §3, optionally extended>"#

#doc (Manual) "<Your chapter title — PLAIN TEXT, no math>" =>

<prose and directives>
```

- The `#doc (Manual) "…"` **title must be plain text** — inline math `$`…`` inside
  a heading fails to convert. Same for any `#`/`##` section headings inside the
  chapter: plain text only.
- Do **not** add `{blueprint_graph}` / `{blueprint_summary}` / bibliography — those
  live only in the top-level `Blueprint.lean`.

## 2. The five directives

```
:::definition "label"
<mathematical statement, prose + KaTeX>
:::

:::theorem "label"
<statement>.  This rests on {uses "other-label"}[].
:::

:::proof "label"
<paragraph-level MATHEMATICAL sketch>, using {uses "other-label"}[].
:::
```

- `:::lemma`, `:::proposition`, `:::corollary` are theorem-shaped aliases — pick by
  mathematical role.
- A `:::proof "label"` **shares the label** of the theorem it proves and follows it.
- `{uses "label"}[]` adds a **dependency-graph edge** to the node named `label`
  (use it whenever this node genuinely depends on the target). `{bpref "label"}[]`
  is a "see also" link with **no** edge. The empty `[]` lets Verso choose the link
  text; `[custom text]` overrides it.
- **Always close every `:::name "label"` block with a matching `:::`.**

## 3. Canonical KaTeX macro prelude (paste verbatim into `tex_prelude`)

Use exactly this line; append extra `\def`s at the end if your section needs more
(every macro you use in math **must** be defined here or be standard KaTeX, or the
build fails):

```
\def\Z{\mathbb{Z}}\def\Q{\mathbb{Q}}\def\R{\mathbb{R}}\def\C{\mathbb{C}}\def\N{\mathbb{N}}\def\F{\mathbb{F}}\def\Zp{\mathbb{Z}_p}\def\Qp{\mathbb{Q}_p}\def\Cp{\mathbb{C}_p}\def\Fp{\mathbb{F}_p}\def\Zpx{\mathbb{Z}_p^{\times}}\def\Qpx{\mathbb{Q}_p^{\times}}\def\Qbar{\overline{\mathbb{Q}}}\def\Qpbar{\overline{\mathbb{Q}_p}}\def\cO{\mathcal{O}}\def\cC{\mathcal{C}}\def\cH{\mathcal{H}}\def\cG{\mathcal{G}}\def\cN{\mathcal{N}}\def\cM{\mathcal{M}}\def\cD{\mathcal{D}}\def\cA{\mathcal{A}}\def\sX{\mathscr{X}}\def\sY{\mathscr{Y}}\def\sM{\mathscr{M}}\def\sL{\mathscr{L}}\def\sU{\mathscr{U}}\def\sW{\mathscr{W}}\def\sE{\mathscr{E}}\def\Gal{\mathrm{Gal}}\def\Frob{\mathrm{Frob}}\def\Lam{\Lambda}\def\Teich{\omega}\def\ord{\mathrm{ord}}\def\val{\mathrm{val}}\def\res{\operatorname{res}}\def\Res{\operatorname{Res}}\def\Tr{\mathrm{Tr}}\def\Nm{\mathrm{N}}\def\Mahler{\mathfrak{M}}\def\Mellin{\mathrm{Mel}}\def\Exp{\mathrm{Exp}}\def\Col{\mathrm{Col}}\def\Log{\mathrm{Log}}\def\charid{\mathrm{char}}\def\abs#1{\left\lvert#1\right\rvert}\def\norm#1{\left\lVert#1\right\rVert}\def\ang#1{\left\langle#1\right\rangle}\def\set#1{\left\{#1\right\}}\def\floor#1{\left\lfloor#1\right\rfloor}
```

KaTeX math: `` $`…` `` inline, `` $$`…` `` display. Use `$`…`` — **never** bare
`$…$` (that is plain prose, not rendered).

## 4. Quality bar (this is the whole point)

1. **Drop Lean/typeclass plumbing.** State the mathematics, not Lean types. "Let
   `R` be a commutative ring" once, not per-lemma typeclass lists.
2. **Use the paper's own notation** (e.g. `\zeta_p`, `\Lam`, the Iwasawa modules
   `\sX_\infty` etc.). Introduce new notation once and reuse it.
3. **Proof sketches are mathematics, not tactics.** A reader who never opens Lean
   must follow the spine of the argument. "By linearity of the integral and the
   bound $`|e^{ix}|\le 1`" — good. "By `simp`/`omega`" or "see the source" — bad.
   One or two paragraphs per proof; do not transcribe the paper verbatim.
4. **Capture every result.** Every definition, theorem, proposition, lemma, and
   named corollary in your line range becomes a node. Skip only routine remarks.
5. **Bold is single-asterisk `*bold*`** in Verso (not markdown `**bold**`).

## 5. Cross-reference label registry (canonical hub labels)

Use kebab-case labels. For a **local** result, prefix with your chapter's tag
(given in your task, e.g. `meas-…`, `kl-…`). For the **major shared objects**
below, use *exactly* the canonical label in its home chapter, and reference it
from any chapter via `{uses "label"}[]`. Only cross-reference these canonical
labels between chapters (other chapters' local labels are not guaranteed to
exist).

| Home chapter | Canonical label | Object |
|---|---|---|
| Motivation | `riemann-zeta` | the Riemann zeta function |
| Motivation | `special-values-zeta` | $`\zeta(1-n) = -B_n/n`$ |
| Motivation | `kummer-congruences` | Kummer congruences |
| Motivation | `dirichlet-L-function` | Dirichlet L-function $`L(\chi,s)`$ |
| Measures | `p-adic-measure` | a p-adic measure on $`\Zp`$ |
| Measures | `iwasawa-algebra` | the Iwasawa algebra $`\Lam`$ |
| Measures | `mahler-transform` | the Mahler transform |
| Measures | `iwasawa-isomorphism` | $`\Lam \cong \Zp[[T]]`$ |
| Measures | `pseudo-measure` | pseudo-measures |
| Measures | `locally-analytic-distribution` | loc. analytic distributions |
| KubotaLeopoldt | `measure-mu-a` | the measures $`\mu_a`$ |
| KubotaLeopoldt | `kubota-leopoldt` | the Kubota–Leopoldt p-adic L-function $`\zeta_p`$ |
| Interpolation | `teichmuller-character` | the Teichmüller character $`\omega`$ |
| Interpolation | `mellin-transform` | the Mellin transform |
| Interpolation | `interpolation-property` | the interpolation theorem for $`\zeta_p`$ |
| ValuesAtOne | `p-adic-value-s1` | $`\zeta_p`$ near $`s=1`$ |
| Residue | `residue-zeta-p` | residue of $`\zeta_p`$ at $`s=1`$ |
| Eisenstein | `p-adic-eisenstein-family` | the p-adic Eisenstein family |
| ColemanMap | `coleman-theorem` | Coleman's theorem on norm-coherent units |
| ColemanMap | `coleman-map` | the Coleman map |
| ColemanMap | `cyclotomic-units` | cyclotomic units |
| IwasawaZeros | `ideal-of-zeta-p` | the ideal generated by $`\zeta_p`$ |
| IwasawaZeros | `iwasawa-zeros-theorem` | Iwasawa's theorem on the zeros |
| IwasawaProof | `coleman-equivariance` | equivariance of the Coleman map |
| IwasawaProof | `fundamental-exact-sequence` | the fundamental exact sequence |
| MainConjecture | `lambda-module-structure` | structure theory of $`\Lam`-modules |
| MainConjecture | `characteristic-ideal` | the characteristic ideal |
| MainConjecture | `iwasawa-main-conjecture` | the Iwasawa Main Conjecture |
| MuInvariant | `mu-invariant` | Iwasawa's $`\mu`-invariant |
| ModularForms | `gl2-iwasawa` | the GL(2) Iwasawa picture |

## 6. Full chapter list (narrative order)

`Intro` (Overview), then: `Motivation`, `Measures`, `KubotaLeopoldt`,
`Interpolation`, `ValuesAtOne`, `Residue`, `Eisenstein`, `ColemanMap`,
`IwasawaZeros`, `IwasawaProof`, `MainConjecture`, `MuInvariant`, `ModularForms`.

## 7. Model chapter (mimic this shape)

```lean
import Verso
import VersoManual
import VersoBlueprint
import PadicLFunctions
import PadicLFunctionsBlueprint.Refs

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude r#"\def\Zp{\mathbb{Z}_p}\def\Lam{\Lambda}\def\Qp{\mathbb{Q}_p}"#

#doc (Manual) "Measures and the Iwasawa algebra" =>

Throughout, $`p` is a fixed prime. We work with continuous functions on the
$`p`-adic integers $`\Zp` and the measures that integrate them.

:::definition "p-adic-measure"
A *$`p`-adic measure* on $`\Zp` is a continuous $`\Qp`-linear functional
$`\mu : \cC(\Zp,\Qp) \to \Qp` on the space of continuous functions, i.e. a bounded
functional $`f \mapsto \int_{\Zp} f\,d\mu`.
:::

:::definition "iwasawa-algebra"
The *Iwasawa algebra* is the completed group algebra
$`\Lam := \Zp[[\Zp]] = \varprojlim_n \Zp[\Z/p^n]`, identified with the space of
measures on $`\Zp` under convolution.
:::

:::theorem "iwasawa-isomorphism"
The Mahler transform induces a ring isomorphism $`\Lam \cong \Zp[[T]]` between the
Iwasawa algebra and the ring of formal power series, depending on {uses "p-adic-measure"}[]
and {uses "iwasawa-algebra"}[].
:::

:::proof "iwasawa-isomorphism"
A measure $`\mu` is determined by its values $`\int \binom{x}{n} d\mu` on the Mahler
basis of binomial coefficients; assembling these as the coefficients of a power
series in $`T = [1]-1` gives the map, and Mahler's theorem (uniform density of the
binomial polynomials) shows it is a bijection. Compatibility with convolution
upgrades it to a ring isomorphism.
:::
```

## 8. Before you finish

Run `lake env lean <your chapter file>` and fix every error it reports (KaTeX
macro errors point at the `#doc` line; unbalanced `:::` blocks are parse errors).
Ignore the harmless `VersoBlueprint … has local changes` warning. The file must
elaborate cleanly.
