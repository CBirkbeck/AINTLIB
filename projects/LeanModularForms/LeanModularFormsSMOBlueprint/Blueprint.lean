import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic
import LeanModularForms.SMOObligations.StrongMultiplicityOneFull

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Strong Multiplicity One — Lean blueprint" =>

This is the blueprint for the [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms)
formalisation of _strong multiplicity one_ for cusp forms (Miyake, _Modular Forms_,
Theorems 4.6.8 and 4.6.12): a newform is determined by all but finitely many of its
Hecke eigenvalues. The development is built on an abstract $`\mathrm{GL}_2` Hecke-ring
/ newform theory (`HeckeRing.GL2`), and the headline
$`\texttt{strongMultiplicityOne\_axiom\_clean}` is sorry-free and axiom-clean.

Each node carries a `(lean := …)` reference to the actual declaration in the
`LeanModularForms` library, so Verso reads its completion status directly from Lean.
The dependency graph at the foot of the page records the logical spine.

# Hecke operators and eigenforms

:::definition "hecke-character-space" (lean := "HeckeRing.GL2.modFormCharSpace")
Fix a level $`N` and weight $`k`. The space of cusp forms decomposes under the
diamond operators $`\langle d \rangle` into _character ($`\chi`-isotypic) spaces_:
for a Dirichlet character $`\chi : (\mathbb{Z}/N)^\times \to \mathbb{C}^\times`,
$$`S_k(N, \chi) = \{\, f : \langle d \rangle f = \chi(d)\, f \text{ for all } d \,\},`
on which the Hecke operators $`T_n` (for $`\gcd(n, N) = 1`) act as commuting normal
operators. In `LeanModularForms` this is $`\texttt{modFormCharSpace}`.
:::

:::definition "eigenform" (lean := "HeckeRing.GL2.Eigenform, HeckeRing.GL2.Eigenform.eigenvalue")
An _eigenform_ of level $`N` and weight $`k` is a nonzero cusp form that is a
simultaneous eigenvector for all the Hecke operators $`T_n` with $`\gcd(n, N) = 1`
({uses "hecke-character-space"}[]). Its _eigenvalue_ $`\lambda_n` is defined by
$`T_n f = \lambda_n f`. In `LeanModularForms` this is the structure
$`\texttt{Eigenform}` with $`\texttt{Eigenform.eigenvalue}`.
:::

:::theorem "coeff-eigenvalue" (lean := "HeckeRing.GL2.Eigenform.coeff_eq_coeff_one_mul_eigenvalue")
The Fourier coefficients of an eigenform are recovered from its eigenvalues and its
first coefficient ({uses "eigenform"}[]):
$$`a_n(f) = a_1(f) \, \lambda_n \qquad (\gcd(n, N) = 1).`
In particular, if $`a_1(f) \ne 0` then $`f` is determined by its Hecke eigenvalues
away from $`N`.
:::

:::proof "coeff-eigenvalue"
The $`n`-th Hecke operator acts on $`q`-expansions by $`a_m(T_n f) = \sum_{d \mid (m,n)}
d^{k-1} a_{mn/d^2}(f)`; reading off the first coefficient ($`m = 1`) of
$`T_n f = \lambda_n f` gives $`a_n(f) = \lambda_n\, a_1(f)`, since the only divisor term
surviving at $`m = 1` is $`d = 1`.
:::

# The old/new decomposition

:::definition "cusp-forms-new-old" (lean := "HeckeRing.GL2.cuspFormsOld, HeckeRing.GL2.cuspFormsNew, HeckeRing.GL2.oldPart")
At level $`N`, the cusp forms split into the _old subspace_ $`S_k^{\mathrm{old}}(N)`
($`\texttt{cuspFormsOld}`) — the span of the degeneracy images of forms of proper
divisor level — and the _new subspace_ $`S_k^{\mathrm{new}}(N)`
($`\texttt{cuspFormsNew}`), its orthogonal complement under the Petersson inner
product ({uses "eigenform"}[]). The _old part_ $`\texttt{oldPart}` is the projection
of a cusp form onto $`S_k^{\mathrm{old}}(N)`; a _newform_ is a normalised eigenform
lying in $`S_k^{\mathrm{new}}(N)`.
:::

:::theorem "old-part-vanishing" (lean := "HeckeRing.GL2.oldPart_eq_zero_of_shared_eigenvalues, HeckeRing.GL2.newform_notMem_cuspFormsOldExtended")
If a cusp form shares all (away-from-$`N`) Hecke eigenvalues with a newform, then its
old part vanishes ({uses "cusp-forms-new-old"}[]); dually, a newform never lies in the
extended old subspace. Hence a form whose eigenvalue system equals that of a newform
is forced into the new subspace.
:::

:::proof "old-part-vanishing"
The old subspace is built from level-raises of lower-level forms, whose eigenvalue
systems are exactly those occurring at proper divisor levels. A newform of level $`N`
has, by definition, an eigenvalue system that is _genuinely_ of level $`N` — it does
not occur at any proper divisor (this is $`\texttt{newform\_notMem\_cuspFormsOldExtended}`).
So if a form's eigenvalues match a level-$`N` newform's, none of the old-subspace
generators can contribute, and its old part is zero.
:::

# Strong multiplicity one

:::theorem "strong-multiplicity-one" (lean := "HeckeRing.GL2.strongMultiplicityOne_axiom_clean, HeckeRing.GL2.strongMultiplicityOne_constMul")
_(Strong multiplicity one — Miyake 4.6.8 / 4.6.12.)_ Two newforms whose Hecke
eigenvalues $`\lambda_n` agree for all but finitely many $`n` are scalar multiples of
one another ({uses "eigenform"}[], {uses "cusp-forms-new-old"}[]) — and, once
normalised, equal. In `LeanModularForms` the headline is the _axiom-clean_
$`\texttt{strongMultiplicityOne\_axiom\_clean}`, refining
$`\texttt{strongMultiplicityOne\_constMul}` (Theorem 4.6.12, made unconditional on the
character-space isotypic decomposition).
:::

:::proof "strong-multiplicity-one"
Let $`f, g` be newforms sharing $`\lambda_n` for almost all $`n`. Their difference
$`h = a_1(g)\,f - a_1(f)\,g` has $`a_n(h) = 0` for almost all $`n` by the
coefficient/eigenvalue relation ({uses "coeff-eigenvalue"}[]). A cusp form with almost
all coefficients zero, sharing a newform's eigenvalue system, must have vanishing old
part ({uses "old-part-vanishing"}[]) yet lies in the new subspace
({uses "cusp-forms-new-old"}[]); the only such form is $`0`. Hence
$`a_1(g)\,f = a_1(f)\,g`, so $`f` and $`g` are proportional, and equal after
normalisation.
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}
