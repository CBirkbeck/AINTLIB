import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.SMOObligations.StrongMultiplicityOneFull

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Strong Multiplicity One — Lean blueprint" =>

This is the blueprint for the [`LeanModularForms`](https://github.com/CBirkbeck/LeanModularForms)
formalisation of *strong multiplicity one* for cusp forms (Miyake, _Modular Forms_,
Theorems 4.6.8 and 4.6.12), built on the abstract `HeckeRing.GL2` Hecke-ring /
newform theory.

Each node carries a `(lean := …)` reference to the actual declaration in the
`LeanModularForms` library, so Verso reads its completion status directly from
Lean — green once the declaration is fully proved. The dependency graph at the
foot of the page records which results feed into which.

# Eigenforms and the old/new decomposition

:::definition "eigenform" (lean := "HeckeRing.GL2.Eigenform")
An *eigenform* of level $`N` and weight $`k` is a cusp form that is a simultaneous
eigenvector for the Hecke operators $`T_n`. In `LeanModularForms` this is the
structure $`\texttt{HeckeRing.GL2.Eigenform}`; its Hecke eigenvalues are recovered
from its Fourier coefficients by $`a_n(f) = a_1(f)\,\lambda_n` (the
coefficient/eigenvalue relation).
:::

:::definition "cusp-forms-new-old" (lean := "HeckeRing.GL2.cuspFormsNew, HeckeRing.GL2.cuspFormsOld")
For level $`N`, the cusp forms split into the *old subspace*
$`\texttt{cuspFormsOld}` — spanned by level-raises of forms of proper divisor
level — and the *new subspace* $`\texttt{cuspFormsNew}`, its Petersson-orthogonal
complement ({uses "eigenform"}[]). A *newform* is a normalised eigenform in the
new subspace.
:::

# Strong multiplicity one

:::theorem "strong-multiplicity-one" (lean := "HeckeRing.GL2.strongMultiplicityOne_axiom_clean, HeckeRing.GL2.strongMultiplicityOne_constMul")
*(Strong multiplicity one — Miyake 4.6.8 / 4.6.12.)* Two newforms whose Hecke
eigenvalues $`\lambda_n` agree for all but finitely many $`n` are equal (up to a
constant multiple) — a newform is determined by almost all of its eigenvalues
({uses "eigenform"}[], {uses "cusp-forms-new-old"}[]). In `LeanModularForms` the
headline is the *axiom-clean* $`\texttt{strongMultiplicityOne\_axiom\_clean}`,
refining $`\texttt{strongMultiplicityOne\_constMul}` (Theorem 4.6.12, made
unconditional on the character-space isotypic decomposition).
:::

:::proof "strong-multiplicity-one"
If two eigenforms share eigenvalues at almost all $`n`, their difference lies in
the old subspace ({uses "cusp-forms-new-old"}[]) yet is itself new, so it is
forced to vanish: the old part of a form sharing a new form's eigenvalues is zero
($`\texttt{oldPart\_eq\_zero\_of\_shared\_eigenvalues}`), and a newform is not in
the extended old subspace ($`\texttt{newform\_notMem\_cuspFormsOldExtended}`).
Hence the two forms agree up to the constant fixed by the shared first
coefficient.
:::

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}
