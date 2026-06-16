import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PadicLFunctionsBlueprint.Chapters.Intro
import PadicLFunctionsBlueprint.Chapters.Motivation
import PadicLFunctionsBlueprint.Chapters.Measures
import PadicLFunctionsBlueprint.Chapters.KubotaLeopoldt
import PadicLFunctionsBlueprint.Chapters.Interpolation
import PadicLFunctionsBlueprint.Chapters.ValuesAtOne
import PadicLFunctionsBlueprint.Chapters.Residue
import PadicLFunctionsBlueprint.Chapters.Eisenstein
import PadicLFunctionsBlueprint.Chapters.ColemanMap
import PadicLFunctionsBlueprint.Chapters.IwasawaZeros
import PadicLFunctionsBlueprint.Chapters.IwasawaProof
import PadicLFunctionsBlueprint.Chapters.MainConjecture
import PadicLFunctionsBlueprint.Chapters.MuInvariant
import PadicLFunctionsBlueprint.Chapters.ModularForms
import PadicLFunctionsBlueprint.Refs
import PadicLFunctions
import PadicLFunctionsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "An introduction to p-adic L-functions — Lean blueprint" =>

This is the mathematical blueprint for a Lean 4 / Mathlib formalisation of
{Informal.citet "RJW"}[], *An introduction to p-adic L-functions*.

The notes build, from the ground up, the cyclotomic Iwasawa theory of the
Riemann zeta function. Starting from $`p`-adic measures and the Iwasawa algebra
$`\Lam \cong \Zp[[T]]`, they construct the *Kubota–Leopoldt $`p`-adic
$`L`-function* $`\zeta_p`, prove that it interpolates the special values
$`\zeta(1-n) = -B_n/n` of the Riemann zeta function against the Teichmüller
character, and then develop the structure theory of $`\Lam`-modules far enough to
state and (for Vandiver primes) prove the *Iwasawa Main Conjecture*. A final
part sketches the analogous picture for modular forms.

*How to read this blueprint.* Each node below is a definition, theorem or
proposition with its mathematical statement and a paragraph-level proof sketch.
The dependency graph records which results feed into which. A node is coloured
*green* once the Lean declaration it references (`lean := …`) is fully proved,
*blue* while it is stated but still contains `sorry`, and left uncoloured while it
is roadmap-only. There is no manual status to maintain: Verso reads it from the
Lean side directly.

*Status.* *Roadmap stage.* The chapters record the intended statements and
proof strategies for the whole paper (§2–§15 of {Informal.citet "RJW"}[]); the
Lean skeletons that the graph points at are being introduced incrementally, after
which the corresponding nodes colour in.

{include 0 PadicLFunctionsBlueprint.Chapters.Intro}

{include 0 PadicLFunctionsBlueprint.Chapters.Motivation}

{include 0 PadicLFunctionsBlueprint.Chapters.Measures}

{include 0 PadicLFunctionsBlueprint.Chapters.KubotaLeopoldt}

{include 0 PadicLFunctionsBlueprint.Chapters.Interpolation}

{include 0 PadicLFunctionsBlueprint.Chapters.ValuesAtOne}

{include 0 PadicLFunctionsBlueprint.Chapters.Residue}

{include 0 PadicLFunctionsBlueprint.Chapters.Eisenstein}

{include 0 PadicLFunctionsBlueprint.Chapters.ColemanMap}

{include 0 PadicLFunctionsBlueprint.Chapters.IwasawaZeros}

{include 0 PadicLFunctionsBlueprint.Chapters.IwasawaProof}

{include 0 PadicLFunctionsBlueprint.Chapters.MainConjecture}

{include 0 PadicLFunctionsBlueprint.Chapters.MuInvariant}

{include 0 PadicLFunctionsBlueprint.Chapters.ModularForms}

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}

# References

{blueprint_bibliography}
