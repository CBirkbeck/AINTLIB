import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import LeanModularFormsBlueprint.Chapters.Curves
import LeanModularFormsBlueprint.Chapters.Cpv
import LeanModularFormsBlueprint.Chapters.Winding
import LeanModularFormsBlueprint.Chapters.Conditions
import LeanModularFormsBlueprint.Chapters.HW33
import LeanModularFormsBlueprint.Chapters.WindingElliptic
import LeanModularFormsBlueprint.Chapters.Valence
import LeanModularFormsBlueprint.Refs
import LeanModularForms
import LeanModularFormsBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Modular Forms — Hungerbühler–Wasem & Valence Formula in Lean" =>

This is the mathematical blueprint for the Lean 4 / Mathlib formalisation of the
Hungerbühler–Wasem generalised residue theorem (Hungerbühler–Wasem 2018) and its
application to the classical valence formula for modular forms on
$`\operatorname{SL}_2(\mathbb{Z})`, following the textbook proof of
Diamond–Shurman.

The development proceeds in two arcs. The first builds the analytic machinery of
*closed piecewise-$`C^{1}` immersions*, the *multi-point Cauchy principal value*,
and the *generalised winding number*, then states and discharges the
paper-faithful form of the Hungerbühler–Wasem residue theorem under its two
geometric side-conditions (A') and (B). The second computes the generalised
winding numbers at the three elliptic points $`i, \rho, \rho+1` of the
fundamental-domain boundary and feeds them through the residue theorem to obtain
the valence formula $`\operatorname{ord}_\infty(f) + \tfrac12\operatorname{ord}_i(f) + \tfrac13\operatorname{ord}_\rho(f) + \cdots = k/12`.

*How to read this blueprint.* Each node below is a definition or theorem with its
mathematical statement and a paragraph-level proof sketch. The dependency graph
records which results feed into which. A node is coloured *green* once the Lean
declaration it references (`lean := …`) is fully proved, *blue* while it is stated
but still contains `sorry`, and left uncoloured while it is roadmap-only. There is
no manual status to maintain: Verso reads it from the Lean side directly.

{include 0 LeanModularFormsBlueprint.Chapters.Curves}

{include 0 LeanModularFormsBlueprint.Chapters.Cpv}

{include 0 LeanModularFormsBlueprint.Chapters.Winding}

{include 0 LeanModularFormsBlueprint.Chapters.Conditions}

{include 0 LeanModularFormsBlueprint.Chapters.HW33}

{include 0 LeanModularFormsBlueprint.Chapters.WindingElliptic}

{include 0 LeanModularFormsBlueprint.Chapters.Valence}

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}

# References

{blueprint_bibliography}
