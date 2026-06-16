import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import CebotarevDensityBlueprint.Chapters.Density
import CebotarevDensityBlueprint.Chapters.Frobenius
import CebotarevDensityBlueprint.Chapters.ZetaProduct
import CebotarevDensityBlueprint.Chapters.Cyclotomic
import CebotarevDensityBlueprint.Chapters.Abelian
import CebotarevDensityBlueprint.Chapters.Main
import CebotarevDensityBlueprint.Refs
import CebotarevDensity
import CebotarevDensityBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The Chebotarev Density Theorem in Lean" =>

This is the mathematical blueprint for the Lean 4 / Mathlib formalisation of the
Chebotarev density theorem.

The development proceeds in six arcs: Dirichlet density of a set of primes; the
decomposition group, inertia, and Frobenius at a prime; the factorisation of the
Dedekind zeta function of an abelian extension into Artin/Dirichlet $`L`-functions;
the cyclotomic case of Chebotarev (via Dirichlet's theorem on primes in arithmetic
progressions); the reduction of the general abelian case to the cyclotomic one; and
finally the full Chebotarev density theorem.

*How to read this blueprint.* Each node below is a definition or theorem with its
mathematical statement and a paragraph-level proof sketch. The dependency graph
records which results feed into which. A node is coloured *green* once the Lean
declaration it references (`lean := …`) is fully proved, *blue* while it is stated
but still contains `sorry`, and left uncoloured while it is roadmap-only. There is
no manual status to maintain: Verso reads it from the Lean side directly.

{include 0 CebotarevDensityBlueprint.Chapters.Density}

{include 0 CebotarevDensityBlueprint.Chapters.Frobenius}

{include 0 CebotarevDensityBlueprint.Chapters.ZetaProduct}

{include 0 CebotarevDensityBlueprint.Chapters.Cyclotomic}

{include 0 CebotarevDensityBlueprint.Chapters.Abelian}

{include 0 CebotarevDensityBlueprint.Chapters.Main}

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}

# References

{blueprint_bibliography}
