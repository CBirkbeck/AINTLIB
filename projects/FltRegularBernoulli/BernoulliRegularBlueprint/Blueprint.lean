import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import BernoulliRegularBlueprint.Chapters.CmSplitting
import BernoulliRegularBlueprint.Chapters.Characters
import BernoulliRegularBlueprint.Chapters.Bernoulli
import BernoulliRegularBlueprint.Chapters.GaussStickelberger
import BernoulliRegularBlueprint.Chapters.LValueNegative
import BernoulliRegularBlueprint.Chapters.HMinusFormula
import BernoulliRegularBlueprint.Chapters.CyclotomicUnits
import BernoulliRegularBlueprint.Chapters.Final
import BernoulliRegularBlueprint.Chapters.IrregularPrimes
import BernoulliRegularBlueprint.Chapters.AbandonedRoute
import BernoulliRegularBlueprint.Chapters.Flt37
import BernoulliRegularBlueprint.Refs
import BernoulliRegular
import BernoulliRegularBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Kummer's Criterion and Regular Primes in Lean" =>

This is the mathematical blueprint for the Lean 4 / Mathlib formalisation around
Kummer's criterion for regular primes, the analytic class number formula for
cyclotomic fields, and their consequences for Fermat's Last Theorem.

The development runs from the CM field and the splitting of its class number into
plus and minus parts, through characters of the cyclotomic Galois group,
generalised Bernoulli numbers, Gauss sums and Stickelberger's theorem, the
evaluation of $`L`-values at non-positive integers, the relative class number
formula for $`\hminus`, cyclotomic units and the plus class number, to the final
proof of Kummer's criterion. It then applies the criterion to obtain Fermat's Last
Theorem for the exponent $`37` and the infinitude of irregular primes.

*How to read this blueprint.* Each node below is a definition or theorem with its
mathematical statement and a paragraph-level proof sketch. The dependency graph
records which results feed into which. A node is coloured *green* once the Lean
declaration it references (`lean := …`) is fully proved, *blue* while it is stated
but still contains `sorry`, and left uncoloured while it is roadmap-only. There is
no manual status to maintain: Verso reads it from the Lean side directly.

{include 0 BernoulliRegularBlueprint.Chapters.CmSplitting}

{include 0 BernoulliRegularBlueprint.Chapters.Characters}

{include 0 BernoulliRegularBlueprint.Chapters.Bernoulli}

{include 0 BernoulliRegularBlueprint.Chapters.GaussStickelberger}

{include 0 BernoulliRegularBlueprint.Chapters.LValueNegative}

{include 0 BernoulliRegularBlueprint.Chapters.HMinusFormula}

{include 0 BernoulliRegularBlueprint.Chapters.CyclotomicUnits}

{include 0 BernoulliRegularBlueprint.Chapters.Final}

{include 0 BernoulliRegularBlueprint.Chapters.IrregularPrimes}

{include 0 BernoulliRegularBlueprint.Chapters.AbandonedRoute}

{include 0 BernoulliRegularBlueprint.Chapters.Flt37}

# Dependency graph

{blueprint_graph}

# Progress summary

{blueprint_summary}

# References

{blueprint_bibliography}
