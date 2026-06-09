import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import AINTLIB.Chapters.Elementary
import AINTLIB.Chapters.Analytic
import AINTLIB.Chapters.Algebraic
import AINTLIB.Chapters.ClassFieldTheory
import AINTLIB.Chapters.PAdicAdic
import AINTLIB.Chapters.ModularForms
import AINTLIB.Chapters.EllipticArithGeom
import AINTLIB.Chapters.FLT
import AINTLIB.Chapters.DiophantineTranscendence
import AINTLIB.Chapters.AdditiveCombinatorial

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "AINTLIB — An Atlas of Number Theory in Lean" =>

This blueprint is an **atlas of formalised number theory in Lean**: it collects the main, Wikipedia-level results of number theory as they exist in Lean today and weaves them into a single cross-project dependency graph spanning the ten principal areas below.

**What it covers.** Three layers, distinguished on each node:

- **mathlib's number-theory core** — live-checked against mathlib, so each result's completion status (sorry-free or in progress) is computed directly from Lean and shown by the node's colour in the dependency graph.
- **External Lean projects** — results formalised in dedicated repositories (Fermat's Last Theorem and regular primes, modular forms and Hecke operators, the Chebotarev density theorem, the prime number theorem, adic spaces, class field theory, the polynomial Freiman–Ruzsa theorem, and more). These appear as informal nodes that link to the project formalising them, marked sorry-free or in progress according to that project's state.
- **Forthcoming in mathlib** — results currently under review as open mathlib pull requests, each linked to its PR, so the atlas shows the moving frontier as well as the settled theory.

**How to read it.** The dependency graph at the foot of this page is the heart of the atlas: each node is a definition, theorem, or lemma, and an edge from $`A` to $`B` means $`A` depends on $`B`. Node colour encodes completion status. Following an edge across a chapter boundary reveals the connections — how cyclotomic field theory feeds Fermat's Last Theorem for regular primes, or how the modular discriminant links modular forms to elliptic curves.

**A few cross-project chains worth tracing.**

- *Regular primes:* mathlib's cyclotomic fields → Kummer's criterion and Bernoulli numbers (flt-regular-bernoulli, KummerCriterion) → Fermat's Last Theorem for regular primes (flt-regular).
- *Modular forms:* mathlib's modular forms and the slash action → the valence formula and strong multiplicity one (LeanModularForms) → the L-series of a modular form (forthcoming in mathlib).
- *Curves over finite fields:* the elliptic-curve group law (mathlib) → the Hasse bound (Hasse-Weil) → the Weil conjectures.
- *Analytic core:* the Riemann zeta and Dirichlet L-functions (mathlib) → non-vanishing on the line $`\mathrm{Re}(s)=1` (DirichletNonvanishing) → the prime number theorem and sieve methods (PNT+).

The ten chapters follow, each pairing every result with a human-readable statement and a paragraph-level proof sketch.

{include 0 AINTLIB.Chapters.Elementary}
{include 0 AINTLIB.Chapters.Analytic}
{include 0 AINTLIB.Chapters.Algebraic}
{include 0 AINTLIB.Chapters.ClassFieldTheory}
{include 0 AINTLIB.Chapters.PAdicAdic}
{include 0 AINTLIB.Chapters.ModularForms}
{include 0 AINTLIB.Chapters.EllipticArithGeom}
{include 0 AINTLIB.Chapters.FLT}
{include 0 AINTLIB.Chapters.DiophantineTranscendence}
{include 0 AINTLIB.Chapters.AdditiveCombinatorial}

{blueprint_graph}
{blueprint_summary}
