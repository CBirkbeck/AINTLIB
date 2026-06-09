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

This blueprint maps the main, Wikipedia-level results of number theory as formalised in Lean across mathlib and related projects.
It provides a single cross-project dependency graph connecting definitions, theorems, and proofs spanning the ten principal areas of number theory covered below.

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
