import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import AINTLIB.Chapters.Addition
import AINTLIB.Chapters.Collatz
import AINTLIB.Chapters.Multiplication

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Starter Blueprint" =>

This small Blueprint tracks a few basic arithmetic facts on natural numbers,
then ends with a separate Collatz chapter that is intentionally unfinished. It
is intentionally small, so it can serve as a starting point for a new project.

{include 0 AINTLIB.Chapters.Addition}
{include 0 AINTLIB.Chapters.Multiplication}
{include 0 AINTLIB.Chapters.Collatz}

{blueprint_graph}
{blueprint_summary}
