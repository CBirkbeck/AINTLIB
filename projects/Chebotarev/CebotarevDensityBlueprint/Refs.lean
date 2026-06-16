import Verso
import VersoManual
import VersoBlueprint
import VersoManual.Bibliography

open Verso
open Verso.Genre
open Verso.Genre.Manual
open Informal

/-!
# Bibliography entries for the CebotarevDensity blueprint

Each entry is a `Verso.Genre.Manual.Bibliography.Citable` tagged with a
`@[bib "label"]` attribute. Labels are referenced from the chapter prose via
`{Informal.citet <label> ...}[]` / `{Informal.citep <label> ...}[]` and rendered
by the `{blueprint_bibliography}` directive in `Blueprint.lean`.

(Populate from the source blueprint's bibliography as chapters are migrated.)
-/
