import Verso
import VersoManual
import VersoBlueprint
import VersoManual.Bibliography

open Verso
open Verso.Genre
open Verso.Genre.Manual
open Informal

/-!
# Bibliography entries for the p-adic L-functions blueprint

Each entry is a `Verso.Genre.Manual.Bibliography.Citable` tagged with a
`@[bib "label"]` attribute. Labels are referenced from the chapter prose via
`{Informal.citet <label> ...}[]` / `{Informal.citep <label> ...}[]` and rendered
by the `{blueprint_bibliography}` directive in `Blueprint.lean`.
-/

@[bib "RJW"]
def rodriguesJacintoWilliams : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"An introduction to p-adic L-functions"
  , authors := #[inlines!"Joaquín Rodrigues Jacinto", inlines!"Chris Williams"]
  , journal := inlines!"arXiv preprint arXiv:2309.15692"
  , year := 2023
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://arxiv.org/abs/2309.15692"
  }

@[bib "washington"]
def washington : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Introduction to Cyclotomic Fields, 2nd ed."
  , authors := #[inlines!"Lawrence C. Washington"]
  , journal := inlines!"Graduate Texts in Mathematics 83, Springer-Verlag"
  , year := 1997
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := none
  }

@[bib "coleman"]
def coleman : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Division values in local fields"
  , authors := #[inlines!"Robert F. Coleman"]
  , journal := inlines!"Inventiones Mathematicae"
  , year := 1979
  , month := none
  , volume := inlines!"53"
  , number := inlines!"2"
  , url := none
  }
