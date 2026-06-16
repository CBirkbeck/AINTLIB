import Verso
import VersoManual
import VersoBlueprint
import VersoManual.Bibliography

open Verso
open Verso.Genre
open Verso.Genre.Manual
open Informal

/-!
# Bibliography entries for the LeanModularForms blueprint

Each entry is a `Verso.Genre.Manual.Bibliography.Citable` tagged with a
`@[bib "label"]` attribute. Labels are referenced from the chapter prose via
`{Informal.citet <label> ...}[]` / `{Informal.citep <label> ...}[]` and rendered
by the `{blueprint_bibliography}` directive in `Blueprint.lean`.
-/

@[bib "HW"]
def hungerbuhlerWasem : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"A residue theorem for closed piecewise C¹ immersions"
  , authors := #[inlines!"Norbert Hungerbühler", inlines!"Micha Wasem"]
  , journal := inlines!"arXiv preprint arXiv:1810.13524"
  , year := 2018
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://arxiv.org/abs/1810.13524"
  }

@[bib "DiamondShurman"]
def diamondShurman : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"A First Course in Modular Forms"
  , authors := #[inlines!"Fred Diamond", inlines!"Jerry Shurman"]
  , journal := inlines!"Graduate Texts in Mathematics 228, Springer-Verlag"
  , year := 2005
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := none
  }
