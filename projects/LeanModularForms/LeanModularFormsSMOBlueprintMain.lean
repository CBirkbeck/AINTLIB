import VersoManual
import VersoBlueprint.PreviewManifest
import LeanModularFormsSMOBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithPreviewData
    (%doc LeanModularFormsSMOBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
