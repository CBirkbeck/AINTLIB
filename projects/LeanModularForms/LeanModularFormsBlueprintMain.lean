import VersoManual
import VersoBlueprint.PreviewManifest
import LeanModularFormsBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithPreviewData
    (%doc LeanModularFormsBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
