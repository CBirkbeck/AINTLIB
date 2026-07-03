import VersoManual
import VersoBlueprint.PreviewManifest
import DedekindResidueBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithPreviewData
    (%doc DedekindResidueBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
