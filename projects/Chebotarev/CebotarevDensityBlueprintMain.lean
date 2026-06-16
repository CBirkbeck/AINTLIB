import VersoManual
import VersoBlueprint.PreviewManifest
import CebotarevDensityBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithPreviewData
    (%doc CebotarevDensityBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
