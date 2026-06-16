import VersoManual
import VersoBlueprint.PreviewManifest
import BernoulliRegularBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithPreviewData
    (%doc BernoulliRegularBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
