import VersoManual
import VersoBlueprint.PreviewManifest
import ExtremeValueProjectBlueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc ExtremeValueProjectBlueprint)
    args
    (extensionImpls := by exact extension_impls%)
