import Lamping.Environment
import Std

open Lamping

-- Catches a mismatched runtime even when metadata alone compiles.
#guard Lean.versionString == baselineRelease

example : baselineRelease = "4.24.0" := rfl
