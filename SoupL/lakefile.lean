import Lake
open System Lake DSL

package «SoupL» where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.1.0"
require «Gamine» from ".."/"Gamine"

@[default_target]
lean_lib «SoupL»
