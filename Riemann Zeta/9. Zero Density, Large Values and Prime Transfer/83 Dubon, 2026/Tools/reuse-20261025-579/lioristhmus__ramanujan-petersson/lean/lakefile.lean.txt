import Lake
open Lake DSL

package "RamanujanPetersson" where

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

@[default_target]
lean_lib RamanujanPetersson where
