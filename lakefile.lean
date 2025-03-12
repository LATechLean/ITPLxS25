import Lake
open Lake DSL

package «ITPLxS25» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require autograder from git
  "https://github.com/robertylewis/lean4-autograder-main.git"

@[default_target]
lean_lib «ITPLxS25» where
  -- add any library configuration options here
