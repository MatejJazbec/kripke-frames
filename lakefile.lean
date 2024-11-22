import Lake
open Lake DSL

package "kripke-frames" where
  version := v!"0.1.0"
  keywords := #["math"]
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]
require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «KripkeFrames» where
  -- add any library configuration options here
