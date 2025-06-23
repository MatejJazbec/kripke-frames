import KripkeFrames.Basic

--------------------------------------------------------------------------------------------------------------------
-- Example of frame
inductive World
| w1 | w2 | w3

open World

def example_frame : KripkeFrame :=
{ W := World,
  R := λ w₁ w₂ ↦
    (w₁ = w1 ∧ w₂ = w2) ∨
    (w₁ = w2 ∧ w₂ = w3) ∨
    (w₁ = w3 ∧ w₂ = w1) }

-- #eval KripkeFrame_is_reflexive example_frame -- Should return `false` for the above example
