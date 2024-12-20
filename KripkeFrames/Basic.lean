-- Definition of Kripke frame
structure KripkeFrame where
  (W : Type)                 -- A type representing the set of possible worlds
  (R : W → W → Prop)         -- A binary relation on worlds (accessibility relation)

def KripkeFrame_is_reflexive (F : KripkeFrame) : Prop :=
  ∀ w : F.W, F.R w w

def KripkeFrame_is_transitive (F : KripkeFrame) : Prop :=
  ∀ w v u : F.W, F.R w v → F.R v u → F.R w u

def KripkeFrame_is_symmetric (F : KripkeFrame) : Prop :=
  ∀ w v : F.W, F.R w v → F.R v w


-- structure ReflexiveTransitiveKripkeFrame extends KripkeFrame :=
--   (refl : ∀ w : W, R w w)                        -- Reflexivity
--   (trans : ∀ w v u : W, R w v → R v u → R w u)   -- Transitivity

structure KripkeModel extends KripkeFrame where
  (V : W → Prop → Prop)  -- Valuation function mapping worlds to truth values of propositions

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

def box (F : KripkeModel) (φ : F.W → Prop) (w : F.W) : Prop :=
  ∀ v : F.W, F.R w v → φ v

def diamond (F : KripkeModel) (φ : F.W → Prop) (w : F.W) : Prop :=
  ∃ v : F.W, F.R w v ∧ φ v
