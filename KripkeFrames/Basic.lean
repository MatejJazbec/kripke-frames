import Mathlib.Tactic



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

def KripkeFrame_is_serial (F : KripkeFrame) : Prop :=
  ∀ w : F.W, ∃ v : F.W, F.R w v

def KripkeFrame_is_dense (F : KripkeFrame) : Prop :=
  ∀ w v : F.W, F.R w v → ∃ u : F.W, F.R w u ∧ F.R u v

def KripkeFrame_is_euclidean (F : KripkeFrame) : Prop :=
  ∀ w v u : F.W, F.R w v → F.R w u → F.R v u

-- Definition of Kripke frames with R having specific property
-- structure ReflexiveTransitiveKripkeFrame extends KripkeFrame :=
--   (refl : ∀ w : W, R w w)                        -- Reflexivity
--   (trans : ∀ w v u : W, R w v → R v u → R w u)   -- Transitivity

-- Definition of Kripke model
structure KripkeModel extends KripkeFrame where
  (V : W → Prop → Prop)  -- Valuation function mapping worlds to truth values of propositions


-- Definition of modalities
def box (F : KripkeModel) (φ : F.W → Prop) (w : F.W) : Prop :=
  ∀ w' : F.W, F.R w w' → φ w'

def diamond (F : KripkeModel) (φ : F.W → Prop) (w : F.W) : Prop :=
  ∃ w' : F.W, F.R w w' ∧ φ w'
