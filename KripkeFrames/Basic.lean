import Mathlib.Tactic
import Mathlib.Order.BooleanAlgebra
import Init.System
import Init.Data.List.Basic
import Init.Prelude


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
structure KripkeModel (Atom : Type) extends KripkeFrame where
  (V : Atom → W → Prop)  -- Valuation function mapping worlds to truth values of propositions
    -- R is a partial order
  -- (R_refl : ∀ w : W, R w w)
  -- (R_trans : ∀ w v u : W, R w v → R v u → R w u)
  -- (R_antisymm : ∀ w v : W, R w v → R v w → w = v)
  --  -- V is monotone with respect to R
  -- (V_monotone : ∀ (p : Atom) (w w' : W), R w w' → V p w → V p w')

-- section Boolean


-- Definition of modalities
def box {Atom} (F : KripkeModel Atom) (φ : F.W → Prop) (w : F.W) : Prop :=
  ∀ w' : F.W, F.R w w' → φ w'

def diamond {Atom} (F : KripkeModel Atom) (φ : F.W → Prop) (w : F.W) : Prop :=
  ∃ w' : F.W, F.R w w' ∧ φ w'

-- Monotonicity of □
theorem box_monotone {Atom} {F : KripkeModel Atom} {p q : F.W → Prop}
    (h : ∀ w, p w → q w) :
    ∀ w, box F p w → box F q w :=
by
  intros w hw u hR
  exact h u (hw u hR)

-- Monotonicity of ◇
theorem diamond_monotone {Atom} {F : KripkeModel Atom} {p q : F.W → Prop}
    (h : ∀ w, p w → q w) :
    ∀ w, diamond F p w → diamond F q w :=
fun _ hdiamond =>
  match hdiamond with
  | ⟨u, hR, hp⟩ => ⟨u, hR, h u hp⟩



variable {F : KripkeFrame}

instance: Bot (F.W → Prop) where
  bot := (fun _ => False)

instance : Top (F.W → Prop) where
  top := fun _ => True

instance: LE (F.W → Prop) where
  le := fun p q => ∀ w, p w → q w


instance : Preorder (F.W → Prop) where
  le_refl := by intro p w h; exact h
  le_trans := by intro p q r hpq hqr w hp; exact hqr w (hpq w hp)


instance : PartialOrder (F.W → Prop) where
  le_antisymm := by
    intros p q hpq hqp
    funext w
    apply propext
    exact ⟨hpq w, hqp w⟩

instance : SemilatticeInf (F.W → Prop) where
  inf := fun p q w => p w ∧ q w
  inf_le_left := by intros p q w h; exact h.1
  inf_le_right := by intros p q w h; exact h.2
  le_inf := by intros p q r hp hr w h; exact ⟨hp w h, hr w h⟩


instance : SemilatticeSup (F.W → Prop) where
  sup := fun p q w => p w ∨ q w
  le_sup_left := by intros p q w h; exact Or.inl h
  le_sup_right := by intros p q w h; exact Or.inr h
  sup_le := by intros p q r hp hq w h
               cases h with
               | inl hp' => exact hp w hp'
               | inr hq' => exact hq w hq'

instance : HasCompl (F.W → Prop) where
  compl := fun p w => ¬ p w

instance : BooleanAlgebra (F.W → Prop) where
  inf := (· ⊓ ·)
  sup := (· ⊔ ·)
  compl := (·ᶜ)
  top := ⊤
  bot := ⊥
  le := (· ≤ ·)
  le_refl := by intro _ _ h; exact h
  le_trans := by intro _ _ _ h₁ h₂ _ hp; exact h₂ _ (h₁ _ hp)
  le_antisymm := by intro p q hpq hqp; funext w; apply propext; exact ⟨hpq w, hqp w⟩
  le_sup_left := by intros _ _ _ h; exact Or.inl h
  le_sup_right := by intros _ _ _ h; exact Or.inr h
  sup_le := by intros _ _ _ h₁ h₂ _ h; cases h with
    | inl h₁' => exact h₁ _ h₁'
    | inr h₂' => exact h₂ _ h₂'
  inf_le_left := by intros _ _ _ h; exact h.1
  inf_le_right := by intros _ _ _ h; exact h.2
  le_inf := by intros _ _ _ h₁ h₂ _ h; exact ⟨h₁ _ h, h₂ _ h⟩
  le_sup_inf := by
    intros x y z w h
    let ⟨hxy, hxz⟩ := h
    by_cases hx : x w
    · exact Or.inl hx
    · exact Or.inr ⟨hxy.resolve_left hx, hxz.resolve_left hx⟩
  inf_compl_le_bot := by
    intro p w h
    exact h.2 h.1
  top_le_sup_compl := by
    intro p w _
    by_cases hp : p w
    · exact Or.inl hp
    · exact Or.inr hp
  le_top := by
    intro p w hp; exact True.intro
  bot_le := by
    intro p w hbot; cases hbot

  himp_eq := by
    intros x y
    funext w
    apply propext
    constructor
    · intro h
      by_cases hx : x w
      · exact Or.inl (h hx)
      · exact Or.inr hx
    · intro h hx
      cases h with
      | inl hy => exact hy
      | inr hnx => contradiction

-- end


-- section Semantics

def UnitFrame : KripkeFrame where
  W := Unit
  R := fun _ _ => True

inductive TwoAtoms : Type
 | p : TwoAtoms
 | q : TwoAtoms

def UnitModel : KripkeModel TwoAtoms where
  W := Unit
  R := fun _ _ => True
  V := fun (A : TwoAtoms) (_ : Unit) =>
        match A with
        | .p => True
        | .q => False
  -- R_refl := by
  --   intro w
  --   trivial
  -- R_trans := by
  --   intros w v u _ _
  --   trivial
  -- R_antisymm := by
  --   intros w v _ _
  --   cases w
  --   cases v
  --   rfl
  -- V_monotone := by
  --   intros p w w' _ h
  --   exact h

inductive Formula (Atom : Type) where
| true : Formula Atom
| atom : Atom → Formula Atom
| and : Formula Atom → Formula Atom → Formula Atom
| imp : Formula Atom → Formula Atom → Formula Atom
| box : Formula Atom → Formula Atom
| bot   : Formula Atom   -- ⊥

@[reducible, simp]
def KripkeModel.valid {Atom} (M : KripkeModel Atom) (φ : Formula Atom) (w : M.W) : Prop :=
match φ with
| .true => True
| .atom a => M.V a w
| .and φ₁ φ₂ => M.valid φ₁ w ∧ M.valid φ₂ w
| .imp φ₁ φ₂ => (M.valid φ₁ w → M.valid φ₂ w) -- | .imp φ₁ φ₂ => ∀ w', M.R w w' → M.valid φ₁ w' → M.valid φ₂ w' -- | .imp φ₁ φ₂ => ∀ w', M.R w w' → M.valid φ₁ w' → M.valid φ₂ w'
| .box φ => ∀ w', M.R w w' → M.valid φ w'
| .bot => False  -- ⊥

inductive Proof {Atom : Type} : List (Formula Atom) → Formula Atom → Type where
| hypo : ∀ Hypos φ, φ ∈ Hypos → Proof Hypos φ
| true_I : ∀ Hypos, Proof Hypos .true
| and_I : ∀ Hypos {φ₁ φ₂}, Proof Hypos φ₁ → Proof Hypos φ₂ → Proof Hypos (.and φ₁ φ₂)
| and_E₁ : ∀ Hypos {φ₁ φ₂}, Proof Hypos (.and φ₁ φ₂) → Proof Hypos φ₁
| and_E₂ : ∀ Hypos {φ₁ φ₂}, Proof Hypos (.and φ₁ φ₂) → Proof Hypos φ₂
| imp_I : ∀ Hypos {φ₁ φ₂}, Proof (.cons φ₁ Hypos) φ₂ → Proof Hypos (.imp φ₁ φ₂)
| imp_E : ∀ Hypos {φ₁ φ₂}, Proof Hypos (.imp φ₁ φ₂) → Proof Hypos φ₁ → Proof Hypos φ₂
| box_I : ∀ Hypos {φ}, Proof Hypos φ → Proof Hypos (.box φ)
| bot_E  : ∀ Hypos {φ}, Proof Hypos Formula.bot → Proof Hypos φ   -- ⊥-elim



-- lemma KripkeModel.valid_monotone {Atom} (M : KripkeModel Atom) :
--   ∀ (ψ : Formula Atom) {w w' : M.W}, M.R w w' → M.valid ψ w → M.valid ψ w' :=
-- by
--   intro ψ
--   induction ψ with
--   | true =>
--     intro w w' hR _; exact True.intro

--   | atom a =>
--     intro w w' hR hw
--     exact M.V_monotone a w w' hR hw

--   | and φ₁ φ₂ ih₁ ih₂ =>
--     intro w w' hR ⟨h1, h2⟩
--     exact ⟨ih₁ hR h1, ih₂ hR h2⟩

--   | imp φ₁ φ₂ ih₁ ih₂ =>
--   intro w w' hR h
--   intro u hwu hw1
--   have hwu' := M.R_trans w w' u hR hwu
--   exact h u hwu' hw1

--   | box φ ih =>
--   intro w w' hR h u hwu
--   -- by transitivity: w R w' and w' R u ⇒ w R u
--   have hwu' := M.R_trans w w' u hR hwu
--   exact h u hwu'

-- Environment: maps each hypothesis in Hypos and world w to its validity
def Env {Atom} (M : KripkeModel Atom) (Hypos : List (Formula Atom)) :=
  ∀ φ (_ : φ ∈ Hypos) (w : M.W), M.valid φ w

-- Env at the original world w
def EnvAt {Atom} (M : KripkeModel Atom) (Hypos : List (Formula Atom)) (w : M.W) :=
  ∀ φ (_ : φ ∈ Hypos), M.valid φ w

theorem KripkeModel.semanticValidity {Atom} (M : KripkeModel Atom) {Hypos}
  {φ : Formula Atom} (prf : Proof Hypos φ) (w : M.W) (env : EnvAt M Hypos w) : M.valid φ w :=
match prf with
| .hypo _ φ h => env φ h
| .true_I _ => True.intro
| .and_I _ prf₁ prf₂ => ⟨semanticValidity M  prf₁ w env, semanticValidity M prf₂ w  env⟩
| .and_E₁ _ prf' => (semanticValidity M prf' w  env).1
| .and_E₂ _ prf' => (semanticValidity M prf' w  env).2
| .imp_E _ prf_imp prf₁ =>
    let h_imp := semanticValidity M prf_imp w env
    let h₁ := semanticValidity M prf₁ w  env
    h_imp h₁
| @Proof.imp_I _ Hypos φ₁ φ₂ prf' =>
    fun hw =>
      -- define EnvAt for φ₁ :: Hypos at the same world w
      let env_at_w : EnvAt M (φ₁ :: Hypos) w :=
        fun ψ hmem =>
          match hmem with
          | List.Mem.head _ => hw          -- φ₁ holds at this world
          | List.Mem.tail _ h' => env ψ h' -- other hypotheses
      semanticValidity M prf' w env_at_w
| .box_I _ prf' =>
  fun w' hR =>
    let env_at_w' : EnvAt M Hypos w' := fun ψ hmem => sorry -- env ψ hmem
    semanticValidity M prf' w' env_at_w'
| .bot_E _ prf' => False.elim (semanticValidity M prf' w env)


-- theorem KripkeModel.semanticValidity {Atom} (M : KripkeModel Atom) {Hypos}                  ------ using Env
--   {φ : Formula Atom} (env : Env M Hypos) (prf : Proof Hypos φ) (w : M.W) : M.valid φ w :=
-- match prf with
-- | .hypo _ φ h => env φ h w
-- | .true_I _ => True.intro
-- | .and_I _ prf₁ prf₂ => ⟨semanticValidity M env prf₁ w, semanticValidity M env prf₂ w⟩
-- | .and_E₁ _ prf' => (semanticValidity M env prf' w).1
-- | .and_E₂ _ prf' => (semanticValidity M env prf' w).2
-- -- | .imp_E _ prf_imp prf₁ =>                          -- with additional structure on model
-- --     let h₁ := semanticValidity M env prf_imp w
-- --     let h₂ := semanticValidity M env prf₁ w
-- --     h₁ w (by apply M.R_refl) h₂
-- -- | .imp_E _ prf_imp prf₁ =>                          -- intuitionistic implication
-- --     let h₁ := semanticValidity M env prf_imp w
-- --     let h₂ := semanticValidity M env prf₁ w
-- --     -- apply the definition of → at w:
-- --     h₁ w (by
-- --       -- the imp validity at w for world w' requires w R w' → ...
-- --       -- so choose w' = w? But we can't assume w R w
-- --       -- So we need to adapt: we can only conclude φ₂ at w' if w R w' holds
-- --             admit) h₂
-- | .imp_E _ prf_imp prf₁ =>                               -- classical implication
--     let h_imp := semanticValidity M env prf_imp w
--     let h₁ := semanticValidity M env prf₁ w
--     h_imp h₁
-- | .box_I _ prf' =>
--     fun w' hR =>
--       semanticValidity M env prf' w'
-- -- | @Proof.imp_I _ Hypos φ₁ φ₂ prf' =>                 -- intuitionistic implication
-- --   fun w' hR hw1 =>
-- --     let env' : Env M (φ₁ :: Hypos) := fun ψ hmem w' =>
-- --       match hmem with
-- --       | List.Mem.head _ =>
-- --           -- here ψ = φ₁
-- --           Eq.ndrec hw1 (by admit)
-- --       | List.Mem.tail _ h' =>  env ψ h' w'
-- --     semanticValidity M env' prf' w'
-- | @Proof.imp_I _ Hypos φ₁ φ₂ prf' =>                    -- classical implication
--     fun hw =>
--       let env' : Env M (φ₁ :: Hypos) := fun ψ hmem w' =>
--         match hmem with
--         | List.Mem.head _ => by sorry -- hw          -- local hypothesis φ₁ at this world
--         | List.Mem.tail _ h' => env ψ h' w'
--       semanticValidity M env' prf' w
-- -- | @Proof.imp_I _ Hypos φ₁ φ₂ prf' =>
-- --   fun w' hR hw1 =>
-- --     let env' : Env M (φ₁ :: Hypos) :=
-- --       fun ψ hmem =>
-- --         match hmem with
-- --         | List.Mem.head _ => env ψ _   -- w'' fixed implicitly at w'
-- --         | List.Mem.tail _ h' => env ψ h'
-- --     semanticValidity M env' prf' w'


-- end
