import Mathlib.Tactic
import Mathlib.Order.BooleanAlgebra
import Init.System


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

-- -- Definition of Kripke model
-- structure KripkeModel extends KripkeFrame where
--   (V : W → Prop → Prop)  -- Valuation function mapping worlds to truth values of propositions


-- -- Definition of modalities
-- def box (F : KripkeModel) (φ : F.W → Prop) (w : F.W) : Prop :=
--   ∀ w' : F.W, F.R w w' → φ w'

-- def diamond (F : KripkeModel) (φ : F.W → Prop) (w : F.W) : Prop :=
--   ∃ w' : F.W, F.R w w' ∧ φ w'

-- Definition of Kripke model
structure KripkeModel (Atom : Type) extends KripkeFrame where
  (V : Atom → W → Prop)  -- Valuation function mapping worlds to truth values of propositions

-- section Boolean

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

-- Modal operators
def box (p : F.W → Prop) : F.W → Prop :=
  fun w => ∀ w', F.R w w' → p w'

def diamond (p : F.W → Prop) : F.W → Prop :=
  fun w => ∃ w', F.R w w' ∧ p w'

-- Monotonicity of □ and ◇
theorem box_monotone {p q : F.W → Prop} (h : p ≤ q) : box p ≤ box q := by
  intro w hw w' hr
  exact h w' (hw w' hr)

theorem diamond_monotone {p q : F.W → Prop} (h : p ≤ q) : diamond p ≤ diamond q := by
  intro w ⟨w', hr, hp⟩
  exact ⟨w', hr, h w' hp⟩









-- instance: OrderBot (F.W → Prop) where
--   bot_le := by intros _ _ ; simp

-- instance: OrderTop (F.W → Prop) where
--   top := (fun _ => True)
--   le_top := by intro p w ; simp

-- instance: HasCompl (F.W → Prop) where
--   compl := fun p w => ∀ w', F.R w w' → p w'

-- instance: Preorder (F.W → Prop) where
--   le_refl := sorry
--   le_trans := sorry

-- instance: PartialOrder (F.W → Prop) where
--   le_antisymm := sorry

-- instance: SemilatticeInf (F.W → Prop) where
--   inf := fun p q w => p w ∧ q w
--   inf_le_left := by intros p q w ; simp ; intro _ _ ; assumption
--   inf_le_right := sorry
--   le_inf := sorry

-- instance: SemilatticeSup (F.W → Prop) := by sorry

-- -- instance: Lattice (F.W → Prop) where

-- instance: GeneralizedHeytingAlgebra (F.W → Prop) where
--   himp := fun p q w => ∀ w', F.R w w' → p w' → q w'
--   le_himp_iff := sorry

-- -- This is our main goal
-- instance {F : KripkeFrame}: BooleanAlgebra (F.W → Prop) where
--   himp_bot := sorry

-- end

-- def UnitFrame : KripkeFrame where
--   W := Unit
--   R := fun _ _ => True

-- inductive TwoAtoms : Type
--  | p : TwoAtoms
--  | q : TwoAtoms

-- def UnitModel : KripkeModel TwoAtoms where
--   W := Unit
--   R := fun _ _ => True
--   V := fun (A : TwoAtoms) (_ : Unit) =>
--         match A with
--         | .p => True
--         | .q => False

-- inductive Formula (Atom : Type) where
-- | true : Formula Atom
-- | atom : Atom → Formula Atom
-- | and : Formula Atom → Formula Atom → Formula Atom
-- | imp : Formula Atom → Formula Atom → Formula Atom
-- | box : Formula Atom → Formula Atom

-- @[reducible, simp]
-- def KripkeModel.valid {Atom} (M : KripkeModel Atom) (φ : Formula Atom) (w : M.W) : Prop :=
-- match φ with
-- | .true => True
-- | .atom a => M.V a w
-- | .and φ₁ φ₂ => M.valid φ₁ w ∧ M.valid φ₂ w
-- | .imp φ₁ φ₂ => ∀ w', M.R w w' → M.valid φ₁ w' → M.valid φ₂ w'
-- | .box φ => ∀ w', M.R w w' → M.valid φ w'

-- inductive Proof {Atom : Type} : List (Formula Atom) → Formula Atom → Type where
-- | hypo : ∀ Hypos φ, φ ∈ Hypos → Proof Hypos φ
-- | true_I : ∀ Hypos, Proof Hypos .true
-- | and_I : ∀ Hypos {φ₁ φ₂}, Proof Hypos φ₁ → Proof Hypos φ₂ → Proof Hypos (.and φ₁ φ₂)
-- | and_E₁ : ∀ Hypos {φ₁ φ₂}, Proof Hypos (.and φ₁ φ₂) → Proof Hypos φ₁
-- | imp_I : ∀ Hypos {φ₁ φ₂}, Proof (.cons φ₁ Hypos) φ₂ → Proof Hypos (.imp φ₁ φ₂)

-- theorem KripkeModel.semanticValidity {Atom} (M : KripkeModel Atom) {Hypos} {φ : Formula Atom} (prf : Proof Hypos φ) (w : M.W) : M.valid φ w :=
--   match prf with
--   | .true_I => by simp
--   | .and_I prf₁ prf₂ => ⟨semanticValidity M prf₁ w, semanticValidity M prf₂ w⟩
--   | .and_E₁ prf' => (semanticValidity M prf' w).1

-- -- Definition of modalities
-- def box {Atom} (F : KripkeModel Atom) (φ : F.W → Prop) (w : F.W) : Prop :=
--   ∀ w' : F.W, F.R w w' → φ w'

-- def diamond {Atom} (F : KripkeModel Atom) (φ : F.W → Prop) (w : F.W) : Prop :=
--   ∃ w' : F.W, F.R w w' ∧ φ w'












-- ------------------------------------------------------------------------------------------------------------
-- -- Semantic truth of a formula at a world
-- def true_at (M : KripkeModel) (φ : M.W → Prop) (w : M.W) : Prop :=
--   φ w

-- -- Definition: A formula is true in a model if it's true at every world in it
-- def true_in_model (M : KripkeModel) (φ : M.W → Prop) : Prop :=

--   ∀ w : M.W, true_at M φ w


-- -- diamond M p w ↔ ¬ box M (¬ p) w
-- theorem dual_valid (M : KripkeModel):
--   ∀ (p : M.W → Prop) (w : M.W),
--     diamond M p w ↔ ¬ box M (fun v => ¬ p v) w :=
-- by
--   intros p w
--   apply Iff.intro
--   -- → direction: ◇p w → ¬ □¬p w
--   · intro ⟨v, hR, hp⟩ hbox
--     have hnp := hbox v hR
--     contradiction
--   -- ← direction: ¬ □¬p w → ◇p w
--   · intro h
--     by_contra hcontra
--     apply h
--     intro v hR
--     by_contra hnvp
--     apply hcontra  -- diamond M p w = ∃ v, R w v ∧ p v
--     use v




-- theorem modal_axiom_K_valid :
--   ∀ (F : KripkeModel) (A B : F.W → Prop) (w : F.W),
--     box F (λ w ↦ A w → B w) w →
--     box F A w →
--     box F B w := by {
--     intros F A B w h1 h2 v hR
--     exact (h1 v hR) (h2 v hR)
--     }



-- theorem modal_axiom_T_valid
--   (F : KripkeModel)
--   (h_refl : ∀ w : F.W, F.R w w) :
--   ∀ (A : F.W → Prop) (w : F.W),
--     box F A w → A w := by {
--       intros A w h
--       apply h w
--       exact h_refl w
--     }

-- theorem modal_dense_valid
--   (F : KripkeModel)
--   (h_dense : ∀ w u : F.W, F.R w u → ∃ v : F.W, F.R w v ∧ F.R v u) :
--   ∀ (A : F.W → Prop) (w : F.W),
--     box F (box F A) w → box F A w := by {
--       intros A w h v hR
--       -- By density, from R w v, get some intermediate v' such that R w v' ∧ R v' v
--       obtain ⟨ v', h1, h2⟩ := h_dense w v hR
--       -- From box F (box F A) w, we know: ∀ v, R w v → (∀ u, R v u → A u)
--       -- Apply it to v' to get: ∀ u, R v' u → A u
--       specialize h v' h1
--       -- Then apply h to v using R v' v
--       exact h v h2
--     }

-- theorem modal_axiom_4_valid
--   (F : KripkeModel)
--   (h_trans : ∀ w v u : F.W, F.R w v → F.R v u → F.R w u) :
--   ∀ (A : F.W → Prop) (w : F.W),
--     box F A w → box F (box F A) w := by {
--       intros A w h v hR
--       intros u hRv
--       exact h u (h_trans w v u hR hRv)
--     }

-- theorem modal_axiom_D_valid
--   (F : KripkeModel)
--   (h_serial : ∀ w : F.W, ∃ v : F.W, F.R w v) :
--   ∀ (A : F.W → Prop) (w : F.W),
--     box F A w → diamond F A w := by {
--       intros A w h_box
--       obtain ⟨ v, hR ⟩ := h_serial w
--       exists v
--       exact ⟨hR, h_box v hR⟩
--     }

-- theorem modal_axiom_B_valid
--   (F : KripkeModel)
--   (h_symm : ∀ w v, F.R w v → F.R v w) :
--   ∀ (A : F.W → Prop) (w : F.W),
--     A w → box F (diamond F A) w := by
--   intros A w hA v hR
--   use w
--   exact ⟨h_symm w v hR, hA⟩




-- theorem modal_axiom_5_valid
--   (F : KripkeModel)
--   (h_euclid : ∀ w u v : F.W, F.R w u → F.R w v → F.R u v) :
--   ∀ (A : F.W → Prop) (w : F.W),
--     diamond F A w → box F (diamond F A) w := by
--   intros A w cow v hRwv
--   obtain ⟨u, hRwu, hAu⟩ := cow
--   use u
--   constructor
--   · exact h_euclid w v u hRwv hRwu
--   · exact hAu




-- -- Frame validity definition: φ is valid on frame F if φ holds in every model and every world on F
-- def valid_on_frame (F : KripkeFrame) (φ : ∀ (M : KripkeModel), M.W → Prop) : Prop :=
--   ∀ (V : F.W → Prop → Prop) (w : F.W), φ {F with V := V} w


-- -- https://philosophy.stackexchange.com/questions/15019/proof-of-the-reflexivity-of-the-accessibility-relation

-- -- -- Fact 2a: only if direction (contrapositive)
-- -- theorem fact_2a_only_if
-- --   (F : KripkeFrame)
-- --   (hvalid : ∀ (V : F.W → Prop → Prop) (w : F.W) (φ : F.W → Prop),
-- --     (φ w → diamond {F with V := V} φ w)) :
-- --   KripkeFrame_is_reflexive F := by
-- --   by_contra h_not_refl
-- --   obtain ⟨w₀, h⟩ := not_forall.mp h_not_refl
-- --   let V : F.W → Prop → Prop := fun w p => w = w₀
-- --   let φ : F.W → Prop := fun w => w = w₀
-- --   have hφ : φ w₀ := rfl
-- --   have hdiamond := hvalid V w₀ φ
-- --   have h_imp := hdiamond hφ
-- --   obtain ⟨v, hRv, hv⟩ := h_imp
-- --   rw [hv] at hRv
-- --   contradiction

-- -- -- Fact 2b: if direction
-- -- theorem fact_2b_if
-- --   (F : KripkeFrame)
-- --   (h_refl : KripkeFrame_is_reflexive F) :
-- --   ∀ (V : F.W → Prop → Prop) (w : F.W) (φ : F.W → Prop),
-- --     (φ w → diamond {F with V := V} φ w) := by
-- --   intros V w φ hφ
-- --   exists w
-- --   constructor
-- --   · exact h_refl w
-- --   · exact hφ

-- -- -- Fact 2 combining both directions
-- -- theorem fact_2 (F : KripkeFrame) :
-- --   (∀ (V : F.W → Prop → Prop) (w : F.W) (φ : F.W → Prop),
-- --     (φ w → diamond {F with V := V} φ w)) ↔
-- --   KripkeFrame_is_reflexive F := by
-- --   apply Iff.intro
-- --   -- Only if direction (fact_2a)
-- --   · intro hvalid
-- --     by_contra h_not_refl
-- --     obtain ⟨w₀, h⟩ := not_forall.mp h_not_refl
-- --     let V : F.W → Prop → Prop := fun w p => w = w₀
-- --     let φ : F.W → Prop := fun w => w = w₀
-- --     have hφ : φ w₀ := rfl
-- --     have hdiamond := hvalid V w₀ φ
-- --     have h_imp := hdiamond hφ
-- --     obtain ⟨v, hRv, hv⟩ := h_imp
-- --     rw [hv] at hRv
-- --     contradiction

-- --   -- If direction (fact_2b)
-- --   · intro h_refl V w φ hφ
-- --     exists w
-- --     constructor
-- --     · exact h_refl w
-- --     · exact hφ




-- theorem valid_D_implies_serial
--   {F : KripkeFrame}
--   (valid_D : ∀ (M : KripkeModel), M.toKripkeFrame = F → ∀ (p : M.W → Prop) (w : M.W), box M p w → diamond M p w) :
--   ∀ w : F.W, ∃ v : F.W, F.R w v := by
--     intro w
--     by_contra no_succ
--     let M : KripkeModel := {
--       W := F.W,
--       R := F.R,
--       V := fun _ _ ↦ false
--     }
--     have hM_eq : M.toKripkeFrame = F := rfl
--     let p : M.W → Prop := fun _ ↦ true
--     have box_true : box M p w := by
--         intro v hRwv
--         trivial

--     have diamond_true := valid_D M hM_eq p w box_true
--     simp only [diamond] at diamond_true
--     have exists_R := Exists.imp (fun v ⟨hRwv, _⟩ => hRwv) diamond_true
--     exact no_succ exists_R


-- theorem valid_T_implies_reflexive
--   {F : KripkeFrame}
--   (valid_T : ∀ (M : KripkeModel), M.toKripkeFrame = F →
--               ∀ (p : M.W → Prop) (w : M.W), box M p w → p w) :
--   ∀ w : F.W, F.R w w :=
-- by {
--   intro w

--   -- Define model M based on frame F with valuation p(x) := R w x
--   let M : KripkeModel := {
--     W := F.W,
--     R := F.R,
--     V := fun x (prop : Prop) =>
--       -- We ignore prop and just use a fixed predicate p := fun x => R w x
--       -- So interpret p as a predicate, say p = True, all others False
--       if prop = True then F.R w x else False
--   }

--   -- Define p as predicate p(x) := R w x
--   let p : M.W → Prop := fun x => F.R w x

--   -- box M p w means ∀ v, R w v → p v, which is true because p v = R w v
--   have box_p_w : box M p w := by {
--     intro v hRwv
--     exact hRwv
--   }

--   -- Apply the hypothesis: from box p w, p w holds
--   have pw : p w := valid_T M rfl p w box_p_w

--   -- p w := R w w, done
--   exact pw
-- }


-- theorem valid_B_implies_symmetric
--   {F : KripkeFrame}
--   (valid_B : ∀ (M : KripkeModel), M.toKripkeFrame = F →
--               ∀ (p : M.W → Prop) (w : M.W),
--                 p w → box M (diamond M p) w) :
--   ∀ u v : F.W, F.R u v → F.R v u :=
-- by {
--   intros u v hRuv

--   -- Define valuation V so that p(w) := ¬ R v w
--   let M : KripkeModel := {
--     W := F.W,
--     R := F.R,
--     V := fun x (prop : Prop) =>
--       if prop = True then
--         -- interpret proposition p as ¬ R v x
--         ¬ F.R v x
--       else
--         False
--   }

--   let p : M.W → Prop := fun w => ¬ F.R v w

--   -- Assume p u (i.e. ¬ R v u)
--   by_contra no_sym
--   have pu : p u := no_sym

--   -- From valid_B: if p u holds then box (diamond p) u holds
--   have box_diamond_p_u : box M (diamond M p) u :=
--     valid_B M rfl p u pu

--   -- By definition of box, ∀ w, if R u w then diamond p holds at w
--   -- In particular, for w = v, since R u v = hRuv
--   have diamond_p_v : diamond M p v :=
--     box_diamond_p_u v hRuv

--   -- By definition of diamond, ∃ w', R v w' ∧ p w'
--   obtain ⟨w', hRvw', hpw'⟩ := diamond_p_v

--   have contradiction : False := hpw' hRvw'

--   exact contradiction
-- }

-- -- axiom 4 => transitivity
-- theorem valid_4_implies_transitive
--   (valid_4 : ∀ (F : KripkeFrame) (M : KripkeModel),
--       M.toKripkeFrame = F →
--       ∀ (p : M.W → Prop) (w : M.W),
--         box M p w → box M (box M p) w) :
--   ∀ (F : KripkeFrame), ∀ x y z : F.W, F.R x y → F.R y z → F.R x z :=
-- by
--   intros F x y z hxy hyz
--   by_contra h_not_xz

--   -- Define model M where p w := F.R x w
--   let M : KripkeModel :=
--     { W := F.W,
--       R := F.R,
--       V := fun w φ ↦ if φ = True then F.R x w else False }

--   let p : M.W → Prop := fun w ↦ F.R x w

--   have hM_eq : M.toKripkeFrame = F := rfl

--   -- Show box M p x holds
--   have box_p_x : box M p x := by
--     intros w' hR
--     exact hR

--   -- Use validity of axiom 4
--   have box_box_p_x := valid_4 F M hM_eq p x box_p_x

--   -- Then box p must hold at y since R x y
--   have box_p_y := box_box_p_x y hxy

--   -- Then p must hold at z since R y z
--   have : p z := box_p_y z hyz
--   simp [p] at this

--   exact h_not_xz this

-- -- axiom 5 => euclidean
-- theorem valid_5_implies_euclidean :
--   (∀ (F : KripkeFrame) (M : KripkeModel),
--     M.toKripkeFrame = F →
--     ∀ (p : M.W → Prop) (w : M.W),
--       diamond M p w → box M (diamond M p) w) →
--   ∀ (F : KripkeFrame), ∀ (w u v : F.W), F.R w u → F.R w v → F.R u v :=
-- by
--   intros valid_5 F w u v hRwu hRwv
--   by_contra h_not_Ruv

--   let M : KripkeModel :=
--     { W := F.W
--       R := F.R
--       V := fun x φ ↦ if φ = True then x = v else False }

--   let p : M.W → Prop := fun x ↦ x = v

--   have hM_eq : M.toKripkeFrame = F := rfl

--   have diamond_p_w : diamond M p w :=
--     ⟨v, hRwv, by simp [p]⟩

--   have box_diamond_p_w := valid_5 F M hM_eq p w diamond_p_w

--   have diamond_p_u := box_diamond_p_w u hRwu

--   rcases diamond_p_u with ⟨x, hRux, px⟩
--   simp [p] at px
--   rw [px] at hRux

--   exact h_not_Ruv hRux





-- --------------------------------------------------------------------------------------------------------------------
-- -- Example of frame
-- inductive World
-- | w1 | w2 | w3

-- open World

-- def example_frame : KripkeFrame :=
-- { W := World,
--   R := λ w₁ w₂ ↦
--     (w₁ = w1 ∧ w₂ = w2) ∨
--     (w₁ = w2 ∧ w₂ = w3) ∨
--     (w₁ = w3 ∧ w₂ = w1) }

-- -- #eval KripkeFrame_is_reflexive example_frame -- Should return `false` for the above example
