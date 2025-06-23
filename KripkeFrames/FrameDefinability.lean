import KripkeFrames.Basic

------------------------------------------------------------------------------------------------------------
-- Semantic truth of a formula at a world
def true_at (M : KripkeModel) (φ : M.W → Prop) (w : M.W) : Prop :=
  φ w

-- Definition: A formula is true in a model if it's true at every world in it
def true_in_model (M : KripkeModel) (φ : M.W → Prop) : Prop :=

  ∀ w : M.W, true_at M φ w


-- diamond M p w ↔ ¬ box M (¬ p) w
theorem dual_valid (M : KripkeModel):
  ∀ (p : M.W → Prop) (w : M.W),
    diamond M p w ↔ ¬ box M (fun v => ¬ p v) w :=
by
  intros p w
  apply Iff.intro
  -- → direction: ◇p w → ¬ □¬p w
  · intro ⟨v, hR, hp⟩ hbox
    have hnp := hbox v hR
    contradiction
  -- ← direction: ¬ □¬p w → ◇p w
  · intro h
    by_contra hcontra
    apply h
    intro v hR
    by_contra hnvp
    apply hcontra  -- diamond M p w = ∃ v, R w v ∧ p v
    use v




theorem modal_axiom_K_valid :
  ∀ (F : KripkeModel) (A B : F.W → Prop) (w : F.W),
    box F (λ w ↦ A w → B w) w →
    box F A w →
    box F B w := by {
    intros F A B w h1 h2 v hR
    exact (h1 v hR) (h2 v hR)
    }



theorem modal_axiom_T_valid
  (F : KripkeModel)
  (h_refl : ∀ w : F.W, F.R w w) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F A w → A w := by {
      intros A w h
      apply h w
      exact h_refl w
    }

theorem modal_dense_valid
  (F : KripkeModel)
  (h_dense : ∀ w u : F.W, F.R w u → ∃ v : F.W, F.R w v ∧ F.R v u) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F (box F A) w → box F A w := by {
      intros A w h v hR
      -- By density, from R w v, get some intermediate v' such that R w v' ∧ R v' v
      obtain ⟨ v', h1, h2⟩ := h_dense w v hR
      -- From box F (box F A) w, we know: ∀ v, R w v → (∀ u, R v u → A u)
      -- Apply it to v' to get: ∀ u, R v' u → A u
      specialize h v' h1
      -- Then apply h to v using R v' v
      exact h v h2
    }

theorem modal_axiom_4_valid
  (F : KripkeModel)
  (h_trans : ∀ w v u : F.W, F.R w v → F.R v u → F.R w u) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F A w → box F (box F A) w := by {
      intros A w h v hR
      intros u hRv
      exact h u (h_trans w v u hR hRv)
    }

theorem modal_axiom_D_valid
  (F : KripkeModel)
  (h_serial : ∀ w : F.W, ∃ v : F.W, F.R w v) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F A w → diamond F A w := by {
      intros A w h_box
      obtain ⟨ v, hR ⟩ := h_serial w
      exists v
      exact ⟨hR, h_box v hR⟩
    }

theorem modal_axiom_B_valid
  (F : KripkeModel)
  (h_symm : ∀ w v, F.R w v → F.R v w) :
  ∀ (A : F.W → Prop) (w : F.W),
    A w → box F (diamond F A) w := by
  intros A w hA v hR
  use w
  exact ⟨h_symm w v hR, hA⟩




theorem modal_axiom_5_valid
  (F : KripkeModel)
  (h_euclid : ∀ w u v : F.W, F.R w u → F.R w v → F.R u v) :
  ∀ (A : F.W → Prop) (w : F.W),
    diamond F A w → box F (diamond F A) w := by
  intros A w cow v hRwv
  obtain ⟨u, hRwu, hAu⟩ := cow
  use u
  constructor
  · exact h_euclid w v u hRwv hRwu
  · exact hAu




-- Frame validity definition: φ is valid on frame F if φ holds in every model and every world on F
def valid_on_frame (F : KripkeFrame) (φ : ∀ (M : KripkeModel), M.W → Prop) : Prop :=
  ∀ (V : F.W → Prop → Prop) (w : F.W), φ {F with V := V} w


-- https://philosophy.stackexchange.com/questions/15019/proof-of-the-reflexivity-of-the-accessibility-relation

-- -- Fact 2a: only if direction (contrapositive)
-- theorem fact_2a_only_if
--   (F : KripkeFrame)
--   (hvalid : ∀ (V : F.W → Prop → Prop) (w : F.W) (φ : F.W → Prop),
--     (φ w → diamond {F with V := V} φ w)) :
--   KripkeFrame_is_reflexive F := by
--   by_contra h_not_refl
--   obtain ⟨w₀, h⟩ := not_forall.mp h_not_refl
--   let V : F.W → Prop → Prop := fun w p => w = w₀
--   let φ : F.W → Prop := fun w => w = w₀
--   have hφ : φ w₀ := rfl
--   have hdiamond := hvalid V w₀ φ
--   have h_imp := hdiamond hφ
--   obtain ⟨v, hRv, hv⟩ := h_imp
--   rw [hv] at hRv
--   contradiction

-- -- Fact 2b: if direction
-- theorem fact_2b_if
--   (F : KripkeFrame)
--   (h_refl : KripkeFrame_is_reflexive F) :
--   ∀ (V : F.W → Prop → Prop) (w : F.W) (φ : F.W → Prop),
--     (φ w → diamond {F with V := V} φ w) := by
--   intros V w φ hφ
--   exists w
--   constructor
--   · exact h_refl w
--   · exact hφ

-- -- Fact 2 combining both directions
-- theorem fact_2 (F : KripkeFrame) :
--   (∀ (V : F.W → Prop → Prop) (w : F.W) (φ : F.W → Prop),
--     (φ w → diamond {F with V := V} φ w)) ↔
--   KripkeFrame_is_reflexive F := by
--   apply Iff.intro
--   -- Only if direction (fact_2a)
--   · intro hvalid
--     by_contra h_not_refl
--     obtain ⟨w₀, h⟩ := not_forall.mp h_not_refl
--     let V : F.W → Prop → Prop := fun w p => w = w₀
--     let φ : F.W → Prop := fun w => w = w₀
--     have hφ : φ w₀ := rfl
--     have hdiamond := hvalid V w₀ φ
--     have h_imp := hdiamond hφ
--     obtain ⟨v, hRv, hv⟩ := h_imp
--     rw [hv] at hRv
--     contradiction

--   -- If direction (fact_2b)
--   · intro h_refl V w φ hφ
--     exists w
--     constructor
--     · exact h_refl w
--     · exact hφ




theorem valid_D_implies_serial
  {F : KripkeFrame}
  (valid_D : ∀ (M : KripkeModel), M.toKripkeFrame = F → ∀ (p : M.W → Prop) (w : M.W), box M p w → diamond M p w) :
  ∀ w : F.W, ∃ v : F.W, F.R w v := by
    intro w
    by_contra no_succ
    let M : KripkeModel := {
      W := F.W,
      R := F.R,
      V := fun _ _ ↦ false
    }
    have hM_eq : M.toKripkeFrame = F := rfl
    let p : M.W → Prop := fun _ ↦ true
    have box_true : box M p w := by
        intro v hRwv
        trivial

    have diamond_true := valid_D M hM_eq p w box_true
    simp only [diamond] at diamond_true
    have exists_R := Exists.imp (fun v ⟨hRwv, _⟩ => hRwv) diamond_true
    exact no_succ exists_R


theorem valid_T_implies_reflexive
  {F : KripkeFrame}
  (valid_T : ∀ (M : KripkeModel), M.toKripkeFrame = F →
              ∀ (p : M.W → Prop) (w : M.W), box M p w → p w) :
  ∀ w : F.W, F.R w w :=
by {
  intro w

  -- Define model M based on frame F with valuation p(x) := R w x
  let M : KripkeModel := {
    W := F.W,
    R := F.R,
    V := fun x (prop : Prop) =>
      -- We ignore prop and just use a fixed predicate p := fun x => R w x
      -- So interpret p as a predicate, say p = True, all others False
      if prop = True then F.R w x else False
  }

  -- Define p as predicate p(x) := R w x
  let p : M.W → Prop := fun x => F.R w x

  -- box M p w means ∀ v, R w v → p v, which is true because p v = R w v
  have box_p_w : box M p w := by {
    intro v hRwv
    exact hRwv
  }

  -- Apply the hypothesis: from box p w, p w holds
  have pw : p w := valid_T M rfl p w box_p_w

  -- p w := R w w, done
  exact pw
}


theorem valid_B_implies_symmetric
  {F : KripkeFrame}
  (valid_B : ∀ (M : KripkeModel), M.toKripkeFrame = F →
              ∀ (p : M.W → Prop) (w : M.W),
                p w → box M (diamond M p) w) :
  ∀ u v : F.W, F.R u v → F.R v u :=
by {
  intros u v hRuv

  -- Define valuation V so that p(w) := ¬ R v w
  let M : KripkeModel := {
    W := F.W,
    R := F.R,
    V := fun x (prop : Prop) =>
      if prop = True then
        -- interpret proposition p as ¬ R v x
        ¬ F.R v x
      else
        False
  }

  let p : M.W → Prop := fun w => ¬ F.R v w

  -- Assume p u (i.e. ¬ R v u)
  by_contra no_sym
  have pu : p u := no_sym

  -- From valid_B: if p u holds then box (diamond p) u holds
  have box_diamond_p_u : box M (diamond M p) u :=
    valid_B M rfl p u pu

  -- By definition of box, ∀ w, if R u w then diamond p holds at w
  -- In particular, for w = v, since R u v = hRuv
  have diamond_p_v : diamond M p v :=
    box_diamond_p_u v hRuv

  -- By definition of diamond, ∃ w', R v w' ∧ p w'
  obtain ⟨w', hRvw', hpw'⟩ := diamond_p_v

  have contradiction : False := hpw' hRvw'

  exact contradiction
}

-- axiom 4 => transitivity
theorem valid_4_implies_transitive
  (valid_4 : ∀ (F : KripkeFrame) (M : KripkeModel),
      M.toKripkeFrame = F →
      ∀ (p : M.W → Prop) (w : M.W),
        box M p w → box M (box M p) w) :
  ∀ (F : KripkeFrame), ∀ x y z : F.W, F.R x y → F.R y z → F.R x z :=
by
  intros F x y z hxy hyz
  by_contra h_not_xz

  -- Define model M where p w := F.R x w
  let M : KripkeModel :=
    { W := F.W,
      R := F.R,
      V := fun w φ ↦ if φ = True then F.R x w else False }

  let p : M.W → Prop := fun w ↦ F.R x w

  have hM_eq : M.toKripkeFrame = F := rfl

  -- Show box M p x holds
  have box_p_x : box M p x := by
    intros w' hR
    exact hR

  -- Use validity of axiom 4
  have box_box_p_x := valid_4 F M hM_eq p x box_p_x

  -- Then box p must hold at y since R x y
  have box_p_y := box_box_p_x y hxy

  -- Then p must hold at z since R y z
  have : p z := box_p_y z hyz
  simp [p] at this

  exact h_not_xz this

-- axiom 5 => euclidean
theorem valid_5_implies_euclidean :
  (∀ (F : KripkeFrame) (M : KripkeModel),
    M.toKripkeFrame = F →
    ∀ (p : M.W → Prop) (w : M.W),
      diamond M p w → box M (diamond M p) w) →
  ∀ (F : KripkeFrame), ∀ (w u v : F.W), F.R w u → F.R w v → F.R u v :=
by
  intros valid_5 F w u v hRwu hRwv
  by_contra h_not_Ruv

  let M : KripkeModel :=
    { W := F.W
      R := F.R
      V := fun x φ ↦ if φ = True then x = v else False }

  let p : M.W → Prop := fun x ↦ x = v

  have hM_eq : M.toKripkeFrame = F := rfl

  have diamond_p_w : diamond M p w :=
    ⟨v, hRwv, by simp [p]⟩

  have box_diamond_p_w := valid_5 F M hM_eq p w diamond_p_w

  have diamond_p_u := box_diamond_p_w u hRwu

  rcases diamond_p_u with ⟨x, hRux, px⟩
  simp [p] at px
  rw [px] at hRux

  exact h_not_Ruv hRux
