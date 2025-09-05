import KripkeFrames.Basic

------------------------------------------------------------------------------------------------------------
-- Semantic truth of a formula at a world
def true_at {Atom : Type} (M : KripkeModel Atom) (φ : M.W → Prop) (w : M.W) : Prop :=
  φ w

-- Definition: A formula is true in a model if it's true at every world in it
def true_in_model {Atom : Type} (M : KripkeModel Atom) (φ : M.W → Prop) : Prop :=

  ∀ w : M.W, true_at M φ w


-- diamond M p w ↔ ¬ box M (¬ p) w
theorem dual_valid {Atom : Type} (M : KripkeModel Atom):
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



theorem modal_axiom_K_valid {Atom : Type} :
  ∀ (M : KripkeModel Atom) (A B : M.W → Prop) (w : M.W),
    box M (λ w ↦ A w → B w) w →
    box M A w →
    box M B w :=
by
  intros M A B w h1 h2 v hR
  exact (h1 v hR) (h2 v hR)



theorem modal_axiom_T_valid
  {Atom : Type} (F : KripkeModel Atom)
  (h_refl : ∀ w : F.W, F.R w w) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F A w → A w := by {
      intros A w h
      apply h w
      exact h_refl w
    }

theorem modal_dense_valid
  {Atom : Type} (F : KripkeModel Atom)
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
  {Atom : Type} (F : KripkeModel Atom)
  (h_trans : ∀ w v u : F.W, F.R w v → F.R v u → F.R w u) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F A w → box F (box F A) w := by {
      intros A w h v hR
      intros u hRv
      exact h u (h_trans w v u hR hRv)
    }

theorem modal_axiom_D_valid
  {Atom : Type} (F : KripkeModel Atom)
  (h_serial : ∀ w : F.W, ∃ v : F.W, F.R w v) :
  ∀ (A : F.W → Prop) (w : F.W),
    box F A w → diamond F A w := by {
      intros A w h_box
      obtain ⟨ v, hR ⟩ := h_serial w
      exists v
      exact ⟨hR, h_box v hR⟩
    }

theorem modal_axiom_B_valid
  {Atom : Type} (F : KripkeModel Atom)
  (h_symm : ∀ w v, F.R w v → F.R v w) :
  ∀ (A : F.W → Prop) (w : F.W),
    A w → box F (diamond F A) w := by
  intros A w hA v hR
  use w
  exact ⟨h_symm w v hR, hA⟩


theorem modal_axiom_5_valid
  {Atom : Type} (F : KripkeModel Atom)
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
def valid_on_frame (F : KripkeFrame) (φ : ∀ (M : KripkeModel Unit), M.W → Prop) : Prop :=
  ∀ (V : Unit → F.W → Prop) (w : F.W), φ {F with V := V} w


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
  {Atom : Type} (M : KripkeModel Atom)
  (valid_D : ∀ (p : M.W → Prop) (w : M.W), box M p w → diamond M p w) :
  ∀ (w : M.W), ∃ v : M.W, M.R w v :=
by
  intro w
  by_contra no_succ
  let p : M.W → Prop := fun _ ↦ True
  have box_true : box M p w := by intros v hR; trivial
  have diamond_true := valid_D p w box_true
  simp only [diamond] at diamond_true
  have exists_R := Exists.imp (fun v ⟨hRwv, _⟩ => hRwv) diamond_true
  exact no_succ exists_R



theorem valid_T_implies_reflexive
  {Atom : Type} (M : KripkeModel Atom)
  (valid_T : ∀ (p : M.W → Prop) (w : M.W), box M p w → p w) :
  ∀ w : M.W, M.R w w :=
by
  intro w
  -- Define p as the predicate: p(v) := R w v
  let p : M.W → Prop := fun v => M.R w v
  -- box M p w holds because for any v with R w v, p v = R w v
  have box_p_w : box M p w := by intros v hR; exact hR
  -- Apply validity of T: box p w → p w
  exact valid_T p w box_p_w


theorem valid_B_implies_symmetric
{Atom : Type} (M : KripkeModel Atom)
  (valid_B : ∀ (p : M.W → Prop) (w : M.W), p w → box M (diamond M p) w) :
  ∀ u v : M.W, M.R u v → M.R v u :=
by
  intros u v hRuv
  -- Define predicate p(w) := ¬ R v w
  let p : M.W → Prop := fun w => ¬ M.R v w
  by_contra no_sym
  have pu : p u := no_sym
  -- From valid_B: if p u holds then box (diamond p) u holds
  have box_diamond_p_u : box M (diamond M p) u :=
    valid_B p u pu
  -- By definition of box: ∀ w, if R u w then diamond p holds at w
  have diamond_p_v : diamond M p v := box_diamond_p_u v hRuv
  -- diamond p v := ∃ w', R v w' ∧ p w'
  obtain ⟨w', hRvw', hpw'⟩ := diamond_p_v
  exact hpw' hRvw' -- contradiction

-- axiom 4 => transitivity
theorem valid_4_implies_transitive
{Atom : Type} (M : KripkeModel Atom)
  (valid_4 : ∀ (p : M.W → Prop) (w : M.W), box M p w → box M (box M p) w) :
  ∀ x y z : M.W, M.R x y → M.R y z → M.R x z :=
by
  intros x y z hxy hyz
  by_contra h_not_xz
  let p : M.W → Prop := fun w => M.R x w
  have box_p_x : box M p x := by intros w' hR; exact hR
  have box_box_p_x := valid_4 p x box_p_x
  have box_p_y := box_box_p_x y hxy
  have : p z := box_p_y z hyz
  exact h_not_xz this

-- axiom 5 => euclidean
theorem valid_5_implies_euclidean
{Atom : Type} (M : KripkeModel Atom)
  (valid_5 : ∀ (p : M.W → Prop) (w : M.W), diamond M p w → box M (diamond M p) w) :
  ∀ w u v : M.W, M.R w u → M.R w v → M.R u v :=
by
  intros w u v hRwu hRwv
  by_contra h_not_Ruv
  let p : M.W → Prop := fun x => x = v
  have diamond_p_w : diamond M p w := ⟨v, hRwv, rfl⟩
  have box_diamond_p_w := valid_5 p w diamond_p_w
  have diamond_p_u := box_diamond_p_w u hRwu
  obtain ⟨x, hRux, px⟩ := diamond_p_u
  rw [px] at hRux
  exact h_not_Ruv hRux
