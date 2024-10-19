
import Common

namespace Cedille

  namespace Mode
    def dom (m : Mode) (K : Const) : Term :=
      match m with
      | mf => .const .type
      | mt => .const K
      | m0 => .const K

    def codom (m : Mode) : Term :=
      match m with
      | mf => .const .type
      | mt => .const .kind
      | m0 => .const .type
  end Mode

  notation "#" m => Term.bound (Term.mode_to_sort m) 0

  inductive Conv : CvTerm -> Term -> Term -> Prop
  | sym : Conv c t2 t1 -> Conv (.sym c) t1 t2
  | ax : Conv .ax ★ ★
  | var : Conv .var (.bound K x) (.bound K x)
  | pi : Conv c1 A1 A2 -> Conv c2 B1 B2 ->
    Conv (.pi c1 c2) (.all m A1 B1) (.all m A2 B2)
  | lam_mt : Conv c1 A1 A2 -> Conv c2 t1 t2 ->
    Conv (.lam_mt c1 c2) (.lam mt A1 t1) (.lam mt A2 t2)
  | lam_mf : Conv c t1 t2 ->
    Conv (.lam_mf c) (.lam mf A1 t1) (.lam mf A2 t2)
  | lam_eta : m ≠ m0 ->
    Conv c (t1 β[ #m ]) (.app m t2 (#m)) ->
    Conv (.lam_eta c) (.lam m A t1) t2
  | lam_m0 : Conv c t1 t2 -> Conv (.lam_m0 c) (.lam m0 A t1) t2
  | app : Conv c1 f1 f2 -> Conv c2 a1 a2 ->
    Conv (.app c1 c2) (.app m f1 f2) (.app m a1 a2)
  | app_beta :
    Conv c (b β[t]) t2 ->
    Conv (.app_beta c) (.app m (.lam m A b) t) t2
  | app_m0 : Conv c t1 t2 -> Conv (.app_m0 c) (.app m0 t1 a) t2
  | prod : Conv c1 A1 A2 -> Conv c2 B1 B2 ->
    Conv (.prod c1 c2) (.prod A1 B1) (.prod A2 B2)
  | pair : Conv c t1 t2 -> Conv (.pair c) (.pair T1 t1 s1 c1) t2
  | fst : Conv c t1 t2 -> Conv (.fst c) (.fst t1) t2
  | snd : Conv c t1 t2 -> Conv (.snd c) (.snd t1) t2
  | eq : Conv c1 A1 A2 -> Conv c2 a1 a2 -> Conv c3 b1 b2 ->
    Conv (.eq c1 c2 c3) (.eq A1 a1 b1) (.eq A2 a2 b2)
  | refl : Conv c (.lam mf .none (.bound .type 0)) t2 ->
    Conv (.refl c) (.refl A1 t1) t2
  | subst : Conv c e1 t2 -> Conv (.subst c) (.subst A1 P1 a1 b1 e1) t2
  | conv : Conv c t1 t2 -> Conv (.conv c) (.conv A1 t1 c1) t2

  notation:100 c:101 " : " A:99 " === " B:98 => Conv c A B

  inductive Proof : List Term -> Term -> Term -> Prop
  | ax : Proof Γ ★ □
  | var :
    List.getI Γ x = A ->
    Proof (List.take x Γ) A (.const K) ->
    Proof Γ (.bound K x) A
  | pi :
    Proof Γ A (Mode.dom m K) ->
    Proof (A::Γ) B (Mode.codom m) ->
    Proof Γ (.all m A B) (Mode.codom m)
  | lam :
    Proof Γ A (Mode.dom m K) ->
    Proof (A::Γ) t B ->
    Proof (A::Γ) B (Mode.codom m) ->
    (m = m0 -> t β[.none] = t) ->
    Proof Γ (.lam m A t) (.all m A B)
  | app :
    Proof Γ f (.all m A B) ->
    Proof Γ a A ->
    Proof Γ (.app m f a) (B β[a])
  | prod :
    Proof Γ A ★ ->
    Proof (A::Γ) B ★ ->
    Proof Γ (.prod A B) ★
  | pair :
    Proof Γ (.prod A B) ★ ->
    Proof Γ t A ->
    Proof Γ s (B β[t]) ->
    c : t === s ->
    Proof Γ (.pair (.prod A B) t s c) (.prod A B)
  | fst :
    Proof Γ t (.prod A B) ->
    Proof Γ (.fst t) A
  | snd :
    Proof Γ t (.prod A B) ->
    Proof Γ (.snd t) (B β[.fst t])
  | eq :
    Proof Γ A ★ ->
    Proof Γ a A ->
    Proof Γ b A ->
    Proof Γ (.eq A a b) ★
  | refl :
    Proof Γ A ★ ->
    Proof Γ t A ->
    Proof Γ (.refl A t) (.eq A t t)
  | subst :
    Proof Γ A ★ ->
    Proof Γ P (.all mt A ★) ->
    Proof Γ a A ->
    Proof Γ b A ->
    Proof Γ e (.eq A a b) ->
    Proof Γ (.subst A P a b e) (.all mf (.app mt P a) (.app mt P b))
  | conv :
    Proof Γ t A ->
    Proof Γ B K ->
    c : A === B ->
    Proof Γ (.conv B t c) B

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Proof Γ t A

  namespace Term
    def bot : Term := .all mf ★ (.bound .type 0)
    def botv : Term := .bound .type 0
  end Term

  -- theorem false_conv_implies_eq : c : Term.bot === A -> Term.bot = A := by {
  --   sorry
  -- }

  -- lemma test : (A -> ¬ B) -> ¬ (A ∧ B) := by {
  --   intro h1 h2
  --   apply h1 h2.1 h2.2
  -- }

  -- lemma consistency_snd : Term.Neutral t -> ¬ ([] ⊢ .snd t : Term.bot) := by {
  --   intro hn h
  --   generalize Γdef : [] = Γ at h
  --   generalize Adef : Term.bot = A at h
  --   cases h; case _ C D j => {
  --     sorry
  --   }
  -- }

  theorem consistency_normal4 : Term.Normal t -> [★] ⊢ t : Term.botv -> False :=
    λ hn => @Term.Normal.rec
    (λ t hn => ∀ T, Term.Normal T -> T ≠ ★ -> [★] ⊢ t : T -> False)
    (λ t hn => [★] ⊢ t : Term.botv -> False)
    (by {
      simp at *; intro c k T h
      sorry
    })
    (by {
      simp at *; intro f a m nh1 nh2 ih1 ih2 T h
      cases h; case _ _ _ j _ =>
      apply ih1 _ j
    })
    (by {
      simp at *; intro t nh ih1 T h
      cases h; case _ _ j =>
      apply ih1 _ j
    })
    (by {
      simp at *; intro t nh ih T h
      cases h; case _ _ _ j =>
      apply ih _ j
    })
    (by {
      simp at *; intro A P a b e nhA nhP nha nhb nhe ihA ihP iha ihb ihe T h
      cases h; case _ _ _ _ _ j =>
      apply ihe _ j
    })
    (by {
      simp at *; intro a b e nha nhb nhe ih1 ih2 ih3 T h
      cases h
    })
    (by {
      simp at *; intro B t c nh1 nh2 h1 h2 T h
      cases h; case _ _ _ _ j _ =>
      apply h2 _ j
    })
    (by {
      simp at *; intro c k h
      cases h; case _ j1 j2 =>
      sorry
    })
    (by {
      simp at *; intro K h
      cases h
    })
    (by {
      simp at *; intro A t m nh1 nh2 ih1 ih2 h
      cases h
    })
    (by {
      simp at *; intro f a m nh1 nh2 ih1 ih2 h
      sorry
    })
    (by {
      simp at *; intro A B m nh1 nh2 ih1 ih2 h
      sorry
    })
    (by {
      simp at *; intro T t s c nhT nht nhs ihT iht ihs h
      cases h
    })
    (by {
      simp at *; intro t hn ih h
      cases h; case _ _ j =>
      apply ih _ j
    })
    (by {
      simp at *; intro t hn ih h
      sorry
    })
    (by {
      simp at *; intro A B nhA nhB ihA ihB h
      cases h
    })
    (by {
      simp at *; intro A t nhA nht ihA iht h
      cases h
    })
    (by {
      simp at *; intro A P a b e nhA nhP nha nhb nhe ihA ihP iha ihb ihe h
      cases h
    })
    (by {
      simp at *; intro a b e nha nhb nhe iha ihb ihe h
      cases h
    })
    (by {
      simp at *; intro A a b nhA nha nhb ihA ihb iha h
      cases h
    })
    (by {
      simp at *; intro B t c nhB nht ihB iht h
      cases h; case _ A K j1 j2 j3 =>
      sorry
    })
    t
    hn

  -- inductive FalseLike : Term -> Prop
  -- | bot : FalseLike Term.bot
  -- | fst : FalseLike t1 -> FalseLike (.prod t1 t2)
  -- | snd : FalseLike t2 -> FalseLike (.prod t1 t2)
  -- | app m : [] ⊢ t : A -> FalseLike (B β[t]) -> FalseLike (.all m A B)

  -- theorem consistency_normal3
  --   : Term.Neutral t ∨ Term.Normal t -> FalseLike T -> ¬ ([] ⊢ t : T)
  -- := @Nat.rec
  --   (λ s => ∀ t T, Term.size t ≤ s ->
  --     Term.Neutral t ∨ Term.Normal t ->
  --     FalseLike T ->
  --     ¬ ([] ⊢ t : T))
  --   (by {
  --     simp; intro t sh h
  --     cases t <;> simp at *
  --     case bound c k => {
  --       intro h
  --       generalize Γdef : [] = Γ at h
  --       generalize Adef : Term.bot = A at h
  --       sorry
  --     }
  --     case none => sorry
  --     case const => sorry
  --   })
  --   (by {
  --     simp; intro s ih t T sh nh fh h
  --     generalize Γdef : [] = Γ at h
  --     cases t <;> simp at *
  --     case bound c k => rw [<-Γdef] at *; apply ih (.bound c k) T (by simp) nh fh h
  --     case none => rw [<-Γdef] at *; apply ih .none T (by simp) nh fh h
  --     case const c => rw [<-Γdef] at *; apply ih (.const c) T (by simp) nh fh h
  --     case app m t1 t2 => {
  --       have sh1 : Term.size t1 ≤ s := by sorry
  --       have sh2 : Term.size t2 ≤ s := by sorry
  --       cases h; case _ A B j1 j2 => {
  --         rw [<-Γdef] at *
  --         replace fh := FalseLike.app m j2 fh
  --         cases nh
  --         case _ nh => cases nh; case _ n1 n2 => apply ih _ _ sh1 (.inl n1) fh j1
  --         case _ nh => cases nh; case _ n1 n2 => apply ih _ _ sh1 (.inl n1) fh j1
  --       }
  --     }
  --     case all => sorry
  --     case lam m t1 t2 => {
  --       have sh1 : Term.size t1 ≤ s := by sorry
  --       have sh2 : Term.size t2 ≤ s := by sorry
  --       cases h; case _ K B j1 j2 j3 j4 => {
  --         sorry
  --       }
  --     }
  --     case pair t1 t2 t3 c => {
  --       have sh1 : Term.size t1 ≤ s := by sorry
  --       have sh2 : Term.size t2 ≤ s := by sorry
  --       have sh3 : Term.size t3 ≤ s := by sorry
  --       cases h; case _ A B j1 j2 j3 j4 => {
  --         sorry
  --       }
  --     }
  --     case fst t => {
  --       replace sh : Term.size t ≤ s := by sorry
  --       cases h; case _ B j => {
  --         have fh : FalseLike (.prod T B) := .fst fh
  --         rw [<-Γdef] at j
  --         cases nh
  --         case _ nh => cases nh; case _ nh => apply ih _ _ sh (.inl nh) fh j
  --         case _ nh => cases nh; case _ nh => apply ih _ _ sh (.inl nh) fh j
  --       }
  --     }
  --     case snd t => {
  --       sorry
  --     }
  --     case prod => sorry
  --     case refl => sorry
  --     case subst t1 t2 t3 t4 t5 => {
  --       cases h; case _ j1 j2 j3 j4 j5 => {
  --         sorry
  --       }
  --     }
  --     case phi => sorry
  --     case eq => sorry
  --     case conv t1 t2 c => {
  --       have sh1 : Term.size t1 ≤ s := by sorry
  --       have sh2 : Term.size t2 ≤ s := by sorry
  --       sorry
  --     }
  --   })
  --   (Term.size t)
  --   t
  --   T
  --   (by rfl)

  -- theorem consistency_normal : ¬ ([] ⊢ t : Term.bot ∧ Term.Normal t) := by {
  --   intro h
  --   generalize Γdef : [] = Γ at h
  --   generalize Adef : Term.bot = A at h
  --   induction h.1
  --   case ax => injection Adef
  --   case var => sorry
  --   case pi m _ _ _ _ _ _ => cases m <;> injection Adef
  --   case lam => sorry
  --   case app => sorry
  --   case prod => injection Adef
  --   case pair => injection Adef
  --   case fst => sorry
  --   case snd Γ t A B j ih => {
  --     cases h.2; case _ hn => {
  --       rw [<-Adef, <-Γdef] at h
  --       sorry
  --     }
  --   }
  --   case eq => injection Adef
  --   case refl => injection Adef
  --   case subst => injection Adef with _ h2; injection h2
  --   case conv Γ t A B K c j1 j2 j3 ih1 ih2 => {
  --     subst Γdef; subst Adef; simp at *
  --     let j3 := false_conv_implies_eq (Conv.sym j3)
  --     cases h.2; case _ _ nt =>
  --     apply ih1 j3 j1 nt
  --   }
  -- }

end Cedille
