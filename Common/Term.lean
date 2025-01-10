
import Common.Mathlib

inductive Mode where
| free
| erased
| type

@[reducible, simp]
instance Mode_inst_BEq : BEq Mode where
  beq m1 m2 := match m1, m2 with
  | .free, .free => true
  | .erased, .erased => true
  | .type, .type => true
  | _, _ => false

instance Mode_inst_LawfulBEq : LawfulBEq Mode where
  eq_of_beq := by intro m1 m2 h; cases m1 <;> cases m2 <;> simp at *
  rfl := by intro m; cases m <;> simp

notation "m0" => Mode.erased
notation "mt" => Mode.type
notation "mf" => Mode.free

inductive Const : Type where
| type : Const
| kind : Const

@[reducible, simp]
instance Const_inst_Beq : BEq Const where
  beq c1 c2 := match c1, c2 with
  | .type, .type => true
  | .kind, .kind => true
  | _, _ => false

instance Const_inst_LawfulBEq : LawfulBEq Const where
  eq_of_beq := by intro m1 m2 h; cases m1 <;> cases m2 <;> simp at *
  rfl := by intro m; cases m <;> simp

-- inductive CvTerm : Type where
-- | sym : CvTerm -> CvTerm
-- | trans : CvTerm -> CvTerm -> CvTerm
-- | none : CvTerm
-- | const : CvTerm
-- | bound : Nat -> CvTerm
-- | all_congr : CvTerm -> CvTerm -> CvTerm
-- | lam_congr : CvTerm -> CvTerm -> CvTerm
-- | lam_eta : CvTerm -> CvTerm
-- | lam_mf_erased : CvTerm -> CvTerm
-- | lam_m0_erased : CvTerm -> CvTerm
-- | app_congr : CvTerm -> CvTerm -> CvTerm
-- | app_beta : CvTerm -> CvTerm
-- | app_m0_erased : CvTerm -> CvTerm
-- | prod_congr : CvTerm -> CvTerm -> CvTerm
-- | pair_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
-- | pair_erased : CvTerm -> CvTerm
-- | fst_congr : CvTerm -> CvTerm
-- | fst_erased : CvTerm -> CvTerm
-- | snd_congr : CvTerm -> CvTerm
-- | snd_erased : CvTerm -> CvTerm
-- | phi_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
-- | phi_erased : CvTerm -> CvTerm
-- | eq_congr : CvTerm -> CvTerm -> CvTerm -> CvTerm
-- | refl_congr : CvTerm -> CvTerm
-- | refl_erased : CvTerm -> CvTerm
-- | subst_congr : CvTerm -> CvTerm -> CvTerm
-- | subst_erased : CvTerm -> CvTerm
-- | conv_congr : CvTerm -> CvTerm -> CvTerm
-- | conv_erased : CvTerm -> CvTerm
-- deriving BEq

inductive Term : Type where
| bound : Const -> Nat -> Term
| none : Term
| const : Const -> Term
| lam : Mode -> Term -> Term -> Term
| app : Mode -> Term -> Term -> Term
| all : Mode -> Term -> Term -> Term
| pair : Nat -> Term -> Term -> Term -> Term
| fst : Term -> Term
| snd : Term -> Term
| prod : Term -> Term -> Term
| refl : Term -> Term
| subst : Term -> Term -> Term
| phi : Term -> Term -> Term -> Term
| eq : Term -> Term -> Term -> Term
| conv : Nat -> Term -> Term -> Term

@[reducible]
def beqfn : Term -> Term -> Bool
| .bound c1 n1, .bound c2 n2 => c1 == c2 && n1 == n2
| .none, .none => true
| .const c1, .const c2 => c1 == c2
| .lam m1 x1 x2, .lam m2 y1 y2 => m1 == m2 && beqfn x1 y1 && beqfn x2 y2
| .app m1 x1 x2, .app m2 y1 y2 => m1 == m2 && beqfn x1 y1 && beqfn x2 y2
| .all m1 x1 x2, .all m2 y1 y2 => m1 == m2 && beqfn x1 y1 && beqfn x2 y2
| .pair n1 x1 x2 x3, .pair n2 y1 y2 y3 => n1 == n2 && beqfn x1 y1 && beqfn x2 y2 && beqfn x3 y3
| .fst x1, .fst y1 => beqfn x1 y1
| .snd x1, .snd y1 => beqfn x1 y1
| .prod x1 x2, .prod y1 y2 => beqfn x1 y1 && beqfn x2 y2
| .refl x1, .refl y1 => beqfn x1 y1
| .subst x1 x2, .subst y1 y2 => beqfn x1 y1 && beqfn x2 y2
| .phi x1 x2 x3, .phi y1 y2 y3 => beqfn x1 y1 && beqfn x2 y2 && beqfn x3 y3
| .eq x1 x2 x3, .eq y1 y2 y3 => beqfn x1 y1 && beqfn x2 y2 && beqfn x3 y3
| .conv n1 x1 x2, .conv n2 y1 y2 => n1 == n2 && beqfn x1 y1 && beqfn x2 y2
| _, _ => false

namespace Term

  theorem eq_of_beq : {t1 t2 : Term} -> beqfn t1 t2 = true -> t1 = t2 := by
  intro t1 t2 h
  induction t1 generalizing t2
  all_goals (cases t2 <;> simp at *)
  case bound => rw [@LawfulBEq.eq_of_beq Const _ _ _ _ h.1, h.2]; simp
  case const => rw [h]
  case lam ih1 ih2 _ _ _ => rw [@LawfulBEq.eq_of_beq Mode _ _ _ _ h.1.1, ih1 h.1.2, ih2 h.2]; simp
  case app ih1 ih2 _ _ _ => rw [@LawfulBEq.eq_of_beq Mode _ _ _ _ h.1.1, ih1 h.1.2, ih2 h.2]; simp
  case all ih1 ih2 _ _ _ => rw [@LawfulBEq.eq_of_beq Mode _ _ _ _ h.1.1, ih1 h.1.2, ih2 h.2]; simp
  case pair ih1 ih2 ih3 _ _ _ _ => rw [ih1 h.1.1.2, ih2 h.1.2, ih3 h.2, h.1.1.1]; simp
  case fst ih _ => rw [ih h]
  case snd ih _ => rw [ih h]
  case prod ih1 ih2 _ _ => rw [ih1 h.1, ih2 h.2]; simp
  case refl ih _ => rw [ih h]
  case subst ih1 ih2 _ _ => rw [ih1 h.1, ih2 h.2]; simp
  case phi ih1 ih2 ih3 _ _ _ => rw [ih1 h.1.1, ih2 h.1.2, ih3 h.2]; simp
  case eq ih1 ih2 ih3 _ _ _ => rw [ih1 h.1.1, ih2 h.1.2, ih3 h.2]; simp
  case conv ih1 ih2 _ _ _ => rw [h.1.1, ih1 h.1.2, ih2 h.2]; simp

  theorem beq_rfl : {t : Term} -> beqfn t t = true := by
  intro t; induction t <;> simp at * <;> simp [*]

end Term

@[reducible, simp]
instance Term_inst_Beq : BEq Term where
  beq t1 t2 := beqfn t1 t2

instance Term_inst_LawfulBEq : LawfulBEq Term where
  eq_of_beq := Term.eq_of_beq
  rfl := Term.beq_rfl


notation "★" => Term.const Const.type
notation "□" => Term.const Const.kind

infixl:15 "`@f" => Term.app mf
infixl:15 "`@τ" => Term.app mt
infixl:15 "`@0" => Term.app m0

notation "λf[" A "]" t:50 => Term.lam mf A t
notation "λτ[" A "]" t:50 => Term.lam mt A t
notation "λ0[" A "]" t:50 => Term.lam m0 A t

notation "∀f[" A "]" B:50 => Term.all mf A B
notation "∀τ[" A "]" B:50 => Term.all mt A B
notation "∀0[" A "]" B:50 => Term.all m0 A B

instance instInhabitedTerm : Inhabited Term where
  default := Term.none

-- namespace CvTerm

--   @[simp]
--   def refl : Term -> CvTerm
--   | .bound _ k => .bound k
--   | .none => .none
--   | .const _ => .const
--   | .lam _ t1 t2 => .lam_congr (refl t1) (refl t2)
--   | .app _ t1 t2 => .app_congr (refl t1) (refl t2)
--   | .all _ t1 t2 => .all_congr (refl t1) (refl t2)
--   | .pair t1 t2 t3 => .pair_congr (refl t1) (refl t2) (refl t3)
--   | .fst t => .fst_congr (refl t)
--   | .snd t => .snd_congr (refl t)
--   | .prod t1 t2 => .prod_congr (refl t1) (refl t2)
--   | .refl t => .refl_congr (refl t)
--   | .subst t1 t2 => .subst_congr (refl t1) (refl t2)
--   | .phi t1 t2 t3 => .phi_congr (refl t1) (refl t2) (refl t3)
--   | .eq t1 t2 t3 => .eq_congr (refl t1) (refl t2) (refl t3)
--   | .conv t1 t2 _ => .conv_congr (refl t1) (refl t2)

--   @[simp]
--   def size : CvTerm -> Nat
--   | .sym c => size c + 1
--   | .trans c1 c2 => size c1 + size c2 + 1
--   | .none => 0
--   | .const => 0
--   | .bound _ => 0
--   | .all_congr c1 c2 => size c1 + size c2 + 1
--   | .lam_congr c1 c2 => size c1 + size c2 + 1
--   | .lam_eta c => size c + 1
--   | .lam_mf_erased c => size c + 1
--   | .lam_m0_erased c => size c + 1
--   | .app_congr c1 c2 => size c1 + size c2 + 1
--   | .app_beta c => size c + 1
--   | .app_m0_erased c => size c + 1
--   | .prod_congr c1 c2 => size c1 + size c2 + 1
--   | .pair_congr c1 c2 c3 => size c1 + size c2 + size c3 + 1
--   | .pair_erased c => size c + 1
--   | .fst_congr c => size c + 1
--   | .fst_erased c => size c + 1
--   | .snd_congr c => size c + 1
--   | .snd_erased c => size c + 1
--   | .phi_congr c1 c2 c3 => size c1 + size c2 + size c3 + 1
--   | .phi_erased c => size c + 1
--   | .eq_congr c1 c2 c3 => size c1 + size c2 + size c3 + 1
--   | .refl_congr c => size c + 1
--   | .refl_erased c => size c + 1
--   | .subst_congr c1 c2 => size c1 + size c2 + 1
--   | .subst_erased c => size c + 1
--   | .conv_congr c1 c2 => size c1 + size c2 + 1
--   | .conv_erased c => size c + 1

-- end CvTerm

namespace Term

  @[simp]
  def size : Term -> Nat
  | bound _ _ => 0
  | none => 0
  | const _ => 0
  | lam _ t1 t2 => size t1 + size t2 + 1
  | app _ t1 t2 => size t1 + size t2 + 1
  | all _ t1 t2 => size t1 + size t2 + 1
  | pair _ t1 t2 t3 => size t1 + size t2 + size t3 + 1
  | fst t => size t + 1
  | snd t => size t + 1
  | prod t1 t2 => size t1 + size t2 + 1
  | refl t => size t + 1
  | subst t1 t2 => size t1 + size t2 + 1
  | phi t1 t2 t3 => size t1 + size t2 + size t3 + 1
  | eq t1 t2 t3 => size t1 + size t2 + size t3 + 1
  | conv _ t1 t2 => size t1 + size t2 + 1

  -- inductive IsFreeVar : Nat -> Term -> Prop where
  -- | bound : IsFreeVar n (.bound K n)
  -- | lam1 : IsFreeVar n A -> IsFreeVar n (.lam m A t)
  -- | lam2 : IsFreeVar (n + 1) t -> IsFreeVar n (.lam m A t)
  -- | app1 : IsFreeVar n f -> IsFreeVar n (.app m f a)
  -- | app2 : IsFreeVar n a -> IsFreeVar n (.app m f a)
  -- | all1 : IsFreeVar n A -> IsFreeVar n (.all m A t)
  -- | all2 : IsFreeVar (n + 1) t -> IsFreeVar n (.all m A t)
  -- | pair1 : IsFreeVar n B -> IsFreeVar n (.pair B t s)
  -- | pair2 : IsFreeVar n t -> IsFreeVar n (.pair B t s)
  -- | pair3 : IsFreeVar n s -> IsFreeVar n (.pair B t s)
  -- | fst : IsFreeVar n t -> IsFreeVar n (.fst t)
  -- | snd : IsFreeVar n t -> IsFreeVar n (.snd t)
  -- | prod1 : IsFreeVar n A -> IsFreeVar n (.prod A B)
  -- | prod2 : IsFreeVar (n + 1) B -> IsFreeVar n (.prod A B)
  -- | refl : IsFreeVar n t -> IsFreeVar n (.refl t)
  -- | subst1 : IsFreeVar n P -> IsFreeVar n (.subst P e)
  -- | subst2 : IsFreeVar n e -> IsFreeVar n (.subst P e)
  -- | phi1 : IsFreeVar n a -> IsFreeVar n (.phi a b e)
  -- | phi2 : IsFreeVar n b -> IsFreeVar n (.phi a b e)
  -- | phi3 : IsFreeVar n e -> IsFreeVar n (.phi a b e)
  -- | eq1 : IsFreeVar n A -> IsFreeVar n (.eq A a b)
  -- | eq2 : IsFreeVar n a -> IsFreeVar n (.eq A a b)
  -- | eq3 : IsFreeVar n b -> IsFreeVar n (.eq A a b)
  -- | conv1 : IsFreeVar n B -> IsFreeVar n (.conv B t c)
  -- | conv2 : IsFreeVar n t -> IsFreeVar n (.conv B t c)

end Term

infix:100 " ∈ " => Term.IsFreeVar
