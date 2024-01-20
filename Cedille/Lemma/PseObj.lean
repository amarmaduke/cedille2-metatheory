
import Common
import Cedille.Def
import Cedille.Lemma.Refold
import Cedille.Lemma.Inversion
import Cedille.Lemma.Syntax

namespace Cedille

  lemma lc_of_open (x : Name) : lc i ({i |-> x}t) -> lc (Nat.succ i) t := by {
    intro h
    induction t generalizing i <;> simp
    case bound j => {
      simp at h; split at h
      case _ h2 => subst h2; simp
      case _ h2 => simp at h; linarith
    }
    case bind k t1 t2 ih1 ih2 => {
      simp at h
      cases h; case _ h1 h2 =>
      apply And.intro _ _
      apply ih1 h1; apply ih2 h2
    }
    case ctor k t1 t2 t3 ih1 ih2 ih3 => {
      simp at h
      casesm* _ ∧ _; case _ h1 h2 h3 =>
      apply And.intro _ _
      apply ih1 h1; apply And.intro _ _
      apply ih2 h2; apply ih3 h3
    }
  }

  theorem pseobj_is_lc0 : PseObj t -> lc 0 t := by {
    intro pseobj
    induction pseobj <;> simp [*]
    case bind k A B hn p1 S p2 ih1 ih2 => {
      have xfresh := @Name.fresh_is_fresh S
      generalize _xdef : @Name.fresh S = x at *
      apply lc_of_open x
      apply ih2 x xfresh
    }
    case lam A t p1 S1 p2 S2 p3 ih3 ih2 => {
      have xfresh := @Name.fresh_is_fresh S1
      generalize _xdef : @Name.fresh S1 = x at *
      apply lc_of_open x
      apply ih2 x xfresh
    }
  }

  -- lemma pseobj_rename : PseObj t -> PseObj ({i |-> y}{i <-| x}t) := by {
  --   intro h
  --   induction h generalizing i y x <;> simp
  --   case ax => constructor
  --   case var z => split <;> (simp; constructor)
  --   case bind k A B hn p1 p2 ih1 ih2 => {
  --     apply PseObj.bind hn ih1 _
  --     intro z zn; simp at zn
  --     have lem1 := fv_open2 (Nat.succ i) y ({Nat.succ i <-| x}B)
  --     have lem2 := FvSet.not_mem_subset_not_mem zn lem1
  --     have lem3 : z ≠ x := by sorry
  --     have lem4 := fv_close_var lem3 lem2
  --     replace ih2 := @ih2 z lem4 (Nat.succ i)
  --     rw [Syntax.oc5, Syntax.oc7]; exact ih2
  --     simp; simp [*]; simp
  --   }
  --   case lam => sorry
  --   case pair => sorry
  --   case ctor => sorry
  -- }

  -- Not yet used
  -- lemma pseobj_open : PseObj ({_|-> x}t) -> PseObj ({_|-> y}t) := by sorry

end Cedille
