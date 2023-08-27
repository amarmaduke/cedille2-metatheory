
import Common

namespace Cedille

  inductive Mode where
  | free
  | erased
  | type

  notation "m0" => Mode.erased
  notation "mt" => Mode.type
  notation "mf" => Mode.free

  inductive Binder where
  | lam (m : Mode)
  | pi (m : Mode)
  | inter

  inductive Constructor where
  | app (m : Mode)
  | pair
  | fst
  | snd
  | eq
  | refl
  | eqind
  | promote
  | delta
  | phi

  inductive Constant where
  | typeU : Constant
  | kindU : Constant

  notation:300 "Term" n:300 => (@Syntax Binder Constructor Constant n)

  def const {n} (k : Constant) : Term n := Syntax.const k
  def typeu {n} : Term n := Syntax.const Constant.typeU
  def kindu {n} : Term n := Syntax.const Constant.kindU
  def free {n} (x : Name) : Term n := Syntax.free x
  def bound {n} (i : Fin n) : Term n := Syntax.bound i
  def lam {n} (m : Mode) (t1 : Term n) (t2 : Term (n + 1)) : Term n
    := Syntax.bind (Binder.lam m) t1 t2
  def pi {n} (m : Mode) (t1 : Term n) (t2 : Term (n + 1)) : Term n
    := Syntax.bind (Binder.pi m) t1 t2
  def inter {n} (t1 : Term n) (t2 : Term (n + 1)) : Term n := Syntax.bind Binder.inter t1 t2
  def app {n} (m : Mode) (t1 t2 : Term n) : Term n
    := Syntax.ctor (Constructor.app m) t1 t2 kindu
  def pair {n} (t1 t2 t3 : Term n) : Term n := Syntax.ctor Constructor.pair t1 t2 t3
  def fst {n} (t : Term n) : Term n := Syntax.ctor Constructor.fst t kindu kindu
  def snd {n} (t : Term n) : Term n := Syntax.ctor Constructor.snd t kindu kindu
  def eq {n} (t1 t2 t3 : Term n) : Term n := Syntax.ctor Constructor.eq t1 t2 t3
  def refl {n} (t : Term n) : Term n := Syntax.ctor Constructor.refl t kindu kindu
  def J {n} : Term n := Syntax.ctor Constructor.eqind kindu kindu kindu
  def promote {n} (t : Term n) : Term n := Syntax.ctor Constructor.promote t kindu kindu
  def delta {n} (t : Term n) : Term n := Syntax.ctor Constructor.delta t kindu kindu
  def phi {n} (t1 t2 t3 : Term n) : Term n := Syntax.ctor Constructor.phi t1 t2 t3

  def fv {n} (t : Term n) := Syntax.fv t
  def size {n} (t : Term n) := Syntax.size t

  notation:400 a:400 " @ω " b:401 => app mf a b
  notation:400 a:400 " @0 " b:401 => app m0 a b
  notation:400 a:400 " @τ " b:401 => app mt a b

-- eqind : Red (J @τ t1 @τ t2 @0 t3 @0 t4 @ (refl t5) @ t6) (t6 @τ t1)
-- FIXME:
  def eqind_t : Term n :=
    pi m0 typeu (
      pi m0 (
        pi mt (bound 0) (
          pi mt (bound 1) (
            pi mt (eq (bound 0) (bound 1) (bound 0)) typeu
          )
        )
      ) (
        pi m0 (bound 1) (
          pi m0 (bound 2) (
            pi mf (eq (bound 1) (bound 2) (bound 0)) (
              pi mf (
                pi m0 (bound 6) (eq (bound 0) (bound 0) (bound 0))
              ) (
                (bound 4 /- P -/)
                  @τ (bound 4 /- x -/)
                  @τ (bound 5 /- y -/)
                  @τ (bound 6 /- x = y -/)
              )
            )
          )
        )
      )
    )
  -- def eqind_p (A : Term 0) : Term 0 := pi A (
  --   pi (Syntax.weaken A 1) (
  --     pi (eq (Syntax.weaken A 2) (bound 1) (bound 0)) (
  --       typeu
  --   )))

  -- def eqind_r (A : Term 0) (P : Term 0) : Term 0 := epi A (
  --   let x : Term 1 := bound 0;
  --   let r : Term 1 := refl (Syntax.weaken A 1) x;
  --   (Syntax.weaken P 1) ⬝ x ⬝ x ⬝ r
  -- )

  def idt : Term 0 := pi m0 typeu (pi mf (bound 0) (bound 1))

  def cbool : Term 0 := pi m0 typeu (pi mf (bound 0) (pi mf (bound 1) (bound 2)))
  def ctt : Term 0 := lam m0 typeu (lam mf (bound 0) (lam mf (bound 1) (bound 1)))
  def cff : Term 0 := lam m0 typeu (lam mf (bound 0) (lam mf (bound 1) (bound 0)))

  def erase {n} (t : Term n) : Term n :=
    match t with
    | Syntax.free x => free x
    | Syntax.bound i => bound i
    | Syntax.const c => const c
    | Syntax.bind (Binder.lam m) t1 t2 =>
      match m with
      | m0 => let x := Name.fresh (fv t2); erase ({_|-> x}t2)
      | mt => lam mt (erase t1) (erase t2)
      | mf => lam mf kindu (erase t2)
    | Syntax.bind (Binder.pi m) t1 t2 => pi m (erase t1) (erase t2)
    | Syntax.bind Binder.inter t1 t2 => inter (erase t1) (erase t2)
    | Syntax.ctor (Constructor.app m) t1 t2 _ =>
      match m with
      | m0 => erase t1
      | m => app m (erase t1) (erase t2)
    | Syntax.ctor Constructor.pair t1 _t2 _ => erase t1
    | Syntax.ctor Constructor.fst t _ _ => erase t
    | Syntax.ctor Constructor.snd t _ _ => erase t
    | Syntax.ctor Constructor.eq t1 t2 t3 => eq (erase t1) (erase t2) (erase t3)
    | Syntax.ctor Constructor.refl _t _ _ => lam mf kindu (bound 0)
    | Syntax.ctor Constructor.eqind _ _ _ => lam mf kindu (bound 0)
    | Syntax.ctor Constructor.promote t _ _ => erase t
    | Syntax.ctor Constructor.delta t _ _ => erase t
    | Syntax.ctor Constructor.phi t1 _t2 _t3 => erase t1
  termination_by _ => Syntax.size t
  decreasing_by {
    simp_wf
    all_goals (try linarith)
  }

  inductive Red : Term 0 -> Term 0 -> Prop where
  | beta : Red (app m (lam m t1 t2) t3) ([_:= t3]t2)
  | fst : Red (fst (pair t1 t2 t3)) t1
  | snd : Red (snd (pair t1 t2 t3)) t2
  | eqind : Red (J @0 t1 @0 t2 @0 t3 @0 t4 @ω (refl t5) @ω t6) (t6 @0 t5)
  | promote : Red (promote (refl (fst t))) (refl t)
  | phi : (erase t1) = (erase t2) -> Red (phi t1 t2 t3) t2
  | bind1 : Red t1 t1' -> Red (Syntax.bind k t1 t2) (Syntax.bind k t1' t2)
  | bind2 {S : FvSet!} :
    ((x : Name) -> x ∉ S -> Red ({_|-> x}t2) ({_|-> x}t2')) ->
    Red (Syntax.bind k t1 t2) (Syntax.bind k t1 t2')
  | ctor1 : Red t1 t1' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1' t2 t3)
  | ctor2 : Red t2 t2' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1 t2' t3)
  | ctor3 : Red t3 t3' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1 t2 t3')

  notation:150 t1:150 " -β> " t2:150 => Red t1 t2

  inductive RedStar : Term 0 -> Term 0 -> Prop where
  | refl : RedStar t t
  | step : t1 -β> t2 -> RedStar t2 t3 -> RedStar t1 t3

  notation:150 t1:150 " -β>* " t2:150 => RedStar t1 t2
  notation:150 t1:150 " -β>+ " t2:150 => ∃ k : Term n, t1 -β> k ∧ k -β>* t2

  inductive Conv : Term 0 -> Term 0 -> Prop where
  | conv :
    t1 -β>* t1' ->
    t2 -β>* t2' ->
    (erase t1') = (erase t2') ->
    Conv t1 t2

  notation:150 t1:150 " =β= " t2:150 => Conv t1 t2

  namespace Mode
    def pi_domain (m : Mode) (K : Constant) : Term n :=
      match m with
      | mf => typeu
      | mt => const K
      | m0 => const K

    def pi_codomain (m : Mode) : Term n :=
      match m with
      | mf => typeu
      | mt => kindu
      | m0 => typeu

    def lam_domain (m : Mode) : Term n :=
      match m with
      | mf => typeu
      | mt => kindu
      | m0 => typeu
  end Mode

  mutual

  inductive Infer : Map! (Term 0) -> Term 0 -> Term 0 -> Prop
  -- Basic
  | ax :
    Wf Γ ->
    Infer Γ typeu kindu
  | var :
    Wf Γ ->
    (x, A) ∈ Γ ->
    Infer Γ (free x) A
  -- Functions
  | pi {S : FvSet!} :
    ConInfer Γ A (Mode.pi_domain m K) ->
    ((x : Name) -> x ∉ S -> ConInfer (Γ ++ [x:A]) ({_|-> x}B) (Mode.pi_codomain m)) ->
    Infer Γ (pi m A B) (Mode.pi_codomain m)
  | lam {S : FvSet!} :
    ConInfer Γ A (const K) ->
    ((x : Name) -> x ∉ S -> Infer (Γ ++ [x:A]) ({_|-> x}t) ({_|-> x}B)) ->
    (m = m0 -> (x : Name) -> x ∉ fv t -> x ∉ (fv ∘ erase) ({_|-> x}t)) ->
    Infer Γ (lam m A t) (pi m A B)
  | app {S : FvSet!} :
    ConInfer Γ f (pi m A B) ->
    Check Γ a A ->
    Infer Γ (app m f a) ([_:= a]B)
  -- Intersections
  | inter {S : FvSet!} :
    ConInfer Γ A typeu ->
    ((x : Name) -> x ∉ S -> ConInfer (Γ ++ [x:A]) ({_|-> x}B) typeu) ->
    Infer Γ (inter A B) typeu
  | pair :
    ConInfer Γ T (pi mt A B) ->
    Check Γ t A ->
    Check Γ s ([_:= t]B) ->
    t =β= s ->
    Infer Γ (pair t s T) (inter A B)
  | fst :
    ConInfer Γ t (inter A B) ->
    Infer Γ (fst t) A
  | snd :
    ConInfer Γ t (inter A B) ->
    Infer Γ (snd t) ([_:= fst t]B)
  -- Equality
  | eq :
    Check Γ a A ->
    Check Γ b A ->
    Infer Γ (eq A a b) typeu
  | refl :
    Infer Γ t A ->
    Infer Γ (refl t) (eq A t t)
  | eqind : Infer Γ J eqind_t
  | promote :
    ConInfer Γ e (eq T (fst a) (fst b)) ->
    ConInfer Γ a (inter A B) ->
    Infer Γ (promote e) (eq (inter A B) a b)
  | phi :
    ConInfer Γ b (inter A B) ->
    Check Γ a A ->
    Check Γ e (eq A a (fst b)) ->
    (fv (erase b)) ⊆ (fv (erase a)) ->
    (fv (erase e)) ⊆ (fv (erase a)) ->
    Infer Γ (phi a b e) (inter A B)
  | delta :
    Check Γ e (eq cbool ctt cff) ->
    Infer Γ (delta e) (pi m0 typeu (bound 0))

  inductive ConInfer : (Map! (Term 0)) -> Term 0 -> Term 0 -> Prop where
  | infer :
    Infer Γ t A ->
    A -β>* B ->
    ConInfer Γ t B

  inductive Check : (Map! (Term 0)) -> Term 0 -> Term 0 -> Prop where
  | check :
    Infer Γ t A ->
    A =β= B ->
    Check Γ t B

  inductive Wf : (Map! (Term 0)) -> Prop where
  | nil : Wf List.nil
  | append : x ∉ (Map.fv Γ) -> Wf Γ -> ConInfer Γ A (const K) -> Wf (Γ ++ [x : A])

  end

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Infer Γ t A
  notation:170 Γ:170 " ⊢ " t:170 " >: " A:170 => ConInfer Γ t A
  notation:170 Γ:170 " ⊢ " t:170 " =: " A:170 => Check Γ t A
  notation:170 "⊢ " Γ:170 => Wf Γ

  -- namespace Infer
  --   def simple_rec (P : ∀ n, Map! (Term n) -> Term n -> Term n -> Prop) := @Infer.rec
  --     (λ n Γ t a _ => @P n Γ t a)
  --     (λ n Γ t a _ => @P n Γ t a)
  --     (λ n Γ t a _ => @P n Γ t a)
  --     (λ _ _ => True)
  -- end Infer

end Cedille
