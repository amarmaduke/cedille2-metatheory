
import Common

namespace SystemFOmega

  inductive Binder where
  | lam
  | pi

  inductive Constructor where
  | app

  inductive Constant where
  | typeU : Constant
  | kindU : Constant

  notation:300 "ωTerm" n:300 => (@Syntax Binder Constructor Constant n)
  notation:300 "ωTerm" => (@Syntax Binder Constructor Constant 0)


  def const {n} (k : Constant) : ωTerm n := Syntax.const k
  def typeu {n} : ωTerm n := Syntax.const Constant.typeU
  def kindu {n} : ωTerm n := Syntax.const Constant.kindU
  def free {n} (x : Name) : ωTerm n := Syntax.free x
  def lam {n} (t1 : ωTerm n) (t2 : ωTerm (n + 1)) : ωTerm n := Syntax.bind Binder.lam t1 t2
  def pi {n} (t1 : ωTerm n) (t2 : ωTerm (n + 1)) : ωTerm n := Syntax.bind Binder.pi t1 t2
  def app {n} (t1 t2 : ωTerm n) : ωTerm n := Syntax.ctor Constructor.app t1 t2 typeu
  def fv {n} (t : ωTerm n) := Syntax.fv t
  def weaken {n} (t : ωTerm n) m : ωTerm (n + m) := Syntax.weaken t m

  inductive Red : ωTerm -> ωTerm -> Sort _ where
  | beta : Red (app (lam t1 t2) t3) ([_:= t3]t2)
  | bind1 : Red t1 t1' -> Red (Syntax.bind k t1 t2) (Syntax.bind k t1' t2)
  | bind2 {S : FvSet!} : ((x : Name) -> ¬ x ∈ S -> Red ({_|-> x}t2) ({_|-> x}t2'))
    -> Red (Syntax.bind k t1 t2) (Syntax.bind k t1 t2')
  | ctor1 : Red t1 t1' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1' t2 t3)
  | ctor2 : Red t2 t2' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1 t2' t3)
  | ctor3 : Red t3 t3' -> Red (Syntax.ctor k t1 t2 t3) (Syntax.ctor k t1 t2 t3')

  notation:150 t1:150 " -β> " t2:150 => Red t1 t2

  inductive RedStar : ωTerm -> ωTerm -> Sort _ where
  | refl : RedStar t t
  | step : t1 -β> t2 -> RedStar t2 t3 -> RedStar t1 t3

  notation:150 t1:150 " -β>* " t2:150 => RedStar t1 t2

  inductive Conv : ωTerm -> ωTerm -> Sort _ where
  | conv : t1 -β>* t1' -> t2 -β>* t2' -> t1' = t2' -> Conv t1 t2

  notation:150 t1:150 " =β= " t2:150 => Conv t1 t2

  mutual
  
  inductive Infer : (Map! ωTerm) -> ωTerm -> ωTerm -> Prop where
  | ax :
    Wf Γ ->
    Infer Γ typeu kindu
  | var {A : ωTerm 0} :
    Wf Γ ->
    Γ = Γ1 ++ [x : A] ++ Γ2 ->
    Infer Γ (free x) A
  | pi1 {S : FvSet!} :
    Check Γ A kindu ->
    ((x : Name) -> x ∉ S -> Check (Γ ++ [x : A]) ({_|-> x}B) kindu) ->
    Infer Γ (pi A B) kindu
  | pi2 {S : FvSet!} :
    ConInfer Γ A (const K) ->
    ((x : Name) -> x ∉ S -> Check (Γ ++ [x : A]) ({_|-> x}B) typeu) ->
    Infer Γ (pi A B) typeu
  | lam {S : FvSet!} :
    ConInfer Γ A (const K) ->
    ((x : Name) -> x ∉ S -> Infer (Γ ++ [x : A]) ({_|-> x}N) ({_|-> x}B)) ->
    Infer Γ (lam A N) (pi A B)
  | app :
    ConInfer Γ M (pi A B) ->
    Check Γ N A ->
    Infer Γ (app M N) ([_:= N]B)

  inductive ConInfer : (Map! ωTerm) -> ωTerm -> ωTerm -> Prop where
  | infer :
    Infer Γ t A ->
    A -β>* B ->
    ConInfer Γ t B

  inductive Check : (Map! ωTerm) -> ωTerm -> ωTerm -> Prop where
  | check :
    Infer Γ t A ->
    ConInfer Γ B (const K) ->
    A =β= B ->
    Check Γ t B

  inductive Wf : (Map! ωTerm) -> Prop where
  | nil : Wf List.nil
  | append : x ∉ (Map.fv Γ) -> Wf Γ -> ConInfer Γ A (const K) -> Wf (Γ ++ [x : A])

  end

  notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Infer Γ t A
  notation:170 Γ:170 " ⊢ " t:170 " >: " A:170 => ConInfer Γ t A
  notation:170 Γ:170 " ⊢ " t:170 " =: " A:170 => Check Γ t A
  notation:170 "⊢ " Γ:170 => Wf Γ

  axiom infer {n : Nat} : Map! ωTerm n -> ωTerm n -> Option (ωTerm n)
  axiom infer_const {n : Nat} : Map! ωTerm n -> ωTerm n -> Option Constant
  axiom infer_pi {n : Nat} : Map! ωTerm n -> ωTerm -> Option (ωTerm n × ωTerm (n + 1))
  axiom check {n : Nat} : Map! ωTerm n -> ωTerm n -> ωTerm n -> Option Unit
  axiom wf {n : Nat} : Map! ωTerm n -> Option Unit

  axiom infer_sound {Γ : Map! ωTerm} {t A : ωTerm}
    : infer Γ t = some A -> Γ ⊢ t : A
  axiom infer_complete {Γ : Map! ωTerm} {t A : ωTerm}
    : Γ ⊢ t : A -> infer Γ t = some A
  
  axiom infer_const_sound {Γ : Map! ωTerm} {t : ωTerm} {K : Constant}
    : infer Γ t = some (const K) -> Γ ⊢ t >: const K
  axiom infer_const_complete {Γ : Map! ωTerm} {t : ωTerm} {K : Constant}
    : Γ ⊢ t >: const K -> infer Γ t = some (const K)

  axiom infer_pi_sound {Γ : Map! ωTerm} {t A : ωTerm} {B : ωTerm 1}
    : infer_pi Γ t = some (A, B) -> Γ ⊢ t >: pi A B
  axiom infer_pi_complete {Γ : Map! ωTerm} {t A : ωTerm} {B : ωTerm 1}
    : Γ ⊢ t >: pi A B -> infer_pi Γ t = some (A, B)

  axiom check_sound {Γ : Map! ωTerm} {t A : ωTerm}
    : check Γ t A = some () -> Γ ⊢ t =: A
  axiom check_complete {Γ : Map! ωTerm} {t A : ωTerm}
    : Γ ⊢ t =: A -> check Γ t A = some ()

  axiom wf_sound {Γ : Map! ωTerm}
    : wf Γ = some () -> ⊢ Γ
  axiom wf_complete {Γ : Map! ωTerm}
    : ⊢ Γ -> wf Γ = some ()

end SystemFOmega
