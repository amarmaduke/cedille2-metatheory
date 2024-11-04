
import Common

namespace Fomega

  abbrev Ctx := List Term

  namespace Ctx

    def apply : Subst Term -> Ctx -> Ctx
    | _, [] => []
    | σ, .cons h t => .cons ([σ]h) (apply ^σ t)

    def beta : Ctx -> Term -> Ctx
    | s, t => apply ((.replace t) :: (r#I)) s

  end Ctx

end Fomega

notation:90 "[" σ "]" t:89 => Fomega.Ctx.apply σ t
notation:90 s:90 "β[" t "]" => Fomega.Ctx.beta s t
