


-- u === v if ∃ u', v'. u -β>* u' and v -β>* v' and |u'| =α= |v'|

-- want something like `f`
-- `f` : A -> A ∩ B, extensionally the identity
-- for any situation have this ^, construct a function that behaves like the identity (on objects)
-- but its not clear how to define it, especially |`f`|??
-- introduce φ

-- (φ a b c : A ∩ B)
-- (a : A) is the cached input
-- (b : A ∩ B) is the "proof-version" of the definition
-- (c : a =A b.1) is the proof its extensionally the identity ((f a).1 = b)
-- |φ a b c| = |a|
-- in "proof-land" you reduce `b`, but in "object-land" you only consider `a`
-- φ a b (refl x) -β> b (if this happens, |a| =β= |b|)

-- the things convertible with phi to be convertible in both objects and proofs
-- u === v <-> |u| =β= |v| (consider when u, and v have φ somewhere in the term)
-- 1. u === v -> |u| =β= |v|
-- 2. |u| =β= |v| -> u === v
-- worry the proof of equality (c) is some False thing

-- |[t, s; T]| = |t|, (to construct a dependent intersection t === s)

-- ... middle of some computation ... (where `i` is a free variable)
-- (φ (λ x:A. i + x) (λ x:B. w) c).2 @ t
-- erased: (λ x. |i + x|) @ |t|

-- |φ a b c| = |φ a|

-- add rule to φ conversion, φ t =φ= t, where t a term
-- possibility: =φ= is t -φ> t' and s -φ> s' and |t'| =α= |s'|
-- u === v if ∃ u', v'. u -β>* u' and v -β>* v' and |u'| =φ= |v'|



