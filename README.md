# cedille2-metatheory

phi needs to change:
    Phi is basically a function
        1. f : A -> (a : A) /\ P a and
        2. FV(|f|) = empty, such that
        3. f_eq : (a : A) -> a = (f a).1

this causes problems with relating it back to Cedille1 though, so we "crack open f"

    phi { a, b, e }
    FV(|a|) = { i } (i in context of course)
    FV(|b|) < FV(|a|) (should this also just be { i }?)
    FV(|e|) < FV(|b|)

    reduction:
    |a| = |b| -> phi { a, b, (refl -x) } -> b
    ^-------^ is this even needed?

if C |- t : a = b and FV (|t|) = empty then
    t ->* refl -x

if C |- refl -x =: a = b, then |a| = |b|
Proof:
    C |- refl -x : T, by inversion
    T becomes x = x
    now we have x = x === a = b
    holds only if x === a and x === b
    by transitivity a === b
    which means exists a', b' such that a -> a', b -> b' and |a'| = |b'|




