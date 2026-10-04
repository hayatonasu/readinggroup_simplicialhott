{-# OPTIONS --safe --without-K #-}
module Oct6practice where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


data Path {A : Set} (x : A) : A → Set₁ where -- this is how equality is defined in agda. from now on we will use the symbol `≡` typed like "\==" or "\equiv".
     myRefl : Path {A} x x -- this says the only constuctor of this type is an element of `x ≡ x`. We'll see what this gives us later on.

pathInd : {A : Set} {a : A} (motive : (x : A) → (p : a ≡ x) → Set) (base : motive a refl) → {b : A} → (p : a ≡ b) → motive b p
pathInd motive base p = J motive p base

-- J : {A : Set a} {x : A} (B : (y : A) → x ≡ y → Set b)
--     {y : A} (p : x ≡ y) → B x refl → B y p
-- J B refl b = b -- This is how path induction is normally defined in agda.
-- I think the definition given here is more intuitive.

-- Here is an example of proving something using path induction. We
-- have laabeled the motive and the base explicitly, but this is not
-- necessary.
leibnitz : {A B : Set} → (f : A → B) → (a a' : A) → a ≡ a' → f a ≡ f a'
leibnitz f a a' = pathInd motive base -- the `{a}` in curly braces is included only so that we can refer to it in the definition.
                                      --It does not need to be provided when using the function `app`.
  where
    motive = (λ x _ → f a ≡ f x) -- this is the function that takes x and a proof that a≡x and returns the type f a ≡ f x
    base = refl -- this is a proof that f a ≡ f a. Of course, this can be proved using reflexivity.


-- It is more common (and more convenient) in agda to write a function
-- that uses pattern matching on the constuctors of the type rather
-- than using a recursor like `pathInd`. The function below is the
-- same as `leibnitz`, but uses pattern matching:
app : {A B : Set} (f : A → B) → (a a' : A) → a ≡ a' → f a ≡ f a'
app f a a' refl = ans -- The `refl` here refers to the type constructor of `Path`.
  where                -- It says, "assume that our element of `a ≡ a'` was constructed by `refl`.
                       -- Because `refl: a ≡ a`, this presumes that `a` is definitionally equal to `a'`.
    ans = refl -- Because we assumed that our input was `refl`, we now
               -- need an element of `f a ≡ f a`. The obvious choice
               -- for this is `refl : f a ≡ f a`.

-- The fact that `refl` takes in no arguments is a consequence of the
-- fact that the equality type is defined as the type of paths with one
-- based point, rather than the type of paths with *no* based point.

-- Insert a bunch of practice questions here:
