{-# OPTIONS --safe --without-K #-}
module test where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Path {A : Set} : A → A → Set₁ where
  myRefl : (x : A) → Path {A} x x -- this is how equality is defined in agda. from now on we will use the symbol `≡` typed like "\==" or "\equiv".


data Σ (A : Set) (B : A → Set) : Set where
    pair : (a : A) → (b : B a) → Σ A B

first : {A : Set} → { B : A → Set} → Σ A B → A 
first (pair a b) = a 

second : {A : Set} → { B : A → Set} → (p : Σ A B ) → B (first p) 
second (pair a b) = b

identity : {A : Set} → A → A
identity {A} a = a

iscontr : (A : Set) → Set
iscontr A = Σ A (λ a → ((x : A) → a ≡ x) )

isprop : (A : Set) → Set
isprop A = (x y : A) → iscontr (x ≡ y)

isset : (A : Set) → Set
isset A = (x y : A) → isprop (x ≡ y)

pathInd : {A : Set} {a : A} (motive : (x : A) → (p : a ≡ x) → Set) (base : motive a refl) → {b : A} → (p : a ≡ b) → motive b p
pathInd motive base p = J motive p base


-- J : {A : Set a} {x : A} (B : (y : A) → x ≡ y → Set b)
--     {y : A} (p : x ≡ y) → B x refl → B y p
-- J B refl b = b -- This is how path induction is normally defined in agda.
-- I think the definition gave here is more intuitive

-- here is an example of proving something using path induction. We have laabeled the motive and the base explicitly, but this is not necessary.
app1 : {A B : Set} → (f : A → B) → (a a' : A) → a ≡ a' → f a ≡ f a'
app1 f a a' = pathInd motive base -- the `{a}` in curly braces is included only so that we can refer to it in the definition. It does not need to be provided when using the function `app`.
  where
    motive = (λ x _ → f a ≡ f x) -- this is the function that takes x and a proof that a≡x and returns the type f a ≡ f x
    base = refl -- this is a proof that f a ≡ f a. Of course, this can be proved using reflexivity.

-- It is more common (and more convenient) in agda to write a function that uses pattern matching on the constuctors of the type rather than using a recursor like `pathInd`. Here is an example of this:
app2 : {A B : Set} (f : A → B) → (a a' : A) → a ≡ a' → f a ≡ f a'
app2 f a a' refl = ans -- The `refl` here refers to the type constructor of `Path`.
  where                -- It says, "assume that our element of `a ≡ a'` was constructed by `refl`. Because `refl: a ≡ a`, this presumes that `a` is definitionally equal to `a'`.
    ans = refl -- Because we assumed that our input was `refl`, we now
               -- need an element of `f a ≡ f a`. The obvious choice
               -- for this is `refl : f a ≡ f a`.

-- The fact that `refl` takes in no arguments is a consequence of the
-- fact that the equality type is defined as the type of paths with one
-- based point, rather than the type of paths with *no* based point.






---- The following is what I borrowed from my old repository.


-- composition
-- _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
-- (g ∘ f ) x = g (f x)
-- infixr 30 _∘_

-- This is a slightly more complicated composition that allows `g` to be a dependent function.
_∘_ : {A B : Set} → {C : B → Set} → ((y : B) → C y) → (f : A → B) → ((x : A) → C (f x))
(g ∘ f ) x = g (f x)
infixr 30 _∘_

_∘d_ : ∀ {A : Set} {B : A → Set} {C : (x : A) → B x → Set} → ((x : A) → (y : B x) → C x y) → (f : (x : A) → B x) → ((x : A) → C x (f x))
(g ∘d f ) x = g x (f x)
infixr 30 _∘d_


∘≡∘d : ∀ {A B C : Set} (g : B → C) (f : A → B) → g ∘ f ≡  (λ x y → g y) ∘d f
∘≡∘d {A} {B} {C} f g = refl

id : {A : Set} → A → A 
id x = x

concat : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
concat refl q = q

inv : {A : Set} {x y : A} → x ≡ y → y ≡ x
inv refl = refl
    
assoc : {A : Set} → {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
    → concat (concat p q) r ≡ concat p (concat q r)
assoc refl q r = refl

left-unit : {A : Set} {x y : A} (p : x ≡ y) → concat refl p ≡ p
left-unit refl = refl

right-unit : {A : Set} {x y : A} (p : x ≡ y) → concat p refl ≡ p
right-unit refl = refl

left-inv : {A : Set} {x y : A} (p : x ≡ y) → concat (inv p) p ≡ refl
left-inv refl = refl

right-inv : {A : Set} {x y : A} (p : x ≡ y ) → concat p (inv p) ≡ refl
right-inv refl = refl

-- application
ap : {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

    
ap-id : {A : Set} {x y : A} (p : x ≡ y) → p ≡ ap (λ x → x) p
ap-id refl = refl

ap-comp : {A B C : Set} (f : A → B) → (g : B → C) → {x y : A} → (p : x ≡ y)
    → ap g (ap f p) ≡ ap (λ x → g (f x)) p
ap-comp f g refl = refl

ap-inv : {A : Set} {x y : A} (p : x ≡ y) → inv p ≡ ap (λ x → x) (inv p)
ap-inv refl = refl

-- transport
tr : {A : Set} {B : A → Set} {x y : A} → x ≡ y → B x → B y
tr refl b = b

-- dependent application
apd : {A : Set} {B : A → Set} → (f : (x : A) → B x)
    → {x y : A} → (p : x ≡ y)
    → tr p (f x) ≡ f y
apd f refl = refl

{-
-- we cannot show the following proposition under --without-K option
refl-uniq : {A : Set} {a : A} → (p : a ≡ a) → refl ≡ p
refl-uniq refl = refl
-}



