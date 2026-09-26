{-# OPTIONS --safe --without-K #-}
module test where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- composition
-- _∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
-- (g ∘ f ) x = g (f x)
-- infixr 30 _∘_

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

data Σ (A : Set) (B : A → Set) : Set where
    pair : (a : A) → (b : B a) → Σ A B

witΣ : {A : Set} → { B : A → Set} → Σ A B → A 
witΣ (pair a b) = a 

prfwitΣ : {A : Set} → { B : A → Set} → (p : Σ A B ) → B (witΣ p) 
prfwitΣ (pair a b) = b

cont : {A : Set} {a : A} → (y : Σ A (λ x → a ≡ x)) → pair a refl ≡ y
cont (pair a refl) = refl

dist-inv-conc : {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z ) → (inv (concat p q )) ≡ (concat (inv q) (inv p))
dist-inv-conc refl refl = refl

-- coproduct type
data _⊔_ (A : Set) (B : Set) : Set where
    inl : A → A ⊔ B
    inr : B → A ⊔ B

copair : {A B X : Set} → (A → X) → (B → X) → (A ⊔ B → X)
copair f g (inl a) = f a
copair f g (inr b) = g b