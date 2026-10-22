```agda
{-# OPTIONS --without-K --no-import-sorts #-}
module Oct13 where
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to Type ; Setω to Typeω ; Prop to ProofIrrelevantProp)
  public
```
(I imported the primitives with Set renamed with Type)

# October 13th: Notes

Acknowledgement: I used claude to resolve some errors and make the first version of two exercises (fundamental theorem, SIP for magmas) and I rewrote it manually.

## Review

We have learned path induction:

```agda
pathInd : {A : Type} {a : A} (motive : (x : A) → (p : a ≡ x) → Type) (base : motive a refl) → {b : A} → (p : a ≡ b) → motive b p
pathInd motive base refl = base
```

and that it automatically induces higher coherences.

### Preliminary

```agda
transpose : {l l' : Level} {A : Type l} {B : A → Type l'} → {a a' : A} → a ≡ a' → B a → B a' 
transpose {_} {_} {A} {B} {a} {a} refl = λ x → x

infixr 9 _∘_
_∘_ : {l l' l'' : Level} {A : Type l} {B : Type l'} {C : Type l''} → (B → C) → (A → B) → (A → C)
_∘_ {_} {_} {_} {A} {B} {C} g f x = g (f x)

id : {l : Level} {A : Type l} → A → A 
id x = x

infixr 8 _×_ 
_×_ : {l l' : Level} → Type l → Type l' → Type (l ⊔ l') 
_×_ A B = Σ A (λ x → B)

module _ {l} {A : Type l} where 
    concat' : {u v w : A} → u ≡ v → u ≡ w → v ≡ w 
    concat' {u} {u} {u} refl refl = refl
    -- concat' p q = p⁻¹ ⊙ q

    concat'-sym : {u v : A} → (p : u ≡ v) → concat' p p ≡ refl
    concat'-sym {u} {u} refl = refl

    functorial-concat' : {u : A} {H : (x : A) → u ≡ x} → (v w : A) → (p : v ≡ w) → concat' {u} {v} {w} (H v) (H w) ≡ p
    functorial-concat' {u} {H} v .v refl = concat'-sym (H v)
```

```agda
variable 
    l l' l'' : Level
```

## Overview of today's reading group

### Homotopy Type Theory
- Types are inherently spaces.    
- Propositions, sets, etc. are special kinds of types.      
- The univalence axiom (principle) is a powerful axiom that lets us treat equality the way many mathematicians use it unconsciously but informally. 
- In particular, [structure identity principle](https://ncatlab.org/nlab/show/structure+identity+principle) (HoTT Book § 9.8) is a corollary of this, which states *any correct notion of equivalence between mathematical objects should be characterized by the property that they are indistinguishable from structures depend on them*, or *any correct notion of equivalence between mathematical objects should be equivalent to equality*.

### Simplicial Homotopy Type Theory
- Types are inherently simplicial spaces.
- Segal spaces (precategories), (univalent=Rezk complete) categories are special kinds of types.
- The directed version of the univalence axiom is the main idea of the paper we are aiming to read: http://arxiv.org/abs/2407.09146.
- It should imply something analogous to structure identity principle, called [structure homomorphism principle](https://ncatlab.org/nlab/show/structure+homomorphism+principle). This states that *any correct notion of morphisms between mathematical objects should be equivalent to directed equality*.

### Today's goal
Run through the basic concepts of Homotoppy Type Theory to prepare ourselves for the paper.

- Understanding homotopy levels (contractible types, propositions, Types)
- Understanding the univalance axiom, why it's important? (The structure identity principle)

## Contractible types, propositions, and sets as special types

We do not know whether two proofs of equalities `a ≡ b` for `a  b: A` are the same, because `A` is not a set, it's a (homotopy) type, or an ∞-groupoid.
However, some types are sets, and it is a property for a type to be a set.

### Contractible types
    HoTT Book § 3.11, Rijke's book § 10

```agda
record is-contr (A : Type l) : Type l where
    constructor _,_
    field 
        center : A 
        contraction : (x : A) → center ≡ x
open is-contr
```

I used [`record`](https://agda.readthedocs.io/en/latest/language/record-types.html), but this is the same thing as 
```agda
-- is-contr : (A : Type l) → Type l 
-- is-contr A = Σ A (λ a → (x : A) → a ≡ x)

-- center : {A : Type l} → ...
```
In theory, this would be better if you prove many things about Σ-types and want to apply them also to `is-contr`.
I decided to use `record` for readablity.

A good example is the type of all paths from a fixed element. 
(cf. the coYoneda `∫ᶜ C(x,c) ≅ 1`.)

```agda
is-contr-based-path : (A : Type l) → (a : A) → is-contr (Σ A (λ x → a ≡ x))
center (is-contr-based-path A a) = (a , refl)
contraction (is-contr-based-path A a) = contraction-based-path
    where 
    contraction-based-path : (t :  Σ A (λ x → a ≡ x)) → (a , refl) ≡ t 
    contraction-based-path (x , refl) = refl
    
```

In fact, this characterizes the path type up to equivalence (see the fundamental theorem).

### Propositions
    HoTT Book § 3.2 - 3.6, Rijke's book  § 12.1, 12.2

A propostion is a type such that if it has an element, it is contractible.
We define  `is-prop` by the following form that is the easiest form to check.
```agda
is-prop : Type l → Type l
is-prop A = (a b : A) → a ≡ b

Prop : (l : Level) → Type (lsuc l) 
Prop l = Σ (Type l) (λ A → is-prop A)
``` 

Moral: if any two elements must be the same, any element becomes a center of contraction.

There are alternative definitions of being a proposition, which will turn out to be equivalent.

```agda
is--1-type : Type l → Type l
is--1-type A = (a b : A) → is-contr (a ≡ b)

is-prop' : Type l → Type l
is-prop' A = A → is-contr A 
```

#### Exercise --- Equivalences of different definitions of propositions 
([Copatterns](https://agda.readthedocs.io/en/latest/language/copatterns.html) are useful when you define a function *into* an record type, not *from* one. You can do this by `Ctrl+c Ctrl+c` and press `Enter` without entering a variable.)

```agda
module _ {A : Type l} where 

    is-prop'←is--1-type :  is--1-type A → is-prop' A
    center (is-prop'←is--1-type H x) = x
    contraction (is-prop'←is--1-type H x) y = center (H x y)
        
    is--1-type←is-prop' : is-prop' A → is--1-type A 
    center (is--1-type←is-prop' H x y) = concat' (contraction (H x) x) (contraction (H x) y)
    contraction (is--1-type←is-prop' H x x) refl = concat'-sym (contraction (H x) x)

    is-prop←is--1-type : is--1-type A → is-prop A 
    is-prop←is--1-type H a b =  center (H a b) 

    is--1-type←is-prop : is-prop A → is--1-type A 
    center (is--1-type←is-prop H a b) = concat' (H a a) (H a b)
--  wrong: center (is--1-type←is-prop H a b) = H a b
    contraction (is--1-type←is-prop H a a) refl = concat'-sym (H a a) 
```  

### Sets 
A set is a type that for each pair of elements `(a , b)`, the identity type `a ≡ b` is a proposition.

```agda
is-set : Type l → Type l 
is-set A = (a b : A) → is-prop (a ≡ b)

Set : (l : Level) → Type (lsuc l) 
Set l = Σ (Type l) (λ A → is-set A)

⟨_⟩ : Set l → Type l 
⟨_⟩ A = fst A
```

### k-truncated types 

More generally, we can inductively define k-truncated types as follows.

```agda
-- data ℕ : Type where
--         zero : ℕ
--         succ : ℕ → ℕ

data 𝕋 : Type where
        -2-𝕋 : 𝕋
        succ-𝕋 : 𝕋 → 𝕋

-1-𝕋 : 𝕋
-1-𝕋 = succ-𝕋 -2-𝕋

0-𝕋 : 𝕋
0-𝕋 = succ-𝕋 -1-𝕋

is-trunc : (k : 𝕋) → Type l → Type l 
is-trunc -2-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (a b : A) → is-trunc k (a ≡ b)

-- is--1-type : Type l → Type l
-- is--1-type A = is-trunc -1-𝕋 A 

Truncated-Type : {l : Level} (k : 𝕋) → Type (lsuc l)
Truncated-Type {l} k = Σ (Type l) (λ A → is-trunc k A)
```

Contractible types are propostions (-1-types).

```agda
is--1-type-is-contr : {A : Type l} → is-contr A → is--1-type A
is--1-type-is-contr {_} {A} is-contr-A = is--1-type←is-prop' (λ x → is-contr-A)

is-prop-is-contr : {A : Type l} → is-contr A → is-prop A
is-prop-is-contr = is-prop←is--1-type ∘ is--1-type-is-contr 
``` 

Similarly, any k-type is a (k+1)-type, so we have a chain of subtypes `ContrType ⊆ Prop ⊆ Set ⊆ ⋯` of ` Type`.

```agda
is-suc-k-type-is-k-type : {k : 𝕋} → {A : Type l} → is-trunc k A → is-trunc (succ-𝕋 k) A 
is-suc-k-type-is-k-type {_} { -2-𝕋} {A} = is--1-type-is-contr
is-suc-k-type-is-k-type {_} {succ-𝕋 k} {A} H a b = is-suc-k-type-is-k-type (H a b)
```

## Homotopy and equivalence

### Homotopy 
```agda
infix 6 _~_
_~_ : {A : Type l} {B : A → Type l'} → (f g : (x : A) → B x) → Type (l ⊔ l') 
_~_ {_} {_} {A} {_} f g = (x : A) → f x ≡ g x
```

This makes `Type` a (∞,1)-category.
```agda
refl-homotopy : {A : Type l} {B : A → Type l'} → (f : (x : A) → B x) → f ~ f 
refl-homotopy f = λ x → refl
```

### Equivalence (HoTT Book Chapter 4, Rijke's textbook §9)
An equivalence is one of the correct notions of sameness between types.

```agda
record has-section {A : Type l} {B : Type l'} (f : A → B) : Type (l ⊔ l') where 
    field
        section : B → A 
        proof-section : f ∘ section ~ id
open has-section 

record has-retraction {A : Type l} {B : Type l'} (f : A → B) : Type (l ⊔ l') where 
    field
        retraction : B → A 
        proof-retraction : retraction ∘ f ~ id
open has-retraction 

is-equiv : {A : Type l} {B : Type l'} (f : A → B) → Type (l ⊔ l') 
is-equiv f = has-section f × has-retraction f

infix 3 _≃_
_≃_ : (A : Type l) (B : Type l') → Type (l ⊔ l') 
_≃_ A B = Σ (A → B) (λ f → is-equiv f)
```

#### Exercise --- ≃ is an equivalence relation 
```agda
refl-≃ : (A : Type l) → A ≃ A 
refl-≃ A = {!   !}

sym-≃ : {A B : Type l} → A ≃ B → B ≃ A 
sym-≃ = {!   !}

trans-≃ : {A B C : Type l} → A ≃ B → B ≃ C → A ≃ C 
trans-≃ = {!   !}
```

#### Remark --- having an inverse is not the right notion!
One could define an inverse of a function as follows.
```agda
has-inverse : ∀ {A B : Type (lsuc l)} (f : A → B) → Type (lsuc l) 
has-inverse {_} {A} {B} f = Σ (B → A) (λ f^-1 → (f ∘ f^-1 ~ id) × (f^-1 ∘ f ~ id))
```

However, this is not equivlaent to `is-equiv` (even with the univalence axiom), only logically equivalent.

Two types are called *logically equivalent* if there are functions between them in both directions.

```agda
_↔_ : (A : Type l) (B : Type l') → Type (l ⊔ l') 
_↔_ A B = (A → B) × (B → A)
```

This notion of equivalence is much weaker than equivalence of types, but sufficent for (in fact, equivalent to) equivalences between propositions.

1. We have a term of `is-equiv f ↔ has-inverse f`, but not `is-equiv f ≃ has-inverse f`. 
2. `is-equiv f` is a proposition, while `has-inverse f` is not.

#### Exercise --- `is-equiv f` is a proposition 
```agda
module _ (A B : Type l) (f : A → B) where 
    is--1-type-has-section : is--1-type (has-section f)
    is--1-type-has-section = {!   !}
```

### Contractible maps 
Another equivalent definition is 
```agda
record Fib {A : Type l} {B : Type l'} (f : A → B) (b : B) : Type (l ⊔ l') where 
    field 
        fiber : A 
        proof-fiber : f fiber ≡ b 
open Fib 

is-contr-map : {A : Type l} {B : Type l'} (f : A → B) → Type (l ⊔ l') 
is-contr-map {B = B} f = (y : B) → is-contr (Fib f y)
```

```agda
module _ {A B : Type l} (f : A → B) where

    is-contr-map-is-equiv : is-equiv f → is-contr-map f 
    is-contr-map-is-equiv = {!   !}

    is-equiv-is-contr-map : is-contr-map f → is-equiv f
    is-equiv-is-contr-map = {!   !}

```

#### Exercise --- The fundamental theorem of path types (Rijke's book § 11) 
For a family `x : A ⊢ B x` with a family of maps `f : (x : A) → a ≡ x → B x`, every `f x` is an equivalence if the total space `Σ A B` is contractible.
This is a characterization of path types: `is-contr-based-path` says that `Σ A (λ x → a ≡ x)` is contractible.

```agda
module _ {A : Type l} {B : A → Type l'} where

    -- the map induced on total spaces
    tot : {C : A → Type l''} → ((x : A) → B x → C x) → Σ A B → Σ A C
    tot f (x , b) = (x , f x b)

    -- any map between contractible types is an equivalence
    is-equiv-is-contr : {X : Type l} {Y : Type l'} (g : X → Y) → is-contr X → is-contr Y → is-equiv g
    is-equiv-is-contr = {!   !}

    -- a family of maps is a family of equivalences iff the total map is an equivalence
    is-fiberwise-equiv-is-equiv-tot : {C : A → Type l''} (f : (x : A) → B x → C x)
        → is-equiv (tot f) → (x : A) → is-equiv (f x)
    is-fiberwise-equiv-is-equiv-tot = {!   !}

fundamental-theorem-id : {A : Type l} {B : A → Type l'} (a : A) (f : (x : A) → a ≡ x → B x)
    → is-contr (Σ A B) → (x : A) → is-equiv (f x)
fundamental-theorem-id = {!   !}
```


## The univalence principle 

### Function extensionality

In category theoretic terms, a proposition is called *a property* as opposed to *a structure*.
When we use `is-***`, we mean that the type `is-*** A` is actually a propostion (≃ a property).
Suppose we want to prove a given type, which is often constructed with function types and other constructors, is a proposition.
Then, we need to prove two elements, say two functions, are equal.
Proving that two functions are equal is hardly possible without *the function extentionality* axiom.

```agda
eval-apply : {A : Type l} {B : A → Type l'} (f g : (x : A) → B x) → f ≡ g → f ~ g
eval-apply f .f refl x = refl 

FunExt : {l l' : Level} → {A : Type l} → {B : A → Type l'} → Type (l ⊔ l')
FunExt {_} {_} {A} {B} = (f g : (x : A) → B x) → is-equiv (eval-apply f g)

postulate
    funext : {A : Type l} {B : A → Type l'} → FunExt {_} {_} {A} {B}

inv-funext : {A : Type l} {B : A → Type l'} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g 
inv-funext f g = section (fst (funext f g))

WeakFunExt : {A : Type l} → {B : A → Type l'} → Type (l ⊔ l')
WeakFunExt {_} {_} {A} {B} = ((x : A) → is-contr (B x)) → is-contr ( (x : A) → B x)

weakfunext : {A : Type l} → {B : A → Type l'} → WeakFunExt {l} {l'} {A} {B}
center (weakfunext {_} {_} {A} {B} H) = λ x → center (H x)
contraction (weakfunext {_} {_} {A} {B} H) f = (inv-funext (λ x → center (H x)) f) (λ x → contraction (H x) (f x))
```


#### Exercise --- examples of usage of the function extentionality

0. If `x : A ⊢ P x` is a proposition, `(x : A) → P x` is also a proposition.
```agda
is-prop-function : {A : Type l} → {P : A → Type l'} → ((x : A) → is-prop (P x)) → is-prop ((x : A) → P x)
is-prop-function H f g = (inv-funext f g) (λ x → H x (f x) (g x))
```

More generally, k-types are closed under function type: `A : Type` and ` x : A ⊢ B (x) : k-Type` ⇒ `Π A (λ x → B (x)) : k-Type`.

```agda
is-k-type-function-into-k-type : {A : Type l} → {B : A → Type l'} (k : 𝕋) → ((x : A) → is-trunc k (B x)) → is-trunc k ( (x : A) → B x)
is-k-type-function-into-k-type -2-𝕋 = weakfunext
is-k-type-function-into-k-type (succ-𝕋 k) h f g = {!   !}
```

1. `is-contr` is a propery.
```agda
is-property-is-contr : {A : Type l} → is-prop (is-contr A) 
is-property-is-contr {l} {A} (c , H) (d , K) = component-wise-equality-is-contr c d H K {!   !} {!   !}
    where 
    component-wise-equality-is-contr : {A : Type l} (c d : A) (H : (x : A) → c ≡ x) (K : (x : A) → d ≡ x) → (p : c ≡ d) → (transpose {B = (λ z → (x : A) → z ≡ x)} p H ≡ K) → (record {center = c; contraction = H} ≡ record {center = d; contraction = K} )
    component-wise-equality-is-contr c .c H .H refl refl = refl
```

More generally, `is-trunc k` is a property.
```agda
is-property-is-trunc-k : {k : 𝕋} {A : Type l} → is-prop (is-trunc k A)
is-property-is-trunc-k {k} {A} = {!   !}
```

2. If `x : A ⊢ P x` is a property and `A` is a (k+1)-type, then `Σ A (λ x → P x)` is a (k+1)-type. (This is false when k+1 is -2.)
Such a type is called a subtype of `A`.
```agda
is-trunc-subtype :  {A : Type l} {P : A → Type l'} {k : 𝕋} → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (Σ A (λ x → P x))
is-trunc-subtype {_} {_} {A} {P} { -2-𝕋} = {!   !}
is-trunc-subtype {_} {_} {A} {P} {succ-𝕋 k} = {!   !}

```

The above properties imply that most of the `is-***`'s in the file are propositions.
```agda
is-property-has-section : {A B : Type l} {f : A → B} → is-prop (has-section f)
is-property-has-section {A} {B} {f} = {!   !}
```


3. `is-prop` is a property

```agda
-- This one does not require the function extensionality.
is-set-is-prop : {A : Type l} → is-prop A → is-set A
is-set-is-prop {_} {A} H a b = is-prop-is-contr (center-of-path a b , contraction-of-path a b)
    where 
    center-of-path : (x y : A) → x ≡ y
    center-of-path x y = concat' (H a x) (H a y)
    contraction-of-path : (x y : A) →  (p : x ≡ y) → center-of-path x y ≡ p
    contraction-of-path x y p = functorial-concat' x y p 

is-property-is-prop : {A : Type l} → is-prop (is-prop A)
is-property-is-prop {_} {A} H K = (inv-funext H K) (λ x → (inv-funext (H x) (K x)) (homotopy x))
    where 
    homotopy : (x y : A) → H x y ≡ K x y
    homotopy x y = is-set-is-prop H x y (H x y) (K x y)
```

Since `is-prop'` and `is--1-type` are propositions as well, all of them are truly equivalent, not just logically equivalent.

### The univalance axiom 
Supose we define a mathematical structure, say magmas.

```agda
record Magma (l : Level) : Type (lsuc l) where 
    field 
        carrier : Type l 
        is-set-carrier : is-set carrier
        _*_ : carrier → carrier → carrier 
open Magma
```

Then, one would define morphisms between them. 

```agda
record Hom-Magma {l : Level} (X Y : Magma l) : Type l where
    private 
        module X = Magma X
        module Y = Magma Y
    field 
        carrier-map : X.carrier → Y.carrier
        pres-* : {a b : X.carrier } → (carrier-map a) Y.* (carrier-map b) ≡ carrier-map (a X.* b)
open Hom-Magma
```

That gives us the notion of isomorphisms.
```agda
record _≅_ {l : Level} (X Y : Magma l) : Type l where
    field 
        forward : Hom-Magma X Y 
        backward : Hom-Magma Y X
    private 
        module f = Hom-Magma forward 
        module g = Hom-Magma backward
    field 
        back-and-forth : f.carrier-map ∘ g.carrier-map ~ id 
        forth-and-back : g.carrier-map ∘ f.carrier-map ~ id 
open _≅_
```

When `A ≅ B` and `p : P A` for ` X : Magma ⊢ P X`, a mathematician expects `p' : P B` to exist.
One can prove this by tedious calculation of course, but it would be much easier if `A ≅ B` were literally an equality between two magmas. 
The identification of `A = B` and `A ≅ B` (or `A ≃ B`) is everyday practice in mathematics. 

This is basically what the structure identity principle means: 
> identity of structured types is equivalent to structure-preserving equivalence (HoTT Book)

We ask the universe of types to admit this kind of identification.
```agda
equiv←eq : {A B : Type l} → A ≡ B → A ≃ B
equiv←eq {_} {A} {.A} refl = refl-≃ A

is-univ-univ : (l : Level) → Type (lsuc l)
is-univ-univ l = (A B : Type l) → is-equiv (equiv←eq {A = A} {B = B})

postulate 
    univ-axiom : {l : Level} → is-univ-univ l
```

The univalence axiom implies the function extensionality.

#### Exercise --- SIP for magmas 
One useful template to prove SIP is the following.

1. Every magma is isomorphic to itself, so path induction gives a map from paths to isomorphisms.
```agda
id-Hom-Magma : (X : Magma l) → Hom-Magma X X
id-Hom-Magma X = {!   !}

id-≅ : (X : Magma l) → X ≅ X
id-≅ X = {!   !}

≅←eq : {X Y : Magma l} → X ≡ Y → X ≅ Y
≅←eq {_} {X} {.X} refl = id-≅ X
```

2. Apply the fundamental theorem of identity.
It remains to show that the total space of `≅` is contractible.
This is where the univalence axiom (and the function extensionality) is used.

```agda
module _ {l : Level} where

    is-contr-total-≅ : (X : Magma l) → is-contr (Σ (Magma l) (λ Y → X ≅ Y))
    is-contr-total-≅ X = {!   !}

    SIP-Magma : (X Y : Magma l) → is-equiv (≅←eq {X = X} {Y = Y})
    SIP-Magma X Y = fundamental-theorem-id X (λ Y → ≅←eq {X = X} {Y = Y}) (is-contr-total-≅ X) Y
```
