```
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

## Review

We have learned path induction:

```
pathInd : {A : Type} {a : A} (motive : (x : A) → (p : a ≡ x) → Type) (base : motive a refl) → {b : A} → (p : a ≡ b) → motive b p
pathInd motive base refl = base
```

and that it automatically induces higher coherences.

``` 
-- transpose : {l l' : Level} {A : Type l} {B : A → Type l'} → {a a' : A} → a ≡ a' → B a → B a' 
-- transpose {_} {_} {A} {B} {a} {a} refl = λ x → x
```

## Overview of today's reading group



## Today's goal

- Understanding homotopy levels (contractible types, propositions, Types)
- Understanding the univalance axiom, why it's important? (The structure identity principle)

## Contractibles, propositions, sets as some types

We do not know if two proofs of equalities `a ≡ b` for `a  b: A` are the same, because `A` is not a set, it's a (homotopy) type, or an ∞-groupoid.
However, some types are sets, and it is a property for a type to be a set.

### Contractible types
```
record is-contr {l : Level} (A : Type l) : Type l where
    field 
        center : A 
        contraction : (x : A) → center ≡ x
open is-contr
```

I used `record`, but this is the same thing as 
```
-- is-contractible : (A : Type) → Type 
-- is-contractible A = Σ A (λ a → (x : A) → a ≡ x)
```

A good example is the type of all paths from a fixed element. 
(cf. the coYoneda `∫ᶜ C(x,c) ≅ 1`.)

```
is-contr-based-path : {l : Level} (A : Type l) → (a : A) → is-contr (Σ A (λ x → a ≡ x))
is-contr-based-path A a = record { center = {!   !} ; contraction = {!   !} }
    -- where 
    -- contraction-based-path : (t :  Σ A (λ x → a ≡ x)) → (a , refl) ≡ t 
    -- contraction-based-path t = ?
```

### truncation levels

We inductively define k-truncated types as follows.

``` 
data 𝕋 : Type where
        -2-𝕋 : 𝕋
        succ-𝕋 : 𝕋 → 𝕋

-1-𝕋 : 𝕋
-1-𝕋 = succ-𝕋 -2-𝕋

0-𝕋 : 𝕋
0-𝕋 = succ-𝕋 -1-𝕋
```

### k-truncated types 
```
is-trunc : {l : Level} (k : 𝕋) → Type l → Type l 
is-trunc -2-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (a b : A) → is-trunc k (a ≡ b)

is-prop : {l : Level} → Type l → Type l
is-prop A = is-trunc -1-𝕋 A 

is-set : {l : Level} → Type l → Type l
is-set A = is-trunc 0-𝕋 A 

Truncated-Type : {l : Level} (k : 𝕋) → Type (lsuc l)
Truncated-Type {l} k = Σ (Type l) (λ A → is-trunc k A)

Prop : {l : Level} → Type (lsuc l) 
Prop = Truncated-Type -1-𝕋

Set : {l : Level} → Type (lsuc l) 
Set {l} = Truncated-Type 0-𝕋
```

There are alternative definitions of being a proposition, which will turn out to be equivalent.
``` 
is-prop' : {l : Level} → Type l → Type l
is-prop' A = A → is-contr A 

is-prop'' : {l : Level} → Type l → Type l
is-prop'' A = (a b : A) → a ≡ b
```

### Equivalences of different definitions of propositions 
``` 
is-prop'←is-prop : {l : Level} → {A : Type l} → is-prop A → is-prop' A
is-prop'←is-prop {_} {A} is-prop-A x = record { 
    center = x ; 
    contraction = is-prop'←is-prop-contraction}
    where 
    is-prop'←is-prop-contraction : (a : A) → x ≡ a
    is-prop'←is-prop-contraction a = center (is-prop-A x a)
    

is-prop←is-prop' : {l : Level} → {A : Type l} → is-prop' A → is-prop A 
is-prop←is-prop' {_} {A} is-prop'-A x y = record { 
    center = concat' (contraction-from-a x) (contraction-from-a y) ;
    contraction = is-prop←is-prop'-contraction y}
    where 
        concat' : {u v w : A} → u ≡ v → u ≡ w → v ≡ w 
        concat' {u} {u} {u} refl refl = refl
        
        concat'-sym : {u v : A} → (p : u ≡ v) → concat' p p ≡ refl
        concat'-sym {u} {u} refl = refl

        is-contr-A : is-contr A
        is-contr-A = is-prop'-A x

        a = center is-contr-A

        contraction-from-a = contraction is-contr-A

        is-prop←is-prop'-contraction : (z : A) → (p : x ≡ z) → concat' (contraction-from-a x) (contraction-from-a z) ≡ p
        is-prop←is-prop'-contraction z refl = concat'-sym (contraction is-contr-A z)
```  

Contractible types are propostions.

``` 
is-prop-is-contr : {l : Level} → {A : Type l} → is-contr A → is-prop A
is-prop-is-contr {_} {A} is-contr-A = is-prop←is-prop' (λ x → is-contr-A)
``` 

Similarly, any k-type is a (k+1)-type, so we have a chain of subtypes `ContrType ⊆ Prop ⊆ Set ⊆ ⋯` of ` Type`.

```
is-suc-k-type-is-k-type : {l : Level} → {k : 𝕋} → {A : Type l} → is-trunc k A → is-trunc (succ-𝕋 k) A 
is-suc-k-type-is-k-type {_} {k} {A} = {!   !}
```

### Contractible maps 
``` 
record Fib {l : Level} {A B : Type l} (f : A → B) (b : B) : Type l where 
    field 
        fiber : A 
        wit-fiber : f fiber ≡ b 
open Fib 

is-contr-map : {l : Level} {A B : Type l} (f : A → B) → Type l 
is-contr-map {_} {_} {B} f = (y : B) → is-contr (Fib f y)
```

### Function extensionality

Some important properties require *the function extentionality* axiom.

``` 
-- FunExt : {l l' : Level} → {A : Type l} → {B : A → Type l'} → Type (l ⊔ l')
-- FunExt {_} {_} {A} {B} = (f g : (x : A) → B x) → 

WeakFunExt : {l l' : Level} → {A : Type l} → {B : A → Type l'} → Type (l ⊔ l')
WeakFunExt {_} {_} {A} {B} = ((x : A) → is-contr (B x)) → is-contr ( (x : A) → B x)

postulate
    weakfunext : {l l' : Level} {A : Type l} {B : A → Type l'} → WeakFunExt {l} {l'} {A} {B}
```

### Some properties on truncated types

1. 

2. k-types are closed under function type: `A : Type` and ` x : A ⊢ B (x) : k-Type` ⇒ `Π A (λ x → B (x)) : k-Type`.

``` 
is-k-type-function-into-k-type : {l l' : Level} → {A : Type l} → {B : A → Type l'} (k : 𝕋) → ((x : A) → is-trunc k (B x)) → is-trunc k ( (x : A) → B x)
is-k-type-function-into-k-type -2-𝕋 = weakfunext
is-k-type-function-into-k-type (succ-𝕋 k) h f g = {!   !}
```

3. Being a k-type is a proposition. (That's why I say "being a k-type", not "structure of k-type").


