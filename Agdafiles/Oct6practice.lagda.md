```
{-# OPTIONS --safe --without-K #-}
module Oct6practice where
```

Below we are importing packages that give us the equality type in agda,
along with many convenient features. The equality type in agda is
given by `a ≡ b`, as we will see later.

```
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
```

## The equality type
Here we give our own definition of the (based) equality type in
agda. `Path {A} x : A \to Set` is actually a family of types, in this case indexed
over the elements of A. With the base point `x` as a parameter, we say that the only constuctor of this type is `refl : Path x x`. 

```
data Path {u} {A : Set u} (x : A) : A → Set u where 
    -- --  refl : Path x x 
```

From now on we will use the symbol `≡` typed like
"\==" or "\equiv".

What does this mean? It is complicated and will likely take a while to understand. The categorically inclined can take a look at [this section](https://hott.github.io/book/hott-online-82-g578b85c.pdf#section.5.8) of the book "Homotopy type theory." If that explaination doesn't help you, congratulations, you are normal! Try following/working through the examples below to get a better understanding of how path induction works.

## Path induction
In Rijke's textbook, he gives the type of based path induction to be this:

```
pathInd : {A : Set} {a : A} (motive : (x : A) → (p : a ≡ x) → Set) (base : motive a refl) → {b : A} → (p : a ≡ b) → motive b p
```

we define the function as follows:

```
pathInd motive base refl = base
```

What does this mean? When defining a function inductively, we only need to define where the constructors of the function are sent. **To define a function on paths between any two points, it suffices to show only where the identity element goes**. Why? Something about the yoneda lemma I guess? see the link above. It does *not* mean that all paths are the same as the identity path (or else homotopy type theory would be a silly thing to study).

Here is an example of proving something using path induction. We
have laabeled the motive and the base explicitly, but this is not
necessary.

```
leibnitz : {a b : Set} → (f : a → b) → (a a' : a) → a ≡ a' → f a ≡ f a'
leibnitz f a a' = pathInd motive base -- the `{a}` in curly braces is included only so that we can refer to it in the definition. it does not need to be provided when using the function `app`.
  where
    motive = (λ x _ → f a ≡ f x) -- this is the function that takes x and a proof that a≡x and returns the type f a ≡ f x
    base = refl -- this is a proof that f a ≡ f a. of course, this can be proved using reflexivity.
```


it is more common (and more convenient) in agda to write a function
that uses pattern matching on the constuctors of the type rather than
using a recursor like `pathind`. the function below is the same as
`leibnitz`, but uses pattern matching:

```
ap : {A B : Set} (f : A → B) → {a a' : A} → a ≡ a' → f a ≡ f a'
ap f {a} {a'} refl = ans -- The `refl` here refers to the type constructor of `Path`.
  where                -- It says, "assume that our element of `a ≡ a'` was constructed by `refl`. Because `refl: a ≡ a`, this presumes that `a` is definitionally equal to `a'`.
    ans = refl
    -- Because we assumed that our input was `refl`, we now
    -- need an element of `f a ≡ f a`. The obvious choice
    -- for this is `refl : f a ≡ f a`.
```

The fact that `refl` takes in no arguments is a consequence of us using the based equality type. Agda knows what the type of the goal is, so refl must match that type.


Note that pattern matching is ridiculously powerful. It is so powerful that it can make definitions illegible. See the following example, and try to figure out what the definitions actually say:

```
ex_concat : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
ex_concat refl refl = refl

ex_assoc : {A : Set} → {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
    → ex_concat (ex_concat p q) r ≡ ex_concat p (ex_concat q r)
ex_assoc refl refl refl = refl
```

Because of this, in this worksheet we will only use the function `pathInd` with a clearly defined motive and base.



## Let's try proving each of the following:

Transitivity:

```
infix 30 _⊚_
_⊚_ : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_⊚_ hxy hyz = {!!}
```

Symmetry:

```
inv : {A : Set} {x y : A} → x ≡ y → y ≡ x
inv hxy = {!!}
```

Associator

```
assoc : {A : Set} → {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
    → (p ⊚ q) ⊚ r ≡ p ⊚ (q ⊚ r)
assoc p q r = {!!}
```

Left unitor

```
left-unit : {A : Set} {x y : A} (p : x ≡ y) → refl ⊚ p ≡ p
left-unit hxy = {!!}
```

Right unitor

```
right-unit : {A : Set} {x y : A} (p : x ≡ y) → p ⊚ refl ≡ p
right-unit hxy = {!!}
```

Left inverse(or)

```
left-inv : {A : Set} {x y : A} (p : x ≡ y) → (inv p) ⊚ p ≡ refl
left-inv hxy = {!!}
```

Right inverse

```
right-inv : {A : Set} {x y : A} (p : x ≡ y ) → p ⊚ (inv p) ≡ refl
right-inv hxy = {!!}
```

Given the definition of the identity function `id`:

```
id : {A : Set} → A → A
id = λ x → x
```

A path `p : x ≡ y` is equivalent to the path `ap id p : id x ≡ id y`:

```
ap-id : {A : Set} {x y : A} (p : x ≡ y) → ( p ≡ ap id p )
ap-id hxy = {!!}
```

Note that the output is not of type `Path {A}`, but of type `Path {Path {A}}`.


Composition can be extracted as desired (first we define function composition with the notation `f∘g`):

```
_∘_ : {A B : Set} → {C : B → Set} → ((y : B) → C y) → (f : A → B) → ((x : A) → C (f x))
(g ∘ f ) x = g (f x)
infixr 30 _∘_


ap-comp : {A B C : Set} (f : A → B) → (g : B → C) → {x y : A} → (p : x ≡ y)
    → ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g hxy = {!!}
```

This one looks familliar... can you see how it is different from `ap-id`?

```
ap-inv : {A : Set} {x y : A} (p : x ≡ y) → inv p ≡ ap id (inv p)
ap-inv hxy = {!!}
```

How should the transport function be defined? this takes an equivalence between elements in a type and gives a map between types with those indices.

```
tr : {A : Set} {B : A → Set} {x y : A} → x ≡ y → B x → B y
tr hxy b = {!!}
```

Dependent application of a function behaves as expected:

```
apd : {A : Set} {B : A → Set} → (f : (x : A) → B x)
    → {x y : A} → (p : x ≡ y)
    → tr p (f x) ≡ f y
apd f hxy = {!!}

```


## Let's kick it up a notch!
These are the practice problems from chapter 5 of Rijke's textbook.

1. Show that the operation inverting identifications distributes over the
concatenation operation, i.e., construct the following:

```
dist-inv-concat : {A : Set} {x y z : A} (p : x ≡ y) → (q : y ≡ z) → ( inv (p ⊚ q) ≡ (inv q) ⊚ (inv p))
dist-inv-concat p q = {!!}
```

2. construct the following maps:

```
con-left : {A : Set} {w x y z : A} (p : x ≡ y) → (q : x ≡ y) → (r : w ≡ x) → (p ≡ q) → (r ⊚ p ≡ r ⊚ q)
con-left p q r hpr = {!!}

con-right : {A : Set} {w x y z : A} (p : w ≡ x) → (q : w ≡ x) → (r : x ≡ y) → (p ≡ q) → (p ⊚ r ≡ q ⊚ r)
con-right p q r hpr = {!!}


inv-con : {A : Set} {w x y z : A} (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) → (p ⊚ q ≡ r) →  q ≡ (inv p) ⊚ r
inv-con p q r hpqr = {!!}

con-inv : {A : Set} {w x y z : A} (p : x ≡ y) → (q : y ≡ z) → (r : x ≡ z) → (p ⊚ q ≡ r) →  p ≡ r ⊚ (inv q)
con-inv p q r hqpr = {!!}
```

4. Consider four identifications (a ≡ b ≡ c ≡ d ≡ e). Lets do a Mac Lane pentagon!
a. Construct the five identifications:

```
alpha1 : {A : Set} {a b c d e : A} (p :  a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) → (((p ⊚ q) ⊚ r) ⊚ s) ≡ ((p ⊚ (q ⊚ r)) ⊚ s)
alpha1  p q r s = ap right_s (assoc p q r) -- extra variables added for clarity, not required in proof
  where
    right_s = (λ x → x ⊚ s) 
alpha2 : {A : Set} {a b c d e : A} (p :  a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) → ((p ⊚ (q ⊚ r)) ⊚ s) ≡ (p ⊚ ((q ⊚ r) ⊚ s))
alpha2 p q r s = {!!}

alpha3 : {A : Set} {a b c d e : A} (p :  a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) → (p ⊚ ((q ⊚ r) ⊚ s)) ≡ (p ⊚ (q ⊚ (r ⊚ s)))
alpha3 p q r s = {!!}

alpha4 : {A : Set} {a b c d e : A} (p :  a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) → (((p ⊚ q) ⊚ r) ⊚ s) ≡ ((p ⊚ q) ⊚ (r ⊚ s))
alpha4 p q r s = {!!}

alpha5 : {A : Set} {a b c d e : A} (p :  a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) → ((p ⊚ q) ⊚ (r ⊚ s)) ≡ (p ⊚ (q ⊚ (r ⊚ s)))
alpha5 p q r s = {!!}
```


b. show the following:

```
macLane : {A : Set} {a b c d e : A} (p :  a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) → ((((alpha1 p q r s) ⊚ (alpha2 p q r s)) ⊚ (alpha3 p q r s)) ≡ ((alpha4 p q r s) ⊚ (alpha5 p q r s)))
macLane p q r s = {!!}
```

Try to prove this. what goes wrong? What error message does agda give you?

```
oops : {A : Set} {a b : A} (p q : a ≡ b) →(p ≡ q)
oops p q = {!!}
```
