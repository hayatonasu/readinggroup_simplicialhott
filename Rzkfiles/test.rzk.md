# Sample literate Rzk markdown

```rzk
#lang rzk-1
#define id (A : U)
  : A → A
  := \ x → x
```

A is contractible there exists x : A such that for any y : A we have x = y.

```rzk
#def iscontr (A : U)
  : U
  := Σ (a : A) , (x : A) → a =_{A} x
```
-- A is a proposition if for any x, y : A we have x = y
```rzk
#def isaprop (A : U)
  : U
  := (x : A) → (y : A) → x =_{A} y
```

A is a set if for any x, y : A the type x =_{A} y is a proposition

```rzk
#def isaset (A : U)
  : U
  := (x : A) → (y : A) → isaprop (x =_{A} y)
```

```rzk
#def isagroupoid (A : U)
  : U
  := (x : A) → (y : A) → isaset (x =_{A} y)
```

```rzk
#def app (A B : U) (f : A → B) (a a' : A)
  : (a = a') → (f a = f a')
  := \ p → idJ (A , a , \ x _ → f a = f x , refl , a' , p)
```
