# Simplicial HoTT reading group

This is a reading group website for studying simplicial homotopy type theory.

## About
We will learn about [a type theory for synthetic ∞-categories](https://arxiv.org/abs/1705.07442), called simplicial HoTT, reviewing basic type theory and ∞-category theory and following it by the more recent paper [Directed univalence in simplicial homotopy type theory](https://arxiv.org/abs/2407.09146).

## What's next?
We are going to read this paper ["Formalizing the ∞-Categorical Yoneda Lemma"](https://arxiv.org/abs/2309.08340).

### Caution
Even though I put this website public, the reading group is for Dalhousie University students and postdocs. Also, most of the materials are written throughout our learning process, so we make no guarantee that they are correct or complete. 

## Seminar notes 

- Sept 22: categorical semantics of MLTT. (Daniel)
- Sept 29: intro to HoTT, identity types, path induction. (Deni) [notes](seminarnotes/Sep29_Deni_HoTT_Identity_types_notes.pdf)
- Oct 06: HoTT in Agda workshop. (Jeremiah) [worksheet](agda/Oct6practice.lagda.md)
- Oct 13: Truncation levels, univalence. (Hayato) [notes](agda/Oct13.lagda.md)
- Oct 20: Quasicategories. (Tanner) [notes](seminarnotes/Oct20_Tanner_Type_Theory_Quasicategory_Presentation.pdf)



## Formalization

### Agda


### Rzk
[Rzk](https://rzk-lang.github.io/rzk/en/mkdocs-languages/) is a proof assistant designed specifically for simplicial HoTT.

A library for sHoTT can be found [here](https://rzk-lang.github.io/sHoTT/), part of which is simply about HoTT.

Rzk has an [in-browser playground](https://rzk-lang.github.io/rzk/v0.7.1/playground/), and when you put the raw URL link to the file in our repo, you can see it in your browser. 
For example, see this https://rzk-lang.github.io/rzk/playground/?snippet_url=https://raw.githubusercontent.com/hayatonasu/readinggroup_simplicialhott/refs/heads/main/Rzkfiles/test.rzk.md.

To get familiar with Rzk, we can play [this game](https://rzk-lang.github.io/warmup-game/)!
