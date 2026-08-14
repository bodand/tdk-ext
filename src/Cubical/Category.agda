{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Category where

open import Cubical.Foundations.Prelude

record Category (o ℓ : Level) : Type (ℓ-suc (ℓ-max o ℓ)) where
   infixr 40 _∘_

   field
      Ob  : Type o
      Hom : Ob → Ob → Type ℓ

      isSetHom : {A B : Ob} → isSet (Hom A B)

      id : {A : Ob} → Hom A A
      _∘_ : {A B C : Ob} → Hom B C → Hom A B → Hom A C

      id-left  : {A B : Ob} (f : Hom A B) → id ∘ f ≡ f
      id-right : {A B : Ob} (f : Hom A B) → f ∘ id ≡ f

      assoc : {A B C D : Ob} (f : Hom A B) (g : Hom B C) (h : Hom C D)
         → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
