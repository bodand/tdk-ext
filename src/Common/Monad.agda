{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Monad where

open import Cubical.Foundations.Prelude

open import Meta.Category

open import Common.Functor

record Monad {o ℓ r : Level} (C : Category o ℓ r) : Type (ℓ-max o (ℓ-max ℓ r)) where
   private
      module C = Category C
      _~_ = λ {A B} → C._~=_ {A} {B}

   field
      F : Functor C C

   private
      module M = Functor F
      M-obj = M.F-obj

      open C using () renaming (_∘_ to _∘C_)

   field
      return : {X : C.Ob} → C.Hom X (M-obj X)
      bind : {X Y : C.Ob} → C.Hom X (M-obj Y) → C.Hom (M-obj X) (M-obj Y)

      bind-proper : {X Y : C.Ob} {f g : C.Hom X (M-obj Y)}
                  → f ~ g → bind f ~ bind g

      left-id : {X Y : C.Ob} {f : C.Hom X (M-obj Y)}
              → (bind f) ∘C (return {X}) ~ f

      right-id : {X Y : C.Ob}
               → bind (return {X}) ~ C.id {M-obj X}

      assic : {X Y Z : C.Ob} (f : C.Hom X (M-obj Y)) (g : C.Hom Y (M-obj Z))
            → (bind g) ∘C (bind f) ~ bind ((bind g) ∘C f)

