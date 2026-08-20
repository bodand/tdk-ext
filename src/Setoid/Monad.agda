{-# OPTIONS --cubical --safe --guardedness #-}

module Setoid.Monad where

open import Cubical.Foundations.Prelude
open import Setoid.Category as SC
open import Setoid.Functor as SF

record Monad {o ℓ r : Level}
             {C : SC.SetoidCategory o ℓ r}
             (M : SF.Functor C C)
         : Type (ℓ-max (ℓ-max o ℓ) r) where
   private
      module C = SC.SetoidCategory C
      open C using () renaming (_∘_ to _∘C_; _≈_ to _≈C_)

      M-obj = SF.Functor.F-obj M
      M-map = SF.Functor.F-map M

   field
      return : {A : C.Ob} → C.Hom A (M-obj A)
      join : {A : C.Ob} → C.Hom (M-obj (M-obj A)) (M-obj A)

      left-return :
         {A : C.Ob}
         → (join {A}) ∘C (M-map (return {A})) ≈C C.id

      right-return :
         {A : C.Ob}
         → (join {A}) ∘C (return {M-obj A}) ≈C C.id

      join-assoc :
         {A : C.Ob}
         → (join {A}) ∘C (M-map (join {A})) ≈C (join {A}) ∘C (join {M-obj A})

