{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Monad where

open import Cubical.Foundations.Prelude
open import Cubical.Category as CC
open import Cubical.Functor as CF

record Monad {o ℓ : Level}
             {C : CC.Category o ℓ}
             (M : CF.Functor C C)
         : Type (ℓ-max o ℓ) where
   private
      module C = CC.Category C
      open C using () renaming (_∘_ to _∘C_)

      M-obj = CF.Functor.F-obj M
      M-map = CF.Functor.F-map M

   field
      return : {A : C.Ob} → C.Hom A (M-obj A)
      join : {A : C.Ob} → C.Hom (M-obj (M-obj A)) (M-obj A)

      left-return :
         {A : C.Ob}
         → (join {A}) ∘C (M-map (return {A})) ≡ C.id

      right-return :
         {A : C.Ob}
         → (join {A}) ∘C (return {M-obj A}) ≡ C.id

      join-assoc :
         {A : C.Ob}
         → (join {A}) ∘C (M-map (join {A})) ≡ (join {A}) ∘C (join {M-obj A})


