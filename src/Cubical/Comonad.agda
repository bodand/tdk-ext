{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Comonad where

open import Cubical.Foundations.Prelude
open import Cubical.Category as CC
open import Cubical.Functor as CF

record Comonad {o ℓ : Level}
             {C : CC.Category o ℓ}
             (W : CF.Functor C C)
         : Type (ℓ-max o ℓ) where
   private
      module C = CC.Category C
      open C using () renaming (_∘_ to _∘C_)

      W-obj = CF.Functor.F-obj W
      W-map = CF.Functor.F-map W

   field
      extract : {A : C.Ob} → C.Hom (W-obj A) A
      dup : {A : C.Ob} → C.Hom (W-obj A) (W-obj (W-obj A))

      left-extract :
         {A : C.Ob}
         → (dup {A}) ∘C (W-map (extract {A})) ≡ C.id

      right-extract :
         {A : C.Ob}
         → (dup {A}) ∘C (extract {W-obj A}) ≡ C.id

      dup-assoc :
         {A : C.Ob}
         → (W-map (dup {A})) ∘C (dup {A}) ≡ (dup {W-obj A}) ∘C (dup {A})

