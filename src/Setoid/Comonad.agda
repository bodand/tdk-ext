{-# OPTIONS --cubical --safe --guardedness #-}

module Setoid.Comonad where

open import Cubical.Foundations.Prelude
open import Setoid.Category as SC
open import Setoid.Functor as SF

record Comonad {o ℓ r : Level}
             {C : SC.SetoidCategory o ℓ r}
             (W : SF.Functor C C)
         : Type (ℓ-max (ℓ-max o ℓ) r) where
   private
      module C = SC.SetoidCategory C
      open C using () renaming (_∘_ to _∘C_; _≈_ to _≈C_)

      W-obj = SF.Functor.F-obj W
      W-map = SF.Functor.F-map W

   field
      extract : {A : C.Ob} → C.Hom (W-obj A) A
      dup : {A : C.Ob} → C.Hom (W-obj A) (W-obj (W-obj A))

      left-extract :
         {A : C.Ob}
         → (dup {A}) ∘C (W-map (extract {A})) ≈C C.id

      right-extract :
         {A : C.Ob}
         → (dup {A}) ∘C (extract {W-obj A}) ≈C C.id

      dup-assoc :
         {A : C.Ob}
         → (W-map (dup {A})) ∘C (dup {A}) ≈C (dup {W-obj A}) ∘C (dup {A})

