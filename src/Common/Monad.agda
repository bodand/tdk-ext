{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Monad where

open import Cubical.Foundations.Prelude

open import Meta.Equality
open import Meta.Category

open import Common.Functor

record Monad {o ℓ r : Level} (C : Category o ℓ r) : Type (ℓ-max o (ℓ-max ℓ r)) where
   private
      module C = Category C
      _~_ = λ {A B} → Equality._~=_ (C.Eq A B)

   field
      F : Functor C C

   private
      module M = Functor F
      M-obj = M.F-obj
      M-map = M.F-map

      open C using () renaming (_∘_ to _∘C_)

   field
      return : {X : C.Ob} → C.Hom X (M-obj X)
      join   : {X : C.Ob} → C.Hom (M-obj (M-obj X)) (M-obj X)

      left-id  : {X : C.Ob}
             → (join {X}) ∘C (return {M-obj X}) ~ C.id {M-obj X}

      right-id : {X : C.Ob}
             → (join {X}) ∘C (M-map (return {X})) ~ C.id {M-obj X}

      assoc    : {X : C.Ob}
             → (join {X}) ∘C (M-map (join {X})) ~ (join {X}) ∘C (join {M-obj X})
