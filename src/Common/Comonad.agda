{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Comonad where

open import Cubical.Foundations.Prelude

open import Meta.Equality
open import Meta.Category

open import Common.Functor

record Comonad {o ℓ r : Level} (C : Category o ℓ r) : Type (ℓ-max o (ℓ-max ℓ r)) where
   private
      module C = Category C
      _~_ = λ {A B} → Equality._~=_ (C.Eq A B)

   field
      W : Functor C C

   private
      module W = Functor W
      W-obj = W.F-obj
      W-map = W.F-map

      open C using () renaming (_∘_ to _∘C_)

   field
      extract : {X : C.Ob} → C.Hom (W-obj X) X
      dup     : {X : C.Ob} → C.Hom (W-obj X) (W-obj (W-obj X))

      left-id  : {X : C.Ob}
             → (extract {W-obj X}) ∘C (dup {X}) ~ C.id {W-obj X}

      right-id : {X : C.Ob}
             → (W-map (extract {X})) ∘C (dup {X}) ~ C.id {W-obj X}

      coassoc  : {X : C.Ob}
             → (W-map (dup {X})) ∘C (dup {X}) ~ (dup {W-obj X}) ∘C (dup {X})

