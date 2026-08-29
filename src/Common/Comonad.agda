{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Comonad where

open import Cubical.Foundations.Prelude

open import Meta.Category

open import Common.Functor

record Comonad {o ℓ r : Level} (C : Category o ℓ r) : Type (ℓ-max o (ℓ-max ℓ r)) where
   private
      module C = Category C
      _~_ = λ {A B} → C._~=_ {A} {B}

   field
      W : Functor C C

   private
      module W = Functor W
      W-obj = W.F-obj

      open C using () renaming (_∘_ to _∘C_)

   field
      extract : {X : C.Ob} → C.Hom (W-obj X) X
      extend  : {X Y : C.Ob} → C.Hom (W-obj X) Y → C.Hom (W-obj X) (W-obj Y)

      extend-proper : {X Y : C.Ob} {f g : C.Hom (W-obj X) Y}
                  → f ~ g → extend f ~ extend g

      left-id : {X Y : C.Ob} (f : C.Hom (W-obj X) Y)
              → (extract {Y}) ∘C (extend f) ~ f

      right-id : {X : C.Ob}
               → extend (extract {X}) ~ C.id {W-obj X}

      coassoc : {X Y Z : C.Ob} (f : C.Hom (W-obj X) Y) (g : C.Hom (W-obj Y) Z)
              → (extend g) ∘C (extend f) ~ extend (g ∘C (extend f))

