{-# OPTIONS --cubical --safe --guardedness #-}

module Common.NaturalTransformation where

open import Cubical.Foundations.Prelude
open import Meta.Category
open import Common.Functor

record NaturalTransformation {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                             {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                             (F G : Functor C D) : Type (ℓ-max o₁ (ℓ-max ℓ₁ (ℓ-max r₁ (ℓ-max o₂ (ℓ-max ℓ₂ r₂))))) where
   private
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G

      open D using () renaming (_∘_ to _D∘_; _~=_ to _D~=_)
   field
      component : {X : C.Ob} → D.Hom (F.F-obj X) (G.F-obj X)

      naturality : {X Y : C.Ob} (f : C.Hom X Y)
                 → (G.F-map f D∘ component) D~= (component D∘ F.F-map f)

record NaturalIso {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                  {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                  (F G : Functor C D) : Type (ℓ-max o₁ (ℓ-max ℓ₁ (ℓ-max r₁ (ℓ-max o₂ (ℓ-max ℓ₂ r₂))))) where
   private
      module C = Category C
      module D = Category D

      open D using () renaming (_~=_ to _D~=_; _∘_ to _D∘_)

   field
      trans-to   : NaturalTransformation F G
      trans-from : NaturalTransformation G F

   private
      to   = NaturalTransformation.component trans-to
      from = NaturalTransformation.component trans-from

   field
      isom-to-from : {X : C.Ob} → to {X} D∘ from {X} D~= D.id
      isom-from-to : {X : C.Ob} → from {X} D∘ to {X} D~= D.id

