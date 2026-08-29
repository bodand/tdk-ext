{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Functor where

open import Cubical.Foundations.Prelude
open import Meta.Category

record Functor {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
               (C : Category o₁ ℓ₁ r₁)
               (D : Category o₂ ℓ₂ r₂)
               : Type (ℓ-max o₁ (ℓ-max ℓ₁ (ℓ-max r₁ (ℓ-max o₂ (ℓ-max ℓ₂ r₂))))) where
   private
      module C = Category C
      module D = Category D

      open C using () renaming (_~=_ to _~C_; _∘_ to _∘C_)
      open D using () renaming (_~=_ to _~D_; _∘_ to _∘D_)

   field
      F-obj : C.Ob → D.Ob
      F-map : {A B : C.Ob} → C.Hom A B → D.Hom (F-obj A) (F-obj B)

      F-proper : {A B : C.Ob} {f g : C.Hom A B}
             → f ~C g
             → F-map f ~D F-map g

      F-id : {A : C.Ob}
         → F-map (C.id {A}) ~D D.id {F-obj A}

      F-comp : {A B X : C.Ob} (f : C.Hom A B) (g : C.Hom B X)
           → F-map (g ∘C f) ~D (F-map g) ∘D (F-map f)

