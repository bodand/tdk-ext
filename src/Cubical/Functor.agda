{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Category as CC

record Functor {o₀ ℓ₀ o₁ ℓ₁ : Level}
               (C₀ : CC.Category o₀ ℓ₀)
               (C₁ : CC.Category o₁ ℓ₁)
            : Type (ℓ-suc (ℓ-max (ℓ-max o₀ o₁) (ℓ-max ℓ₀ ℓ₁))) where
   private
      module C₀ = CC.Category C₀
      module C₁ = CC.Category C₁

      open C₀ using () renaming (_∘_ to _∘₀_)
      open C₁ using () renaming (_∘_ to _∘₁_)

   field
      F-obj : C₀.Ob → C₁.Ob
      F-map :
         {A B : C₀.Ob}
         (H : C₀.Hom A B)
         → C₁.Hom (F-obj A) (F-obj B)

      F-id :
         {A : C₀.Ob}
         → F-map (C₀.id {A}) ≡ C₁.id {F-obj A}

      F-∘ :
         {A B C : C₀.Ob}
         (f : C₀.Hom A B) (g : C₀.Hom B C)
         →  F-map (g ∘₀ f) ≡ (F-map g) ∘₁ (F-map f)
