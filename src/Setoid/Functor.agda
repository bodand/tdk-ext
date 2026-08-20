{-# OPTIONS --cubical --safe --guardedness #-}

module Setoid.Functor where

open import Cubical.Foundations.Prelude
open import Setoid.Category as SC

record Functor {o₀ ℓ₀ r₀ o₁ ℓ₁ r₁ : Level}
               (C₀ : SC.SetoidCategory o₀ ℓ₀ r₀)
               (C₁ : SC.SetoidCategory o₁ ℓ₁ r₁)
            : Type (ℓ-suc
                  (ℓ-max
                     (ℓ-max
                        (ℓ-max o₀ o₁)
                        (ℓ-max ℓ₀ ℓ₁))
                     (ℓ-max r₀ r₁))
               ) where
   private
      module C₀ = SC.SetoidCategory C₀
      module C₁ = SC.SetoidCategory C₁

      open C₀ using () renaming (_∘_ to _∘₀_; _≈_ to _≈₀_)
      open C₁ using () renaming (_∘_ to _∘₁_; _≈_ to _≈₁_)

   field
      F-obj : C₀.Ob → C₁.Ob
      F-map :
         {A B : C₀.Ob}
         (H : C₀.Hom A B)
         → C₁.Hom (F-obj A) (F-obj B)

      F-id :
         {A : C₀.Ob}
         → F-map (C₀.id {A}) ≈₁ C₁.id {F-obj A}

      F-∘ :
         {A B C : C₀.Ob}
         (f : C₀.Hom A B) (g : C₀.Hom B C)
         → F-map (g ∘₀ f) ≈₁ (F-map g) ∘₁ (F-map f)

      F-map-proper :
         {A B : C₀.Ob}
         {f g : C₀.Hom A B}
         → f ≈₀ g
         → (F-map f) ≈₁ (F-map g)
