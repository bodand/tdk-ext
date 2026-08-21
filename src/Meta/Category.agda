{-# OPTIONS --cubical --safe --guardedness #-}

module Meta.Category where

open import Cubical.Foundations.Prelude

open import Meta.Equality

record Category (o ℓ r : Level) : Type (ℓ-suc (ℓ-max o (ℓ-max ℓ r))) where
   field
      Ob  : Type o
      Hom : Ob → Ob → Type ℓ

      Eq  : (A B : Ob) → Equality {ℓ} {r} (Hom A B)

   infix 30 _~=_
   infixr 40 _∘_
   private
      _~=_ = λ {A B} → Equality._~=_ (Eq A B)

   field
      id : {A : Ob} → Hom A A
      _∘_ : {A B C : Ob} → Hom B C → Hom A B → Hom A C

      ∘-cong : {A B C : Ob} {f f′ : Hom A B} {g g′ : Hom B C}
           → f ~= f′ → g ~= g′ → (g ∘ f) ~= (g′ ∘ f′)

      id-left : {A B : Ob} (f : Hom A B) → (id ∘ f) ~= f
      id-right : {A B : Ob} (f : Hom A B) → (f ∘ id) ~= f
      assoc : {A B C D : Ob} (f : Hom A B) (g : Hom B C) (h : Hom C D)
          → h ∘ (g ∘ f) ~= (h ∘ g) ∘ f

