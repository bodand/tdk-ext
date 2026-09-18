{-# OPTIONS --cubical --safe --guardedness #-}

module Common.QJAdjunction where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as SQ
open import Meta.Category

open import Common.Adjoint
open import Common.QFunctor
open import Common.JFunctor
import Setoid.Category as SetoidC
import Cubical.Category as CubicalC
open import Setoid.Setoid

-- Egyoldali konstrukciós adat: Q-ból előállít egy jobb adjungált funktort. 
Q-LeftAdjointData : (ℓ : Level) → LeftAdjoint (CubicalC.Category ℓ) (SetoidC.Category ℓ ℓ) (Q ℓ)
Q-LeftAdjointData ℓ = record
   { F-obj = λ X → record
       { Carrier = fst X
       ; _≈_     = _≡_
       ; ≈-equiv = record
          { reflexive  = λ x → refl
          ; symmetric  = λ x y p → sym p
          ; transitive = λ x y z p q → p ∙ q
          }
       }

   ; ε = λ {X} → SQ.rec (snd X) (λ x → x) (λ x y p → p)

   ; right-adj-mor = λ f → record
       { fun       = λ y → f [ y ]
       ; preserves = λ {y y'} r → cong f (eq/ y y' r)
       }

   ; right-adj-mor-proper = λ p y i → p i [ y ]

   ; lambek-1 = λ {X = X} f → funExt (
       SQ.elimProp (λ _ → snd X _ _)
                   (λ y → refl))

   ; lambek-2 = λ g y → refl
   }

-- Rövidítés:
Q-LeftAdjoint : (ℓ : Level) → LeftAdjoint (CubicalC.Category ℓ) (SetoidC.Category ℓ ℓ) (Q ℓ)
Q-LeftAdjoint = Q-LeftAdjointData


-- Példa adjungáltra:
Q⊣constructedRightAdjoint : (ℓ : Level)
                           → (Q ℓ) ⊣ RightAdjointFunctor (Q-LeftAdjointData ℓ)
Q⊣constructedRightAdjoint ℓ = LeftAdjoint→Adjunction (Q-LeftAdjointData ℓ)

--  Q adjungált J-hez:
Q⊣J : (ℓ : Level) → (Q ℓ) ⊣ (J₂ ℓ)
Q⊣J ℓ = record
   { right-adj-mor = λ f → record
       { fun       = λ y → f [ y ]
       ; preserves = λ {y y′} r → cong f (eq/ y y′ r)
       }

   ; left-adj-mor = λ {Y = X} g →
       SQ.rec (snd X)
              (SetoidHom.fun g)
              (λ x y r → SetoidHom.preserves g r)

   ; right-adj-mor-proper = λ p y i → p i [ y ]

   ; left-adj-mor-proper = λ {Y = X} p → funExt (
       SQ.elimProp (λ _ → snd X _ _)
                   (λ x → p x))

   ; lambek-1 = λ {Y = X} f → funExt (
       SQ.elimProp (λ _ → snd X _ _)
                   (λ x → refl))

   ; lambek-2 = λ g y → refl

   ; natural-in-D = λ f k y → refl
   ; natural-in-C = λ f h x → refl
   }
