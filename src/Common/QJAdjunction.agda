{-# OPTIONS --cubical --safe --guardedness #-}

module Common.QJAdjunction where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as SQ
open import Meta.Category

open import Common.Adjoint
open import Common.QFunctor
import Setoid.Category as SetoidC
import Cubical.Category as CubicalC
open import Setoid.Setoid

Q-LeftAdjoint : (ℓ : Level) → LeftAdjoint (CubicalC.Category ℓ) (SetoidC.Category ℓ ℓ) (Q ℓ)
Q-LeftAdjoint ℓ = record
   { F-obj = λ X → record { Carrier = X ; _≈_ = _≡_ }

   -- TODO isSet X
   ; ε = λ {X} → SQ.rec {!   !} (λ x → x) (λ x y p → p)

   ; right-adj-mor = λ f → record
       { fun       = λ y → f [ y ]
       ; preserves = λ {y y'} r → cong f (eq/ y y' r)
       }

   ; right-adj-mor-proper = λ p y i → p i [ y ]

   -- TODO isProp ...
   ; lambek-1 = λ f → funExt (
       SQ.elimProp (λ _ → {!   !})
                   (λ y → refl))

   ; lambek-2 = λ g y → refl
   }
