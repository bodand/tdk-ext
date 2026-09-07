{-# OPTIONS --cubical --safe --guardedness #-}

module Common.JFunctor where

open import Cubical.Foundations.Prelude
open import Meta.Category
open import Common.Functor

import Setoid.Category as SetoidC
import Cubical.Category as CubicalC
open import Setoid.Setoid

-- A J már foglalt a Cubical Preludeban, úgyhogy J₂
J₂ : (ℓ : Level) → Functor (CubicalC.Category ℓ) (SetoidC.Category ℓ ℓ)
J₂ ℓ = record
   { F-obj      = λ X → record
      { Carrier = X
      ; _≈_     = _≡_
      ; ≈-equiv = record
         { reflexive  = λ x → refl
         ; symmetric  = λ x y p → sym p
         ; transitive = λ x y z p q → p ∙ q
         }
      }
   ; F-map      = λ f → record
      { fun       = f
      ; preserves = cong f
      }

   ; F-proper   = λ p x i → p i x

   ; F-id       = λ x → refl
   ; F-comp     = λ f g x → refl
   }
