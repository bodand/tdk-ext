{-# OPTIONS --cubical --safe --guardedness #-}

module Common.QFunctor where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as SQ
open import Meta.Category
open import Common.Functor

import Setoid.Category as SetoidC
import Cubical.Category as CubicalC
open import Setoid.Setoid

Q : (ℓ : Level) → Functor (SetoidC.Category ℓ ℓ) (CubicalC.Category ℓ)
Q ℓ = record
   { F-obj    = λ S → ((Setoid.Carrier S) / (Setoid._≈_ S)) , squash/

   ; F-map    = λ {A B} f →
      SQ.rec squash/
         (λ x → [ SetoidHom.fun f x ])
         (λ x y r → eq/ (SetoidHom.fun f x) (SetoidHom.fun f y) (SetoidHom.preserves f r))

   ; F-proper = λ {A B} {f g} p → funExt (
      SQ.elimProp (λ _ → squash/ _ _)
                  (λ x → eq/ (SetoidHom.fun f x) (SetoidHom.fun g x) (p x)))

   ; F-id     = λ {A} → funExt (
      SQ.elimProp (λ _ → squash/ _ _)
                  (λ x → refl))

   ; F-comp   = λ {A B C} f g → funExt (
      SQ.elimProp (λ _ → squash/ _ _)
                  (λ x → refl))
   }
