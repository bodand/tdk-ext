{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Relation.Binary as R

import Meta.Category as MC

Category : (ℓ : Level) → MC.Category (ℓ-suc ℓ) ℓ ℓ
Category ℓ = record
   { Ob       = hSet ℓ
   ; Hom      = λ A B → (fst A → fst B)
   ; _~=_     = _≡_
   ; ~=-equiv = record
      { reflexive  = λ f → refl
      ; symmetric  = λ f g p → sym p
      ; transitive = λ f g h p q → p ∙ q
      }
   ; id       = λ x → x
   ; _∘_      = λ f g x → f (g x)
   ; ∘-cong   = λ p q i x → q i (p i x)
   ; id-left  = λ f → refl
   ; id-right = λ f → refl
   ; assoc    = λ f g h → refl
   }
