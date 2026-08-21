{-# OPTIONS --cubical --safe --guardedness #-}

module Cubical.Category where

open import Cubical.Foundations.Prelude

open import Meta.Equality
import Meta.Category as MC

equality : {ℓ : Level} (A : Type ℓ) → Equality {ℓ} {ℓ} A
equality A = record
   { _~=_ = _≡_
   ; ~=-refl = refl
   ; ~=-sym = sym
   ; ~=-trans = _∙_
   }

Category : (ℓ : Level) → MC.Category (ℓ-suc ℓ) ℓ ℓ
Category ℓ = record
   { Ob       = Type ℓ
   ; Hom      = λ A B → (A → B)
   ; Eq       = λ A B → equality (A → B)
   ; id       = λ x → x
   ; _∘_      = λ f g x → f (g x)
   ; ∘-cong   = λ p q i x → q i (p i x)
   ; id-left  = λ f → refl
   ; id-right = λ f → refl
   ; assoc    = λ f g h → refl
   }

