{-# OPTIONS --cubical --safe --guardedness #-}

module Setoid.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary as R

open import Setoid.Setoid
import Meta.Category as MC

Category : (c ℓ : Level) → MC.Category (ℓ-suc (ℓ-max c ℓ)) (ℓ-max c ℓ) (ℓ-max c ℓ)
Category c ℓ = record
   { Ob       = Setoid c ℓ
   ; Hom      = SetoidHom

   ; _~=_     = _≈Hom_
   ; ~=-equiv = λ {A B} → record
      { reflexive  = λ f x → Setoid.≈-refl B
      ; symmetric  = λ f g p x → Setoid.≈-sym B (p x)
      ; transitive = λ f g h p q x → Setoid.≈-trans B (p x) (q x)
      }

   ; id       = λ {A} → record
                 { fun = λ x → x
                 ; preserves = λ p → p
                 }

   ; _∘_      = λ {A B C} g f → record
                 { fun = λ x → SetoidHom.fun g (SetoidHom.fun f x)
                 ; preserves = λ p → SetoidHom.preserves g (SetoidHom.preserves f p)
                 }

   ; ∘-cong   = λ {A B C} {f f′ g g′} p q x →
                 Setoid.≈-trans C (SetoidHom.preserves g (p x)) (q (SetoidHom.fun f′ x))
   ; id-left  = λ {A B} f x → Setoid.≈-refl B
   ; id-right = λ {A B} f x → Setoid.≈-refl B
   ; assoc    = λ {A B C D} f g h x → Setoid.≈-refl D
   }

