{-# OPTIONS --cubical --safe --guardedness #-}

module Setoid.Category where

open import Cubical.Foundations.Prelude

open import Setoid.Setoid
open import Meta.Equality
import Meta.Category as MC

equality : {c₁ ℓ₁ c₂ ℓ₂ : Level} (A : Setoid c₁ ℓ₁) (B : Setoid c₂ ℓ₂)
         → Equality (SetoidHom A B)
equality A B = record
   { _~=_     = _≈Hom_

   -- Bizonyítjuk, hogy ez ekvivalenciareláció (a cél-szetoid B tulajdonságaiból)
   ; ~=-refl  = λ x → Setoid.≈-refl B
   ; ~=-sym   = λ p x → Setoid.≈-sym B (p x)
   ; ~=-trans = λ p q x → Setoid.≈-trans B (p x) (q x)
   }

Category : (c ℓ : Level) → MC.Category (ℓ-suc (ℓ-max c ℓ)) (ℓ-max c ℓ) (ℓ-max c ℓ)
Category c ℓ = record
   { Ob       = Setoid c ℓ
   ; Hom      = SetoidHom
   ; Eq       = equality

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

