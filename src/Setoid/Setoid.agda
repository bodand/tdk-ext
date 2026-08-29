{-# OPTIONS --cubical --safe --guardedness #-}

module Setoid.Setoid where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary as R

record Setoid (c ℓ : Level) : Type (ℓ-suc (ℓ-max c ℓ)) where
   field
      Carrier : Type c
      _≈_     : Carrier → Carrier → Type ℓ
      ≈-equiv : R.BinaryRelation.isEquivRel _≈_

   ≈-refl  : {x : Carrier} → x ≈ x
   ≈-refl {x} = R.BinaryRelation.isEquivRel.reflexive ≈-equiv x

   ≈-sym   : {x y : Carrier} → x ≈ y → y ≈ x
   ≈-sym {x} {y} p = R.BinaryRelation.isEquivRel.symmetric ≈-equiv x y p

   ≈-trans : {x y z : Carrier} → x ≈ y → y ≈ z → x ≈ z
   ≈-trans {x} {y} {z} p q = R.BinaryRelation.isEquivRel.transitive ≈-equiv x y z p q

record SetoidHom {c₁ ℓ₁ c₂ ℓ₂ : Level} (A : Setoid c₁ ℓ₁) (B : Setoid c₂ ℓ₂)
                 : Type (ℓ-max (ℓ-max c₁ ℓ₁) (ℓ-max c₂ ℓ₂)) where
   field
      fun : Setoid.Carrier A → Setoid.Carrier B

      preserves : {x y : Setoid.Carrier A}
                → Setoid._≈_ A x y
                → Setoid._≈_ B (fun x) (fun y)

_≈Hom_ : {c₁ ℓ₁ c₂ ℓ₂ : Level} {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂}
       → SetoidHom A B → SetoidHom A B → Type (ℓ-max c₁ ℓ₂)
_≈Hom_ {A = A} {B = B} f g =
   (x : Setoid.Carrier A) → Setoid._≈_ B (SetoidHom.fun f x) (SetoidHom.fun g x)

