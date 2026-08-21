{-# OPTIONS --cubical --safe --guardedness #-}

module Meta.Equality where

open import Cubical.Foundations.Prelude

record Equality {ℓ r : Level} (A : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ r)) where
   infix 30 _~=_
   field
      _~=_ : A → A → Type r
      ~=-refl : {x : A}
         → x ~= x
      ~=-sym : {x y : A}
         → x ~= y → y ~= x
      ~=-trans : {x y z : A}
         → x ~= y → y ~= z → x ~= z

