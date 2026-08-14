{-# OPTIONS --cubical --safe --guardedness #-}
module Test where

open import Cubical.Foundations.Prelude

-- A simple test to prove reflexivity using a cubical path
test : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
test x = refl
