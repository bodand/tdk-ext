{-# OPTIONS --cubical --safe --guardedness #-}

module Meta.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary as R

record Category (o ℓ r : Level) : Type (ℓ-suc (ℓ-max o (ℓ-max ℓ r))) where
   infix 30 _~=_
   infixr 40 _∘_
   field
      Ob  : Type o
      Hom : Ob → Ob → Type ℓ

      _~=_ : {A B : Ob} → Hom A B → Hom A B → Type r
      ~=-equiv : {A B : Ob} → R.BinaryRelation.isEquivRel (_~=_ {A} {B})

      id : {A : Ob} → Hom A A
      _∘_ : {A B C : Ob} → Hom B C → Hom A B → Hom A C

      ∘-cong : {A B C : Ob} {f f′ : Hom A B} {g g′ : Hom B C}
           → f ~= f′ → g ~= g′ → (g ∘ f) ~= (g′ ∘ f′)

      id-left : {A B : Ob} (f : Hom A B) → (id ∘ f) ~= f
      id-right : {A B : Ob} (f : Hom A B) → (f ∘ id) ~= f
      assoc : {A B C D : Ob} (f : Hom A B) (g : Hom B C) (h : Hom C D)
          → h ∘ (g ∘ f) ~= (h ∘ g) ∘ f

   ~=-refl  : {A B : Ob} {f : Hom A B} → f ~= f
   ~=-refl  {A} {B} {f} = R.BinaryRelation.isEquivRel.reflexive (~=-equiv {A} {B}) f

   ~=-sym   : {A B : Ob} {f g : Hom A B} → f ~= g → g ~= f
   ~=-sym   {A} {B} {f} {g} p = R.BinaryRelation.isEquivRel.symmetric (~=-equiv {A} {B}) f g p

   ~=-trans : {A B : Ob} {f g h : Hom A B} → f ~= g → g ~= h → f ~= h
   ~=-trans {A} {B} {f} {g} {h} p q = R.BinaryRelation.isEquivRel.transitive (~=-equiv {A} {B}) f g h p q

