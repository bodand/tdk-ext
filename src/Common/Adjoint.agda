{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Adjoint where

open import Cubical.Foundations.Prelude
open import Meta.Category

open import Common.Functor
open import Common.Monad

record RightAdjoint {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                    (C : Category o₁ ℓ₁ r₁)
                    (D : Category o₂ ℓ₂ r₂)
                    (G : Functor C D) : Type (ℓ-max (ℓ-max o₁ (ℓ-max ℓ₁ r₁)) (ℓ-max o₂ (ℓ-max ℓ₂ r₂))) where
   private
      module C = Category C
      module D = Category D
      module G = Functor G

      open C using () renaming (_~=_ to _~C_)
      open D using () renaming (_~=_ to _~D_; _∘_ to _∘D_)

      G-obj = G.F-obj
      G-map = G.F-map
   field
      F-obj : D.Ob → C.Ob

      unit : {Y : D.Ob} → D.Hom Y (G-obj (F-obj Y))

      left-adj-mor : {Y : D.Ob} {X : C.Ob} → D.Hom Y (G-obj X) → C.Hom (F-obj Y) X

      left-adj-mor-proper : {Y : D.Ob} {X : C.Ob} {g g′ : D.Hom Y (G-obj X)}
                          → g ~D g′
                          → (left-adj-mor g) ~C (left-adj-mor g′)

      lambek-1-dual : {Y : D.Ob} {X : C.Ob} (g : D.Hom Y (G-obj X))
                    → (G-map (left-adj-mor g)) ∘D (unit {Y}) ~D g

      lambek-2-dual : {Y : D.Ob} {X : C.Ob} (f : C.Hom (F-obj Y) X)
                     → left-adj-mor ((G-map f) ∘D (unit {Y})) ~C f

record LeftAdjoint {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                    (C : Category o₁ ℓ₁ r₁)
                    (D : Category o₂ ℓ₂ r₂)
                    -- G so I can differentiate F-obj from G-obj witout having to write
                    -- out full paths like F.F-obj
                    (G : Functor D C)
               : Type (ℓ-max (ℓ-max o₁ (ℓ-max ℓ₁ r₁)) (ℓ-max o₂ (ℓ-max ℓ₂ r₂))) where
   private
      module C = Category C
      module D = Category D
      module G = Functor G

      open C using () renaming (_~=_ to _~C_; _∘_ to _∘C_)
      open D using () renaming (_~=_ to _~D_; _∘_ to _∘D_)

      G-obj = G.F-obj
      G-map = G.F-map
   field
      F-obj : C.Ob → D.Ob

      ε : {X : C.Ob} → C.Hom (G-obj (F-obj X)) X

      right-adj-mor : {Y : D.Ob} {X : C.Ob}
                    → C.Hom (G-obj Y) X
                    → D.Hom Y (F-obj X)

      right-adj-mor-proper : {Y : D.Ob} {X : C.Ob} {g g′ : C.Hom (G-obj Y) X}
                           → g ~C g′
                           → (right-adj-mor g) ~D (right-adj-mor g′)

      lambek-1 : {Y : D.Ob} {X : C.Ob} (f : C.Hom (G-obj Y) X)
               → (ε {X}) ∘C (G-map (right-adj-mor f)) ~C f

      lambek-2 : {Y : D.Ob} {X : C.Ob} (g : D.Hom Y (F-obj X))
               → right-adj-mor ((ε {X}) ∘C (G-map g)) ~D g

LeftAdjointFunctor : {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                   {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                   {G : Functor C D}
                   → RightAdjoint C D G
                   → Functor D C
LeftAdjointFunctor {C = C} {D = D} {G = G} RA = record
   { F-obj    = F-obj
   ; F-map    = λ {Y Z} g → left-adj-mor ((unit {Z}) ∘D g)
   ; F-proper = λ {Y Z} {g g′} p → left-adj-mor-proper (D.∘-cong p D.~=-refl)
   ; F-id     = λ {Y} → C.~=-trans
      (left-adj-mor-proper
         (D.~=-trans
            (D.id-right unit)
            (D.~=-trans
               (D.~=-sym (D.id-left (unit)))
               (D.∘-cong D.~=-refl (D.~=-sym (G.F-id))))))
      (lambek-2-dual (C.id))
   ; F-comp   = λ {A B C} f g → C.~=-trans
      (left-adj-mor-proper (D.~=-trans
         (D.~=-trans
            (D.assoc f g unit)
         (D.~=-trans
            (D.∘-cong
               D.~=-refl
               (D.~=-sym (lambek-1-dual (unit ∘D g))))
         (D.~=-trans
            (D.~=-sym (D.assoc
               f
               unit
               (G.F-map (left-adj-mor (unit ∘D g)))))
         (D.~=-trans
            (D.∘-cong
               (D.~=-sym (lambek-1-dual (unit ∘D f)))
               D.~=-refl)
            (D.assoc
               unit
               (G.F-map (left-adj-mor (unit ∘D f)))
               (G.F-map (left-adj-mor (unit ∘D g))))))))

         (D.∘-cong
            D.~=-refl
            (D.~=-sym (G.F-comp
               (left-adj-mor (unit ∘D f))
               (left-adj-mor (unit ∘D g)))))))
      (lambek-2-dual (left-adj-mor (unit ∘D g) ∘C left-adj-mor (unit ∘D f)))
   }
   where
      open RightAdjoint RA
      module C = Category C
      module D = Category D
      module G = Functor G

      open D using () renaming (_∘_ to _∘D_)
      open C using () renaming (_∘_ to _∘C_)


RightAdjointFunctor : {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                   {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                   {F : Functor D C}
                   → LeftAdjoint C D F
                   → Functor C D
RightAdjointFunctor {C = C} {D = D} {F = F} LA = record
   { F-obj    = F-obj
   ; F-map    = λ {Y Z} f → right-adj-mor (f ∘C ε)
   ; F-proper = λ {Y Z} {g g′} p → right-adj-mor-proper (C.∘-cong C.~=-refl p)
   ; F-id     = λ {Y} → D.~=-trans
      (right-adj-mor-proper (C.~=-trans
         (C.id-left ε)
         (C.~=-trans
            (C.~=-sym (C.id-right ε))
            (C.∘-cong
               (C.~=-sym G.F-id)
               C.~=-refl))))
      (lambek-2 D.id)
   ; F-comp   = λ {A B C} f g → D.~=-trans
      (right-adj-mor-proper
         (C.~=-trans
            (C.~=-sym (C.assoc ε f g))
         (C.~=-trans
            (C.∘-cong (C.~=-sym (lambek-1 (f ∘C ε))) C.~=-refl)
         (C.~=-trans
            (C.assoc (G.F-map (right-adj-mor (f ∘C ε))) ε g)
         (C.~=-trans
            (C.∘-cong C.~=-refl (C.~=-sym (lambek-1 (g ∘C ε))))
         (C.~=-trans
            (C.~=-sym
               (C.assoc (G.F-map (right-adj-mor (f ∘C ε)))
                        (G.F-map (right-adj-mor (g ∘C ε)))
                        ε))
            (C.∘-cong
               (C.~=-sym
                  (G.F-comp (right-adj-mor (f ∘C ε))
                            (right-adj-mor (g ∘C ε))))
               C.~=-refl)
         ))))))

      (lambek-2 (right-adj-mor (g ∘C ε) ∘D right-adj-mor (f ∘C ε)))}
   where
      open LeftAdjoint LA
      module C = Category C
      module D = Category D
      module G = Functor F

      open D using () renaming (_∘_ to _∘D_)
      open C using () renaming (_∘_ to _∘C_)

