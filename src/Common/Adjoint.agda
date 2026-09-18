{-# OPTIONS --cubical --safe --guardedness #-}

module Common.Adjoint where

open import Cubical.Foundations.Prelude
open import Meta.Category

open import Common.Functor
open import Common.Monad
open import Common.Comonad

infix 4 _⊣_

record _⊣_ {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
           {C : Category o₁ ℓ₁ r₁}
           {D : Category o₂ ℓ₂ r₂}
           (F : Functor C D)
           (G : Functor D C)
           : Type (ℓ-max (ℓ-max o₁ (ℓ-max ℓ₁ r₁)) (ℓ-max o₂ (ℓ-max ℓ₂ r₂))) where
   private
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G

      open C using () renaming (_~=_ to _~C_; _∘_ to _∘C_)
      open D using () renaming (_~=_ to _~D_; _∘_ to _∘D_)

      F-obj = F.F-obj
      F-map = F.F-map
      G-obj = G.F-obj
      G-map = G.F-map

   field
      right-adj-mor : {X : C.Ob} {Y : D.Ob}
                    → D.Hom (F-obj X) Y
                    → C.Hom X (G-obj Y)

      left-adj-mor : {X : C.Ob} {Y : D.Ob}
                   → C.Hom X (G-obj Y)
                   → D.Hom (F-obj X) Y

      right-adj-mor-proper : {X : C.Ob} {Y : D.Ob}
                           {f f′ : D.Hom (F-obj X) Y}
                           → f ~D f′
                           → right-adj-mor f ~C right-adj-mor f′

      left-adj-mor-proper : {X : C.Ob} {Y : D.Ob}
                          {g g′ : C.Hom X (G-obj Y)}
                          → g ~C g′
                          → left-adj-mor g ~D left-adj-mor g′

      lambek-1 : {X : C.Ob} {Y : D.Ob}
               (f : D.Hom (F-obj X) Y)
               → left-adj-mor (right-adj-mor f) ~D f

      lambek-2 : {X : C.Ob} {Y : D.Ob}
               (g : C.Hom X (G-obj Y))
               → right-adj-mor (left-adj-mor g) ~C g

      natural-in-D : {X : C.Ob} {Y Y′ : D.Ob}
                   (f : D.Hom (F-obj X) Y)
                   (k : D.Hom Y Y′)
                   → right-adj-mor (k ∘D f)
                     ~C (G-map k) ∘C (right-adj-mor f)

      natural-in-C : {X′ X : C.Ob} {Y : D.Ob}
                   (f : D.Hom (F-obj X) Y)
                   (h : C.Hom X′ X)
                   → right-adj-mor (f ∘D (F-map h))
                     ~C (right-adj-mor f) ∘C h

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


-- One-sided left-adjoint data presents an adjunction with the right
-- adjoint functor constructed from that data.
LeftAdjoint→Adjunction : {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                        {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                        {L : Functor D C}
                        (LA : LeftAdjoint C D L)
                        → L ⊣ RightAdjointFunctor LA
LeftAdjoint→Adjunction {C = C} {D = D} {L = L} LA = record
   { right-adj-mor        = transpose
   ; left-adj-mor         = untranspose
   ; right-adj-mor-proper = transpose-proper
   ; left-adj-mor-proper  = untranspose-proper
   ; lambek-1             = lambek1
   ; lambek-2             = lambek2
   ; natural-in-D         = natural-codomain
   ; natural-in-C         = natural-domain
   }
   where
      module C = Category C
      module D = Category D
      module L = Functor L
      module R = Functor (RightAdjointFunctor LA)

      open C using () renaming (_∘_ to _∘C_)
      open D using () renaming (_∘_ to _∘D_)

      open LeftAdjoint LA using (ε)

      transpose = LeftAdjoint.right-adj-mor LA
      transpose-proper = LeftAdjoint.right-adj-mor-proper LA
      lambek1 = LeftAdjoint.lambek-1 LA
      lambek2 = LeftAdjoint.lambek-2 LA

      untranspose : {Y : D.Ob} {X : C.Ob}
                  → D.Hom Y (R.F-obj X)
                  → C.Hom (L.F-obj Y) X
      untranspose g = ε ∘C L.F-map g

      untranspose-proper : {Y : D.Ob} {X : C.Ob}
                         {g g′ : D.Hom Y (R.F-obj X)}
                         → D._~=_ g g′
                         → C._~=_ (untranspose g) (untranspose g′)
      untranspose-proper p = C.∘-cong (L.F-proper p) C.~=-refl

      transpose-unique : {Y : D.Ob} {X : C.Ob}
                       {f : C.Hom (L.F-obj Y) X}
                       {g : D.Hom Y (R.F-obj X)}
                       → C._~=_ f (untranspose g)
                       → D._~=_ (transpose f) g
      transpose-unique {g = g} p =
         D.~=-trans (transpose-proper p) (lambek2 g)

      untranspose-comp : {X : C.Ob} {Y Z : D.Ob}
                       (g : D.Hom Y (R.F-obj X))
                       (h : D.Hom Z Y)
                       → C._~=_ (untranspose (g ∘D h))
                                  ((untranspose g) ∘C (L.F-map h))
      untranspose-comp {X = X} g h = C.~=-trans
         (C.∘-cong (L.F-comp h g) C.~=-refl)
         (C.assoc (L.F-map h) (L.F-map g) (ε {X}))

      untranspose-R-map : {X X′ : C.Ob} {Y : D.Ob}
                        (k : C.Hom X X′)
                        (g : D.Hom Y (R.F-obj X))
                        → C._~=_ (untranspose ((R.F-map k) ∘D g))
                                   (k ∘C (untranspose g))
      untranspose-R-map {X = X} k g = C.~=-trans
         (untranspose-comp (R.F-map k) g)
         (C.~=-trans
            (C.∘-cong C.~=-refl (lambek1 (k ∘C (ε {X}))))
            (C.~=-sym (C.assoc (L.F-map g) (ε {X}) k)))

      natural-codomain : {Y : D.Ob} {X X′ : C.Ob}
                       (f : C.Hom (L.F-obj Y) X)
                       (k : C.Hom X X′)
                       → D._~=_ (transpose (k ∘C f))
                                  ((R.F-map k) ∘D (transpose f))
      natural-codomain f k = transpose-unique (C.~=-sym (C.~=-trans
         (untranspose-R-map k (transpose f))
         (C.∘-cong (lambek1 f) C.~=-refl)))

      natural-domain : {Y′ Y : D.Ob} {X : C.Ob}
                     (f : C.Hom (L.F-obj Y) X)
                     (h : D.Hom Y′ Y)
                     → D._~=_ (transpose (f ∘C (L.F-map h)))
                                ((transpose f) ∘D h)
      natural-domain f h = transpose-unique (C.~=-sym (C.~=-trans
         (untranspose-comp (transpose f) h)
         (C.∘-cong C.~=-refl (lambek1 f))))


-- Dually, one-sided right-adjoint data presents an adjunction with the
-- left adjoint functor constructed from that data.
RightAdjoint→Adjunction : {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                         {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                         {R : Functor C D}
                         (RA : RightAdjoint C D R)
                         → LeftAdjointFunctor RA ⊣ R
RightAdjoint→Adjunction {C = C} {D = D} {R = R} RA = record
   { right-adj-mor        = transpose
   ; left-adj-mor         = untranspose
   ; right-adj-mor-proper = transpose-proper
   ; left-adj-mor-proper  = untranspose-proper
   ; lambek-1             = lambek1
   ; lambek-2             = lambek2
   ; natural-in-D         = natural-codomain
   ; natural-in-C         = natural-domain
   }
   where
      module C = Category C
      module D = Category D
      module L = Functor (LeftAdjointFunctor RA)
      module R = Functor R

      open C using () renaming (_∘_ to _∘C_)
      open D using () renaming (_∘_ to _∘D_)

      open RightAdjoint RA using (unit)

      untranspose = RightAdjoint.left-adj-mor RA
      untranspose-proper = RightAdjoint.left-adj-mor-proper RA
      lambek1-dual = RightAdjoint.lambek-1-dual RA
      lambek2-dual = RightAdjoint.lambek-2-dual RA

      transpose : {Y : D.Ob} {X : C.Ob}
                → C.Hom (L.F-obj Y) X
                → D.Hom Y (R.F-obj X)
      transpose f = (R.F-map f) ∘D unit

      transpose-proper : {Y : D.Ob} {X : C.Ob}
                       {f f′ : C.Hom (L.F-obj Y) X}
                       → C._~=_ f f′
                       → D._~=_ (transpose f) (transpose f′)
      transpose-proper p = D.∘-cong D.~=-refl (R.F-proper p)

      lambek1 : {Y : D.Ob} {X : C.Ob}
               (f : C.Hom (L.F-obj Y) X)
               → C._~=_ (untranspose (transpose f)) f
      lambek1 = lambek2-dual

      lambek2 : {Y : D.Ob} {X : C.Ob}
               (g : D.Hom Y (R.F-obj X))
               → D._~=_ (transpose (untranspose g)) g
      lambek2 = lambek1-dual

      natural-codomain : {Y : D.Ob} {X X′ : C.Ob}
                       (f : C.Hom (L.F-obj Y) X)
                       (k : C.Hom X X′)
                       → D._~=_ (transpose (k ∘C f))
                                  ((R.F-map k) ∘D (transpose f))
      natural-codomain f k = D.~=-trans
         (D.∘-cong D.~=-refl (R.F-comp f k))
         (D.~=-sym (D.assoc unit (R.F-map f) (R.F-map k)))

      natural-domain : {Y′ Y : D.Ob} {X : C.Ob}
                     (f : C.Hom (L.F-obj Y) X)
                     (h : D.Hom Y′ Y)
                     → D._~=_ (transpose (f ∘C (L.F-map h)))
                                ((transpose f) ∘D h)
      natural-domain {Y = Y} f h = D.~=-trans
         (natural-codomain (L.F-map h) f)
         (D.~=-trans
            (D.∘-cong (lambek1-dual ((unit {Y}) ∘D h)) D.~=-refl)
            (D.assoc h (unit {Y}) (R.F-map f)))

RightAdjointMonad : {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                    {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                    {G : Functor C D}
                    → RightAdjoint C D G
                    → Monad D
RightAdjointMonad {C = C} {D = D} {G = G} RA = record
   { F = record
       { F-obj    = λ X → G.F-obj (L.F-obj X)
       ; F-map    = λ f → G.F-map (L.F-map f)
       ; F-proper = λ p → G.F-proper (L.F-proper p)
       ; F-id     = D.~=-trans (G.F-proper L.F-id) G.F-id
       ; F-comp   = λ f g → D.~=-trans (G.F-proper (L.F-comp f g)) (G.F-comp (L.F-map f) (L.F-map g))
       }
   ; return      = unit
   ; bind        = λ f → G.F-map (left-adj-mor f)
   ; bind-proper = λ p → G.F-proper (left-adj-mor-proper p)
   ; left-id     = λ {X Y f} → lambek-1-dual f
   ; right-id    = λ {X Y} → D.~=-trans
      (G.F-proper (C.~=-trans
         (left-adj-mor-proper (D.~=-trans
            (D.~=-sym (D.id-left unit))
            (D.~=-sym (D.∘-cong
               D.~=-refl
               G.F-id))))
         (lambek-2-dual C.id)))
      G.F-id

   ; assoc       = λ f g → D.~=-trans
      (D.~=-sym (G.F-comp (left-adj-mor f) (left-adj-mor g)))
      (G.F-proper (C.~=-trans
         (C.~=-sym (lambek-2-dual (left-adj-mor g ∘C left-adj-mor f)))
         (left-adj-mor-proper (D.~=-trans
            (D.∘-cong D.~=-refl (G.F-comp (left-adj-mor f) (left-adj-mor g)))
            (D.~=-trans
               (D.~=-sym (D.assoc unit (G.F-map (left-adj-mor f)) (G.F-map (left-adj-mor g))))
               (D.∘-cong (lambek-1-dual f) D.~=-refl))))))
   }
   where
      open RightAdjoint RA
      module C = Category C
      module D = Category D
      module G = Functor G

      open D using () renaming (_∘_ to _∘D_)
      open C using () renaming (_∘_ to _∘C_)

      module L = Functor (LeftAdjointFunctor RA)

LeftAdjointComonad : {o₁ ℓ₁ r₁ o₂ ℓ₂ r₂ : Level}
                   {C : Category o₁ ℓ₁ r₁} {D : Category o₂ ℓ₂ r₂}
                   {G : Functor D C}
                   → LeftAdjoint C D G
                   → Comonad C
LeftAdjointComonad {C = C} {D = D} {G = G} LA = record
   { W             = record
       { F-obj    = λ X → G.F-obj (R.F-obj X)
       ; F-map    = λ f → G.F-map (R.F-map f)
       ; F-proper = λ p → G.F-proper (R.F-proper p)
       ; F-id     = C.~=-trans (G.F-proper R.F-id) G.F-id
       ; F-comp   = λ f g → C.~=-trans (G.F-proper (R.F-comp f g)) (G.F-comp (R.F-map f) (R.F-map g))
       }
   ; extract       = ε
   ; extend        = λ f → G.F-map (right-adj-mor f)
   ; extend-proper = λ p → G.F-proper (right-adj-mor-proper p)
   ; left-id       = λ f → lambek-1 f
   ; right-id      = λ {X} → C.~=-trans
      (G.F-proper (D.~=-trans
         (right-adj-mor-proper (C.~=-trans
            (C.~=-sym (C.id-right ε))
            (C.∘-cong (C.~=-sym G.F-id) C.~=-refl)))
         (lambek-2 D.id)))
      G.F-id
   ; coassoc       = λ f g → C.~=-trans
      (C.~=-sym (G.F-comp (right-adj-mor f) (right-adj-mor g)))
      (G.F-proper (D.~=-trans
         (D.~=-sym (lambek-2 (right-adj-mor g ∘D right-adj-mor f)))
         (right-adj-mor-proper (C.~=-trans
            (C.∘-cong (G.F-comp (right-adj-mor f) (right-adj-mor g)) C.~=-refl)
            (C.~=-trans
               (C.assoc (G.F-map (right-adj-mor f)) (G.F-map (right-adj-mor g)) ε)
               (C.∘-cong C.~=-refl (lambek-1 g)))))))
   }
   where
       open LeftAdjoint LA
       module C = Category C
       module D = Category D
       module G = Functor G

       open C using () renaming (_∘_ to _∘C_)
       open D using () renaming (_∘_ to _∘D_)

       module R = Functor (RightAdjointFunctor LA)
