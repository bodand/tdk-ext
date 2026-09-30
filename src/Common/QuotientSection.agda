{-# OPTIONS --cubical --safe --guardedness #-}

module Common.QuotientSection where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as SQ
open import Meta.Category

open import Common.Functor
open import Common.QFunctor
open import Common.JFunctor
open import Common.QJAdjunction

import Setoid.Category as SetoidC
import Cubical.Category as CubicalC
open import Setoid.Setoid

record QuotientSection { ℓ : Level } (S : Setoid ℓ ℓ) : Type ℓ where
   field
      representative : Setoid.Carrier S / Setoid._≈_ S → Setoid.Carrier S
      right-inverse : (q : Setoid.Carrier S / Setoid._≈_ S) → [ representative q ] ≡ q 

-- TODO Ez nem lenne így egyértelműbb, hogy mit csinálunk? Mmint explicit kimondani,
--      hogy itt bevezetjük, az AoC-t?
--      A --safe flagnek mondjuk a `postulate' nem tetszik
--postulate
   --axiomOfChoice : ∀ {ℓ} (S : Setoid ℓ ℓ) → QuotientSection S

module Choice (sectionS : ∀ {ℓ} (S : Setoid ℓ ℓ) → QuotientSection S) where
   open import Common.NaturalTransformation

   ≡→≈ : ∀ {ℓ} {S : Setoid ℓ ℓ} {x y : Setoid.Carrier S} → x ≡ y → Setoid._≈_ S x y
   ≡→≈ {S = S} p = subst (λ z → Setoid._≈_ S _ z) p (Setoid.≈-refl S)

   JQ→Id : {ℓ : Level} → NaturalTransformation (J₂ ℓ ∘F Q ℓ) (IdFunctor {C = SetoidC.Category ℓ ℓ})
   JQ→Id {ℓ} = record
      { component = λ {S} → record
         { fun = QuotientSection.representative (sectionS S)
         ; preserves = λ p → ≡→≈ {S = S} (cong (QuotientSection.representative (sectionS S)) p)
         }
      ; naturality = λ {S T} f q → ?
         -- TODO : Geminivel feltakarítattam a (sikertelen) próbálkozásom.
         --        (Ez látszólag így jobban érthető, mint az eddigiek, majd lehet a többinél
         --        is megcsináltatom, ha lesz időm.)
         --
         --        De az isProp T -t legalul nem látom valósnak? Kivéve, ha van vmi ami miatt
         --        a szetoid ≈ prop, amit nem látok?
         --
         --        Fel kéne venni a Setoid-ba, hogy ≈-isProp? Ha jól emlékszem, nyáron is
         --        volt ilyen felvéve az AddPa-ba.
         --
         --let repS = QuotientSection.representative (sectionS S)
             --repT = QuotientSection.representative (sectionS T)
             --invS = QuotientSection.right-inverse (sectionS S)
             --invT = QuotientSection.right-inverse (sectionS T)

             --Qf = Functor.F-map (Q ℓ) f

             ---- 1. A funktor definíció szerinti kiértékelése a választott reprezentánson
             --eval-f-on-repr : [ SetoidHom.fun f (repS q) ] ≡ Qf [ repS q ]
             --eval-f-on-repr = refl

             ---- 2. Az S-beli kiválasztás inverzének alkalmazása (visszazárás az eredeti osztályba)
             --apply-inv-S : Qf [ repS q ] ≡ Qf q
             --apply-inv-S = cong Qf (invS q)

             ---- 3. A T-beli kiválasztás kiterjesztése a megérkezési oldalon (szimmetrikusan)
             --sym-inv-T : Qf q ≡ [ repT (Qf q) ]
             --sym-inv-T = sym (invT (Qf q))

             ---- 4. A teljes egyenlőség a kózens (Cubical) térben
             --quotient-eq : [ SetoidHom.fun f (repS q) ] ≡ [ repT (Qf q) ]
             --quotient-eq = eval-f-on-repr ∙ apply-inv-S ∙ sym-inv-T

         --in SQ.effective {! ≈-isProp T !} (Setoid.≈-equiv T) _ _ quotient-eq
      }

   Id≅JQ : (ℓ : Level) → NaturalIso (IdFunctor {C = SetoidC.Category ℓ ℓ}) (J₂ ℓ ∘F Q ℓ)
   Id≅JQ ℓ = record
      { trans-to     = Id→JQ ℓ
      ; trans-from   = JQ→Id

      ; isom-to-from = λ {S} q → QuotientSection.right-inverse (sectionS S) q

      ; isom-from-to = λ {S} x → ? -- itt is kell az isProp szerintem
      }
