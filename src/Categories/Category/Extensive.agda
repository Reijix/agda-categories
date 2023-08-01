{-# OPTIONS --without-K --safe #-}

module Categories.Category.Extensive where

-- A category is extensive, if the following holds:
-- Pullbacks of finite-coproduct injections along arbitrary morphisms exist
-- and finite coproducts are disjoint and stable under pullback.
-- https://ncatlab.org/nlab/show/extensive+category

open import Level

open import Categories.Category.Core
open import Categories.Category.Distributive using (Distributive)
open import Categories.Diagram.Pullback using (Pullback; IsPullback)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Object.Coproduct using (Coproduct; IsCoproduct; IsCoproduct⇒Coproduct)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

record Extensive (𝒞 : Category o ℓ e) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open M 𝒞 

  field
    cocartesian : Cocartesian 𝒞

  module CC = Cocartesian cocartesian
  open CC using (_+_; i₁; i₂; ¡)

  field
    -- Pullbacks of coproduct injections along arbitrary morphisms exist
    pullback₁ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₁
    pullback₂ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₂
    
    -- coproducts are stable under pullback
    pullback-of-cp-is-cp : {A B C : Obj} {f : A ⇒ B + C} (P₁ : Pullback 𝒞 f i₁) (P₂ : Pullback 𝒞 f i₂) → IsCoproduct 𝒞 (Pullback.p₁ P₁) (Pullback.p₁ P₂)

    -- coproducts are disjoint
    pullback₁-is-mono : ∀ {A B : Obj} → Mono (i₁ {A = A}{B = B})
    pullback₂-is-mono : ∀ {A B : Obj} → Mono (i₂ {A = A}{B = B})
    disjoint : ∀ {A B : Obj} → IsPullback 𝒞 ¡ ¡ (i₁ {A = A}{B = B}) i₂

  -- Any extensive cartesian category is also distributive
  -- To show this we construct the following two pullbacks and then show by pullback-of-cp-is-cp
  -- that the top row must be a coproduct, and thereby isomorphic to A × B + A × C
  {-
  A × B -- id ⁂ i₁ --> A × (B + C) <-- id ⁂ i₂ -- A × C
    |                       |                        |
    π₂        pb₁           π₂           pb₂         π₂
    |                       |                        |
    V                       V                        V
    B  ------ i₁ -------> B + C <------- i₂ ------  C  
  -}
  Extensive×Cartesian⇒Distributive : Cartesian 𝒞 → Distributive 𝒞
  Extensive×Cartesian⇒Distributive cartesian = record 
    { cartesian = cartesian 
    ; cocartesian = cocartesian 
    ; isIsoˡ = λ {A B C} → record { inv = iso.to ; iso = iso.iso } }
    where
      open Cartesian cartesian using (products)
      module BP = BinaryProducts products
      open BP
      open HomReasoning
      open Equiv
      open MR 𝒞

      module _ {A B C : Obj} where
        -- we can even proof that the square is a pullback for any g
        -- then the left and right square are just instances with g = i₁ and g = i₂
        pb : ∀ {D} (g : D ⇒ B + C) → Pullback 𝒞 (π₂ {A = A} {B = B + C}) g
        pb g = record { p₁ = id ⁂ g ; p₂ = π₂ ; isPullback = record
          { commute = π₂∘⁂
          ; universal = λ {_} {h₁} {h₂} H → ⟨ π₁ ∘ h₁ , h₂ ⟩
          ; unique = λ {X} {h₁} {h₂} {i} {eq} H1 H2 → sym (BP.unique (begin 
              π₁ ∘ i              ≈˘⟨ identityˡ ⟩∘⟨refl ⟩ 
              ((id ∘ π₁) ∘ i)     ≈˘⟨ pullˡ π₁∘⁂ ⟩
              (π₁ ∘ (id ⁂ g) ∘ i) ≈⟨ refl⟩∘⟨ H1 ⟩
              π₁ ∘ h₁             ∎) H2)
          ; p₁∘universal≈h₁ = λ {X} {h₁} {h₂} {eq} → begin 
              (id ⁂ g) ∘ ⟨ π₁ ∘ h₁ , h₂ ⟩ ≈⟨ ⁂∘⟨⟩ ⟩
              ⟨ id ∘ π₁ ∘ h₁ , g ∘ h₂ ⟩   ≈⟨ ⟨⟩-congʳ identityˡ ⟩
              ⟨ π₁ ∘ h₁ , g ∘ h₂ ⟩        ≈˘⟨ ⟨⟩-congˡ eq ⟩
              ⟨ π₁ ∘ h₁ , π₂ ∘ h₁ ⟩       ≈⟨ g-η ⟩
              h₁                          ∎
          ; p₂∘universal≈h₂ = project₂
          } }
        
        iso : (A × B) + (A × C) ≅ A × (B + C)
        iso = Categories.Object.Coproduct.up-to-iso 𝒞 CC.coproduct (IsCoproduct⇒Coproduct 𝒞 (pullback-of-cp-is-cp (pb i₁) (pb i₂)))
      module iso {A B C} = _≅_ (iso {A} {B} {C})
