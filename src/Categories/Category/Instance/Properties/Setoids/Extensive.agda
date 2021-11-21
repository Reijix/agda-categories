{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Extensive where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Setoids
open import Categories.Category.Extensive
open import Categories.Category.Cocartesian
open import Categories.Diagram.Pullback
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Category.Monoidal.Instance.Setoids 
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using ([_,_]′)
open import Function.Equality as SΠ renaming (id to ⟶-id)

import Relation.Binary.PropositionalEquality as P

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    module S = Category S
    
  open Pullback
  
  Setoids-Extensive : (ℓ : Level) → Extensive (Setoids ℓ ℓ)
  Setoids-Extensive ℓ = record
     { cocartesian = record { initial = initial ; coproducts = coproducts }
     ; pullback₁ = λ f → pullback ℓ ℓ f i₁ 
     ; pullback₂ = λ f → pullback ℓ ℓ f i₂ 
     ; pullback-of-cp-is-cp = λ {C A B} f → record
         { [_,_] = λ g h →
             record
             { _⟨$⟩_ = copair-$ f g h
             ; cong = λ {z z'} → copair-cong f g h z z'
             }
          ; inject₁ = λ {X g h z} eq →
               trans (isEquivalence {ℓ} X) (copair-inject₁ f g h z) (cong g eq)
          ; inject₂ = λ {X g h z} eq →
               trans (isEquivalence {ℓ} X) (copair-inject₂ f g h z) (cong h eq)
          ; unique = λ {X u g h} x eq {z} eq' →
               trans (isEquivalence {ℓ} X) (copair-unique f g h u z eq) (cong u eq')
          }
     ; pullback₁-is-mono = λ _ _ eq x≈y → drop-inj₁ (eq x≈y)
     ; pullback₂-is-mono = λ _ _ eq x≈y → drop-inj₂ (eq x≈y)
     ; disjoint = λ {A B} → record
          { commute = λ { {()} _}
          ; universal = λ {C f g} eq → record
             { _⟨$⟩_ = λ z → conflict A B (f ⟨$⟩ z) (g ⟨$⟩ z) (eq (refl (isEquivalence {ℓ} C)))
             ; cong = λ z → tt
             } 
          ; unique = λ _ _ _ → tt
          ; p₁∘universal≈h₁ = λ {C h₁ h₂ eq x y} x≈y → conflict A B (h₁ ⟨$⟩ x) (h₂ ⟨$⟩ y) (eq x≈y) 
          ; p₂∘universal≈h₂ = λ {C h₁ h₂ eq x y} x≈y → conflict A B (h₁ ⟨$⟩ x) (h₂ ⟨$⟩ y) (eq x≈y)
          }
     }
       where
         open Cocartesian (Setoids-Cocartesian {ℓ} {ℓ})
         open Relation.Binary.IsEquivalence 
         open import Data.Sum using (inj₁; inj₂)
         open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence)

         -- must be in the standard library. Maybe it is?
         conflict : ∀ {ℓ ℓ' ℓ''} (X Y : Setoid ℓ ℓ') {Z : Set ℓ''}
           (x : ∣ X ∣) (y : ∣ Y ∣) → [ ⊎-setoid X Y ][ inj₁ x ≈ inj₂ y ] → Z
         conflict X Y x y ()

         copair-$ : ∀ {A B C X : Setoid ℓ ℓ}
           (f : C ⟶ ⊎-setoid A B) (g : P (pullback ℓ ℓ f i₁) ⟶ X)
           (h : P (pullback ℓ ℓ f i₂) ⟶ X) → ∣ C ∣ → ∣ X ∣
         copair-$ {A} {B} f g h z with (f ⟨$⟩ z) | P.inspect (f ⟨$⟩_) z
         ... | inj₁ x | P.[ eq ] = g ⟨$⟩ record { elem₁ = z ; elem₂ = x ; commute = reflexive (isEquivalence (⊎-setoid A B)) eq }
         ... | inj₂ y | P.[ eq ] = h ⟨$⟩ record { elem₁ = z ; elem₂ = y ; commute = reflexive (isEquivalence (⊎-setoid A B)) eq }

         copair-$-i₁ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) →
           (x : ∣ A ∣) (z : ∣ C ∣) (eq : [ ⊎-setoid A B ][ f ⟨$⟩ z ≈ inj₁ x ]) →
           [ X ][ copair-$ f g h z ≈ g ⟨$⟩ record { elem₁ = z ; elem₂ = x ; commute = eq} ] -- [ X ][ copair-$ f g h z ]

         copair-$-i₁ {A} {B} f g h x z eq = cong {!!} eq

         copair-cong : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) →
           (z z' : ∣ C ∣) → (z≈z' : [ C ][ z ≈ z' ]) → [ X ][ copair-$ f g h z ≈ copair-$ f g h z' ]
         copair-cong {A} {B} {C} f g h z z' z≈z' with (f ⟨$⟩ z) | P.inspect (_⟨$⟩_ f) z | (f ⟨$⟩ z') | P.inspect (_⟨$⟩_ f) z'
         ... | inj₁ x | P.[ eq ] | inj₁ x' | P.[ eq' ] = cong g
          (z≈z' , drop-inj₁ (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z') (reflexive-A⊎B eq'))))
           where
             trans-A⊎B = trans (isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (isEquivalence (⊎-setoid A B))
             reflexive-A⊎B = reflexive (isEquivalence (⊎-setoid A B))
         ... | inj₁ x | P.[ eq ] | inj₂ y  | P.[ eq' ] = conflict A B x y
          (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z') (reflexive-A⊎B eq')))
           where
             trans-A⊎B = trans (isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (isEquivalence (⊎-setoid A B))
             reflexive-A⊎B = reflexive (isEquivalence (⊎-setoid A B))
         ... | inj₂ y | P.[ eq ] | inj₁ x  | P.[ eq' ] = conflict A B x y
          (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq')) (trans-A⊎B (cong f (sym-C z≈z')) (reflexive-A⊎B eq)))
           where
             trans-A⊎B = trans (isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (isEquivalence (⊎-setoid A B))
             sym-C = sym (isEquivalence C)
             reflexive-A⊎B = reflexive (isEquivalence (⊎-setoid A B))
         ... | inj₂ y | P.[ eq ] | inj₂ y' | P.[ eq' ] = cong h (z≈z' , drop-inj₂
          (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z') (reflexive-A⊎B eq'))))
           where
             trans-A⊎B = trans (isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (isEquivalence (⊎-setoid A B))
             reflexive-A⊎B = reflexive (isEquivalence (⊎-setoid A B))

         -- copair-inject₁ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
         --   (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) →
         --   (x : Setoid.Carrier A) → (z : Setoid.Carrier C) → [ ⊎-setoid A B ][ f ⟨$⟩ z ≈ i₁ ⟨$⟩ x ] → [ X ][ copair-$ f g h z ≈ g ⟨$⟩ {!!} ]
         -- copair-inject₁ f g h x z eq = {!!} -- ( f ⟨$⟩ z ) -- with (f ⟨$⟩ z)
         -- -- ... | a = {!!}

         copair-inject₁ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) 
           (z : FiberProduct f i₁) → [ X ][ copair-$ f g h (FiberProduct.elem₁ z) ≈ g ⟨$⟩ z ]
         copair-inject₁ f g h record { elem₁ = z ; elem₂ = x ; commute = eq } = {!!}

         copair-inject₂ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) 
           (z : FiberProduct f i₂) → [ X ][ copair-$ f g h (FiberProduct.elem₁ z) ≈ h ⟨$⟩ z ]
         copair-inject₂ f g h record { elem₁ = z ; elem₂ = y ; commute = eq } = {!!}

         copair-unique : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X)
           (u : C ⟶ X) (z : ∣ C ∣) →
           [ P (pullback ℓ ℓ f i₂) ⇨ X ][ u ∘ p₁ (pullback ℓ ℓ f i₂) ≈ h ] →
           [ X ][ copair-$ f g h z ≈ u ⟨$⟩ z ]
         copair-unique f g h u z eq = {!!} -- with (f ⟨$⟩ z)
         -- ... | inj₁ x = ?
         -- ... | inj₂ y = ?
        
