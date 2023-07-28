{-# OPTIONS --without-K --safe #-}

module Categories.Category.Extensive where

-- https://ncatlab.org/nlab/show/extensive+category

open import Level

open import Categories.Category.Core
open import Categories.Category.Distributive
open import Categories.Diagram.Pullback
open import Categories.Category.Cocartesian
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Object.Coproduct
open import Categories.Object.Terminal
open import Categories.Morphism
open import Function using (_$_)

private
  variable
    o ℓ e : Level

record Extensive (𝒞 : Category o ℓ e) : Set (suc (o ⊔ ℓ ⊔ e)) where
  open Category 𝒞
  open Pullback

  field
    cocartesian : Cocartesian 𝒞

  module CC = Cocartesian cocartesian
  open CC using (_+_; i₁; i₂; ¡)

  field
    pullback₁ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₁
    pullback₂ : {A B C : Obj} (f : A ⇒ B + C) → Pullback 𝒞 f i₂
    pullback-of-cp-is-cp : {A B C : Obj} (f : A ⇒ B + C) → IsCoproduct 𝒞 (p₁ (pullback₁ f)) (p₁ (pullback₂ f))
    
    pullback₁-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₁ {A = A}{B = B})
    pullback₂-is-mono : ∀ {A B : Obj} → Mono 𝒞 (i₂ {A = A}{B = B})

    disjoint : ∀ {A B : Obj} → IsPullback 𝒞 ¡ ¡ (i₁ {A = A}{B = B}) i₂

Extensive⇒Distributive : ∀ {𝒞 : Category o ℓ e} → Cartesian 𝒞 → Extensive 𝒞 → Distributive 𝒞
Extensive⇒Distributive {𝒞 = 𝒞} cartesian E = record 
  { cartesian = cartesian 
  ; cocartesian = cocartesian 
  ; iso = λ {X Y Z} → record 
    { inv = {!    !}
    ; iso = {!  !} 
    }
  }
  where
    open Category 𝒞
    open Extensive E
    open Cocartesian cocartesian
    open Cartesian cartesian
    open Terminal terminal
    -- open Initial initial
    open BinaryProducts products
    open HomReasoning
    open Equiv
    constr₁ : ∀ {A B} → Pullback 𝒞 ((! {A = A}) +₁ (! {A = B})) i₁
    constr₁ = pullback₁ (! +₁ !)
    constr₂ : ∀ {A B} → Pullback 𝒞 ((! {A = A}) +₁ (! {A = B})) i₂
    constr₂ = pullback₂ (! +₁ !)
    test4 = λ {A B C : Obj} → pullback-of-cp-is-cp {A = A × (B + C)} {B = ⊤} {C = ⊤} ((! +₁ !) ∘ (π₂ {A = A} {B = B + C}))
    coprod = λ {A B C : Obj} → IsCoproduct⇒Coproduct 𝒞 (test4 {A} {B} {C})
    t : ∀ {A B C : Obj} → Obj
    t {A} {B} {C} = let open Coproduct (coprod {A} {B} {C}) in A+B
    test5 = λ {A B C : Obj} → pullback-of-cp-is-cp {A = A × (B + C)} {B = B} {C = C} π₂
    coprod' = λ {A B C : Obj} → IsCoproduct⇒Coproduct 𝒞 (test5 {A} {B} {C})

    cop : ∀ {A B C : Obj} → Coproduct 𝒞 (A × B) (A × C)
    cop {A} {B} {C} = record
      { A+B = A × (B + C)
      ; i₁ = id ⁂ i₁
      ; i₂ = id ⁂ i₂
      ; [_,_] = λ {X} f g → {!  !}
      ; inject₁ = {!   !}
      ; inject₂ = {!   !}
      ; unique = {!   !}
      } where open Coproduct (coprod {A} {B} {C}) using () renaming ([_,_] to [_,_]')

    ttt = λ {A B C} → let open Coproduct (coprod' {A} {B} {C}) in {!  c !}
    pb : ∀ {A B C} → Pullback 𝒞 (π₂ {A = A} {B = B + C}) i₁
    pb {A} {B} {C} = record { P = A × B ; p₁ = id ⁂ i₁ ; p₂ = π₂ ; isPullback = record
      { commute = π₂∘⁂
      ; universal = λ {X} {h₁} {h₂} H → ⟨ π₁ ∘ h₁ , h₂ ⟩
      ; unique = λ {X} {h₁} {h₂} {i} {eq} H1 H2 → sym (unique (sym $
          begin 
            π₁ ∘ h₁ ≈⟨ ∘-resp-≈ʳ (sym H1) ⟩ 
            (π₁ ∘ (id ⁂ i₁) ∘ i) ≈⟨ sym-assoc ⟩
            ((π₁ ∘ (id ⁂ i₁)) ∘ i) ≈⟨ ∘-resp-≈ˡ π₁∘⁂ ⟩
            ((id ∘ π₁) ∘ i) ≈⟨ ∘-resp-≈ˡ identityˡ ⟩
            π₁ ∘ i ∎) H2)
      ; p₁∘universal≈h₁ = λ {X} {h₁} {h₂} {eq} → 
          begin 
            (id ⁂ i₁) ∘ ⟨ π₁ ∘ h₁ , h₂ ⟩ ≈⟨ ⁂∘⟨⟩ ⟩
            ⟨ id ∘ π₁ ∘ h₁ , i₁ ∘ h₂ ⟩ ≈⟨ ⟨⟩-congʳ identityˡ ⟩
            ⟨ π₁ ∘ h₁ , i₁ ∘ h₂ ⟩ ≈⟨ ⟨⟩-congˡ (sym eq) ⟩
            ⟨ π₁ ∘ h₁ , π₂ ∘ h₁ ⟩ ≈⟨ g-η ⟩
            h₁ ∎
      ; p₂∘universal≈h₂ = λ {X} {h₁} {h₂} {eq} → project₂
      } }
    pb2 : ∀ {A B C} → Pullback 𝒞 (! {A = A}) (! {A = B + C})
    pb2 {A} {B} {C} = record { P = A × (B + C) ; p₁ = π₁ ; p₂ = π₂ ; isPullback = record
      { commute = !-unique₂
      ; universal = λ {_ h₁ h₂} _ → ⟨ h₁ , h₂ ⟩
      ; unique = λ H1 H2 → sym (unique H1 H2)
      ; p₁∘universal≈h₁ = project₁
      ; p₂∘universal≈h₂ = project₂
      } }
    pb3 : ∀ {A B C} → Pullback 𝒞 (! {A = A}) (! {A = B + C})
    pb3 {A} {B} {C} = record { P = (A × B) + (A × C) ; p₁ = [ π₁ , π₁ ] ; p₂ = [ i₁ ∘ π₂ , i₂ ∘ π₂ ] ; isPullback = record
      { commute = !-unique₂
      ; universal = λ {X h₁ h₂} H → {!   !}
      ; unique = {!   !}
      ; p₁∘universal≈h₁ = {!   !}
      ; p₂∘universal≈h₂ = {!   !}
      } }
    pb1 = λ {A B C : Obj} → pullback₁ {A = A × (B + C)} π₂









