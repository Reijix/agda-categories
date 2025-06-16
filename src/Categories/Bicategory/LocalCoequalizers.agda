{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory

module Categories.Bicategory.LocalCoequalizers {o ℓ e t} (𝒞 : Bicategory o ℓ e t)  where

open import Categories.Diagram.Coequalizer
open import Level
open import Categories.Functor.Properties
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞
open import Categories.Functor


record LocalCoequalizers : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  field
    localCoequalizers : (A B : Obj) → Coequalizers (hom A B)
    precompPreservesCoequalizer : {A B E : Obj} → (f : E ⇒₁ A)
      → PreservesCoequalizers (-⊚_ {E} {A} {B} f)
    postcompPreservesCoequalizer : {A B E : Obj} → (f : B ⇒₁ E)
      → PreservesCoequalizers (_⊚- {B} {E} {A} f)

open LocalCoequalizers

module _ (localcoeq : LocalCoequalizers)
         {A B E : Obj} {X Y : A ⇒₁ B} {α β : X ⇒₂ Y}
         (coeq : Coequalizer (hom A B) α β) where

  precompCoequalizer : (f : E ⇒₁ A) → Coequalizer (hom E B) (α ◁ f) (β ◁ f)
  precompCoequalizer f = record
    { obj = Coequalizer.obj coeq ∘₁ f
    ; arr = Coequalizer.arr coeq ◁ f
    ; isCoequalizer = precompPreservesCoequalizer localcoeq f {coeq = coeq}
    }

  postcompCoequalizer : (f : B ⇒₁ E) → Coequalizer (hom A E) (f ▷ α) (f ▷ β)
  postcompCoequalizer f = record
    { obj = f ∘₁ Coequalizer.obj coeq
    ; arr = f ▷ Coequalizer.arr coeq
    ; isCoequalizer = postcompPreservesCoequalizer localcoeq f {coeq = coeq}
    }
