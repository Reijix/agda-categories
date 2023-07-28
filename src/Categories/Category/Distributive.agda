{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian
import Categories.Morphism as M

module Categories.Category.Distributive {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open Category 𝒞
open M 𝒞

record Distributive : Set (levelOfTerm 𝒞) where
    field
        cartesian : Cartesian 𝒞
        cocartesian : Cocartesian 𝒞
    
    open Cartesian cartesian
    open BinaryProducts products
    open Cocartesian cocartesian

    distribute : ∀ {A B C} → (A × B + A × C) ⇒ (A × (B + C))
    distribute = [ id ⁂ i₁ , id ⁂ i₂ ]

    field
        iso : ∀ {A B C} → IsIso (distribute {A} {B} {C})
