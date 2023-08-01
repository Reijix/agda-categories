{-# OPTIONS --without-K --safe #-}

-- Bundled version of a extensive category
module Categories.Category.Extensive.Bundle where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Category.Extensive using (Extensive)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Distributive using (Distributive)

record ExtensiveCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e  -- U for underlying
    extensive : Extensive U

  open Category U public
  open Extensive extensive public
  open Cocartesian cocartesian public

record ExtensiveDistributiveCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U         : Category o ℓ e  -- U for underlying
    cartesian : Cartesian U
    extensive : Extensive U
  
  open Category U public
  open Extensive extensive public
  open Cartesian cartesian public
  open Cocartesian cocartesian public

  distributive : Distributive U
  distributive = Extensive×Cartesian⇒Distributive cartesian

  open Distributive distributive public
