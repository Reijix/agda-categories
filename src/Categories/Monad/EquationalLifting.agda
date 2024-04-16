open import Level
open import Categories.Category.Core
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Monad hiding (id)
open import Categories.Monad.Strong
open import Categories.Monad.Commutative
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Cartesian.SymmetricMonoidal
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Monad.EquationalLifting {o ℓ e} {C : Category o ℓ e} (cartesian : Cartesian C) where
  open Category C
  open Cartesian cartesian using (products)
  open BinaryProducts products
  open CartesianMonoidal cartesian using (monoidal)
  open Symmetric (symmetric C cartesian) using (braided)

  IsEquationalLiftingMonad : ∀ (CM : CommutativeMonad braided) → Set (o ⊔ e)
  IsEquationalLiftingMonad CM = ∀ {X} → τ.η _ ∘ Δ {M.F.₀ X} ≈ M.F.₁ ⟨ M.η.η X , id ⟩
    where
      open CommutativeMonad CM
      module τ = strengthen

  -- TODO show that C_T is counital copy category from which follows that it is restriction category.
    Proposition 5.6 in restriction categories III