{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Mainly *properties* of isomorphisms, and a lot of other things too

-- TODO: are the uses of rewrite really necessary?
-- TODO: split things up more semantically?

module Categories.Morphism.Isomorphism {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (_⊔_)
open import Function using (flip)

open import Data.Product using (_,_)
open import Relation.Binary using (Rel; _Preserves_⟶_; IsEquivalence)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

import Categories.Category.Construction.Core as Core
open import Categories.Category.IsGroupoid
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as Morphismₚ
import Categories.Morphism.IsoEquiv as IsoEquiv

open Core 𝒞
open Morphism 𝒞 renaming (TransitiveClosure to ⇒TransitiveClosure)
open Morphismₚ 𝒞
open IsoEquiv 𝒞 using (_≃_)

import Categories.Morphism.Reasoning as MR

open Category 𝒞

private
  module MCore where
    open Morphismₚ Core public
    open Morphism Core public

  variable
    A B C : Obj

open Category Core using () renaming (_∘_ to _∘ᵢ_) public
open IsGroupoid.iso Core-isGroupoid using ()
  renaming (isoˡ to sym∘ᵢ≃refl; isoʳ to ∘ᵢsym≃refl)

CommutativeIso = IsGroupoid.CommutativeSquare Core-isGroupoid

--------------------
-- Also stuff about transitive closure

∘ᵢ-tc : A [ _≅_ ]⁺ B → A ≅ B
∘ᵢ-tc = MCore.∘-tc

infix 4 _≃⁺_
_≃⁺_ : Rel (A [ _≅_ ]⁺ B) _
_≃⁺_ = MCore._≈⁺_

TransitiveClosure : Category _ _ _
TransitiveClosure = MCore.TransitiveClosure

--------------------
-- some infrastructure setup in order to say something about morphisms and isomorphisms
module _ where
  private
    variable
      f g h i j k a b c d l : A ⇒ B

  private
    data IsoPlus : A [ _⇒_ ]⁺ B → Set (o ⊔ ℓ ⊔ e) where
      [_]     : Iso f g → IsoPlus [ f ]
      _∼⁺⟨_⟩_ : ∀ A {f⁺ : A [ _⇒_ ]⁺ B} {g⁺ : B [ _⇒_ ]⁺ C} → IsoPlus f⁺ → IsoPlus g⁺ → IsoPlus (_ ∼⁺⟨ f⁺ ⟩ g⁺)

  open _≅_

  ≅⁺⇒⇒⁺ : A [ _≅_ ]⁺ B → A [ _⇒_ ]⁺ B
  ≅⁺⇒⇒⁺ [ f ]            = [ from f ]
  ≅⁺⇒⇒⁺ (_ ∼⁺⟨ f⁺ ⟩ f⁺′) = _ ∼⁺⟨ ≅⁺⇒⇒⁺ f⁺ ⟩ ≅⁺⇒⇒⁺ f⁺′

  reverse : A [ _≅_ ]⁺ B → B [ _≅_ ]⁺ A
  reverse [ f ]            = [ ≅.sym f ]
  reverse (_ ∼⁺⟨ f⁺ ⟩ f⁺′) = _ ∼⁺⟨ reverse f⁺′ ⟩ reverse f⁺

  reverse⇒≅-sym : (f⁺ : A [ _≅_ ]⁺ B) → ∘ᵢ-tc (reverse f⁺) ≡ ≅.sym (∘ᵢ-tc f⁺)
  reverse⇒≅-sym [ f ]            = ≡.refl
  reverse⇒≅-sym (_ ∼⁺⟨ f⁺ ⟩ f⁺′)  = ≡.cong₂ (Morphism.≅.trans 𝒞) (reverse⇒≅-sym f⁺′) (reverse⇒≅-sym f⁺)

  TransitiveClosure-groupoid : IsGroupoid TransitiveClosure
  TransitiveClosure-groupoid = record
    { _⁻¹ = reverse
    ; iso = λ {_ _ f⁺} → record
      { isoˡ = isoˡ′ f⁺
      ; isoʳ = isoʳ′ f⁺
      }
    }
    where isoˡ′ : (f⁺ : A [ _≅_ ]⁺ B) → ∘ᵢ-tc (reverse f⁺) ∘ᵢ ∘ᵢ-tc f⁺ ≃ ≅.refl
          isoˡ′ f⁺ rewrite reverse⇒≅-sym f⁺ = sym∘ᵢ≃refl
          isoʳ′ : (f⁺ : A [ _≅_ ]⁺ B) → ∘ᵢ-tc f⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺) ≃ ≅.refl
          isoʳ′ f⁺ rewrite reverse⇒≅-sym f⁺ = ∘ᵢsym≃refl

  from-∘ᵢ-tc : (f⁺ : A [ _≅_ ]⁺ B) → from (∘ᵢ-tc f⁺) ≡ ∘-tc (≅⁺⇒⇒⁺ f⁺)
  from-∘ᵢ-tc [ f ]                         = ≡.refl
  from-∘ᵢ-tc (_ ∼⁺⟨ f⁺ ⟩ f⁺′)
    rewrite from-∘ᵢ-tc f⁺ | from-∘ᵢ-tc f⁺′ = ≡.refl

  ≅*⇒⇒*-cong : ≅⁺⇒⇒⁺ {A} {B} Preserves _≃⁺_ ⟶ _≈⁺_
  ≅*⇒⇒*-cong {i = f⁺} {g⁺} f⁺≃⁺g⁺ = begin
    ∘-tc (≅⁺⇒⇒⁺ f⁺) ≡˘⟨ from-∘ᵢ-tc f⁺ ⟩
    from (∘ᵢ-tc f⁺) ≈⟨ _≃_.from-≈ f⁺≃⁺g⁺ ⟩
    from (∘ᵢ-tc g⁺) ≡⟨ from-∘ᵢ-tc g⁺ ⟩
    ∘-tc (≅⁺⇒⇒⁺ g⁺) ∎
    where open HomReasoning

  ≅-shift : ∀ {f⁺ : A [ _≅_ ]⁺ B} {g⁺ : B [ _≅_ ]⁺ C} {h⁺ : A [ _≅_ ]⁺ C} →
              (_ ∼⁺⟨ f⁺ ⟩  g⁺) ≃⁺ h⁺ → g⁺ ≃⁺ (_ ∼⁺⟨ reverse f⁺ ⟩ h⁺)
  ≅-shift {f⁺ = f⁺} {g⁺ = g⁺} {h⁺ = h⁺} eq = begin
    ∘ᵢ-tc g⁺                                     ≈⟨ introʳ (I.isoʳ f⁺) ⟩
    ∘ᵢ-tc g⁺ ∘ᵢ (∘ᵢ-tc f⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺)) ≈⟨ pullˡ eq ⟩
    ∘ᵢ-tc h⁺ ∘ᵢ ∘ᵢ-tc (reverse f⁺)               ∎
    where open IsGroupoid.HomReasoning Core-isGroupoid
          open MR Core
          module I {A B} (f⁺ : A [ _≅_ ]⁺ B) = Morphism.Iso (IsGroupoid.iso TransitiveClosure-groupoid {f = f⁺})

  lift : ∀ {f⁺ : A [ _⇒_ ]⁺ B} → IsoPlus f⁺ → A [ _≅_ ]⁺ B
  lift [ iso ]            = [ record
    { from = _
    ; to   = _
    ; iso  = iso
    } ]
  lift (_ ∼⁺⟨ iso ⟩ iso′) = _ ∼⁺⟨ lift iso ⟩ lift iso′

  reduce-lift : ∀ {f⁺ : A [ _⇒_ ]⁺ B} (f′ : IsoPlus f⁺) → from (∘ᵢ-tc (lift f′)) ≡ ∘-tc f⁺
  reduce-lift [ f ]                         = ≡.refl
  reduce-lift (_ ∼⁺⟨ f′ ⟩ f″)
    rewrite reduce-lift f′ | reduce-lift f″ = ≡.refl

  lift-cong : ∀ {f⁺ g⁺ : A [ _⇒_ ]⁺ B} (f′ : IsoPlus f⁺) (g′ : IsoPlus g⁺) →
                f⁺ ≈⁺ g⁺ → lift f′ ≃⁺ lift g′
  lift-cong f′ g′ eq = record
    { from-≈ = from-≈′
    ; to-≈   = Iso-≈ eq (helper f′) (helper g′)
    }
    where from-≈′ : from (∘ᵢ-tc (lift f′)) ≈ from (∘ᵢ-tc (lift g′))
          from-≈′ rewrite reduce-lift f′ | reduce-lift g′ = eq
          helper : ∀ {f⁺ : A [ _⇒_ ]⁺ B} (f′ : IsoPlus f⁺) → Iso (∘-tc f⁺) (to (∘ᵢ-tc (lift f′)))
          helper [ f ]           = f
          helper (_ ∼⁺⟨ f′ ⟩ f″) = Iso-∘ (helper f′) (helper f″)

  lift-triangle : f ∘ g ≈ h → (f′ : Iso f i) → (g′ : Iso g j) → (h′ : Iso h k) →
                  lift (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) ≃⁺ lift [ h′ ]
  lift-triangle eq f′ g′ h′ = lift-cong (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) [ h′ ] eq

  lift-square : f ∘ g ≈ h ∘ i → (f′ : Iso f a) → (g′ : Iso g b) → (h′ : Iso h c) → (i′ : Iso i j) →
                lift (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) ≃⁺ lift (_ ∼⁺⟨ [ i′ ] ⟩ [ h′ ])
  lift-square eq f′ g′ h′ i′ = lift-cong (_ ∼⁺⟨ [ g′ ] ⟩ [ f′ ]) (_ ∼⁺⟨ [ i′ ] ⟩ [ h′ ]) eq

  lift-pentagon : f ∘ g ∘ h ≈ i ∘ j →
                  (f′ : Iso f a) → (g′ : Iso g b) → (h′ : Iso h c) → (i′ : Iso i d) → (j′ : Iso j l) →
                  lift (_ ∼⁺⟨ _ ∼⁺⟨ [ h′ ] ⟩ [ g′ ] ⟩ [ f′ ]) ≃⁺ lift (_ ∼⁺⟨ [ j′ ] ⟩ [ i′ ])
  lift-pentagon eq f′ g′ h′ i′ j′ = lift-cong (_ ∼⁺⟨ _ ∼⁺⟨ [ h′ ] ⟩ [ g′ ] ⟩ [ f′ ]) (_ ∼⁺⟨ [ j′ ] ⟩ [ i′ ]) eq

module _ where
  private
    variable
      f f′ g h h′ i i′ j k : A ≅ B

  open _≅_

  -- projecting isomorphism commutations to morphism commutations

  project-triangle : g ∘ᵢ f ≃ h → from g ∘ from f ≈ from h
  project-triangle {g = g} {f = f} {h} eq = ≅*⇒⇒*-cong {i = _ ∼⁺⟨ [ f ] ⟩ [ g ]} {j = [ h ]} eq

  project-square : g ∘ᵢ f ≃ i ∘ᵢ h → from g ∘ from f ≈ from i ∘ from h
  project-square {g = g} {f = f} {i = i} {h = h} eq = ≅*⇒⇒*-cong {i = _ ∼⁺⟨ [ f ] ⟩ [ g ]} {j = _ ∼⁺⟨ [ h ] ⟩ [ i ]} eq

  -- direct lifting from morphism commutations to isomorphism commutations

  lift-triangle′ : from f ∘ from g ≈ from h → f ∘ᵢ g ≃ h
  lift-triangle′ eq = lift-triangle eq _ _ _

  lift-square′ : from f ∘ from g ≈ from h ∘ from i → f ∘ᵢ g ≃ h ∘ᵢ i
  lift-square′ eq = lift-square eq _ _ _ _

  lift-pentagon′ : from f ∘ from g ∘ from h ≈ from i ∘ from j → f ∘ᵢ g ∘ᵢ h ≃ i ∘ᵢ j
  lift-pentagon′ eq = lift-pentagon eq _ _ _ _ _

  open MR Core
  open IsGroupoid Core-isGroupoid
  open IsGroupoid.HomReasoning Core-isGroupoid
  open MR.GroupoidR _ Core-isGroupoid

  squares×≃⇒≃ : CommutativeIso f g h i → CommutativeIso f′ g h i′ → i ≃ i′ → f ≃ f′
  squares×≃⇒≃ {g = g} sq₁ sq₂ eq =
    MCore.isos×≈⇒≈ eq helper₁ (IsEquivalence.sym MCore.≅-isEquivalence helper₂) sq₁ sq₂
    where helper₁ = record { iso = IsGroupoid.iso Core-isGroupoid }
          helper₂ = record { iso = IsGroupoid.iso Core-isGroupoid }

  -- imagine a triangle prism, if all the sides and the top face commute, the bottom face commute.
  triangle-prism : i′ ∘ᵢ f′ ≃ h′ →
                   CommutativeIso i j k i′ → CommutativeIso f g j f′ → CommutativeIso h g k h′ →
                   i ∘ᵢ f ≃ h
  triangle-prism {i′ = i′} {f′ = f′} {i = i} {k = k} {f = f} {g = g}
                 eq sq₁ sq₂ sq₃ = squares×≃⇒≃ glued sq₃ eq
    where glued : CommutativeIso (i ∘ᵢ f) g k (i′ ∘ᵢ f′)
          glued = sym (glue (sym sq₁) (sym sq₂))

  elim-triangleˡ : f ∘ᵢ g ∘ᵢ h ≃ i → f ∘ᵢ j ≃ i → g ∘ᵢ h ≃ j
  elim-triangleˡ {f = f} {g = g} {h = h} {i = i} {j = j} perim tri = begin
    g ∘ᵢ h                ≈⟨ introˡ sym∘ᵢ≃refl ⟩
    (f ⁻¹ ∘ᵢ f) ∘ᵢ g ∘ᵢ h ≈⟨ pullʳ perim ⟩
    f ⁻¹ ∘ᵢ i             ≈˘⟨ switch-fromtoˡ′ tri ⟩
    j                     ∎

  elim-triangleˡ′ : f ∘ᵢ g ∘ᵢ h ≃ i → j ∘ᵢ h ≃ i → f ∘ᵢ g ≃ j
  elim-triangleˡ′ {f = f} {g = g} {h = h} {i = i} {j = j} perim tri = begin
    f ∘ᵢ g                  ≈⟨ introʳ sym∘ᵢ≃refl ⟩
    (f ∘ᵢ g) ∘ᵢ (h ∘ᵢ h ⁻¹) ≈⟨ pullˡ (trans (Category.assoc Core) perim) ⟩
    i ∘ᵢ h ⁻¹               ≈˘⟨ switch-fromtoʳ′ tri ⟩
    j                       ∎

  cut-squareʳ : CommutativeIso g f h i → i ∘ᵢ j ≃ h → j ∘ᵢ g ≃ f
  cut-squareʳ {g = g} {f = f} {h = h} {i = i} {j = j} sq tri = begin
    j ∘ᵢ g           ≈⟨ switch-fromtoˡ′ tri ⟩∘⟨ refl ⟩
    (i ⁻¹ ∘ᵢ h) ∘ᵢ g ≈⟨ Category.assoc Core ⟩
    i ⁻¹ ∘ᵢ h ∘ᵢ g   ≈˘⟨ switch-fromtoˡ′ (sym sq) ⟩
    f                ∎
