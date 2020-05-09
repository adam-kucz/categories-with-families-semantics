{-# OPTIONS --exact-split --safe --prop #-}
module CategoryWithFamilies where

open import Category.Fam

open import Category
open import Category.Opposite
open import Functor
open import Construction.Terminal

open import Universes
open import Type.Sum

record CategoryWithFamilies (𝒰 𝒱 𝒲 𝒳 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒳) ⁺ ˙ where
  infix 182 _∙_
  field
    Ctxs : Category 𝒰 𝒱
    F : Functor (Ctxs ᵒᵖ) (Fam 𝒲 𝒳)
  instance _ = Ctxs; _ = F
  field
    [] : Terminal
    _∙_ : (Δ : obj)(A : pr₁ (F₀ Δ)) → obj
    𝒑 : (Δ : obj)(A : pr₁ (F₀ Δ)) → Δ ∙ A ~> Δ
    𝒒 : (Δ : obj)(A : pr₁ (F₀ Δ)) → obj -- ℂ[ Δ ∙ A ⊢ F₁ (𝒑 Δ A) A ]
    -- F₁ (𝒑 Δ A) A : pr₁ (F₀ (Δ ∙ A))
    -- ℂ[_⊢_] : (X : obj)(A : pr₁ ⦃ F₀ X ⦄) → 𝒳 ˙
    universal-property : {Γ Δ : obj}{A : pr₁ (F₀ Γ)}(f : Γ ~> Δ)(t : pr₂ (F₀ Γ) A) → Γ ~> (Δ ∙ A)
    
    -- obj : 𝒰 ˙
    -- _~>_ : (X Y : obj) → 𝒱 ˙
    -- id : ∀ X → X ~> X
    -- _∘_ : ∀ {X Y Z} → (g : Y ~> Z) (f : X ~> Y) → X ~> Z
    -- left-unit : ∀ {X Y} (f : X ~> Y) → id Y ∘ f == f
    -- right-unit : ∀ {X Y} (f : X ~> Y) → f ∘ id X == f
    -- assoc : ∀ {X Y Z W}
    --   (h : Z ~> W)
    --   (g : Y ~> Z)
    --   (f : X ~> Y)
    --   → -----------------------------
    --   h ∘ (g ∘ f) == (h ∘ g) ∘ f
