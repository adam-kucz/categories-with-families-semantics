{-# OPTIONS --exact-split --safe --prop #-}
module Category.Fam where

open import Category

open import Universes
open import Type.Sum
open import Function hiding (_∘_) renaming (id to id-fun)
open import Proof

Fam : (𝒰 𝒱 : Universe) → Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
Fam 𝒰 𝒱 = record
  { obj = Σ λ (X : 𝒰 ˙) → (x : X) → 𝒱 ˙
  ; _~>_ = λ {(A , B) (A' , B') → Σ λ (f : A → A') → (x : A) → B x → B' (f x)}
  ; id = λ _ → id-fun , λ _ → id-fun
  ; _∘_ = λ { (f , g)(f' , g') →
    f ∘ₛ f' ,
    λ x → g (f' x) ∘ₛ g' x}
  ; left-unit = λ _ → Id.refl _
  ; right-unit = λ _ → Id.refl _
  ; assoc = λ _ _ _ → Id.refl _
  }
