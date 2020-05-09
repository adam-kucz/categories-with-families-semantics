{-# OPTIONS --exact-split --safe --prop #-}
module Category.Fam where

open import Category

open import Universes
open import Type.Sum
open import Function renaming (id to id-fun; _∘_ to _o_)
open import Proof

Fam : (𝒰 𝒱 : Universe) → Category (𝒰 ⁺ ⊔ 𝒱 ⁺) (𝒰 ⊔ 𝒱)
Fam 𝒰 𝒱 = record
  { obj = Σ λ (X : 𝒰 ˙) → (x : X) → 𝒱 ˙
  ; _~>_ = λ {(A , B) (A' , B') → Σ λ (f : A → A') → (x : A) → B x → B' (f x)}
  ; id = λ _ → id-fun , λ _ → id-fun
  ; _∘_ = λ { {A , B}{A' , B'}{A″ , B″}(f , g)(f' , g') →
    f o f' ,
    λ x → g (f' x) o g' x}
  ; left-unit = λ _ → Id-refl _
  ; right-unit = λ _ → Id-refl _
  ; assoc = λ _ _ _ → Id-refl _
  }
