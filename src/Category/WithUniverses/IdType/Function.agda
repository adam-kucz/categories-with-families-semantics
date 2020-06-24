{-# OPTIONS --exact-split --prop --no-fast-reduce #-}
module Category.WithUniverses.IdType.Function where

open import Category.WithUniverses.IdType.Definition

open import Universes hiding (A; B; _⁺⁺; _⁺)
open import Proof hiding (refl)

open import Category.WithUniverses.Definition
open import Category.WithUniverses.Function
open import Category hiding (ℂ)
open import Functor hiding (Id)

open import Proposition.Identity.Coercion

module WithIdTypes {C : CwU 𝒰 𝒱 𝒲} ⦃ id-types : HasIdTypes C ⦄ where
  open CwU C renaming (module Coer to CwU-Coer)
  open WithCwU C
  open Variable hiding (C)
  open HasIdTypes id-types
  private
    instance
      _ = ℂ

  module Coer₀ where
    Id-type : {A : Ty s Γ}(a : Tm A) →
      Γ ,, A ⁺ ∙ bar a ~> Γ ,, A ,, A ⁺ == Γ ,, A ~> Γ ,, A ,, A ⁺
    Id-type {Γ = Γ}{A} a = ap (λ — → Γ ,, — ~> Γ ,, A ,, A ⁺) $ A ⁺∙bar a

  Id-type : (A : Ty s Γ)(a a' : Tm A) → Ty s Γ
  Id-type {Γ = Γ} A a a' =
    Id A ∙ (wk-bar a' (just Γ +,, A) ∘ bar a)

  module Coer₁ where
    refl-term : {A : Ty s Γ}(a : Tm A) →
      Tm (Id A ⁺ ∙ (refl A ∘ bar a)) == Tm (Id-type A a a)
    refl-term {Γ = Γ}{A} a = ap Tm {r = _==_}(
      proof Id A ⁺ ∙ (refl A ∘ bar a)
        === Id A ∙ (𝒑 (Id A) ∘ (refl A ∘ bar a))
          :by: ∙-comp== (Id A) (𝒑 (Id A)) (refl A ∘ bar a)
        === Id A ∙ (𝒑 (Id A) ∘ refl A ∘ bar a)
          :by: ap (Id A ∙_) $ assoc (𝒑 (Id A)) (refl A) (bar a)
        === Id A ∙ (bar (𝒒 A) ∘ bar a)
          :by: ap (λ — → Id A ∙ (— ∘ bar a)) $ p∘refl A
        === Id A ∙ (wk-bar a (just Γ +,, A) ∘ bar a)
          :by: ap (Id A ∙_) $ sym $ wk-bar∘bar a
      qed)
  
  refl-term : (a : Tm A) → Tm (Id-type A a a)
  refl-term {A = A} a = coe (Coer₁.refl-term a) (𝒒 (Id A) ⊙ (refl A ∘ bar a))

  module Coer where
    open Coer₀ public
    open Coer₁ public
