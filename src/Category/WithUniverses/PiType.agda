{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.PiType where

open import Category.WithUniverses.Definition

open import Universes hiding (A; B)
open import Type.Sum hiding (_,_; 〈_,_〉)
open import Data.Nat hiding (_⊔_)
open import Proof

open import Category hiding (ℂ)
open import Functor

private
  variable
    s₀ s₁ : ℕ

open import Category.Fam

open import Function
  hiding (_∘_; _$_; Π) renaming (id to id-fun)

open import Proposition.Identity.Coercion

record HasPiTypes (C : CwU 𝒰 𝒱 𝒲) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙ where
  open CwU C
  private
    instance _ = ℂ; _ = λ {s} → ℱ s
  field
    Π : ∀{Γ}(A : Ty s₀ Γ)(B : Ty s₁ (Γ ,, A)) → Ty (max s₀ s₁) Γ
    ƛ_ : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B) → Tm (Π A B)
    app : ∀{Γ}
      {A : Ty s₀ Γ}
      {B : Ty s₁ (Γ ,, A)}
      (b : Tm (Π A B))
      (a : Tm A)
      → ------------------------------
      let coer : Tm A == Tm (Ty-sub (id Γ) A)
          coer = ap (λ f → Tm (pr₁ f A)) $ sym $ id-preserv Γ
      in
      Tm (B ∙ 〈 id Γ , coe coer a 〉)
    Π-subs : ∀{Γ Δ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (f : Δ ~> Γ)
      → ------------------------------------------------------------------
      let coer : Tm (Ty-sub (𝒑 (A ∙ f)) (Ty-sub f A))
                 ==
                 Tm (Ty-sub (f ∘ 𝒑 (A ∙ f)) A)
          coer = ap (λ — → Tm (pr₁ — A)) $ sym $
                 ∘-preserv (𝒑 (A ∙ f)) f
      in
      Π A B ∙ f == Π (A ∙ f) (B ∙ 〈 f ∘ 𝒑 (A ∙ f) , coe coer (𝒒 (A ∙ f)) 〉)

    ƛ-subs : ∀{Γ Δ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B)
      (f : Δ ~> Γ)
      → -----------------------------------------------------------------
      let coer : Tm (Ty-sub (𝒑 (A ∙ f)) (Ty-sub f A))
                 ==
                 Tm (Ty-sub (f ∘ 𝒑 (A ∙ f)) A)
          coer = ap (λ — → Tm (pr₁ — A)) $ sym $
                 ∘-preserv (𝒑 (A ∙ f)) f
      in
      (ƛ b) ⊙ f Het.== ƛ (b ⊙ 〈 f ∘ 𝒑 (A ∙ f) , coe coer (𝒒 (A ∙ f)) 〉)
    β-reduce : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B) (a : Tm A)
      → ----------------------------------------------------------------
      let coer : Tm A == Tm (Ty-sub (id Γ) A)
          coer = ap (λ — → Tm (pr₁ — A)) $ sym $ id-preserv Γ
      in
      app (ƛ b) a == b ⊙ 〈 id Γ , coe coer a 〉
    η-reduce : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (f : Tm (Π A B))
      → -----------------------------------------------------------------
      ƛ (app (coe (ap Tm $ Π-subs A B (𝒑 A)) (f ⊙ 𝒑 A)) (𝒒 A)) Het.== f
