{-# OPTIONS --exact-split --prop --no-fast-reduce #-}
module Category.WithUniverses.IdType.Definition where

open import Category.WithUniverses.Definition

open import Universes hiding (A; B; _⁺⁺; _⁺)
open import Function
  hiding (_∘_; _$_) renaming (id to id-fun)
open import Type.Sum hiding (_,_; 〈_,_〉)
open import Data.Nat hiding (_⊔_)
open import Logic
open import Proof hiding (refl)

open import Category hiding (ℂ)
open import Category.Fam
open import Functor hiding (Id)

open import Proposition.Identity.Coercion

private
  variable
    s₀ s₁ : ℕ

record HasIdTypes (C : CwU 𝒰 𝒱 𝒲) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙ where
  open CwU C
  private instance _ = ℂ; _ = λ {s} → ℱ s
  field
    Id : ∀{Γ}(A : Ty s Γ) → Ty s (Γ ,, A ,, A ⁺)

  I : ∀{Γ}(A : Ty s Γ) → Ctx
  I A = _ ,, A ,, A ⁺ ,, Id A

  field
    refl : ∀{Γ}(A : Ty s Γ) → Γ ,, A ~> I A
    R-Id : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (I A)}
      (b : Tm (B ∙ refl A))
      → --------------------------------
      Tm B

    p∘refl : ∀{Γ}(A : Ty s Γ)
      → ----------------------------
      𝒑 (Id A) ∘ refl A == bar (𝒒 A)
    
    reduce : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (I A)}
      (b : Tm (B ∙ refl A))
      → -----------------------------------------
      R-Id b ⊙ refl A == b

    Id-subs : ∀{Γ Δ} (A : Ty s Γ) (f : Δ ~> Γ)
      → ------------------------------------------------
      Id A ∙ q[ q[ f , A ] , A ⁺ ] Het.== Id (A ∙ f)
    refl-subs : ∀{Γ Δ}
      (A : Ty s Γ) (f : Δ ~> Γ)
      → ----------------------------------------
      let coer = subrel {_P_ = _==_} $
            Id.ap2 (λ A' Id-A' →
              Δ ,, A ∙ f ,, A' ,, Id-A' ~> Γ ,, A ,, A ⁺ ,, Id A)
              (A ⁺∙q[ f ]==)
              (Id-subs A f)
      in
      refl A ∘ q[ f , A ] ==
      coe coer q[ q[ q[ f , A ] , A ⁺ ] , Id A ] ∘ refl (A ∙ f)
    R-Id-subs :  ∀{Γ Δ}{A : Ty s₀ Γ}{B : Ty s₁ (I A)}
      (b : Tm (B ∙ refl A))
      (f : Δ ~> Γ)
      → --------------------------------
      let coer₁ : Δ ,, A ∙ f ,, A ⁺ ∙ q[ f , A ] ,, Id A ∙ q[ q[ f , A ] , A ⁺ ]
                  ~> Γ ,, A ,, A ⁺ ,, Id A ==
                  Δ ,, A ∙ f ,, (A ∙ f) ⁺ ,, Id (A ∙ f) ~> Γ ,, A ,, A ⁺ ,, Id A
          coer₁ = subrel {_P_ = _==_} $
            Id.ap2 (λ A' Id-A' →
              Δ ,, A ∙ f ,, A' ,, Id-A' ~> Γ ,, A ,, A ⁺ ,, Id A)
              (A ⁺∙q[ f ]==)
              (Id-subs A f)
          q' = coe coer₁ q[ q[ q[ f , A ] , A ⁺ ] , Id A ]
          coer₀ : Tm (B ∙ refl A ∙ q[ f , A ]) == Tm (B ∙ q' ∙ refl (A ∙ f))
          coer₀ = ap Tm {r = _==_} (
            proof B ∙ refl A ∙ q[ f , A ]
              === B ∙ (refl A ∘ q[ f , A ]) :by: ∙-comp== B (refl A) q[ f , A ]
              === B ∙ (q' ∘ refl (A ∙ f))   :by: ap (B ∙_) (refl-subs A f)
              === B ∙ q' ∙ refl (A ∙ f)
                :by: sym $ ∙-comp== B q' (refl (A ∙ f))
            qed)
      in R-Id (coe coer₀ (b ⊙ q[ f , A ])) == R-Id b ⊙ q'
