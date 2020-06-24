{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.PiType.Definition where

open import Category.WithUniverses.Definition

open import Universes hiding (A; B; _⁺⁺; _⁺)
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
open import Logic

open import Proposition.Identity.Coercion

record HasPiTypes (C : CwU 𝒰 𝒱 𝒲) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙ where
  open CwU C
  private
    instance _ = ℂ; _ = λ {s} → ℱ s
  field
    Π : ∀{Γ}(A : Ty s₀ Γ)(B : Ty s₁ (Γ ,, A)) → Ty (max s₀ s₁) Γ
    ƛ : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B) → Tm (Π A B)
    app : ∀{Γ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      → ------------------------------
      Γ ,, A ,, Π A B ⁺ ~> Γ ,, A ,, B

    p∘app : ∀{Γ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      → ------------------------------
      𝒑 B ∘ app A B == 𝒑 (Π A B ⁺)
    -- also called Π-C'
    ap-Π-to-2nd-last : ∀{Γ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (b : Tm B)
      → ------------------------------
      let coer : ∀{Δ s}(B : Ty s Δ) → Tm B  == Tm (B ∙ id Δ)
          coer {Δ} B = ap (λ — → Tm (pr₁ — B)) $ sym $ id-preserv Δ
      in
      app A B ∘ bar ((ƛ b) ⊙ 𝒑 A) == bar b

    Π-subs : ∀{Γ Δ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (f : Δ ~> Γ)
      → ------------------------------------------------------------------
      Π A B ∙ f == Π (A ∙ f) (B ∙ q[ f , A ])
    ƛ-subs : ∀{Γ Δ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B)
      (f : Δ ~> Γ)
      → -----------------------------------------------------------------
      (ƛ b) ⊙ f Het.== ƛ (b ⊙ q[ f , A ])
    app-subs : ∀{Γ Δ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (f : Δ ~> Γ)
      → ------------------------------------------------
      let Γ' = Γ ,, A ,, Π A B ⁺
          Δ' = Δ ,, A ∙ f
          coer : Δ' ,, Π A B ⁺ ∙ q[ f , A ] ~> Γ' ==
                 Δ' ,, Π (A ∙ f) (B ∙ q[ f , A ]) ⁺ ~> Γ'
          coer = ap (λ C → Δ' ,, C ~> Γ') {r = _==_} (
            proof Π A B ⁺ ∙ q[ f , A ]
              === Π A B ∙ (𝒑 A ∘ q[ f , A ])
                :by: ∙-comp== (Π A B) (𝒑 A) q[ f , A ] 
              === Π A B ∙ (f ∘ 𝒑 (A ∙ f))
                :by: ap (Π A B ∙_) $ ∧left q[ f , A ]-prop
              === (Π A B ∙ f) ⁺
                :by: sym $ ∙-comp== (Π A B) f (𝒑 (A ∙ f))
              === Π (A ∙ f) (B ∙ q[ f , A ]) ⁺
                :by: ap _⁺ $ Π-subs A B f
            qed)
      in
      app A B ∘ coe coer q[ q[ f , A ] , Π A B ⁺ ]
      == 
      q[ q[ f , A ] , B ] ∘ app (A ∙ f) (B ∙ q[ f , A ])

  app-fun :  ∀{Γ}
    {A : Ty s₀ Γ}
    {B : Ty s₁ (Γ ,, A)}
    (b : Tm (Π A B))
    (a : Tm A)
    → ------------------------------
    Tm (B ∙ bar a)
  app-fun {A = A}{B} b a = coe coer (𝒒 B ⊙ eval-app)
    where eval-app : _ ~> _ ,, A ,, B
          eval-app = app A B ∘ bar (b ⊙ 𝒑 A) ∘ bar a
          coer : Tm (B ⁺ ∙ eval-app) == Tm (B ∙ bar a)
          coer = ap Tm {r = _==_}(
            proof B ⁺ ∙ eval-app
              === B ∙ (𝒑 B ∘ eval-app)
                :by: ∙-comp== B (𝒑 B) eval-app
              === B ∙ (𝒑 B ∘ (app A B ∘ bar (b ⊙ 𝒑 A)) ∘ bar a)
                :by: ap (B ∙_) $ assoc (𝒑 B) _ (bar a)
              === B ∙ (𝒑 B ∘ app A B ∘ bar (b ⊙ 𝒑 A) ∘ bar a)
                :by: ap (λ — → B ∙ (— ∘ bar a)) $ assoc (𝒑 B) (app A B) _
              === B ∙ (𝒑 (Π A B ⁺) ∘ bar (b ⊙ 𝒑 A) ∘ bar a)
                :by: ap (λ — → B ∙ (— ∘ bar (b ⊙ 𝒑 A) ∘ bar a)) $
                     p∘app A B
              === B ∙ (id (_ ,, A) ∘ bar a)
                :by: ap (λ — → B ∙ (— ∘ bar a)) $ p (Π A B ⁺) ∘bar (b ⊙ 𝒑 A)
              === B ∙ bar a
                :by: ap (B ∙_) $ left-unit (bar a)
            qed)
