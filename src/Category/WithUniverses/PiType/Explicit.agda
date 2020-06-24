{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.PiType.Explicit where

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

record HasPiTypes-explicit (C : CwU 𝒰 𝒱 𝒲) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙ where
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
      Π A B ∙ f == Π (A ∙ f) (B ∙ q[ f , A ])

    ƛ-subs : ∀{Γ Δ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B)
      (f : Δ ~> Γ)
      → -----------------------------------------------------------------
      (ƛ b) ⊙ f Het.== ƛ (b ⊙ q[ f , A ])
    β-reduce : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B) (a : Tm A)
      → ----------------------------------------------------------------
      app (ƛ b) a == b ⊙ bar a
    η-reduce : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (f : Tm (Π A B))
      → -----------------------------------------------------------------
      ƛ (app (coe (ap Tm $ Π-subs A B (𝒑 A)) (f ⊙ 𝒑 A)) (𝒒 A)) Het.== f

  app-mor :  ∀{Γ}
    (A : Ty s₀ Γ)
    (B : Ty s₁ (Γ ,, A))
    → ---------------------------------------
    Γ ,, A ,, (Π A B ∙ 𝒑 A) ~> Γ ,, A ,, B
  app-mor {s₀}{s₁}{Γ} A B =
    〈 𝒑 (Π A B ⁺) , coe coer″ (app (coe coer-b b) a) 〉 -- coer″
    where Δ = Γ ,, A ,, Π A B ⁺
          -- A⁺⁺ : Ty s₀ Δ
          -- A⁺⁺ = A ⁺⁺
          -- Π⁺⁺ : Ty (max s₀ s₁) Δ
          -- Π⁺⁺ = Π A B ⁺⁺
          a : Tm (A ⁺ ∙ 𝒑 (Π A B ⁺))
          a = 𝒒 A ⊙ 𝒑 (Π A B ⁺) -- 𝒒 A ⊙ 𝒑 (Π A B ⁺)
          b : Tm (Π A B ⁺⁺)
          b = 𝒒 (Π A B ⁺)
          coer : Tm (A ⁺⁺) == Tm (A ∙ (𝒑 A ∘ 𝒑 (A ⁺)))
          coer = ap Tm $ ∙-comp== A (𝒑 A) (𝒑 (A ⁺))
          coer' : Tm (A ⁺³) == Tm (A ⁺ ∙ (𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺)))
          coer' = ap Tm $ ∙-comp== (A ⁺) (𝒑 (Π A B ⁺)) (𝒑 (A ⁺⁺))
          B⁺ = B ∙ 〈 𝒑 A ∘ 𝒑 (A ⁺) , coe coer (𝒒 (A ⁺)) 〉
          B⁺⁺ = B⁺ ∙ 〈 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ,
                       coe coer' (𝒒 (A ⁺⁺)) 〉
          coer-b : Tm (Π A B ⁺⁺) == Tm (Π (A ⁺⁺) B⁺⁺)
          coer-b = ap Tm (
            proof Π A B ⁺⁺
              === (Π (A ⁺) B⁺) ∙ 𝒑 (Π A B ⁺)
                :by: ap (_∙ 𝒑 (Π A B ⁺)) $ Π-subs A B (𝒑 A)
              === Π (A ⁺⁺) B⁺⁺
                :by: Π-subs (A ⁺) B⁺ (𝒑 (Π A B ⁺))
            qed)
          coer‴ : Tm (A ⁺⁺) == Tm (A ⁺⁺ ∙ id Δ)
          coer‴ = ap (λ — → Tm (pr₁ — (A ⁺⁺))) $ sym $ id-preserv Δ
          coer″ : Tm (B⁺⁺ ∙ 〈 id Δ , coe coer‴ a 〉)
                  ==
                  Tm (B ∙ 𝒑 (Π A B ⁺))
          coer″ = ap Tm (
            proof B ∙ f₀ ∙ f₁ ∙ f₂
              === B ∙ (f₀ ∘ f₁) ∙ f₂
                :by: ap (_∙ f₂) $ ∙-comp== B f₀ f₁
              === B ∙ 〈 𝒑 A ∘ (𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺)) ,
                        coe coer₀ (coe coer' (𝒒 (A ⁺⁺))) 〉 ∙ f₂
                :by: ap (λ — → B ∙ — ∙ f₂)
                     〈 𝒑 A ∘p A ,q〉∘〈 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ,
                                    coe coer' (𝒒 (A ⁺⁺)) 〉
              === B ∙ 〈 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ,
                        coe coer₁ (𝒒 (A ⁺⁺)) 〉 ∙ f₂
                :by: ap (λ — → B ∙ — ∙ f₂)
                     〈 assoc (𝒑 A) _ _ ,
                      proof coe coer₀ (coe coer' (𝒒 (A ⁺⁺)))
                        het== coe coer' (𝒒 (A ⁺⁺))
                          :by: coe-eval coer₀ (coe coer' (𝒒 (A ⁺⁺)))
                        het== 𝒒 (A ⁺⁺)
                          :by: coe-eval coer' (𝒒 (A ⁺⁺))
                        het== coe coer₁ (𝒒 (A ⁺⁺))
                          :by: isym $ coe-eval coer₁ (𝒒 (A ⁺⁺))
                      qed 〉==
              === B ∙ (〈 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ,
                         coe coer₁ (𝒒 (A ⁺⁺)) 〉 ∘ f₂)
                :by: ∙-comp== B
                     〈 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ,
                       coe coer₁ (𝒒 (A ⁺⁺)) 〉 f₂ 
              === B ∙ 𝒑 (Π A B ⁺)
                :by: ap (B ∙_) (
                  proof 〈 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ,
                         coe coer₁ (𝒒 (A ⁺⁺)) 〉 ∘ f₂
                    === 〈 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ∘ f₂ ,
                          coe coer₃ (coe coer₁ (𝒒 (A ⁺⁺)) ⊙ f₂) 〉
                      :by: 〈 _ , _ 〉∘ f₂
                    === 〈 𝒑 A ∘ 𝒑 (Π A B ⁺) , coe coer₂ a 〉
                      :by: 〈 proof 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) ∘ f₂
                               === 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ (𝒑 (A ⁺⁺) ∘ f₂)
                                 :by: sym $ assoc _ _ f₂
                               === 𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ id Δ
                                 :by: ap (𝒑 A ∘ 𝒑 (Π A B ⁺) ∘_) $
                                      ∧left 〈 id Δ , coe coer‴ a 〉-prop
                               === 𝒑 A ∘ 𝒑 (Π A B ⁺)
                                 :by: right-unit (𝒑 A ∘ 𝒑 (Π A B ⁺))
                             qed ,
                             proof coe coer₃ (coe coer₁ (𝒒 (A ⁺⁺)) ⊙ f₂)
                               het== coe coer₁ (𝒒 (A ⁺⁺)) ⊙ f₂
                                 :by: coe-eval coer₃ (
                                        coe coer₁ (𝒒 (A ⁺⁺)) ⊙ f₂)
                               het== 𝒒 (A ⁺⁺) ⊙ f₂
                                 :by: Id.ap2 (λ C (q : Tm C) → q ⊙ f₂)
                                        (sym $ coer₁')
                                        (coe-eval coer₁ (𝒒 (A ⁺⁺)))
                               het== coe coer‴ a
                                 :by: ∧right 〈 id Δ , coe coer‴ a 〉-prop
                               het== a
                                 :by: coe-eval coer‴ a
                               het== coe coer₂ a
                                 :by: isym $ coe-eval coer₂ a
                             qed 〉==
                    === 〈 𝒑 A , 𝒒 A 〉 ∘ 𝒑 (Π A B ⁺)
                      :by: sym $ 〈 𝒑 A , 𝒒 A 〉∘ 𝒑 (Π A B ⁺) 
                    === id (Γ ,, A) ∘ 𝒑 (Π A B ⁺)
                      :by: ap (_∘ 𝒑 (Π A B ⁺)) $ 〈p,q〉==id A 
                    === 𝒑 (Π A B ⁺)
                      :by: left-unit (𝒑 (Π A B ⁺)) 
                  qed)
            qed)
            where f₀ = 〈 𝒑 A ∘ 𝒑 (A ⁺) , coe coer (𝒒 (A ⁺)) 〉
                  f₁ = 〈 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺) , coe coer' (𝒒 (A ⁺⁺)) 〉
                  f₂ = 〈 id Δ , coe coer‴ a 〉
                  coer₀ = ap Tm $ ∙-comp== A (𝒑 A) (𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺))
                  coer₁' =
                    proof A ∙ 𝒑 A ∙ 𝒑 (Π A B ⁺) ∙ 𝒑 (A ⁺⁺)
                      === A ∙ (𝒑 A ∘ 𝒑 (Π A B ⁺)) ∙ 𝒑 (A ⁺⁺)
                        :by: ap (_∙ 𝒑 (A ⁺⁺)) $ ∙-comp== A (𝒑 A) (𝒑 (Π A B ⁺))
                      === A ∙ (𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺))
                        :by: ∙-comp== A (𝒑 A ∘ 𝒑 (Π A B ⁺)) (𝒑 (A ⁺⁺))
                    qed
                  coer₁ = ap Tm coer₁'
                  coer₂ = ap Tm $ ∙-comp== A (𝒑 A) (𝒑 (Π A B ⁺))
                  coer₃ = ap Tm $ ∙-comp== A (𝒑 A ∘ 𝒑 (Π A B ⁺) ∘ 𝒑 (A ⁺⁺)) f₂
