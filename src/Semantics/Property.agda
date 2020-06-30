{-# OPTIONS --exact-split --prop #-}
open import PropUniverses hiding (_⁺; _⁺⁺)
open import Category.WithUniverses

module Semantics.Property
  (C : CwU 𝒰 𝒱 𝒲)
  ⦃ pi-types : HasPiTypes C ⦄
  ⦃ id-types : HasIdTypes C ⦄
  where

open import Semantics.Definition C
open import TypeTheory

open import Data.Nat
open import Logic hiding (_,_)

open import Category hiding (ℂ)
open import Functor

open CwU C renaming (module Coer to CwU-Coer)
open WithCwU C
open HasPiTypes pi-types renaming (app to app')
-- open HasIdTypes id-types renaming (Id to Id'; refl to refl')
-- open WithIdTypes ⦃ id-types ⦄ renaming (refl-term to refl-term')
--   hiding (module Coer)
private instance _ = ℂ; _ = λ {s} → ℱ s

soundness : ∀{Γ : Context n}{t t' T i}
  (p₀ : Γ ⊢ t ∋ T)
  (p₁ : Γ ⊢ T ∋ ⋆ i)
  (q : t ⇝ t')
  → ---------------------
  ∃ λ X → ∃ λ (ρ : Val n X) → ∃ λ A → ∃ λ a →
  ⟦ Γ ⟧:=[ X , ρ ] ∧
  ∥ T ∥[ X , ρ , i ]:= A ∧
  ∥ t ∥[ X , ρ , i , A ]:= a ∧
  ∥ t' ∥[ X , ρ , i , A ]:= a
soundness (pre p₀ R⇝T) p₁ q = {!!}
soundness (sort Γ p) p₁ q = {!!}
soundness (pi-type p₀ p₂) p₁ q = {!!}
soundness (lam p₀) p₁ q = {!!}
soundness (elim Δ⊢ρe∈S) p₁ q = {!!}











-- problem₀ : {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
--   {A : Ty s₀ Γ}
--   {a₀ a₁ : Tm A}{a₀==a₁ : Tm (Id-type A a₀ a₁)}
--   → let Id-typ = Id-type (A ⁺) (a₀ ⊙ 𝒑 A) (𝒒 A)
--         Γ' = Γ ,, A ,, Id-typ
--   in {B : Ty s₁ Γ'}
--   → ?

{-
{- want:
bar (a₀==a₁ ⊙ 𝒑 A) ∘ bar a₁  : Γ ~> Γ ,, A ,, Id-type A a₀ a₁ ∙ 𝒑 A
bar (a₀==a₁ ⊙ 𝒑 A) : Γ ,, A ~> Γ ,, A ,, Id-type A a₀ a₁ ∙ 𝒑 A
bar a₁ : Γ ~> Γ ,, A

where
a₀==a₁ ⊙ 𝒑 A : Tm (Id-type A a₀ a₁ ⁺)
Id-type A a₀ a₁ = Id A ∙ (wk-bar a₁ (just Γ +,, A) ∘ bar a₀)
𝒒 A : Tm (A ⁺)
𝒒 A ⊙ bar a₀ :~ Tm A

Id-typ = 
  Id-type (A ⁺) (a₀ ⊙ 𝒑 A) (𝒒 A) =
  Id (A ⁺) ∙ (bar (𝒒 A ⊙ 𝒑 (A ⁺)) ∘ bar (a₀ ⊙ 𝒑 A)) =
  (Id A ∙ q[ q[ 𝒑 A , A ] , A ⁺ ]) (bar (𝒒 A ⊙ 𝒑 A⁺) ∘ bar (a₀ ⊙ 𝒑 A)) =
  Id A ∙ (q[ q[ 𝒑 A , A ] , A ⁺ ] ∘ bar (𝒒 A ⊙ 𝒑 A⁺) ∘ bar (a₀ ⊙ 𝒑 A)) =
  Id A ∙ 〈 bar a₀ ∘ 𝒑 A , coe _ (𝒒 A)  〉


Id-type A a₀ a₁ ∙ 𝒑 A =
  Id A ∙ (bar (a₁ ⊙ 𝒑 A) ∘ bar a₀ ∘ 𝒑 A) =~
  Id A ∙ 〈 bar a₀ ∘ 𝒑 A , a₁ ⊙ 𝒑 A 〉

bar (a₁ ⊙ 𝒑 A) ∘ bar a₀ ∘ 𝒑 A =~
〈 bar a₀ , a₁ ⊙ 𝒑 A ⊙ bar a₀ 〉 ∘ 𝒑 A =~
〈 bar a₀ , a₁ 〉 ∘ 𝒑 A =~
〈 bar a₀ ∘ 𝒑 A , a₁ ⊙ 𝒑 A 〉

with
q[ f , A ] ∘ 〈 f' , t' 〉 =~ 〈 f ∘ f' , t' 〉
bar a =~ 〈 id , a 〉
〈 f , a 〉 ∘ g =~ 〈 f ∘ g , a ⊙ g 〉
-}
          coer₀ : Γ″ ~> Γ″ ,, A ⁺⁺ == Γ″ ~> Γ″ ,, A ⁺ ∙ q[ 𝒑 A , A ]
          coer₀ = ap (λ — → Γ″ ~> Γ″ ,, —) $ sym $ A ⁺∙q[ 𝒑 A ]==
          q₀ = q[ 𝒑 A , A ]
          coer₁ = ap Tm $ ∙-comp== (A ⁺) q₀ (id Γ″)
          coer₂ : Tm (A ⁺⁺) == Tm (A ⁺ ∙ q[ 𝒑 A , A ] ∙ id Γ″)
          coer₂ = ap Tm {r = _==_}(
            proof A ⁺⁺
              === A ⁺⁺ ∙ id Γ″
                :by: ap (λ f → pr₁ f (A ⁺⁺)) $ sym $ id-preserv Γ″
              === A ⁺ ∙ q[ 𝒑 A , A ] ∙ id Γ″
                :by: ap (_∙ id Γ″) $ sym $ A ⁺∙q[ 𝒑 A ]==
            qed)
          coer₃ = CwU-Coer.bar (A ⁺⁺)
          coer₄ = ap Tm $ sym $ A ⁺∙q[ 𝒑 A ]==
          coer₅ = CwU-Coer.〈 q₀ , A ⁺ 〉∘ bar (a₀ ⊙ 𝒑 A)
          coer₆ = ap Tm (
            proof A ⁺
              === A ∙ (id Γ ∘ 𝒑 A)
                :by: ap (A ∙_) $ sym $ left-unit (𝒑 A)
              === A ∙ (𝒑 A ∘ bar a₀ ∘ 𝒑 A)
                :by: ap (λ — → A ∙ (— ∘ 𝒑 A)) $ sym $ p A ∘bar a₀
              === A ∙ (𝒑 A ∘ (bar a₀ ∘ 𝒑 A))
                :by: sym $ ap (A ∙_) $ assoc (𝒑 A)(bar a₀)(𝒑 A)
              === A ⁺ ∙ (bar a₀ ∘ 𝒑 A)
                :by: sym $ ∙-comp== A (𝒑 A) (bar a₀ ∘ 𝒑 A)
            qed)
          f-equiv : q[ q[ 𝒑 A , A ] , A ⁺ ] ∘
                    coe coer₀ (bar (𝒒 A ⊙ 𝒑 (A ⁺))) ∘
                    bar (a₀ ⊙ 𝒑 A)
                    ==
                    〈 bar a₀ ∘ 𝒑 A , coe coer₆ (𝒒 A)  〉
          f-equiv =
            proof q[ q[ 𝒑 A , A ] , A ⁺ ] ∘
                  coe coer₀ (bar (𝒒 A ⊙ 𝒑 (A ⁺))) ∘
                  bar (a₀ ⊙ 𝒑 A)
              === q[ q[ 𝒑 A , A ] , A ⁺ ] ∘
                  〈 id Γ″ , coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺)) 〉 ∘
                  bar (a₀ ⊙ 𝒑 A)
                :by: ap (λ — → q[ q[ 𝒑 A , A ] , A ⁺ ] ∘ — ∘ bar (a₀ ⊙ 𝒑 A)) $
                     subrel {_R_ = Het._==_}{_P_ = _==_} (
                     proof coe coer₀ (bar (𝒒 A ⊙ 𝒑 (A ⁺)))
                       het== bar (𝒒 A ⊙ 𝒑 (A ⁺))
                         :by: coe-eval coer₀ (bar (𝒒 A ⊙ 𝒑 (A ⁺)))
                       het== 〈 id Γ″ , coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺)) 〉
                         :by: 〈,〉het==〈,〉 (Id.refl (id Γ″))
                                        (sym $ A ⁺∙q[ 𝒑 A ]==)
                              (proof coe coer₃ (𝒒 A ⊙ 𝒑 (A ⁺))
                                 het== 𝒒 A ⊙ 𝒑 (A ⁺)
                                   :by: coe-eval coer₃ (𝒒 A ⊙ 𝒑 (A ⁺))
                                 het== coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺))
                                   :by: isym $ coe-eval coer₂ (𝒒 A ⊙ 𝒑 (A ⁺))
                               qed)
                     qed)
                     [: _==_ ]
              === 〈 q₀ ∘ id Γ″ , coe coer₁ (coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺))) 〉 ∘
                  bar (a₀ ⊙ 𝒑 A)
                :by: ap (_∘ bar (a₀ ⊙ 𝒑 A))
                     q[ q[ 𝒑 A , A ] , A ⁺ ]∘〈 id Γ″ , coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺)) 〉
              === 〈 q₀ , coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)) 〉 ∘ bar (a₀ ⊙ 𝒑 A)
                :by: ap (_∘ bar (a₀ ⊙ 𝒑 A)) 〈 right-unit q₀ ,
                     proof coe coer₁ (coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺)))
                       het== coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺))
                         :by: coe-eval coer₁ (coe coer₂ (𝒒 A ⊙ 𝒑 (A ⁺)))
                       het== 𝒒 A ⊙ 𝒑 (A ⁺)
                         :by: coe-eval coer₂ (𝒒 A ⊙ 𝒑 (A ⁺))
                       het== coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺))
                         :by: isym $ coe-eval coer₄ (𝒒 A ⊙ 𝒑 (A ⁺))
                     qed 〉==
              === 〈 q₀ ∘ bar (a₀ ⊙ 𝒑 A) ,
                    coe coer₅ (coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)) ⊙ bar (a₀ ⊙ 𝒑 A)) 〉
                :by: 〈 q₀ , coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)) 〉∘ bar (a₀ ⊙ 𝒑 A)
              === 〈 bar a₀ ∘ 𝒑 A , coe coer₆ (𝒒 A)  〉
                :by: 〈 q[p A ]∘bar a₀ ,
                     proof coe coer₅ (coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)) ⊙ bar (a₀ ⊙ 𝒑 A))
                       het== coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)) ⊙ bar (a₀ ⊙ 𝒑 A)
                         :by: coe-eval coer₅ (
                                coe coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)) ⊙ bar (a₀ ⊙ 𝒑 A))
                       het== 𝒒 A ⊙ 𝒑 (A ⁺) ⊙ bar (a₀ ⊙ 𝒑 A)
                         :by: ⊙==⊙ (Id.refl Γ″)
                                   (subrel $ A ⁺∙q[ 𝒑 A ]==)
                                   (coe-eval coer₄ (𝒒 A ⊙ 𝒑 (A ⁺)))
                                   (Het.refl (bar (a₀ ⊙ 𝒑 A)))
                       het== 𝒒 A ⊙ (𝒑 (A ⁺) ∘ bar (a₀ ⊙ 𝒑 A))
                         :by: ⊙-comp== (𝒒 A) (𝒑 (A ⁺)) (bar (a₀ ⊙ 𝒑 A))
                       het== 𝒒 A ⊙ id (Γ ,, A)
                         :by: ap (𝒒 A ⊙_) ⦃ Relating-all-==-het== ⦄ $
                              p A ⁺ ∘bar a₀ ⊙ 𝒑 A
                       het== 𝒒 A
                         :by: 𝒒 A ⊙id
                       het== coe coer₆ (𝒒 A)
                         :by: isym $ coe-eval coer₆ (𝒒 A)
                     qed 〉==
            qed
-}
