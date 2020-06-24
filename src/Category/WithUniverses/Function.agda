{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.Function where

open import Category.WithUniverses.Definition

open import Universes hiding (_⁺; _⁺⁺; A; B)

open import Category hiding (ℂ)
open import Functor

open import Proposition.Identity.Coercion

module WithCwU (C : CwU 𝒰 𝒱 𝒲) where
  open CwU C
  open Variable
  instance _ = ℂ; _ = λ {s} → ℱ s

  infixl 182 _+,,_
  data _,,…==_ : (Δ Γ : Ctx) → 𝒰 ⊔ 𝒲 ˙ where
    just : (Γ : Ctx) → Γ ,,…== Γ
    _+,,_ :
      (p : Γ ,,…== Δ)
      (A : Ty s Δ)
      → ------------------------------
      Γ ,,…== Δ ,, A

  wk-mor : (p : Γ ,,…== Δ) → Δ ~> Γ
  wk-mor (just Γ) = id Γ
  wk-mor (just Γ +,, A) = 𝒑 A
  wk-mor (p@(_ +,, _) +,, A) = wk-mor p ∘ 𝒑 A

  wk-bar : {A : Ty s Γ}
    (a : Tm A)
    (p : Γ ,,…== Δ)
    → -------------------------
    Δ ~> Δ ,, A ∙ wk-mor p
  wk-bar a p = bar (a ⊙ wk-mor p)

  open import Type.Sum hiding (_,_; 〈_,_〉)
  open import Logic
  open import Proof

  wk-bar∘bar : {A : Ty s Γ}(a : Tm A)
    → --------------------------------------------------
    wk-bar a (just Γ +,, A) ∘ bar a == bar (𝒒 A) ∘ bar a
  wk-bar∘bar {Γ = Γ}{A} a =
    proof wk-bar a (just Γ +,, A) ∘ bar a
      === 〈 id (Γ ,, A) , coe coer₀ (a ⊙ 𝒑 A) 〉 ∘ bar a
        :by: Id.refl _
      === 〈 id (Γ ,, A) ∘ bar a ,
            coe coer₁ (coe coer₀ (a ⊙ 𝒑 A) ⊙ bar a) 〉
        :by: 〈 id (Γ ,, A) , coe coer₀ (a ⊙ 𝒑 A) 〉∘ bar a
      === 〈 id (Γ ,, A) ∘ bar a , coe coer₁ (coe coer₀ (𝒒 A) ⊙ bar a) 〉
        :by: ap (λ — → 〈 id (Γ ,, A) ∘ bar a , coe coer₁ — 〉) $
             subrel {_R_ = Het._==_}{_P_ = _==_} (
             proof coe coer₀ (a ⊙ 𝒑 A) ⊙ bar a
               het== a ⊙ 𝒑 A ⊙ bar a
                 :by: ⊙==⊙ (Id.refl _)(
                        subrel {_R_ = _==_} $ ap (λ f → pr₁ f (A ⁺)) $
                        id-preserv (Γ ,, A))
                       (coe-eval coer₀ (a ⊙ 𝒑 A))
                       (Het.refl (bar a))
               het== a ⊙ (𝒑 A ∘ bar a)
                 :by: ⊙-comp== a (𝒑 A) (bar a)  
               het== a ⊙ id Γ
                 :by: ⊙==⊙ (Id.refl _)(Het.refl _)(Het.refl a)
                        (subrel $ p A ∘bar a) 
               het== a
                 :by: a ⊙id
               het== coe (Coer.bar A) a
                 :by: isym $ coe-eval (Coer.bar A) a
               het== 𝒒 A ⊙ bar a
                 :by: isym $ ∧right 〈 id Γ , coe (Coer.bar A) a 〉-prop
               het== coe coer₀ (𝒒 A) ⊙ bar a
                 :by: ⊙==⊙ (Id.refl _)(
                        subrel {_R_ = _==_} $ ap (λ f → pr₁ f (A ⁺)) $
                        sym $ id-preserv (Γ ,, A))
                       (isym $ coe-eval coer₀ (𝒒 A))
                       (Het.refl _)
             qed)
      === 〈 id (Γ ,, A) , coe coer₀ (𝒒 A) 〉 ∘ bar a
        :by: sym $ 〈 id (Γ ,, A) , coe coer₀ (𝒒 A) 〉∘ bar a
      === bar (𝒒 A) ∘ bar a
        :by: Id.refl _
    qed
    where coer₀ = Coer.bar (A ⁺)
          coer₁ = Coer.〈 id (Γ ,, A) , A ⁺ 〉∘ bar a
