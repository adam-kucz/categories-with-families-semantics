{-# OPTIONS --exact-split --prop #-}
module CategoryWithFamilies.Equivalence where

open import CategoryWithFamilies.Definition
open import Category.Fam

open import Category hiding (ℂ)
open import Functor

open import Universes
open import Proposition.Sum hiding (_,_)
open import Type.Sum hiding (〈_,_〉)
open import Function
  using (_~_; ==→~; Bijection; forw; back; bi-inverse)
  renaming (id to id-fun; _∘_ to _∘ₛ_)
open import Logic hiding (⊤; _,_)
open import Proof
open import Proposition.Proof hiding (id)

open import Proposition.Identity.Coercion
open import Axiom.FunctionExtensionality
open import Axiom.UniqueChoice

CwF-Explicit-is-CwF :
  Bijection (CwF-Explicit 𝒰 𝒱 𝒲 𝒳) (CwF 𝒰 𝒱 𝒲 𝒳)
forw ⦃ CwF-Explicit-is-CwF ⦄ cwf-exp = record
  { ℂ = C
  ; ℱ = [F₀= (λ X → Ty X , Tm)
        ,F₁= (λ f → Ty-sub f , λ x → Tm-sub f {x})
        ,id-pres= (λ X → Σ==
          (subrel $ fun-ext λ x → subrel $ Ty-Id x)
          {!λ σ → fun-ext (Tm-Id {X}{σ})!})
        ,∘-pres= {!!}
        ]
  ; ⊤ = ⊤
  ; _∙_ = _,,_
  ; 𝒑 = λ _ → 𝒑
  ; 𝒒 = λ _ → 𝒗
  ; univ-prop = λ {_}{_}{A} f t →
    〈 f , t 〉 ∃., (
    Cons-L A f t _∧_.,
    Cons-R A f t _∧_.,
    λ { y (p _∧_., q) →
      let instance _ = C
          coercion : Tm (Ty-sub y (Ty-sub (𝒑 A) A)) == Tm (Ty-sub (𝒑 A ∘ y) A)
          coercion = ap Tm $ sym $ Ty-Comp y (𝒑 A) A
      in
      proof y
        === id _ ∘ y         :by: sym $ left-unit y
        === 〈 𝒑 A , 𝒗 A 〉 ∘ y :by: ap (_∘ y) $ sym $ Cons-Id A
        === 〈 𝒑 A ∘ y , coe coercion (Tm-sub y (𝒗 A)) 〉
          :by: Cons-Nat (𝒑 A) y (𝒗 A)
        === 〈 f , t 〉
          :by: subrel $ Id.ap2 〈_,_〉 p (
            proof coe coercion (Tm-sub y (𝒗 A))
              〉 Het._==_ 〉 Tm-sub y (𝒗 A)
                :by: coe-eval coercion (Tm-sub y (𝒗 A))
              〉 Het._==_ 〉 t
                :by: q
            qed)
      qed})
  }
  where open CwF-Explicit cwf-exp
back ⦃ CwF-Explicit-is-CwF ⦄ cwf = record
  { C = ℂ
  ; Ty = Ty
  ; Tm = Tm
  ; Ty-sub = Ty-sub
  ; Tm-sub = Tm-sub
  ; Ty-Id = ty-id
  ; Ty-Comp = ty-comp
  ; Tm-Id = λ {Θ}{σ} t → let instance _ = ℱ; _ = ℂ in
    let coercion = λ x → ap (pr₂ (F₀ Θ)) (sym $ ty-id x) in
    proof pr₂ (F₁ (id Θ)) σ t
      〉 _==_ 〉 coe (coercion σ) t
        :by: ap (λ — → — σ t) (subrel {_R_ = Het._==_}{_P_ = _==_} (
          proof pr₂ (F₁ ⦃ ℱ ⦄ (id Θ))
            〉 Het._==_ 〉 (λ x → id-fun)
              :by: ∧right (from-Σ== (id-preserv Θ))
            〉 Het._==_ 〉 (λ x t → coe (coercion x) t)
              :by: fun-ext (λ x → fun-ext λ x₁ → isym $ coe-eval (coercion x) x₁)
          qed))
      〉 Het._==_ 〉 t
        :by: coe-eval (coercion σ) t
    qed
  ; Tm-Comp = {!!}
  ; ⊤ = ⊤
  ; _,,_ = _∙_
  ; 𝒑 = λ {Γ} → 𝒑 Γ
  ; 𝒗 = λ {Γ} → 𝒒 Γ
  ; 〈_,_〉 = λ f M → elem [ f , M ]
  ; Cons-L = λ _ f M → ∧left $ ∧left $ prop [ f , M ]
  ; Cons-R = λ _ f M → ∧right $ ∧left $ prop [ f , M ]
  ; Cons-Nat = {!!}
  ; Cons-Id = λ {Δ} σ →
    sym $
    ∧right (prop [ 𝒑 Δ σ , 𝒒 Δ σ ]) (id (Δ ∙ σ))
    (right-unit (𝒑 _ σ) _∧_.,
     (proof pr₂ (F₁ (id (Δ ∙ σ))) _ (𝒒 Δ σ)
        〉 Het._==_ 〉 pr₂ (id ⦃ Fam _ _ ⦄ (F₀ (Δ ∙ σ))) _ (𝒒 Δ σ)
          :by: ap (λ — → pr₂ — _ (𝒒 Δ σ)) $ id-preserv (Δ ∙ σ)
        〉 Het._==_ 〉 𝒒 _ σ
          :by: Het.refl _
      qed))
  }
  where open CwF cwf
        instance _ = ℱ; _ = ℂ
        ty-id : {Θ : obj}
          (σ : (pr₁ ∘ₛ F₀) Θ)
          → -----------------------
          (pr₁ ∘ₛ F₁) (id Θ) σ == σ
        ty-id {Θ} σ =
          have F₁ (id Θ) == (id-fun , λ _ → id-fun) :from: id-preserv Θ
          ⟶ pr₁ (F₁ (id Θ)) == id-fun              :by: ∧left ∘ₚ from-Σ==
          ⟶ pr₁ (F₁ (id Θ)) σ == σ                 :by: ap (λ — → — σ)
        ty-comp : ∀ {Γ Δ Θ : obj}
          (f : Γ ~> Δ)
          (g : Δ ~> Θ)
          (σ : (pr₁ ∘ₛ F₀) Θ)
          → ------------------------------------------------------------
          (pr₁ ∘ₛ F₁) (g ∘ f) σ == (Ty-sub f ∘ₛ Ty-sub g) σ
        ty-comp {Γ}{Δ}{Θ}f g σ = 
          have F₁ (g ∘ f) == compose (Fam _ _){C = F₀ Γ}(F₁ f)(F₁ g)
            :from: ∘-preserv f g
          ⟶ pr₁ (F₁ (g ∘ f)) == pr₁ (F₁ f) ∘ₛ pr₁ (F₁ g)
            :by: ∧left ∘ₚ from-Σ==
          ⟶ (pr₁ ∘ₛ F₁) (g ∘ f) σ == (pr₁ (F₁ f) ∘ₛ pr₁ (F₁ g)) σ
            :by: ap (λ — → — σ)
        [_,_] : {Γ Δ : obj}{A : Ty Δ}
          (f : Γ ~> Δ)
          (t : pr₂ (F₀ Γ) (pr₁ (F₁ f) A)) → _
        [ f , M ] = !choice (univ-prop f M)
        
bi-inverse ⦃ CwF-Explicit-is-CwF ⦄ = {!!}
