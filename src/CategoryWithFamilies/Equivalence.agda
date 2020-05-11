{-# OPTIONS --exact-split --prop #-}
module CategoryWithFamilies.Equivalence where

open import CategoryWithFamilies.Definition
open import Category.Fam

open import Category hiding (ℂ)
open import Functor

open import Universes
open import Proposition.Sum hiding (_,_)
open import Type.Sum hiding (〈_,_〉)
open import Function using
  ( _~_; ==→~
  ; Bijection; forw; back; bi-inverse
  ; inverse-left; inverse-right; left-inv; right-inv)
  renaming (id to id-fun; _∘_ to _∘ₛ_)
open import Logic hiding (⊤; _,_)
open import Proof
open import Proposition.Proof hiding (id)

open import Proposition.Identity.Coercion
open import Axiom.FunctionExtensionality
open import Axiom.UniqueChoice

-- CwF-Explicit== :
--   {C₀ C₁ : Category 𝒰 𝒱}
--   (p₀ : C₀ == C₁)
--   {Ty₀ : obj ⦃ C₀ ⦄ → 𝒲 ˙}{Ty₁ : obj ⦃ C₀ ⦄ → 𝒲 ˙}
--   (p₁ : Ty₀ Het.== Ty₁)
--   (p₂ : (λ Γ → Tm cwf-exp₁ {Γ}) Het.== (λ Γ → Tm cwf-exp₂ {Γ}))
--   -- (p₃ : (λ Γ Δ → Ty-sub cwf-exp₁ {Γ}{Δ}) Het.==
--   --       (λ Γ Δ → Ty-sub cwf-exp₂ {Γ}{Δ}))
--   -- (p₄ : (λ Γ Δ → Tm-sub cwf-exp₁ {Γ}{Δ}) Het.==
--   --       (λ Γ Δ → Tm-sub cwf-exp₂ {Γ}{Δ}))
--   -- (p₅ : _,,_ cwf-exp₁ Het.== _,,_ cwf-exp₂)
--   -- (p₆ : (λ Γ → 𝒑 cwf-exp₁ {Γ}) Het.== (λ Γ → 𝒑 cwf-exp₂ {Γ}))
--   -- (p₇ : (λ Γ → 𝒗 cwf-exp₁ {Γ}) Het.== (λ Γ → 𝒗 cwf-exp₂ {Γ}))
--   -- (p₈ : (λ Γ Δ σ → 〈_,_〉 cwf-exp₁ {Γ}{Δ}{σ}) Het.==
--   --       (λ Γ Δ σ → 〈_,_〉 cwf-exp₂ {Γ}{Δ}{σ}))
--   → ---------------------------------------------
--   cwf-exp₁ == cwf-exp₂
-- CwF-Explicit== cwf-exp₁ cwf-exp₂ (Id-refl _) (Het.refl _) (Het.refl _) p₃ p₄ p₅ p₆ p₇ p₈ = {!!}

CwF-Explicit-is-CwF :
  Bijection (CwF-Explicit 𝒰 𝒱 𝒲 𝒳) (CwF 𝒰 𝒱 𝒲 𝒳)
forw ⦃ CwF-Explicit-is-CwF ⦄ cwf-exp = record
  { ℂ = C
  ; ℱ = [F₀= (λ X → Ty X , Tm)
        ,F₁= (λ f → Ty-sub f , λ x → Tm-sub f {x})
        ,id-pres= (λ X → Σ==
          (subrel $ fun-ext λ σ → subrel $ Ty-Id σ)
          (fun-ext λ _ → fun-ext λ x → Tm-Id x))
        ,∘-pres= (λ g f → Σ==
          (subrel $ fun-ext λ σ → subrel $ Ty-Comp g f σ)
          (fun-ext λ _ → fun-ext λ x → Tm-Comp g f x))
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
  ; Tm-Comp = λ {Γ} f g {σ} x → 
    proof pr₂ (F₁ (g ∘ f)) σ x
      〉 Het._==_ 〉 pr₂ (compose (Fam _ _){C = F₀ Γ}(F₁ f)(F₁ g)) σ x
        :by: ap (λ — → pr₂ — σ x) $ ∘-preserv f g
      〉 Het._==_ 〉 (Tm-sub f ∘ₛ Tm-sub g) x
        :by: Het.refl _
    qed
  ; ⊤ = ⊤
  ; _,,_ = _∙_
  ; 𝒑 = λ {Γ} → 𝒑 Γ
  ; 𝒗 = λ {Γ} → 𝒒 Γ
  ; 〈_,_〉 = λ f M → elem [ f , M ]
  ; Cons-L = λ _ → left-[_,_]
  ; Cons-R = λ _ → right-[_,_]
  ; Cons-Nat = λ {_}{Δ}{Β}{σ} f g M →
    let coercion : Tm (Ty-sub g (Ty-sub f σ)) == Tm (Ty-sub (f ∘ g) σ)
        coercion = ap Tm $ sym $ ty-comp g f σ
    in
    ∧right (prop [ f ∘ g , coe coercion (Tm-sub g M) ])
      (elem [ f , M ] ∘ g)
      ((proof 𝒑 Δ σ ∘ (elem [ f , M ] ∘ g)
          === 𝒑 Δ σ ∘ elem [ f , M ] ∘ g   :by: assoc (𝒑 Δ σ) _ g
          === f ∘ g
            :by: ap (_∘ g) $ left-[ f , M ]
        qed) _∧_.,
       (proof Tm-sub (elem [ f , M ] ∘ g) (𝒒 Δ σ)
         〉 Het._==_ 〉 pr₂ (F₁ (elem [ f , M ] ∘ g)) _ (𝒒 Δ σ)
           :by: Het.refl _
         〉 Het._==_ 〉 pr₂ (compose (Fam _ _){C = F₀ Β}
                            (F₁ g)
                            (F₁ (elem [ f , M ])))
                      _ (𝒒 Δ σ)
           :by: ap (λ — → pr₂ — _ (𝒒 Δ σ)) $ ∘-preserv g (elem [ f , M ])
         〉 Het._==_ 〉 pr₂ (F₁ g) (Ty-sub (elem [ f , M ]) (Ty-sub (𝒑 Δ σ) σ))
                                (Tm-sub (elem [ f , M ]) (𝒒 Δ σ))
           :by: Het.refl _
         〉 Het._==_ 〉 pr₂ (F₁ g) (Ty-sub f σ) M
           :by: Id.ap2 (pr₂ (F₁ g))
                  (proof (Ty-sub (elem [ f , M ]) ∘ₛ Ty-sub (𝒑 Δ σ)) σ
                     === Ty-sub (𝒑 Δ σ ∘ elem [ f , M ]) σ
                       :by: ap (λ — → pr₁ — σ) $
                            sym (∘-preserv (elem [ f , M ]) (𝒑 Δ σ))
                     === Ty-sub f σ
                       :by: ap (λ — → Ty-sub — σ) left-[ f , M ]
                   qed)
                  (right-[ f , M ])
         〉 Het._==_ 〉 coe coercion (Tm-sub g M)
           :by: isym $ coe-eval coercion (Tm-sub g M)
        qed))
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
        left-[_,_] : ∀{Γ Δ : obj}{σ : Ty Δ}
          (f : Γ ~> Δ)
          (M : Tm (Ty-sub f σ))
          → -----------------------
          𝒑 Δ σ ∘ elem [ f , M ] == f
        left-[ f , M ] = ∧left $ ∧left $ prop [ f , M ]
        right-[_,_] : ∀{Γ Δ : obj}{σ : Ty Δ}
          (f : Γ ~> Δ)
          (M : Tm (Ty-sub f σ))
          → -----------------------
          Tm-sub (elem [ f , M ]) (𝒒 Δ σ) Het.== M
        right-[ f , M ] = ∧right $ ∧left $ prop [ f , M ]

left-inv ⦃ inverse-left ⦃ bi-inverse ⦃ CwF-Explicit-is-CwF ⦄ ⦄ ⦄ x = {!!}
right-inv ⦃ inverse-right ⦃ bi-inverse ⦃ CwF-Explicit-is-CwF ⦄ ⦄ ⦄ x = {!!}
