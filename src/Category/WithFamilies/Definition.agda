{-# OPTIONS --exact-split --prop #-}
module Category.WithFamilies.Definition where

open import Category.Fam

open import Category hiding (ℂ)
open import Category.Opposite
open import Functor
open import Construction.Terminal

open import Universes
open import Type.Sum hiding (〈_,_〉)
open import Function
  using (_~_) renaming (id to id-fun; _∘_ to _∘ₛ_)
open import Proof

open import Proposition.Identity.Coercion

record CwF-Explicit (𝒰 𝒱 𝒲 𝒳 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒳) ⁺ ˙ where
  field
    C : Category 𝒰 𝒱
  private
    instance _ = C
  Ctx = obj ⦃ C ⦄

  field
    Ty : (Γ : Ctx) → 𝒲 ˙ -- types
    Tm : {Γ : Ctx}(σ : Ty Γ) → 𝒳 ˙ -- terms

    -- substitution
    Ty-sub : ∀{Γ Δ}(f : Γ ~> Δ) → Ty Δ → Ty Γ
    Tm-sub : ∀{Γ Δ : Ctx}(f : Γ ~> Δ){σ : Ty Δ} → Tm σ → Tm (Ty-sub f σ)
    -- laws
    Ty-Id : ∀{Θ}
      (σ : Ty Θ)
      → ------------------
      Ty-sub (id Θ) σ == σ
    Ty-Comp : ∀{Γ Δ Θ : Ctx}
      (f : Γ ~> Δ)
      (g : Δ ~> Θ)
      (σ : Ty Θ)
      → ----------------------------------------
      Ty-sub (g ∘ f) σ == (Ty-sub f ∘ₛ Ty-sub g) σ
    Tm-Id : ∀{Θ}{σ : Ty Θ}
      → ------------------------
      Tm-sub (id Θ) {σ} ~ id-fun
    Tm-Comp : ∀{Γ Δ Θ : Ctx}
      (f : Γ ~> Δ)
      (g : Δ ~> Θ)
      {σ : Ty Θ}
      → -----------------------
      Tm-sub (g ∘ f) {σ} ~ Tm-sub f ∘ₛ Tm-sub g

    -- empty context
    ⊤ : Terminal
    -- comprehension (of σ)
    -- extend context
    _,,_ : (Γ : Ctx)(σ : Ty Γ) → Ctx
    -- projection (associated to σ)
    -- each non-empty context can be weakened
    𝒑 : ∀{Γ}(σ : Ty Γ) → (Γ ,, σ) ~> Γ
    -- second projection
    -- lookup the last context variable
    𝒗 : ∀{Γ}(σ : Ty Γ) → Tm (Ty-sub (𝒑 σ) σ)
    -- Ty-sub (𝒑 σ) σ : Ty (Γ ,, σ)

    -- extending context morphisms
    -- given that context Γ can create Δ
    -- and that Γ can create term of type (σ in Δ created from Γ)
    -- then Γ can create (Δ ,, σ)
    -- by saving the created term to the last variable
    〈_,_〉 : ∀{Γ Δ : Ctx}{σ : Ty Δ}
      (f : Γ ~> Δ)
      (M : Tm (Ty-sub f σ))
      → --------------------
      Γ ~> (Δ ,, σ)

    -- laws
    -- adding variable of type σ and forgetting it is identity 
    Cons-L : ∀{Γ Δ : Ctx}
      (σ : Ty Δ)
      (f : Γ ~> Δ)
      (M : Tm (Ty-sub f σ))
      → -----------------------
      𝒑 σ ∘ 〈 f , M 〉 == f
    -- saving a term in context and then looking it up
    -- is the same as writing it directly 
    Cons-R : ∀{Γ Δ : Ctx}
      (σ : Ty Δ)
      (f : Γ ~> Δ)
      (M : Tm (Ty-sub f σ))
      → -----------------------
      Tm-sub 〈 f , M 〉 (𝒗 σ) Het.== M
    -- changing context Β into Γ and then changing Γ into (Δ ,, σ)
    -- by changing Γ into Δ and saving a term of type (σ substituted from Δ to Γ)
    -- is the same as
    -- changing context Β into Γ and then Γ into Δ
    -- and saving a term of type changed from (σ substituted from Δ to Γ)
    -- by using the context transformation from Β to Γ 
    Cons-Nat : ∀{Γ Δ Β : Ctx}{σ : Ty Δ}
      (f : Γ ~> Δ)
      (g : Β ~> Γ)
      (M : Tm (Ty-sub f σ))
      → -----------------------
      〈 f , M 〉 ∘ g
      ==
      〈 f ∘ g , coe (ap Tm $ sym $ Ty-Comp g f σ) (Tm-sub g M) 〉
    -- the new context created from (Δ ,, σ)
    -- by forgetting σ to get Δ
    -- and by looking up σ variable to get term of type σ
    -- is identical to the original context
    Cons-Id : ∀{Δ : Ctx}
      (σ : Ty Δ)
      → --------------------------
      〈 𝒑 σ , 𝒗 σ 〉 == id (Δ ,, σ)

open import Logic using (∃!; _∧_)

record CwF (𝒰 𝒱 𝒲 𝒳 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒳) ⁺ ˙ where
  infix 182 _∙_
  field
    ℂ : Category 𝒰 𝒱
    ℱ : Functor (ℂ ᵒᵖ) (Fam 𝒲 𝒳)
  private
    instance _ = ℂ; _ = ℱ

  Ty : (Δ : obj) → 𝒲 ˙
  Ty Δ = pr₁ (F₀ Δ)

  Tm : {Δ : obj}(A : Ty Δ) → 𝒳 ˙
  Tm {Δ} = pr₂ (F₀ Δ)

  Ty-sub : ∀{Γ Δ}(f : Γ ~> Δ) → Ty Δ → Ty Γ
  Ty-sub f = pr₁ (F₁ f)
  
  Tm-sub : ∀{Γ Δ : obj}(f : Γ ~> Δ){σ : Ty Δ} → Tm σ → Tm (Ty-sub f σ)
  Tm-sub f {σ} = pr₂ (F₁ f) σ

  field
    ⊤ : Terminal
    _∙_ : (Δ : obj)(A : Ty Δ) → obj
    𝒑 : (Δ : obj)(A : Ty Δ) → Δ ∙ A ~> Δ
    𝒒 : (Δ : obj)(A : Ty Δ) → Tm (Ty-sub (𝒑 Δ A) A)
    univ-prop : ∀{Γ Δ : obj}{A : Ty Δ}
      (f : Γ ~> Δ)
      (t : Tm (Ty-sub f A))
      → -----------------------------
      ∃! λ (〈f,t〉 : Γ ~> (Δ ∙ A)) →
      𝒑 Δ A ∘ 〈f,t〉 == f ∧
      Tm-sub 〈f,t〉 (𝒒 Δ A) Het.== t
