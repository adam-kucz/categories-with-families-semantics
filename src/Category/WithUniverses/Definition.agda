{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.Definition where

open import Category hiding (ℂ)
open import Category.Opposite
open import Category.Fam
open import Example.Set'
open import Functor
open import Construction.Terminal

open import Universes
open import Type.Sum hiding (〈_,_〉)
open import Data.Nat hiding (_⊔_; ⊤)
open import Function using (flip; _~_) renaming (id to id-fun)
open import Proof

open import Proposition.Identity.Coercion

variable
  s : ℕ

record CwU-Explicit (𝒰 𝒱 𝒲 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  field
    ℂ : Category 𝒰 𝒱

  Ctx = obj ⦃ ℂ ⦄
  Types = Set' {𝒲}
  instance _ = ℂ

  field
    ⦃ ⋄ ⦄ : Terminal
    Ctx→Ty : (s : ℕ) → Functor (ℂ ᵒᵖ) Types

  Ty : ∀ (s : ℕ) Γ → obj ⦃ Types ⦄
  Ty s = F₀ ⦃ Ctx→Ty s ⦄

  -- use context Δ to define Γ
  -- so any type in Γ can be transformed to a type in Δ
  _∙_ : ∀ {Γ Δ}
    (A : Ty s Γ)
    (f : Δ ~> Γ)
    → --------------------------
    Ty s Δ
  _∙_ {s} = flip (F₁ ⦃ Ctx→Ty s ⦄)

  Terms = Types

  field
    Tm : {Γ : Ctx}(A : Ty s Γ) → obj ⦃ Terms ⦄
    Tm-sub : ∀ {Γ Δ}{A : Ty s Γ}
      (f : Δ ~> Γ)
      → ----------------------------------------
      Tm A → Tm (A ∙ f)

  -- use context Δ to define Γ
  -- so any term of type A in Γ
  -- can be transformed to a term of type (A ∙ f) in Δ
  _⊙_ : ∀ {Γ Δ}{A : Ty s Γ}
    (a : Tm A)
    (f : Δ ~> Γ)
    → --------------------------
    Tm (A ∙ f)
  _⊙_ {s} = flip Tm-sub

  field
    Tm-Id : ∀ {Γ}{A : Ty s Γ}
      (a : Tm A)
      → --------------------------------------------------
      a ⊙ id Γ Het.== a

    Tm-Comp : ∀ {X Y Z}{A : Ty s X}
      (a : Tm A)
      (f : Y ~> X)
      (g : Z ~> Y)
      → --------------------------------------------------
      a ⊙ (f ∘ g) Het.== (a ⊙ f) ⊙ g

  -- comprehension structure
  field
    -- operations
    -- extend context
    _,,_ : (X : obj)(A : Ty s X) → obj
    -- context weakening
    𝒑 : ∀ {X}(A : Ty s X) → (X ,, A) ~> X
    -- lookup the last context variable
    𝒒 : ∀ {X}(A : Ty s X) → Tm (A ∙ 𝒑 A)
    -- extending context morphisms
    -- given that context Γ can create Δ
    -- and that Γ can create term of type (A in Δ created from Γ)
    -- then Γ can create (Δ ,, A)
    -- by saving the created term to the last variable
    〈_,_〉 : ∀ {Γ Δ}{A : Ty s Γ}
      (f : Δ ~> Γ)
      (a : Tm (A ∙ f))
      → --------------------------------------
      Δ ~> (Γ ,, A)
    -- laws
    -- adding variable of type A and forgetting it is identity 
    Cons-L : ∀ {Γ Δ}{A : Ty s Γ}
      (f : Δ ~> Γ)
      (a : Tm (A ∙ f))
      → ----------------------------------------
      𝒑 A ∘ 〈 f , a 〉 == f
    -- saving a term in context and then looking it up
    -- is the same as writing it directly 
    Cons-R : ∀{Γ Δ}{A : Ty s Γ}
      (f : Δ ~> Γ)
      (a : Tm (A ∙ f))
      → ----------------------------------------
      𝒒 A ⊙ 〈 f , a 〉 Het.== a
    -- changing context Β into Γ and then changing Γ into (Δ ,, σ)
    -- by changing Γ into Δ and saving a term of type (σ substituted from Δ to Γ)
    -- is the same as
    -- changing context Β into Γ and then Γ into Δ
    -- and saving a term of type changed from (σ substituted from Δ to Γ)
    -- by using the context transformation from Β to Γ 
    Cons-Nat : ∀ {Γ Δ Β}{A : Ty s Γ}
      (f : Δ ~> Γ)
      (a : Tm (A ∙ f))
      (g : Β ~> Δ)
      → ----------------------------------------
      〈 f , a 〉 ∘ g
      ==
      〈 f ∘ g ,
        coe (ap (λ — → Tm (— A))
              $ sym $ ∘-preserv ⦃ Ctx→Ty s ⦄ g f)
        (a ⊙ g) 〉
    -- the new context created from (Γ ,, A)
    -- by forgetting A to get Γ
    -- and by looking up A variable to get term of type A
    -- is identical to the original context
    Cons-Id : ∀ {Γ}(A : Ty s Γ)
      → ----------------------------------------
      〈 𝒑 A , 𝒒 A 〉 == id (Γ ,, A)


  field
    𝑈 : (Γ : obj)(s : ℕ) → Ty (s +1) Γ
    hierarchy : (Γ : Ctx)(s : ℕ)
      → ----------------------------------------
      Ty s Γ == Tm (𝑈 Γ s)
    universe-preserv : {Γ Δ : Ctx}
      (s : ℕ)
      (f : Δ ~> Γ)
      → ----------------------------------------
      𝑈 Γ s ∙ f == 𝑈 Δ s
    action-agreement : ∀ {Γ Δ s}
      (A : Ty s Γ)
      (f : Δ ~> Γ) →
      let simp : Tm (𝑈 Γ s ∙ f) == Ty s Δ
          simp =
            proof Tm (𝑈 Γ s ∙ f)
              === Tm (𝑈 Δ s)
                :by: ap Tm $ universe-preserv s f
              === Ty s Δ
                :by: sym $ hierarchy Δ s
            qed
      in  ----------------------------------------
      A ∙ f == coe simp (coe (hierarchy Γ s) A ⊙ f)

open import Proposition.Sum
open import Logic using (∃!; _∧_; ∧left; ∧right)

open import Axiom.UniqueChoice

record CwU (𝒰 𝒱 𝒲 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  field
    ℂ : Category 𝒰 𝒱
    ℱ : (s : ℕ) → Functor (ℂ ᵒᵖ) (Fam 𝒲 𝒲)
  private
    instance _ = ℂ; _ = λ {s} → ℱ s

  Ctx = obj ⦃ ℂ ⦄
  
  Ty : (s : ℕ)(Δ : Ctx) → 𝒲 ˙
  Ty s Δ = pr₁ (F₀ ⦃ ℱ s ⦄ Δ)

  Tm : {Δ : Ctx}(A : Ty s Δ) → 𝒲 ˙
  Tm {_}{Δ} = pr₂ (F₀ Δ)

  Ty-sub : ∀{Γ Δ}(f : Γ ~> Δ) → Ty s Δ → Ty s Γ
  Ty-sub f = pr₁ (F₁ f)
  
  Tm-sub : ∀{Γ Δ}(f : Γ ~> Δ){σ : Ty s Δ} → Tm σ → Tm (Ty-sub f σ)
  Tm-sub f {σ} = pr₂ (F₁ f) σ

  _∙_ : ∀ {Γ Δ}
    (A : Ty s Γ)
    (f : Δ ~> Γ)
    → --------------------------
    Ty s Δ
  A ∙ f = Ty-sub f A

  _⊙_ : ∀ {Γ Δ}{A : Ty s Γ}
    (a : Tm A)
    (f : Δ ~> Γ)
    → --------------------------
    Tm (A ∙ f)
  a ⊙ f = Tm-sub f a

  infix 182 _,,_
  field
    ⦃ ⊤ ⦄ : Terminal
    _,,_ : (Δ : Ctx)(A : Ty s Δ) → Ctx
    𝒑 : {Δ : Ctx}(A : Ty s Δ) → Δ ,, A ~> Δ
    𝒒 : {Δ : Ctx}(A : Ty s Δ) → Tm (Ty-sub (𝒑 A) A)
    univ-prop : ∀{Γ Δ}{A : Ty s Δ}
      (f : Γ ~> Δ)
      (t : Tm (Ty-sub f A))
      → -----------------------------
      ∃! λ (〈f,t〉 : Γ ~> (Δ ,, A)) →
      𝒑 A ∘ 〈f,t〉 == f ∧
      Tm-sub 〈f,t〉 (𝒒 A) Het.== t

  〈_,_〉 : ∀{Γ Δ}{A : Ty s Δ}
    (f : Γ ~> Δ)
    (t : Tm (Ty-sub f A))
    → --------------------
    Γ ~> (Δ ,, A)
  〈 f , t 〉 = elem (!choice (univ-prop f t))

  〈_,_〉-prop : ∀{Γ Δ}{A : Ty s Δ}
    (f : Γ ~> Δ)
    (t : Tm (Ty-sub f A))
    → --------------------
    𝒑 A ∘ 〈 f , t 〉 == f ∧ Tm-sub 〈 f , t 〉 (𝒒 A) Het.== t
  〈 f , t 〉-prop = ∧left (prop (!choice (univ-prop f t)))

  〈_,_〉-uniq : ∀{Γ Δ}{A : Ty s Δ}
    (f : Γ ~> Δ)
    (t : Tm (Ty-sub f A))
    → --------------------
    _
  〈 f , t 〉-uniq = ∧right (prop (!choice (univ-prop f t)))


  field
    𝑈 : (Γ : Ctx)(s : ℕ) → Ty (s +1) Γ
    hierarchy : (Γ : Ctx)(s : ℕ)
      → ----------------------------------------
      Ty s Γ == Tm (𝑈 Γ s)
    𝑈-preserv : ∀{Γ Δ}
      (s : ℕ)
      (f : Δ ~> Γ)
      → ----------------------------------------
      𝑈 Γ s ∙ f == 𝑈 Δ s
    Ty-sub==Tm-sub : ∀{Γ Δ : Ctx}
      (A : Ty s Γ)
      (f : Δ ~> Γ) →
      A ∙ f Het.== coe (hierarchy Γ s) A ⊙ f
