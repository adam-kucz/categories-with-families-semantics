{-# OPTIONS --exact-split --prop #-}
module CategoryWithUniverses where

open import Category hiding (ℂ)
open import Category.Opposite
open import Example.Set'
open import Functor
open import Construction.Terminal

open import Universes
open import Type.Sum hiding (〈_,_〉)
open import Data.Nat hiding (_⊔_)
open import Function using (flip; _~_) renaming (id to id-fun)
open import Proof

open import Proposition.Identity.Coercion

variable
  s : ℕ

record CwU (𝒰 𝒱 𝒲 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  field
    ℂ : Category 𝒰 𝒱

  Ctx = obj ⦃ ℂ ⦄
  instance _ = ℂ

  field
    ⦃ 𝟙-ℂ ⦄ : Terminal
    presheaf : (s : ℕ) → Functor (ℂ ᵒᵖ) (Set' {𝒲})

  _∙_ : ∀ {X Y}
    (A : F₀ ⦃ presheaf s ⦄ X)
    (f : Y ~> X)
    → --------------------------
    F₀ ⦃ presheaf s ⦄ Y
  _∙_ {s} = flip (F₁ ⦃ presheaf s ⦄)

  field
    ℂ[_⊢_] : (X : Ctx)(A : F₀ ⦃ presheaf s ⦄ X) → obj ⦃ Set' {𝒲} ⦄
    presheaf-structure-F : ∀ {X Y}{A : F₀ ⦃ presheaf s ⦄ X}
      (f : Y ~> X)
      → ----------------------------------------
      ℂ[ X ⊢ A ] → ℂ[ Y ⊢ A ∙ f ]

  _⊙_ : ∀ {X Y}{A : F₀ ⦃ presheaf s ⦄ X}
    (a : ℂ[ X ⊢ A ])
    (f : Y ~> X)
    → --------------------------
    ℂ[ Y ⊢ A ∙ f ]
  _⊙_ {s} = flip presheaf-structure-F

  field
    presheaf-structure-id : ∀ {X}{A : F₀ ⦃ presheaf s ⦄ X}
      (a : ℂ[ X ⊢ A ])
      → --------------------------------------------------
      a ⊙ id X Het.== a

    presheaf-structure-compose : ∀ {X Y Z}{A : F₀ ⦃ presheaf s ⦄ X}
      (a : ℂ[ X ⊢ A ])
      (f : Y ~> X)
      (g : Z ~> Y)
      → --------------------------------------------------
      a ⊙ (f ∘ g) Het.== (a ⊙ f) ⊙ g

  -- comprehension structure
  field
    -- operations
    _,,_ : (X : obj)(A : F₀ ⦃ presheaf s ⦄ X) → obj
    𝒑 : ∀ {X}(A : F₀ ⦃ presheaf s ⦄ X) → (X ,, A) ~> X
    𝒒 : ∀ {X}(A : F₀ ⦃ presheaf s ⦄ X) → ℂ[ X ,, A ⊢ A ∙ 𝒑 A ]
    〈_,_〉 : ∀ {X Y}{A : F₀ ⦃ presheaf s ⦄ X}
      (f : Y ~> X)
      (a : ℂ[ Y ⊢ A ∙ f ])
      → --------------------------------------
      Y ~> (X ,, A)
    -- laws
    projection-𝒑-law : ∀ {X Y}{A : F₀ ⦃ presheaf s ⦄ X}
      (f : Y ~> X)
      (a : ℂ[ Y ⊢ A ∙ f ])
      → ----------------------------------------
      𝒑 A ∘ 〈 f , a 〉 == f
    projection-𝒒-law : ∀ {X Y}{A : F₀ ⦃ presheaf s ⦄ X}
      (f : Y ~> X)
      (a : ℂ[ Y ⊢ A ∙ f ])
      → ----------------------------------------
      𝒒 A ⊙ 〈 f , a 〉 Het.== a
    composition-law : ∀ {X Y Z}{A : F₀ ⦃ presheaf s ⦄ X}
      (f : Y ~> X)
      (a : ℂ[ Y ⊢ A ∙ f ])
      (g : Z ~> Y)
      → ----------------------------------------
      〈 f , a 〉 ∘ g
      ==
      〈 f ∘ g ,
        coe (ap (λ — → ℂ[ Z ⊢ — A ])
              $ sym $ ∘-preserv ⦃ presheaf s ⦄ g f)
        (a ⊙ g) 〉
    identity-law : ∀ {X}(A : F₀ ⦃ presheaf s ⦄ X)
      → ----------------------------------------
      〈 𝒑 A , 𝒒 A 〉 == id (X ,, A)


  field
    𝑈 : (X : obj)(s : ℕ) → F₀ ⦃ presheaf (s +1) ⦄ X
    hierarchy : (X : obj)(s : ℕ)
      → ----------------------------------------
      F₀ ⦃ presheaf s ⦄ X == ℂ[ X ⊢ 𝑈 X s ]
    ∙-left-identity : {X Y : obj}
      (s : ℕ)
      (f : Y ~> X)
      → ----------------------------------------
      𝑈 X s ∙ f == 𝑈 Y s
    action-agreement : ∀ {X Y s}
      (A : F₀ ⦃ presheaf s ⦄ X)
      (f : Y ~> X) →
      let simp : ℂ[ Y ⊢ 𝑈 X s ∙ f ] == F₀ ⦃ presheaf s ⦄ Y
          simp =
            proof ℂ[ Y ⊢ 𝑈 X s ∙ f ]
              === ℂ[ Y ⊢ 𝑈 Y s ]      :by: ap ℂ[ Y ⊢_] $ ∙-left-identity s f
              === F₀ ⦃ presheaf s ⦄ Y :by: sym $ hierarchy Y s
            qed
      in  ----------------------------------------
      A ∙ f == coe simp (coe (hierarchy X s) A ⊙ f)

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
