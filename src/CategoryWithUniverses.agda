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

record CategoryWithUniverses (𝒰 𝒱 𝒲 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  field
    ℂ : Category 𝒰 𝒱

  Ctx = obj ⦃ ℂ ⦄
  instance _ = ℂ

  field
    ⦃ 𝟙-ℂ ⦄ : Terminal
    presheaf : (s : ℕ) → Functor (ℂ ᵒᵖ) (Set' {𝒲})

  -- syntax F₀ ⦃ presheaf s ⦄ X = ℂ-family-over X of-size s

  _∙_ : ∀ {X Y}
    (A : F₀ ⦃ presheaf s ⦄ X)
    (f : Y ~> X)
    → --------------------------
    F₀ ⦃ presheaf s ⦄ Y
  _∙_ {s} = flip (F₁ ⦃ presheaf s ⦄)

  -- A ∙ id X = F₁ ⦃ presheaf s ⦄ (id X) A = id (F₀ X) A = A
  -- A ∙ (f ∘ g) = F₁ (f ∘ g) A = (F₁ f ∘ F₁ g) A = F₁ f (F₁ g A) = F₁ f (A ∙ g) = (A ∙ g) ∙ f

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
