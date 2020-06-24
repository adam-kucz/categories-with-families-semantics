{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.SigmaType where

open import Category.WithUniverses.Definition

open import Universes hiding (A; B; _⁺⁺; _⁺)
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

record HasSigmaTypes (C : CwU 𝒰 𝒱 𝒲) : 𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙ where
  open CwU C
  private
    instance _ = ℂ; _ = λ {s} → ℱ s
  field
    Σ : ∀{Γ}(A : Ty s₀ Γ)(B : Ty s₁ (Γ ,, A)) → Ty (max s₀ s₁) Γ
    pair :  ∀{Γ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      → ------------------------------
      Γ ,, A ,, B ~> Γ ,, Σ A B
    R : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (C : Ty s (Γ ,, Σ A B))
      (H : Tm (C ∙ pair A B))
      → -----------------------
      Tm C

    Σ-subs : ∀{Γ Δ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (f : Δ ~> Γ)
      → ------------------------------------------------------------------
      Σ A B ∙ f == Σ (A ∙ f) (B ∙ q[ f , A ])

    p∘pair : ∀{Γ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      → ------------------------------
      𝒑 (Σ A B) ∘ pair A B == 𝒑 A ∘ 𝒑 B

    R-reduce : ∀{Γ}
      {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}{C : Ty s (Γ ,, Σ A B)}
      {H : Tm (C ∙ pair A B)}
      → -----------------------
      R C H ⊙ pair A B == H

    pair[_,_]∘q[_⁺] : ∀{Γ Δ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (f : Δ ~> Γ)
      → --------------------------
      let coer : Δ ,, Σ A B ∙ f ~> Γ ,, Σ A B
                 ==
                 Δ ,, Σ (A ∙ f) (B ∙ q[ f , A ]) ~> Γ ,, Σ A B
          coer = ap (λ — → Δ ,, — ~> Γ ,, Σ A B) $ Σ-subs A B f
      in
      pair A B ∘ q[ q[ f , A ] , B ]
      ==
      coe coer q[ f , Σ A B ] ∘ pair (A ∙ f) (B ∙ q[ f , A ])

    R-subs : ∀{Γ Δ}
      {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}{C : Ty s (Γ ,, Σ A B)}
      {H : Tm (C ∙ pair A B)}
      (f : Δ ~> Γ)
      → -----------------------
      let coer = ap (λ — → Δ ,, — ~> Γ ,, Σ A B) $ Σ-subs A B f
          f⁺ = coe coer q[ f , Σ A B ]
          coer' : Tm (C ∙ pair A B ∙ q[ q[ f , A ] , B ])
                  ==
                  Tm (C ∙ f⁺ ∙ pair (A ∙ f) (B ∙ q[ f , A ]))
          coer' = ap Tm (
            proof C ∙ pair A B ∙ q[ q[ f , A ] , B ]
              === C ∙ (pair A B ∘ q[ q[ f , A ] , B ])
                :by: ∙-comp== C (pair A B) q[ q[ f , A ] , B ]
              === C ∙ (f⁺ ∘ pair (A ∙ f) (B ∙ q[ f , A ]))
                :by: ap (C ∙_) pair[ A , B ]∘q[ f ⁺]
              === C ∙ f⁺ ∙ pair (A ∙ f) (B ∙ q[ f , A ])
                :by: sym $ ∙-comp== C f⁺ (pair (A ∙ f) (B ∙ q[ f , A ]))
            qed)
      in
      R C H ⊙ f⁺
      ==
      R (C ∙ f⁺) (coe coer' (H ⊙ q[ q[ f , A ] , B ]))

{-
    ƛ_ : ∀{Γ}{A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
      (b : Tm B) → Tm (Π A B)
    app : ∀{Γ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      → ------------------------------
      Γ ,, A ,, Π A B ⁺ ~> Γ ,, A ,, B

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

    App-T : ∀{Γ}
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
      let coer : ∀{Δ s}(B : Ty s Δ) → Tm B  == Tm (Ty-sub (id Δ) B)
          coer {Δ} B = ap (λ — → Tm (pr₁ — B)) $ sym $ id-preserv Δ
      in
      app A B ∘ bar ((ƛ b) ⊙ 𝒑 A) == bar b
    third : ∀{Γ Δ}
      (A : Ty s₀ Γ)
      (B : Ty s₁ (Γ ,, A))
      (f : Δ ~> Γ)
      → ------------------------------------------------
      let Γ' = Γ ,, A ,, Π A B ⁺
          Δ' = Δ ,, A ∙ f
          coer : Δ' ,, Π A B ⁺ ∙ q[ f , A ] ~> Γ'
                 ==
                 Δ' ,, Π (A ∙ f) (B ∙ q[ f , A ]) ⁺ ~> Γ'
          coer = ap (λ C → Δ' ,, C ~> Γ') (
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
-}
