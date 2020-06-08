{-# OPTIONS --exact-split --prop #-}
open import PropUniverses
open import Category.WithUniverses

module Semantics.Definition
  (C : CwU 𝒰 𝒱 𝒲)
  ⦃ pi-types : HasPiTypes C ⦄
  where

open import TypeTheory.Syntax

open import Type.Sum hiding (_,_; 〈_,_〉)
open import Data.Nat hiding (_⊔_; ⊤)

open CwU C
open HasPiTypes pi-types renaming (app to app')

Ty&Tm : (Γ : Ctx) → 𝒲 ˙
Ty&Tm Γ = Σ λ (s : ℕ) → Σ λ (A : Ty s Γ) → Tm A

Val : (n : ℕ)(Γ : Ctx) → 𝒲 ˙
Val n Γ = Var n → Ty&Tm Γ

open import Proposition.Decidable
open import Proposition.Identity

_[new:=_] :
  {Γ : Ctx}
  (ρ : Val n Γ)
  (val : Ty&Tm Γ)
  → -------------------
  Val (n +1) Γ
(ρ [new:= val ]) new = val
(ρ [new:= val ]) (old x) = ρ x

_[new:=[_,_,_]] : 
  {Γ : Ctx}
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  (a : Tm A)
  → -------------------
  Val (n +1) Γ
ρ [new:=[ s , A , a ]] = ρ [new:= s Σ., (A Σ., a) ]

weaken : 
  {Γ : Ctx}{s : ℕ}
  (A : Ty s Γ)
  (ρ : Val n Γ)
  → ----------------
  Val n (Γ ,, A)
weaken A ρ x with ρ x
weaken A ρ x | s Σ., (B Σ., b) = s Σ., ((B ∙ 𝒑 A) Σ., (b ⊙ 𝒑 A))

open import Basic

data ∥_∥[_,_,_,_]:=_ :
  (t : Term n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  (a : Tm A)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ

data ∣_∣[_,_]:=_ :
  (e : Elim n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (val : Ty&Tm Γ)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ

open import Proposition.Identity.Coercion

∥_∥[_,_,_]:=_ :
  (T : Term n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ
∥ T ∥[ Γ , ρ , s ]:= A =
  ∥ T ∥[ Γ , ρ , s +1 , 𝑈 Γ s ]:=
    coe (hierarchy Γ s) A

∣_∣[_,_]:=[_,_,_] :
  (T : Elim n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  (a : Tm A)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ
∣ e ∣[ Γ , ρ ]:=[ s , A , a ] = ∣ e ∣[ Γ , ρ ]:= (s Σ., (A Σ., a))

data ∥_∥[_,_,_,_]:=_ where
  univ : (s : ℕ)(Γ : Ctx)(ρ : Val n Γ)
    → ----------------------------------------
    ∥ ⋆ {n} s ∥[ Γ , ρ , s +1 ]:= 𝑈 Γ s

  pi : {T₀ : Term n}{T₁ : Term (n +1)}
    {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
    {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
    (p₀ : ∥ T₀ ∥[ Γ , ρ , s₀ ]:= A)
    (p₁ : ∥ T₁ ∥[ Γ ,, A , weaken A ρ [new:=[ s₀ , A ∙ 𝒑 A , 𝒒 A ]] , s₁ ]:= B)
    -- ρ [new:=[ s₀ , A ∙ 𝒑 A , 𝒒 A ]]
    → ------------------------------------------------------------------------
    ∥ [x: T₀ ]→ T₁ ∥[ Γ , ρ , max s₀ s₁ ]:= Π A B

  lam :
    {t : Term (n +1)}
    {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
    {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
    {b : Tm B}
    (p : ∥ t ∥[ Γ ,, A , weaken A ρ [new:=[ s₀ , A ∙ 𝒑 A , 𝒒 A ]] , s₁ , B ]:= b)
    → --------------------------------------------------------------------------
    ∥ λx, t ∥[ Γ , ρ , max s₀ s₁ , Π A B ]:= ƛ b

  elim : ∀
    {e : Elim n}{Γ : Ctx}{ρ : Val n Γ}{s : ℕ}{A : Ty s Γ}{a : Tm A}
    (p : ∣ e ∣[ Γ , ρ ]:=[ s , A , a ])
    → --------------------------------------------------------------
    ∥ ⌊ e ⌋ ∥[ Γ , ρ , s , A ]:= a

private
  instance _ = ℂ; _ = λ {s} → ℱ s

open import Category
open import Functor

open import Proof


data ∣_∣[_,_]:=_ where
  var : (v : Var n)(Γ : Ctx)(ρ : Val n Γ)
    → -------------------------------------
    ∣ var v ∣[ Γ , ρ ]:= ρ v

  annot : {t T : Term n}
    {Γ : Ctx}{ρ : Val n Γ}{s : ℕ}{A : Ty s Γ}{a : Tm A}
    (p₀ : ∥ T ∥[ Γ , ρ , s ]:= A)
    (p₁ : ∥ t ∥[ Γ , ρ , s , A ]:= a)
    → --------------------------------------------------
    ∣ t ꞉ T ∣[ Γ , ρ ]:=[ s , A , a ]

  app :  {e : Elim n}{t : Term n}
    {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
    {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
    {a : Tm A}{b : Tm (Π A B)}
    (p₀ : ∣ e ∣[ Γ , ρ ]:=[ max s₀ s₁ , Π A B , b ])
    (p₁ : ∥ t ∥[ Γ , ρ , s₀ , A ]:= a)
    → ----------------------------------------------------------
    let coer : Tm A == Tm (Ty-sub (id Γ) A)
        coer = ap (λ — → Tm (pr₁ — A)) $ sym $ id-preserv Γ
    in
    ∣ e ` t ∣[ Γ , ρ ]:=[ s₁ , B ∙ 〈 id Γ , coe coer a 〉 , app' b a ]

open import Construction.Terminal

data ⟦_⟧:=[_,_] : (Γ : Context n)(X : Ctx)(ρ : Val n X) → 𝒰 ⊔ 𝒲 ˙ where
  empty : ⟦ ◇ ⟧:=[ 𝟙 , (λ ()) ]
  cons :
    {Γ : Context n}{T : Term n}
    {X : Ctx}{ρ : Val n X}{s : ℕ}{A : Ty s X}
    (p₀ : ⟦ Γ ⟧:=[ X , ρ ])
    (p₁ : ∥ T ∥[ X , ρ , s ]:= A)
    → -----------------------------------------
    ⟦ Γ ∥x: T ⟧:=[ X ,, A , weaken A ρ [new:=[ s , A ∙ 𝒑 A , 𝒒 A ]] ]
