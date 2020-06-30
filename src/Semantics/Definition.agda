{-# OPTIONS --exact-split --prop #-}
open import PropUniverses hiding (_⁺; _⁺⁺)
open import Category.WithUniverses

module Semantics.Definition
  (C : CwU 𝒰 𝒱 𝒲)
  ⦃ pi-types : HasPiTypes C ⦄
  ⦃ id-types : HasIdTypes C ⦄
  where

open import TypeTheory.Syntax

open import Type.Sum hiding (〈_,_〉) renaming (_,_ to _Σ,_)
open import Data.Nat hiding (_⊔_; ⊤)

open CwU C renaming (module Coer to CwU-Coer)
open WithCwU C

Ty&Tm : (Γ : Ctx) → 𝒲 ˙
Ty&Tm Γ = Σ λ (s : ℕ) → Σ λ (A : Ty s Γ) → Tm A

Val : (n : ℕ)(Γ : Ctx) → 𝒲 ˙
Val n Γ = Var n → Ty&Tm Γ

open import Proposition.Decidable
open import Proposition.Identity

wk : ∀{Γ}(A : Ty s Γ)(val : Ty&Tm Γ) → Ty&Tm (Γ ,, A)
wk A (s Σ, (B Σ, b)) = s Σ, (B ⁺ Σ, b ⊙ 𝒑 A)

infixl 171 _[new:=_]
_[new:=_] :
  {Γ : Ctx}
  (ρ : Val n Γ)
  (val : Ty&Tm Γ)
  → -------------------
  Val (n +1) Γ
(ρ [new:= val ]) new = val
(ρ [new:= val ]) (old x) = ρ x

weaken : 
  {Γ : Ctx}{s : ℕ}
  (A : Ty s Γ)
  (ρ : Val n Γ)
  → ----------------
  Val n (Γ ,, A)
weaken A ρ x with ρ x
weaken A ρ x | s Σ, (B Σ, b) = s Σ, ((B ∙ 𝒑 A) Σ, (b ⊙ 𝒑 A))

infixl 171 _[new:=[_,_,_]]
_[new:=[_,_,_]] : 
  {Γ : Ctx}
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  (a : Tm (A ∙ 𝒑 A))
  → -------------------
  Val (n +1) (Γ ,, A)
ρ [new:=[ s , A , a ]] = weaken A ρ [new:= s Σ, (A ⁺ Σ, a) ]

infix 170 ∥_∥[_,_,_,_]:=_
data ∥_∥[_,_,_,_]:=_ :
  (t : Term n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  (a : Tm A)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ

infix 170 ∣_∣[_,_]:=_
data ∣_∣[_,_]:=_ :
  (e : Elim n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (val : Ty&Tm Γ)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ

open import Proposition.Identity.Coercion

infix 170 ∥_∥[_,_,_]:=_
∥_∥[_,_,_]:=_ :
  (T : Term n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ
∥ T ∥[ Γ , ρ , s ]:= A =
  ∥ T ∥[ Γ , ρ , s +1 , 𝑈 Γ s ]:= coe (hierarchy Γ s) A

infix 170 ∣_∣[_,_]:=[_,_,_]
∣_∣[_,_]:=[_,_,_] :
  (T : Elim n)
  (Γ : Ctx)
  (ρ : Val n Γ)
  (s : ℕ)
  (A : Ty s Γ)
  (a : Tm A)
  → --------------------
  𝒰 ⊔ 𝒲 ᵖ
∣ e ∣[ Γ , ρ ]:=[ s , A , a ] = ∣ e ∣[ Γ , ρ ]:= (s Σ, (A Σ, a))

open import Proof

open HasPiTypes pi-types renaming (app to app')
open HasIdTypes id-types renaming (Id to Id'; refl to refl')
open WithIdTypes ⦃ id-types ⦄ renaming (refl-term to refl-term')
  hiding (module Coer)
open import Category hiding (ℂ)
open import Functor
private instance _ = ℂ; _ = λ {s} → ℱ s

data ∥_∥[_,_,_,_]:=_ where
  univ : (s : ℕ)(Γ : Ctx)(ρ : Val n Γ)
    → ----------------------------------------
    ∥ ⋆ {n} s ∥[ Γ , ρ , s +1 ]:= 𝑈 Γ s

  [x:_]→_ : {T₀ : Term n}{T₁ : Term (n +1)}
    {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
    {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
    (p₀ : ∥ T₀ ∥[ Γ , ρ , s₀ ]:= A)
    (p₁ : ∥ T₁ ∥[ Γ ,, A , ρ [new:=[ s₀ , A , 𝒒 A ]] , s₁ ]:= B)
    → ------------------------------------------------------------------------
    ∥ [x: T₀ ]→ T₁ ∥[ Γ , ρ , max s₀ s₁ ]:= Π A B

  λx,_ :
    {t : Term (n +1)}
    {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
    {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
    {b : Tm B}
    (p : ∥ t ∥[ Γ ,, A , ρ [new:=[ s₀ , A , 𝒒 A ]] , s₁ , B ]:= b)
    → --------------------------------------------------------------------------
    ∥ λx, t ∥[ Γ , ρ , max s₀ s₁ , Π A B ]:= ƛ b

  ⌊_⌋ : ∀
    {e : Elim n}{Γ : Ctx}{ρ : Val n Γ}{s : ℕ}{A : Ty s Γ}{a : Tm A}
    (p : ∣ e ∣[ Γ , ρ ]:=[ s , A , a ])
    → --------------------------------------------------------------
    ∥ ⌊ e ⌋ ∥[ Γ , ρ , s , A ]:= a

  -- Id[_]_==_ : {T t t' : Term n}
  --   {Γ : Ctx}{ρ : Val n Γ}{s : ℕ}
  --   {A : Ty s Γ}{a a' : Tm A}
  --   (p₀ : ∥ T ∥[ Γ , ρ , s ]:= A)
  --   (p₁ : ∥ t ∥[ Γ , ρ , s , A ]:= a)
  --   (p₂ : ∥ t' ∥[ Γ , ρ , s , A ]:= a')
  --   → ---------------------------------------------------------
  --   ∥ Id[ T ] t == t' ∥[ Γ , ρ , s ]:= Id-type A a a'

  -- refl-term : {T t : Term n}
  --   {Γ : Ctx}{ρ : Val n Γ}{s : ℕ}
  --   {A : Ty s Γ}{a a' : Tm A}
  --   (p₀ : ∥ T ∥[ Γ , ρ , s ]:= A)
  --   (p₁ : ∥ t ∥[ Γ , ρ , s , A ]:= a)
  --   → ---------------------------------------------------------
  --   ∥ refl-term ∥[ Γ , ρ , s , Id-type A a a ]:= refl-term' a

data ∣_∣[_,_]:=_ where
  var : (v : Var n)(Γ : Ctx)(ρ : Val n Γ)
    → -------------------------------------
    ∣ var v ∣[ Γ , ρ ]:= ρ v

  _꞉_ : {t T : Term n}
    {Γ : Ctx}{ρ : Val n Γ}{s : ℕ}{A : Ty s Γ}{a : Tm A}
    (p₀ : ∥ T ∥[ Γ , ρ , s ]:= A)
    (p₁ : ∥ t ∥[ Γ , ρ , s , A ]:= a)
    → --------------------------------------------------
    ∣ t ꞉ T ∣[ Γ , ρ ]:=[ s , A , a ]

  _`_ :  {f : Elim n}{s : Term n}
    {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
    {A : Ty s₀ Γ}{B : Ty s₁ (Γ ,, A)}
    {a : Tm A}{b : Tm (Π A B)}
    (p₀ : ∣ f ∣[ Γ , ρ ]:=[ max s₀ s₁ , Π A B , b ])
    (p₁ : ∥ s ∥[ Γ , ρ , s₀ , A ]:= a)
    → ----------------------------------------------------------
    ∣ f ` s ∣[ Γ , ρ ]:=[ s₁ , B ∙ bar a , app-fun b a ]

  -- J[_,[x,y]→_,_] :
  --   {e : Elim n}{T : Term (n +2)}{t : Term n}
  --   {Γ : Ctx}{ρ : Val n Γ}{s₀ s₁ : ℕ}
  --   {A : Ty s₀ Γ}
  --   {a₀ a₁ : Tm A}{a₀==a₁ : Tm (Id-type A a₀ a₁)}
  --   → let Id-typ = Id-type (A ⁺) (a₀ ⊙ 𝒑 A) (𝒒 A)
  --         Γ' = Γ ,, A ,, Id-typ
  --   in {B : Ty s₁ Γ'}
  --   → let B' = {!!}
  --         ρ' = ρ [new:=[ s₀ , A , 𝒒 A ]] [new:=[ s₀ , Id-typ , 𝒒 Id-typ ]]
  --         Γ″ = Γ ,, A ,, A ⁺
  --   in {b : Tm B}
  --   (p₀ : ∣ e ∣[ Γ , ρ ]:=[ s₀ , Id-type A a₀ a₁ , a₀==a₁ ])
  --   (p₁ : ∥ T ∥[ Γ' , ρ' , s₁ ]:= B)
  --   (p₂ : ∥ t ∥[ Γ , ρ , s₁ , B' ]:= {!!})
  --   → --------------------------------------------------------------------------
  --   ∣ J[ e ,[x,y]→ T , t ] ∣[ Γ , ρ ]:=[ s₁ , B ∙ coe {!(B ∙ ?) ∙ bar a₁!} (bar (a₀==a₁ ⊙ 𝒑 A) ∘ bar a₁) , b ⊙ {!!} ]

open import Construction.Terminal

data ⟦_⟧:=[_,_] : (Γ : Context n)(X : Ctx)(ρ : Val n X) → 𝒰 ⊔ 𝒲 ᵖ where
  ◇ : ⟦ ◇ ⟧:=[ 𝟙 , (λ ()) ]
  _∥x:_ :
    {Γ : Context n}{T : Term n}
    {X : Ctx}{ρ : Val n X}{s : ℕ}{A : Ty s X}
    (p₀ : ⟦ Γ ⟧:=[ X , ρ ])
    (p₁ : ∥ T ∥[ X , ρ , s ]:= A)
    → -----------------------------------------
    ⟦ Γ ∥x: T ⟧:=[ X ,, A , ρ [new:=[ s , A , 𝒒 A ]] ]
