{-# OPTIONS --exact-split --prop --safe #-}
module TypeTheory.Judgment where

open import TypeTheory.Syntax

open import PropUniverses
open import Data.Nat hiding (_⊔_)

infix 152 _⊢_∋_ _⊢_∈_
data _⊢_∋_ {n} : (Δ : Context n)(T : Term n)(t : Term n) → 𝒰₀ ᵖ
data _⊢_∈_ : {n : ℕ}(Δ : Context n)(e : Elim n)(S : Term n) → 𝒰₀ ᵖ

open import TypeTheory.Reduction

data _⊢_∋_ {n} where
  pre : ∀{Δ : Context n}{T R t : Term n}
    (Δ⊢T∋t : Δ ⊢ R ∋ t)
    (R⇝T : T ⇝ R)
    → ------------------------
    Δ ⊢ T ∋ t

  sort : ∀{i j}(Γ : Context n)
    (p : i < j)
    → --------------
    Γ ⊢ ⋆ j ∋ ⋆ i
   
  pi-type : ∀{i}{Γ : Context n} {T S}
    (Γ⊢*ᵢ∋S : Γ ⊢ ⋆ i ∋ S)
    (Γ,x:S⊢*ⱼ∋T : Γ ∥x: S ⊢ ⋆ i ∋ T)
    → --------------------------------------
    Γ ⊢ ⋆ i ∋ [x: S ]→ T

  lam : ∀{Δ : Context n} {T S t}
    (Δ,x:S⊢T∋t : Δ ∥x: S ⊢ T ∋ t)
    → --------------------------------------
    Δ ⊢ [x: S ]→ T ∋ λx, t
  
  elim : ∀{Δ : Context n}{T S : Term n}{e : Elim n}
    (Δ⊢ρe∈S : Δ ⊢ e ∈ S)
    → --------------------------------------
    Δ ⊢ T ∋ ⌊ e ⌋

  -- id-type : ∀{i}{Γ : Context n}{T t t'}
  --   (Γ⊢*ᵢ∋T : Γ ⊢ ⋆ i ∋ T)
  --   (Γ⊢T∋t : Γ ⊢ T ∋ t)
  --   (Γ⊢T∋t' : Γ ⊢ T ∋ t')
  --   → --------------------------------------
  --   Γ ⊢ ⋆ i ∋ Id[ T ] t == t'

  -- refl-term : ∀{i}{Γ : Context n}{T t}
  --   (Γ⊢*ᵢ∋T : Γ ⊢ ⋆ i ∋ T)
  --   (Γ⊢T∋t : Γ ⊢ T ∋ t)
  --   → --------------------------------------
  --   Γ ⊢ Id[ T ] t == t ∋ refl-term

open import TypeTheory.ContextCollection
import Data.List as L
open import Collection
open import Proof

_!_[_] : (Γ : Context n)(m : ℕ)(p : m +1 ≤ n) → Term n
Γ ! m [ p ] = to-list Γ L.! m [ p' ]
  where p' = Id.coe (ap (m +1 ≤_) $ sym $ len-to-list Γ) p

open import TypeTheory.Substitution

data _⊢_∈_ where
  post : ∀{Δ : Context n}{S R}{e}
    (Δ⊢e∈S : Δ ⊢ e ∈ S)
    (S⇝R : S ⇝ R)
    → ------------------------
    Δ ⊢ e ∈ R

  -- syntax modified compared to the paper, meaning preserved
  var : ∀ {Γ : Context n}
    (p : m +1 ≤ n)
    → ----------------------------------------------------
    Γ ⊢ var (nth-var m p) ∈ (Γ ! m [ p ])

  app : ∀{Γ : Context n} {T S s f}
    (Γ⊢f∈[x:S]→T : Γ ⊢ f ∈ [x: S ]→ T)
    (Γ⊢S∋s : Γ ⊢ S ∋ s)
    → --------------------------------------
    Γ ⊢ f ` s ∈ T [ s ꞉ S /new]

  cut : ∀{i}{Γ : Context n}{S s}
    (Γ⊢*ᵢ∋S : Γ ⊢ ⋆ i ∋ S)
    (Γ⊢S∋s : Γ ⊢ S ∋ s)
    → --------------------------------------
    Γ ⊢ s ꞉ S ∈ S

  -- J :  ∀{i}{Γ : Context n}{e T t₀ t₁ T' t}
  --   (Γ⊢e∈Id[T]t₀==t₁ : Γ ⊢ e ∈ Id[ T ] t₀ == t₁)
  --   (Γ,x:T,y:Id⊢⋆ᵢ∋T' :
  --      Γ ∥x: T ∥x: Id[ expand T ] expand t₀ == ⌊ var new ⌋ ⊢ ⋆ i ∋ T')
  --   (Γ⊢T'∋t : Γ ⊢ T' [ t₀ ꞉ T /x, refl-term ꞉ Id[ T ] t₀ == t₀ /y] ∋ t)
  --   → --------------------------------------------------------------------------
  --   Γ ⊢ J[ e ,[x,y]→ T' , t ] ∈ T' [ t₁ ꞉ T /x, e /y]
