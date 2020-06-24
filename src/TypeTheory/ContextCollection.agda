{-# OPTIONS --exact-split --prop --safe #-}
module TypeTheory.ContextCollection where

open import TypeTheory.Syntax
open import Collection hiding (_++_)

open import PropUniverses
open import Data.Nat

open import TypeTheory.Substitution

data member : (T : Term n)(Γ : Context n) → 𝒰₀ ᵖ where
  _∈last-of_ : (T : Term n)(Γ : Context n) → member (expand T)(Γ ∥x: T)
  _∈prefix_∥x:_ :
    (T : Term n)
    {Γ : Context n}
    (p : member T Γ)
    (S : Term n)
    → ---------------------
    member (expand T)(Γ ∥x: S)

instance
  ContextCollection : Collection 𝒰₀ (Context n)(Term n)
  ContextListable : Listable 𝒰₀ (Context n)(Term n)

_∈_ ⦃ ContextCollection ⦄ = member

open import Data.List
open import Proof
open import Logic

collection ⦃ ContextListable ⦄ = ContextCollection
to-list ⦃ ContextListable {n = 0} ⦄ ◇ = []
to-list ⦃ ContextListable {n = n +1} ⦄ (Γ ∥x: S) =
  map expand (to-list Γ ++ [ S ])
⟶ (to-list-valid ⦃ ContextListable ⦄) (T ∈last-of Γ) =
  ∈map expand $ ⟵ (∈++ (to-list Γ) [ T ]) $ ∨right $ x∈x∷ []
⟶ (to-list-valid ⦃ ContextListable ⦄) (T ∈prefix p ∥x: S) =
  ∈map expand $ ⟵ (∈++ (to-list _) [ S ]) $ ∨left $ ⟶ to-list-valid p
⟵ (to-list-valid ⦃ ContextListable ⦄ {Γ ∥x: S}{T}) q
  with ∈map⁻¹ (to-list Γ ++ [ S ]) expand q
... | T' , (Id.refl _ , T'∈Γ++S) with ⟶ (∈++ (to-list Γ) [ S ]) T'∈Γ++S
... | ∨left p = T' ∈prefix (⟵ to-list-valid p) ∥x: S
... | ∨right (x∈x∷ []) = S ∈last-of Γ

open import Operation.Binary

len-to-list : (Γ : Context n) → len (to-list Γ) == n
len-to-list ◇ = Id.refl 0
len-to-list {n +1}(Γ ∥x: S) =
  proof len (map expand (to-list Γ ++ [ S ]))
    === len (to-list Γ ++ [ S ]) :by: len-map expand (to-list Γ ++ [ S ]) 
    === len (to-list Γ) + 1      :by: fold-map++ (λ _ → 1) (to-list Γ) [ S ]
    === n + 1                    :by: ap (_+ 1) $ len-to-list Γ
    === n +1                     :by: comm n 1
  qed
  where instance _ = Monoid+
