{-# OPTIONS --exact-split --prop --safe #-}
module TypeTheory.Syntax where

open import Universes
open import Data.Nat

data Var : (n : ℕ) → 𝒰₀ ˙ where
  new : {n : ℕ} → Var (n +1)
  old : {n : ℕ} (a : Var n) → Var (n +1)

open import Proof

nth-var : ∀ n {m} (p : n +1 ≤ m) → Var m
nth-var zero {m +1} p = new
nth-var (n +1) {m +1} p = old (nth-var n (ap pred p))

last-var : ∀ n → Var (n +1)
last-var n = nth-var n (refl (n +1))

open import Proposition.Decidable

instance
  DecidableVar== : HasDecidableIdentity (Var n)

DecidableVar== {x = new} {new} = true (Id.refl new)
DecidableVar== {x = new} {old _} = false λ ()
DecidableVar== {x = old _} {new} = false λ ()
DecidableVar== {x = old v} {old v'} with decide (v == v')
DecidableVar== | true p = true (ap old p)
DecidableVar== | false ¬p = false λ { (Id.refl (old v)) → ¬p (Id.refl v) }

data Term (n : ℕ) : 𝒰₀ ˙
data Elim (n : ℕ) : 𝒰₀ ˙
    
infix 170 [x:_]→_ λx,_ Id[_]_==_
data Term n where
  ⋆ : (i : ℕ) → Term n
  [x:_]→_ : (S : Term n) (T : Term (n +1)) → Term n
  λx,_ : (t : Term (n +1)) → Term n
  ⌊_⌋ : (e : Elim n) → Term n
  Id[_]_==_ : (T t t' : Term n) → Term n
  refl-term : Term n
  
infix 160 _`_ _꞉_ J[_,[x,y]→_,_]
data Elim n where
  var : (v : Var n) → Elim  n
  _`_ : (f : Elim n) (s : Term n) → Elim n
  _꞉_ : (s : Term n) (S : Term n) → Elim n
  J[_,[x,y]→_,_] : (e : Elim n)(T : Term (n +2))(t : Term n) → Elim n

data ExprTag : 𝒰₀ ˙ where
  term elim : ExprTag

variable
  tag : ExprTag

expr-of-type : (e : ExprTag) (n : ℕ) → 𝒰₀ ˙
expr-of-type term = Term
expr-of-type elim = Elim

infixl 155 _∥x:_
-- index n denotes how many variables are defined by a (pre-)context
-- by construction no free variables are allowed in contexts
data Context : (n : ℕ) → 𝒰₀ ˙ where
  ◇ : Context 0
  _∥x:_ : {n : ℕ}
    (Γ : Context n)
    (S : Term n)
    → ----------------
    Context (n +1)

