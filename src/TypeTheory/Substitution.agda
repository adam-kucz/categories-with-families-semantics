{-# OPTIONS --exact-split --prop --safe #-}
module TypeTheory.Substitution where

open import TypeTheory.Syntax

open import Universes
open import Data.Nat

Ren : (m n : ℕ) → 𝒰₀ ˙
Ren m n = (v : Var m) → Var n

lift-ren : (ρ : Ren m n) → Ren (m +1) (n +1)
lift-ren ρ new = new
lift-ren ρ (old v) = old (ρ v)

weaken-1 : Ren m (m +1)
weaken-1 new = new
weaken-1 (old x) = old (weaken-1 x)

open import Function

weaken : ∀ k → Ren m (k + m)
weaken zero = id
weaken (k +1) = weaken-1 ∘ weaken k

rename : ∀
  (ρ : Ren m n)
  {tag}
  (t : expr-of-type tag m)
  → -------------------------------
  expr-of-type tag n
rename ρ {term} (⋆ i) = ⋆ i
rename ρ {term} ([x: S ]→ T) = [x: rename ρ S ]→ rename (lift-ren ρ) T
rename ρ {term} (λx, t) = λx, rename (lift-ren ρ) t
rename ρ {term} ⌊ e ⌋ = ⌊ rename ρ e ⌋
-- rename ρ {term} (Id[ t ] t₁ == t₂) = Id[ rename ρ t ] rename ρ t₁ == rename ρ t₂
-- rename ρ {term} refl-term = refl-term
rename ρ {elim} (var v) = var (ρ v)
rename ρ {elim} (f ` s) = rename ρ f ` rename ρ s
rename ρ {elim} (s ꞉ S) = rename ρ s ꞉ rename ρ S
-- rename ρ {elim} J[ t ,[x,y]→ T , t₁ ] =
--   J[ rename ρ t ,[x,y]→ rename ρ' T , rename ρ t₁ ]
--   where ρ' = lift-ren (lift-ren ρ)

expand-by : ∀
  (k : ℕ)
  {tag}
  (t : expr-of-type tag m)
  → -----------------------
  expr-of-type tag (k + m)
expand-by k t = rename (weaken k) t

expand : ∀{tag}
  (t : expr-of-type tag m)
  → -----------------------
  expr-of-type tag (m +1)
expand = rename weaken-1

shift : (t : expr-of-type tag m) → expr-of-type tag (m +1)
shift = rename old

Sub : (m n : ℕ) → 𝒰₀ ˙
Sub m n = (v : Var m) → Elim n

lift : (σ : Sub m n) → Sub (m +1) (n +1)
lift σ new = var new
lift σ (old v) = shift (σ v)

sub : ∀
  (σ : Sub m n)
  {tag}
  (t : expr-of-type tag m)
  → -------------------------------
  expr-of-type tag n
sub σ {term} (⋆ i) = ⋆ i
sub σ {term} ([x: T ]→ S) = [x: sub σ T ]→ sub (lift σ) S
sub σ {term} (λx, t) = λx, sub (lift σ) t
sub σ {term} ⌊ e ⌋ = ⌊ sub σ e ⌋
-- sub σ {term} (Id[ t ] t₁ == t₂) = Id[ sub σ t ] sub σ t₁ == sub σ t₂
-- sub σ {term} refl-term = refl-term
sub σ {elim} (var v) = σ v
sub σ {elim} (f ` s) = sub σ f ` sub σ s
sub σ {elim} (s ꞉ S) = sub σ s ꞉ sub σ S
-- sub σ {elim} J[ t ,[x,y]→ T , t₁ ] =
--   J[ sub σ t ,[x,y]→ sub σ' T , sub σ t₁ ]
--   where σ' = lift (lift σ)

newSub : (e : Elim n) → Sub (n +1) n
newSub e new = e
newSub e (old v) = var v

infix 180 _[_/new] _[_/x,_/y]
_[_/new] :
  (t : expr-of-type tag (n +1))
  (e : Elim n)
  → -------------------------------
  expr-of-type tag n
t [ e /new] = sub (newSub e) t

_[_/x,_/y] :
  (t : expr-of-type tag (n +2))
  (e e' : Elim n)
  → ----------------------------
  expr-of-type tag n
_[_/x,_/y] {n = n} t e e' = sub σ t
  where σ : Sub (n +2) n
        σ new = e
        σ (old new) = e'
        σ (old (old v)) = var v
