{-# OPTIONS --exact-split --prop --safe #-}
module TypeTheory.Reduction where

open import TypeTheory.Syntax
open import TypeTheory.Substitution

open import PropUniverses hiding (_⊔_)
open import Data.Nat
open import Relation.Binary

data OneHoleContext
  : ------------------------------------------------------------
  (hole : ExprTag) -- required type of hole
  (m : ℕ) -- number of free variables in hole
  (result : ExprTag) -- type resulting from filling hole
  (n : ℕ) -- number of free variables of the context (n ≤ m)
  → 𝒰₀ ˙
  where
  — : ∀{n tag} → OneHoleContext tag n tag n

  [x:_]→_↓ : ∀ {m n tag}
    (S : Term n)
    (C : OneHoleContext tag m term (n +1))
    → ---------------------
    OneHoleContext tag m term n

  [x:_↓]→_ : ∀ {m n tag}
    (C₀ : OneHoleContext tag m term n)
    (T : Term (n +1))
    → ---------------------
    OneHoleContext tag m term n

  Id[_↓]_==_ : ∀{m n tag}
    (C : OneHoleContext tag m term n)
    (t₀ t₁ : Term n)
    → ---------------------
    OneHoleContext tag m term n

  Id[_]_↓==_ : ∀{m n tag}
    (T : Term n)
    (C : OneHoleContext tag m term n)
    (t₁ : Term n)
    → ---------------------
    OneHoleContext tag m term n

  Id[_]_==_↓ : ∀{m n tag}
    (T t₀ : Term n)
    (C : OneHoleContext tag m term n)
    → ---------------------
    OneHoleContext tag m term n

  J[_↓,[x,y]→_,_] : ∀{m n tag}
    (C : OneHoleContext tag m elim n)
    (T' : Term (n +2))
    (t : Term n)
    → ---------------------
    OneHoleContext tag m elim n

  J[_,[x,y]→_↓,_] : ∀{m n tag}
    (e : Elim n)
    (C : OneHoleContext tag m term (n +2))
    (t : Term n)
    → ---------------------
    OneHoleContext tag m elim n

  J[_,[x,y]→_,_↓] : ∀{m n tag}
    (e : Elim n)
    (T' : Term (n +2))
    (C : OneHoleContext tag m term n)
    → ---------------------
    OneHoleContext tag m elim n

  λx,_ : ∀{m n tag}
    (C : OneHoleContext tag m term (n +1))
    → ----------------------
    OneHoleContext tag m term n

  ⌊_⌋ : ∀{m n tag}
    (C : OneHoleContext tag m elim n)
    → ---------------------
    OneHoleContext tag m term n

  _`_↓ : ∀ {m n tag}
    (f : Elim n)
    (C : OneHoleContext tag m term n)
    → ----------------------
    OneHoleContext tag m elim n

  _↓`_ : ∀ {m n tag}
    (C : OneHoleContext tag m elim n)
    (s : Term n)
    → ----------------------
    OneHoleContext tag m elim n

  _꞉_↓ : ∀ {m n tag}
    (s : Term n)
    (C : OneHoleContext tag m term n)
    →  ----------------------
    OneHoleContext tag m elim n

  _↓꞉_ : ∀ {m n tag}
    (C₀ : OneHoleContext tag m term n)
    (S : Term n)
    →  ----------------------
    OneHoleContext tag m elim n

infix 180 _[_/—]
_[_/—] : ∀{m n tag₀ tag₁}
  (C[—] : OneHoleContext tag₀ m tag₁ n)
  (e : expr-of-type tag₀ m)
  → ----------------------
  expr-of-type tag₁ n
— [ e /—] = e
[x: S ]→ C[—] ↓ [ e /—] = [x: S ]→ C[—] [ e /—]
([x: C[—] ↓]→ T) [ e /—] = [x: C[—] [ e /—] ]→ T
(λx, C[—]) [ e /—] = λx, C[—] [ e /—]
⌊ C[—] ⌋ [ e /—] = ⌊ C[—] [ e /—] ⌋
(f ` C[—] ↓) [ e /—] = f ` C[—] [ e /—]
(C[—] ↓` s) [ e /—] = C[—] [ e /—] ` s
(s ꞉ C[—] ↓) [ e /—] = s ꞉ C[—] [ e /—]
(C[—] ↓꞉ S) [ e /—] = C[—] [ e /—] ꞉ S
(Id[ C[—] ↓] t₀ == t₁) [ e /—] = Id[ C[—] [ e /—] ] t₀ == t₁
(Id[ T ] C[—] ↓== t₁) [ e /—] = Id[ T ] C[—] [ e /—] == t₁
Id[ T ] t₀ == C[—] ↓ [ e /—] = Id[ T ] t₀ == C[—] [ e /—]
J[ C[—] ↓,[x,y]→ T' , t ] [ e /—] = J[ C[—] [ e /—] ,[x,y]→ T' , t ]
J[ e₀ ,[x,y]→ C[—] ↓, t ] [ e /—] = J[ e₀ ,[x,y]→ C[—] [ e /—] , t ]
J[ e₀ ,[x,y]→ T' , C[—] ↓] [ e /—] = J[ e₀ ,[x,y]→ T' , C[—] [ e /—] ]

infix 36 _⇝_ _↠_
data _⇝_ : BinRel 𝒰₀ (expr-of-type tag n) where
  β : ∀ (s S : Term n) t T
    → ----------------------------------------------------
    (λx, t ꞉ ([x: S ]→ T)) ` s ⇝ (t ꞉ T) [ s ꞉ S /new]

  value : (t T : Term n)
    → ------------------
    ⌊ t ꞉ T ⌋ ⇝ t

  J[refl:Id[_]_==self,[x,y]→_,_] :
    (T t₀ : Term n)(T' : Term (n +2))(t : Term n)
    → -------------------------------------------------
    J[ (refl-term ꞉ Id[ T ] t₀ == t₀) ,[x,y]→ T' , t ]
    ⇝
    t ꞉ T' [ t₀ ꞉ T /x, refl-term ꞉ Id[ T ] t₀ == t₀ /y]

  hole : ∀ {m n tag₀ tag₁ s t}
    (C[—] : OneHoleContext tag₀ m tag₁ n)
    (reduct : s ⇝ t)
    → --------------------
    C[—] [ s /—] ⇝ C[—] [ t /—]

_↠_ : BinRel 𝒰₀ (expr-of-type tag n)
_↠_ = refl-trans-close _⇝_

infix 36 _⊢_⇓_ _⊢_↓_

data _⊢_⇓_ (Γ : Context n) : (c : Elim n)(t : Term n) → 𝒰₀ ᵖ
data _⊢_↓_ (Γ : Context n) : (e : Elim n)(c : Elim n) → 𝒰₀ ᵖ

data _⊢_⇓_ Γ where
  ⋆ : ∀ s
    → ----------------
    Γ ⊢ ⋆ s ꞉ ⋆ (s +1) ⇓ ⋆ s

  [x:_]→_ : ∀{S S' T T' s₀ s₁}
    (p : Γ ⊢ S ꞉ ⋆ s₀ ⇓ S')
    (q : Γ ∥x: S' ⊢ T ꞉ ⋆ s₁ ⇓ T')
    → ------------------------------------------
    Γ ⊢ [x: S ]→ T ꞉ ⋆ (s₀ ⊔ s₁) ⇓ [x: S' ]→ T'

  λx,_ : ∀{S T t t'}
    (p : Γ ∥x: S ⊢ t ꞉ T ⇓ t')
    → ------------------------------------------
    Γ ⊢ λx, t ꞉ [x: S ]→ T ⇓ λx, t'

  Id-type : ∀{T T' t₀ t₀' t₁' t₁ s}
    (p : Γ ⊢ T ꞉ ⋆ s ⇓ T')
    (q : Γ ⊢ t₀ ꞉ T ⇓ t₀')
    (q : Γ ⊢ t₁ ꞉ T ⇓ t₁')
    → ----------------------------------------------
    Γ ⊢ Id[ T ] t₀ == t₁ ꞉ ⋆ s ⇓ Id[ T' ] t₀' == t₁'

  refl[_,_] : ∀ T t
    → ----------------------------------------------
    Γ ⊢ refl-term ꞉ Id[ T ] t == t ⇓ refl-term

  ↓→⇓ : ∀{e t T}
    (p : Γ ⊢ e ↓ t ꞉ T)
    → ------------------
    Γ ⊢ ⌊ e ⌋ ꞉ T ⇓ t

infix 180 _!_
_!_ : (Γ : Context n)(x : Var n) → Term n
(Γ ∥x: S) ! new = expand-by 1 S
(Γ ∥x: _) ! old x = expand-by 1 (Γ ! x)

data _⊢_↓_ Γ where
  var : ∀ x
    → ----------------------------
    Γ ⊢ var x ↓ ⌊ var x ⌋ ꞉ Γ ! x

  _꞉_ : ∀{s t t' T T'}
    (p : Γ ⊢ T ꞉ ⋆ s ⇓ T')
    (q : Γ ⊢ t ꞉ T' ⇓ t')
    → ---------------------
    Γ ⊢ t ꞉ T ↓ t' ꞉ T'

  lambda-eval : ∀{f t t' S T T' s s' i}
    (p₀ : Γ ⊢ f ↓ λx, t ꞉ [x: S ]→ T)
    (p₁ : Γ ⊢ s ꞉ S ⇓ s')
    (p₂ : Γ ⊢ T [ s' ꞉ S /new] ꞉ ⋆ i ⇓ T')
    (p₃ : Γ ⊢ t [ s' ꞉ S /new] ꞉ T' ⇓ t')
    → --------------------------------------
    Γ ⊢ f ` s ↓ t' ꞉ T' 

  app : ∀{f f' S T T' s s' i}
    (p₀ : Γ ⊢ f ↓ ⌊ f' ⌋ ꞉ [x: S ]→ T)
    (p₁ : Γ ⊢ s ꞉ S ⇓ s')
    (p₂ : Γ ⊢ T [ s' ꞉ S /new] ꞉ ⋆ i ⇓ T')
    → ------------------------------------
    Γ ⊢ f ` s ↓ ⌊ f' ` s' ⌋ ꞉ T'

  -- J :
  --   Γ ⊢ J(e, x,y.T', t) ↓ ꞉ T' [ t₁ ꞉ T /x, e /y]

test-λ : ◇ ⊢ (λx, ⌊ var new ⌋ ꞉ [x: ⋆ 1 ]→ ⋆ 1) ` ⋆ 0 ↓ ⋆ 0 ꞉ ⋆ 1
test-λ = lambda-eval ([x: ⋆ 1 ]→ ⋆ 1 ꞉ λx, ↓→⇓ (var new))
                     (⋆ 0)
                     (⋆ 1)
                     (↓→⇓ (⋆ 1 ꞉ ⋆ 0))

-- test-λ2 : ◇ ⊢ (λx, ⌊ var new ⌋ ꞉ [x: ⋆ 1 ]→ ⋆ 1) ` ⋆ 0 ↓
--              ⌊ (λx, ⌊ var new ⌋ ꞉ [x: ⋆ 1 ]→ ⋆ 1) ` ⋆ 0 ⌋ ꞉ ⋆ 1
-- test-λ2 = app ([x: ⋆ 1 ]→ ⋆ 1 ꞉ {!!}) {!!} {!!}
