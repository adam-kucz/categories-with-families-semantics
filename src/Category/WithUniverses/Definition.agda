{-# OPTIONS --exact-split --prop #-}
module Category.WithUniverses.Definition where

open import Category hiding (ℂ)
open import Category.Opposite
open import Category.Fam
open import Example.Set'
open import Functor
open import Construction.Terminal

open import Universes
  renaming (_⁺ to _+) hiding (_⁺⁺; A; B)
open import Type.Sum hiding (_,_; 〈_,_〉)
open import Data.Nat hiding (_⊔_; ⊤)
open import Function
  renaming (id to id-fun; _∘_ to _∘ₛ_) hiding (_$_; _∘ₛ_)
open import Proof

open import Proposition.Identity.Coercion

variable
  s : ℕ

open import Proposition.Sum
open import Logic using (∃!; _∧_; ∧left; ∧right)

open import Axiom.UniqueChoice

record CwU (𝒰 𝒱 𝒲 : Universe) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) + ˙ where
  field
    ℂ : Category 𝒰 𝒱
    ℱ : (s : ℕ) → Functor (ℂ ᵒᵖ) (Fam 𝒲 𝒲)
  private
    instance _ = ℂ; _ = λ {s} → ℱ s

  Ctx = obj ⦃ ℂ ⦄
  
  Ty : (s : ℕ)(Δ : Ctx) → 𝒲 ˙
  Ty s Δ = pr₁ (F₀ ⦃ ℱ s ⦄ Δ)

  Tm : {Δ : Ctx}(A : Ty s Δ) → 𝒲 ˙
  Tm {_}{Δ} = pr₂ (F₀ Δ)

  Ty-sub : ∀{Γ Δ}(f : Γ ~> Δ) → Ty s Δ → Ty s Γ
  Ty-sub f = pr₁ (F₁ f)
  
  Tm-sub : ∀{Γ Δ}(f : Γ ~> Δ){σ : Ty s Δ} → Tm σ → Tm (Ty-sub f σ)
  Tm-sub f {σ} = pr₂ (F₁ f) σ

  infixl 183 _∙_ _⊙_
  _∙_ : ∀ {Γ Δ}
    (A : Ty s Γ)
    (f : Δ ~> Γ)
    → --------------------------
    Ty s Δ
  A ∙ f = Ty-sub f A

  _⊙_ : ∀ {Γ Δ}{A : Ty s Γ}
    (a : Tm A)
    (f : Δ ~> Γ)
    → --------------------------
    Tm (A ∙ f)
  a ⊙ f = Tm-sub f a

  infixl 182 _,,_
  field
    ⦃ ⊤ ⦄ : Terminal
    _,,_ : (Γ : Ctx)(A : Ty s Γ) → Ctx
    𝒑 : {Γ : Ctx}(A : Ty s Γ) → Γ ,, A ~> Γ
    𝒒 : {Γ : Ctx}(A : Ty s Γ) → Tm (A ∙ 𝒑 A)
    univ-prop : ∀{Γ Δ}{A : Ty s Δ}
      (f : Γ ~> Δ)
      (t : Tm (A ∙ f))
      → -----------------------------
      ∃! λ (〈f,t〉 : Γ ~> (Δ ,, A)) →
      𝒑 A ∘ 〈f,t〉 == f ∧
      𝒒 A ⊙ 〈f,t〉 Het.== t

  〈_,_〉 : ∀{Γ Δ}{A : Ty s Δ}
    (f : Γ ~> Δ)
    (t : Tm (A ∙ f))
    → --------------------
    Γ ~> Δ ,, A
  〈 f , t 〉 = elem (!choice (univ-prop f t))

  〈_,_〉-prop : ∀{Γ Δ}{A : Ty s Δ}
    (f : Γ ~> Δ)
    (t : Tm (A ∙ f))
    → --------------------
    𝒑 A ∘ 〈 f , t 〉 == f ∧ 𝒒 A ⊙ 〈 f , t 〉 Het.== t
  〈 f , t 〉-prop = ∧left (prop (!choice (univ-prop f t)))

  〈_,_〉-uniq : ∀{Γ Δ}{A : Ty s Δ}
    (f : Γ ~> Δ)
    (t : Tm (A ∙ f))
    → --------------------
    _
  〈 f , t 〉-uniq = ∧right (prop (!choice (univ-prop f t)))

  field
    𝑈 : (Γ : Ctx)(s : ℕ) → Ty (s +1) Γ
    hierarchy : (Γ : Ctx)(s : ℕ)
      → ----------------------------------------
      Ty s Γ == Tm (𝑈 Γ s)
    𝑈-preserv : ∀{Γ Δ}
      (s : ℕ)
      (f : Δ ~> Γ)
      → ----------------------------------------
      𝑈 Γ s ∙ f == 𝑈 Δ s
    Ty-sub==Tm-sub : ∀{Γ Δ : Ctx}
      (A : Ty s Γ)
      (f : Δ ~> Γ) →
      A ∙ f Het.== coe (hierarchy Γ s) A ⊙ f

  module Variable where
    variable
      Γ Δ Β : Ctx
      s₀ s₁ s₂ : ℕ
      A : Ty s Γ
      B : Ty s (Γ ,, A)
      C : Ty s (Γ ,, A ,, B)
  open Variable

  infixl 184 _⁺ _⁺⁺ _⁺³
  _⁺ : Ty s₁ Γ → Ty s₁ (Γ ,, A)
  _⁺ {A = A} = _∙ 𝒑 A
  _⁺⁺ : Ty s Γ → Ty s (Γ ,, A ,, B)
  T ⁺⁺ = T ⁺ ⁺
  _⁺³ : Ty s Γ → Ty s (Γ ,, A ,, B ,, C)
  T ⁺³ = T ⁺⁺ ⁺

  ∙-comp== :
    (A : Ty s Γ) (f : Δ ~> Γ) (g : Β ~> Δ)
    → -------------------------------------
    A ∙ f ∙ g == A ∙ (f ∘ g)
  ∙-comp== A f g = ap (λ — → pr₁ — A) $ sym $ ∘-preserv g f

  ⊙-comp== : {A : Ty s Γ}
    (a : Tm A) (f : Δ ~> Γ) (g : Β ~> Δ)
    → ------------------------------------
    a ⊙ f ⊙ g Het.== a ⊙ (f ∘ g)
  ⊙-comp== {Β = Β}{A} a f g =
    proof a ⊙ f ⊙ g
      === (pr₂ (F₁ g) (A ∙ f) ∘ₛ pr₂ (F₁ f) A) a
        :by: Id.refl _ [: _==_ ]
      het== pr₂ (F₁ (f ∘ g)) A a
        :by: Id.ap2 (λ — (f : _ → pr₂ (F₀ Β) —) → f a)
               (∙-comp== A f g)
               (proof pr₂ (F₁ g) (A ∙ f) ∘ₛ pr₂ (F₁ f) A
                  het== pr₂ (F₁ (f ∘ g)) A
                    :by: ap (λ — → pr₂ — A) ⦃ Relating-all-==-het== ⦄ $
                         sym {R = _==_} $ ∘-preserv g f
                qed)
      === a ⊙ (f ∘ g)
        :by: Id.refl _
    qed

  ⊙==⊙ : ∀{Γ Γ'}{A : Ty s Γ}{A' : Ty s Γ'}
    {a : Tm A}{a' : Tm A'}
    {f : Δ ~> Γ}{f' : Δ ~> Γ'}
    (p₀ : Γ == Γ')
    (p₁ : A Het.== A')
    (q : a Het.== a')
    (q' : f Het.== f')
    → --------------------------
    a ⊙ f Het.== a' ⊙ f'
  ⊙==⊙ (Id.refl Γ)(Het.refl A)(Het.refl a)(Het.refl f) = Het.refl (a ⊙ f)

  _⊙id : {A : Ty s Γ}(a : Tm A) → a ⊙ id Γ Het.== a
  _⊙id {Γ = Γ}{A} a =
    ap (λ f → pr₂ f A a) ⦃ Relating-all-==-het== ⦄ (id-preserv Γ)

  〈p,q〉==id : (A : Ty s Γ) → 〈 𝒑 A , 𝒒 A 〉 == id (Γ ,, A)
  〈p,q〉==id {Γ = Γ} A = sym $ 〈 𝒑 A , 𝒒 A 〉-uniq (id (Γ ,, A))
    (right-unit (𝒑 A) ,
     ap (λ — → pr₂ — (pr₁ (F₁ (𝒑 A)) A) (𝒒 A)) {r' = Het._==_}
        (id-preserv (Γ ,, A)))

  module Coer where
    〈_,_〉∘_ : (f : Δ ~> Γ)(A : Ty s Γ)(g : Β ~> Δ) →
      Tm (A ∙ f ∙ g) == Tm (A ∙ (f ∘ g))
    〈 f , A 〉∘ g = ap Tm $ ∙-comp== A f g

    bar : (A : Ty s Γ) → Tm A == Tm (A ∙ id Γ)
    bar {Γ = Γ} A = ap (λ — → Tm (pr₁ — A)) $ sym (id-preserv Γ)

    q[_,_] : (f : Δ ~> Γ)(A : Ty s Γ) →
      Tm ((A ∙ f) ⁺) == Tm (A ∙ (f ∘ 𝒑 (A ∙ f)))
    q[ f , A ] = ap Tm $ ∙-comp== A f (𝒑 (A ∙ f))

  〈_,_〉∘_ : ∀ {Γ Δ Β}{A : Ty s Γ}
    (f : Δ ~> Γ)
    (a : Tm (A ∙ f))
    (g : Β ~> Δ)
    → ---------------------------------------------------------
    〈 f , a 〉 ∘ g
    ==
    〈 f ∘ g , coe (Coer.〈 f , A 〉∘ g) (a ⊙ g) 〉
  〈_,_〉∘_ {s}{Β = Β}{A = A} f a g =
    〈 f ∘ g , coe (Coer.〈 f , A 〉∘ g) (a ⊙ g) 〉-uniq
    (〈 f , a 〉 ∘ g)
    ((proof 𝒑 A ∘ (〈 f , a 〉 ∘ g)
        === (𝒑 A ∘ 〈 f , a 〉) ∘ g
          :by: assoc (𝒑 A) 〈 f , a 〉 g
        === f ∘ g
          :by: ap (_∘ g) $ ∧left 〈 f , a 〉-prop
      qed) ,
     (proof 𝒒 A ⊙ (〈 f , a 〉 ∘ g)
        het== 𝒒 A ⊙ 〈 f , a 〉  ⊙ g
          :by: isym $ ⊙-comp== (𝒒 A) 〈 f , a 〉 g
        === pr₂ (F₁ g) (A ⁺ ∙ 〈 f , a 〉) (𝒒 A ⊙ 〈 f , a 〉)
          :by: Id.refl _ [: Het._==_ ]
        het== pr₂ (F₁ g) (A ∙ f) a
          :by: Id.ap2 (λ B (a : Tm B) → pr₂ (F₁ g) B a)
                 (proof A ⁺ ∙ 〈 f , a 〉
                    === A ∙ (𝒑 A ∘ 〈 f , a 〉)
                      :by: ∙-comp== A (𝒑 A) 〈 f , a 〉
                    === A ∙ f
                      :by: ap (A ∙_) $ ∧left 〈 f , a 〉-prop
                  qed)
                 (∧right 〈 f , a 〉-prop)
        het== coe (Coer.〈 f , A 〉∘ g) (a ⊙ g)
          :by: isym $ coe-eval (Coer.〈 f , A 〉∘ g) (a ⊙ g)
      qed))

  bar : {A : Ty s Γ}
    (a : Tm A)
    → -------------------------
    Γ ~> Γ ,, A
  bar {Γ = Γ}{A} a = 〈 id Γ , coe (Coer.bar A) a 〉

  p_∘bar_ : ∀{Γ}
    (A : Ty s Γ)
    (a : Tm A)
    → ----------------------------------
    𝒑 A ∘ bar a == id Γ
  p_∘bar_ {Γ = Γ} A a = ∧left 〈 id Γ , coe (Coer.bar A) a 〉-prop

  _⁺∙bar_ :  ∀{Γ}
    (A : Ty s Γ)
    (a : Tm A)
    → ---------------------
    A ⁺ ∙ bar a == A
  _⁺∙bar_ {Γ = Γ} A a =
    proof A ⁺ ∙ bar a
      === A ∙ (𝒑 A ∘ bar a) :by: ∙-comp== A (𝒑 A) (bar a)
      === A ∙ id Γ          :by: ap (A ∙_) $ p A ∘bar a
      === A                 :by: ap (λ — → pr₁ — A) $ id-preserv Γ
    qed

  bar⁻¹ : {A : Ty s Γ}
    (sec : Σₚ λ (f : Γ ~> Γ ,, A) → 𝒑 A ∘ f == id Γ)
    → ----------------------------------------------
    Tm A
  bar⁻¹ {Γ = Γ}{A} (f , p) = coe p' (𝒒 A ⊙ f)
    where p' : Tm ((A ⁺) ∙ f) == Tm A
          p' = ap (λ — → Tm (— A)) {r = _==_} (
            proof Ty-sub f ∘ₛ Ty-sub (𝒑 A)
              === Ty-sub (𝒑 A ∘ f) :by: ap pr₁ $ sym $ ∘-preserv f (𝒑 A)
              === Ty-sub (id Γ)    :by: ap Ty-sub p
              === id-fun           :by: ap pr₁ $ id-preserv Γ
            qed)

  instance
    LeftInverse-bar : ∀{Γ}{A : Ty s Γ} →
      LeftInverse (λ x → bar x , p A ∘bar x) bar⁻¹
    RightInverse-bar : ∀{Γ}{A : Ty s Γ} →
      RightInverse (λ x → bar x , p A ∘bar x) bar⁻¹

  left-inv ⦃ LeftInverse-bar {Γ = Γ}{A} ⦄ a =
    proof bar⁻¹ (bar a , p A ∘bar a)
      === coe p (𝒒 A ⊙ bar a)
        :by: Id.refl _
      het== 𝒒 A ⊙ 〈 id Γ , coe coer a 〉
        :by: coe-eval p (𝒒 A ⊙ bar a)
      het== coe coer a :by: ∧right 〈 id Γ , coe coer a 〉-prop
      het== a          :by: coe-eval coer a
    qed
    where p = ap (λ — → Tm (— A)) {r = _==_}(
            proof Ty-sub (bar a) ∘ₛ Ty-sub (𝒑 A)
              === Ty-sub (𝒑 A ∘ bar a)
                :by: ap pr₁ $ sym $ ∘-preserv (bar a) (𝒑 A)
              === Ty-sub (id Γ)
                :by: ap Ty-sub $ p A ∘bar a
              === id-fun
                :by: ap pr₁ $ id-preserv Γ
            qed)
          coer = ap (λ — → Tm (pr₁ — A)) $ sym (id-preserv Γ)
  right-inv ⦃ RightInverse-bar {Γ = Γ}{A} ⦄ (f , p) =
    subrel $ Σₚ== $ subrel {_R_ = Het._==_}{_P_ = _==_}(
    proof bar (bar⁻¹ (f , p))
      === bar (coe p″ (𝒒 A ⊙ f)) :by: Id.refl _
      === 〈 id Γ , coe coer (coe p″ (𝒒 A ⊙ f)) 〉
        :by: Id.refl _
      het== 〈 𝒑 A ∘ f , coe coer' (𝒒 A ⊙ f) 〉
        :by: Id.ap2 (λ f a → 〈 f , a 〉)
               (sym p)
               (proof coe coer (coe p″ (𝒒 A ⊙ f))
                  het== coe p″ (𝒒 A ⊙ f)
                    :by: coe-eval coer (coe p″ (𝒒 A ⊙ f))
                  het== 𝒒 A ⊙ f
                    :by: coe-eval p″ (𝒒 A ⊙ f)
                  het== coe coer' (𝒒 A ⊙ f)
                    :by: isym $ coe-eval coer' (𝒒 A ⊙ f)
                qed)
      === 〈 𝒑 A , 𝒒 A 〉 ∘ f
        :by: sym $ 〈 𝒑 A , 𝒒 A 〉∘ f
      === id (Γ ,, A) ∘ f :by: ap (_∘ f) $ 〈p,q〉==id A
      === f               :by: left-unit f
    qed)
    where p' : Ty-sub f ∘ₛ Ty-sub (𝒑 A) == Ty-sub (𝒑 A ∘ f)
          p' = proof Ty-sub f ∘ₛ Ty-sub (𝒑 A)
                 === Ty-sub (𝒑 A ∘ f)
                   :by: ap pr₁ $ sym $ ∘-preserv f (𝒑 A)
               qed
          p″ : Tm (A ⁺ ∙ f) == Tm A
          p″ = ap (λ — → Tm (— A)) {r = _==_}(
            proof Ty-sub f ∘ₛ Ty-sub (𝒑 A)
              === Ty-sub (𝒑 A ∘ f) :by: p'
              === Ty-sub (id Γ)    :by: ap Ty-sub p
              === id-fun           :by: ap pr₁ $ id-preserv Γ
            qed)
          coer = ap (λ — → Tm (pr₁ — A)) $ sym (id-preserv Γ)
          coer' = ap (λ — → Tm (— A)) p'

  q[_,_] : (f : Δ ~> Γ)(A : Ty s Γ) → Δ ,, A ∙ f ~> Γ ,, A
  q[ f , A ] = 〈 f ∘ 𝒑 (A ∙ f) , coe Coer.q[ f , A ] (𝒒 (A ∙ f)) 〉

  q[_,_]-prop : ∀{Γ Δ}
    (f : Δ ~> Γ)
    (A : Ty s Γ)
    → --------------------
    𝒑 A ∘ q[ f , A ] == f ∘ 𝒑 (A ∙ f) ∧ 𝒒 A ⊙ q[ f , A ] Het.== 𝒒 (A ∙ f)
  q[ f , A ]-prop = ∧left p , (
    proof 𝒒 A ⊙ q[ f , A ]
      het== coe Coer.q[ f , A ] (𝒒 (A ∙ f))
        :by: ∧right p
      het== 𝒒 (A ∙ f)
        :by: coe-eval Coer.q[ f , A ] (𝒒 (A ∙ f))
    qed)
    where p = 〈 f ∘ 𝒑 (A ∙ f) , coe Coer.q[ f , A ] (𝒒 (A ∙ f)) 〉-prop

  〈_,_〉== :
    {f f' : Γ ~> Δ}
    (p : f == f')
    {t : Tm (A ∙ f)}
    {t' : Tm (A ∙ f')}
    (q : t Het.== t')
    → --------------------
    〈 f , t 〉 == 〈 f' , t' 〉
  〈 Id.refl f , Het.refl t 〉== = Id.refl 〈 f , t 〉

  〈,〉het==〈,〉 : {A A' : Ty s Δ}
    {f f' : Γ ~> Δ}
    (p₀ : f == f')
    (p₁ : A == A')
    {t : Tm (A ∙ f)}
    {t' : Tm (A' ∙ f')}
    (q : t Het.== t')
    → --------------------
    〈 f , t 〉 Het.== 〈 f' , t' 〉
  〈,〉het==〈,〉 (Id.refl f)(Id.refl A)(Het.refl t) = Het.refl 〈 f , t 〉

  q[_,_]∘〈_,_〉 :
    (f : Γ ~> Δ)
    (A : Ty s Δ)
    → let A' = A ∙ f in
    (f' : Β ~> Γ)
    (t' : Tm (A' ∙ f'))
    → ----------------------------------------------------------
    q[ f , A ] ∘ 〈 f' , t' 〉
    ==
    〈 f ∘ f' , coe (ap Tm $ ∙-comp== A f f') t' 〉
  q[ f , A ]∘〈 f' , t' 〉 =
    proof 〈 f ∘ 𝒑 A' , coe coer₀ (𝒒 A') 〉 ∘ 〈 f' , t' 〉
      === 〈 f ∘ 𝒑 A' ∘ 〈 f' , t' 〉 ,
            coe coer₂ (coe coer₀ (𝒒 A') ⊙ 〈 f' , t' 〉) 〉
        :by: 〈 f ∘ 𝒑 A' , coe coer₀ (𝒒 A') 〉∘ 〈 f' , t' 〉
      === 〈 f ∘ f' , coe coer₁ t' 〉
        :by: 〈 proof f ∘ 𝒑 A' ∘ 〈 f' , t' 〉
                 === f ∘ (𝒑 A' ∘ 〈 f' , t' 〉)
                   :by: sym $ assoc f (𝒑 A') 〈 f' , t' 〉
                 === f ∘ f'
                   :by: ap (f ∘_) $ ∧left 〈 f' , t' 〉-prop
               qed ,
               proof coe coer₂ (coe coer₀ (𝒒 A') ⊙ 〈 f' , t' 〉)
                 het== coe coer₀ (𝒒 A') ⊙ 〈 f' , t' 〉
                   :by: coe-eval coer₂ (coe coer₀ (𝒒 A') ⊙ 〈 f' , t' 〉)
                 het== 𝒒 A' ⊙ 〈 f' , t' 〉
                   :by: Id.ap2 (λ A (q : Tm A) → q ⊙ 〈 f' , t' 〉)
                               (sym $ ∙-comp== A f (𝒑 A'))
                               (coe-eval coer₀ (𝒒 A'))
                 het== t'           :by: ∧right 〈 f' , t' 〉-prop
                 het== coe coer₁ t' :by: isym $ coe-eval coer₁ t'
               qed 〉==
    qed
    where A' = A ∙ f
          coer₀ = ap Tm $ ∙-comp== A f (𝒑 A')
          coer₁ = ap Tm $ ∙-comp== A f f'
          coer₂ = ap Tm $ ∙-comp== A (f ∘ 𝒑 A') 〈 f' , t' 〉
  
  _⁺∙q[_]== :
    (A : Ty s Γ)
    (f : Δ ~> Γ)
    → ----------------------------
    A ⁺ ∙ q[ f , A ] == (A ∙ f) ⁺
  A ⁺∙q[ f ]== =
    proof A ⁺ ∙ q[ f , A ]
      === A ∙ (𝒑 A ∘ q[ f , A ]) :by: ∙-comp== A (𝒑 A) q[ f , A ]
      === A ∙ (f ∘ 𝒑 (A ∙ f))    :by: ap (A ∙_) $ ∧left q[ f , A ]-prop
      === (A ∙ f) ⁺              :by: sym $ ∙-comp== A f (𝒑 (A ∙ f))
    qed

  q[p_]∘bar_ :
    (A : Ty s₀ Γ)
    (a : Tm A)
    → ----------------------------------------------------------
    q[ 𝒑 A , A ] ∘ bar (a ⊙ 𝒑 A) == bar a ∘ 𝒑 A
  q[p_]∘bar_ {Γ = Γ} A a =
    proof q[ 𝒑 A , A ] ∘ bar (a ⊙ 𝒑 A)
      === 〈 𝒑 A ∘ id (Γ ,, A) , coe coer₁ (coe coer₀ (a ⊙ 𝒑 A)) 〉
        :by: q[ 𝒑 A , A ]∘〈 id (Γ ,, A) , coe coer₀ (a ⊙ 𝒑 A) 〉
      === 〈 id Γ ∘ 𝒑 A , coe coer₃ (coe coer₂ a ⊙ 𝒑 A) 〉
        :by: 〈 sym $ bi-unit (𝒑 A) ,
             proof coe coer₁ (coe coer₀ (a ⊙ 𝒑 A))
               het== coe coer₀ (a ⊙ 𝒑 A)
                 :by: coe-eval coer₁ (coe coer₀ (a ⊙ 𝒑 A))
               het== a ⊙ 𝒑 A
                 :by: coe-eval coer₀ (a ⊙ 𝒑 A)
               het== coe coer₂ a ⊙ 𝒑 A
                 :by: ⊙==⊙ (Id.refl Γ)
                      (subrel {_R_ = _==_} $ ap (λ f → pr₁ f A) $
                       sym $ id-preserv Γ)
                      (isym $ coe-eval coer₂ a)
                      (Het.refl (𝒑 A))
               het== coe coer₃ (coe coer₂ a ⊙ 𝒑 A)
                 :by: isym $ coe-eval coer₃ (coe coer₂ a ⊙ 𝒑 A)
             qed 〉==
      === bar a ∘ 𝒑 A
        :by: sym $ 〈 id Γ , coe coer₂ a 〉∘ 𝒑 A
    qed
    where coer₀ = Coer.bar (A ⁺)
          coer₁ = ap Tm $ ∙-comp== A (𝒑 A) (id (Γ ,, A))
          coer₂ = Coer.bar A
          coer₃ = Coer.〈 id Γ , A 〉∘ 𝒑 A
