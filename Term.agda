{-# OPTIONS --allow-unsolved-metas #-}
module Term where

open import Type
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality
  using (subst; _≡_; refl; cong; cong₂; trans; sym)

infixl 5 _,_
data Ctx : Ctxᵏ → Set where
    ∅ : Ctx ∅
    _,ᵏ_ : Ctx 𝒦 → ∀ J → Ctx (𝒦 ,ᵏ J)
    _,_ : Ctx 𝒦 → 𝒦 ⊢ᵏ * → Ctx 𝒦

variable
    Γ Δ : Ctx 𝒦

infix 4 _∋_
data _∋_ : Ctx 𝒦 → 𝒦 ⊢ᵏ * → Set where
    Z : Γ , A ∋ A 
    S : Γ ∋ A → Γ , B ∋ A  
    T : Γ ∋ A → Γ ,ᵏ J ∋ weakenᵏ A 

infix 4 _⊢_
data _⊢_ {𝒦} Γ : 𝒦 ⊢ᵏ * → Set where
    ` : Γ ∋ A → Γ ⊢ A
    ⟨⟩ : Γ ⊢ Unit
    ± : Nat → Γ ⊢ Int
    true : Γ ⊢ Bool
    false : Γ ⊢ Bool
    if_then_else_ : Γ ⊢ Bool → Γ ⊢ A → Γ ⊢ A → Γ ⊢ A
    ⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
    fst : Γ ⊢ A × B → Γ ⊢ A 
    snd : Γ ⊢ A × B → Γ ⊢ B 
    -- inl : 
    -- inr : 
    -- case_of_⇒_ :
    ƛ : Γ , A ⊢ B → Γ ⊢ A ⇒ B
    _·_ : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    Λ : Γ ,ᵏ J ⊢ A → Γ ⊢ Π A
    _·ᵏ_ : Γ ⊢ Π A → (B : 𝒦 ⊢ᵏ J) → Γ ⊢ A [ B ]ᵏ
    pack_,_as_ : ∀ {A} → (α : 𝒦 ⊢ᵏ J) → Γ ⊢ (A [ α ]ᵏ) → Γ ,ᵏ J ⊢ A → Γ ⊢ Σ A
    unpack_as_,_of_ : ∀ {A} → Γ ⊢ Σ A → (α : 𝒦 ⊢ᵏ J) → Γ ,ᵏ J ⊢ A → Γ ⊢ (A [ α ]ᵏ)
    roll : ∀ A → Γ ⊢ A [ μ A ]ᵏ → Γ ⊢ μ A 
    unroll : Γ ⊢ μ A → Γ ⊢ A [ μ A ]ᵏ

conv∋ : A ≡ B → Γ ∋ A → Γ ∋ B 
conv∋ refl α = α

conv⊢ : A ≡ B → Γ ⊢ A → Γ ⊢ B
conv⊢ refl α = α

Ren : Ctx 𝒦₁ → Ctx 𝒦₂ → Renᵏ 𝒦₁ 𝒦₂ → Set
Ren Γ Δ ρ = ∀{A} → Γ ∋ A → Δ ∋ (renᵏ ρ A)

lift : ∀ {Γ Δ} {ρᵏ : Renᵏ 𝒦₁ 𝒦₂} → Ren Γ Δ ρᵏ → {A : 𝒦₁ ⊢ᵏ *} → Ren (Γ , A) (Δ , renᵏ ρᵏ A) ρᵏ
lift ρ  Z = Z
lift ρ (S x) = S (ρ x)

ᵏlift : ∀ {Γ Δ} {ρᵏ : Renᵏ 𝒦₁ 𝒦₂} → Ren Γ Δ ρᵏ → (Ren (Γ ,ᵏ J) (Δ ,ᵏ J) (liftᵏ ρᵏ))
ᵏlift ρ (T x) = conv∋ (trans (sym (renᵏ-comp _)) (renᵏ-comp _)) (T (ρ x))

-- ren : ∀ {Γ Δ} {ρᵏ : Renᵏ 𝒦₁ 𝒦₂} → Ren Γ Δ ρᵏ → ({A : 𝒦₁ ⊢ᵏ *} → Γ ⊢ A → Δ ⊢ renᵏ ρᵏ A)
-- ren ρ (` x) = ` (ρ x)
-- ren ρ ⟨⟩ = ⟨⟩
-- ren ρ (± x) = ± x
-- ren ρ true = true
-- ren ρ false = true
-- ren ρ (if cond then e₁ else e₂) = if ren ρ cond then ren ρ e₁ else ren ρ e₂
-- ren ρ ⟨ e₁ , e₂ ⟩ = ⟨ ren ρ e₁ , ren ρ e₂ ⟩
-- ren ρ (fst e) = fst (ren ρ e)
-- ren ρ (snd e) = snd (ren ρ e)
-- ren ρ (ƛ e) = ƛ (ren (lift ρ) e)
-- ren ρ (e₁ · e₂) = ren ρ e₁ · ren ρ e₂
-- ren ρ (Λ e) = Λ (ren (ᵏlift ρ) e)
-- ren ρ (_·ᵏ_ {A = A} e B ) = conv⊢ (sym (ren[]ᵏ _ A B)) (ren ρ e ·ᵏ renᵏ _ B)
-- ren ρ (pack α , a as a₁) = {!  !}
-- ren ρ (unpack_as_,_of_ a α a₁) = {!   !}
-- ren ρ (roll A a) = {!   !}
-- ren ρ (unroll a) = {!   !}

_[_] : Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A 
_[_] e = {!   !}

_ᵏ[_] : {A : 𝒦 ,ᵏ J ⊢ᵏ *} → Γ ,ᵏ J ⊢ A → (B : 𝒦 ⊢ᵏ J) → Γ ⊢ A [ B ]ᵏ 
_ᵏ[_] e = {!   !}

variable
    e e' e₁ e₂ : Γ ⊢ A 